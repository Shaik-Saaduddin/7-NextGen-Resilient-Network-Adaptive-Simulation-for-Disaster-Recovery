// =============================================================================
//  Disaster-Resilient MANET  —  ns-3.45
//  AODV + DBSCAN + Three Node Types + Disaster + Self-Recovery
//
//  Node layout (global IDs):
//    [0 .. NUM_TOWERS-1]                     Network Towers  (stationary)
//    [NUM_TOWERS .. NUM_TOWERS+NUM_LORA-1]   LoRa Relays     (slow-moving)
//    [NUM_TOWERS+NUM_LORA .. total-1]        User Devices    (KAIST traces)
//
//  Timeline:
//    t=2s    Initial DBSCAN, towers elected as primary CHs
//    t=7s+   Periodic re-clustering every 5s while towers alive
//    t=15s   DISASTER: all towers fail, users turn red
//    t=17s   RECOVERY: DBSCAN re-runs, LoRa nodes elected as new CHs
//    t=22s+  Periodic re-clustering under LoRa CHs
//
//  Color scheme (strictly as specified):
//    Tower  active    Purple  (128,   0, 128)
//    Tower  destroyed Grey    (150, 150, 150)
//    LoRa   CH/active Pink    (255, 105, 180)
//    LoRa   inactive  Grey    (150, 150, 150)
//    User   active    Green   (  0, 200,   0)
//    User   disconn.  Red     (255,   0,   0)
//
//  KAIST dataset:
//    Files: KAIST_30sec_001.txt ... KAIST_30sec_092.txt
//    Format (tab-separated, scientific notation, no header):
//        time_sec    x_m    y_m
//    92 files available.  NUM_USERS is capped at 92 if using KAIST.
//    Negative coordinates are globally shifted to positive.
//    Coordinates are scaled to fit AREA_SIZE x AREA_SIZE metres.
//    Default path hard-coded; override with --kaistDir=<path>
//
//  Build:
//    cd ~/ns-allinone-3.45/ns-3.45
//    cp disaster-manet.cc scratch/
//    ./ns3 build scratch/disaster-manet
//
//  Run (uses KAIST automatically from default path):
//    ./ns3 run "disaster-manet"
//
//  Run without dataset (pure random mobility):
//    ./ns3 run "disaster-manet --kaistDir=none"
//
//  Run with custom path:
//    ./ns3 run "disaster-manet --kaistDir=/some/other/path"
//
//  Tune parameters:
//    ./ns3 run "disaster-manet --numUsers=60 --numTowers=5 --numLora=15
//               --disasterT=20 --recoveryT=22 --simTime=80 --eps=110"
//
//  Visualize:
//    cd ~/ns-allinone-3.45/ns-3.45
//    netanim disaster-manet.xml
// =============================================================================

#include "ns3/core-module.h"
#include "ns3/network-module.h"
#include "ns3/mobility-module.h"
#include "ns3/internet-module.h"
#include "ns3/aodv-module.h"
#include "ns3/wifi-module.h"
#include "ns3/applications-module.h"
#include "ns3/flow-monitor-module.h"
#include "ns3/netanim-module.h"

#include <vector>
#include <set>
#include <map>
#include <cmath>
#include <limits>
#include <algorithm>
#include <iostream>
#include <fstream>
#include <sstream>
#include <iomanip>
#include <string>

using namespace ns3;
NS_LOG_COMPONENT_DEFINE ("DisasterManet");

// =============================================================================
//  Parameters  (all overridable at runtime via --flag=value)
// =============================================================================
static uint32_t    NUM_TOWERS    = 5;
static uint32_t    NUM_LORA      = 15;
static uint32_t    NUM_USERS     = 92;   // 92 KAIST trace files available
static double      AREA_SIZE     = 800.0;
static double      SIM_TIME      = 100.0;
static double      DISASTER_T    = 30.0;
static double      RECOVERY_T    = 32.0;
static uint32_t    NUM_FLOWS     = 20;
static double      DBSCAN_EPS    = 120.0;
static int         DBSCAN_MINPTS = 3;

// Default = your actual KAIST path.
// Pass --kaistDir=none to use random mobility instead.
static std::string KAIST_DIR =
    "/home/saad/ns-3.45/Final-Year-Project-Datasets/"
    "Final Year Project/Traces_TimeXY_30sec_txt/KAIST";

// =============================================================================
//  Colors
// =============================================================================
struct RGB { uint8_t r, g, b; };

static const RGB COL_TOWER_ACTIVE  = {128,   0, 128};  // purple
static const RGB COL_TOWER_DEAD    = {150, 150, 150};  // grey
static const RGB COL_LORA_ACTIVE   = {255, 105, 180};  // pink
static const RGB COL_LORA_INACTIVE = {150, 150, 150};  // grey
static const RGB COL_USER_ACTIVE   = {  0, 200,   0};  // green
static const RGB COL_USER_DISCO    = {255,   0,   0};  // red

// =============================================================================
//  Node types
// =============================================================================
enum NodeKind { TOWER, LORA, USER };

// =============================================================================
//  Global state
// =============================================================================
static AnimationInterface *g_anim = nullptr;

static uint32_t g_firstTower = 0;
static uint32_t g_firstLora  = 0;
static uint32_t g_firstUser  = 0;

static std::set<uint32_t> g_deadTowers;
static std::set<uint32_t> g_discoUsers;
static std::set<uint32_t> g_loraCHs;

static std::vector<int> g_clusterLabel;

static bool g_disasterDone = false;
static bool g_recoveryDone = false;

struct LegendEntry { uint32_t id; RGB col; std::string label; double sz; };
static std::vector<LegendEntry> g_legend;

// =============================================================================
//  Helpers
// =============================================================================
static NodeKind KindOf (uint32_t id)
{
    if (id < g_firstLora) return TOWER;
    if (id < g_firstUser) return LORA;
    return USER;
}

static void Paint (uint32_t id, const RGB &c, double sz, const std::string &lbl)
{
    g_anim->UpdateNodeColor       (id, c.r, c.g, c.b);
    g_anim->UpdateNodeSize        (id, sz,  sz);
    g_anim->UpdateNodeDescription (id, lbl);
}

// =============================================================================
//  KAIST trace loader
//
//  File format (confirmed from actual data):
//    - Tab-separated, 3 columns, scientific notation, no header
//    - Column 0: time (seconds, 30s intervals)
//    - Column 1: x (metres, can be large negative)
//    - Column 2: y (metres, can be large negative)
//    - Example: "0.0000000000000000e+000  -3.842e+002  -4.666e+001"
//
//  Filename convention: KAIST_30sec_001.txt through KAIST_30sec_092.txt
//
//  Global shift (applied identically across all files so relative positions
//  are preserved): computed in a pre-scan pass before any node is installed.
//
//  Returns true if file was loaded and had at least one valid waypoint.
// =============================================================================

struct KaistWaypoint { double t, x, y; };

// Pre-scan ALL KAIST files to find the global bounding box.
// This ensures all nodes share the same coordinate system after shifting.
static void KaistGlobalBounds (const std::string &dir,
                                uint32_t numFiles,
                                double &outMinX, double &outMinY,
                                double &outMaxX, double &outMaxY)
{
    outMinX = outMinY =  std::numeric_limits<double>::max ();
    outMaxX = outMaxY = -std::numeric_limits<double>::max ();

    for (uint32_t i = 1; i <= numFiles; i++) {
        std::ostringstream fname;
        fname << dir << "/KAIST_30sec_"
              << std::setw (3) << std::setfill ('0') << i << ".txt";

        std::ifstream f (fname.str ());
        if (!f.is_open ()) continue;

        std::string line;
        while (std::getline (f, line)) {
            if (line.empty () || line[0] == '#') continue;
            std::istringstream ss (line);
            double t, x, y;
            if (!(ss >> t >> x >> y)) continue;
            outMinX = std::min (outMinX, x);
            outMinY = std::min (outMinY, y);
            outMaxX = std::max (outMaxX, x);
            outMaxY = std::max (outMaxY, y);
        }
    }
}

// Load one KAIST file and install waypoints on mob.
// shiftX / shiftY: add to raw coords to make them non-negative.
// scale: multiply after shifting to fit AREA_SIZE.
static bool LoadKaistFile (const std::string &path,
                            Ptr<WaypointMobilityModel> mob,
                            double shiftX, double shiftY,
                            double scale)
{
    std::ifstream f (path);
    if (!f.is_open ()) return false;

    int count = 0;
    std::string line;
    while (std::getline (f, line)) {
        if (line.empty () || line[0] == '#') continue;
        std::istringstream ss (line);
        double t, x, y;
        if (!(ss >> t >> x >> y)) continue;

        double nx = std::max (0.0, std::min (AREA_SIZE, (x + shiftX) * scale));
        double ny = std::max (0.0, std::min (AREA_SIZE, (y + shiftY) * scale));

        mob->AddWaypoint (Waypoint (Seconds (t), Vector (nx, ny, 0.0)));
        count++;
    }
    return (count > 0);
}

// =============================================================================
//  DBSCAN
// =============================================================================
struct Pt { double x, y; };

static std::vector<int> RunDbscan (const std::vector<Pt> &pts)
{
    int n = (int)pts.size ();
    if (n == 0) return {};
    std::vector<int> label (n, 0);
    int cid = 0;
    const double eps2 = DBSCAN_EPS * DBSCAN_EPS;

    auto rq = [&](int i) {
        std::vector<int> nb;
        for (int j = 0; j < n; j++) {
            double dx = pts[i].x - pts[j].x, dy = pts[i].y - pts[j].y;
            if (dx*dx + dy*dy <= eps2) nb.push_back (j);
        }
        return nb;
    };

    for (int i = 0; i < n; i++) {
        if (label[i] != 0) continue;
        auto seeds = rq (i);
        if ((int)seeds.size () < DBSCAN_MINPTS) { label[i] = -1; continue; }
        ++cid; label[i] = cid;
        for (int s = 0; s < (int)seeds.size (); s++) {
            int q = seeds[s];
            if (label[q] == -1) { label[q] = cid; continue; }
            if (label[q] != 0)  continue;
            label[q] = cid;
            auto res = rq (q);
            if ((int)res.size () >= DBSCAN_MINPTS)
                seeds.insert (seeds.end (), res.begin (), res.end ());
        }
    }
    return label;
}

// =============================================================================
//  CH election
//  preferred = node IDs eligible to be CH (towers pre-disaster, LoRa post)
//  If no preferred node is in a cluster, elect highest-degree node of any type.
// =============================================================================
static std::map<int,uint32_t> ElectCHs (
        const std::vector<Pt>       &pts,
        const std::vector<int>      &label,
        int                          numC,
        const std::vector<uint32_t> &liveId,
        const std::set<uint32_t>    &preferred)
{
    std::map<int,uint32_t> ch;
    const double eps2 = DBSCAN_EPS * DBSCAN_EPS;

    for (int c = 1; c <= numC; c++) {
        int bestP = -1, bestPcnt = -1;
        int bestA = -1, bestAcnt = -1;
        for (int i = 0; i < (int)pts.size (); i++) {
            if (label[i] != c) continue;
            int cnt = 0;
            for (int j = 0; j < (int)pts.size (); j++) {
                if (i == j || label[j] != c) continue;
                double dx = pts[i].x - pts[j].x, dy = pts[i].y - pts[j].y;
                if (dx*dx + dy*dy <= eps2) cnt++;
            }
            if (cnt > bestAcnt) { bestAcnt = cnt; bestA = i; }
            if (preferred.count (liveId[i]) && cnt > bestPcnt)
                { bestPcnt = cnt; bestP = i; }
        }
        int w = (bestP >= 0) ? bestP : bestA;
        if (w >= 0) ch[c] = liveId[w];
    }
    return ch;
}

// =============================================================================
//  Assign noise/isolated nodes to nearest CH
// =============================================================================
static void AssignNoise (std::vector<int>             &label,
                         const std::vector<Pt>        &pts,
                         const std::map<int,uint32_t> &ch,
                         const std::vector<uint32_t>  &liveId)
{
    if (ch.empty ()) return;
    std::map<int,int> loc;
    for (auto &kv : ch)
        for (int i = 0; i < (int)liveId.size (); i++)
            if (liveId[i] == kv.second) { loc[kv.first] = i; break; }

    for (int i = 0; i < (int)pts.size (); i++) {
        if (label[i] > 0) continue;
        double best = 1e18; int bc = ch.begin ()->first;
        for (auto &kv : loc) {
            int hi = kv.second;
            double dx = pts[i].x - pts[hi].x, dy = pts[i].y - pts[hi].y;
            double d  = std::sqrt (dx*dx + dy*dy);
            if (d < best) { best = d; bc = kv.first; }
        }
        label[i] = bc;
    }
}

// =============================================================================
//  Core clustering + repaint
// =============================================================================
static void DoClustering (NodeContainer allNodes,
                           std::set<uint32_t> preferred)
{
    uint32_t N = allNodes.GetN ();
    std::vector<Pt>       pts;
    std::vector<uint32_t> liveId;

    for (uint32_t id = 0; id < N; id++) {
        if (g_deadTowers.count (id)) continue;
        Ptr<MobilityModel> m = allNodes.Get (id)->GetObject<MobilityModel> ();
        if (!m) continue;
        Vector p = m->GetPosition ();
        pts.push_back ({p.x, p.y});
        liveId.push_back (id);
    }
    if (pts.empty ()) return;

    auto label = RunDbscan (pts);
    int  numC  = *std::max_element (label.begin (), label.end ());
    if (numC < 0) numC = 0;

    auto localCH = ElectCHs (pts, label, numC, liveId, preferred);
    AssignNoise (label, pts, localCH, liveId);

    // Write back to global arrays
    g_clusterLabel.assign (N, 0);
    for (int li = 0; li < (int)liveId.size (); li++)
        g_clusterLabel[liveId[li]] = label[li];

    g_loraCHs.clear ();
    for (auto &kv : localCH)
        if (KindOf (kv.second) == LORA) g_loraCHs.insert (kv.second);

    std::cout << std::fixed << std::setprecision (1)
              << "[t=" << Simulator::Now ().GetSeconds () << "s]"
              << "  clusters=" << numC
              << "  CHs="      << localCH.size ()
              << "  live="     << pts.size ()
              << "  dead_towers=" << g_deadTowers.size ()
              << "\n";

    // — Paint towers ——————————————————————————————————————————————————————
    for (uint32_t id = g_firstTower; id < g_firstLora; id++) {
        if (g_deadTowers.count (id))
            Paint (id, COL_TOWER_DEAD, 14.0, "TWR-DEAD");
        else
            Paint (id, COL_TOWER_ACTIVE, 18.0, "TOWER-" + std::to_string (id));
    }

    // — Paint LoRa ————————————————————————————————————————————————————————
    for (uint32_t id = g_firstLora; id < g_firstUser; id++) {
        if (g_loraCHs.count (id))
            Paint (id, COL_LORA_ACTIVE,   14.0, "LORA-CH-" + std::to_string (id));
        else
            Paint (id, COL_LORA_INACTIVE,  7.0, "LORA-"    + std::to_string (id));
    }

    // — Paint users ———————————————————————————————————————————————————————
    for (uint32_t id = g_firstUser; id < N; id++) {
        if (g_discoUsers.count (id))
            Paint (id, COL_USER_DISCO,  5.0, "U-DISCO-" + std::to_string (id));
        else
            Paint (id, COL_USER_ACTIVE, 5.0, "U-"       + std::to_string (id));
    }
}

// =============================================================================
//  Pre-disaster periodic clustering (towers preferred)
// =============================================================================
void PeriodicCluster (NodeContainer allNodes)
{
    if (g_disasterDone) return;
    std::set<uint32_t> pref;
    for (uint32_t id = g_firstTower; id < g_firstLora; id++) pref.insert (id);
    DoClustering (allNodes, pref);
    Simulator::Schedule (Seconds (5.0), &PeriodicCluster, allNodes);
}

// =============================================================================
//  Post-recovery periodic clustering (LoRa preferred)
// =============================================================================
void PostRecoveryCluster (NodeContainer allNodes)
{
    std::set<uint32_t> pref;
    for (uint32_t id = g_firstLora; id < g_firstUser; id++) pref.insert (id);
    DoClustering (allNodes, pref);

    // Update disco set based on fresh clustering
    for (uint32_t id = g_firstUser; id < allNodes.GetN (); id++) {
        if (g_clusterLabel[id] > 0) {
            g_discoUsers.erase (id);
            Paint (id, COL_USER_ACTIVE, 5.0, "U-" + std::to_string (id));
        } else {
            g_discoUsers.insert (id);
            Paint (id, COL_USER_DISCO, 5.0, "U-DISCO-" + std::to_string (id));
        }
    }
    Simulator::Schedule (Seconds (5.0), &PostRecoveryCluster, allNodes);
}

// =============================================================================
//  DISASTER EVENT
// =============================================================================
void DisasterEvent (NodeContainer allNodes)
{
    g_disasterDone = true;
    double now = Simulator::Now ().GetSeconds ();

    std::cout << "\n############################################\n"
              << "#  DISASTER at t=" << std::fixed << std::setprecision (1)
              << now << "s\n"
              << "#  All " << NUM_TOWERS << " network towers destroyed!\n"
              << "############################################\n\n";

    for (uint32_t id = g_firstTower; id < g_firstLora; id++) {
        g_deadTowers.insert (id);

        // Bring IPv4 down → triggers AODV RERR to all neighbours
        Ptr<Ipv4> ip = allNodes.Get (id)->GetObject<Ipv4> ();
        if (ip)
            for (uint32_t ifc = 1; ifc < ip->GetNInterfaces (); ifc++)
                ip->SetDown (ifc);

        // Stop all applications on the tower
        Ptr<Node> nd = allNodes.Get (id);
        for (uint32_t j = 0; j < nd->GetNApplications (); j++) {
            Ptr<Application> a = nd->GetApplication (j);
            if (a) a->SetStopTime (Seconds (now + 0.001));
        }

        Paint (id, COL_TOWER_DEAD, 14.0, "TWR-DEAD");
        std::cout << "  Tower " << id << " destroyed\n";
    }

    // All users become disconnected (red)
    g_discoUsers.clear ();
    for (uint32_t id = g_firstUser; id < allNodes.GetN (); id++) {
        g_discoUsers.insert (id);
        Paint (id, COL_USER_DISCO, 5.0, "U-DISCO-" + std::to_string (id));
    }

    // LoRa goes grey — not yet elected as CHs
    g_loraCHs.clear ();
    for (uint32_t id = g_firstLora; id < g_firstUser; id++)
        Paint (id, COL_LORA_INACTIVE, 7.0, "LORA-" + std::to_string (id));

    std::cout << "\n  Recovery scheduled at t="
              << RECOVERY_T << "s\n\n";
}

// =============================================================================
//  RECOVERY EVENT
// =============================================================================
void RecoveryEvent (NodeContainer allNodes)
{
    g_recoveryDone = true;
    double now = Simulator::Now ().GetSeconds ();

    std::cout << "\n############################################\n"
              << "#  RECOVERY at t=" << std::fixed << std::setprecision (1)
              << now << "s\n"
              << "#  LoRa devices taking over as new CHs\n"
              << "############################################\n\n";

    std::set<uint32_t> pref;
    for (uint32_t id = g_firstLora; id < g_firstUser; id++) pref.insert (id);
    DoClustering (allNodes, pref);

    // Users with a valid cluster assignment reconnect → green
    uint32_t reconnected = 0;
    g_discoUsers.clear ();
    for (uint32_t id = g_firstUser; id < allNodes.GetN (); id++) {
        if (g_clusterLabel[id] > 0) {
            Paint (id, COL_USER_ACTIVE, 5.0, "U-" + std::to_string (id));
            reconnected++;
        } else {
            g_discoUsers.insert (id);
            Paint (id, COL_USER_DISCO, 5.0, "U-DISCO-" + std::to_string (id));
        }
    }

    std::cout << "  Reconnected: "   << reconnected
              << "  Still isolated: " << g_discoUsers.size () << "\n\n";

    // Continue periodic re-clustering under LoRa CHs
    Simulator::Schedule (Seconds (5.0), &PostRecoveryCluster, allNodes);
}

// =============================================================================
//  main
// =============================================================================
int main (int argc, char *argv[])
{
    CommandLine cmd;
    cmd.AddValue ("numTowers",  "Number of network towers",          NUM_TOWERS);
    cmd.AddValue ("numLora",    "Number of LoRa relay devices",      NUM_LORA);
    cmd.AddValue ("numUsers",   "Number of mobile user devices",     NUM_USERS);
    cmd.AddValue ("areaSize",   "Field side length (m)",             AREA_SIZE);
    cmd.AddValue ("simTime",    "Simulation duration (s)",           SIM_TIME);
    cmd.AddValue ("disasterT",  "Tower failure time (s)",            DISASTER_T);
    cmd.AddValue ("recoveryT",  "Recovery start time (s)",           RECOVERY_T);
    cmd.AddValue ("numFlows",   "Number of UDP flows",               NUM_FLOWS);
    cmd.AddValue ("eps",        "DBSCAN neighbourhood radius (m)",   DBSCAN_EPS);
    cmd.AddValue ("minPts",     "DBSCAN core-point threshold",       DBSCAN_MINPTS);
    cmd.AddValue ("kaistDir",   "KAIST trace dir; 'none'=random",    KAIST_DIR);
    cmd.Parse (argc, argv);

    srand ((unsigned)time (nullptr));

    bool useKaist = (KAIST_DIR != "none" && !KAIST_DIR.empty ());

    // Cap NUM_USERS to 92 when using KAIST (92 files available)
    if (useKaist && NUM_USERS > 92) {
        std::cout << "  [INFO] Capping numUsers to 92 (KAIST file count)\n";
        NUM_USERS = 92;
    }

    uint32_t totalNodes = NUM_TOWERS + NUM_LORA + NUM_USERS;
    g_firstTower = 0;
    g_firstLora  = NUM_TOWERS;
    g_firstUser  = NUM_TOWERS + NUM_LORA;
    g_clusterLabel.assign (totalNodes, 0);

    double recEps = std::sqrt (5.0 * AREA_SIZE * AREA_SIZE /
                               ((double)totalNodes * M_PI));

    std::cout << "\n================================================\n"
              << "  Disaster-Resilient MANET  (ns-3.45)\n"
              << "  Towers="     << NUM_TOWERS
              << "  LoRa="       << NUM_LORA
              << "  Users="      << NUM_USERS
              << "  Total="      << totalNodes << "\n"
              << "  Area="       << AREA_SIZE << "x" << AREA_SIZE << "m\n"
              << "  Disaster t=" << DISASTER_T << "s"
              << "  Recovery t=" << RECOVERY_T << "s\n"
              << "  DBSCAN eps=" << DBSCAN_EPS << "m"
              << "  minPts="     << DBSCAN_MINPTS << "\n"
              << std::fixed << std::setprecision (1)
              << "  Rec. eps for ~5 nbrs: " << recEps << "m\n"
              << "  KAIST: " << (useKaist ? KAIST_DIR : "disabled (random)") << "\n"
              << "================================================\n\n";

    // =========================================================================
    //  Pre-scan KAIST files for global bounding box
    //  (must happen before any node installation so scale is consistent)
    // =========================================================================
    double kaistShiftX = 0, kaistShiftY = 0, kaistScale = 1.0;

    if (useKaist) {
        double minX, minY, maxX, maxY;
        KaistGlobalBounds (KAIST_DIR, 92, minX, minY, maxX, maxY);

        kaistShiftX = (minX < 0) ? -minX : 0.0;
        kaistShiftY = (minY < 0) ? -minY : 0.0;

        double spanX = maxX - minX;
        double spanY = maxY - minY;
        double span  = std::max (spanX, spanY);
        kaistScale   = (span > AREA_SIZE) ? (AREA_SIZE / span) : 1.0;

        std::cout << "  KAIST bounds: x=[" << minX << "," << maxX << "]"
                  << "  y=[" << minY << "," << maxY << "]\n"
                  << "  shift=(" << kaistShiftX << "," << kaistShiftY << ")"
                  << "  scale=" << kaistScale << "\n\n";
    }

    // =========================================================================
    //  Create ALL nodes first
    // =========================================================================
    NodeContainer allNodes;
    allNodes.Create (totalNodes);

    // =========================================================================
    //  Shared WiFi ad-hoc channel (802.11b, 20 dBm ≈ 250 m range)
    // =========================================================================
    WifiHelper wifi;
    wifi.SetStandard (WIFI_STANDARD_80211b);

    YansWifiChannelHelper wChan = YansWifiChannelHelper::Default ();
    YansWifiPhyHelper     wPhy;
    wPhy.SetChannel (wChan.Create ());
    wPhy.Set ("TxPowerStart", DoubleValue (20.0));
    wPhy.Set ("TxPowerEnd",   DoubleValue (20.0));

    WifiMacHelper wMac;
    wMac.SetType ("ns3::AdhocWifiMac");

    NetDeviceContainer devices = wifi.Install (wPhy, wMac, allNodes);

    // =========================================================================
    //  Mobility
    // =========================================================================

    // — Towers: evenly spaced grid ——————————————————————————————————————————
    {
        Ptr<ListPositionAllocator> pa = CreateObject<ListPositionAllocator> ();
        uint32_t cols = (uint32_t)std::ceil (std::sqrt ((double)NUM_TOWERS));
        uint32_t rows = (uint32_t)std::ceil ((double)NUM_TOWERS / cols);
        for (uint32_t i = 0; i < NUM_TOWERS; i++) {
            double x = AREA_SIZE * ((i % cols) + 0.5) / cols;
            double y = AREA_SIZE * ((i / cols) + 0.5) / rows;
            pa->Add (Vector (x, y, 0.0));
        }
        MobilityHelper mh;
        mh.SetPositionAllocator (pa);
        mh.SetMobilityModel ("ns3::ConstantPositionMobilityModel");
        NodeContainer tc (allNodes.Begin (), allNodes.Begin () + NUM_TOWERS);
        mh.Install (tc);
    }

    // — LoRa: slow random waypoint (0.5–2 m/s) ——————————————————————————
    {
        std::ostringstream rng;
        rng << "ns3::UniformRandomVariable[Min=0|Max=" << (int)AREA_SIZE << "]";
        Ptr<RandomRectanglePositionAllocator> pa =
            CreateObject<RandomRectanglePositionAllocator> ();
        pa->SetAttribute ("X", StringValue (rng.str ()));
        pa->SetAttribute ("Y", StringValue (rng.str ()));

        MobilityHelper mh;
        mh.SetPositionAllocator (pa);
        mh.SetMobilityModel (
            "ns3::RandomWaypointMobilityModel",
            "Speed",             StringValue ("ns3::UniformRandomVariable[Min=0.5|Max=2]"),
            "Pause",             StringValue ("ns3::ConstantRandomVariable[Constant=5]"),
            "PositionAllocator", PointerValue (pa));

        NodeContainer lc (allNodes.Begin () + NUM_TOWERS,
                          allNodes.Begin () + NUM_TOWERS + NUM_LORA);
        mh.Install (lc);
    }

    // — Users: KAIST traces (files 001..NUM_USERS) or random fallback ———
    {
        std::ostringstream rng;
        rng << "ns3::UniformRandomVariable[Min=0|Max=" << (int)AREA_SIZE << "]";
        Ptr<RandomRectanglePositionAllocator> pa =
            CreateObject<RandomRectanglePositionAllocator> ();
        pa->SetAttribute ("X", StringValue (rng.str ()));
        pa->SetAttribute ("Y", StringValue (rng.str ()));

        int kaistLoaded = 0, kaistFallback = 0;

        for (uint32_t u = 0; u < NUM_USERS; u++) {
            Ptr<Node> nd = allNodes.Get (g_firstUser + u);
            bool ok = false;

            if (useKaist) {
                // Files are 1-based: node u=0 → KAIST_30sec_001.txt
                std::ostringstream fname;
                fname << KAIST_DIR << "/KAIST_30sec_"
                      << std::setw (3) << std::setfill ('0') << (u + 1) << ".txt";

                Ptr<WaypointMobilityModel> wmob =
                    CreateObject<WaypointMobilityModel> ();
                wmob->SetAttribute ("InitialPositionIsWaypoint",
                                    BooleanValue (true));

                if (LoadKaistFile (fname.str (), wmob,
                                   kaistShiftX, kaistShiftY, kaistScale)) {
                    nd->AggregateObject (wmob);
                    kaistLoaded++; ok = true;
                }
            }

            if (!ok) {
                // Random Waypoint fallback
                MobilityHelper mh;
                mh.SetPositionAllocator (pa);
                mh.SetMobilityModel (
                    "ns3::RandomWaypointMobilityModel",
                    "Speed",             StringValue ("ns3::UniformRandomVariable[Min=2|Max=10]"),
                    "Pause",             StringValue ("ns3::ConstantRandomVariable[Constant=1]"),
                    "PositionAllocator", PointerValue (pa));
                NodeContainer single; single.Add (nd);
                mh.Install (single);
                kaistFallback++;
            }
        }

        std::cout << "  Users: " << kaistLoaded   << " from KAIST traces, "
                  << kaistFallback << " random fallback\n\n";
    }

    // =========================================================================
    //  AODV routing + Internet stack
    // =========================================================================
    AodvHelper aodv;
    InternetStackHelper internet;
    internet.SetRoutingHelper (aodv);
    internet.Install (allNodes);

    Ipv4AddressHelper ipv4h;
    ipv4h.SetBase ("10.0.0.0", "255.255.0.0");
    Ipv4InterfaceContainer ifaces = ipv4h.Assign (devices);

    // =========================================================================
    //  UDP OnOff flows  (user → user only)
    // =========================================================================
    uint16_t basePort = 9000;
    for (uint32_t f = 0; f < NUM_FLOWS; f++) {
        uint32_t src = g_firstUser + rand () % NUM_USERS;
        uint32_t dst = g_firstUser + rand () % NUM_USERS;
        if (src == dst) { f--; continue; }

        OnOffHelper onoff ("ns3::UdpSocketFactory",
            InetSocketAddress (ifaces.GetAddress (dst), basePort + f));
        onoff.SetConstantRate (DataRate ("256kbps"), 512);
        ApplicationContainer tx = onoff.Install (allNodes.Get (src));
        tx.Start (Seconds (3.0));
        tx.Stop  (Seconds (SIM_TIME - 3.0));

        PacketSinkHelper sink ("ns3::UdpSocketFactory",
            InetSocketAddress (Ipv4Address::GetAny (), basePort + f));
        sink.Install (allNodes.Get (dst)).Start (Seconds (0.0));
    }

    // =========================================================================
    //  FlowMonitor
    // =========================================================================
    FlowMonitorHelper fmHelper;
    Ptr<FlowMonitor>  flowMon = fmHelper.InstallAll ();

    // =========================================================================
    //  Legend nodes — MUST be created BEFORE AnimationInterface
    // =========================================================================
    {
        struct LE { RGB col; const char *label; double sz; };
        static const LE ENTRIES[] = {
            { COL_TOWER_ACTIVE,  "Tower  (active)",     18.0 },
            { COL_TOWER_DEAD,    "Tower  (destroyed)",  14.0 },
            { COL_LORA_ACTIVE,   "LoRa   (CH active)",  14.0 },
            { COL_LORA_INACTIVE, "LoRa   (inactive)",    7.0 },
            { COL_USER_ACTIVE,   "User   (active)",       5.0 },
            { COL_USER_DISCO,    "User   (disconnected)", 5.0 },
        };
        static const int NE = (int)(sizeof (ENTRIES) / sizeof (ENTRIES[0]));

        NodeContainer lgnd;
        lgnd.Create (NE);

        Ptr<ListPositionAllocator> lpa = CreateObject<ListPositionAllocator> ();
        for (int i = 0; i < NE; i++)
            lpa->Add (Vector (AREA_SIZE + 80.0, 50.0 + i * 65.0, 0.0));

        MobilityHelper lmob;
        lmob.SetPositionAllocator (lpa);
        lmob.SetMobilityModel ("ns3::ConstantPositionMobilityModel");
        lmob.Install (lgnd);

        WifiHelper            lw; lw.SetStandard (WIFI_STANDARD_80211b);
        YansWifiChannelHelper lc = YansWifiChannelHelper::Default ();
        YansWifiPhyHelper     lp; lp.SetChannel (lc.Create ());
        WifiMacHelper         lm; lm.SetType ("ns3::AdhocWifiMac");
        lw.Install (lp, lm, lgnd);
        InternetStackHelper ls; ls.Install (lgnd);

        g_legend.clear ();
        for (int i = 0; i < NE; i++)
            g_legend.push_back ({ lgnd.Get (i)->GetId (),
                                  ENTRIES[i].col,
                                  std::string (ENTRIES[i].label),
                                  ENTRIES[i].sz });
    }

    // =========================================================================
    //  NetAnim — after ALL nodes (including legend) are created
    // =========================================================================
    AnimationInterface anim ("disaster-manet.xml");
    g_anim = &anim;
    anim.SetMaxPktsPerTraceFile (1000000);

    for (uint32_t id = 0; id < NUM_TOWERS; id++)
        Paint (id, COL_TOWER_ACTIVE, 18.0, "TOWER-" + std::to_string (id));
    for (uint32_t id = g_firstLora; id < g_firstUser; id++)
        Paint (id, COL_LORA_INACTIVE, 7.0, "LORA-" + std::to_string (id));
    for (uint32_t id = g_firstUser; id < totalNodes; id++)
        Paint (id, COL_USER_ACTIVE, 5.0, "U-" + std::to_string (id));
    for (auto &e : g_legend) {
        anim.UpdateNodeColor       (e.id, e.col.r, e.col.g, e.col.b);
        anim.UpdateNodeSize        (e.id, e.sz, e.sz);
        anim.UpdateNodeDescription (e.id, e.label);
    }

    // =========================================================================
    //  Event schedule
    // =========================================================================

    // t=2s : initial clustering, towers preferred
    {
        std::set<uint32_t> pref;
        for (uint32_t id = g_firstTower; id < g_firstLora; id++) pref.insert (id);
        Simulator::Schedule (Seconds (2.0), &DoClustering, allNodes, pref);
    }

    // t=7s : periodic clustering before disaster
    Simulator::Schedule (Seconds (7.0), &PeriodicCluster, allNodes);

    // DISASTER_T : tower failure
    Simulator::Schedule (Seconds (DISASTER_T), &DisasterEvent, allNodes);

    // RECOVERY_T : LoRa-based self-recovery
    Simulator::Schedule (Seconds (RECOVERY_T), &RecoveryEvent, allNodes);

    // =========================================================================
    //  Run
    // =========================================================================
    Simulator::Stop (Seconds (SIM_TIME));
    Simulator::Run ();

    // =========================================================================
    //  Flow statistics
    // =========================================================================
    flowMon->CheckForLostPackets ();
    auto stats = flowMon->GetFlowStats ();

    double totTput = 0, totPdr = 0, totDelay = 0;
    uint32_t valid = 0;

    for (auto &kv : stats) {
        auto &s = kv.second;
        if (!s.txPackets) continue;
        totPdr += (double)s.rxPackets / s.txPackets * 100.0;
        if (s.rxPackets > 0 && s.timeLastRxPacket > s.timeFirstTxPacket) {
            double dur = (s.timeLastRxPacket - s.timeFirstTxPacket).GetSeconds ();
            totTput  += (s.rxBytes * 8.0) / (dur * 1024.0);
            totDelay += s.delaySum.GetSeconds () / s.rxPackets;
            valid++;
        }
    }

    std::cout << "\n========== SIMULATION RESULTS ==========\n"
              << "  Total nodes    : " << totalNodes    << "\n"
              << "  Total flows    : " << stats.size () << "\n"
              << "  Flows w/ data  : " << valid         << "\n";
    if (valid > 0)
        std::cout << std::fixed << std::setprecision (3)
                  << "  Avg throughput : " << totTput  / valid        << " Kbps\n"
                  << "  Avg PDR        : " << totPdr   / stats.size() << " %\n"
                  << "  Avg delay      : " << totDelay / valid        << " s\n";
    std::cout << "=========================================\n\n"
              << "  NetAnim output : disaster-manet.xml\n"
              << "  Open with:       netanim disaster-manet.xml\n"
              << "=========================================\n";

    Simulator::Destroy ();
    return 0;
}
