#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/bsat/satSolver.h"
#include "sat/cnf/cnf.h"

#include <algorithm>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iterator>
#include <memory>
#include <random>
#include <set>
#include <unordered_map>
#include <utility>
#include <vector>

extern "C" {
Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t* pNtk, int fExors, int fRegisters);
}

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandKlFlex(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTt, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBddSize, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_kl_flex", Lsv_CommandKlFlex, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

using LsvCut = std::vector<unsigned>;
using LsvCuts = std::vector<LsvCut>;

static const LsvCuts& Lsv_EnumerateCuts(Abc_Obj_t* node, int k,
                                        std::vector<LsvCuts>& cache) {
  LsvCuts& cuts = cache[Abc_ObjId(node)];
  if (!cuts.empty()) return cuts;

  // Strash normally removes constant fanins; retain support for imported AIGs.
  if (Abc_AigNodeIsConst(node)) {
    cuts.push_back({});
  } else {
    cuts.push_back({Abc_ObjId(node)});
    if (Abc_ObjIsNode(node)) {
      std::set<LsvCut> seen(cuts.begin(), cuts.end());
      const LsvCuts& left = Lsv_EnumerateCuts(Abc_ObjFanin0(node), k, cache);
      const LsvCuts& right = Lsv_EnumerateCuts(Abc_ObjFanin1(node), k, cache);
      for (const LsvCut& a : left) {
        for (const LsvCut& b : right) {
          LsvCut merged;
          std::set_union(a.begin(), a.end(), b.begin(), b.end(),
                         std::back_inserter(merged));
          if (merged.size() <= static_cast<size_t>(k) && seen.insert(merged).second)
            cuts.push_back(std::move(merged));
        }
      }
      LsvCuts irredundant;
      for (const LsvCut& cut : cuts) {
        bool redundant = false;
        for (unsigned mask = 1; mask + 1 < (1u << cut.size()); ++mask) {
          LsvCut subset;
          for (size_t i = 0; i < cut.size(); ++i)
            if (mask & (1u << i)) subset.push_back(cut[i]);
          if (seen.count(subset)) {
            redundant = true;
            break;
          }
        }
        if (!redundant) irredundant.push_back(cut);
      }
      cuts.swap(irredundant);
    }
  }
  return cuts;
}

static int Lsv_LeafIndex(Abc_Obj_t* node, const LsvCut& cut) {
  auto leaf = std::lower_bound(cut.begin(), cut.end(), Abc_ObjId(node));
  return leaf != cut.end() && *leaf == Abc_ObjId(node) ? leaf - cut.begin() : -1;
}

static bool Lsv_EvaluateTruth(Abc_Obj_t* node, const LsvCut& cut, uint64_t mask,
                              std::unordered_map<unsigned, uint64_t>& cache,
                              uint64_t& truth) {
  unsigned id = Abc_ObjId(node);
  auto cached = cache.find(id);
  if (cached != cache.end()) {
    truth = cached->second;
    return true;
  }
  int index = Lsv_LeafIndex(node, cut);
  if (index >= 0) {
    truth = 0;
    for (unsigned assignment = 0; assignment < (1u << cut.size()); ++assignment)
      truth |= uint64_t((assignment >> (cut.size() - index - 1)) & 1) << assignment;
  } else if (Abc_AigNodeIsConst(node)) {
    truth = mask;
  } else {
    if (!Abc_ObjIsNode(node)) return false;
    uint64_t left, right;
    if (!Lsv_EvaluateTruth(Abc_ObjFanin0(node), cut, mask, cache, left) ||
        !Lsv_EvaluateTruth(Abc_ObjFanin1(node), cut, mask, cache, right))
      return false;
    if (Abc_ObjFaninC0(node)) left ^= mask;
    if (Abc_ObjFaninC1(node)) right ^= mask;
    truth = left & right;
  }
  cache.emplace(id, truth);
  return true;
}

#ifdef ABC_USE_CUDD
struct LsvBddDeref {
  DdManager* dd;
  void operator()(DdNode* node) const { Cudd_RecursiveDeref(dd, node); }
};
using LsvBddRef = std::unique_ptr<DdNode, LsvBddDeref>;

static DdNode* Lsv_BuildBdd(Abc_Obj_t* node, const LsvCut& cut, DdManager* dd,
                             std::unordered_map<unsigned, LsvBddRef>& cache) {
  unsigned id = Abc_ObjId(node);
  auto cached = cache.find(id);
  if (cached != cache.end()) return cached->second.get();
  int index = Lsv_LeafIndex(node, cut);
  DdNode* result;
  if (index >= 0) {
    result = Cudd_bddIthVar(dd, index);
  } else if (Abc_AigNodeIsConst(node)) {
    result = Cudd_ReadOne(dd);
  } else {
    if (!Abc_ObjIsNode(node)) return nullptr;
    DdNode* left = Lsv_BuildBdd(Abc_ObjFanin0(node), cut, dd, cache);
    if (!left) return nullptr;
    DdNode* right = Lsv_BuildBdd(Abc_ObjFanin1(node), cut, dd, cache);
    if (!right) return nullptr;
    result = Cudd_bddAnd(dd, Cudd_NotCond(left, Abc_ObjFaninC0(node)),
                         Cudd_NotCond(right, Abc_ObjFaninC1(node)));
  }
  if (result) {
    Cudd_Ref(result);
    cache.emplace(id, LsvBddRef(result, LsvBddDeref{dd}));
  }
  return result;
}
#endif

static int Lsv_CommandCut(Abc_Frame_t* frame, int argc, char** argv,
                          bool bddsize) {
  if (argc != 2) {
    Abc_Print(-2, "usage: %s <k> (2 <= k <= 6)\n", argv[0]);
    return 1;
  }
  char* end;
  errno = 0;
  long k = std::strtol(argv[1], &end, 10);
  if (errno || *end || k < 2 || k > 6) {
    Abc_Print(-1, "k must be an integer from 2 to 6.\n");
    return 1;
  }
  Abc_Ntk_t* network = Abc_FrameReadNtk(frame);
  if (!network || !Abc_NtkIsStrash(network)) {
    Abc_Print(-1, "Read a circuit and run strash first.\n");
    return 1;
  }

#ifdef ABC_USE_CUDD
  std::unique_ptr<DdManager, decltype(&Cudd_Quit)> dd(
      bddsize ? Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0) : nullptr,
      &Cudd_Quit);
  if (bddsize && !dd) {
    Abc_Print(-1, "Cannot initialize CUDD.\n");
    return 1;
  }
  if (dd) Cudd_AutodynDisable(dd.get());
#else
  if (bddsize) {
    Abc_Print(-1, "BDD support requires a build with CUDD.\n");
    return 1;
  }
#endif

  std::vector<LsvCuts> cache(Abc_NtkObjNumMax(network));
  Abc_Obj_t* node;
  int i;
  Abc_NtkForEachNode(network, node, i) {
    for (const LsvCut& cut : Lsv_EnumerateCuts(node, k, cache)) {
      printf("%u: ", Abc_ObjId(node));
      for (size_t j = 0; j < cut.size(); ++j)
        printf("%s%u", j ? " " : "", cut[j]);
      if (!bddsize) {
        unsigned assignments = 1u << cut.size();
        uint64_t mask = assignments == 64 ? ~uint64_t(0) : (uint64_t(1) << assignments) - 1;
        std::unordered_map<unsigned, uint64_t> values;
        uint64_t truth;
        if (!Lsv_EvaluateTruth(node, cut, mask, values, truth)) {
          Abc_Print(-1, "Cut contains an invalid AIG node.\n");
          return 1;
        }
        printf(": %llX\n", static_cast<unsigned long long>(truth));
      }
#ifdef ABC_USE_CUDD
      else {
        std::unordered_map<unsigned, LsvBddRef> values;
        DdNode* result = Lsv_BuildBdd(node, cut, dd.get(), values);
        if (result) printf(": %d\n", Cudd_DagSize(result));
        if (!result) {
          Abc_Print(-1, "Cannot build BDD.\n");
          return 1;
        }
      }
#endif
    }
  }
  return 0;
}

static int Lsv_CommandCutTt(Abc_Frame_t* frame, int argc, char** argv) {
  return Lsv_CommandCut(frame, argc, argv, false);
}

static int Lsv_CommandCutBddSize(Abc_Frame_t* frame, int argc, char** argv) {
  return Lsv_CommandCut(frame, argc, argv, true);
}

// ---------------------------------------------------------------------------
// PA2: lsv_kl_flex <k> <l>
//
// A KL cut is identified with its region S = roots + interior; U = fanins of S
// outside S. Every node of S with a fanout outside S (incl. POs) must be a root
// (K4), and adding any other node of S as a root keeps U and S unchanged. So we
// search only "base" cuts whose roots are exactly those output nodes, run SAT
// once per base cut, and derive the cuts with extra roots from it: the extra
// roots are invisible outside S, so their bits of c are free.
//
// In a KL cut, the leaves first hit from each root form an irredundant cut of
// that root, so each cut is generated exactly once by picking, for distinct
// roots, one PA1 cut each, and requiring that no leaf lies inside another
// root's region (else the first-hit sets would differ).

namespace {

struct LsvKlPair {
  unsigned root;
  LsvCut leaves;                 // sorted
  std::vector<unsigned> region;  // nodes visited from root, stopping at leaves
};

struct LsvKlCut {
  std::vector<unsigned> roots, leaves, region;  // all sorted
};

struct LsvKlSearch {
  Abc_Ntk_t* ntk;
  int k, l;
  std::vector<LsvKlPair> pairs;
  std::vector<std::vector<int>> byLeaf, bySize;  // pair indices, ascending
  std::vector<int> inS, inU, mark;
  std::vector<char> isRoot;
  std::vector<int> chosen;
  std::vector<unsigned> leaves;  // distinct leaves of the current union
  int stamp = 0, sizeS = 0, best = 0;
  std::vector<LsvKlCut> results;

  Abc_Obj_t* Obj(unsigned id) const { return Abc_NtkObj(ntk, id); }

  bool Fits(const LsvKlPair& p) const {
    if (isRoot[p.root] || inU[p.root]) return false;
    size_t extra = 0;
    for (unsigned x : p.leaves) {
      if (isRoot[x] || inS[x]) return false;
      if (!inU[x]) ++extra;
    }
    if (leaves.size() + extra > static_cast<size_t>(k)) return false;
    for (unsigned y : p.region)
      if (inU[y]) return false;
    return true;
  }

  void Push(int j) {
    const LsvKlPair& p = pairs[j];
    for (unsigned y : p.region)
      if (inS[y]++ == 0) ++sizeS;
    for (unsigned x : p.leaves)
      if (inU[x]++ == 0) leaves.push_back(x);
    isRoot[p.root] = 1;
    chosen.push_back(j);
  }

  void Pop() {
    const LsvKlPair& p = pairs[chosen.back()];
    chosen.pop_back();
    isRoot[p.root] = 0;
    for (unsigned x : p.leaves)
      if (--inU[x] == 0) leaves.erase(std::find(leaves.begin(), leaves.end(), x));
    for (unsigned y : p.region)
      if (--inS[y] == 0) --sizeS;
  }

  bool LeavesS(unsigned id) const {  // some fanout leaves S (or is a PO)
    Abc_Obj_t* fanout;
    int i;
    Abc_ObjForEachFanout(Obj(id), fanout, i) if (!inS[Abc_ObjId(fanout)]) return true;
    return false;
  }

  // K3: every leaf has a path to a PI that avoids the other leaves.
  bool Escapes(unsigned leaf) {
    if (Abc_ObjIsPi(Obj(leaf))) return true;
    ++stamp;
    std::vector<Abc_Obj_t*> stack{Abc_ObjFanin0(Obj(leaf)), Abc_ObjFanin1(Obj(leaf))};
    while (!stack.empty()) {
      Abc_Obj_t* t = stack.back();
      stack.pop_back();
      unsigned id = Abc_ObjId(t);
      if (inU[id] || mark[id] == stamp || Abc_AigNodeIsConst(t)) continue;
      if (Abc_ObjIsPi(t)) return true;
      mark[id] = stamp;
      stack.push_back(Abc_ObjFanin0(t));
      stack.push_back(Abc_ObjFanin1(t));
    }
    return false;
  }

  void Record() {
    for (int j : chosen)
      for (unsigned y : pairs[j].region)
        if (!isRoot[y] && LeavesS(y)) return;  // K4
    if (sizeS < best) return;
    if (sizeS > best) {
      best = sizeS;
      results.clear();
    }
    LsvKlCut cut;
    for (int j : chosen) {
      cut.roots.push_back(pairs[j].root);
      cut.region.insert(cut.region.end(), pairs[j].region.begin(), pairs[j].region.end());
    }
    cut.leaves = leaves;
    std::sort(cut.roots.begin(), cut.roots.end());
    std::sort(cut.leaves.begin(), cut.leaves.end());
    std::sort(cut.region.begin(), cut.region.end());
    cut.region.erase(std::unique(cut.region.begin(), cut.region.end()), cut.region.end());
    results.push_back(std::move(cut));
  }

  void Try(size_t j, int depth) {
    if (!Fits(pairs[j])) return;
    Push(j);
    bool ok = true;
    for (int c : chosen) ok = ok && LeavesS(pairs[c].root);  // base cut only
    for (size_t i = 0; ok && i < leaves.size(); ++i) ok = Escapes(leaves[i]);
    // Both checks only get worse when more roots are added.
    if (ok) {
      Record();
      if (depth + 1 < l) Search(j + 1, depth + 1);
    }
    Pop();
  }

  // pairs are sorted by region size, so once this fails it fails for all later j.
  bool Hopeless(size_t j, int depth) const {
    return sizeS + static_cast<int>((l - depth) * pairs[j].region.size()) < best;
  }

  void Search(size_t start, int depth) {
    if (depth == 0) {
      for (size_t j = 0; j < pairs.size() && !Hopeless(j, 0); ++j) Try(j, 0);
      return;
    }
    // The next root's cut either shares a leaf with the current leaves ...
    std::vector<int> shared;
    for (unsigned x : leaves) {
      const std::vector<int>& v = byLeaf[x];
      shared.insert(shared.end(), std::lower_bound(v.begin(), v.end(), (int)start), v.end());
    }
    std::sort(shared.begin(), shared.end());
    shared.erase(std::unique(shared.begin(), shared.end()), shared.end());
    for (int j : shared) {
      if (Hopeless(j, depth)) break;
      Try(j, depth);
    }
    // ... or is disjoint from them and small enough to fit.
    for (size_t size = 1; size + leaves.size() <= static_cast<size_t>(k); ++size) {
      const std::vector<int>& v = bySize[size];
      for (auto it = std::lower_bound(v.begin(), v.end(), (int)start); it != v.end(); ++it) {
        if (Hopeless(*it, depth)) break;
        bool disjoint = true;
        for (unsigned x : pairs[*it].leaves) disjoint = disjoint && !inU[x];
        if (disjoint) Try(*it, depth);
      }
    }
  }
};

}  // namespace

// c is in A(u) iff no X with U(X) = u makes a PO of N[V <- c] differ from N.
// Under U = u the original roots equal cu, so both copies get constant roots,
// and leaves outside the TFO of V become constants too; strash then folds most
// of the miter away before SAT sees it.
static bool Lsv_KlAllowed(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut,
                          unsigned u, unsigned cu, unsigned c, std::vector<char>& cex) {
  int n = cut.leaves.size(), m = cut.roots.size();
  Abc_Ntk_t* mt = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
  Abc_Aig_t* man = (Abc_Aig_t*)mt->pManFunc;
  size_t N = Abc_NtkObjNumMax(ntk);
  std::vector<Abc_Obj_t*> base(N), a(N), b(N);
  std::vector<char> tfo(N);
  Abc_Obj_t* one = Abc_AigConst1(mt);
  auto bit = [&](unsigned v, int w, int j) { return Abc_ObjNotCond(one, !((v >> (w - 1 - j)) & 1)); };
  unsigned constId = Abc_ObjId(Abc_AigConst1(ntk));
  base[constId] = a[constId] = b[constId] = one;
  Abc_Obj_t* obj;
  int i;
  Abc_NtkForEachPi(ntk, obj, i) base[Abc_ObjId(obj)] = a[Abc_ObjId(obj)] = b[Abc_ObjId(obj)] =
      Abc_NtkCreatePi(mt);
  for (int j = 0; j < m; ++j) tfo[cut.roots[j]] = 1;
  auto fix = [&](unsigned id) {  // constants for roots and for leaves outside the TFO
    for (int j = 0; j < m; ++j)
      if (cut.roots[j] == id) { a[id] = bit(cu, m, j); b[id] = bit(c, m, j); return; }
    if (tfo[id]) return;
    for (int j = 0; j < n; ++j)
      if (cut.leaves[j] == id) { a[id] = b[id] = bit(u, n, j); return; }
  };
  Abc_NtkForEachPi(ntk, obj, i) fix(Abc_ObjId(obj));
  Vec_PtrForEachEntry(Abc_Obj_t*, order, obj, i) {
    unsigned id = Abc_ObjId(obj), f0 = Abc_ObjFaninId0(obj), f1 = Abc_ObjFaninId1(obj);
    int c0 = Abc_ObjFaninC0(obj), c1 = Abc_ObjFaninC1(obj);
    base[id] = Abc_AigAnd(man, Abc_ObjNotCond(base[f0], c0), Abc_ObjNotCond(base[f1], c1));
    if (!tfo[id]) tfo[id] = tfo[f0] || tfo[f1];
    a[id] = Abc_AigAnd(man, Abc_ObjNotCond(a[f0], c0), Abc_ObjNotCond(a[f1], c1));
    b[id] = Abc_AigAnd(man, Abc_ObjNotCond(b[f0], c0), Abc_ObjNotCond(b[f1], c1));
    fix(id);
  }
  Abc_Obj_t* diff = Abc_ObjNot(one);
  Abc_NtkForEachPo(ntk, obj, i) {
    unsigned d = Abc_ObjFaninId0(obj);
    diff = Abc_AigOr(man, diff, Abc_AigXor(man, a[d], b[d]));
  }
  Abc_Obj_t* mu = diff;
  for (int j = 0; j < n; ++j)
    mu = Abc_AigAnd(man, mu, Abc_AigXor(man, base[cut.leaves[j]], Abc_ObjNot(bit(u, n, j))));
  bool allowed = mu == Abc_ObjNot(one);
  if (!allowed) {
    Abc_ObjAddFanin(Abc_NtkCreatePo(mt), mu);
    Abc_AigCleanup(man);
    Abc_NtkAddDummyPiNames(mt);
    Abc_NtkAddDummyPoNames(mt);
    Aig_Man_t* aig = Abc_NtkToDar(mt, 0, 0);
    // Plain SAT settles most calls; the rest go to fraig-based CEC, whose SAT
    // sweeping merges the equal parts of the two copies.
    Cnf_Dat_t* cnf = Cnf_Derive(aig, 1);
    sat_solver* sat = (sat_solver*)Cnf_DataWriteIntoSolver(cnf, 1, 0);
    int r = l_False;
    if (sat) {
      lit l = Abc_Var2Lit(cnf->pVarNums[Aig_ManCo(aig, 0)->Id], 0);
      r = sat_solver_solve(sat, &l, &l + 1, 1000, 0, 0, 0);
      Aig_Obj_t* ci;
      int k;
      if (r == l_True) Aig_ManForEachCi(aig, ci, k) {
        int v = cnf->pVarNums[ci->Id];
        cex.push_back(v >= 0 && sat_solver_var_value(sat, v));
      }
      sat_solver_delete(sat);
    }
    Cnf_DataFree(cnf);
    if (r == l_Undef) r = Fra_FraigCec(&aig, 1000000000, 0) == 1 ? l_False : l_True;
    allowed = r == l_False;
    Aig_ManStop(aig);
  }
  Abc_NtkDelete(mt);
  return allowed;
}

// One incremental solver per cut, shared by all (u, c): the original network
// plus a second copy of the TFO of V whose roots are free variables. A query
// assumes U = u on the original and V = c on the copy. If the plain "some PO
// differs" call does not settle it, sweep: walk the TFO in topological order,
// visiting only nodes with a fanin not yet proved equal, and prove each
// original/copy pair equal under the assumptions (the care set U = u). Proved
// equalities are added under an activation literal. If the unproved set dies
// out before a PO, c is allowed.
struct LsvKlSat {
  Abc_Ntk_t* ntk;
  Vec_Ptr_t* order;
  const LsvKlCut& cut;
  sat_solver* s;
  int N, mu, nVars;
  std::vector<char> tfo, isRoot;
  std::vector<int> pos, xors;
  int limit1, limit2, limit3, maxUndef;
  unsigned polU = ~0u;
  std::vector<char> seenDiff, witness;
  std::vector<uint64_t> wO, wF;
  std::mt19937_64 rng{1};

  int F(int id) const { return tfo[id] ? N + id : id; }

  LsvKlSat(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut)
      : ntk(ntk), order(order), cut(cut), N(Abc_NtkObjNumMax(ntk)) {
    // Conflict limits: PO-differs call, one node pair, one PO driver; and how many
    // unsettled pairs to tolerate before falling back to Lsv_KlAllowed.
    limit1 = 100, limit2 = 1000, limit3 = 20000, maxUndef = 10;
    tfo.assign(N, 0), isRoot.assign(N, 0), pos.assign(N, -1);
    for (unsigned r : cut.roots) tfo[r] = isRoot[r] = 1;
    s = sat_solver_new();
    mu = 2 * N;
    nVars = mu + 1 + Abc_NtkPoNum(ntk);
    sat_solver_setnvars(s, nVars);
    sat_solver_add_const(s, Abc_ObjId(Abc_AigConst1(ntk)), 0);
    Abc_Obj_t* obj;
    int i;
    Vec_PtrForEachEntry(Abc_Obj_t*, order, obj, i) {
      int id = Abc_ObjId(obj), f0 = Abc_ObjFaninId0(obj), f1 = Abc_ObjFaninId1(obj);
      int c0 = Abc_ObjFaninC0(obj), c1 = Abc_ObjFaninC1(obj);
      pos[id] = i;
      sat_solver_add_and(s, id, f0, f1, c0, c1, 0);
      if (isRoot[id] || !(tfo[f0] || tfo[f1])) continue;
      tfo[id] = 1;
      sat_solver_add_and(s, N + id, F(f0), F(f1), c0, c1, 0);
    }
    std::vector<lit> clause{Abc_Var2Lit(mu, 1)};
    Abc_NtkForEachPo(ntk, obj, i) {
      int d = Abc_ObjFaninId0(obj);
      if (!tfo[d]) continue;
      sat_solver_add_xor(s, mu + 1 + i, d, N + d, 0);
      xors.push_back(mu + 1 + i);
      clause.push_back(Abc_Var2Lit(mu + 1 + i, 0));
    }
    sat_solver_addclause(s, clause.data(), clause.data() + clause.size());
  }
  ~LsvKlSat() { sat_solver_delete(s); }

  void Model(std::vector<char>& x) {
    Abc_Obj_t* pi;
    int i;
    x.clear();
    Abc_NtkForEachPi(ntk, pi, i) x.push_back(sat_solver_var_value(s, Abc_ObjId(pi)));
  }

  // Simulates x and 63 neighbours of it on both copies; among the patterns with
  // U = u, records which nodes differ. Returns whether a PO differs (cex set).
  bool Simulate(const std::vector<char>& x, unsigned u, unsigned c, std::vector<char>& cex) {
    int n = cut.leaves.size(), m = cut.roots.size(), nPis = Abc_NtkPiNum(ntk);
    std::vector<uint64_t> w(nPis);
    for (int i = 0; i < nPis; ++i) w[i] = x[i] ? ~uint64_t(0) : 0;
    for (int bit = 1; bit < 64; ++bit)
      for (int k = 0; k <= bit % 3; ++k) w[rng() % nPis] ^= uint64_t(1) << bit;
    Abc_Obj_t* obj;
    int i;
    wO[Abc_ObjId(Abc_AigConst1(ntk))] = ~uint64_t(0);
    Abc_NtkForEachPi(ntk, obj, i) wO[Abc_ObjId(obj)] = w[i];
    for (int j = 0; j < m; ++j) wF[cut.roots[j]] = (c >> (m - 1 - j)) & 1 ? ~uint64_t(0) : 0;
    auto in = [&](std::vector<uint64_t>& v, int f, int compl_) { return compl_ ? ~v[f] : v[f]; };
    Vec_PtrForEachEntry(Abc_Obj_t*, order, obj, i) {
      int id = Abc_ObjId(obj), f0 = Abc_ObjFaninId0(obj), f1 = Abc_ObjFaninId1(obj);
      int c0 = Abc_ObjFaninC0(obj), c1 = Abc_ObjFaninC1(obj);
      wO[id] = in(wO, f0, c0) & in(wO, f1, c1);
      if (tfo[id] && !isRoot[id])
        wF[id] = in(tfo[f0] ? wF : wO, f0, c0) & in(tfo[f1] ? wF : wO, f1, c1);
    }
    uint64_t valid = ~uint64_t(0);
    for (int j = 0; j < n; ++j) valid &= (u >> (n - 1 - j)) & 1 ? wO[cut.leaves[j]] : ~wO[cut.leaves[j]];
    Vec_PtrForEachEntry(Abc_Obj_t*, order, obj, i) {
      int id = Abc_ObjId(obj);
      if (tfo[id] && ((wO[id] ^ wF[id]) & valid)) seenDiff[id] = 1;
    }
    Abc_NtkForEachPo(ntk, obj, i) {
      int d = Abc_ObjFaninId0(obj);
      uint64_t diff = tfo[d] ? (wO[d] ^ wF[d]) & valid : 0;
      if (!diff) continue;
      int bit = 0;
      while (!((diff >> bit) & 1)) ++bit;
      cex.clear();
      for (int k = 0; k < nPis; ++k) cex.push_back((w[k] >> bit) & 1);
      return true;
    }
    return false;
  }

  int Solve(std::vector<lit>& a, int limit) {
    return sat_solver_solve(s, a.data(), a.data() + a.size(), limit, 0, 0, 0);
  }

  // 1: c is in A(u), 0: it is not, -1: gave up. u must be producible and cu its root value.
  int Query(unsigned u, unsigned cu, unsigned c, std::vector<char>& cex) {
    int n = cut.leaves.size(), m = cut.roots.size();
    std::vector<lit> a;
    for (int j = 0; j < n; ++j) a.push_back(Abc_Var2Lit(cut.leaves[j], !((u >> (n - 1 - j)) & 1)));
    for (int j = 0; j < m; ++j) {
      a.push_back(Abc_Var2Lit(cut.roots[j], !((cu >> (m - 1 - j)) & 1)));
      a.push_back(Abc_Var2Lit(N + cut.roots[j], !((c >> (m - 1 - j)) & 1)));
    }
    if (u != polU) {
      // Decide towards a known X with U(X) = u, so models stay inside the care set.
      polU = u;
      witness.clear();
      if (Solve(a, 0) == l_True) {
        Model(witness);
        std::vector<lit> pol;
        for (int v = 0; v < N; ++v) {
          pol.push_back(Abc_Var2Lit(v, !sat_solver_var_value(s, v)));
          pol.push_back(Abc_Var2Lit(N + v, !sat_solver_var_value(s, v)));
        }
        sat_solver_set_literal_polarity(s, pol.data(), pol.size());
      }
    }
    a.push_back(Abc_Var2Lit(mu, 0));
    int r = Solve(a, limit1);
    a.pop_back();
    int nUndef = 0;
    if (r == l_True) Model(cex);
    if (r != l_Undef) return r == l_False;

    int act = nVars++;
    sat_solver_setnvars(s, nVars);
    a.push_back(Abc_Var2Lit(act, 0));
    std::set<int> work;  // topological positions of nodes with an unproved fanin
    auto spread = [&](Abc_Obj_t* o) {  // returns whether o drives a PO
      bool po = false;
      Abc_Obj_t* fo;
      int i;
      Abc_ObjForEachFanout(o, fo, i) {
        if (Abc_ObjIsPo(fo)) po = true;
        else work.insert(pos[Abc_ObjId(fo)]);
      }
      return po;
    };
    int result = 1;
    seenDiff.assign(N, 0);
    wO.resize(N), wF.resize(N);
    std::vector<char> x;
    if (!witness.empty() && Simulate(witness, u, c, cex)) result = 0;
    for (int j = 0; j < m && result == 1; ++j)
      if ((((cu ^ c) >> (m - 1 - j)) & 1) && spread(Abc_NtkObj(ntk, cut.roots[j]))) result = 0;
    while (result == 1 && !work.empty()) {
      int p = *work.begin();
      work.erase(work.begin());
      Abc_Obj_t* obj = (Abc_Obj_t*)Vec_PtrEntry(order, p);
      int id = Abc_ObjId(obj);
      if (isRoot[id]) continue;
      int res = seenDiff[id] ? l_True : l_False;
      // A PO driver must be settled; other nodes may stay unproved.
      bool po = false;
      Abc_Obj_t* fo;
      int i;
      Abc_ObjForEachFanout(obj, fo, i) po = po || Abc_ObjIsPo(fo);
      for (int pol = 0; pol < 2 && res != l_True; ++pol) {
        a.push_back(Abc_Var2Lit(id, pol));
        a.push_back(Abc_Var2Lit(N + id, !pol));
        r = Solve(a, po ? limit3 : limit2);
        a.pop_back(), a.pop_back();
        if (r != l_False) res = r;
        if (r != l_True) continue;
        // The model and its neighbours show which later nodes differ: no SAT call for those.
        Model(x);
        if (Simulate(x, u, c, cex)) result = 0;
      }
      if (res == l_False) {
        lit c1[3] = {Abc_Var2Lit(act, 1), Abc_Var2Lit(id, 1), Abc_Var2Lit(N + id, 0)};
        lit c2[3] = {Abc_Var2Lit(act, 1), Abc_Var2Lit(id, 0), Abc_Var2Lit(N + id, 1)};
        sat_solver_addclause(s, c1, c1 + 3);
        sat_solver_addclause(s, c2, c2 + 3);
        continue;
      }
      if (res == l_Undef && ++nUndef > maxUndef) result = -1;
      if (spread(obj) && result == 1) result = -1;  // an unproved PO driver without a model
    }
    lit off = Abc_Var2Lit(act, 1);
    sat_solver_addclause(s, &off, &off + 1);
    return result;
  }
};

// Returns A(u) as a bit mask over root values c, for every leaf value u.
static std::vector<unsigned> Lsv_KlFlex(Abc_Ntk_t* ntk, Vec_Ptr_t* order,
                                        const LsvKlCut& cut) {
  int n = cut.leaves.size(), m = cut.roots.size();
  unsigned full = (1u << (1 << m)) - 1;
  std::vector<unsigned> masks(1u << n, full);

  Abc_Ntk_t* miter = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
  Abc_Aig_t* man = (Abc_Aig_t*)miter->pManFunc;
  std::vector<Abc_Obj_t*> orig(Abc_NtkObjNumMax(ntk)), forced(orig.size());
  std::vector<char> tfo(orig.size());
  unsigned constId = Abc_ObjId(Abc_AigConst1(ntk));
  orig[constId] = forced[constId] = Abc_AigConst1(miter);
  Abc_Obj_t* obj;
  int i;
  Abc_NtkForEachPi(ntk, obj, i) orig[Abc_ObjId(obj)] = forced[Abc_ObjId(obj)] =
      Abc_NtkCreatePi(miter);
  for (int j = 0; j < m; ++j) {
    forced[cut.roots[j]] = Abc_NtkCreatePi(miter);
    tfo[cut.roots[j]] = 1;
  }
  Vec_PtrForEachEntry(Abc_Obj_t*, order, obj, i) {
    unsigned id = Abc_ObjId(obj), f0 = Abc_ObjFaninId0(obj), f1 = Abc_ObjFaninId1(obj);
    orig[id] = Abc_AigAnd(man, Abc_ObjNotCond(orig[f0], Abc_ObjFaninC0(obj)),
                          Abc_ObjNotCond(orig[f1], Abc_ObjFaninC1(obj)));
    if (tfo[id]) continue;  // a root: already a new PI
    if (tfo[f0] || tfo[f1]) {
      tfo[id] = 1;
      forced[id] = Abc_AigAnd(man, Abc_ObjNotCond(forced[f0], Abc_ObjFaninC0(obj)),
                              Abc_ObjNotCond(forced[f1], Abc_ObjFaninC1(obj)));
    } else {
      forced[id] = orig[id];
    }
  }
  Abc_Obj_t* mu = Abc_ObjNot(Abc_AigConst1(miter));
  Abc_NtkForEachPo(ntk, obj, i) {
    unsigned d = Abc_ObjFaninId0(obj);
    if (tfo[d]) mu = Abc_AigOr(man, mu, Abc_AigXor(man, orig[d], forced[d]));
  }
  for (unsigned leaf : cut.leaves) Abc_ObjAddFanin(Abc_NtkCreatePo(miter), orig[leaf]);
  Abc_ObjAddFanin(Abc_NtkCreatePo(miter), mu);
  for (unsigned root : cut.roots) Abc_ObjAddFanin(Abc_NtkCreatePo(miter), orig[root]);
  Abc_AigCleanup(man);
  Abc_NtkAddDummyPiNames(miter);
  Abc_NtkAddDummyPoNames(miter);

  Aig_Man_t* aig = Abc_NtkToDar(miter, 0, 0);
  int nPis = Abc_NtkPiNum(ntk);

  // Random simulation finds most produced u, their root values, and most c
  // that a PO can observe; SAT is only asked about the rest.
  std::vector<char> seen(masks.size());
  std::vector<unsigned> orig_c(masks.size()), observed(masks.size());
  std::vector<uint64_t> val(Aig_ManObjNumMax(aig));
  std::mt19937_64 rng(1);
  auto co = [&](int i) {
    Aig_Obj_t* o = Aig_ManCo(aig, i);
    return val[Aig_ObjFaninId0(o)] ^ (Aig_ObjFaninC0(o) ? ~uint64_t(0) : 0);
  };
  auto simWord = [&]() {  // PI words are set by the caller
    std::vector<uint64_t> leafVal(n), rootVal(m);
    for (unsigned c = 0; c < (1u << m); ++c) {
      for (int j = 0; j < m; ++j)
        val[Aig_ManCi(aig, nPis + j)->Id] = (c >> (m - 1 - j)) & 1 ? ~uint64_t(0) : 0;
      val[Aig_ManConst1(aig)->Id] = ~uint64_t(0);
      Aig_Obj_t* o;
      int i;
      Aig_ManForEachNode(aig, o, i) val[i] =
          (val[Aig_ObjFaninId0(o)] ^ (Aig_ObjFaninC0(o) ? ~uint64_t(0) : 0)) &
          (val[Aig_ObjFaninId1(o)] ^ (Aig_ObjFaninC1(o) ? ~uint64_t(0) : 0));
      if (c == 0) {
        for (int j = 0; j < n; ++j) leafVal[j] = co(j);
        for (int j = 0; j < m; ++j) rootVal[j] = co(n + 1 + j);
      }
      uint64_t mu = co(n);
      for (int bit = 0; bit < 64; ++bit) {
        unsigned u = 0, r = 0;
        for (int j = 0; j < n; ++j) u = u << 1 | ((leafVal[j] >> bit) & 1);
        if (c == 0) {
          for (int j = 0; j < m; ++j) r = r << 1 | ((rootVal[j] >> bit) & 1);
          seen[u] = 1;
          orig_c[u] = r;
        }
        if ((mu >> bit) & 1) observed[u] |= 1u << c;
      }
    }
  };
  for (int word = 0; word < 64; ++word) {
    for (int i = 0; i < nPis; ++i) val[Aig_ManCi(aig, i)->Id] = rng();
    simWord();
  }
  // Random patterns rarely observe V in deep arithmetic. A SAT counterexample
  // does, and so do many of its neighbours, often for other u and c as well.
  auto simNear = [&](const std::vector<char>& x) {
    for (int word = 0; word < 4; ++word) {
      std::vector<uint64_t> w(nPis);
      for (int i = 0; i < nPis; ++i) w[i] = x[i] ? ~uint64_t(0) : 0;
      for (int bit = 1; bit < 64; ++bit)
        for (int k = 0; k <= bit % 3; ++k) w[rng() % nPis] ^= uint64_t(1) << bit;
      for (int i = 0; i < nPis; ++i) val[Aig_ManCi(aig, i)->Id] = w[i];
      simWord();
    }
  };

  LsvKlSat sweep(ntk, order, cut);
  Cnf_Dat_t* cnf = Cnf_Derive(aig, Aig_ManCoNum(aig));
  sat_solver* sat = (sat_solver*)Cnf_DataWriteIntoSolver(cnf, 1, 0);
  if (sat) {
    auto coVar = [&](int i) { return cnf->pVarNums[Aig_ManCo(aig, i)->Id]; };
    std::vector<lit> lits(n);
    for (unsigned u = 0; u < masks.size(); ++u) {
      for (int j = 0; j < n; ++j) lits[j] = Abc_Var2Lit(coVar(j), !((u >> (n - 1 - j)) & 1));
      if (!seen[u]) {
        if (sat_solver_solve(sat, lits.data(), lits.data() + n, 0, 0, 0, 0) == l_False)
          continue;  // u is never produced: everything is allowed
        orig_c[u] = 0;
        for (int j = 0; j < m; ++j)
          orig_c[u] = orig_c[u] << 1 | sat_solver_var_value(sat, coVar(n + 1 + j));
      }
      unsigned mask = 1u << orig_c[u];  // the original root values are always fine
      for (unsigned c = 0; c < (1u << m); ++c) {
        if (c == orig_c[u] || ((observed[u] >> c) & 1)) continue;
        std::vector<char> cex;
        int q = sweep.Query(u, orig_c[u], c, cex);
        bool ok = q < 0 ? Lsv_KlAllowed(ntk, order, cut, u, orig_c[u], c, cex) : q;
        if (!cex.empty()) simNear(cex);
        if (ok) mask |= 1u << c;
      }
      masks[u] = mask;
    }
    sat_solver_delete(sat);
  }
  Cnf_DataFree(cnf);
  Aig_ManStop(aig);
  Abc_NtkDelete(miter);
  return masks;
}

// Prints the base cut and every cut obtained by adding non-output nodes of S as
// roots; their bits of c do not matter.
static void Lsv_KlPrint(const LsvKlCut& cut, const std::vector<unsigned>& masks,
                        std::vector<unsigned>& roots, size_t next, int l) {
  std::vector<unsigned> sorted = roots;
  std::sort(sorted.begin(), sorted.end());
  int m = sorted.size(), mb = cut.roots.size();
  for (int j = 0; j < m; ++j) printf("%s%u", j ? " " : "", sorted[j]);
  printf(":");
  for (unsigned leaf : cut.leaves) printf(" %u", leaf);
  printf(":");
  for (unsigned base : masks) {
    unsigned mask = 0;
    for (unsigned c = 0; c < (1u << m); ++c) {
      unsigned cb = 0;
      for (int j = 0, b = 0; j < m; ++j)
        if (b < mb && sorted[j] == cut.roots[b]) cb |= ((c >> (m - 1 - j)) & 1) << (mb - 1 - b++);
      if ((base >> cb) & 1) mask |= 1u << c;
    }
    printf(" %X", mask);
  }
  printf("\n");
  for (size_t i = next; i < cut.region.size() && static_cast<int>(roots.size()) < l; ++i) {
    unsigned v = cut.region[i];
    if (std::binary_search(cut.roots.begin(), cut.roots.end(), v)) continue;
    roots.push_back(v);
    Lsv_KlPrint(cut, masks, roots, i + 1, l);
    roots.pop_back();
  }
}

static int Lsv_CommandKlFlex(Abc_Frame_t* frame, int argc, char** argv) {
  long kl[2];
  bool ok = argc == 3;
  for (int i = 0; ok && i < 2; ++i) {
    char* end;
    errno = 0;
    kl[i] = std::strtol(argv[i + 1], &end, 10);
    ok = !errno && !*end;
  }
  if (!ok || kl[0] < 1 || kl[0] > 6 || kl[1] < 1 || kl[1] > 4) {
    Abc_Print(-2, "usage: lsv_kl_flex <k> <l> (1 <= k <= 6, 1 <= l <= 4)\n");
    return 1;
  }
  Abc_Ntk_t* ntk = Abc_FrameReadNtk(frame);
  if (!ntk || !Abc_NtkIsStrash(ntk)) {
    Abc_Print(-1, "Read a circuit and run strash first.\n");
    return 1;
  }

  LsvKlSearch s;
  s.ntk = ntk;
  s.k = kl[0];
  s.l = kl[1];
  size_t nObjs = Abc_NtkObjNumMax(ntk);
  s.inS.assign(nObjs, 0);
  s.inU.assign(nObjs, 0);
  s.mark.assign(nObjs, 0);
  s.isRoot.assign(nObjs, 0);
  std::vector<LsvCuts> cache(nObjs);
  std::vector<char> inCut(nObjs);
  Abc_Obj_t* node;
  int i;
  Abc_NtkForEachNode(ntk, node, i) {
    for (const LsvCut& cut : Lsv_EnumerateCuts(node, s.k, cache)) {
      if (cut.empty() || (cut.size() == 1 && cut[0] == Abc_ObjId(node))) continue;
      LsvKlPair p{Abc_ObjId(node), cut, {}};
      for (unsigned x : cut) inCut[x] = 1;
      std::vector<Abc_Obj_t*> stack{node};
      ++s.stamp;
      while (!stack.empty()) {
        Abc_Obj_t* t = stack.back();
        stack.pop_back();
        unsigned id = Abc_ObjId(t);
        if (inCut[id] || s.mark[id] == s.stamp || Abc_AigNodeIsConst(t)) continue;
        s.mark[id] = s.stamp;
        p.region.push_back(id);
        stack.push_back(Abc_ObjFanin0(t));
        stack.push_back(Abc_ObjFanin1(t));
      }
      for (unsigned x : cut) inCut[x] = 0;
      s.pairs.push_back(std::move(p));
    }
  }
  std::stable_sort(s.pairs.begin(), s.pairs.end(),
                   [](const LsvKlPair& a, const LsvKlPair& b) {
                     return a.region.size() > b.region.size();
                   });
  s.byLeaf.resize(nObjs);
  s.bySize.resize(s.k + 1);
  for (size_t j = 0; j < s.pairs.size(); ++j) {
    for (unsigned x : s.pairs[j].leaves) s.byLeaf[x].push_back(j);
    s.bySize[s.pairs[j].leaves.size()].push_back(j);
  }
  s.Search(0, 0);

  Vec_Ptr_t* order = Abc_NtkDfs(ntk, 1);
  for (const LsvKlCut& cut : s.results) {
    std::vector<unsigned> masks = Lsv_KlFlex(ntk, order, cut);
    std::vector<unsigned> roots = cut.roots;
    Lsv_KlPrint(cut, masks, roots, 0, s.l);
  }
  Vec_PtrFree(order);
  return 0;
}
