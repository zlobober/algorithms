#include <cstdio>
#include <cassert>
#include <vector>
#include <algorithm>
#include <set>
using namespace std;

#ifdef DEBUG
    #define eprintf(...) fprintf(stderr, __VA_ARGS__)
    #define Assert(condition, message, ...) if (!(condition)) { eprintf("Line %d: assertion '%s' failed (" message ")\n", __LINE__, #condition, __VA_ARGS__); exit(1); }
#else
    #define eprintf(...)
    #define Assert(...)
#endif

constexpr int Infinity = 100 * 1000 * 1000;

// Primal:
//   x_e \in R
//   x(delta(v)) = 1, v = 0, ..., n-1
//   x(delta(U)) >= 1, odd set U
//   sum(w_e x_e) -> min
// Dual:
//   pi_U \in R for U = {v}
//   pi_U \in R_+ for odd set U, |U| >= 3
//   sum(pi_U) <= w_e, e \in delta(U)
//   sum(pi_U) -> max
// CSP:
//   x_e = 1 -> sum(pi_U) = w_e, e \in delta(U)
// CSD:
//   pi_U > 0 -> x(delta(U)) = 1 (i.e. U is blossom)

struct MinWeightedMatching {
    // Algorithm-wise constants.
    vector<vector<int>> Weights;
    int n;
    // Iteration-wise constants.
    set<int> BlossomPool;
    int TotalPi = 0;
    vector<int> Pi;
    vector<vector<int>> X;
    vector<vector<int>> AdjustedWeights;
    vector<bool> IsActive;
    vector<bool> IsExposed;
    vector<vector<int>> BlossomChildren;
    vector<int> BlossomParent;
    vector<vector<int>> BlossomDescendants;
    int Time = 0;
    int TotalX = 0;
    int ActiveCount = 0;
    // Iteration helper fields.
    vector<int> Level;
    vector<int> Timestamp;
    vector<int> Parent;

    void AssertConsistency() {
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                assert(AdjustedWeights[i][j] <= Infinity);
            }
        }
        for (int i = 0; i < 2 * n; i++) {
            assert(Pi[i] <= Infinity && Pi[i] >= -Infinity);
        }
        #ifndef HEAVY_ASSERT_CONSISTENCY
        return;
        #endif
        int actualTotalX = 0;
        for (int i = 0; i < 2 * n; i++) {
            for (int j = 0; j < i; j++) {
                actualTotalX += X[i][j];
            }
        }
        Assert(TotalX == actualTotalX, "TotalX: %d, actualTotalX: %d", TotalX, actualTotalX);

        int actualTotalPi = 0;
        for (int i = 0; i < 2 * n; i++) {
            actualTotalPi += Pi[i];
        }
        Assert(TotalPi == actualTotalPi, "TotalPi: %d, actualTotalPi: %d", TotalPi, actualTotalPi);

        for (int i = 0; i < n; i++) {
            for (int j = 0; j < i; j++) {
                int totalPi = 0;
                for (int b = 0; b < 2 * n; b++) {
                    auto descendants = GetBlossomDescendants(b);
                    if (count(descendants.begin(), descendants.end(), i) + count(descendants.begin(), descendants.end(), j) == 1) {
                        totalPi += Pi[b];
                    }
                }
                int actualAdjustedWeight = Weights[i][j] - totalPi;
                Assert(AdjustedWeights[i][j] == actualAdjustedWeight, "i: %d, j: %d, AdjustedWeights[i][j]: %d, actualAdjustedWeight: %d", i, j, AdjustedWeights[i][j], actualAdjustedWeight);
            }
        }

        for (int i = 0; i < 2 * n; i++) {
            int degree = 0;
            for (int j = 0; j < 2 * n; j++) {
                degree += X[i][j];
            }
            Assert(degree <= 1, "i: %d, degree: %d", i, degree);
            if (IsActive[i]) {
                Assert(IsExposed[i] == (degree == 0), "i: %d, IsExposed[i]: %d, degree: %d", i, (int)IsExposed[i], degree);
            }
        }

        for (int i = 0; i < 2 * n; i++) {
            for (int j = 0; j < 2 * n; j++) {
                Assert(X[i][j] == X[j][i], "i: %d, j: %d, X[i][j]: %d, X[j][i]: %d", i, j, X[i][j], X[j][i]);
            }
        }

        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                Assert(AdjustedWeights[i][j] == AdjustedWeights[j][i], "i: %d, j: %d, AdjustedWeights[i][j]: %d, AdjustedWeights[j][i]: %d", i, j, AdjustedWeights[i][j], AdjustedWeights[j][i]);
            }
        }

        for (int i = n; i < 2 * n; i++) {
            if (BlossomPool.count(i)) {
                continue;
            }
            int internalMatchingEdgeCount = 0;
            for (int j : BlossomChildren[i]) {
                for (int k : BlossomChildren[i]) {
                    if (j < k) {
                        internalMatchingEdgeCount += X[j][k];
                    }
                }
            }
            Assert(2 * internalMatchingEdgeCount + 1 == (int)BlossomChildren[i].size(), "i: %d, internalMatchingEdgeCount: %d, BlossomChildren[i].size(): %d", i, internalMatchingEdgeCount, (int)BlossomChildren[i].size());
        }

        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                Assert(X[i][j] == 0 || AdjustedWeights[i][j] == 0, "i: %d, j: %d, X[i][j]: %d, AdjustedWeights[i][j]: %d", i, j, X[i][j], AdjustedWeights[i][j]);
            }
        }
    }

    void LogState() {
        #ifndef DEBUG
        return;
        #endif
        eprintf("=== Iteration state ===\n");
        eprintf("Time: %d\n", Time);
        eprintf("TotalX: %d\n", TotalX);
        eprintf("TotalPi: %d\n", TotalPi);
        #ifdef VERBOSE
        eprintf("Active: ");
        for (int i = 0; i < 2 * n; i++) {
            if (IsActive[i]) {
                eprintf("%d ", i);
            }
        }
        eprintf("\n");
        eprintf("Exposed: ");
        for (int i = 0; i < 2 * n; i++) {
            if (IsExposed[i]) {
                eprintf("%d ", i);
            }
        }
        eprintf("\n");
        eprintf("Matching: ");
        for (int i = 0; i < 2 * n; i++) {
            for (int j = 0; j < i; j++) {
                if (X[i][j]) {
                    eprintf("(%d %d) ", i, j);
                }
            }
        }
        eprintf("\n");
        eprintf("Pi:\n");
        for (int i = 0; i < 2 * n; i++) {
            if (!BlossomPool.count(i)) {
                eprintf("%d: %d\n", i, Pi[i]);
            }
        }
        eprintf("Blossoms:\n");
        for (int i = n; i < 2 * n; i++) {
            if (!IsActive[i]) {
                continue;
            }
            eprintf("  %d: ", i);
            for (int j : BlossomChildren[i]) {
                eprintf("%d ", j);
            }
            eprintf("\n");
        }
        eprintf("AdjustedWeights:\n");
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                eprintf("%d ", AdjustedWeights[i][j]);
            }
            eprintf("\n");
        }
        #endif
        eprintf("=======================\n");
    }

    MinWeightedMatching(vector<vector<int>> weights) {
        Weights = move(weights);
        n = Weights.size();
        assert(n % 2 == 0);
        for (int i = n; i < 2 * n; i++) {
            BlossomPool.insert(i);
        }
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                Weights[i][j] *= 2;
            }
        }
        AdjustedWeights = Weights;
        Pi.resize(2 * n);
        X.resize(2 * n, vector<int>(2 * n, 0));
        Timestamp.resize(2 * n, 0);
        Level.resize(2 * n, -1);
        IsActive.resize(2 * n, false);
        IsExposed.resize(2 * n, false);
        for (int i = 0; i < n; i++) {
            IsActive[i] = IsExposed[i] = true;
        }
        X.resize(2 * n, vector<int>(2 * n, 0));
        Parent.resize(2 * n, -1);
        BlossomParent.resize(2 * n, -1);
        BlossomChildren.resize(2 * n);
        for (int i = 0; i < n; i++) {
            BlossomChildren[i] = {i};
        }
        BlossomDescendants.resize(2 * n);
        for (int i = 0; i < n; i++) {
            BlossomDescendants[i] = {i};
        }
        ActiveCount = n;
    }

    int AllocateBlossom() {
        assert(!BlossomPool.empty());
        int blossomId = *BlossomPool.begin();
        BlossomPool.erase(blossomId);
        eprintf("Blossom allocated (blossomId: %d)\n", blossomId);
        BlossomChildren[blossomId].clear();
        return blossomId;
    }

    void FreeBlossom(int blossomId) {
        assert(BlossomPool.insert(blossomId).second);
        eprintf("Blossom freed (blossomId: %d)\n", blossomId);
    }

    void VisitBlossomDescendants(int v, vector<int>& result) {
        result.push_back(v);
        if (v < n) {
            return;
        }
        for (int i : BlossomChildren[v]) {
            VisitBlossomDescendants(i, result);
        }
    }

    vector<int> GetBlossomDescendants(int v) {
        vector<int> result;
        VisitBlossomDescendants(v, result);
        return result;
    }

    vector<int> BlossomParents(int v) {
        vector<int> result;
        for (int i = v; i != -1; i = BlossomParent[v]) {
            result.push_back(i);
        }
        return result;
    }

    int BlossomAdjustedWeight(int v, int u) {
        const auto& descendantsV = BlossomDescendants[v];
        const auto& descendantsU = BlossomDescendants[u];
        int result = Infinity;
        for (int i : descendantsV) {
            for (int j : descendantsU) {
                if (i >= n || j >= n) {
                    continue;
                }
                if (result > AdjustedWeights[i][j]) {
                    result = AdjustedWeights[i][j];
                }
            }
        }
        return result;
    }

    int DFSResultV, DFSResultU;
    // 0 - did not find alternating path nor blossom
    // 1 - found alternating path u -> Parent[u] -> ... .
    // 2 - found blossom u -> Parent[u] -> ... && v -> Parent[u] -> ...
    int DFS(int v, int level) {
        Timestamp[v] = Time;
        Level[v] = level;
        Assert(IsExposed[v] == (level == 0), "v: %d, level: %d", v, level);
        for (int u = 0; u < 2 * n; u++) {
            if (!IsActive[u]) {
                continue;
            }
            if (u == v) {
                continue;
            }
            if (BlossomAdjustedWeight(v, u) != 0) {
                continue;
            }
            Assert(X[v][u] == 0 || level % 2 == 1 || u == Parent[v], "v: %d, u: %d, X[v][u]: %d, level: %d", v, u, X[v][u], level);
            if (X[v][u] == 0 && level % 2 == 1) {
                continue;
            }
            if (Timestamp[u] != Time) {
                Parent[u] = v;
                if (IsExposed[u]) {
                    DFSResultU = u;
                    return 1;
                }
                if (int result = DFS(u, level + 1)) {
                    return result;
                }
            } else {
                if (Level[u] % 2 == 0 && Level[v] % 2 == 0) {
                    DFSResultU = u;
                    DFSResultV = v;
                    return 2;
                }
            }
        }
        return 0;
    }

    void Alternate(int v, int u) {
        eprintf("Found alternating path (v: %d, u: %d, TotalX: %d -> %d)\n", v, u, TotalX, TotalX + 1);
        eprintf("! Alternating path: \n");
        for (int i = u; i != v; i = Parent[i]) {
            X[i][Parent[i]] ^= 1;
            X[Parent[i]][i] ^= 1;
            eprintf("%d ", i);
        }
        eprintf("%d\n", v);
        IsExposed[v] = IsExposed[u] = false;
        TotalX++;
        eprintf("Path alternated\n");
    }

    void ShrinkBlossom(int v, int u) {
        eprintf("Found blossom (v: %d, u: %d)\n", v, u);
        int lca = -1;
        for (int i = v, j = u; ; ) {
            if (i == j) {
                lca = i;
                break;
            }
            if (Level[i] >= Level[j]) {
                i = Parent[i];
            }
            if (Level[j] > Level[i]) {
                j = Parent[j];
            }
        }
        eprintf("Found lowest common ancestor (lca: %d)\n", lca);
        int blossomId = AllocateBlossom();
        auto& children = BlossomChildren[blossomId];
        children = {lca};
        for (int i = v; i != lca; i = Parent[i]) {
            children.push_back(i);
        }
        reverse(children.begin() + 1, children.end());
        for (int i = u; i != lca; i = Parent[i]) {
            children.push_back(i);
        }
        eprintf("! Blossom: ");
        for (int i : children) {
            IsActive[i] = false;
            BlossomParent[i] = blossomId;
            IsExposed[i] = false;
            eprintf("%d ", i);
        }
        eprintf("\n");
        IsActive[blossomId] = true;
        if (Parent[lca] == -1) {
            IsExposed[blossomId] = true;
        } else {
            Assert(X[lca][Parent[lca]], "lca: %d, Parent[lca]: %d, X[lca][Parent[lca]]: %d", lca, Parent[lca], X[lca][Parent[lca]]);
            IsExposed[blossomId] = false;
            X[lca][Parent[lca]] = X[Parent[lca]][lca] = 0;
            X[blossomId][Parent[lca]] = X[Parent[lca]][blossomId] = 1;
        }
        const auto& descendants = BlossomDescendants[blossomId];
        vector<bool> isDescendant(2 * n, false);
        for (int i : descendants) {
            isDescendant[i] = true;
        }
        eprintf("Blossom shirnked (BlossomId: %d)\n", blossomId);
    }

    void ModifyDualSolution(int epsilon) {
        eprintf("Modifying dual solution (epsilon: %d)\n", epsilon);
        auto getDelta = [&] (int v) {
            if (Timestamp[v] != Time) {
                return 0;
            } else if (Level[v] % 2 == 0) {
                return epsilon;
            } else {
                return -epsilon;
            }
        };
        for (int i = 0; i < 2 * n; i++) {
            if (!IsActive[i]) {
                continue;
            }
            int deltaI = getDelta(i);
            Pi[i] += deltaI;
            TotalPi += deltaI;
            const auto& descendantsI = BlossomDescendants[i];
            for (int j = 0; j < 2 * n; j++) {
                if (!IsActive[j]) {
                    continue;
                }
                if (i == j) {
                    continue;
                }
                int deltaJ = getDelta(j);
                auto descendantsJ = BlossomDescendants[j];
                for (int di : descendantsI) {
                    for (int dj : descendantsJ) {
                        if (di < n && dj < n && di != dj) {
                            Assert(AdjustedWeights[di][dj] >= deltaI + deltaJ, "di: %d, dj: %d, AdjustedWeights[di][dj]: %d, deltaI: %d, deltaJ: %d", di, dj, AdjustedWeights[di][dj], deltaI, deltaJ);
                            AdjustedWeights[di][dj] -= deltaI + deltaJ;
                        }
                    }
                }
            }
        }
    }

    void DeShrinkBlossom(int blossomId) {
        eprintf("De-shrinking blossom (blossomId: %d)\n", blossomId);
        const auto& children = BlossomChildren[blossomId];
        int k = children.size();
        for (int i : children) {
            for (int j = 0; j < 2 * n; j++) {
                X[i][j] = X[j][i] = 0;
            }
        }
        int rootParent = -1;
        for (int i = 0; i < 2 * n; i++) {
            if (X[i][blossomId]) {
                assert(rootParent == -1);
                rootParent = i;
                X[i][blossomId] = X[blossomId][i] = 0;
            }
        }
        Assert(rootParent != -1, "rootParent: %d", rootParent);
        int root = -1, minimumAdjustedWeight = Infinity;
        for (int i : children) {
            int adjustedWeight = BlossomAdjustedWeight(rootParent, i);
            if (adjustedWeight < minimumAdjustedWeight) {
                minimumAdjustedWeight = adjustedWeight;
                root = i;
            }
        }
        assert(root != -1);
        eprintf("Blossom round found (rootParent: %d, root: %d)\n", rootParent, root);
        X[rootParent][root] = X[root][rootParent] = 1;
        int position = find(children.begin(), children.end(), root) - children.begin();
        assert(position < k);
        for (int i = position + 1; i < position + k; i += 2) {
            int v = children[i % k];
            int u = children[(i + 1) % k];
            X[v][u] = X[u][v] = true;
        }
        for (int i : children) {
            assert(!IsActive[i]);
            IsActive[i] = true;
            BlossomParent[i] = -1;
        }
        IsActive[blossomId] = false;
        eprintf("Blossom de-shrinked\n");
        FreeBlossom(blossomId);
    }

    void MakeDualStep() {
        eprintf("Making dual step\n");
        int oddBlossomLimit = Infinity;
        int tightestOddBlossomId = -1;
        int evenEvenLimit = Infinity;
        int tightestEvenEvenV = -1, tightestEvenEvenU = -1;
        int evenOutLimit = Infinity;
        int tightestEvenOutV = -1, tightestEvenOutU = -1;

        for (int i = 0; i < 2 * n; i++) {
            if (Timestamp[i] != Time) {
                continue;
            }
            if (i >= n && Level[i] % 2 == 1) {
                if (oddBlossomLimit > Pi[i]) {
                    oddBlossomLimit = Pi[i];;
                    tightestOddBlossomId = i;
                }
            }
            if (Level[i] % 2 == 1) {
                continue;
            }
            for (int j = 0; j < 2 * n; j++) {
                if (!IsActive[j]) {
                    continue;
                }
                if (i == j) {
                    continue;
                }
                int adjustedWeight = BlossomAdjustedWeight(i, j);
                if (Timestamp[j] == Time && Level[j] % 2 == 0) {
                    Assert(adjustedWeight % 2 == 0, "i: %d, j: %d, adjustedWeight: %d", i, j, adjustedWeight);
                    if (evenEvenLimit > adjustedWeight / 2) {
                        evenEvenLimit = adjustedWeight / 2;
                        tightestEvenEvenV = i;
                        tightestEvenEvenU = j;
                    }
                }
                if (Timestamp[j] != Time) {
                    if (evenOutLimit > adjustedWeight) {
                        evenOutLimit = adjustedWeight;
                        tightestEvenOutV = i;
                        tightestEvenOutU = j;
                    }
                }
            }
        }
        eprintf("Tightest odd blossom (BlossomId: %d, Limit: %d)\n", tightestOddBlossomId, oddBlossomLimit);
        eprintf("Tightest even-even edge (v: %d, u: %d, Limit: %d)\n", tightestEvenEvenV, tightestEvenEvenU, evenEvenLimit);
        eprintf("Tightest even-out edge (v: %d, u: %d Limit: %d)\n", tightestEvenOutV, tightestEvenOutU, evenOutLimit);
        Assert(oddBlossomLimit < Infinity / 2 || evenOutLimit < Infinity / 2 || evenEvenLimit < Infinity / 2, "see above%s", "");
        int limit = min({oddBlossomLimit, evenEvenLimit, evenOutLimit});
        ModifyDualSolution(limit);
        if (oddBlossomLimit == limit) {
            Assert(Pi[tightestOddBlossomId] == 0, "tightestOddBlossomId: %d, Pi[tightestOddBlossomId]: %d", tightestOddBlossomId, Pi[tightestOddBlossomId]);
            DeShrinkBlossom(tightestOddBlossomId);
        }
    }

    bool MakePrimalStep() {
        eprintf("Trying to make primal step\n");
        for (int v = 0; v < 2 * n; v++) {
            if (!IsActive[v]) {
                continue;
            }
            if (!IsExposed[v]) {
                continue;
            }
            if (Timestamp[v] == Time) {
                continue;
            }
            #ifdef VERBOSE
            eprintf("Running DFS (v: %d)\n", v);
            #endif
            Parent[v] = -1;
            switch (int result = DFS(v, 0)) {
                case 1:
                    Alternate(v, DFSResultU);
                    return true;
                case 2:
                    ShrinkBlossom(DFSResultV, DFSResultU);;
                    return true;
                case 0:
                    break;
            }
        }
        eprintf("Did not find alternating path nor blossom\n");
        return false;
    }

    void InitIteration() {
        for (int i = n; i < 2 * n; i++) {
            if (BlossomPool.count(i)) {
                continue;
            }
            BlossomDescendants[i] = GetBlossomDescendants(i);
        }
    }

    void MakeIteration() {
        Time++;
        eprintf("Iteration started (Time: %d)\n", Time);
        InitIteration();
        if (MakePrimalStep()) {
            return;
        }
        MakeDualStep();
    }

    vector<pair<int, int>> Run() {
        while (true) {
            LogState();
            AssertConsistency();
            if (2 * TotalX == n) {
                break;
            }
            MakeIteration();
        }
        eprintf("Alogrithm finished, de-shrinking blossoms\n");
        for (int i = n; i < 2 * n; i++) {
            if (IsActive[i]) {
                auto descendants = BlossomDescendants[i];
                for (int j : descendants) {
                    if (j >= n) {
                        LogState();
                        DeShrinkBlossom(j);
                    }
                }
            }
        }
        LogState();
        Assert(2 * TotalX == n, "TotalX: %d, n: %d", TotalX, n);
        vector<pair<int, int>> result;
        int totalCost = 0;
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < i; j++) {
                if (X[i][j]) {
                    result.emplace_back(i, j);
                    totalCost += Weights[i][j];
                }
            }
        }
        Assert(totalCost == TotalPi, "totalCost: %d, TotalPi: %d", totalCost, TotalPi);
        return result;
    }
};

int Bruteforce(int i, const vector<vector<int>>& weights, vector<bool>& used, int currentSum) {
    while (i < (int)used.size() && used[i]) {
        ++i;
    }
    if (i == (int)used.size()) {
        return currentSum;
    }
    int result = Infinity;
    used[i] = true;
    for (int j = 0; j < (int)used.size(); j++) {
        if (used[j]) {
            continue;
        }
        used[j] = true;
        result = min(result, Bruteforce(i + 1, weights, used, currentSum + weights[i][j]));
        used[j] = false;
    }
    used[i] = false;
    return result;
}

int Naive(const vector<vector<int>>& weights) {
    vector<bool> used(weights.size(), false);
    return Bruteforce(0, weights, used, 0);
}

int main() {
    int n;
    scanf("%d", &n);
    vector<vector<int>> weights;
    for (int i = 0; i < n; i++) {
        weights.emplace_back();
        for (int j = 0; j < n; j++) {
            int w;
            scanf("%d", &w);
            weights.back().push_back(w);
        }
    }

    auto matching = MinWeightedMatching(weights);
    auto result = matching.Run();
    Assert(matching.TotalPi % 2 == 0, "TotalPi: %d", matching.TotalPi);
    printf("%d\n", matching.TotalPi / 2);
    for (auto pair : result) {
        printf("%d %d\n", pair.first, pair.second);
    }
#ifdef NAIVE
    int naiveMatching = Naive(weights);
    Assert(matching.TotalPi / 2 == naiveMatching, "TotalPi / 2: %d, naiveMatching: %d", matching.TotalPi / 2, naiveMatching);
#endif
}
