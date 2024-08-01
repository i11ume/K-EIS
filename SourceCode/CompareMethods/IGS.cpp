#pragma GCC optimize(3)

#include <bits/stdc++.h>

using namespace std;

typedef long long ll;
typedef unsigned long long ull;

#define debug(x...)             \
    do {                      \
        cout << #x << " -> ";\
        err(x);               \
    } while (0)

void err() {
    cout << endl;
}

template<class T, class... Ts>
void err(const T &arg, const Ts &... args) {
    cout << arg << ' ';
    err(args...);
}

const ll LINF = 0x3f3f3f3f3f3f3f3f;
const int INF = 0x3f3f3f3f;//2147483647;
const ll MOD[2] = {1000000007, 998244353};
const ll BASE[2] = {131, 13331};
const double pi = acos(-1.0);

const int N = 2e5 + 10, M = N << 1;
const ll mod = MOD[0];

vector<pair<int, int>> seq;
map<int, int> CandidatesSize;

int ask(int x, vector<int> &ask_yes) {
//    debug(x);
    seq.emplace_back(x, ask_yes[x]);
    if (ask_yes[x])return 1;
    return 0;
}

void deal_Candidates(int n, vector<vector<int>> &G) {
    unordered_map<int, int> P;
    for (int i = 1; i <= n; i++) {
        P[i] = 1;
    }
    CandidatesSize[0] += n;
    for (int i = 0; i < seq.size(); i++) {
        auto [x, ret] = seq[i];
        queue<int> q;
        q.push(x);
        vector<int> vis(n + 2);
        vis[x] = 1;
        while (!q.empty()) {
            int u = q.front();
            q.pop();
            for (auto v: G[u]) {
                if (vis[v])continue;
                vis[v] = 1;
                q.push(v);
            }
        }
        if (ret) {
            for (int j = 1; j <= n; j++) {
                if (vis[j]) P[j]++;
            }
        } else {
            for (int j = 1; j <= n; j++) {
                if (!vis[j]) P[j]++;
            }
        }
        unordered_map<int, int> tmp;
        for (auto [u, val]: P) {
            if (val == 2) {
                tmp[u] = 1;
            }
        }
        P = tmp;
        CandidatesSize[i + 1] += (int) P.size();
    }
}

void init_query(int cur, vector<int> &ask_yes, vector<vector<int>> &Graph) {
    ask_yes[cur] = 1;
    for (auto v: Graph[cur]) {
        if (!ask_yes[v]) {
            init_query(v, ask_yes, Graph);
        }
    }
}

void spanTree(int x, vector<vector<int>> &G, vector<vector<int>> &st, vector<int> &vis) {
    vector<pair<int, int>> children;
    for (auto v: G[x]) {
        if (vis[v])continue;
        queue<int> q;
        stack<int> stk;
        vis[v] = 1;
        stk.push(v);
        q.push(v);
        while (!q.empty()) {
            int cur = q.front();
            q.pop();
            for (auto to: G[cur]) {
                if (vis[to])continue;
                vis[to] = 1;
                stk.push(to);
                q.push(to);
            }
        }
        children.push_back({-stk.size(), v});
        while (!stk.empty()) {
            vis[stk.top()] = 0;
            stk.pop();
        }
    }
    sort(children.begin(), children.end());
    for (auto [num, id]: children) {
        if (vis[id])continue;
        vis[id] = 1;
        st[x].push_back(id);
//        debug(x, id);
        spanTree(id, G, st, vis);
    }
}

void
dfs1(int x, int root, vector<int> &dep, vector<int> &sz, vector<vector<int>> &edge, vector<int> &fa, vector<int> &son) {
    sz[x] = 1;
    if (x != root) dep[x] = dep[fa[x]] + 1;
    int ma = 0, heavy_son = x;
    for (int i = 0; i < edge[x].size(); i++) {
        int y = edge[x][i];
        if (y == fa[x]) continue;
        dfs1(y, root, dep, sz, edge, fa, son);
        sz[x] += sz[y];
        if (sz[y] > ma) {
            ma = sz[y], heavy_son = y;
        }
    }
    son[x] = heavy_son;
}

void dfs2(int x, int tp, vector<int> &top, vector<vector<int>> &heavy, vector<int> &son, vector<int> &fa,
          vector<vector<int>> &edge) {
    top[x] = tp;
    heavy[tp].push_back(x);
    if (son[x] != x) dfs2(son[x], tp, top, heavy, son, fa, edge);
    for (int i = 0; i < edge[x].size(); i++) {
        int y = edge[x][i];
        if (y == fa[x] || y == son[x]) continue;
        dfs2(y, y, top, heavy, son, fa, edge);
    }
}


int question_IGS_dfs(int tmp, int &cnt, vector<vector<int>> &heavy, vector<int> &ask_yes, vector<vector<int>> &edge) {
//    if (cnt >= B) return tmp;
    //cout << tmp << endl;
    int len = heavy[tmp].size();
    //cout << len << endl;

    int l = 0, r = len - 1;
    int ans = -1;
    while (l <= r) {
        int mid = (l + r) >> 1;
        int mid_node = heavy[tmp][mid];
        cnt++;
        if (ask(mid_node, ask_yes)) {
            l = mid + 1;
            ans = mid;
        } else r = mid - 1;
    }
    int x = heavy[tmp][ans];
    for (int i = 1; i < (int) edge[x].size(); i++) {
        int y = edge[x][i];
        cnt++;
        if (ask(y, ask_yes)) {
//          if (cnt >= B) return y;
            return question_IGS_dfs(y, cnt, heavy, ask_yes, edge);
        }
    }
    return x;
}

string tmp;

void solve() {
    string ss = tmp + ".txt";
    freopen(ss.c_str(), "r", stdin);
    int n, m;
    cin >> n >> m;
    vector<vector<int>> G(n + 2);
    vector<vector<int>> revG(n + 2);
    // 读入图
    for (int i = 1, u, v; i <= m; i++) {
        cin >> u >> v;
        G[u].push_back(v);
        revG[v].push_back(u);
    }
    // root 向入度为0的点连边
    int rt = n + 1;
    for (int i = 1; i <= n; i++) {
        if (revG[i].empty()) {
            G[rt].push_back(i);
            revG[i].push_back(rt);
        }
    }
    //读入目标集，此时已知目标数量为 1

    string query_ss = tmp + "_query.txt";
    freopen(query_ss.c_str(), "r", stdin);

    string query_log = "IGS_" + tmp + "_query_log.txt";
    freopen(query_log.c_str(), "w", stdout);

    int TestCase;
    cin >> TestCase;
    double sum = 0, average_query_cnt = 0;
    int max_query_cnt = 0, minn_query_cnt = n + 1;
    double sum_query_time = 0;
    for (int __ = 1; __ <= TestCase; __++) {
        int targetNumber;
        cin >> targetNumber;
        vector<int> target;
        vector<int> vis_target(n + 2, 0);
        vector<int> ask_yes(n + 2, 0);
        for (int i = 1, x; i <= targetNumber; i++) {
            cin >> x;
            target.push_back(x);
            vis_target[x] = ask_yes[x] = 1;
        }
        double qu_st = 1.0 * clock() / CLOCKS_PER_SEC;
        // init_query()  O(n)
        for (auto i: target) {
            init_query(i, ask_yes, revG);
        }

        vector<vector<int>> spanning_tree(n + 2);
        vector<int> vis_stree(n + 2);
        vis_stree[rt] = 1;
        spanTree(rt, G, spanning_tree, vis_stree);
        vector<int> depth(n + 2), son(n + 2), top(n + 2), fa(n + 2), sz(n + 2);
        vector<vector<int>> heavy_chain(n + 2);
        dfs1(rt, rt, depth, sz, spanning_tree, fa, son);
        dfs2(rt, rt, top, heavy_chain, son, fa, spanning_tree);
        int query_cnt = 0;
        int my_target = question_IGS_dfs(rt, query_cnt, heavy_chain, ask_yes, spanning_tree);
        cout << "query #" << __ << ":" << "\n";
        double qu_ed = 1.0 * clock() / CLOCKS_PER_SEC;
        double qu_cost = qu_ed - qu_st;
        sum_query_time += qu_cost;
        sum += query_cnt;
        average_query_cnt = sum / __;
        max_query_cnt = max(max_query_cnt, query_cnt);
        minn_query_cnt = min(minn_query_cnt, query_cnt);
        cout << "my_target: " << my_target << "   answer_target: " << target[0] << "\n";
        cout << "query_cnt: " << query_cnt << "\n\n";
        deal_Candidates(n, G);
        seq.clear();
    }
    cout << "max_query_cnt: " << max_query_cnt << "\n";
    cout << "min_query_cnt: " << minn_query_cnt << "\n";
    cout << "avg_query_cnt: " << fixed << setprecision(8) << average_query_cnt << "\n";
    cout << "avg_cost: " << fixed << setprecision(8) << sum_query_time / TestCase << "\n" << endl;

    cout << "PotentialTargetSize: \n";
    for (auto [cur_query_cnt, PSize]: CandidatesSize) {
        cout << cur_query_cnt << " " << 1.0 * PSize / TestCase << "\n";
    }
}

signed main(int argc, char *argv[]) {
    ios::sync_with_stdio(false), cin.tie(nullptr);
    tmp = argv[1];
    solve();
    return 0;
}
/*
 14 16
 1 2
 1 3
 2 3
 2 4
 2 5
 3 8
 3 13
 4 6
 4 7
 4 8
 5 9
 8 10
 8 11
 9 12
 9 13
 12 14
 1
 1
 9

*/

