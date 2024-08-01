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
bfs(int root, vector<int> &dep, vector<int> &l, vector<vector<int>> &edge, int n) {
    queue<int> q;
    for (int i = 1; i <= n; i++) dep[i] = n + 5;
    q.push(root);
    l[root] = dep[root] = 0;
    vector<int> du(n + 1, 0);
    for (int i = 1; i <= n; i++) {
        for (auto v: edge[i]) {
            du[v]++;
        }
    }
    while (!q.empty()) {
        int x = q.front();
        q.pop();
        for (int i = 0; i < edge[x].size(); i++) {
            int y = edge[x][i];
            du[y]--;
            l[y] = dep[y] = min(dep[y], dep[x] + 1);
            if (du[y] == 0) q.push(y);
        }
    }
}

string tmp;

double
single_calp(int x, int r, vector<bool> &is_can, vector<double> &pyes, vector<double> &pr, vector<vector<int>> &edge,
            vector<double> &val, vector<int> &l) {
    if (!is_can[x]) return 0;
    pyes[x] = pr[x];
    double sum_r = val[x] * (l[x] - l[r]);
    for (int i = 0; i < edge[x].size(); i++) {
        int y = edge[x][i];
        if (!is_can[y]) continue;
        sum_r += single_calp(y, r, is_can, pyes, pr, edge, val, l);
        pyes[x] += pyes[y];
    }
    return sum_r;
}

pair<double, int> BinG_calg(int x, double psum, vector<bool> &is_can, vector<double> &pyes, vector<vector<int>> &edge) {
    double ma = min(pyes[x], psum - pyes[x]);
    int id = x;
    for (int i = 0; i < edge[x].size(); i++) {
        int y = edge[x][i];
        if (!is_can[y]) continue;
        pair<double, int> tmp = BinG_calg(y, psum, is_can, pyes, edge);
        if (tmp.first > ma) {
            ma = tmp.first, id = tmp.second;
        }
    }
    return {ma, id};
}

pair<int, int> single_question_BinG(int root, int n, vector<int> &ask_yes, vector<double> &pyes, vector<vector<int>> &G,
                                    vector<double> &pr, vector<double> &val, vector<int> &l) {
    int r = root;
    double psum = 1;
    vector<bool> is_ask(n + 1, false);
    int cnt = 0;
    vector<bool> is_can(n + 1, true);
    while (true) {
        single_calp(r, r, is_can, pyes, pr, G, val, l);
        int x = BinG_calg(r, psum, is_can, pyes, G).second;
        if (is_ask[x]) {
            break;
        }
        is_ask[x] = true;
        cnt++;
        if (ask(x, ask_yes)) { r = x, psum = pyes[r]; }
        else { is_can[x] = false, psum = pyes[r] - pyes[x]; }
    }
    return {r, cnt};
}

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

    string query_log = "BinG_" + tmp + "_query_log.txt";
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
        vector<int> l(n + 2), dep(n + 2);
        vector<double> val(n + 2);
        vector<double> pr(n + 2);
        vector<double> pyes(n + 2);
        bfs(rt, dep, l, spanning_tree, n + 1);
        for (int i = 1; i <= n + 1; i++) {
            val[i] = 1;
            pr[i] = 1.0 / (n + 1);
        }
        auto [my_target, query_cnt] = single_question_BinG(rt, n + 1, ask_yes, pyes, spanning_tree, pr, val, l);
        cout << "query #" << __ << ":" << "\n";
        double qu_ed = 1.0 * clock() / CLOCKS_PER_SEC;
        double qu_cost = qu_ed - qu_st;
        sum_query_time += qu_cost;
        sum += query_cnt;
        average_query_cnt = sum / __;
        max_query_cnt = max(max_query_cnt, query_cnt);
        minn_query_cnt = min(minn_query_cnt, query_cnt);
        cout << "my_target: " << my_target << "   answer_target: " << target[0] << "\n";
        cout << "query_cnt: " << query_cnt << "\n"<<"\n";
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

