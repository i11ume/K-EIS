#include <future>

#pragma GCC optimize(3)

#include <bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/hash_policy.hpp>

using namespace __gnu_pbds;

class ThreadPool {
public:
    ThreadPool(size_t);

    template<class F, class... Args>
    auto enqueue(F &&f, Args &&... args)
    -> std::future<typename std::result_of<F(Args...)>::type>;

    ~ThreadPool();

private:
    // need to keep track of threads so we can join them
    std::vector<std::thread> workers;
    // the task queue
    std::queue<std::function<void()>> tasks;

    // synchronization
    std::mutex queue_mutex;
    std::condition_variable condition;
    bool stop;
};

// the constructor just launches some amount of workers
inline ThreadPool::ThreadPool(size_t threads) : stop(false) {
    for (size_t i = 0; i < threads; ++i)
        workers.emplace_back([this] {
            for (;;) {
                std::function<void()> task;

                {
                    std::unique_lock<std::mutex> lock(this->queue_mutex);
                    this->condition.wait(
                            lock, [this] { return this->stop || !this->tasks.empty(); });
                    if (this->stop && this->tasks.empty())
                        return;
                    task = std::move(this->tasks.front());
                    this->tasks.pop();
                }

                task();
            }
        });
}

// add new work item to the pool
template<class F, class... Args>
auto ThreadPool::enqueue(F &&f, Args &&... args)
-> std::future<typename std::result_of<F(Args...)>::type> {
    using return_type = typename std::result_of<F(Args...)>::type;

    auto task = std::make_shared<std::packaged_task<return_type()>>(
            std::bind(std::forward<F>(f), std::forward<Args>(args)...));

    std::future<return_type> res = task->get_future();
    {
        std::unique_lock<std::mutex> lock(queue_mutex);

        // don't allow enqueueing after stopping the pool
        if (stop)
            throw std::runtime_error("enqueue on stopped ThreadPool");

        tasks.emplace([task]() { (*task)(); });
    }
    condition.notify_one();
    return res;
}

// the destructor joins all threads
inline ThreadPool::~ThreadPool() {
    {
        std::unique_lock<std::mutex> lock(queue_mutex);
        stop = true;
    }
    condition.notify_all();
    for (std::thread &worker: workers)
        worker.join();
}

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

int ask(int x, vector<int> &ask_yes) {
//    debug(x, ask_yes[x]);
    if (ask_yes[x])return 1;
    return 0;
}

void init_query(int cur, vector<int> &ask_yes, vector<vector<int>> &Graph) {
    ask_yes[cur] = 1;
    for (auto v: Graph[cur]) {
        if (!ask_yes[v]) {
            init_query(v, ask_yes, Graph);
        }
    }
}

map<int, int> CandidatesSize;

void deal_Candidates(int n, vector<vector<int>> &G, int &ptsize, int cnt, vector<pair<int, int>> &seq) {
    int cur = n;
    unordered_map<int, int> P;
    for (int i = 1; i <= n; i++) {
        P[i] = 1;
    }
    for (int i = 0; i < seq.size(); i++) {
        auto [x, ret] = seq[i];
//        debug(x,ret);
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
        ptsize = ptsize - cur + (int) P.size();
        cur = (int) P.size();
        CandidatesSize[cnt + 1] += ptsize;
        cnt++;
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


int question_IGS_dfs(int tmp, int &cnt, vector<vector<int>> &heavy, vector<int> &ask_yes, vector<vector<int>> &edge,
                     vector<int> &rmp, vector<pair<int, int>> &seq) {
    int len = heavy[tmp].size();
//    debug(tmp);
    int l = 0, r = len - 1;
    int ans = -1;
    while (l <= r) {
        int mid = (l + r) >> 1;
        int mid_node = heavy[tmp][mid];
//        debug(l, r, mid, mid_node);
        cnt++;
        if (ask(rmp[mid_node], ask_yes)) {
            l = mid + 1;
            ans = mid;
            seq.emplace_back(mid_node, true);
        } else {
            r = mid - 1;
            seq.emplace_back(mid_node, false);
        }
    }
//    debug(heavy[tmp][ans], ans);
    int x = heavy[tmp][ans];
    for (int i = 1; i < (int) edge[x].size(); i++) {
        int y = edge[x][i];
        cnt++;
        if (ask(rmp[y], ask_yes)) {
//          if (cnt >= B) return y;
            seq.emplace_back(y, true);
            return question_IGS_dfs(y, cnt, heavy, ask_yes, edge, rmp, seq);
        } else {
            seq.emplace_back(y, false);
        }
    }
    return x;
}

int IGS(int n, vector<int> &ask_yes, vector<vector<int>> &G, vector<vector<int>> &revG, vector<int> &rmp, int &cnt,
        int &ptsize) {
    int rt = n + 1;
    ask_yes[0] = 1;
    rmp[rt] = 0;
    vector<vector<int>> spanning_tree(n + 2);
    vector<int> vis_stree(n + 2);
    vis_stree[rt] = 1;
    spanTree(rt, G, spanning_tree, vis_stree);
    vector<int> depth(n + 2), son(n + 2), top(n + 2), fa(n + 2), sz(n + 2);
    vector<vector<int>> heavy_chain(n + 2);
    dfs1(rt, rt, depth, sz, spanning_tree, fa, son);
    dfs2(rt, rt, top, heavy_chain, son, fa, spanning_tree);

    int query_cnt = 0;
    vector<pair<int, int>> seq;
    int my_target = question_IGS_dfs(rt, query_cnt, heavy_chain, ask_yes, spanning_tree, rmp, seq);

//    debug(n, my_target, rmp[my_target]);
    deal_Candidates(n, G, ptsize, cnt, seq);
    cnt += query_cnt;
    return rmp[my_target];
}


void dfs(int x, vector<vector<int>> &G, vector<int> &cnt0, vector<int> &col) {
    cnt0[x] = 1;
    for (auto v: G[x]) {
        if (col[v] != -1)continue;
        if (!cnt0[v]) {
            dfs(v, G, cnt0, col);
        }
        cnt0[x] += cnt0[v];
    }
}

void
multi_calc_yes(vector<int> &col, vector<vector<int>> &G, vector<vector<int>> &revG, int n, int x,
               vector<int> &U,
               vector<vector<bool>> &GReach,
               vector<vector<bool>> &revGReach) {
    col[x] = 1;
    unordered_map<int, bool> mp;
    mp[x] = true;
    for (auto v: U) {
        if (revGReach[x][v]) {
            col[v] = 1;
            mp[v] = true;
        }
    }
    vector<int> tmp;
    for (auto v: U) {
        if (!mp.count(v)) {
            tmp.push_back(v);
        }
    }
    U = tmp;
}

void
multi_calc_no(vector<int> &col, vector<vector<int>> &G, vector<vector<int>> &revG, int n, int x,
              vector<int> &U,
              vector<vector<bool>> &GReach,
              vector<vector<bool>> &revGReach) {
    col[x] = 0;
    unordered_map<int, bool> mp;
    mp[x] = true;
    for (auto v: U) {
        if (GReach[x][v]) {
            col[v] = 0;
            mp[v] = true;
        }
    }
    vector<int> tmp;
    for (auto v: U) {
        if (!mp.count(v)) {
            tmp.push_back(v);
        }
    }
    U = tmp;
}

int find(int x, vector<int> &fa) {
    if (fa[x] == x)return x;
    return fa[x] = find(fa[x], fa);
}

pair<int, vector<int>>
multi_select(int n, int K, vector<int> &col, vector<int> &ask_yes, vector<vector<int>> &G,
             vector<vector<int>> &revG, vector<int> &U,
             vector<vector<bool>> &GReach,
             vector<vector<bool>> &revGReach
) {
    int cnt = 0;
    while (!U.empty()) {
        // Check the number of the connected components
        vector<int> key_yes;
        vector<int> key_vis(n + 2, 0);
        for (int i = 1; i <= n + 1; i++) {
            if (col[i] == 1) {
                int flag = 0;
                for (auto v: G[i]) {
                    if (col[v] == 1) {
                        flag = 1;
                        break;
                    }
                }
                if (!flag) {
                    key_yes.push_back(i);
                    key_vis[i] = 1;
                }
            }
        }
        vector<int> fa(n + 2);
        for (int i = 1; i <= n + 1; i++) {
            fa[i] = i;
        }
        for (auto i: key_yes) {
            queue<int> q;
            q.push(i);
            while (!q.empty()) {
                int u = q.front();
                q.pop();
                for (auto v: G[u]) {
                    if (col[v] != -1)continue;
                    int fx = find(u, fa), fy = find(v, fa);
                    if (fx != fy) {
                        fa[fx] = fy;
                        q.push(v);
                    }
                }
            }
        }
        int idx = 0;
        unordered_map<int, int> mp_idx;
        for (int i = 1; i <= n + 1; i++) {
            if (!mp_idx.count(find(i, fa)))mp_idx[find(i, fa)] = ++idx;
        }
        vector<vector<int>> Comp(idx + 1);
        for (int i = 1; i <= n + 1; i++) {
            Comp[mp_idx[find(i, fa)]].push_back(i);
        }
        vector<int> Comp_id;
        for (int i = 1; i <= idx; i++) {
            int flag = 0;
            for (auto v: Comp[i]) {
                if (key_vis[v]) {
                    flag = 1;
                    break;
                }
            }
            if (flag) Comp_id.push_back(i);
        }
        if (Comp_id.size() == K) {
            idx = (int) Comp_id.size();
            vector<vector<vector<int>>> subG(idx + 1);
            vector<vector<vector<int>>> subrevG(idx + 1);
            vector<vector<int>> comp(idx + 1);
            vector<int> vis(n + 2);
            for (int i = 0; i < idx; i++) {
                comp[i + 1] = Comp[Comp_id[i]];
                for (auto v: comp[i + 1]) {
                    vis[v] = i + 1;
                }
            }
            for (int i = 1; i <= n + 1; i++) {
                if (col[i] == -1) {
                    if (vis[i])continue;
                    col[i] = 0;
                }
            }
            vector<int> mp(n + 2, 0);
            vector<vector<int>> rmp(idx + 1);
            int ptsize = 0;
            for (int i = 1; i <= idx; i++) {
                ptsize += (int) comp[i].size();
                subG[i].resize(comp[i].size() + 2);
                subrevG[i].resize(comp[i].size() + 2);
                rmp[i].resize(comp[i].size() + 2);
                for (int z = 0; z < comp[i].size(); z++) {
                    int v = comp[i][z];
                    mp[v] = z + 1;
                    rmp[i][z + 1] = v;
                }
            }
            CandidatesSize[cnt] += ptsize;
            for (int i = 1; i <= n + 1; i++) {
                if (!vis[i])continue;
                for (auto v: G[i]) {
                    if (vis[v] == vis[i]) {
                        subG[vis[i]][mp[i]].push_back(mp[v]);
                        subrevG[vis[i]][mp[v]].push_back(mp[i]);
                    }
                }
            }
            vector<int> my_targets;
            for (int i = 1; i <= idx; i++) {
                int rt = (int) comp[i].size() + 1;
                for (int u = 1; u <= comp[i].size(); u++) {
                    if (subrevG[i][u].empty()) {
                        subG[i][rt].push_back(u);
                        subrevG[i][u].push_back(rt);
                    }
                }
                auto my_target = IGS((int) comp[i].size(), ask_yes, subG[i], subrevG[i], rmp[i], cnt, ptsize);
                my_targets.push_back(my_target);
            }
            return {cnt, my_targets};
        } else {
            int ptsize = 0;
            for (int i = 1; i <= n; i++) {
                if (col[i] == -1) ptsize++;
                if (col[i] == 1) {
                    int f = 0;
                    for (auto v: G[i]) {
                        if (col[v] == 1) {
                            f = 1;
                            break;
                        }
                    }
                    if (!f)ptsize++;
                }
            }
            CandidatesSize[cnt] += ptsize;
            vector<int> cnt1(n + 2, 0), cnt0(n + 2, 0);
            ll maxx = 0;
            int id = 0;
            for (auto i: U) {
                vector<int> tmp_col;
                // suppose Yes when ask i
                tmp_col = col;
                vector<int> tmp_U = U;
                multi_calc_yes(tmp_col, G, revG, n, i, tmp_U, GReach, revGReach);
                for (auto j: U) {
                    if (tmp_col[j] != col[j]) cnt1[i]++;
                }
                // suppose No when ask i
                tmp_col = col;
                tmp_U = U;
                multi_calc_no(tmp_col, G, revG, n, i, tmp_U, GReach, revGReach);
                for (auto j: U) {
                    if (tmp_col[j] != col[j]) cnt0[i]++;
                }
                ll val = 1ll * cnt1[i] * cnt0[i];
                if (maxx < val) {
                    maxx = val;
                    id = i;
                }
            }
            int ret = ask(id, ask_yes);
            cnt++;
            if (ret) {
                multi_calc_yes(col, G, revG, n, id, U, GReach, revGReach);
            } else {
                multi_calc_no(col, G, revG, n, id, U, GReach, revGReach);
            }
        }
    }
}

string tmp;

struct node {
    int id;
    vector<int> targets;
    vector<int> ans_targets;
    double qu_cost;
    int query_cnt;

    bool operator<(const node &b) const {
        return id < b.id;
    }
};

void solve() {
    ThreadPool pool(std::thread::hardware_concurrency() / 2 + 1);
    std::vector<std::future<node>> future_vector;
    string ss = tmp + ".txt";
    freopen(ss.c_str(), "r", stdin);

    int n, m;
    cin >> n >> m;
    vector<vector<int>> G(n + 2);
    vector<vector<int>> revG(n + 2);
    for (int i = 1, u, v; i <= m; i++) {
        cin >> u >> v;
        G[u].push_back(v);
        revG[v].push_back(u);
    }
    int rt = n + 1;
    for (int i = 1; i <= n; i++) {
        if (revG[i].empty()) {
            G[rt].push_back(i);
            revG[i].push_back(rt);
        }
    }
    // n*m init
    vector<vector<bool>> GReach(n + 2, vector<bool>(n + 2));
    vector<vector<bool>> revGReach(n + 2, vector<bool>(n + 2));
    for (int i = 1; i <= n + 1; i++) {
        queue<int> q;
        vector<int> vis(n + 2, 0);
        q.push(i), vis[i] = 1;
        GReach[i][i] = true;
        while (!q.empty()) {
            int cur = q.front();
            q.pop();
            for (auto v: G[cur]) {
                if (vis[v])
                    continue;
                q.push(v);
                vis[v] = 1;
                GReach[i][v] = true;
            }
        }
    }
    for (int i = 1; i <= n + 1; i++) {
        queue<int> q;
        vector<int> vis(n + 2, 0);
        q.push(i), vis[i] = 1;
        revGReach[i][i] = true;
        while (!q.empty()) {
            int cur = q.front();
            q.pop();
            for (auto v: revG[cur]) {
                if (vis[v])
                    continue;
                q.push(v);
                vis[v] = 1;
                revGReach[i][v] = true;
            }
        }
    }
    //
    string query_ss = tmp + "_query2.txt";
    freopen(query_ss.c_str(), "r", stdin);

    int TestCase;
    cin >> TestCase;
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
        sort(target.begin(), target.end());
        // init_query()  O(n)
        for (auto i: target) {
            init_query(i, ask_yes, revG);
        }
        int K = targetNumber;
        vector<int> col(n + 2);
        vector<int> U;
        col[rt] = 1;
        for (int i = 1; i <= n; i++) U.push_back(i), col[i] = -1;
        auto run = [=]() mutable {
            auto qu_st = std::chrono::high_resolution_clock::now();
            auto [query_cnt, my_targets] = multi_select(n, K, col, ask_yes, G, revG, U, GReach, revGReach);

            auto qu_ed = std::chrono::high_resolution_clock::now();
            std::chrono::duration<double> elapsed = qu_ed - qu_st;
            double qu_cost = elapsed.count();
            node cur;
            cur.id = __;
            cur.query_cnt = query_cnt, cur.qu_cost = qu_cost;
            sort(target.begin(), target.end()), sort(my_targets.begin(), my_targets.end());
            cur.ans_targets = target, cur.targets = my_targets;
            return cur;
        };
        future_vector.emplace_back(pool.enqueue(run));
    }
    vector<node> output_vec;
    for (auto &&future: future_vector) {
        node cur = future.get();
        output_vec.push_back(cur);
    }
    sort(output_vec.begin(), output_vec.end());
    string query_log = "UltraIGS_" + tmp + "_query2_log.txt";
    freopen(query_log.c_str(), "w", stdout);

    double sum = 0;
    int max_query_cnt = 0, minn_query_cnt = n + 1;
    double sum_query_time = 0;

    for (auto [id, targets, ans_targets, qu_cost, query_cnt]: output_vec) {
        cout << "query #" << id << ":" << endl;
        if (targets != ans_targets) {
            for (auto i: targets) cout << i << " ";
            cout << endl;
            for (auto i: ans_targets) cout << i << " ";
            cout << endl;
            cout << "Wrong" << endl;
            exit(0);
        }
        cout << "targets: ";
        for (auto i: targets) cout << i << " ";
        cout << "\n";
        cout << "query_cnt: " << query_cnt << "\n";
        cout << "cur_cost: " << qu_cost << "\n" << endl;
        sum += query_cnt;
        max_query_cnt = max(max_query_cnt, query_cnt), minn_query_cnt = min(minn_query_cnt, query_cnt);
        sum_query_time += qu_cost;
    }
    cout << "max_query_cnt: " << max_query_cnt << "\n";
    cout << "min_query_cnt: " << minn_query_cnt << "\n";
    cout << "avg_query_cnt: " << fixed << setprecision(8) << sum / TestCase << "\n";
    cout << "avg_cost: " << fixed << setprecision(8) << sum_query_time / TestCase << "\n\n";
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

*/



