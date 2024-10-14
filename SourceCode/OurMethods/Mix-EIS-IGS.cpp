#include <future>

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
    std::queue<std::function<void()> > tasks;

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
                std::function<void()> task; {
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

    auto task = std::make_shared<std::packaged_task<return_type()> >(
        std::bind(std::forward<F>(f), std::forward<Args>(args)...));

    std::future<return_type> res = task->get_future(); {
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
inline ThreadPool::~ThreadPool() { {
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

#define debug(...)                                                            \
do {                                                                         \
    std::cout << #__VA_ARGS__ << " -> ";                                         \
    err(__VA_ARGS__);                                                          \
} while (0)

void err() { std::cout << std::endl; }

template<class T, class... Ts>
void err(const T &arg, const Ts &... args) {
    std::cout << arg << ' ';
    err(args...);
}


int ask(int x, vector<int> &ask_yes, vector<std::chrono::time_point<std::chrono::high_resolution_clock> > &timestamp) {
    auto qu_st = std::chrono::high_resolution_clock::now();
    timestamp.push_back(qu_st);
    if (ask_yes[x])
        return 1;
    return 0;
}

void init_query(int cur, vector<int> &ask_yes, vector<vector<int> > &Graph) {
    ask_yes[cur] = 1;
    for (auto v: Graph[cur]) {
        if (!ask_yes[v]) {
            init_query(v, ask_yes, Graph);
        }
    }
}

void calc_yes(vector<int> &col,
              vector<vector<int> > &G,
              vector<vector<int> > &revG,
              int n,
              int x,
              vector<int> &U,
              gp_hash_table<int, bool> &P,
              vector<int> &top,
              vector<vector<bool> > &GReach,
              vector<vector<bool> > &revGReach) {
    // P \gets ( P \cap des(x) )  O(n)
    vector<int> erase_seq;
    for (auto [i, val]: P) {
        if (!GReach[x][i]) {
            erase_seq.push_back(i);
        }
    }
    for (auto i: erase_seq) {
        P.erase(i);
    }
    pair<int, int> minn = {n + 2, -1};
    for (auto [i, val]: P) {
        minn = min(minn, {top[i], i});
    }

    // check if the top vertex can reach all the Potential targets O(n)
    {
        int flag = 0;
        for (auto [i, val]: P) {
            if (!GReach[minn.second][i]) {
                flag = 1;
                break;
            }
        }
        if (!flag) {
            x = minn.second;
        }
    }
    // All the vertices which can reach x -> Yes O(n)
    col[x] = 1;
    gp_hash_table<int, bool> mp;
    mp[x] = true;
    for (auto v: U) {
        if (revGReach[x][v]) {
            col[v] = 1;
            mp[v] = true;
        }
    }
    vector<int> tmp;
    for (auto v: U) {
        if (mp.find(v) == mp.end()) {
            tmp.push_back(v);
        }
    }
    U = tmp;
    // (x \in \un) && (des(x) \cap P = \emptyset ) -> x = no O(m)
    // the vertices whose descendants all are not in P
    mp.clear();
    gp_hash_table<int, bool> vis;
    queue<int> q;
    for (auto [i, vali]: P) {
        if (col[i] == -1) {
            vis[i] = true;
            q.push(i);
        }
    }
    while (!q.empty()) {
        int cur = q.front();
        q.pop();
        for (auto v: revG[cur]) {
            if (vis.find(v) != vis.end())continue;
            if (col[v] != -1)continue;
            vis[v] = true;
            q.push(v);
        }
    }
    for (int i: U) {
        if (vis.find(i) == vis.end()) {
            col[i] = 0;
            mp[i] = true;
        }
    }
    tmp.clear();
    for (auto v: U) {
        if (mp.find(v) == mp.end()) {
            tmp.push_back(v);
        }
    }
    U = tmp;
}

void calc_no(vector<int> &col,
             vector<vector<int> > &G,
             vector<vector<int> > &revG,
             int n,
             int x,
             vector<int> &U,
             gp_hash_table<int, bool> &P,
             vector<int> &top,
             vector<vector<bool> > &GReach,
             vector<vector<bool> > &revGReach) {
    // P <- P \cap (V \setminus des(x))
    vector<int> erase_seq;
    for (auto [i, val]: P) {
        if (GReach[x][i]) {
            erase_seq.push_back(i);
        }
    }
    for (auto i: erase_seq) {
        P.erase(i);
    }
    pair<int, int> minn = {n + 2, -1};
    for (auto [i, num]: P) {
        minn = min(minn, {top[i], i});
    }
    gp_hash_table<int, int> mp;
    // check if the top vertex can reach all the Potential targets O(n)
    {
        int flag = 0;
        for (auto [i, val]: P) {
            if (!GReach[minn.second][i]) {
                flag = 1;
                break;
            }
        }
        if (!flag && col[minn.second] == -1) {
            // exist -> vertex is Yes.
            col[minn.second] = 1;
            mp[minn.second] = true;
            for (auto v: U) {
                if (revGReach[minn.second][v]) {
                    col[v] = 1;
                    mp[v] = true;
                }
            }
            vector<int> tmp;
            for (auto v: U) {
                if (mp.find(v) == mp.end()) {
                    tmp.push_back(v);
                }
            }
            U = tmp;
        }
    }

    // (x \in \un) & (des(x) \cap P = \emptyset ) -> x = no
    mp.clear();
    gp_hash_table<int, bool> vis;
    queue<int> q;
    for (auto [i, vali]: P) {
        if (col[i] == -1) {
            vis[i] = true;
            q.push(i);
        }
    }
    while (!q.empty()) {
        int cur = q.front();
        q.pop();
        for (auto v: revG[cur]) {
            if (vis.find(v) != vis.end())continue;
            if (col[v] != -1)continue;
            vis[v] = true;
            q.push(v);
        }
    }
    for (int i: U) {
        if (vis.find(i) == vis.end()) {
            col[i] = 0;
            mp[i] = true;
        }
    }
    vector<int> tmp;
    for (auto v: U) {
        if (mp.find(v) == mp.end()) {
            tmp.push_back(v);
        }
    }
    U = tmp;
}

map<int, int> CandidatesSize;
map<int, double> timeGap;

pair<int, int> single_select(int n,
                             vector<int> &col,
                             vector<int> &ask_yes,
                             vector<vector<int> > &G,
                             vector<vector<int> > &revG,
                             vector<int> &U,
                             gp_hash_table<int, bool> &P,
                             vector<int> &top,
                             vector<vector<bool> > &GReach,
                             vector<vector<bool> > &revGReach,
                             vector<int> &rmp, int &cnt, int &ptsize,
                             vector<std::chrono::time_point<std::chrono::high_resolution_clock> > &timestamp) {
    vector<int> tmp_col;
    vector<int> tmp_U;
    gp_hash_table<int, bool> tmp_P;
    while (P.size() > 1 && !U.empty()) {
        ll maxx = 0;
        int id = 0;
        for (auto i: U) {
            // suppose Yes when ask i
            tmp_col = col;
            tmp_U = U;
            tmp_P = P;
            calc_yes(tmp_col, G, revG, n, i, tmp_U, tmp_P, top, GReach, revGReach);
            ll cnt1 = (int) U.size() - (int) tmp_U.size();
            // suppose No when ask i
            tmp_col = col;
            tmp_U = U;
            tmp_P = P;
            calc_no(tmp_col, G, revG, n, i, tmp_U, tmp_P, top, GReach, revGReach);
            ll cnt0 = (int) U.size() - (int) tmp_U.size();
            if (ll val = 1ll * cnt1 * cnt0; maxx < val) {
                maxx = val;
                id = i;
            }
        }
        int ret = ask(rmp[id], ask_yes, timestamp);
        cnt++;
        if (ret) {
            int bef = (int) P.size();
            calc_yes(col, G, revG, n, id, U, P, top, GReach, revGReach);
            ptsize -= bef - (int) P.size();
        } else {
            int bef = (int) P.size();
            calc_no(col, G, revG, n, id, U, P, top, GReach, revGReach);
            ptsize -= bef - (int) P.size();
        }
        CandidatesSize[cnt] += ptsize;
    }
    if (!P.empty())return {cnt, rmp[P.begin()->first]};
    return {cnt, -1};
}

void dfs(const int x, vector<vector<int> > &G, vector<int> &cnt0, vector<int> &col) {
    cnt0[x] = 1;
    for (const auto v: G[x]) {
        if (col[v] != -1)continue;
        if (!cnt0[v]) {
            dfs(v, G, cnt0, col);
        }
        cnt0[x] += cnt0[v];
    }
}

pair<int, int> single_select_tree(int n,
                                  vector<int> &col,
                                  vector<int> &ask_yes,
                                  vector<vector<int> > &G,
                                  vector<vector<int> > &revG,
                                  vector<int> &U,
                                  gp_hash_table<int, bool> &P,
                                  vector<vector<bool> > &GReach,
                                  vector<vector<bool> > &revGReach, vector<int> &rmp, int &cnt, int &ptsize,
                                  vector<std::chrono::time_point<std::chrono::high_resolution_clock> > &timestamp) {
    vector<int> cnt0(n + 2);
    gp_hash_table<int, bool> mp;
    vector<int> tmp;
    while (P.size() > 1 && !U.empty()) {
        ll maxx = 0;
        int id = 0;
        for (auto i: U) {
            cnt0[i] = 0;
        }
        for (auto i: U) {
            if (!cnt0[i]) {
                dfs(i, G, cnt0, col);
            }
            if (ll val = 1ll * cnt0[i] * (1 + (int) U.size() - cnt0[i]); maxx < val) {
                maxx = val;
                id = i;
            }
        }
        int ret = ask(rmp[id], ask_yes, timestamp);
        cnt++;
        int bef = (int) P.size();
        if (ret) {
            mp.clear();
            P.clear();
            col[id] = true, mp[id] = true, P[id] = true;
            for (auto i: U) {
                if (i == id) continue;
                if (GReach[id][i]) {
                    P[i] = true;
                } else {
                    mp[i] = true;
                    if (GReach[i][id]) {
                        col[i] = 1;
                    } else {
                        col[i] = 0;
                    }
                }
            }
            tmp.clear();
            for (auto v: U) {
                if (mp.find(v) == mp.end()) {
                    tmp.push_back(v);
                }
            }
            U = tmp;
        } else {
            mp.clear();
            for (auto i: U) {
                if (GReach[id][i]) {
                    col[i] = 0;
                    mp[i] = true;
                    if (P.find(i) != P.end())P.erase(i);
                }
            }
            tmp.clear();
            for (auto v: U) {
                if (mp.find(v) == mp.end()) {
                    tmp.push_back(v);
                }
            }
            U = tmp;
        }
        ptsize -= bef - (int) P.size();
        CandidatesSize[cnt] += ptsize;
    }
    if (!P.empty())return {cnt, rmp[P.begin()->first]};
    return {cnt, -1};
}

std::vector<int> multi_calc_yes(std::vector<int> &col, std::vector<std::vector<int> > &G,
                                std::vector<std::vector<int> > &revG,
                                int n, int x,
                                std::vector<int> &U,
                                std::vector<unordered_set<int> > &GReach,
                                std::vector<unordered_set<int> > &revGReach) {
    col[x] = 1;
    std::unordered_set<int> mp;
    mp.insert(x);
    std::vector<int> removed_nodes;
    for (auto v: U) {
        if (revGReach[x].find(v) != revGReach[x].end()) {
            col[v] = 1;
            mp.insert(v);
        }
    }
    auto it = std::remove_if(U.begin(), U.end(), [&mp, &removed_nodes](int v) {
        if (mp.find(v) != mp.end()) {
            removed_nodes.push_back(v);
            return true;
        }
        return false;
    });
    U.erase(it, U.end());
    return removed_nodes;
}

std::vector<int> multi_calc_no(std::vector<int> &col, std::vector<std::vector<int> > &G,
                               std::vector<std::vector<int> > &revG,
                               int n, int x,
                               std::vector<int> &U,
                               std::vector<unordered_set<int> > &GReach,
                               std::vector<unordered_set<int> > &revGReach) {
    col[x] = 0;
    std::unordered_set<int> mp;
    mp.insert(x);
    std::vector<int> removed_nodes;
    for (auto v: U) {
        if (GReach[x].find(v) != GReach[x].end()) {
            col[v] = 0;
            mp.insert(v);
        }
    }
    auto it = std::remove_if(U.begin(), U.end(), [&mp, &removed_nodes](int v) {
        if (mp.find(v) != mp.end()) {
            removed_nodes.push_back(v);
            return true;
        }
        return false;
    });
    U.erase(it, U.end());
    return removed_nodes;
}

int find(int x, vector<int> &fa) {
    if (fa[x] == x)return x;
    return fa[x] = find(fa[x], fa);
}

void spanTree(int x, vector<vector<int> > &G, vector<vector<int> > &st, vector<int> &vis) {
    vector<pair<int, int> > children;
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
dfs1(int x, int root, vector<int> &dep, vector<int> &sz, vector<vector<int> > &edge, vector<int> &fa,
     vector<int> &son) {
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

void dfs2(int x, int tp, vector<int> &top, vector<vector<int> > &heavy, vector<int> &son, vector<int> &fa,
          vector<vector<int> > &edge) {
    top[x] = tp;
    heavy[tp].push_back(x);
    if (son[x] != x) dfs2(son[x], tp, top, heavy, son, fa, edge);
    for (int i = 0; i < edge[x].size(); i++) {
        int y = edge[x][i];
        if (y == fa[x] || y == son[x]) continue;
        dfs2(y, y, top, heavy, son, fa, edge);
    }
}


int question_IGS_dfs(int tmp, int &cnt, vector<vector<int> > &heavy, vector<int> &ask_yes, vector<vector<int> > &edge,
                     vector<int> &rmp, vector<pair<int, int> > &seq,
                     vector<std::chrono::time_point<std::chrono::high_resolution_clock> > &timestamp) {
    int len = heavy[tmp].size();
    //    debug(tmp);
    int l = 0, r = len - 1;
    int ans = -1;
    while (l <= r) {
        int mid = (l + r) >> 1;
        int mid_node = heavy[tmp][mid];
        //        debug(l, r, mid, mid_node);
        cnt++;
        if (ask(rmp[mid_node], ask_yes, timestamp)) {
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
        if (ask(rmp[y], ask_yes, timestamp)) {
            //          if (cnt >= B) return y;
            seq.emplace_back(y, true);
            return question_IGS_dfs(y, cnt, heavy, ask_yes, edge, rmp, seq, timestamp);
        } else {
            seq.emplace_back(y, false);
        }
    }
    return x;
}

int IGS(int n, vector<int> &ask_yes, vector<vector<int> > &G, vector<vector<int> > &revG, vector<int> &rmp, int &cnt,
        int &ptsize, vector<std::chrono::time_point<std::chrono::high_resolution_clock> > &timestamp) {
    int rt = n + 1;
    ask_yes[0] = 1;
    rmp[rt] = 0;
    vector<vector<int> > spanning_tree(n + 2);
    vector<int> vis_stree(n + 2);
    vis_stree[rt] = 1;
    spanTree(rt, G, spanning_tree, vis_stree);
    vector<int> depth(n + 2), son(n + 2), top(n + 2), fa(n + 2), sz(n + 2);
    vector<vector<int> > heavy_chain(n + 2);
    dfs1(rt, rt, depth, sz, spanning_tree, fa, son);
    dfs2(rt, rt, top, heavy_chain, son, fa, spanning_tree);

    int query_cnt = 0;
    vector<pair<int, int> > seq;
    int my_target = question_IGS_dfs(rt, query_cnt, heavy_chain, ask_yes, spanning_tree, rmp, seq, timestamp);
    cnt += query_cnt;
    return rmp[my_target];
}

pair<int, vector<int> >
multi_select(int n, int K, vector<int> &col, vector<int> &ask_yes, vector<vector<int> > &G,
             vector<vector<int> > &revG, vector<int> &U,
             vector<unordered_set<int> > &GReach,
             vector<unordered_set<int> > &revGReach,
             vector<std::chrono::time_point<std::chrono::high_resolution_clock> > &timestamp,
             int &start_query_cnt, map<vector<bool>, pair<int, pair<vector<int>, vector<int> > > > &nxt_question,
             int len
) {
    int cnt = 0;
    vector<bool> ask_seq;
    vector<int> cnty(n + 2, 0);
    vector<int> cntn(n + 2, 0);
    vector<int> key_yes;
    vector<int> key_vis(n + 2, 0);
    vector<int> fa(n + 2);
    unordered_map<int, int> mp_idx;
    vector<vector<int> > Comp;
    vector<int> Comp_id;
    vector<int> dif;
    while (true) {
        // Check the number of the connected components
        key_yes.clear();
        key_vis.assign(n + 2, 0);
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
        mp_idx.clear();
        for (int i = 1; i <= n + 1; i++) {
            if (!mp_idx.count(find(i, fa)))mp_idx[find(i, fa)] = ++idx;
        }
        Comp.assign(idx + 1, vector<int>());
        for (int i = 1; i <= n + 1; i++) {
            Comp[mp_idx[find(i, fa)]].push_back(i);
        }
        Comp_id.clear();
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
            start_query_cnt = cnt;
            idx = (int) Comp_id.size();
            vector<vector<vector<int> > > subG(idx + 1);
            vector<vector<vector<int> > > subrevG(idx + 1);
            vector<vector<int> > comp(idx + 1);
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
            vector<vector<int> > rmp(idx + 1);
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
                auto my_target = IGS((int) comp[i].size(), ask_yes, subG[i], subrevG[i], rmp[i], cnt, ptsize,
                                     timestamp);
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
            ll maxx = 0;
            int id = 0;
            if (cnt < len && nxt_question.find(ask_seq) != nxt_question.end()) {
                id = nxt_question[ask_seq].first;
            } else {
                for (auto i: U) {
                    if (ll val = cnty[i] * cntn[i]; maxx < val) {
                        maxx = val;
                        id = i;
                    }
                }
            }
            int ret = ask(id, ask_yes, timestamp);
            ask_seq.push_back(ret);
            cnt++;
            dif.clear();
            if (ret) {
                dif = multi_calc_yes(col, G, revG, n, id, U, GReach, revGReach);
            } else {
                dif = multi_calc_no(col, G, revG, n, id, U, GReach, revGReach);
            }
            if (cnt < len && nxt_question.find(ask_seq) != nxt_question.end()) {
                if (cnt == len - 1) {
                    cnty = nxt_question[ask_seq].second.first;
                    cntn = nxt_question[ask_seq].second.second;
                }
            } else {
                for (auto i: dif) {
                    for (auto j: U) {
                        if (revGReach[i].find(j) != revGReach[i].end()) {
                            cntn[j]--;
                        }
                        if (GReach[i].find(j) != GReach[i].end()) {
                            cnty[j]--;
                        }
                    }
                }
            }
        }
    }
}

pair<int, vector<int> >
multi_select_tree(int n, int K, vector<int> &col, vector<int> &ask_yes, vector<vector<int> > &G,
                  vector<vector<int> > &revG, vector<int> &U,
                  vector<unordered_set<int> > &GReach,
                  vector<unordered_set<int> > &revGReach,
                  vector<std::chrono::time_point<std::chrono::high_resolution_clock> > &timestamp,
                  int &start_query_cnt, map<vector<bool>, pair<int, pair<vector<int>, vector<int> > > > &nxt_question,
                  int len
) {
    int cnt = 0;
    vector<bool> ask_seq;
    vector<int> key_yes;
    vector<int> key_vis(n + 2, 0);
    vector<int> fa(n + 2);
    queue<int> q;
    unordered_map<int, int> mp_idx;
    vector<vector<int> > Comp;
    vector<int> Comp_id;
    vector<int> cnt1(n + 2, 0), cnt0(n + 2, 0);
    while (true) {
        // Check the number of the connected components
        key_yes.clear();
        key_vis.assign(n + 2, 0);
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
        for (int i = 1; i <= n + 1; i++) {
            fa[i] = i;
        }
        for (auto i: key_yes) {
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
        mp_idx.clear();
        for (int i = 1; i <= n + 1; i++) {
            if (!mp_idx.count(find(i, fa)))mp_idx[find(i, fa)] = ++idx;
        }
        Comp.assign(idx + 1, vector<int>());
        for (int i = 1; i <= n + 1; i++) {
            Comp[mp_idx[find(i, fa)]].push_back(i);
        }
        Comp_id.clear();
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
            start_query_cnt = cnt;
            idx = (int) Comp_id.size();
            vector<vector<vector<int> > > subG(idx + 1);
            vector<vector<vector<int> > > subrevG(idx + 1);
            vector<vector<int> > comp(idx + 1);
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
            vector<vector<int> > rmp(idx + 1);
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
                auto my_target = IGS((int) comp[i].size(), ask_yes, subG[i], subrevG[i], rmp[i], cnt, ptsize,
                                     timestamp);
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
            cnt1.assign(n + 2, 0);
            cnt0.assign(n + 2, 0);
            ll maxx = 0;
            int id = 0;
            if (cnt < len && nxt_question.find(ask_seq) != nxt_question.end()) {
                id = nxt_question[ask_seq].first;
            } else {
                for (auto i: U) {
                    if (!cnt0[i]) {
                        dfs(i, G, cnt0, col);
                    }
                    if (!cnt1[i]) {
                        dfs(i, revG, cnt1, col);
                    }
                    if (ll val = 1ll * cnt0[i] * cnt1[i]; maxx < val) {
                        maxx = val;
                        id = i;
                    }
                }
            }
            int ret = ask(id, ask_yes, timestamp);
            ask_seq.push_back(ret);
            cnt++;
            if (ret) {
                multi_calc_yes(col, G, revG, n, id, U, GReach, revGReach);
            } else {
                multi_calc_no(col, G, revG, n, id, U, GReach, revGReach);
            }
        }
    }
}

int init_ask(int st, int id) {
    if (st & (1 << id)) {
        return 1;
    }
    return 0;
}

map<vector<bool>, pair<int, pair<vector<int>, vector<int> > > > init_multi_select(
    int n, vector<int> &col, vector<vector<int> > &G,
    vector<vector<int> > &revG, vector<int> &U,
    vector<unordered_set<int> > &GReach,
    vector<unordered_set<int> > &revGReach,
    int &st, int LEN
) {
    int cnt = 0;
    vector<bool> status;
    map<vector<bool>, pair<int, pair<vector<int>, vector<int> > > > nxt_question;
    vector<int> cnt1(n + 2, 0), cnt0(n + 2, 0);
    while (!U.empty() && cnt < LEN) {
        ll maxx = 0;
        int id = 0;
        for (auto i: U) {
            vector<int> tmp_col;
            // suppose Yes when ask i
            tmp_col = col;
            vector<int> tmp_U = U;
            multi_calc_yes(tmp_col, G, revG, n, i, tmp_U, GReach, revGReach);
            cnt1[i] = U.size() - tmp_U.size();
            // suppose No when ask i
            tmp_col = col;
            tmp_U = U;
            multi_calc_no(tmp_col, G, revG, n, i, tmp_U, GReach, revGReach);
            cnt0[i] = U.size() - tmp_U.size();
            ll val = 1ll * cnt1[i] * cnt0[i];
            if (maxx < val) {
                maxx = val;
                id = i;
            }
        }

        int ret = init_ask(st, cnt);
        cnt++;
        if (ret) {
            multi_calc_yes(col, G, revG, n, id, U, GReach, revGReach);
        } else {
            multi_calc_no(col, G, revG, n, id, U, GReach, revGReach);
        }
        nxt_question[status] = {id, {cnt1, cnt0}};
        status.push_back(ret ? true : false);
    }
    return nxt_question;
}


map<vector<bool>, pair<int, pair<vector<int>, vector<int> > > >
init_multi_select_tree(int n, vector<int> &col, vector<vector<int> > &G,
                       vector<vector<int> > &revG, vector<int> &U,
                       vector<unordered_set<int> > &GReach,
                       vector<unordered_set<int> > &revGReach,
                       int &st, int LEN
) {
    int cnt = 0;
    vector<bool> status;
    map<vector<bool>, pair<int, pair<vector<int>, vector<int> > > > nxt_question;
    vector<int> cnt1(n + 2, 0), cnt0(n + 2, 0);
    while (!U.empty() && cnt < LEN) {
        cnt1.assign(n + 2, 0), cnt0.assign(n + 2, 0);
        ll maxx = 0;
        int id = 0;
        for (auto i: U) {
            if (!cnt0[i]) {
                dfs(i, G, cnt0, col);
            }
            if (!cnt1[i]) {
                dfs(i, revG, cnt1, col);
            }
            ll val = 1ll * cnt0[i] * cnt1[i];
            if (maxx < val) {
                maxx = val;
                id = i;
            }
        }
        int ret = init_ask(st, cnt);
        cnt++;
        if (ret) {
            multi_calc_yes(col, G, revG, n, id, U, GReach, revGReach);
        } else {
            multi_calc_no(col, G, revG, n, id, U, GReach, revGReach);
        }
        nxt_question[status] = {id, {cnt1, cnt0}};
        status.push_back(ret ? true : false);
    }
    return nxt_question;
}

string tmp;

struct node {
    int id;
    vector<int> targets;
    vector<int> ans_targets;
    double qu_cost;
    int query_cnt;
    int start_query_cnt;
    vector<std::chrono::time_point<std::chrono::high_resolution_clock> > timestamp;

    bool operator<(const node &b) const {
        return id < b.id;
    }
};

void solve() {
    ThreadPool pool(std::thread::hardware_concurrency() / 2 + 1);
    std::vector<std::future<node> > future_vector;
    std::vector<std::future<map<vector<bool>, pair<int, pair<vector<int>, vector<int> > > > > > init_future_vector;
    string ss = tmp + ".txt";
    freopen(ss.c_str(), "r", stdin);

    int n, m;
    cin >> n >> m;
    vector<vector<int> > G(n + 2);
    vector<vector<int> > revG(n + 2);
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
    vector<unordered_set<int> > GReach(n + 2);
    vector<unordered_set<int> > revGReach(n + 2);
    for (int i = 1; i <= n + 1; i++) {
        queue<int> q;
        vector<int> vis(n + 2, 0);
        q.push(i), vis[i] = 1;
        GReach[i].insert(i);
        revGReach[i].insert(i);
        while (!q.empty()) {
            int cur = q.front();
            q.pop();
            for (auto v: G[cur]) {
                if (vis[v])
                    continue;
                q.push(v);
                vis[v] = 1;
                GReach[i].insert(v);
                revGReach[v].insert(i);
            }
        }
    }
    cout << "init_Reach done" << endl;
    //
    string query_ss = tmp + "_query2.txt";
    freopen(query_ss.c_str(), "r", stdin);
    int len = 5;
    for (int st = 0; st < (1 << len); st++) {
        vector<int> col(n + 2);
        vector<int> U;
        col[rt] = 1;
        for (int i = 1; i <= n; i++) U.push_back(i), col[i] = -1;
        auto run = [=]() mutable {
            map<vector<bool>, pair<int, pair<vector<int>, vector<int> > > > cur;
            if (n - 1 != m) cur = init_multi_select(n, col, G, revG, U, GReach, revGReach, st, len);
            else cur = init_multi_select_tree(n, col, G, revG, U, GReach, revGReach, st, len);
            return cur;
        };
        init_future_vector.emplace_back(pool.enqueue(run));
    }
    map<vector<bool>, pair<int, pair<vector<int>, vector<int> > > > nxt_question;
    vector<map<vector<bool>, pair<int, pair<vector<int>, vector<int> > > > > init_output_vec;
    for (auto &&future: init_future_vector) {
        auto cur = future.get();
        init_output_vec.push_back(cur);
    }
    for (auto mpp: init_output_vec) {
        for (auto [x, y]: mpp) {
            if (nxt_question.find(x) == nxt_question.end()) {
                nxt_question[x] = y;
            }
        }
    }
    cout << "Pre done" << endl;
    int TestCase;
    cin >> TestCase;
    vector<int> target;
    vector<int> vis_target(n + 2, 0);
    vector<int> ask_yes(n + 2, 0);
    vector<int> col(n + 2);
    vector<int> U;
    for (int _ = 1; _ <= TestCase; _++) {
        int targetNumber;
        cin >> targetNumber;
        target.clear();
        vis_target.assign(n + 2, 0);
        ask_yes.assign(n + 2, 0);
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
        U.clear();
        col[rt] = 1;
        for (int i = 1; i <= n; i++) U.push_back(i), col[i] = -1;
        auto run = [=]() mutable {
            auto qu_st = std::chrono::high_resolution_clock::now();
            vector<std::chrono::time_point<std::chrono::high_resolution_clock> > timestamp;
            timestamp.push_back(qu_st);
            int query_cnt;
            int start_query_cnt;
            vector<int> my_targets;
            if (m == n - 1) {
                auto ret = multi_select_tree(n, K, col, ask_yes, G, revG, U, GReach, revGReach, timestamp,
                                             start_query_cnt, nxt_question, len);
                query_cnt = ret.first, my_targets = ret.second;
            } else {
                auto ret = multi_select(n, K, col, ask_yes, G, revG, U, GReach, revGReach, timestamp, start_query_cnt,
                                        nxt_question, len);
                query_cnt = ret.first, my_targets = ret.second;
            }
            auto qu_ed = std::chrono::high_resolution_clock::now();
            std::chrono::duration<double> elapsed = qu_ed - qu_st;
            double qu_cost = elapsed.count();
            node cur;
            cur.id = _;
            cur.timestamp = timestamp;
            cur.query_cnt = query_cnt, cur.qu_cost = qu_cost;
            cur.start_query_cnt = start_query_cnt;
            sort(target.begin(), target.end()), sort(my_targets.begin(), my_targets.end());
            cur.ans_targets = target, cur.targets = my_targets;
            return cur;
        };
        future_vector.emplace_back(pool.enqueue(run));
    }
    vector<node> output_vec;
    for (auto &&future: future_vector) {
        node cur = future.get();
        cout << cur.id << " " << cur.qu_cost << endl;
        output_vec.push_back(cur);
    }
    sort(output_vec.begin(), output_vec.end());
    string query_log = "UltraIGS_" + tmp + "_query2_log.txt";
    freopen(query_log.c_str(), "w", stdout);

    double sum = 0;
    int max_query_cnt = 0, minn_query_cnt = n + 1;
    double sum_query_time = 0;
    int found_targets = 0;
    int sum_targets = 0;
    double average_start_query_cnt = 0;
    for (auto [id, targets, ans_targets, qu_cost, query_cnt, start_query_cnt, timestamp]: output_vec) {
        cout << "query #" << id << ":" << endl;
        map<int, int> cnt_t;
        for (auto i: ans_targets)cnt_t[i] = 1;
        int num_targets = 0;
        for (auto i: targets) {
            if (cnt_t.count(i))num_targets++;
        }
        found_targets += num_targets;
        sum_targets += (int) ans_targets.size();
        cout << "targets: ";
        for (auto i: targets) cout << i << " ";
        cout << "\n";
        cout << "query_cnt: " << query_cnt << "\n";
        cout << "cur_cost: " << qu_cost << "\n";
        cout << "start_cnt: " << start_query_cnt << "\n" << endl;
        sum += query_cnt;
        average_start_query_cnt += start_query_cnt;
        max_query_cnt = max(max_query_cnt, query_cnt), minn_query_cnt = min(minn_query_cnt, query_cnt);
        sum_query_time += qu_cost;
        for (int i = 1; i < timestamp.size(); i++) {
            auto pre = timestamp[i - 1], cur = timestamp[i];
            std::chrono::duration<double> elapsed = cur - pre;
            double t = elapsed.count();
            timeGap[i] += t;
        }
    }
    cout << "avg_start_query_cnt: " << fixed << setprecision(8) << average_start_query_cnt / TestCase << "\n";
    cout << "max_query_cnt: " << max_query_cnt << "\n";
    cout << "min_query_cnt: " << minn_query_cnt << "\n";
    cout << "avg_query_cnt: " << fixed << setprecision(8) << sum / TestCase << "\n";
    cout << "avg_cost: " << fixed << setprecision(8) << sum_query_time / TestCase << "\n";
    cout << "found_targets: " << found_targets << " " << "sum_targets: " << sum_targets << "\n";
    cout << "\nPotentialTargetSize: \n";
    for (auto [cur_query_cnt, PSize]: CandidatesSize) {
        cout << cur_query_cnt << " " << 1.0 * PSize / TestCase << "\n";
    }
    cout << "\n";
    cout << "QueryGap:\n";
    for (auto [cur_query_cnt, timegap]: timeGap) {
        cout << cur_query_cnt << " " << 1.0 * timegap / TestCase << "\n";
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

