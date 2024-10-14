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
              vector<unordered_set<int> > &GReach,
              vector<unordered_set<int> > &revGReach) {
    // P \gets ( P \cap des(x) )  O(n)
    vector<int> erase_seq;
    for (auto [i, val]: P) {
        if (GReach[x].find(i) == GReach[x].end()) {
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
            if (GReach[minn.second].find(i) == GReach[minn.second].end()) {
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
        if (revGReach[x].find(v) != revGReach[x].end()) {
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
             vector<unordered_set<int> > &GReach,
             vector<unordered_set<int> > &revGReach) {
    // P <- P \cap (V \setminus des(x))
    vector<int> erase_seq;
    for (auto [i, val]: P) {
        if (GReach[x].find(i) != GReach[x].end()) {
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
            if (GReach[minn.second].find(i) == GReach[minn.second].end()) {
                flag = 1;
                break;
            }
        }
        if (!flag && col[minn.second] == -1) {
            // exist -> vertex is Yes.
            col[minn.second] = 1;
            mp[minn.second] = true;
            for (auto v: U) {
                if (revGReach[minn.second].find(v) != revGReach[minn.second].end()) {
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
                             vector<unordered_set<int> > &GReach,
                             vector<unordered_set<int> > &revGReach,
                             vector<std::chrono::time_point<std::chrono::high_resolution_clock> > &timestamp) {
    int cnt = 0;
    CandidatesSize[cnt] += (int) P.size();
    while (P.size() > 1) {
        ll maxx = 0;
        int id = 0;
        for (auto i: U) {
            vector<int> tmp_col;
            // suppose Yes when ask i
            tmp_col = col;
            vector<int> tmp_U = U;
            gp_hash_table<int, bool> tmp_P = P;
            calc_yes(tmp_col, G, revG, n, i, tmp_U, tmp_P, top, GReach, revGReach);
            ll cnt1 = (int) U.size() - (int) tmp_U.size();
            // suppose No when ask i
            tmp_col = col;
            tmp_U = U;
            tmp_P = P;
            calc_no(tmp_col, G, revG, n, i, tmp_U, tmp_P, top, GReach, revGReach);
            ll cnt0 = (int) U.size() - (int) tmp_U.size();
            ll val = 1ll * cnt1 * cnt0;
            if (maxx < val) {
                maxx = val;
                id = i;
            }
        }
        int ret = ask(id, ask_yes, timestamp);
        cnt++;
        if (ret) {
            calc_yes(col, G, revG, n, id, U, P, top, GReach, revGReach);
        } else {
            calc_no(col, G, revG, n, id, U, P, top, GReach, revGReach);
        }
        CandidatesSize[cnt] += (int) P.size();
    }
    return {cnt, P.begin()->first};
}

void dfs(int x, vector<vector<int> > &G, vector<int> &cnt0, vector<int> &col) {
    cnt0[x] = 1;
    for (auto v: G[x]) {
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
                                  vector<int> &top,
                                  vector<unordered_set<int> > &GReach,
                                  vector<unordered_set<int> > &revGReach,
                                  vector<std::chrono::time_point<std::chrono::high_resolution_clock> > &timestamp) {
    int cnt = 0;
    CandidatesSize[cnt] += (int) P.size();
    vector<int> cnt0(n + 2);
    while (P.size() > 1) {
        ll maxx = 0;
        int id = 0;
        for (auto i: U) {
            cnt0[i] = 0;
        }
        for (auto i: U) {
            if (!cnt0[i]) {
                dfs(i, G, cnt0, col);
            }
            ll val = 1ll * cnt0[i] * (1 + (int) U.size() - cnt0[i]);
            if (maxx < val) {
                maxx = val;
                id = i;
            }
        }
        int ret = ask(id, ask_yes, timestamp);
        cnt++;
        if (ret) {
            gp_hash_table<int, bool> mp;
            P.clear();
            col[id] = true, mp[id] = true, P[id] = true;
            for (auto i: U) {
                if (i == id) continue;
                if (GReach[id].find(i) != GReach[id].end()) {
                    P[i] = true;
                } else {
                    mp[i] = true;
                    if (GReach[i].find(id) != GReach[i].end()) {
                        col[i] = 1;
                    } else {
                        col[i] = 0;
                    }
                }
            }
            vector<int> tmp;
            for (auto v: U) {
                if (mp.find(v) == mp.end()) {
                    tmp.push_back(v);
                }
            }
            U = tmp;
        } else {
            gp_hash_table<int, bool> mp;
            for (auto i: U) {
                if (GReach[id].find(i) != GReach[id].end()) {
                    col[i] = 0;
                    mp[i] = true;
                    if (P.find(i) != P.end())P.erase(i);
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
        CandidatesSize[cnt] += (int) P.size();
    }
    return {cnt, P.begin()->first};
}

string tmp;

struct node {
    int id;
    vector<int> targets;
    vector<int> ans_targets;
    double qu_cost;
    int query_cnt;
    vector<std::chrono::time_point<std::chrono::high_resolution_clock> > timestamp;

    bool operator<(const node &b) const {
        return id < b.id;
    }
};

void solve() {
    ThreadPool pool(std::thread::hardware_concurrency() / 2 + 1);
    std::vector<std::future<node> > future_vector;

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
    vector<int> top(n + 2);
    vector<int> du(n + 2);
    for (int i = 1; i <= n + 1; i++) {
        for (auto v: G[i]) {
            du[v]++;
        }
    }
    queue<int> que;
    que.push(n + 1);
    int top_id = 0;
    while (!que.empty()) {
        int u = que.front();
        top[u] = ++top_id;
        que.pop();
        for (auto v: G[u]) {
            du[v]--;
            if (!du[v]) {
                que.push(v);
            }
        }
    }

    string query_ss = tmp + "_query.txt";
    freopen(query_ss.c_str(), "r", stdin);
    int TestCase;
    cin >> TestCase;
    cout << "start" << endl;
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
        // init_query()  O(n)
        for (auto i: target) {
            init_query(i, ask_yes, revG);
        }
        vector<int> col(n + 2);
        vector<int> U;
        gp_hash_table<int, bool> P;
        col[rt] = 1;
        for (int i = 1; i <= n; i++) U.push_back(i), P[i] = true, col[i] = -1;

        auto run = [=]() mutable {
            if (n - 1 == m) {
                auto qu_st = std::chrono::high_resolution_clock::now();
                // single_select O( turns * ( n*m ) )
                vector<std::chrono::time_point<std::chrono::high_resolution_clock> > timestamp;
                timestamp.push_back(qu_st);
                auto [query_cnt, tar] = single_select_tree(n, col, ask_yes, G, revG, U, P, top, GReach, revGReach,
                                                           timestamp);
                vector<int> my_targets;
                for (auto [x, z]: P) {
                    my_targets.push_back(x);
                }
                auto qu_ed = std::chrono::high_resolution_clock::now();
                std::chrono::duration<double> elapsed = qu_ed - qu_st;
                double qu_cost = elapsed.count();
                node cur;
                cur.id = __;
                cur.timestamp = timestamp;
                cur.query_cnt = query_cnt, cur.qu_cost = qu_cost;
                sort(target.begin(), target.end()), sort(my_targets.begin(), my_targets.end());
                cur.ans_targets = target, cur.targets = my_targets;
                return cur;
            } else {
                auto qu_st = std::chrono::high_resolution_clock::now();
                // single_select O( turns * ( n*m ) )
                vector<std::chrono::time_point<std::chrono::high_resolution_clock> > timestamp;
                timestamp.push_back(qu_st);
                auto [query_cnt, tar] = single_select(n, col, ask_yes, G, revG, U, P, top, GReach, revGReach,
                                                      timestamp);
                vector<int> my_targets;
                for (auto [x, z]: P) {
                    my_targets.push_back(x);
                }
                auto qu_ed = std::chrono::high_resolution_clock::now();
                std::chrono::duration<double> elapsed = qu_ed - qu_st;
                double qu_cost = elapsed.count();
                node cur;
                cur.id = __;
                cur.timestamp = timestamp;
                cur.query_cnt = query_cnt, cur.qu_cost = qu_cost;
                sort(target.begin(), target.end()), sort(my_targets.begin(), my_targets.end());
                cur.ans_targets = target, cur.targets = my_targets;
                return cur;
            }
        };
        future_vector.emplace_back(pool.enqueue(run));
    }
    vector<node> output_vec;
    for (auto &&future: future_vector) {
        node cur = future.get();
        cout << cur.id << " " << cur.qu_cost << " " << cur.query_cnt << endl;
        output_vec.push_back(cur);
    }
    sort(output_vec.begin(), output_vec.end());
    string query_log = "init_Ultra_" + tmp + "_query_log.txt";
    freopen(query_log.c_str(), "w", stdout);

    double sum = 0;
    int max_query_cnt = 0, minn_query_cnt = n + 1;
    double sum_query_time = 0;

    for (auto [id, targets, ans_targets, qu_cost, query_cnt, timestamp]: output_vec) {
        cout << "query #" << id << ":" << endl;
        if (targets != ans_targets) {
            cout << "Wrong" << endl;
            exit(0);
        }
        cout << "targets: ";
        for (auto i: targets) cout << i << " ";
        cout << "\n";
        cout << "query_cnt: " << query_cnt << "\n";
        cout << "cur_cost: " << qu_cost << "\n" << endl;
        for (int i = 1; i < timestamp.size(); i++) {
            auto pre = timestamp[i - 1], cur = timestamp[i];
            std::chrono::duration<double> elapsed = cur - pre;
            double t = elapsed.count();
            timeGap[i] += t;
        }
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
 9 9
 1 3
 1 4
 1 5
 2 5
 3 6
 3 7
 3 8
 4 8
 5 9
 1
 1
 8
*/

