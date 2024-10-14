#include <future>

#pragma GCC optimize(3)

#include <bits/stdc++.h>

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

map<int, int> CandidatesSize;
map<int, double> timeGap;

pair<int, vector<int> >
multi_select(int n, int K, vector<int> &col, vector<int> &ask_yes, vector<vector<int> > &G,
             vector<vector<int> > &revG, vector<int> &U,
             vector<unordered_set<int> > &GReach,
             vector<unordered_set<int> > &revGReach,
             vector<std::chrono::time_point<std::chrono::high_resolution_clock> > &timestamp
) {
    int cnt = 0;
    vector<int> cnty(n + 2, 0);
    vector<int> cntn(n + 2, 0);
    for (int i = 1; i <= n; i++) {
        for (int j = 1; j <= n; j++) {
            if (GReach[i].find(j) != GReach[i].end()) {
                cntn[i]++;
            }
            if (revGReach[i].find(j) != revGReach[i].end()) {
                cnty[i]++;
            }
        }
    }
    vector<int> dif;
    while (!U.empty()) {
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
        for (auto i: U) {
            if (ll val = cnty[i] * cntn[i]; maxx < val) {
                maxx = val;
                id = i;
            }
        }
        int ret = ask(id, ask_yes, timestamp);
        cnt++;
        dif.clear();
        if (ret) {
            dif = multi_calc_yes(col, G, revG, n, id, U, GReach, revGReach);
        } else {
            dif = multi_calc_no(col, G, revG, n, id, U, GReach, revGReach);
        }
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
    vector<int> ret;
    for (int i = 1; i <= n; i++) {
        if (col[i] == 1) {
            int flag = 0;
            for (auto j: G[i]) {
                if (col[j] == 1) {
                    flag = 1;
                    break;
                }
            }
            if (!flag) {
                ret.push_back(i);
            }
        }
    }
    return {cnt, ret};
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


pair<int, vector<int> >
multi_select_tree(int n, int K, vector<int> &col, vector<int> &ask_yes, vector<vector<int> > &G,
                  vector<vector<int> > &revG, vector<int> &U,
                  vector<unordered_set<int> > &GReach,
                  vector<unordered_set<int> > &revGReach,
                  vector<std::chrono::time_point<std::chrono::high_resolution_clock> > &timestamp
) {
    int cnt = 0;
    vector<int> cnt1(n + 2, 0), cnt0(n + 2, 0);
    while (!U.empty()) {
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
        int ret = ask(id, ask_yes, timestamp);
        cnt++;
        if (ret) {
            multi_calc_yes(col, G, revG, n, id, U, GReach, revGReach);
        } else {
            multi_calc_no(col, G, revG, n, id, U, GReach, revGReach);
        }
    }
    vector<int> ret;
    for (int i = 1; i <= n; i++) {
        if (col[i] == 1) {
            int flag = 0;
            for (auto j: G[i]) {
                if (col[j] == 1) {
                    flag = 1;
                    break;
                }
            }
            if (!flag) {
                ret.push_back(i);
            }
        }
    }
    return {cnt, ret};
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
    //
    string query_ss = tmp + "2_query2.txt";
    freopen(query_ss.c_str(), "r", stdin);
    int TestCase;
    cin >> TestCase;
    vector<int> target;
    vector<int> vis_target(n + 2, 0);
    vector<int> ask_yes(n + 2, 0);
    vector<int> col(n + 2);
    vector<int> U;
    for (int __ = 1; __ <= TestCase; __++) {
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
            vector<int> my_targets;
            if (m == n - 1) {
                auto ret = multi_select_tree(n, K, col, ask_yes, G, revG, U, GReach, revGReach, timestamp);
                query_cnt = ret.first, my_targets = ret.second;
            } else {
                auto ret = multi_select(n, K, col, ask_yes, G, revG, U, GReach, revGReach, timestamp);
                query_cnt = ret.first, my_targets = ret.second;
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
        };
        future_vector.emplace_back(pool.enqueue(run));
    }
    vector<node> output_vec;
    for (auto &&future: future_vector) {
        node cur = future.get();
        output_vec.push_back(cur);
    }
    sort(output_vec.begin(), output_vec.end());
    string query_log = "Framework_" + tmp + "_query2_log.txt";
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
        sum += query_cnt;
        max_query_cnt = max(max_query_cnt, query_cnt), minn_query_cnt = min(minn_query_cnt, query_cnt);
        sum_query_time += qu_cost;
        for (int i = 1; i < timestamp.size(); i++) {
            auto pre = timestamp[i - 1], cur = timestamp[i];
            std::chrono::duration<double> elapsed = cur - pre;
            double t = elapsed.count();
            timeGap[i] += t;
        }
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

