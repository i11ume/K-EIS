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

const ll LINF = 0x3f3f3f3f3f3f3f3f;
const int INF = 0x3f3f3f3f;//2147483647;
const ll MOD[2] = {1000000007, 998244353};
const ll BASE[2] = {131, 13331};
const double pi = acos(-1.0);

const int N = 2e5 + 10, M = N << 1;
const ll mod = MOD[0];


map<int, int> CandidatesSize;

int ask(int x, vector<int> &ask_yes, vector<pair<int, int>> &seq) {
//    debug(x);
    seq.emplace_back(x, ask_yes[x]);
    if (ask_yes[x])return 1;
    return 0;
}

void deal_Candidates(int n, vector<vector<int>> &G, vector<pair<int, int>> &seq) {
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

string TMP;

pair<int, int> BinG_DAG(int root, int n, vector<int> &ask_yes, vector<vector<int>> &G, vector<pair<int, int>> &seq) {
    int r = root;
    int sum_node = n;
    int cnt = 0;
    vector<bool> is_ask(n + 2, false);
    vector<bool> is_can(n + 2, true);
    vector<int> pyes(n + 2);
    while (true) {
        int ma = -1;
        int id = -1;
        vector<int> VS;
        for (int i = 1; i <= n; i++) {
            if (!is_can[i])continue;
            pyes[i] = 1;
            queue<int> q;
            vector<int> vis(n + 2);
            vis[i] = 1;
            q.push(i);
            while (!q.empty()) {
                int u = q.front();
                q.pop();
                for (auto v: G[u]) {
                    if (!is_can[v])continue;
                    if (vis[v])continue;
                    vis[v] = 1;
                    q.push(v);
                    pyes[i]++;
                }
            }
            int cur = min(pyes[i], sum_node - pyes[i]);
            if (cur > ma) {
                ma = cur;
                id = i;
                VS = vis;
            }
        }
        if (id == -1 || is_ask[id])break;
        is_ask[id] = true;
        cnt++;
        if (ask(id, ask_yes, seq)) {
            r = id, sum_node = pyes[r];
            for (int i = 1; i <= n; i++) {
                if (!VS[i]) {
                    is_can[i] = false;
                }
            }
        } else {
            sum_node = pyes[r] - pyes[id];
            for (int i = 1; i <= n; i++) {
                if (VS[i]) {
                    is_can[i] = false;
                }
            }
        }
    }
    return {r, cnt};
}


struct node {
    int id;
    vector<int> targets;
    vector<int> ans_targets;
    double qu_cost;
    int query_cnt;
    vector<pair<int, int>> seq;

    bool operator<(const node &b) const {
        return id < b.id;
    }
};

void solve() {
    ThreadPool pool(std::thread::hardware_concurrency() / 2 + 1);
    std::vector<std::future<node>> future_vector;

    string ss = TMP + ".txt";
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

    string query_ss = TMP + "_query.txt";
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
        // init_query()  O(n)
        for (auto i: target) {
            init_query(i, ask_yes, revG);
        }
        auto run = [=]() mutable {
            vector<pair<int, int>> seq;
            auto qu_st = std::chrono::high_resolution_clock::now();
            auto [my_target, query_cnt] = BinG_DAG(rt, n+1, ask_yes, G, seq);
            vector<int> my_targets;
            my_targets.push_back(my_target);
            auto qu_ed = std::chrono::high_resolution_clock::now();
            std::chrono::duration<double> elapsed = qu_ed - qu_st;
            double qu_cost = elapsed.count();
            node cur;
            cur.id = __;
            cur.query_cnt = query_cnt, cur.qu_cost = qu_cost;
            sort(target.begin(), target.end()), sort(my_targets.begin(), my_targets.end());
            cur.ans_targets = target, cur.targets = my_targets;
            cur.seq = seq;
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

    string query_log = "BinG_DAG_" + TMP + "_query_log.txt";
    freopen(query_log.c_str(), "w", stdout);

    double sum = 0;
    int max_query_cnt = 0, minn_query_cnt = n + 1;
    double sum_query_time = 0;

    for (auto [id, targets, ans_targets, qu_cost, query_cnt, seq]: output_vec) {
        cout << "query #" << id << ":" << endl;
        if (targets != ans_targets) {
            cout << "targets: ";
            for (auto i: targets) cout << i << " ";
            cout << "\n";
            cout << "ans_targets: ";
            for (auto i: ans_targets) cout << i << " ";
            cout << "\n";
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
        deal_Candidates(n, G, seq);
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
    TMP = argv[1];
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

