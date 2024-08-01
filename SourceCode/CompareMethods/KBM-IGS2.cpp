#pragma comment(linker, "/STACK:102400000,102400000")

#include <bits/stdc++.h>

using namespace std;

typedef pair<int, int> P;
typedef pair<double, int> Pd;

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


const int Maxn = 1e5 + 5;
const int Maxh = 25;
const int inf = 0x3f3f3f3f;
const int Maxk = 10;
int K = 5;
int B = 80;
int Cas_num = 1;

struct tree {
    vector<int> edge[Maxn], heavy[Maxn];
    int root, sz[Maxn], dep[Maxn], son[Maxn], top[Maxn], fa[Maxn];

    void dfs1(int x) {
        sz[x] = 1;
        if (x != root) dep[x] = dep[fa[x]] + 1;
        int ma = 0, heavy_son = x;
        for (int i = 0; i < edge[x].size(); i++) {
            int y = edge[x][i];
            if (y == fa[x]) continue;
            dfs1(y);
            sz[x] += sz[y];
            if (sz[y] > ma) {
                ma = sz[y], heavy_son = y;
            }
        }
        son[x] = heavy_son;
    }

    void dfs2(int x, int tp) {
        top[x] = tp;
        heavy[tp].push_back(x);
        if (son[x] != x) dfs2(son[x], tp);
        for (int i = 0; i < edge[x].size(); i++) {
            int y = edge[x][i];
            if (y == fa[x] || y == son[x]) continue;
            dfs2(y, y);
        }
    }

    void get_heavy() {
        dfs1(root);
        dfs2(root, root);
    }
};

vector<pair<int, int>> seq;
map<int, int> CandidatesSize;

struct graph {
    vector<int> edge[Maxn], anc[Maxn], des[Maxn], edge2[Maxn], Res;
    int n, m, root, du[Maxn], dep[Maxn], sz[Maxn], l[Maxn], par[Maxn];
    bool vis[Maxn], is_yes[Maxn], is_can[Maxn], visdp[Maxn];
    double p[Maxn], pr[Maxn], val[Maxn], g[Maxn], pyes[Maxn], pno[Maxn];
    double dp[Maxn][Maxh][Maxk], N[Maxn][Maxh][Maxk], g2[Maxn];
    double gyes[Maxn], gno[Maxn], sum_val[Maxn], fsum[Maxn], f1[Maxn];
    double Gyes[Maxn][3], Gno[Maxn][3], Pyes[Maxn][3], Pno[Maxn][3];
    bool ans[Maxn];
    tree heavy_tree;
    vector<vector<int>> Graph;

    void input() {
        cin >> n >> m;
        Graph.resize(n + 1);
        for (int i = 1; i <= n - 1; i++) {
            int x, y;
            cin >> x >> y;
            edge[x].push_back(y);
            Graph[x].push_back(y);
            par[y] = x;
            du[y]++;
        }
    }

    void set_root(int x) {
        root = x;
        par[x] = -1;
    }

    void get_anc() {
        queue<int> q;
        for (int i = 1; i <= n; i++) dep[i] = inf;
        q.push(root);
        l[root] = dep[root] = 0;
        while (!q.empty()) {
            int x = q.front();
            anc[x].push_back(x);
            des[x].push_back(x);
            q.pop();
            for (int i = 0; i < edge[x].size(); i++) {
                int y = edge[x][i];
                du[y]--;
                l[y] = dep[y] = min(dep[y], dep[x] + 1);
                for (int j = 0; j < anc[x].size(); j++)
                    anc[y].push_back(anc[x][j]), des[anc[x][j]].push_back(y);
                if (du[y] == 0) q.push(y);
            }
        }
    }

    void dfs(int x) {
        vis[x] = true;
        for (int i = 0; i < edge2[x].size(); i++) {
            int y = edge2[x][i];
            if (vis[y]) continue;
            dfs(y);
            heavy_tree.edge[x].push_back(y);
        }
    }

    void get_heavy_tree() {
        heavy_tree.root = root;
        for (int i = 1; i <= n; i++) {
            vector<P> tmp;
            vis[i] = false;
            for (int j = 0; j < edge[i].size(); j++) {
                int y = edge[i][j];
                tmp.push_back(P(-des[y].size(), y));
            }
            sort(tmp.begin(), tmp.end());
            for (int j = 0; j < tmp.size(); j++) {
                edge2[i].push_back(tmp[j].second);
            }
        }
        dfs(root);
        heavy_tree.get_heavy();
    }

    void update_ans(vector<int> T) {
        for (int i = 1; i <= n; i++) ans[i] = false;
        for (int i = 0; i < T.size(); i++) {
            int x = T[i];
            for (int j = 0; j < anc[x].size(); j++)
                ans[anc[x][j]] = true;
        }
    }

    void init() {
        input();
        set_root(1);
        get_anc();
        get_heavy_tree();
    }

    void init_cas(vector<int> T) {
        update_ans(T);
    }

    void init_question(int type) {
        for (int i = 1; i <= n; i++) {
            pyes[i] = Pyes[i][type], pno[i] = Pno[i][type],
            gyes[i] = Gyes[i][type], gno[i] = Gno[i][type];
            g2[i] = 0;
        }
        for (int i = 1; i <= n; i++) {
            is_yes[i] = false, is_can[i] = true, visdp[i] = false;
        }
        is_yes[root] = true;
    }

    void init_dp(int x, int K) {
        for (int h = l[root]; h <= l[x]; h++)
            for (int k = 0; k <= K; k++)
                dp[x][h][k] = N[x][h][k] = 0;
    }

    bool question(int x) {
        seq.emplace_back(x, ans[x]);
        return ans[x];
    }

    double single_calp(int x, int r) {
        if (!is_can[x]) return 0;
        pyes[x] = pr[x];
        double sum_r = val[x] * (l[x] - l[r]);
        for (int i = 0; i < edge[x].size(); i++) {
            int y = edge[x][i];
            if (!is_can[y]) continue;
            sum_r += single_calp(y, r);
            pyes[x] += pyes[y];
        }
        return sum_r;
    }


    Pd method2_calg(int x, double sum_r, double psum, int r) {
        double mi = inf;
        int id = 0;
        gyes[x] = 0, sum_val[x] = val[x];
        for (int i = 0; i < edge[x].size(); i++) {
            int y = edge[x][i];
            if (!is_can[y]) continue;
            Pd tmp = method2_calg(y, sum_r, psum, r);
//            debug(x,y);
            if (tmp.first < mi) {
                mi = tmp.first, id = tmp.second;
            }
            gyes[x] += gyes[y], sum_val[x] += sum_val[y];
        }
        gyes[x] += sum_val[x] - val[x];
        gno[x] = sum_r - gyes[x] - (l[x] - l[r]) * sum_val[x];
        double tmp = gyes[x] * pyes[x] + gno[x] * (psum - pyes[x]);
//        debug(x,gyes[x],gno[x],tmp);
        if (tmp < mi) {
            mi = tmp, id = x;
        }
//        debug(mi,id);
        return Pd(mi, id);
    }

    pair<int, int> single_question_method2() {
        int r = root;
        double psum = 1;
        for (int i = 1; i <= n; i++) is_can[i] = true;
        int query_cnt = 0;
        unordered_map<int, bool> asked;
        while (true) {
            double sum_r = single_calp(r, r);
            int x = method2_calg(r, sum_r, psum, r).second;
            if (asked[x]) break;
            asked[x] = true;
            query_cnt++;
            if (question(x)) { r = x, psum = pyes[r]; }
            else { is_can[x] = false, psum = pyes[r] - pyes[x]; }
        }
        return {r, query_cnt};
    }

    double question_method2_calp(int x, double rate) {
        pno[x] = 1 - pr[x] * rate;
        for (int i = 0; i < edge[x].size(); i++) {
            int y = edge[x][i];
            if (!is_yes[x] && !is_can[x]) continue;
            pno[x] *= question_method2_calp(y, rate);
        }
        if (is_yes[x]) {
            pno[x] = 0;
            pyes[x] = 1;
            return 0;
        }
        pyes[x] = 1 - pno[x];
        return pno[x];
    }

    void calg1_dfs(int x) {
        if (!is_yes[x] && !is_can[x]) {
            fsum[x] = sum_val[x] = 0;
            return;
        }
        if (is_can[x]) sum_val[x] = val[x]; else sum_val[x] = 0;
        fsum[x] = sum_val[x] * (l[x] - l[root]);
        for (int i = 0; i < edge[x].size(); i++) {
            int y = edge[x][i];
            calg1_dfs(y);
            fsum[x] += fsum[y];
            sum_val[x] += sum_val[y];
        }
        return;
    }

    void calg1(int K, double delta) {
        calg1_dfs(root);
        set<Pd> H;
        for (int i = 1; i <= n; i++) {
            f1[i] = sum_val[i] * (l[i] - l[root]);
            if (!is_yes[i]) continue;
            H.insert(Pd(f1[i], i));
        }
        set<Pd> H2;
        delta = max(0., delta);
        for (int u = 1; u <= n; u++) {
            if (is_yes[u] || !is_can[u]) continue;
            H2.insert(Pd(g2[u], u));
        }
        set<Pd>::iterator ite;
        double mi = inf;
        for (ite = H2.begin(); ite != H2.end(); ite++) {
            int u = ite->second;
            if ((ite->first) > mi) break;
            int v = u;
            double tmp_sum = 0, dec_sum = 0;
            vector<Pd> tmp_vec;
            while (v != root) {
                if (is_can[v] && v != u) tmp_sum += val[v], dec_sum += val[v] * (l[v] - l[root]);
                tmp_vec.push_back(Pd(f1[v], v));
                double tmp = f1[v];
                f1[v] -= (l[v] - l[root]) * tmp_sum;
                if (!is_yes[v]) H.insert(Pd(f1[v], v));
                else {
                    H.erase(Pd(tmp, v));
                    H.insert(Pd(f1[v], v));
                }
                v = par[v];
            }
            double topk_sum = 0;
            set<Pd>::iterator ite = H.end();
            int cnt = 0;
            while (ite != H.begin() && cnt < K) {
                ite--;
                cnt++;
                topk_sum += ite->first;
            }
            gyes[u] = fsum[root] - dec_sum - topk_sum;
            for (int i = 0; i < tmp_vec.size(); i++) {
                double tmp = tmp_vec[i].first;
                v = tmp_vec[i].second;
                H.erase(Pd(f1[v], v));
                if (is_yes[v]) H.insert(Pd(tmp, v));
                f1[v] = tmp;
            }
            tmp_vec.clear();
            v = u;
            while (v != root) {
                tmp_vec.push_back(Pd(f1[v], v));
                double tmp = f1[v];
                f1[v] -= sum_val[u] * (l[v] - l[root]);
                if (is_yes[v]) {
                    H.erase(Pd(tmp, v));
                    H.insert(Pd(f1[v], v));
                }
                v = par[v];
            }
            topk_sum = 0;
            ite = H.end();
            cnt = 0;
            while (ite != H.begin() && cnt < K) {
                ite--;
                cnt++;
                topk_sum += ite->first;
            }
            gno[u] = fsum[root] - fsum[u] - topk_sum;
            for (int i = 0; i < tmp_vec.size(); i++) {
                double tmp = tmp_vec[i].first;
                v = tmp_vec[i].second;
                if (is_yes[v]) {
                    H.erase(Pd(f1[v], v));
                    H.insert(Pd(tmp, v));
                }
                f1[v] = tmp;
            }
            mi = min(mi, pyes[u] * gyes[u] + pno[u] * gno[u]);
            mi = max(1e-8, mi);
        }
    }

    void cal_dp(int x, int K) {
        if (!is_yes[x] && !is_can[x]) return;
        visdp[x] = true;
        for (int i = 0; i < edge[x].size(); i++) {
            int y = edge[x][i];
            if (visdp[y]) continue;
            cal_dp(y, K);
        }
        for (int h = l[root]; h <= l[x]; h++) {
            for (int k1 = 0; k1 <= K; k1++) N[x][h][k1] = 0;
            for (int i = 0; i < edge[x].size(); i++) {
                int y = edge[x][i];
                double tmp[Maxk] = {};
                for (int k1 = 0; k1 <= K; k1++) tmp[k1] = N[x][h][k1];
                for (int k1 = 0; k1 <= K; k1++) {
                    for (int k2 = 0; k2 <= k1; k2++) {
                        if (N[x][h][k1 - k2] + dp[y][h][k2] > tmp[k1])
                            tmp[k1] = max(tmp[k1], N[x][h][k1 - k2] + dp[y][h][k2]);
                    }
                }
                for (int k1 = 0; k1 <= K; k1++) N[x][h][k1] = tmp[k1];
            }
            for (int k1 = 0; k1 <= K; k1++) {
                if (is_can[x]) N[x][h][k1] += (h - l[root]) * val[x];
            }
        }
        for (int h = l[root]; h <= l[x]; h++)
            for (int k1 = 0; k1 <= K; k1++) {
                if (k1 > 0 && is_yes[x] && h < l[x])
                    dp[x][h][k1] = max(N[x][h][k1], N[x][l[x]][k1 - 1]);
                else
                    dp[x][h][k1] = N[x][h][k1];
            }

    }

    vector<vector<vector<int> > > select_dp(int x, int K) {
        vector<vector<vector<vector<int> > > > dpS;
        vector<vector<vector<int> > > S;
        if (!is_yes[x] && !is_can[x]) return S;
        for (int i = 0; i < edge[x].size(); i++) {
            int y = edge[x][i];
            dpS.push_back(select_dp(y, K));
        }
        for (int h = l[root]; h <= l[x]; h++) {
            for (int k1 = 0; k1 <= K; k1++) N[x][h][k1] = 0;
            vector<int> zero_vec1;
            vector<vector<int> > zero_vec2;
            for (int k1 = 0; k1 <= K; k1++) zero_vec2.push_back(zero_vec1);
            S.push_back(zero_vec2);
            for (int i = 0; i < edge[x].size(); i++) {
                int y = edge[x][i];
                if (!is_yes[y] && !is_can[y]) continue;
                double tmp[Maxk] = {};
                vector<int> tmpS[Maxk];
                for (int k1 = 0; k1 <= K; k1++) tmp[k1] = N[x][h][k1], tmpS[k1] = S[h][k1];
                for (int k1 = 0; k1 <= K; k1++) {
                    for (int k2 = 0; k2 <= k1; k2++) {
                        if (N[x][h][k1 - k2] + dp[y][h][k2] > tmp[k1]) {
                            tmp[k1] = max(tmp[k1], N[x][h][k1 - k2] + dp[y][h][k2]);
                            tmpS[k1].clear(),
                                    tmpS[k1].insert(tmpS[k1].end(), S[h][k1 - k2].begin(), S[h][k1 - k2].end()),
                                    tmpS[k1].insert(tmpS[k1].end(), dpS[i][h][k2].begin(), dpS[i][h][k2].end());
                        }
                    }
                }
                for (int k1 = 0; k1 <= K; k1++)
                    N[x][h][k1] = tmp[k1], S[h][k1] = tmpS[k1], tmpS[k1].clear();
            }
            for (int k1 = 0; k1 <= K; k1++) {
                if (is_can[x]) N[x][h][k1] += (h - l[root]) * val[x];
            }
        }
        for (int h = l[root]; h <= l[x]; h++)
            for (int k1 = 0; k1 <= K; k1++) {
                if (k1 > 0 && is_yes[x] && h < l[x]) {
                    if (N[x][h][k1] < N[x][l[x]][k1 - 1])
                        S[h][k1] = S[l[x]][k1 - 1], S[h][k1].push_back(x);
                    dp[x][h][k1] = max(N[x][h][k1], N[x][l[x]][k1 - 1]);
                } else
                    dp[x][h][k1] = N[x][h][k1];
            }

        return S;
    }

    void calg2(int K, double delta) {
        cal_dp(root, K);
        calg1_dfs(root);
        set<Pd> H;
        delta = max(0., delta);
        for (int u = 1; u <= n; u++) {
            if (is_yes[u] || !is_can[u]) continue;
            H.insert(Pd(g2[u], u));
        }
        set<Pd>::iterator ite;
        double mi = inf;
        for (ite = H.begin(); ite != H.end(); ite++) {
            int u = ite->second;
            //if (u == 365) printf("%d %.3f %.3f %.3f %.3f\n", u, g2[u], gyes[u], gno[u], mi);
            if ((ite->first) > mi) break;
            double tmpdp[Maxh][Maxh][Maxk] = {}, tmpN[Maxh][Maxh][Maxk] = {};
            bool tmp_is_can[Maxh] = {}, tmp_is_yes[Maxh] = {};
            double tmp_sum = 0, dec_sum = 0;
            for (int i = 0; i < anc[u].size(); i++) {
                int v = anc[u][i];
                visdp[v] = false;
                for (int h = l[root]; h <= l[v]; h++)
                    for (int k = 0; k <= K; k++)
                        tmpdp[i][h][k] = dp[v][h][k], tmpN[i][h][k] = N[v][h][k];
                if (is_can[v] && v != u) {
                    dec_sum += val[v] * (l[v] - l[root]);
                    is_can[v] = false;
                    tmp_is_can[i] = true;
                }
                tmp_is_yes[i] = is_yes[v];
                is_yes[v] = true;
                //if (u == 20153) printf("%d %d %d %d\n", v, visdp[v], is_yes[v], is_can[v]);
            }
            cal_dp(root, K);
            //if (u == 365) printf("%.3f %.3f %.3f\n", fsum[root], dec_sum, dp[root][l[root]][K]);
            gyes[u] = fsum[root] - dec_sum - dp[root][l[root]][K];
            for (int i = 0; i < anc[u].size(); i++) {
                int v = anc[u][i];
                for (int h = l[root]; h <= l[v]; h++)
                    for (int k = 0; k <= K; k++)
                        dp[v][h][k] = tmpdp[i][h][k], N[v][h][k] = tmpN[i][h][k];
                if (tmp_is_can[i] && v != u) {
                    is_can[v] = true;
                }
                is_yes[v] = tmp_is_yes[i];
            }
            for (int i = 0; i < anc[u].size(); i++) {
                int v = anc[u][i];
                visdp[v] = false;
                for (int h = l[root]; h <= l[v]; h++)
                    for (int k = 0; k <= K; k++)
                        tmpdp[i][h][k] = dp[v][h][k], tmpN[i][h][k] = N[v][h][k];
            }
            visdp[u] = true;
            init_dp(u, K);
            cal_dp(root, K);
            gno[u] = fsum[root] - fsum[u] - dp[root][l[root]][K];
            for (int i = 0; i < anc[u].size(); i++) {
                int v = anc[u][i];
                for (int h = l[root]; h <= l[v]; h++)
                    for (int k = 0; k <= K; k++)
                        dp[v][h][k] = tmpdp[i][h][k], N[v][h][k] = tmpN[i][h][k];
            }
            mi = min(mi, pyes[u] * gyes[u] + pno[u] * gno[u]);
            //if (u == 365) printf("%d %.3f %.3f %.3f %.3f\n", u, g2[u], gyes[u], gno[u], mi);
            mi = max(1e-8, mi);
        }
    };

    void first_question(int type, int K) {
        for (int i = 1; i <= n; i++) {
            pyes[i] = 0, pno[i] = 0,
            gyes[i] = 0, gno[i] = 0;
            g2[i] = 0;
        }
        for (int i = 1; i <= n; i++) {
            is_yes[i] = false, is_can[i] = true;
            if (type == 2) visdp[i] = false;
        }
        is_yes[root] = true;
        question_method2_calp(root, 1);
        //printf("ok\n");
        if (type == 1)
            calg1(K, 0);
        if (type == 2)
            calg2(K, 0);
        for (int i = 1; i <= n; i++) {
            if (is_yes[i] || !is_can[i]) continue;
            double tmp = pyes[i] * gyes[i] + pno[i] * gno[i];
            Pyes[i][type] = pyes[i], Pno[i][type] = pno[i];
            Gyes[i][type] = gyes[i], Gno[i][type] = gno[i];
        }
    }

    vector<int> multi_recommend_1(int K) {
        calg1_dfs(root);
        set<Pd> H;
        for (int i = 1; i <= n; i++) {
            f1[i] = sum_val[i] * (l[i] - l[root]);
            if (!is_yes[i]) continue;
            //printf("%d %.2f\n", i, f1[i]);
            H.insert(Pd(f1[i], i));
        }
        vector<int> ans;
        set<Pd>::iterator ite = H.end();
        int cnt = 0;
        while (ite != H.begin() && cnt < K) {
            ite--;
            cnt++;
            ans.push_back(ite->second);
        }
        return ans;
    }

    vector<int> multi_recommend_2(int K) {
        vector<int> ans;
        return select_dp(root, K)[l[root]][K];
    }

    vector<int> multi_recommend_3(int K) {
        vector<int> ans;
        for (int i = 1; i <= n; i++) {
            int flag = true;
            if (!is_yes[i]) continue;
            //printf("%d %.2f\n", i, f1[i]);
            //cout << i << endl;
            for (int j = 0; j < edge[i].size(); j++) {
                //cout << i << " " << edge[i][j] << endl;
                if (is_yes[edge[i][j]]) {
                    flag = false;
                    break;
                }
            }
            //cout << i << endl;
            if (flag) ans.push_back(i);
        }
        return ans;
    }

    pair<vector<int>, int> multi_question_method2(int type, int K, int B) {
        if (type == 3) init_question(1); else init_question(type);
        int cnum = n;
        cal_dp(root, K);
        calg1_dfs(root);
        double pre_g = fsum[root];
//        for (int b = 1; b <= B; b++) {
        int query_cnt = 0;
        while (true) {
            int tot = 0;
            for (int i = 1; i <= n; i++) {
                if (is_can[i]) tot++;
            }
            CandidatesSize[query_cnt] += tot;
            if (tot == K) {
                vector<int> ret;
                for (int i = 1; i <= n; i++) {
                    if (is_can[i]) ret.push_back(i);
                }
                return {ret, query_cnt};
                break;
            }
            double mi = inf;
            int id = 0;
            double delta_g = 0;
            for (int i = 1; i <= n; i++) {
                if (is_yes[i] || !is_can[i]) continue;
                double tmp = pyes[i] * gyes[i] + pno[i] * gno[i];
                g2[i] = tmp;
                if (tmp < mi) {
                    mi = min(mi, tmp);
                    id = i;
                }
            }
            bool res = question(id);
            query_cnt++;
            if (res) {
                delta_g = pre_g - gyes[id];
                pre_g = gyes[id];
                for (int i = 0; i < anc[id].size(); i++) {
                    int x = anc[id][i];
                    is_yes[x] = true;
                    if (x != id) {
                        if (is_can[x]) cnum--;
                        is_can[x] = false;
                    }
                }
                if (type == 2) {
                    for (int i = 0; i < anc[id].size(); i++) {
                        int x = anc[id][i];
                        visdp[x] = false;
                    }
                }
            } else {
                delta_g = pre_g - gno[id];
                pre_g = gno[id];
                for (int i = 0; i < des[id].size(); i++) {
                    int x = des[id][i];
                    //pr[x] = 0;
                    if (is_can[x]) cnum--;
                    is_can[x] = false;
                }
                if (type == 2) {
                    for (int i = 0; i < anc[id].size(); i++) {
                        int x = anc[id][i];
                        if (x != id) visdp[x] = false;
                    }
                    init_dp(id, K);
                }
            }
            bool tag = true;
            for (int i = 1; i <= n; i++) {
                if (is_yes[i] || !is_can[i]) continue;
                tag = false;
                break;
            }
            if (tag) break;
            question_method2_calp(root, 1.0 * n / cnum);
            for (int i = 1; i <= n; i++) {
                if (is_yes[i] || !is_can[i]) continue;
                double tmp = pyes[i] * gyes[i] + pno[i] * gno[i];
                if (!res) gyes[i] -= fsum[id], gno[i] -= delta_g;
                else gyes[i] -= delta_g, gno[i] = pre_g - fsum[i];
                g2[i] = 0;
            }
            if (type == 1)
                calg1(K, delta_g);
            if (type == 2)
                calg2(K, delta_g);
            if (type == 3)
                calg1(K, delta_g);
        }
//        if (type == 1) return multi_recommend_1(K);
//        if (type == 2) return multi_recommend_2(K);
//        if (type == 3) return multi_recommend_3(K);
    }

    void multi_method1_dfs(int x, double sum_yes) {
        gyes[x] = sum_yes;
        double sum_no = 0;
        if (is_can[x]) sum_yes += val[x], sum_no += val[x];
        for (int i = 0; i < edge[x].size(); i++) {
            int y = edge[x][i];
            multi_method1_dfs(y, sum_yes);
            sum_no += gno[y];
        }
        gno[x] = sum_no;
        return;
    }

    vector<int> multi_question_method1(int type, int K) {
        init_question(0);
        for (int b = 1; b <= B; b++) {
            multi_method1_dfs(root, 0);
            double ma = -1;
            int id = 0;
            for (int i = 1; i <= n; i++) {
                if (is_yes[i] || !is_can[i]) continue;
                double tmp = min(gyes[i], gno[i]);
                if (tmp > ma) {
                    ma = max(ma, tmp);
                    id = i;
                }
            }
            bool res = question(id);
            if (res) {
                for (int i = 0; i < anc[id].size(); i++) {
                    int x = anc[id][i];
                    is_yes[x] = true;
                    if (x != id) {
                        is_can[x] = false;
                    }
                }
            } else {
                for (int i = 0; i < des[id].size(); i++) {
                    int x = des[id][i];
                    is_can[x] = false;
                }
            }
            bool tag = true;
            for (int i = 1; i <= n; i++) {
                if (is_yes[i] || !is_can[i]) continue;
                tag = false;
                break;
            }
            if (tag) break;
        }
        if (type == 1) return multi_recommend_1(K);
        if (type == 2) return multi_recommend_2(K);
        if (type == 3) return multi_recommend_3(K);
    }

    vector<int> recommend_random() {
        vector<int> S;
        for (int i = 0; i < Res.size(); i++) S.push_back(Res[i]);
        for (int num = Res.size() + 1; num <= K; num++) {
            int x = ((unsigned int) rand() * 65536 + rand()) % n + 1;
            while (p[x] == 0) x = ((unsigned int) rand() * 65536 + rand()) % n + 1;
            S.push_back(x);
        }
        return S;
    }

    void update_dist(int root, int dis[]) {
        queue<P> q;
        q.push(P(root, 0));
        bool vis[Maxn] = {};
        vis[root] = true;
        dis[root] = 0;
        while (!q.empty()) {
            P tmp = q.front();
            q.pop();
            int x = tmp.first, dep = tmp.second + 1;
            for (int i = 0; i < edge[x].size(); i++) {
                int y = edge[x][i];
                if (vis[y] || dis[y] <= dep) continue;
                dis[y] = dep;
                q.push(P(y, dep));
                vis[y] = true;
            }
        }
    }

    double get_score(int root, int dis[]) {
        queue<P> q;
        q.push(P(root, 0));
        bool vis[Maxn] = {};
        vis[root] = true;
        int score = 0;
        while (!q.empty()) {
            P tmp = q.front();
            q.pop();
            int x = tmp.first, dep = tmp.second + 1;
            score += (dis[x] - dep) * p[x];
            for (int i = 0; i < edge[x].size(); i++) {
                int y = edge[x][i];
                if (vis[y] || dis[y] <= dep) continue;
                q.push(P(y, dep));
                vis[y] = true;
            }
        }
        return score;
    }

    int get_score(vector<int> S, vector<int> T) {
        int score = 0, reach_num = 0;
        queue<int> q;
        int vis[Maxn] = {};
        for (int i = 1; i <= n; i++) vis[i] = dep[i];
        for (int i = 0; i < S.size(); i++) q.push(S[i]), vis[S[i]] = 0;
        while (!q.empty()) {
            int x = q.front();
            q.pop();
            for (int i = 0; i < edge[x].size(); i++) {
                int y = edge[x][i];
                if (vis[y] > vis[x] + 1) {
                    vis[y] = vis[x] + 1;
                    q.push(y);
                }
            }
        }
        for (int i = 0; i < T.size(); i++) {
            int x = T[i];
            score += vis[x];
        }
        return score;
    }

    pair<vector<int>, int> solve_multi(vector<int> T) {
        init_cas(T);
        auto tmp = multi_question_method2(1, (int) T.size(), B);
        return tmp;
    }

    pair<int, int> solve_single(int x) {
        vector<int> vec;
        vec.push_back(x);
        update_ans(vec);
        auto res = single_question_method2();
        return res;
    }
} G;

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

string TMP;

void solve() {
    string ss = TMP + ".txt";
    freopen(ss.c_str(), "r", stdin);
    G.init();
    string query_ss = TMP + "_query2.txt";
    freopen(query_ss.c_str(), "r", stdin);

    string query_log = "KBMIGS_" + TMP + "_query2_log.txt";
    freopen(query_log.c_str(), "w", stdout);
    int cas;
    cin >> cas;
    for (int i = 1; i <= G.n; i++) {
        G.val[i] = 1, G.pr[i] = 1.0 * K / G.n;
    }
    G.first_question(1, K);
    G.first_question(2, K);
    double sum_query_cnt = 0, average_query_cnt = 0;
    int max_query_cnt = 0, minn_query_cnt = G.n + 1;
    double sum_query_time = 0;
    double sum = 0, sum1 = 0, sum2 = 0, sum3 = 0, sumt1 = 0, sumt2 = 0, sumt3 = 0;
    for (int i = 0; i < cas; i++) {
        int score, score1, score2, score3;
        double t1, t2, t3;
        int t, x;
        cin >> t;
        cout << "query #" << i + 1 << ":" << endl;
        vector<int> tmp;
        while (t--) {
            cin >> x;
            tmp.push_back(x);
        }
        if (tmp.size() == 1) {
            double qu_st = 1.0 * clock() / CLOCKS_PER_SEC;
            auto [my_target, query_cnt] = G.solve_single(tmp[0]);
            double qu_ed = 1.0 * clock() / CLOCKS_PER_SEC;
            double qu_cost = qu_ed - qu_st;
            sum_query_time += qu_cost;
            sum_query_cnt += query_cnt;
            max_query_cnt = max(max_query_cnt, query_cnt);
            minn_query_cnt = min(minn_query_cnt, query_cnt);
            cout << "my_target: " << my_target << "   answer_target: " << tmp[0] << "\n";
            cout << "query_cnt: " << query_cnt << "\n" << endl;
            deal_Candidates(G.n, G.Graph);
            seq.clear();
        } else {
            double qu_st = 1.0 * clock() / CLOCKS_PER_SEC;
            auto [targets, query_cnt] = G.solve_multi(tmp);
            double qu_ed = 1.0 * clock() / CLOCKS_PER_SEC;
            double qu_cost = qu_ed - qu_st;
            sort(tmp.begin(), tmp.end());
            sort(targets.begin(), targets.end());
            if (targets != tmp) {
                for (auto j: targets) cout << j << " ";
                cout << endl;
                for (auto j: tmp) cout << j << " ";
                cout << endl;
                cout << "Wrong" << endl;
                exit(0);
            }
            cout << "targets: ";
            for (auto j: targets) cout << j << " ";
            cout << "\n";
            cout << "query_cnt: " << query_cnt << "\n" << endl;
            cout << "cur_cost: " << qu_cost << "\n" << endl;
            sum_query_time += qu_cost;
            sum_query_cnt += query_cnt;
            max_query_cnt = max(max_query_cnt, query_cnt);
            minn_query_cnt = min(minn_query_cnt, query_cnt);
            seq.clear();
        }
    }
    cout << "max_query_cnt: " << max_query_cnt << "\n";
    cout << "min_query_cnt: " << minn_query_cnt << "\n";
    cout << "avg_query_cnt: " << fixed << setprecision(8) << sum_query_cnt / cas << "\n";
    cout << "avg_cost: " << fixed << setprecision(8) << sum_query_time / cas << "\n" << endl;

    cout << "PotentialTargetSize: \n";
    for (auto [cur_query_cnt, PSize]: CandidatesSize) {
        cout << cur_query_cnt << " " << 1.0 * PSize / cas << "\n";
    }

}

signed main(int argc, char *argv[]) {
    ios::sync_with_stdio(false), cin.tie(nullptr);
    TMP = argv[1];
    solve();
    return 0;
}
/*
10
1 2
1 3
2 4
2 5
2 6
4 7
4 8
4 9
6 10
10
2
6 9
2
5 9
2
6 7

8961 Yes 10
8348 Yes 11

12688
38707 8348
*/
