#include <bits/stdc++.h>
#include <map>
#include <set>
#include <vector>
#include <algorithm>
#include <iostream>
#include <bitset>
#include <cassert>
#include <queue>
#include <stack>
#include <iomanip>
#include <math.h>
#include <time.h>
#include <chrono>
#include <random>
using namespace std;
using namespace chrono;
#define rep(i, n) for (int i = 0; i < (int)n; i++)
#define repf(i, a, b) for (int i = (int)a; i < (int)b; i++)
#define repr(i, a, b) for (int i = (int)a; i > (int)b; i--)
#define all(v) (v).begin(), (v).end()
#define mp(a, b) make_pair(a, b)
#define eb(x) emplace_back(x)
#define F first
#define S second
typedef long long ll;
typedef long double ld;
typedef pair<int, int> pii;
typedef pair<ll, ll> pll;
typedef pair<ld, ld> pdd;
typedef vector<ll> vll;
typedef vector<vll> vvll;
typedef vector<int> vii;
typedef vector<vii> vvii;
const ll mod = 1e9 + 7;
const int infi = 1147483600;
const ll infl = 4e18 + 5;
const char ENDL = '\n';
//cout << fixed << setprecision(17) << res << endl;
const ll MOD = 998244353;

bool debug = false;
bool time_display = false;

const ll T = 10000;
const ll MAX_V = 400;
const ll MIN_V = 200;
const int MAX_Degree = 5;
const ll MAX_DIST = 5000;

inline int string_to_int(string s)
{
    int ans = 0;
    rep(i, s.size())
    {
        ans *= 10;
        ans += (int)((char)s[i] - '0');
    }
    return ans;
}

string int_to_string(int i)
{
    if (i == 0)
        return "00";
    vector<char> moji;
    while (i > 0)
    {
        moji.push_back((char)(i % 10 + (int)'0'));
        i /= 10;
    }
    string ans = "";
    repr(s, moji.size() - 1, -1) ans += moji[s];
    if (ans.size() < 2)
        return "0" + ans;
    return ans;
}

void read_csv(string path, vector<int> &output)
{
    ifstream ifs(path);
    string str_buf;
    string str_conma_buf;
    int idx = 0;
    while (getline(ifs, str_buf))
    {
        istringstream i_stream(str_buf);
        while (getline(i_stream, str_conma_buf, ','))
        {
            output[idx] = (string_to_int(str_conma_buf));
            idx++;
        }
    }
    ifs.close();
}

ld calc_value(int t, vector<ld> hav)
{
    ld cons = T * T - t * t;
    return (cons * hav[0] + (ld)2.0 * (ld)t * hav[1] - hav[2]);
}

bool comp_max(ld &a, ld b)
{
    if (a < b)
    {
        a = b;
        return true;
    }
    else
    {
        return false;
    }
}

static uint32_t randxor()
{
    static uint32_t x = 123456789;
    static uint32_t y = 362436069;
    static uint32_t z = 521288629;
    static uint32_t w = 88675123;
    uint32_t t;
    t = x ^ (x << 11);
    x = y;
    y = z;
    z = w;
    return w = (w ^ (w >> 19)) ^ (t ^ (t >> 8));
}

random_device rnd;
mt19937 mt11(rnd());

static double randxor01()
{
    return (randxor() + 0.5) * (1.0 / UINT_MAX);
}

ll CALC_MAIN(string path, int orders_to_move, int deadline)
{

    auto startClock = system_clock::now();
    if (debug && time_display)
    {
        cout << "CALC_MAIN start at : "
             << duration_cast<microseconds>(startClock - startClock).count() * 1e-6
             << ENDL;
    }

    ll score = 0;

    //input
    vector<int> input_data(32500);
    if (debug)
    {
        read_csv(path, input_data);
    }
    else
    {
        cin >> input_data[0] >> input_data[1];
        rep(i, input_data[1]) cin >> input_data[3 * i + 2] >> input_data[3 * i + 3] >> input_data[3 * i + 4];
        cin >> input_data[(3 * input_data[1] + 2)];
        int idx = 3 * input_data[1] + 3;
        rep(t, T)
        {
            cin >> input_data[idx];
            if (input_data[idx])
            {
                cin >> input_data[idx + 1] >> input_data[idx + 2];
                idx += 2;
            }
            idx++;
        }
    }
    if (debug && time_display)
    {
        cout << "input end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    //initialize
    int V, E;
    V = input_data[0];
    E = input_data[1];
    vector<multimap<int, int>> edge(V);
    rep(i, E)
    {
        int u, v, d;
        u = input_data[3 * i + 2] - 1;
        v = input_data[3 * i + 3] - 1;
        d = input_data[3 * i + 4];
        edge[u].insert(mp(v, d));
        edge[v].insert(mp(u, d));
    }
    if (debug && time_display)
    {
        cout << "init end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    //距離の計算
    vector<vector<ld>> dist(V, vector<ld>(V, infi));
    rep(i, V)
    {
        //頂点iからのダイクストラ
        multiset<pair<int, int>> search;
        dist[i][i] = 0;
        search.insert(mp(0, i));
        while (true)
        {
            if (search.empty())
                break;
            int now = (*search.begin()).S;
            search.erase(search.begin());
            for (auto itr = edge[now].begin(); itr != edge[now].end(); itr++)
            {
                int nex = (*itr).F;
                int d = (*itr).S;
                if (dist[i][now] + d < dist[i][nex])
                {
                    dist[i][nex] = dist[i][now] + d;
                    search.insert(mp(dist[i][nex], nex));
                }
            }
        }
    }
    if (debug && time_display)
    {
        cout << "calc dist end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    //main_treatment
    //注文がk個以上のときすべて回る（0を通ったら追加する）
    //注文がk個未満のとき0へ向かう。（配達完了処理もちゃんとする）

    vector<int> ans(T, -2);
    int idx = 3 * E + 3;

    vector<int> ord_id(T, -1);  //時刻tの注文のID
    int bef = 0;                //最後に店舗を訪れた時刻
    vector<set<int>> order(V);  //受注した注文
    multimap<int, int> ord_all; //受注した注文の時刻、場所。bef以下で最大の注文場所へ向かう
    vector<vector<ld>> ord_have(V, vector<ld>(3, 0));
    vector<vector<ld>> ord_nhave(V, vector<ld>(3, 0));
    vector<int> ord_cnt(2, 0);

    vector<int> now(4, 0); //辺(u,v)のuから距離dの地点にいて、最終的にwに向かっている
    //main_loop

    if (debug && time_display)
    {
        cout << "main init end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    bool check9500 = true;
    bool go9500 = false;
    int t_last = T;
    int z = 0;
    rep(t, T)
    {
        //時刻tからt+1の処理をおこなう

        //注文を受け取る
        int ord_num = input_data[idx];
        idx++;
        if (ord_num)
        {
            z++;

            ord_id[t] = input_data[idx];
            idx++;
            int target = input_data[idx] - 1;
            idx++;
            order[target].insert(t);
            ord_all.insert(mp(t, target));

            //各頂点の評価更新
            ord_cnt[0]++;
            ord_nhave[target][0]++;
            ord_nhave[target][1] += t;
            ord_nhave[target][2] += pow(t, 2);
        }
        //商品を積む
        if (now[0] == now[1] && now[0] == 0)
        {
            ord_cnt[1] += ord_cnt[0];
            ord_cnt[0] = 0;
            rep(i, V)
            {
                rep(j, 3)
                {
                    ord_have[i][j] += ord_nhave[i][j];
                    ord_nhave[i][j] = 0;
                }
            }
            bef = t;
        }

        //行動の決定
        bool search_next = false;

        //9500のチェックなど
        if (check9500)
        {
            if (now[2] > 0)
            {
                int dist_a = t + dist[now[0]][0] + now[2];
                int dist_b = t + dist[now[1]][0] + (*edge[now[0]].find(now[1])).S - now[2];
                if (dist_a >= 9500 && dist_b >= dist_a)
                {
                    check9500 = false;
                    go9500 = true;
                    now[3] = 0;
                    swap(now[0], now[1]);
                    now[2] = ((*edge[now[0]].find(now[1])).S - now[2]);
                }
                else if (dist_b >= 9500 && dist_a >= dist_b)
                {
                    check9500 = false;
                    go9500 = true;
                    now[3] = 0;
                }
            }
            else if (t + dist[now[0]][0] >= 9500)
            {
                check9500 = false;
                go9500 = true;
                now[3] = 0;
            }
        }

        if (go9500 && now[0] == 0 && now[1] == 0 && now[2] == 0)
        {
            t_last = t;
            break;
        }
        else if (now[2] > 0)
        {
            ans[t] = now[1];
            now[2]++;
        }
        else if (now[0] != now[3])
            search_next = true;
        else if (ord_cnt[1] >= orders_to_move)
        {
            search_next = true;
            if ((*ord_all.begin()).F + deadline >= t)
                now[3] = (*ord_all.begin()).S;
            else
            {
                ld mx = 0;
                repf(i, 1, V)
                {
                    if (i == now[0])
                        continue;
                    if (comp_max(mx, calc_value(t, ord_have[i]) / (ld)dist[now[0]][i]))
                        now[3] = i;
                }
            }
        }
        else if (now[0] != 0)
        {
            search_next = true;
            now[3] = 0;
        }
        if (search_next) //次の辺を選択
        {
            for (auto itr = edge[now[0]].begin(); itr != edge[now[0]].end(); itr++)
            {
                if ((*itr).S + dist[(*itr).F][now[3]] == dist[now[0]][now[3]])
                    ans[t] = (*itr).F;
            }
            now[1] = ans[t];
            now[2] = 1;
        }

        //移動結果の処理
        //配達完了処理とスコアの集計
        //z : 時刻t+1に完了した注文の数
        if (now[2] && now[2] == (*edge[now[0]].find(now[1])).S)
        {
            now[0] = now[1];
            now[2] = 0;
        }

        //配達完了処理とスコアの集計
        if (now[2] == 0 && now[0] != 0)
        {
            //店舗以外の頂点にいる場合
            //その頂点のbef以前の注文を受け取る
            for (auto itr = order[now[0]].begin(); itr != order[now[0]].end(); itr++)
            {
                if ((*itr) > bef)
                {
                    order[now[0]].erase(order[now[0]].begin(), itr);
                    break;
                }
                z--;
                ord_all.erase((*itr));
                ord_cnt[1]--;
                score += pow(T, 2) - pow(t - (*itr), 2);
            }
            if ((!order[now[0]].empty()) && (*order[now[0]].begin()) <= bef)
            {
                order[now[0]].erase(all(order[now[0]]));
            }
            rep(j, 3) ord_have[now[0]][j] = 0;
        }
    }

    //t_lastの行動決定フェーズから
    //Tまでの行動を焼きなまし法を用いて最大化を行う

    //初期解の設定：注文がある頂点の中で最も近い頂点を巡回する
    int t_now = t_last;
    vector<int> root(1, 0);
    vector<int> visited(V, 0);
    visited[0] = 1;
    ld score_mx = 0;
    int nw = 0;
    while (t_now < T)
    {
        int sz = root.size();
        nw = root[sz - 1];
        int nex = -1;
        ld nex_v = -1;

        rep(i, V)
        {
            if (i == nw || t_now + dist[nw][i] > T)
                continue;
            ld i_v = (visited[i] ^ 1) * calc_value(t_now, ord_have[i]) / (ld)(dist[nw][i]);
            if (i_v > nex_v)
            {
                nex_v = i_v;
                nex = i;
            }
        }
        if (nex == -1)
            break;
        root.emplace_back(nex);
        while (nw != nex)
        {
            for (auto itr = edge[nw].begin(); itr != edge[nw].end(); itr++)
            {
                if (dist[nw][nex] == dist[(*itr).F][nex] + (*itr).S)
                {
                    t_now += (*itr).S;
                    if (visited[(*itr).F] == 0)
                    {
                        score_mx += calc_value(t_now, ord_have[(*itr).F]);
                        visited[(*itr).F] = 1;
                    }
                    nw = (*itr).F;
                    break;
                }
            }
        }
    }

    //解の改善をしていく
    int cnt = 0;
    ld START_TEMP = 20000000;
    ld END_TEMP = 100000;
    //score_deltaをtempで割るため、ある程度スコアの差分を予想できていたほうがよい。
    //差分のave取ってみる
    ld END_TIME = 29.5;
    ld temp = START_TEMP;
    ld mx = score_mx;
    vector<int> ans_root = root;

    vector<ld> debug_delta(2, 0);

    while (true)
    {
        if (cnt % 100 == 0)
        {
            double time = duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6;
            if (time > END_TIME)
            {
                break;
            }
            temp = START_TEMP + (END_TEMP - START_TEMP) * time / END_TIME;
        }
        //変更案
        int sz = root.size();
        int x = (randxor() % (sz - 2));
        swap(root[x + 1], root[x + 2]);
        ld score_new = 0;
        t_now = t_last;
        nw = root[0];
        rep(i, V) visited[i] = 0;
        repf(i, 1, sz)
        {
            int nex = root[i];
            if (dist[nw][nex] + t_now > T)
                break;
            while (nw != nex)
            {

                if (dist[nw][nex] + t_now > T)
                    break;
                for (auto itr = edge[nw].begin(); itr != edge[nw].end(); itr++)
                {
                    if (dist[nw][nex] == dist[(*itr).F][nex] + (*itr).S)
                    {
                        if (t_now + (*itr).S > T)
                            break;
                        t_now += (*itr).S;
                        if (visited[(*itr).F] == 0)
                        {
                            score_new += calc_value(t_now, ord_have[(*itr).F]);
                            visited[(*itr).F] = 1;
                        }
                        nw = (*itr).F;
                        break;
                    }
                }
            }
        }
        ld score_delta = score_new - score_mx;

        debug_delta[0]++;
        debug_delta[1] += score_delta / (ld)1000000.0;

        if (exp(score_delta / temp) > randxor01())
        {
            score_mx += score_delta;

            if (mx < score_mx)
            {
                mx = score_mx;
                ans_root = root;
            }
        }
        else
        {
            swap(root[x + 1], root[x + 2]);
        }
        cnt++;
    }

    t_now = t_last;
    nw = ans_root[0];
    rep(i, V) visited[i] = 0;
    repf(i, 1, ans_root.size())
    {
        int nex = ans_root[i];
        if (dist[nw][nex] + t_now > T)
            break;
        while (nw != nex)
        {

            if (dist[nw][nex] + t_now > T)
                break;
            for (auto itr = edge[nw].begin(); itr != edge[nw].end(); itr++)
            {
                if (dist[nw][nex] == dist[(*itr).F][nex] + (*itr).S)
                {
                    if (t_now + (*itr).S > T)
                        break;
                    rep(xx, (*itr).S)
                    {
                        ans[t_now] = (*itr).F;
                        t_now++;
                    }
                    if (visited[(*itr).F] == 0)
                    {
                        score += calc_value(t_now, ord_have[(*itr).F]);
                        visited[(*itr).F] = 1;
                    }
                    nw = (*itr).F;
                    break;
                }
            }
        }
    }
    if (debug)
    {
        cout << "delta ave : ";
        cout << debug_delta[1] / debug_delta[0] << ENDL;
    }

    if (debug && time_display)
    {
        cout << "CALC_MAIN end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }
    if (!(debug))
    {
        rep(i, T) cout << ans[i] + 1 << ENDL;
    }
    if (debug && 0)
    {
        cout << "leave order num :" << z << ENDL;
        for (auto itr = ord_all.begin(); itr != ord_all.end(); itr++)
        {
            cout << (*itr).F << " ";
        }
        cout << ENDL;
    }
    return score;
}

int main()
{
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    const string path = "./test_A/input_";
    string path_in = path + int_to_string(0) + ".csv";
    string problem = "A";
    int o_t_m = 9;
    int dl = 900;
    if (!(debug))
    {
        CALC_MAIN(path_in, o_t_m, dl);
        return 0;
    }
    int n = 1;
    ld s_score = 0;
    rep(i, n)
    {
        cout << ENDL;
        cout << "start " << i << ENDL;
        s_score += (ld)CALC_MAIN(path + int_to_string(i) + ".csv", o_t_m, dl) / (ld)100000000;
    }
    cout << "ave score : " << s_score / (ld)n << ENDL;
}