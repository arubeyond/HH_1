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

int orders_to_move = 9;
int deadline = 900;

int input_data[40000],
    V, E, ord_target[10005], ans[10005], place[10005][4];
//ans[t]:時刻tのコマンド-1
//place[t]：時刻tのはじめ(コマンド入力前)に
//辺[0][1]の[0]から[2]進んだ場所にいて、[3]を目的地にしている
ld score[10005], dist[405][405], ord_have[10005][405][3], ord_nhave[10005][405][3];
multimap<int, int> edge[405];

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

ld calc_value(int t, int i)
{
    ld cons = T * T - t * t;
    return (cons * ord_have[t][i][0] + (ld)2.0 * (ld)t * ord_have[t][i][1] - ord_have[t][i][2]);
}

ld calc_value2(int t, vector<ld> have)
{
    ld cons = T * T - t * t;
    return (cons * have[0] + (ld)2.0 * (ld)t * have[1] - have[2]);
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

void read_csv(string path)
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
            input_data[idx] = (string_to_int(str_conma_buf));
            idx++;
        }
    }
    ifs.close();
}

void INPUT()
{

    cin >> input_data[0] >> input_data[1];
    rep(i, input_data[1]) cin >> input_data[3 * i + 2] >> input_data[3 * i + 3] >> input_data[3 * i + 4];
    rep(i, input_data[0]) cin >> input_data[2 + 3 * input_data[1] + i];
    cin >> input_data[(2 + 3 * input_data[1] + input_data[0])];
}

void init()
{
    V = input_data[0];
    E = input_data[1];
    rep(i, E)
    {
        int u, v, d;
        u = input_data[3 * i + 2] - 1;
        v = input_data[3 * i + 3] - 1;
        d = input_data[3 * i + 4];
        edge[u].insert(mp(v, d));
        edge[v].insert(mp(u, d));
    }
    int idx = 3 * E + 3 + V;
}

void make_dist()
{
    rep(i, V) rep(j, V) dist[i][j] = infi;
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
}

ld SimulatedAnnealing(int t_last, double time)
{
    auto SAstartClock = system_clock::now();

    //init
    vector<int> now(4, 0);                        //現在地
    vector<vector<ld>> have(V, vector<ld>(3, 0)); //各頂点の注文情報
    ld score_bef = score[t_last - 1];             //t_lastまでのスコア。最後にこれに足して答えとする
    rep(i, 4) now[i] = place[t_last - 1][i];
    rep(i, V) rep(j, 3) have[i][j] = ord_have[t_last][i][j];

    int t = t_last;
    int nw = 0;
    ld score_mx = 0;           //暫定スコア
    vector<int> root(1, 0);    //暫定ルート（目的地のみ、道中略）
    vector<int> visited(V, 0); //どの頂点を訪れたか（スコア計算で使う）
    visited[0] = 1;

    //初期解の設定
    while (t < T)
    {
        int sz = root.size();
        nw = root[sz - 1];
        int nex = -1;
        ld nex_v = 0;

        rep(i, V)
        {
            //nwからiに移動した場合のスコア増分
            if (i == nw || t + dist[nw][i] > T)
                continue;
            ld i_v = (visited[i] ^ 1) * calc_value2(t, have[i]) / (ld)dist[nw][i];
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
                    t += (*itr).S;
                    nw = (*itr).F;
                    if (visited[nw] == 0)
                    {
                        score_mx += calc_value2(t, have[nw]);
                        visited[nw] = 1;
                    }
                    break;
                }
            }
        }
    }

    //Tを超えた後のルートも一応作っておく
    while (true)
    {
        int sz = root.size();
        nw = root[sz - 1];
        int nex = -1;
        ld nex_v = 0;
        rep(i, V)
        {
            if (i == nw)
                continue;
            ld i_v = (visited[i] ^ 1) * calc_value2(t, have[i]) / (ld)(dist[nw][i]);
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
                    t += (*itr).S;
                    nw = (*itr).F;
                    visited[nw] = 1;
                    break;
                }
            }
        }
    }

    //時間の限り解の改善
    int cnt = 0;
    ld START_TEMP = 20000000;
    ld END_TEMP = 100000;
    ld END_TIME = 29.5;
    ld temp = START_TEMP + (END_TEMP - START_TEMP) * time / END_TIME;
    vector<int> ans_root = root; //最適解
    ld mx = score_mx;            // 最適値

    while (true)
    {
        if (cnt % 100 == 0)
        {
            double time_now = time +
                              duration_cast<microseconds>(system_clock::now() - SAstartClock).count() * 1e-6;
            if (time_now > END_TIME)
                break;
            temp = START_TEMP + (END_TEMP - START_TEMP) * time_now / END_TIME;
        }

        //改善案：ルートの１～szの中で隣り合ったものを入れ替える
        int sz = root.size();
        int x = (randxor() % (sz - 2));
        swap(root[x + 1], root[x + 2]);
        ld score_new = 0;
        t = t_last;
        nw = root[0];
        rep(i, V) visited[i] = 0;
        repf(i, 1, sz)
        {
            int nex = root[i];
            if (dist[nw][nex] + t > T)
                break;
            while (nw != nex)
            {
                if (dist[nw][nex] + t > T)
                    break;
                for (auto itr = edge[nw].begin(); itr != edge[nw].end(); itr++)
                {
                    if (dist[nw][nex] == dist[(*itr).F][nex] + (*itr).S)
                    {
                        if (t + (*itr).S > T)
                            break;
                        t += (*itr).S;
                        nw = (*itr).F;
                        if (visited[nw] == 0)
                        {
                            score_new += calc_value2(t, have[nw]);
                            visited[nw] = 1;
                        }
                        break;
                    }
                }
            }
        }
        ld score_delta = score_new - score_mx;

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

    //解を出力する
    t = t_last;
    nw = ans_root[0];
    rep(i, V) visited[i] = 0;
    repf(i, 1, ans_root.size())
    {
        int nex = ans_root[i];
        if (dist[nw][nex] + t > T)
            break;
        while (nw != nex)
        {
            if (dist[nw][nex] + t > T)
                break;
            for (auto itr = edge[nw].begin(); itr != edge[nw].end(); itr++)
            {
                if (dist[nw][nex] == dist[(*itr).F][nex] + (*itr).S)
                {
                    if (t + (*itr).S > T)
                        break;
                    nw = (*itr).F;
                    rep(xx, (*itr).S)
                    {
                        ans[t] = nw;
                        t++;
                    }
                    if (visited[nw] == 0)
                    {
                        score_bef += calc_value2(t, have[nw]);
                        visited[nw] = 1;
                    }
                    break;
                }
            }
        }
    }

    //output
    if (!(debug))
    {
        repf(tt, t_last, T)
        {
            int cnt, x;
            cin >> cnt;
            rep(i, cnt) cin >> x;
            cout << ans[tt] + 1 << endl;
            string verdict;
            cin >> verdict;
            if (verdict == "NG")
                return -1;
            cin >> cnt;
            rep(i, cnt) cin >> x;
        }
    }

    return score_bef;
}

int main_loop()
{
    int bef = 0;                  //最後に店舗を訪れた時刻
    vector<set<int>> ord_list(V); //受注した注文
    multimap<int, int> ord_all;   //受注した注文の時刻、場所。bef以下で最大の注文場所へ向かう
    vector<int> ord_cnt(2, 0);    //積んでいない注文、積んだ注文
    vector<int> now(4, 0);        //辺(u,v)のuから距離dの地点にいて、最終的にwに向かっている
    rep(i, V)
    {
        rep(j, 3)
        {
            ord_have[0][i][j] = 0;
            ord_nhave[0][i][j] = 0;
        }
    }

    score[0] = 0;
    int idx = 3 + 3 * E + V;

    bool check9500 = true;
    bool go9500 = false;
    int t_last = T;
    rep(i, T) ans[i] = -2;

    //ord_(n)have[t]:時刻t終了時点のスコア記録
    //ord_(n)have[-1]:全部0
    //place[t]:時刻t終了時点の位置記録
    //Tlastで参照するときはTlast-1の記録から復元する
    rep(t, T)
    {
        //時刻tからt+1の処理をおこなう

        //注文を受け取る
        if (debug)
        {
            ord_target[t] = input_data[idx];
            idx++;
            if (ord_target[t])
            {
                ord_target[t] = input_data[idx + 1];
                ord_target[t]--;
                idx += 2;
            }
        }
        else
        {
            cin >> ord_target[t];
            if (ord_target[t])
            {
                cin >> ord_target[t];
                cin >> ord_target[t];
                ord_target[t]--;
            }
        }
        if (ord_target[t])
        {
            int tar = ord_target[t];
            ord_list[tar].insert(t);
            ord_all.insert(mp(t, tar));

            //積んでいない荷物の集計
            ord_cnt[0]++;
            ord_nhave[t][tar][0]++;
            ord_nhave[t][tar][1] += t;
            ord_nhave[t][tar][2] += pow(t, 2);
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
                    ord_have[t][i][j] += ord_nhave[t][i][j];
                    ord_nhave[t][i][j] = 0;
                }
            }
            bef = t;
        }

        //行動の決定
        bool search_next = false;

        if (check9500)
        {
            if (now[2] > 0)
            {
                int dist_a = t + dist[now[0]][0] + now[2];
                int dist_b = t + dist[now[1]][0] + (*(edge[now[0]].find(now[1]))).S - now[2];
                if (dist_b >= 9499 && dist_a >= dist_b)
                {
                    check9500 = false;
                    go9500 = true;
                    now[3] = 0;
                }
                else if (dist_a >= 9499 && dist_b > dist_a)
                {
                    check9500 = false;
                    go9500 = true;
                    now[3] = 0;
                    swap(now[0], now[1]);
                    now[2] = (*(edge[now[0]].find(now[1]))).S - now[2];
                }
            }
            else if (t + dist[now[0]][0] >= 9499)
            {
                check9500 = false;
                go9500 = true;
                now[3] = 0;
            }
        }

        if (go9500 && now[0] == now[1] && now[0] == 0)
        {
            t_last = t;
            break;
        }
        else if (now[2] > 0)
        {
            //辺の上にいるとき
            ans[t] = now[1];
            now[2]++;
        }
        else if (now[0] != now[3])
        {
            //頂点にいるが目的地についていないとき
            search_next = true;
        }
        else if (ord_cnt[1] >= orders_to_move)
        {
            //頂点にいて、注文を十分に持っているとき、次の目的地を探す
            search_next = true;
            if ((*ord_all.begin()).F + deadline >= t)
                now[3] = (*ord_all.begin()).S; //deadline以上たっている注文があれば優先
            else
            {
                //スコア/距離が最大の頂点を目的地とする
                ld mx = 0;
                repf(i, 1, V)
                {
                    if (i == now[0])
                        continue;
                    if (comp_max(mx, calc_value(t, i) / (ld)dist[now[0]][i]))
                    {
                        now[3] = i;
                    }
                }
            }
        }
        else if (now[0] != 0)
        {
            //注文が十分にないとき店舗へ向かう
            search_next = true;
            now[3] = 0;
        }
        if (search_next)
        {
            //目的地に向けて次移動する頂点を決定する
            for (auto itr = edge[now[0]].begin(); itr != edge[now[0]].end(); itr++)
            {
                if ((*itr).S + dist[(*itr).F][now[3]] == dist[now[0]][now[3]])
                    ans[t] = (*itr).F;
            }
            now[1] = ans[t];
            now[2] = 1;
        }

        //移動結果の処理
        if (now[2] && now[2] == (*edge[now[0]].find(now[1])).S)
        {
            //辺の最後にいたら頂点へ位置情報を修正
            now[0] = now[1];
            now[2] = 0;
        }

        //配達完了処理とスコアの集計
        if (now[2] == 0 && now[0] != 0)
        {
            //店舗以外の頂点にいる場合:その頂点のbef以前の注文を受け取る
            for (auto itr = ord_list[now[0]].begin(); itr != ord_list[now[0]].end(); itr++)
            {
                if ((*itr) > bef)
                {
                    ord_list[now[0]].erase(ord_list[now[0]].begin(), itr);
                    break;
                }
                ord_all.erase((*itr));
                ord_cnt[1]--;
                score[t] += pow(T, 2) - pow(t - (*itr), 2);
                //score += calc_value(t,now[0]);
            }
            if ((!ord_list[now[0]].empty()) && (*ord_list[now[0]].begin()) <= bef)
            {
                ord_list[now[0]].erase(all(ord_list[now[0]]));
            }
            rep(j, 3) ord_have[t][now[0]][j] = 0;
        }

        //ord_have,ord_nhave,placeの更新
        rep(i, 4) place[t][i] = now[i];
        rep(i, V)
        {
            rep(j, 3)
            {
                ord_have[t + 1][i][j] = ord_have[t][i][j];
                ord_nhave[t + 1][i][j] = ord_nhave[t][i][j];
            }
        }
        score[t + 1] = score[t];

        //output
        if (!(debug))
        {
            int cnt, x;
            cin >> cnt;
            rep(i, cnt) cin >> x;
            cout << ans[t] + 1 << endl;
            string verdict;
            cin >> verdict;
            if (verdict == "NG")
                return -1;
            cin >> cnt;
            rep(i, cnt) cin >> x;
        }
    }

    //いま、時刻t_lastで、9499までの全ての注文の処理と、商品を積む作業が終了している。
    //場所はplace[t_last-1]、スコアはscore[t_last]=score[t_last-1]
    //have,nhaveは[t_last]が、注文集荷の処理済み
    //ここからの配送計画について、SAを用いて最適化する。
    return t_last;
}

ll CALC_MAIN(string path)
{

    auto startClock = system_clock::now();
    if (debug && time_display)
    {
        cout << "CALC_MAIN start at : "
             << duration_cast<microseconds>(startClock - startClock).count() * 1e-6
             << ENDL;
    }

    //input
    if (debug)
        read_csv(path);
    else
        INPUT();

    //initialize
    init();

    //距離の計算
    make_dist();

    //最終的な解と値
    vector<int> ans_final(T, -2);

    //main_treatment
    //注文がk個以上のときすべて回る（0を通ったら追加する）
    //注文がk個未満のとき0へ向かう。（配達完了処理もちゃんとする）
    //注文からdeadline経っている商品は優先的に配達する
    int t_last = main_loop();
    double time = duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6;
    ld score_answer = SimulatedAnnealing(t_last, time);

    if (debug && time_display)
    {
        cout << "CALC_MAIN end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    return score_answer;
}

int main()
{
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    const string path = "./test_A/input_";
    string path_in = path + int_to_string(0) + ".csv";
    string problem = "B";
    if (!(debug))
    {
        CALC_MAIN(path_in);
        return 0;
    }
    int n = 1;
    ld s_score = 0;
    rep(i, n)
    {
        cout << ENDL;
        cout << "start " << i << ENDL;
        s_score += (ld)CALC_MAIN(path + int_to_string(i) + ".csv") / (ld)100000000;
    }
    cout << "ave score : " << s_score / (ld)n << ENDL;
}