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

int input_data[32500],
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
    int idx = 3 * E + 3;
    rep(t, T)
    {
        if (input_data[idx])
        {
            ord_target[t] = input_data[idx + 2] - 1;
            idx += 3;
        }
        else
        {
            ord_target[t] = 0;
            idx++;
        }
    }
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

void main_loop()
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

    //ord_(n)have[t]:時刻t終了時点のスコア記録
    //ord_(n)have[-1]:全部0
    //place[t]:時刻t終了時点の位置記録
    //Tlastで参照するときはTlast-1の記録から復元する
    rep(t, T)
    {
        //時刻tからt+1の処理をおこなう

        //注文を受け取る
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
        ans[t] = -2;
        if (now[2] > 0)
        {
            //辺の上にいるとき
            ans[t] = now[1];
            now[2]++;
        }
        else if (now[0] != now[3])
            search_next = true; //頂点にいるが目的地についていないとき
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
    }
    return score;
}

ld sub_loop(int Tlast){
    vector<vector<ld>> have(V, vector<ld>(3, 0)), nhave(V, vector<ld>(3, 0));
    rep(i,V){
        rep(j,3){
            have[i][j] = ord_have[Tlast - 1][i][j];
            nhave[i][j] = ord_nhave[Tlast - 1][i][j];
        }
    }
    vector<int> now(4, 0);
    rep(i, 4) now[i] = place[Tlast - 1][i];
    ld sc = score[Tlast - 1];

    //１．店舗まで移動する
    //２．スコア/距離の大きい順に回っていく
    //１，２どちらでも注文の更新、荷物積み、配達の完了は通常通り行う
    //ただし、移動先の決定が少し違う
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

    //main_treatment
    //注文がk個以上のときすべて回る（0を通ったら追加する）
    //注文がk個未満のとき0へ向かう。（配達完了処理もちゃんとする）
    //注文からdeadline経っている商品は優先的に配達する
    ld score = main_loop();

    if (debug && time_display)
    {
        cout << "CALC_MAIN end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    //output
    if (!(debug))
    {
        rep(i, T) cout << ans[i] + 1 << ENDL;
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