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

bool debug = true;

const ll T = 10000;
const ll MAX_V = 400;
const ll MIN_V = 200;
const int MAX_Degree = 5;
const ll MAX_DIST = 5000;

const int orders_to_move = 5;

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
    return (hav[0] * 2 * (ld)t - hav[1] + cons * hav[2]);
}

ll CALC_MAIN(string path)
{

    auto startClock = system_clock::now();
    if (debug)
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
                cin >> input_data[idx+1] >> input_data[idx + 2];
                idx += 2;
            }
            idx++;
        }
    }
    if (debug)
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
    if (debug)
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
    if (debug)
    {
        cout << "calc dist end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    //main_treatment
    //注文がk個以上のときすべて回る（0を通ったら追加する）
    //注文がk個未満のとき0へ向かう。（配達完了処理もちゃんとする）

    vector<int> ans(T, -1);
    int idx = 3 * E + 3;
    
    vector<int> ord_id(T, -1);  //時刻tの注文のID
    int ord_have = 0;  //積んだ注文の数
    int ord_nhave = 0;  //積んでいない注文の数
    int bef = 0;  //最後に店舗を訪れた時刻
    vector<set<int>> order(V);  //受注した注文
    multimap<int, int> ord_all; //受注した注文の時刻、場所。bef以下で最大の注文場所へ向かう

    vector<int> now(4, 0);  //辺(u,v)のuから距離dの地点にいて、最終的にwに向かっている
    //main_loop

    if (debug)
    {
        cout << "main init end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    rep(t, T)
    {
        //時刻tからt+1の処理をおこなう
        //注文を受け取る
        if (debug && t % 2500 == 0)
        {
            cout << "itr, score : " << t << " " << score << ENDL;
        }
        int ord_num = input_data[idx];
        idx++;
        if (ord_num)
        {
            ord_id[t] = input_data[idx];
            idx++;
            int target = input_data[idx] - 1;
            idx++;
            order[target].insert(t);
            ord_all.insert(mp(t, target));
            ord_nhave++;
            //各頂点の評価更新
        }
        //商品を積む
        if (now[0]==now[1] && now[0]==0){
            ord_have += ord_nhave;
            ord_nhave = 0;
            bef = t;
        }

        //行動の決定
        bool search_next = false;
        if (now[2]>0){
            ans[t] = now[1];
            now[2]++;
        }
        else if (now[0]!=now[3])
            search_next = true;
        else if (ord_have>=orders_to_move){
            search_next = true;
            auto idx = ord_all.upper_bound(bef);
            idx--;
            now[3] = (*idx).S;
        }
        else if (now[0]!=0){
            search_next = true;
            now[3] = 0;
        }
        if (search_next)  //返上orstay以外
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
        int z = 0;
        if (now[2] && now[2]==(*edge[now[0]].find(now[1])).S){
            now[0] = now[1];
            now[2] = 0;
        }
        if (now[2]==0 && now[0]!=0){
            //店舗以外の頂点にいる場合
            //その頂点のbef以前の注文を受け取る
            for (auto itr = order[now[0]].begin(); itr != order[now[0]].end();itr++){
                if((*itr)>bef){
                    order[now[0]].erase(order[now[0]].begin(), itr);
                    break;
                }
                ord_all.erase((*itr));
                ord_have--;
                z++;
                score += pow(T, 2) - pow(t - (*itr), 2);
            }
            if ((!order[now[0]].empty()) && (*order[now[0]].begin())<=bef){
                order[now[0]].erase(all(order[now[0]]));
            }
        }
    }

    if (debug)
    {
        cout << "CALC_MAIN end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }
    if (!(debug))
    {
        rep(i, T) if (ans[i] != -1) ans[i]++;
        rep(i, T) cout << ans[i] << ENDL;
    }

    return score;
}

int main()
{
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    const string path = "./test_A/input_";
    int n = 1;
    string problem = "A";
    rep(i, n)
    {
        string path_in = path + int_to_string(i) + ".csv";
        ld ans = (ld)CALC_MAIN(path_in) / 1000000.0;
        if (debug)
        {
            cout << "final score : " << ans << ENDL;
        }
    }
}