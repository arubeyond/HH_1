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

const ll T = 10000;
const ll MAX_V = 400;
const ll MIN_V = 200;
const int MAX_Degree = 5;
const ll MAX_DIST = 5000;

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

ld calc_dist(pdd a, pdd b)
{
    return sqrt(pow(a.F - b.F, 2) + pow(a.S - b.S, 2));
}

void MAKE_TREE(int V, int E, vvii &edge, vector<pdd> coo, vector<int> col)
{
    auto startClock = system_clock::now();
    double time;
    vector<vector<int>> used(V, vector<int>(V, 1));
    rep(i, V) used[i][i] = 0;
    //最小全域木を作る
    vector<int> connect(V, 0);
    multimap<ld, pair<int, int>> near_edge;
    connect[0] = 1;
    repf(i, 1, V)
        near_edge.insert(mp(calc_dist(coo[0], coo[i]), mp(0, i)));
    near_edge.insert(mp(MAX_DIST * MAX_DIST, mp(-1, -1)));
    rep(i, V - 1)
    {
        ld w = (*near_edge.begin()).F;
        int u = (*near_edge.begin()).S.F;
        int v = (*near_edge.begin()).S.S;
        int uv = u;
        if (connect[u])
            uv = v;
        edge[i][0] = u;
        edge[i][1] = v;
        edge[i][2] = (int)ceil(2 * w);
        used[u][v] = 0;
        used[v][u] = 0;
        connect[u] = 1;
        connect[v] = 1;
        rep(j, uv) if (connect[j] ^ 1) near_edge.insert(mp(calc_dist(coo[uv], coo[j]), mp(j, uv)));
        repf(j, uv + 1, V) if (connect[j] ^ 1) near_edge.insert(mp(calc_dist(coo[uv], coo[j]), mp(uv, j)));
        auto itr = near_edge.end();
        while (itr != near_edge.begin())
        {
            itr--;
            if (connect[(*itr).S.F] & connect[(*itr).S.S])
                near_edge.erase(itr);
        }
    }
    if (debug)
    {
        time = duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6;
        cout << "making min tree is end at"
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }
    //残りの辺を作る
    vector<int> degree(V, 0);
    rep(i, V - 1)
    {
        degree[edge[i][0]]++;
        degree[edge[i][1]]++;
    }
    multimap<ld, pair<int, int>> cost;
    map<pair<int, int>, ld> cost_inv;
    //init
    rep(u, V - 1)
    {
        repf(v, u + 1, V)
        {
            if (used[u][v])
            {
                int f = 1 + 4 * (col[u] == col[v]);
                int g = (1 + MAX_DIST * (degree[u] >= MAX_Degree)) * (1 + MAX_DIST * (degree[v] >= MAX_Degree));
                ld w = calc_dist(coo[u], coo[v]) * degree[u] * degree[v] * f * g;
                cost.insert(mp(w, mp(u, v)));
                cost_inv.insert(mp(mp(u, v), w));
            }
        }
    }

    repf(i, V - 1, E)
    {
        ld w = (*cost.begin()).F;
        int u = (*cost.begin()).S.F;
        int v = (*cost.begin()).S.S;
        edge[i][0] = u;
        edge[i][1] = v;
        edge[i][2] = (int)ceil(4 * w);
        used[u][v] = 0;
        used[v][u] = 0;
        cost_inv.erase(mp(u, v));
        cost.erase(w);
        rep(x, u)
        {
            if (used[x][u])
            {
                w = cost_inv[mp(x, u)];
                w *= (ld)(degree[u] + 1.0) / (ld)(degree[u]) * (ld)(1 + MAX_DIST * (degree[u] + 1 == MAX_Degree));
                cost.insert(mp(w, mp(x, u)));
                cost_inv[mp(x, u)] = w;
            }
        }
        repf(x, u + 1, V)
        {
            if (used[u][x])
            {
                w = cost_inv[mp(u, x)];
                w *= (ld)(degree[u] + 1.0) / (ld)(degree[u]) * (ld)(1 + MAX_DIST * (degree[u] + 1 == MAX_Degree));
                if (debug)
                    cost.insert(mp(w, mp(u, x)));
                cost_inv[mp(u, x)] = w;
            }
        }
        rep(x, v)
        {
            if (used[x][v])
            {
                w = cost_inv[mp(x, v)];
                w *= (ld)(degree[v] + 1.0) / (ld)(degree[v]) * (ld)(1 + MAX_DIST * (degree[v] + 1 == MAX_Degree));
                cost.insert(mp(w, mp(x, v)));
                cost_inv[mp(x, v)] = w;
            }
        }
        repf(x, v + 1, V)
        {
            if (used[v][x])
            {
                w = cost_inv[mp(v, x)];
                w *= (ld)(degree[v] + 1.0) / (ld)(degree[v]) * (ld)(1 + MAX_DIST * (degree[v] + 1 == MAX_Degree));
                cost.insert(mp(w, mp(v, x)));
                cost_inv[mp(v, x)] = w;
            }
        }
        degree[u]++;
        degree[v]++;
    }
}

void make(string path, string problem)
{
    auto startClock = system_clock::now();
    double time;
    if (debug)
    {
        time = duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6;
        cout << "func make is started at"
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    //init : V,E,Rの決定
    int V, E;
    int R = 0;
    V = MIN_V + randxor() % (MAX_V - MIN_V);
    E = 3 * V / 2 + randxor() % (V / 2);
    vector<vector<int>> edge(E, vector<int>(3, 0));
    while (true)
    {
        R++;
        if (R * R > V)
        {
            R--;
            break;
        }
    }
    int r = V - (R * R);
    if (debug)
    {
        const double time = duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6;
        cout << "initialize is end at"
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
        cout << "V, E, R, r : " << V << " " << E << " " << R << " " << r << ENDL;
    }

    //座標を作る（色も）
    multiset<int> leave;
    rep(i, V) leave.insert(i);
    vector<pair<ld, ld>> coo(V);
    vector<int> col(V);
    rep(x, R)
    {
        rep(y, R)
        {
            auto itr = leave.begin();
            rep(i, randxor() % (V - x * R + y)) itr++;
            coo[(*itr)] = mp(x + randxor01(), y + randxor01());
            col[(*itr)] = (x + y) % 2;
            leave.erase(itr);
        }
    }
    rep(i, r)
    {
        auto itr = leave.begin();
        rep(j, randxor() % (V - R * R - i)) itr++;
        coo[(*itr)] = mp(randxor01() * R, randxor01() * R);
        col[(*itr)] = (randxor01() > 0.5);
        leave.erase(itr);
    }
    if (debug)
    {
        time = duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6;
        cout << "coordinate is end at"
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    //グラフ生成
    MAKE_TREE(V, E, edge, coo, col);
    if (debug)
    {
        time = duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6;
        cout << "func make_tree is end at"
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    //注文頻度、注文を作る
    vector<int> freq(V, 1);
    freq[0] = 0;
    pair<ld, ld> cent;
    cent = mp((ld)R / 4.0 + randxor01() * ((ld)R / 2.0), (ld)R / 4.0 + randxor01() * ((ld)R / 2.0));
    repf(i, 1, V)
    {
        if (calc_dist(cent, coo[i]) <= ((ld)R / 8.0) * (1.0 + randxor01()))
            freq[i] = 2;
        freq[i] += freq[i - 1];
    }
    vector<int> Ord(T, -1);
    int T_last = 9500;
    ld T_peak = randxor01() * T_last;
    rep(t, T_last)
    {
        if (t < T_peak)
        {
            if (randxor01() < ((ld)t / T_peak))
                Ord[t] = (upper_bound(all(freq), randxor() % ((ll)freq[V - 1])) - freq.begin());
        }
        else
        {
            if (randxor01() < ((ld)(T_last - t) / (ld)(T_last - T_peak)))
                Ord[t] = (upper_bound(all(freq), randxor() % ((ll)freq[V - 1])) - freq.begin());
        }
    }
    if (debug)
    {
        time = duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6;

        cout << "order making is end at"
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    //csvへの書き込み
    ofstream ofs(path);
    if (problem == "A")
    {
        ofs << V << "," << E << endl;
        rep(i, E) ofs << edge[i][0] + 1 << "," << edge[i][1] + 1 << "," << edge[i][2] << endl;
        ofs << T << endl;
        int ord_id = 1;
        rep(t, T)
        {
            ofs << (Ord[t] >= 0) << endl;
            if (Ord[t] >= 0)
            {
                ofs << ord_id << "," << Ord[t] + 1 << endl;
                ord_id++;
            }
        }
    }
    else if (problem == "B")
    {
        ofs << V << " " << E << endl;
        rep(i, E) ofs << edge[i][0] + 1 << " " << edge[i][1] + 1 << " " << edge[i][2] << endl;
        ofs << freq[0] << " ";
        repf(i, 1, V - 1) ofs << freq[i] - freq[i - 1] << " ";
        ofs << freq[V - 1] - freq[V - 2] << endl;
        ofs << T << endl;
        int ord_id = 1;
        rep(t, T)
        {
            ofs << (Ord[t] >= 0) << endl;
            if (Ord[t] >= 0)
            {
                ofs << ord_id << " " << Ord[t] + 1 << endl;
                ord_id++;
            }
        }
    }
    ofs.close();
    if (debug)
    {
        time = duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6;

        cout << "writing csv is end at"
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }
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

int main()
{
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    auto startClock = system_clock::now();
    const string path = "./HH_1/test_A_in/input_";
    int a, b;
    a = 0;
    b = 1;
    string problem = "B";
    repf(i, a, b)
    {
        string path_in = path + int_to_string(i) + ".in";
        make(path_in, problem);
    }

    double time = duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6;
    cout << "end at"
         << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
         << ENDL;
    /*
    cout << "debug start" << ENDL;
    int V = 100;
    int E = 2*V;
    cout << "(V,E) : " << V << " " << E << ENDL;
    vvii edge(E, vii(3, 0));
    vector<pair<ld, ld>> coo(V);
    vector<int> col(V);
    rep(i,V){
        coo[i] = mp(randxor01() * V, randxor01() * V);
        col[i] = (randxor() & 1);
    }
    MAKE_TREE(V, E, edge, coo, col);
    cout << "debug end" << ENDL;
    */
}