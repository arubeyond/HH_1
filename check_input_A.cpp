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

int string_to_int(string s)
{
    int ans = 0;
    rep(i, s.size())
    {
        ans *= 10;
        ans += (int)((char)s[i] - '0');
    }
    return ans;
}

bool check(string path_in,string problem){
    ifstream ifs(path_in);
    string str_buf;
    string str_conma_buf;
    bool flag = false;
    if(problem=="A"){
        int line_num = 0;
        int line_cnt = 0;
        vii VE(2);
        vii edge(3);
        bool info = true;
        ld d_max;
        int info_id = 1;
        int info_num = 0;
        while (getline(ifs, str_buf))
        {
            if (flag)
                break;
            line_cnt++;
            istringstream i_stream(str_buf);
            if (line_num == 0)
            {
                int idx = 0;
                while (getline(i_stream, str_conma_buf, ','))
                {
                    VE[idx] = string_to_int(str_conma_buf);
                    idx++;
                }
                if (VE[0] < 200 || VE[0] > 400)
                {
                    cout << "V is out of range : " << VE[0] << ENDL;
                    cout << "line number : " << line_cnt << ENDL;
                    flag = true;
                }
                else if (VE[1] < 1.5 * VE[0] || 2 * VE[0] < VE[1])
                {
                    cout << "E is out of range : " << VE[1] << ENDL;
                    cout << "line number : " << line_cnt << ENDL;
                    flag = true;
                }
                else
                {
                    line_num++;
                    d_max = ceil(4 * sqrt(2.0 * VE[0]));
                }
            }
            else if (line_num >= 1 && line_num <= VE[1])
            {
                int idx = 0;
                while (getline(i_stream, str_conma_buf, ','))
                {
                    edge[idx] = string_to_int(str_conma_buf);
                    idx++;
                }
                if (edge[0] < 1 || edge[1] < 1 || edge[0] > VE[0] || edge[1] > VE[1] || edge[0] == edge[1])
                {
                    cout << "edge error : " << edge[0] << " " << edge[1] << " " << VE[0] << ENDL;
                    cout << "line number : " << line_cnt << ENDL;
                    flag = true;
                }
                else if (edge[2] < 1 || edge[2] > d_max)
                {
                    cout << "weight error : " << edge[2] << " " << VE[0] << " " << d_max << ENDL;
                    cout << "line number : " << line_cnt << ENDL;
                    flag = true;
                }
                else
                {
                    line_num++;
                }
            }
            else if (line_num == VE[1] + 1)
            {
                int T_max = string_to_int(str_buf);
                if (T_max != T)
                {
                    cout << "T_max is wrong : " << T_max << ENDL;
                    cout << "line number : " << line_cnt << ENDL;
                    flag = true;
                }
                else
                {
                    line_num++;
                }
            }
            else
            {
                if (info)
                {
                    int info_i = string_to_int(str_buf);
                    if (info_i & 0)
                    {
                        cout << "info number is wrong : " << info_i << ENDL;
                        cout << "line number : " << line_cnt << ENDL;
                        flag = true;
                    }
                    else
                    {
                        line_num++;
                        info_num++;
                        if (info_i)
                            info = 0;
                    }
                }
                else
                {
                    vii line(2);
                    int idx = 0;
                    while (getline(i_stream, str_conma_buf, ','))
                    {
                        line[idx] = string_to_int(str_conma_buf);
                        idx++;
                    }
                    if (line[0] != info_id)
                    {
                        cout << "id erorr : " << line[0] << " " << info_id << ENDL;
                        cout << "line number : " << line_cnt << ENDL;
                        flag = true;
                    }
                    else if (line[1] < 1 || line[1] > VE[0])
                    {
                        cout << "dst is out of range : " << line[1] << " " << VE[0] << ENDL;
                        cout << "line number : " << line_cnt << ENDL;
                        flag = true;
                    }
                    else
                    {
                        line_num++;
                        info_id++;
                        info = 1;
                    }
                }
                if (info_num > T)
                {
                    cout << "info is over" << ENDL;
                    flag = true;
                }
            }
        }
        if (info_num + info_id + VE[1] + 1 != line_cnt)
        {
            cout << "wrong anywhere" << ENDL;
            cout << "info cnt, Nnew=1 cnt, E : "
                 << info_num << " " << info_id << " " << VE[1] << ENDL;
            cout << "sum all , line cnt :" << (info_num + info_id + VE[1] + 1) << line_cnt << ENDL;
            flag = true;
        }
        if (debug && !flag)
        {
            cout << "success!" << ENDL;
            cout << "V, E, order :" << VE[0] << " " << VE[1] << " " << info_id << ENDL;
            cout << "line cnt :" << line_cnt << " " << line_num << ENDL;
        }
    }
    ifs.close();
    return flag;
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
    const string path = "input_";
    int n = 30;
    string problem = "A";
    rep(i, n)
    {
        string path_in = path + int_to_string(i) + ".csv";
        if (check(path_in, problem))
            cout << "input_" << int_to_string(i) << " is wrong" << ENDL;
    }

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