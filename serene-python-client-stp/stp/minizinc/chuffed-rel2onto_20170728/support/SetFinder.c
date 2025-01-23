// #include "SetFinder.h" 
// #include <bitset>
// #include <vector>
// #include <iostream>
// using namespace std;

// int main () {
//     SetFinder<8> sf;
//     bitset<8> a;
//     a[2] = a[4] = a[5] = a[7] = 1; 
//     cout<< a<<endl;
//     sf.add(a,10);
//     bitset<8> b;
//     b[2] = b[4] = b[5] = 1; 
//     cout<< b<<endl;
//     sf.add(b,20);
//     bitset<8> c;
//     c[2] = c[3] = c[5] = 1; 
//     cout<< c<<endl;
//     sf.add(c,30);

//     bool ok = false;
//     int v = sf.find(a,&ok);
//     cout << v<<" "<<ok<<endl;

//     sf.print();
//     cout<<endl;

//     bitset<8> d;
//     d[2] = d[4] = d[5] = d[7] = 1; 
//     cout<< d<< endl;
//     vector<bitset<8> > subs;
//     vector<int> vals;
//     sf.subsets(d,subs,vals,true,8);
//     for (int i = 0; i < subs.size(); i++)
//         cout << "A" <<subs[i]<<" "<<vals[i]<<endl;
//     sf.print();
//     sf.add(a,10);
//     sf.add(b,20);
//     sf.print();

//     bitset<8> e;
//     e[2] = e[4] =  1; 
//     cout<< e<< endl;
//     vector<bitset<8> > subs2;
//     vector<int> vals2;
//     sf.supersets(e,subs2,vals2);
//     for (int i = 0; i < subs2.size(); i++)
//         cout << "A" <<subs2[i]<<" "<<vals2[i]<<endl;

// }
