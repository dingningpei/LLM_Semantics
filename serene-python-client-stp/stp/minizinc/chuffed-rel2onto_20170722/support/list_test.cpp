#include "trailed_cst_list.h"

#include <cassert>

class MyList : public TrailedConstantAccessList<int,int> {
public:
    MyList(int n) : TrailedConstantAccessList(n){}
    virtual int key(int k) {
        return k;
    }
    void print() {
        std::cout <<"Sparse: ";
        for (int i = 0; i < sparse.size(); i++) {
            std::cout <<sparse[i]<<" ";
        }
        std::cout<<std::endl;
        
        std::cout <<"Dense: ";
        for (int i = 0; i < dense.size(); i++) {
            std::cout <<dense[i]<<" ";
        }
        std::cout<<std::endl;
    }
};

class MyListPairs : public TrailedConstantAccessList<std::pair<int,int>,int> {
public:
    MyListPairs(int n) : TrailedConstantAccessList(n){}
    virtual int key(std::pair<int,int> p) {
        return p.first;
    }
    void print() {
        std::cout <<"Sparse: ";
        for (int i = 0; i < sparse.size(); i++) {
            std::cout <<sparse[i]<<" ";
        }
        std::cout<<std::endl;
        
        std::cout <<"Dense: ";
        for (int i = 0; i < dense.size(); i++) {
            std::cout <<"("<<dense[i].first<<","<<dense[i].second<<") ";
        }
        std::cout<<std::endl;
    }
};


int main() {


    MyList l(5);

    l.print();

    assert(!l.get(4));

    l.add(3);
    l.print();
    assert(l.get(3));
    assert(!l.get(4));

    int val;
    assert(l.get(3,&val));
    assert(val == 3);

    l.add(1);
    l.print();

    l.add(3);
    l.print();


    MyList::const_iterator it;

    for (it = l.begin(); it != l.end(); ++it) {
        std::cout << *it <<std::endl;
    }
    l.print();

    MyListPairs lp(5);

    l.print();
    std::pair<int,int> a(4,90);
    
    assert(!lp.get(lp.key(a)));

    std::pair<int,int> b(3,80);
    lp.add(b);
    lp.print();
    assert(lp.get(lp.key(b)));
    assert(!lp.get(lp.key(a)));

    std::pair<int,int> valp;
    assert(lp.get(lp.key(b),&valp));
    assert(valp.first == 3 && valp.second == 80);


    return 0;
}
