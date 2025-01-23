#ifndef __DIFF_LOGIC_H__
#define __DIFF_LOGIC_H__

class DifferenceLogic;

class DiffLogic {
    DifferenceLogic * diff;
public:
    DiffLogic(const int numItems);
    ~DiffLogic();
    void addDiff(IntVar * x, IntVar * y, const int d);
    void addReifyDiff(BoolView * b, IntVar * x, IntVar * y, const int d);
    void addImplyDiff(BoolView * b, IntVar * x, IntVar * y, const int d);
};

#endif
