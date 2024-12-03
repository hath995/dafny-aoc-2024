include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem2 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq

    method parseInput(input: string) returns (ss: seq<seq<int>>)
        ensures Distinct(ss)
    {
        var data := splitOnBreak(input);
        ss := Map(s => Map(Integer, split(s, " ")), Filter((s: string) => s != "", data));
        expect Distinct(ss), "Data must be distinct";
    }

    predicate Increasing(s: seq<int>) {
        if |s| <= 1 then true else s[0] <= s[1] && Increasing(s[1..])
    }

    predicate Increasing2(s: seq<int>) {
        forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
    }

    predicate Decreasing(s: seq<int>) {
        if |s| <= 1 then true else s[0] >= s[1] && Decreasing(s[1..])
    }

    predicate Decreasing2(s: seq<int>) {
        forall i :: 0 <= i < |s| - 1 ==> s[i] >= s[i + 1]
    }

    function abs(x: int): int {
        if x < 0 then -x else x
    }

    predicate DiffersBy(ss: seq<int>) {
        forall i :: 0 <= i < |ss| - 1 ==> 1 <= abs(ss[i] - ss[i + 1]) <= 3
    }

    predicate SafeReport(ss: seq<int>) {
        // (Increasing(ss) || Decreasing(ss)) && DiffersBy(ss)
        (Increasing2(ss) || Decreasing2(ss)) && DiffersBy(ss)
    }

    predicate SafeWithOneRemoved(ss: seq<int>) {
        exists i :: 0 <= i < |ss|  && SafeReport(ss[0..i] + ss[i + 1..])
    }

    predicate Distinct(sss: seq<seq<int>>) {
        forall i, j :: 0 <= i < j < |sss| ==> sss[i] != sss[j]
    }

    method problem2_1(input: string) returns (x: int)
        ensures exists ds: set<seq<int>> :: (forall d :: d in ds ==> SafeReport(d)) && |ds| == x
    {
        var data := parseInput(input);
        x := 0;
        ghost var ds: set<seq<int>> := {};
        for i := 0 to |data| 
            invariant ds == set y | y in data[0..i] && SafeReport(y)
            invariant x == |ds|
        {
            if SafeReport(data[i]) {
                assert |ds| == x;
                x := x + 1;
                ds := ds + {data[i]};
            }
        }
    }

    method problem2_2(input: string) returns (x: int) 
        ensures exists ds: set<seq<int>> :: (forall d :: d in ds ==> SafeReport(d) || SafeWithOneRemoved(d)) && |ds| == x
    {
        var data := parseInput(input);
        ghost var ds: set<seq<int>> := {};
        x := 0;
        for i := 0 to |data|
            invariant ds == set y | y in data[0..i] && (SafeReport(y) || SafeWithOneRemoved(y))
            invariant x == |ds|
        {
            if SafeReport(data[i]) || SafeWithOneRemoved(data[i]) {
                x := x + 1;
                ds := ds + {data[i]};
            }
        }
    }
}