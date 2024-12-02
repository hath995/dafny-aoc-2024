include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem2 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq

    method parseInput(input: string) returns (ss: seq<seq<int>>) {
        var data := splitOnBreak(input);
        ss := Map(s => Map(Integer, split(s, " ")), Filter((s: string) => s != "", data));
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

    method problem2_1(input: string) returns (x: int) {
        var data := parseInput(input);
        x := 0;
        for i := 0 to |data| {
            if SafeReport(data[i]) {
                x := x + 1;
            }
        }
    }

    method problem2_2(input: string) returns (x: int) {
        var data := parseInput(input);
        x := 0;
        for i := 0 to |data| {
            if SafeReport(data[i]) || SafeWithOneRemoved(data[i]) {
                x := x + 1;
            }
        }
    }
}