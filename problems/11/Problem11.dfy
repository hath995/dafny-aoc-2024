include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem11 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq

    function ToStr(num: int): string
        requires num >= 0
    {
        if num < 10 then [numchars()[num]] else ToStr(num / 10) + [numchars()[num % 10]]
    }

    method parseInput(input: string) returns (data: seq<nat>)
    {
        var lines := splitOnBreak(input);
        expect |lines| > 0;
        var res := Map(Integer, split(lines[0], " "));
        expect forall i :: 0 <= i < |res| ==> res[i] >= 0;
        data := res;
    }

    method problem11_1(input: string) returns (x: int) {
        var data := parseInput(input);
        var counts := multiset(data);
        print data, "\n";
        print counts, "\n";
        for i := 0 to 25 {
            var nextCount: multiset<nat> := multiset{};
            while counts != multiset{} 
            {
                var x :| x in counts;
                var xstr := ToStr(x);
                if x == 0 {
                    nextCount := nextCount[1 := nextCount[1] + counts[x]];
                } else if |xstr| % 2 == 0 {
                    var left := xstr[0..|xstr|/2];
                    var right := xstr[|xstr|/2..];
                    expect Integer(left) >= 0;
                    expect Integer(right) >= 0;
                    nextCount := nextCount[Integer(left) := nextCount[Integer(left)] + counts[x]];
                    nextCount := nextCount[Integer(right) := nextCount[Integer(right)] + counts[x]];
                } else {
                    nextCount := nextCount[x*2024 := nextCount[x*2024] + counts[x]];

                }
                counts := counts[x := 0];
            }
            counts := nextCount;
        }
        x := |counts|;
    }

    method problem11_2(input: string) returns (x: int) {
        var data := parseInput(input);
        var counts := multiset(data);
        print data, "\n";
        print counts, "\n";
        for i := 0 to 75 {
            var nextCount: multiset<nat> := multiset{};
            while counts != multiset{} 
            {
                var x :| x in counts;
                var xstr := ToStr(x);
                if x == 0 {
                    nextCount := nextCount[1 := nextCount[1] + counts[x]];
                } else if |xstr| % 2 == 0 {
                    var left := xstr[0..|xstr|/2];
                    var right := xstr[|xstr|/2..];
                    expect Integer(left) >= 0;
                    expect Integer(right) >= 0;
                    nextCount := nextCount[Integer(left) := nextCount[Integer(left)] + counts[x]];
                    nextCount := nextCount[Integer(right) := nextCount[Integer(right)] + counts[x]];
                } else {
                    nextCount := nextCount[x*2024 := nextCount[x*2024] + counts[x]];

                }
                counts := counts[x := 0];
            }
            counts := nextCount;
        }
        x := |counts|;
    }
}
