include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem7 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq

    method parseInput(input: string) returns (data: seq<(nat, seq<nat>)>) 
        ensures |data| > 0
        ensures forall x :: x in data ==> |x.1| > 0
    {
        data := [];
        var lines := splitOnBreak(input);
        for i := 0 to |lines| 
            invariant forall x :: x in data ==> |x.1| > 0
        {
            if lines[i] != "" {
                var parts := split(lines[i], ": ");
                expect |parts| == 2;
                var num := Integer(parts[0]);
                expect num >= 0;
                var ss := Map(Integer, split(parts[1]," "));
                expect forall i :: i in ss ==> i >= 0;
                expect |ss| > 0;
                var qq: seq<nat> := [];
                for i := 0 to |ss| {
                    assert ss[i] in ss;
                    qq := qq + [ss[i]];
                }
                expect |qq| > 0;
                data := data + [(num as nat, qq)];
            }
        }
        expect |data| > 0;
    }

    function ToStr(num: int): string
        requires num >= 0
    {
        if num < 10 then [numchars()[num]] else ToStr(num / 10) + [numchars()[num % 10]]
    }

    lemma ToStrTest() {
        assert ToStr(0) == "0";
        assert ToStr(1) == "1";
        assert ToStr(10) == "10";
        assert ToStr(11) == "11";
        assert ToStr(12) == "12";
        assert ToStr(123) == "123";
        assert ToStr(1234) == "1234";
    }

    function concatInts(x: nat, y: nat): nat
        // requires x >= 0 && y >= 0
    {
       var x := Integer(ToStr(x) + ToStr(y));
       if x < 0 then 0 else x
    }

    method concatIntsTest() {
        expect concatInts(1, 2) == 12;
        expect concatInts(12, 3) == 123;
        expect concatInts(123, 4) == 1234;
        expect concatInts(12, 10) == 1210;
        expect concatInts(12, 183) == 12183;
    }

    predicate CanCalculate(target: nat, x: nat, xs: seq<nat>) 
        decreases |xs|
    {
       if x > target || |xs| == 0 then false else if |xs| == 1 then x + xs[0] == target || x * xs[0] == target else CanCalculate(target, x + xs[0], xs[1..]) || CanCalculate(target, x * xs[0], xs[1..])
    }

    predicate CanCalculate2(target: nat, x: nat, xs: seq<nat>) 
        decreases |xs|
    {
       if x > target || |xs| == 0 then false else if |xs| == 1 then x + xs[0] == target || x * xs[0] == target || concatInts(x, xs[0]) == target else CanCalculate2(target, x + xs[0], xs[1..]) || CanCalculate2(target, x * xs[0], xs[1..]) || CanCalculate2(target, concatInts(x, xs[0]), xs[1..])
    }

    method problem7_1(input: string) returns (x: int) {
        var data := parseInput(input);
        x := 0;
        for i := 0 to |data| {
            var num, ss := data[i].0, data[i].1;
            if CanCalculate(num, ss[0], ss[1..]) {
                x := x + num;
            }
        }
    }

    method problem7_2(input: string) returns (x: int) {
        var data := parseInput(input);
        x := 0;
        for i := 0 to |data| {
            var num, ss := data[i].0, data[i].1;
            if CanCalculate2(num, ss[0], ss[1..]) {
                x := x + num;
            }
        } 
    }
}
