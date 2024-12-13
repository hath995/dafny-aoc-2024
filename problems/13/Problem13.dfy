include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../parser/regex.dfy"
include "../4/matrix.dfy"
module Problem13 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq
    import opened Matrix
    import opened RegEx

/*
f(a,b) = 3*a + b
94*a +22*b = 8400
34*a +67*b = 5400
a >= 0
b >= 0

Button A: X+94, Y+34
Button B: X+22, Y+67
Prize: X=8400, Y=5400
*/
    method parseInput(input: string) returns (ss: seq<(Matrix<real>, Matrix<real>)>)
        decreases *
        ensures forall i :: 0 <= i < |ss| ==> isMatrix(ss[i].0) && isMatrix(ss[i].1) && ss[i].0.rows == 2 && ss[i].0.columns == 2 && ss[i].1.rows == 2 && ss[i].1.columns == 1
    {
        var lineGroups := splitOnDoubleBreak(input);
        expect |lineGroups| > 0;
        ss := [];
        for i := 0 to |lineGroups|
            invariant forall i :: 0 <= i < |ss| ==> isMatrix(ss[i].0) && isMatrix(ss[i].1)&& ss[i].0.rows == 2 && ss[i].0.columns == 2 && ss[i].1.rows == 2 && ss[i].1.columns == 1
        {
            var lines := splitOnBreak(lineGroups[i]);
            if lines == [] {
                continue;
            }
            // print lines, "\n";
            expect |lines| >= 3;
            var mchA, capsA := ReMatch("Button A: X\\+((0|1|2|3|4|5|6|7|8|9)+), Y\\+((0|1|2|3|4|5|6|7|8|9)+)", lines[0]);
            var mchB, capsB := ReMatch("Button B: X\\+((0|1|2|3|4|5|6|7|8|9)+), Y\\+((0|1|2|3|4|5|6|7|8|9)+)", lines[1]); 
            var prz, capsPrz := ReMatch("Prize: X=((0|1|2|3|4|5|6|7|8|9)+), Y=((0|1|2|3|4|5|6|7|8|9)+)", lines[2]);
            // print capsA, " ", capsB, " ", capsPrz, "\n";
            expect |capsA| == 5;
            var ax := Integer(capsA[1]);
            var ay := Integer(capsA[3]);
            expect |capsB| == 5;
            var bx := Integer(capsB[1]);
            var bY := Integer(capsB[3]);
            expect |capsPrz| == 5;
            var px := Integer(capsPrz[1]);
            var py := Integer(capsPrz[3]);
            var m := Matrice([[ax as real,bx as real],[ay as real,bY as real]],2,2);
            var b := Matrice([[px as real],[py as real]],2,1);
            expect isMatrix(m);
            expect isMatrix(b);
            ss := ss + [(m,b)];
        }
        expect |ss| > 0;
    }

    function inverse2x2(m: Matrix<real>) : Matrix<real> 
        requires m.rows == 2
        requires m.columns == 2
        requires isMatrix(m)
        requires m.vals[0][0]*m.vals[1][1] - m.vals[0][1]*m.vals[1][0] != 0.0
    {
        var det := m.vals[0][0]*m.vals[1][1] - m.vals[0][1]*m.vals[1][0];
        Matrice([[m.vals[1][1]/det,-m.vals[0][1]/det],[-m.vals[1][0]/det,m.vals[0][0]/det]],2,2)
    }

    method problem13_1(input: string) returns (x: int)
        decreases *
    {
        var data := parseInput(input);
        x := 0;
        for i := 0 to |data|
        {
            if data[i].0.vals[0][0]*data[i].0.vals[1][1] - data[i].0.vals[0][1]*data[i].0.vals[1][0] == 0.0 {
                continue;
            }
            var inv := inverse2x2(data[i].0);
            var res := matMul(inv,data[i].1);
            print res, "\n";
            if res.vals[0][0].Floor as real == res.vals[0][0] && res.vals[1][0].Floor as real == res.vals[1][0] {
                x := x+ res.vals[0][0].Floor*3 + res.vals[1][0].Floor;
            }
        }
    }

    method problem13_2(input: string) returns (x: int)
        decreases *
    {
        var data := parseInput(input);
        x := 0;
        for i := 0 to |data|
        {
            if data[i].0.vals[0][0]*data[i].0.vals[1][1] - data[i].0.vals[0][1]*data[i].0.vals[1][0] == 0.0 {
                continue;
            }
            var adjustedB := Matrice([[data[i].1.vals[0][0] + 10000000000000.0],[data[i].1.vals[1][0] + 10000000000000.0]],2,1);
            assert isMatrix(adjustedB);
            var inv := inverse2x2(data[i].0);
            var res := matMul(inv,adjustedB);
            print res, "\n";
            if res.vals[0][0].Floor as real == res.vals[0][0] && res.vals[1][0].Floor as real == res.vals[1][0] {
                x := x+ res.vals[0][0].Floor*3 + res.vals[1][0].Floor;
            }
        }
    }
}
