include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../4/matrix.dfy"
module Problem10 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq
    import opened Matrix

    method parseInput(input: string) returns (data: seq<seq<nat>>, dim: (nat, nat))
        ensures |data| > 0
        ensures dim.0 > 0
        ensures dim.1 > 0
        ensures dim.1 == |data|
        ensures forall row :: row in data ==> |row| == dim.0
    {
        var lines := splitOnBreak(input);
        data := [];
        expect |lines| > 0;
        dim := (|lines[0]|, |lines|-1);
        for i := 0 to |lines| 
            invariant forall row :: row in data ==> |row| == dim.0
        {
            if lines[i] != "" {
                var row: seq<nat> := [];
                for j := 0 to |lines[i]| {
                    if lines[i][j] != '\n' {
                        var height := Integer([lines[i][j]]);
                        expect height >= 0;
                        row := row + [height];
                    }
                }
                expect |row| == dim.0;
                data := data + [row];
            }
        }
        expect dim.1 == |data|;
        expect dim.0 > 0;
        expect dim.1 > 0;
        expect |data| > 0;
    }

    function pairToIndex(p: (nat, nat), dim: (nat, nat)): nat
        requires dim.0 > 0
        requires dim.1 > 0
        requires 0 <= p.0 < dim.0
        requires 0 <= p.1 < dim.1
    {
        p.0 + p.1 * dim.0
    }

    lemma pairToIndexLess(p: (nat, nat), dim: (nat, nat))
        requires dim.0 > 0
        requires dim.1 > 0
        requires 0 <= p.0 < dim.0
        requires 0 <= p.1 < dim.1
        ensures pairToIndex(p, dim) < dim.0 * dim.1
        decreases p.1
    {
        if p.1 == 0 {
            assert pairToIndex(p, dim) < dim.0 * dim.1;
        } else {
            calc {
                pairToIndex(p, dim);
                p.0 + p.1 * dim.0;
                p.0 + p.1 * dim.0 - dim.0 + dim.0;
                p.0 + (p.1 - 1) * dim.0 + dim.0;
                pairToIndex((p.0, p.1 - 1), dim) + dim.0;
            }
            pairToIndexLess((p.0, p.1 - 1), (dim.0, dim.1-1));
            assert pairToIndex(p, dim) < dim.0 * dim.1;
        }
    }

    function indexToPair(i: nat, dim: (nat, nat)): (nat, nat)
        requires dim.0 > 0
        requires dim.1 > 0
        requires i < dim.0 * dim.1
        ensures 0 <= indexToPair(i, dim).0 < dim.0
        ensures 0 <= indexToPair(i, dim).1 < dim.1
    {
        assert i / dim.0 < dim.1 by {
            if i / dim.0 >= dim.1 {
                calc{
                    dim.0*(i / dim.0);
                    i;
                }
                assert false;
            }
        }
        (i % dim.0, i / dim.0)
    }

    function abs(x: int): int
    {
        if x < 0 then -x else x
    }

    predicate IsNeighbor(p1: (nat, nat), p2: (nat, nat), dim: (nat, nat))
        requires 0 <= p1.0 < dim.0
        requires 0 <= p1.1 < dim.1
        requires 0 <= p2.0 < dim.0
        requires 0 <= p2.1 < dim.1
    {
        p1 != p2 && abs(p1.0 - p2.0) <= 1 && abs(p1.1 - p2.1) <= 1 && (p1.0 == p2.0 || p1.1 == p2.1)
    }

    method MapToDistanceMatrix(data: seq<seq<nat>>, dim: (nat, nat)) returns (matrix: array2<NumberOrInfinity>)
        requires |data| > 0
        requires dim.0 > 0
        requires dim.1 > 0
        requires forall row :: row in data ==> |row| == dim.0
        requires dim.1 == |data|
        ensures matrix.Length0 == dim.0 * dim.1
        ensures matrix.Length1 == dim.0 * dim.1
        ensures matrix.Length0 == matrix.Length1
        ensures fresh(matrix)
    {
        matrix := new NumberOrInfinity[dim.0 * dim.1, dim.0 * dim.1];
        for i := 0 to matrix.Length0 {
            for j := 0 to matrix.Length1 {
                var p1 := indexToPair(i, dim);
                var p2 := indexToPair(j, dim);
                if IsNeighbor(p1, p2, dim) && abs(data[p1.1][p1.0] - data[p2.1][p2.0] as int) == 1 {
                    matrix[i, j] := Number(1);
                } else {
                    matrix[i, j] := Infinity;
                }
            }
        }
        return matrix;
    }

    method MapToAdjacencyMatrix(data: seq<seq<nat>>, dim: (nat, nat)) returns (matrix: array2<nat>)
        requires |data| > 0
        requires dim.0 > 0
        requires dim.1 > 0
        requires forall row :: row in data ==> |row| == dim.0
        requires dim.1 == |data|
        ensures matrix.Length0 == dim.0 * dim.1
        ensures matrix.Length1 == dim.0 * dim.1
        ensures matrix.Length0 == matrix.Length1
        ensures fresh(matrix)
    {
        matrix := new nat[dim.0 * dim.1, dim.0 * dim.1];
        for i := 0 to matrix.Length0 {
            for j := 0 to matrix.Length1 {
                var p1 := indexToPair(i, dim);
                var p2 := indexToPair(j, dim);
                if IsNeighbor(p1, p2, dim) && abs(data[p1.1][p1.0] - data[p2.1][p2.0] as int) == 1 {
                    matrix[i, j] := 1;
                } else {
                    matrix[i, j] := 0;
                }
            }
        }
        return matrix;
    }

    lemma ThereIsAMinimum(s: set<nat>)
        requires s != {}
        ensures exists x :: x in s && forall y :: y in s ==> x <= y
    {
        assert s != {};
        var x :| x in s;
        if s == {x} {
        } else {
            var s' := s - {x};
            assert s == s' + {x};
            ThereIsAMinimum(s');
        }
    }

    function SetToSequence(s: set<nat>): seq<nat>
        ensures var q := SetToSequence(s); forall i :: 0 <= i < |q| ==> q[i] in s
        ensures |SetToSequence(s)| == |s|
        ensures forall p :: p in s ==> p in SetToSequence(s)
    {
    if s == {} then [] else
        ThereIsAMinimum(s);
        var x :| x in s && forall y :: y in s ==> x <= y;
        [x] + SetToSequence(s - {x})
    }

    method printMatrix(matrix: array2<NumberOrInfinity>)
    {
        for i := 0 to matrix.Length0 {
            for j := 0 to matrix.Length1 {
                if matrix[i, j].Infinity? {
                    print ".", " ";
                }else{
                    print matrix[i,j].n, " ";
                }
            }
            print "\n";
        }
    }

    method printMatrixNat(matrix: array2<nat>)
    {
        for i := 0 to matrix.Length0 {
            for j := 0 to matrix.Length1 {
                    print matrix[i,j], " ";
            }
            print "\n";
        }
    }

    method  problem10_1(input: string) returns (x: int) {
        var data, dim := parseInput(input);
        assert dim.0 > 0;
        assert dim.1 > 0;
        print dim, "\n";
        var matrix := MapToDistanceMatrix(data, dim);
        var trailheads := set x: nat,y: nat | 0 <= x < dim.0 && 0 <= y < dim.1 && 0 <= (x,y).0 < dim.0 && 0 <= (x, y).1 < dim.1 && data[y][x] == 0 :: pairToIndex((x, y), dim);
        assert forall x :: x in trailheads ==> x < dim.0 * dim.1 by {
            forall x | x in trailheads
                ensures x < dim.0 * dim.1
            {
                var p: (nat, nat) :| 0 <= p.0 < dim.0 && 0 <= p.1 < dim.1 && pairToIndex(p, dim) == x;
                pairToIndexLess(p, dim);
            }
        }
        var peaks := set x: nat,y: nat | 0 <= x < dim.0 && 0 <= y < dim.1 && 0 <= (x,y).0 < dim.0 && 0 <= (x, y).1 < dim.1 && data[y][x] == 9 :: pairToIndex((x, y), dim);
        assert forall x :: x in peaks ==> x < dim.0 * dim.1 by {
            forall x | x in peaks
                ensures x < dim.0 * dim.1
            {
                var p: (nat, nat) :| 0 <= p.0 < dim.0 && 0 <= p.1 < dim.1 && pairToIndex(p, dim) == x;
                pairToIndexLess(p, dim);
            }
        }
        // printMatrix(matrix);
        FloydWarshall(matrix);
        x := 0;
        var trailheadSeq := SetToSequence(trailheads);
        assert forall x :: x in trailheadSeq ==> x in trailheads;
        var peakSeq := SetToSequence(peaks);
        // assert forall x :: x in peakSeq ==> x in peaks;
        // assert forall x :: x in peakSeq ==> x < dim.0 * dim.1;
        // var peaksPairs := Map(p => indexToPair(p, dim), peakSeq);
        // print "Peaks", peaksPairs, "\n";
        assert forall x :: x in peakSeq ==> x in peaks;
        for i := 0 to |trailheadSeq| {
            var trailhead := trailheadSeq[i];
            // var trailheadPair := indexToPair(trailhead, dim);
            // var trailheadX := 0;
            for j := 0 to |peakSeq| {
                var peak := peakSeq[j];
                if matrix[trailhead, peak] != Infinity && matrix[trailhead, peak].n == 9 {
                    // trailheadX := trailheadX + 1;
                    // print indexToPair(trailhead, dim), " ", indexToPair(peak, dim), " ", matrix[trailhead, peak], "\n";
                    x := x + 1;
                }
            }
            // print trailheadPair, " ", trailheadX, "\n";
        }
    }

    method multTest() {
        var test: array2<nat> := new nat[3, 3];
        var data: seq<seq<nat>> := [[0,1,4],[2,1,0],[4,2,3]];
        var test2: array2<nat> := new nat[3, 3];
        var data2: seq<seq<nat>> := [[3,2,1],[1,0,4],[2,6,8]];
        for i := 0 to 3 {
            for j := 0 to 3 {
                test[i, j] := data[i][j];
                test2[i, j] := data2[i][j];
            }
        }
        var multest := matrixMul(test, test2);
        printMatrixNat(multest);
    }

    method problem10_2(input: string) returns (x: int) {
        var data, dim := parseInput(input);
        assert dim.0 > 0;
        assert dim.1 > 0;
        print dim, "\n";
        x := 0;
        var matrix := MapToAdjacencyMatrix(data, dim);
        var trailheads := set x: nat,y: nat | 0 <= x < dim.0 && 0 <= y < dim.1 && 0 <= (x,y).0 < dim.0 && 0 <= (x, y).1 < dim.1 && data[y][x] == 0 :: pairToIndex((x, y), dim);
        assert forall x :: x in trailheads ==> x < dim.0 * dim.1 by {
            forall x | x in trailheads
                ensures x < dim.0 * dim.1
            {
                var p: (nat, nat) :| 0 <= p.0 < dim.0 && 0 <= p.1 < dim.1 && pairToIndex(p, dim) == x;
                pairToIndexLess(p, dim);
            }
        }
        var peaks := set x: nat,y: nat | 0 <= x < dim.0 && 0 <= y < dim.1 && 0 <= (x,y).0 < dim.0 && 0 <= (x, y).1 < dim.1 && data[y][x] == 9 :: pairToIndex((x, y), dim);
        assert forall x :: x in peaks ==> x < dim.0 * dim.1 by {
            forall x | x in peaks
                ensures x < dim.0 * dim.1
            {
                var p: (nat, nat) :| 0 <= p.0 < dim.0 && 0 <= p.1 < dim.1 && pairToIndex(p, dim) == x;
                pairToIndexLess(p, dim);
            }
        }
        print "Begin", "\n";
        var m2 := matrixMul(matrix, matrix);
        print "Begin m4", "\n";
        var m4 := matrixMul(m2, m2);
        print "Begin m8", "\n";
        var m8 := matrixMul(m4, m4);
        print "Begin m9", "\n";
        var m9 := matrixMul(m8, matrix);
        var trailheadSeq := SetToSequence(trailheads);
        assert forall x :: x in trailheadSeq ==> x in trailheads;
        var peakSeq := SetToSequence(peaks);
        // printMatrixNat(m8);

        for i := 0 to |trailheadSeq| {
            var trailhead := trailheadSeq[i];
            // var trailheadPair := indexToPair(trailhead, dim);
            // var trailheadX := 0;
            for j := 0 to |peakSeq| {
                var peak := peakSeq[j];
                if m9[trailhead, peak] != 0 {
                    // trailheadX := trailheadX + 1;
                    // print indexToPair(trailhead, dim), " ", indexToPair(peak, dim), " ", m9[trailhead, peak], "\n";
                    x := x + m9[trailhead, peak];
                }
            }
            // print trailheadPair, " ", trailheadX, "\n";
        }
    }
}
