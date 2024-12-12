include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "./QuickUnion.dfy"
module Problem12 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq
    import opened QuickUnion
    method parseInput(input: string) returns (data: seq<string>, dim: (nat, nat))
        ensures |data| > 0
        ensures dim.1 > 0
        ensures dim.0 > 0
        ensures dim.1 == |data|
        ensures forall x :: x in data ==> |x| == dim.0
    {
        data := [];
        var lines := splitOnBreak(input);
        expect |lines| > 0;
        expect |lines[0]| > 0;
        dim := (|lines[0]|, |lines|-1);
        expect dim.1 > 0;
        for i := 0 to |lines| 
            invariant forall x :: x in data ==> |x| == dim.0
        {
            if lines[i] != "" {
                expect |lines[i]| == dim.0;
                data := data + [lines[i]];
            }
        }
        expect |data| == |lines|-1;
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

    method problem12_1(input: string) returns (x: int) 
        decreases *
    {
        var data, dim := parseInput(input);
        var union := new QuickUnion(dim.0 * dim.1);
        x := 0;
        assert union.n == dim.0 * dim.1;
        assert union.parent.Length == dim.0 * dim.1;
        assert fresh(union);
        assert union.Valid();
        for i := 0 to dim.1 
            invariant union.n == dim.0 * dim.1
            invariant union.Valid()
            modifies  union.size, union.parent
        {
            for j := 0 to dim.0
                invariant union.n == dim.0 * dim.1
                invariant union.Valid()
                modifies  union.size, union.parent
            {
                if i+1 < dim.1 && data[i][j] == data[i+1][j] {
                    pairToIndexLess((j,i), dim);
                    pairToIndexLess((j,i+1), dim);
                    assert union.parent.Length == dim.0 * dim.1;
                    union.union(pairToIndex((j,i), dim), pairToIndex((j,i+1), dim));
                }
                if j+1 < dim.0 && data[i][j] == data[i][j+1] {
                    pairToIndexLess((j,i), dim);
                    pairToIndexLess((j+1,i), dim);
                    assert union.parent.Length == dim.0 * dim.1;
                    union.union(pairToIndex((j,i), dim), pairToIndex((j+1,i), dim));
                }
            }
        }
        var groupings: map<nat, seq<(nat, nat)>> := map[];
        for i := 0 to dim.0 * dim.1 
            invariant union.n == dim.0 * dim.1
            invariant union.Valid()
            invariant forall key :: key in groupings.Keys ==> forall x :: x in groupings[key] ==> 0 <= x.0 < dim.0 && 0 <= x.1 < dim.1
            modifies union.parent
        {
            var root := union.findRoot(i);
            if root !in groupings {
                groupings := groupings[root := [indexToPair(i, dim)]];
            } else {
                groupings := groupings[root := groupings[root] + [indexToPair(i, dim)]];
            }
        }
        var groups := groupings.Keys;
        var what := groupings.Values;
        while groups != {} {
            var group :| group in groups;
            var groupMembers := groupings[group];
            groups := groups - {group};
            var perimeter := 0;
            for i := 0 to |groupMembers| {
                var p: (nat, nat) := groupMembers[i];
                if (0 <= (p.0-1 as int) && data[p.1][p.0-1] != data[p.1][p.0]) || p.0 == 0 {
                    perimeter := perimeter + 1;
                }
                if (p.0+1 < dim.0 && data[p.1][p.0+1] != data[p.1][p.0]) || p.0 == dim.0-1 {
                    perimeter := perimeter + 1;
                }
                if (0 <= p.1-1 && data[p.1-1][p.0] != data[p.1][p.0]) || p.1 == 0 {
                    perimeter := perimeter + 1;
                }
                if (p.1+1 < dim.1 && data[p.1+1][p.0] != data[p.1][p.0]) || p.1 == dim.1-1 {
                    perimeter := perimeter + 1;
                }
            }
            x := x + perimeter * |groupMembers|;
        }

    }

    method problem12_2(input: string) returns (x: int) {
        return 4;
    }
}
