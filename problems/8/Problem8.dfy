include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem8 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq

    method parseInput(input: string) returns (attenas: map<char, seq<(nat, nat)>>,dim: (nat, nat))
    {
        attenas := map[];
        var lines := splitOnBreak(input);
        expect |lines| > 0;
        dim := (|lines[0]|, |lines|-1);
        for i := 0 to |lines| 
        {
            if lines[i] != "" {
                for j := 0 to |lines[i]| 
                {
                    if lines[i][j] != '.' {
                        if lines[i][j] !in attenas {
                            attenas := attenas[lines[i][j] := [(j, i)]];
                        }else {
                            attenas := attenas[lines[i][j] := attenas[lines[i][j]] + [(j, i)]];
                        }
                    }
                }
            }
        }
    }

    function abs(x: int): int
    {
        if x < 0 then -x else x
    }

    function diff(a: (nat, nat), b: (nat, nat)): (int, int)
    {
        (a.0 - b.0, a.1 - b.1)
    }

    function addDiff(a: (nat, nat), b: (int, int)): (int, int)
    {
        (a.0 + b.0, a.1 + b.1)
    }

    function scalarMulDiff(a: (int, int), c: int): (int, int)
    {
        (a.0 * c, a.1 * c)
    }

    function subDiff(a: (nat, nat), b: (int, int)): (int, int)
    {
        (a.0 - b.0, a.1 - b.1)
    }

    predicate InBounds(p: (int, int), dim: (nat, nat)) 
    {
        0 <= p.0 < dim.0 && 0 <= p.1 < dim.1
    }

    method problem8_1(input: string) returns (x: int) {
        var data, dim := parseInput(input);
        print dim, "\n";
        print data, "\n";
        var antinodes: set<(int, int)> := {};
        var freqs := data.Keys;
        var freqSeq := SetToSeq(freqs);
        assert forall x :: x in multiset(freqSeq) ==> x in freqs;
        for i := 0 to |freqSeq| 
        {
            var freq := freqSeq[i];
            var freqData := data[freq];
            for j := 0 to |freqData| 
            {
                var a := freqData[j];
                for k := j+1 to |freqData| 
                {
                    var b := freqData[k];
                    if a != b {
                        var d := diff(a, b);
                        var c := addDiff(a, d);
                        if InBounds(c, dim) {
                            antinodes := antinodes + {c};
                        }
                        var e := subDiff(b, d);
                        if InBounds(e, dim) {
                            antinodes := antinodes + {e};
                        }
                    }
                }
            }
        }
        x := |antinodes|;
    }

    method problem8_2(input: string) returns (x: int) {
        var data, dim := parseInput(input);
        print dim, "\n";
        print data, "\n";
        var antinodes: set<(int, int)> := {};
        var freqs := data.Keys;
        var freqSeq := SetToSeq(freqs);
        assert forall x :: x in multiset(freqSeq) ==> x in freqs;
        for i := 0 to |freqSeq| 
        {
            var freq := freqSeq[i];
            var freqData := data[freq];
            for j := 0 to |freqData| 
            {
                var a := freqData[j];
                for k := j+1 to |freqData| 
                {
                    var b := freqData[k];
                    if a != b {
                        var d := diff(a, b);
                        assert d != (0, 0);
                        var c := addDiff(a, d);
                        ghost var ci := 1;
                        antinodes := antinodes + {a};
                        while InBounds(c, dim)
                            invariant c == addDiff(a, scalarMulDiff(d, ci))
                            decreases abs(dim.0 - c.0), abs(dim.1 - c.1)
                        {
                            antinodes := antinodes + {c};
                            c := addDiff(c, d);
                            ci := ci + 1;
                        }
                        antinodes := antinodes + {b};
                        var e := subDiff(b, d);
                        while InBounds(e, dim)
                        {
                            antinodes := antinodes + {e};
                            e := subDiff(e, d);
                        }
                    }
                }
            }
        }
        x := |antinodes|;

    }
}
