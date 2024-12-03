include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../parser/regex.dfy"
module Problem3 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq
    import opened RegEx
    method ParseInput(input: string) returns (ss: seq<(int, int)>) 
       decreases *
    {
        var data := split(input, "mul");
        // print data, "\n";
        ss := [];
        for i := 0 to |data| 
        {
            var mch, caps := ReMatch("\\(((0|1|2|3|4|5|6|7|8|9)+),((0|1|2|3|4|5|6|7|8|9)+)\\).*", data[i]);
            if mch {
                expect |caps| == 5;
                assume {:axiom} |caps| == 5;
                ss := ss + [(Integer(caps[1]), Integer(caps[3]))];
                // print Integer(caps[1]), " ", Integer(caps[3]), "\n";
            }
        }
    }

    method problem3_1(input: string) returns (x: int)
        decreases *
    {
        var data := ParseInput(input);
        return FoldLeft((sum, val) => sum +val, 0, Map((val: (int, int)) => val.0 * val.1, data));
    }

    method ParseInput2(input: string) returns (ss: seq<(int, int)>) 
       decreases *
    {
        var donts := split(input, "don't()");
        var dos := split(input, "do()");
        var do_indices := [0];
        for i := 0 to |dos| 
            invariant |do_indices| == i + 1
        {
            do_indices := do_indices + [do_indices[i] + |dos[i]| + 4];
        }
        var dont_indices: seq<int> := [];
        for i := 0 to |donts|
            invariant |dont_indices| == i
        {
            if i == 0 {
                dont_indices := [ |donts[i]| + 7];
            }else{
                dont_indices := dont_indices + [dont_indices[i-1] + |donts[i]| + 7];
            }
        }
        assume {:axiom} |dont_indices| > 0;
        print do_indices, "\n";
        print dont_indices, "\n";
        var do := 0;
        var dont := 0;
        var intervals: seq<(int, int, bool)> := [];
        while do < |do_indices| && dont < |dont_indices|
            invariant do <= |do_indices| && dont <= |dont_indices|
        {
            if do_indices[do] < dont_indices[dont] {
                intervals := intervals + [(do_indices[do], dont_indices[dont], true)];
                do := do + 1;
            }else{
                intervals := intervals + [(dont_indices[dont], do_indices[do], false)];
                dont := dont + 1;
            }
        }
        print intervals, "\n";


        var data := split(input, "mul");
        var length := 0;
        var enabled := true;
        // print data, "\n";
        var interval := 0;
        ss := [];
        for i := 0 to |data| 
        {
            if interval < |intervals| && length >= intervals[interval].0 && length <= intervals[interval].1 {
                enabled := intervals[interval].2;
            }else {
                while interval < |intervals| && length > intervals[interval].1 {
                    interval := interval + 1;
                }
                if interval < |intervals| {
                    enabled := intervals[interval].2;
                }
            }
            var mch, caps := ReMatch("\\(((0|1|2|3|4|5|6|7|8|9)+),((0|1|2|3|4|5|6|7|8|9)+)\\).*", data[i]);
            if mch && enabled {
                expect |caps| == 5;
                assume {:axiom} |caps| == 5;
                print i," ", data[i], " ", length, " ", enabled, "\n";
                ss := ss + [(Integer(caps[1]), Integer(caps[3]))];
                // print Integer(caps[1]), " ", Integer(caps[3]), "\n";
            }
            length := length + |data[i]| + 3;
        }
    }

    method problem3_2(input: string) returns (x: int) 
        decreases *
    {
        var data := ParseInput2(input);
        print data, "\n";
        return FoldLeft((sum, val) => sum +val, 0, Map((val: (int, int)) => val.0 * val.1, data));
    }
}
