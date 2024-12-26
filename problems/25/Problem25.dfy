include "../../parser/split.dfy"
module Problem25 {
    import opened Split
    import opened Std.Collections.Seq
    type Lock = seq<nat>
    type Key = seq<nat>

    predicate IsLock(x: seq<string>) 
        requires |x| > 0
    {
        forall i :: 0 <= i < |x[0]| ==> x[0][i] == '#'
    }

    method MeasureHeights(x: seq<string>) returns (heights: seq<nat>)
        requires |x| >= 7
        requires forall i :: 0 <= i < 7 ==> |x[i]| == 5
        ensures |heights| == 5
        ensures forall i :: 0 <= i < 5 ==> 1 <= heights[i] < 7
    {
        heights := [];
        for i := 0 to 5 
            invariant |heights| == i
            invariant forall j :: 0 <= j < i ==> 0 < heights[j] < 7
        {
            var height := 0;
            for j := 0 to 7 {
                if x[j][i] == '#' {
                    height := height + 1;
                }
            }
            expect 0 < height < 7;
            heights := heights + [height];
        }
    }

    method parseInput(input: string) returns (locks: seq<Lock>, keys: seq<Key>) 
        ensures forall i :: 0 <= i < |locks| ==> |locks[i]| == 5
        ensures forall i :: 0 <= i < |keys| ==> |keys[i]| == 5
        ensures forall i :: 0 <= i < |locks| ==> forall j :: 0 <= j < 5 ==> 1 <= locks[i][j] < 7
        ensures forall i :: 0 <= i < |keys| ==> forall j :: 0 <= j < 5 ==> 1 <= keys[i][j] < 7
    {
        locks := [];
        keys := [];
        var data := splitOnDoubleBreak(input);
        for i := 0 to |data| 
            invariant forall lock :: 0 <= lock < |locks| ==> |locks[lock]| == 5
            invariant forall key :: 0 <= key < |keys| ==> |keys[key]| == 5
            invariant forall lock :: 0 <= lock < |locks| ==> forall j :: 0 <= j < 5 ==> 1 <= locks[lock][j] < 7
            invariant forall key :: 0 <= key < |keys| ==> forall j :: 0 <= j < 5 ==> 1 <= keys[key][j] < 7
        {
            if data[i] != "" {
                var lines := splitOnBreak(data[i]);
                // print lines, "\n";
                expect |lines| >= 7;
                expect forall j :: 0 <= j < 7 ==> |lines[j]| == 5;
                if IsLock(lines) {
                    var heights := MeasureHeights(lines);
                    locks := locks + [heights];
                } else {
                    var heights := MeasureHeights(lines);
                    keys := keys + [heights];
                }
            }
        }
    }

    method problem25_1(input: string) returns (x: int) {
        var locks, keys := parseInput(input);
        print locks, "\n";
        print keys, "\n";
        var groups: map<nat, map<nat, set<Key>>> := map[];
        for j := 0 to 5 
            invariant forall k :: 0 <= k < j ==> k in groups
            invariant forall k :: 0 <= k < j ==> forall l :: 0 <= l < 7 ==> l in groups[k]
        {
            groups := groups[j := map[]];
            for k := 0 to 7 
                invariant forall i :: 0 <= i < j ==> i in groups
                invariant forall k :: 0 <= k < j ==> forall l :: 0 <= l < 7 ==> l in groups[k]
                invariant j in groups
                invariant forall i :: 0 <= i < k ==> i in groups[j]
            {
                groups := groups[j := groups[j] + groups[j][k := {}]];
            }
        }
        assert forall i :: 0 <= i < 5 ==> i in groups;
        assert forall i :: 0 <= i < 5 ==> forall j :: 0 <= j <= 6 ==> j in groups[i];
        for i := 0 to |keys| 
            invariant forall k :: 0 <= k < 5 ==> k in groups
            invariant forall i :: 0 <= i < 5 ==> forall j :: 0 <= j <= 6 ==> j in groups[i]
        {
            var key := keys[i];
            for j := 0 to 5 
                invariant forall k :: 0 <= k < 5 ==> k in groups
                invariant forall i :: 0 <= i < 5 ==> forall j :: 0 <= j <= 6 ==> j in groups[i]
                // invariant 0 <= j <= 5 && j in groups
                // invariant forall z :: 0 <= z < j ==> key[j] < 7
            {
                for k := key[j] to 7
                    invariant forall k :: 0 <= k < 5 ==> k in groups
                    invariant forall i :: 0 <= i < 5 ==> forall j :: 0 <= j <= 6 ==> j in groups[i]
                    invariant key[j]+1 <= 7
                {

                    groups := groups[j := groups[j][k := groups[j][k] + {key}]];
                }
            }
        }
        // print groups[0], "\n\n";
        // print groups[1], "\n\n";
        // print groups[2], "\n\n";
        // print groups[3], "\n\n";
        // print groups[4], "\n\n";
        x := 0;
        for i := 0 to |locks| 
        {
            // print "Lock ", i," ", locks[i], "\n";
            var possibleKeys: set<Key> := groups[0][7-locks[i][0]];
            // print possibleKeys, "\n";
            for j := 1 to 5 
            {
                // print groups[j][6-locks[i][j]], "\n";
                possibleKeys := possibleKeys * groups[j][7-locks[i][j]];
            }
            x := x + |possibleKeys|;
        }
    }

    method problem25_2(input: string) returns (x: int) {
        return 4;
    }
}
