include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem5 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq

    method parseInput(input: string) returns (orderingRules: map<int, seq<int>>, updates: seq<seq<int>>) 
    {
        var data := splitOnDoubleBreak(input);
        expect |data| == 2;
        assert |data| == 2;
        var orderingRulesString := splitOnBreak(data[0]);
        var updatesString := splitOnBreak(data[1]);
        orderingRules := map[];
        updates := [];
        for i := 0 to |orderingRulesString| 
        {
            if orderingRulesString[i] != "" {
                var parts := split(orderingRulesString[i], "|");
                expect |parts| == 2;
                assert |parts| == 2;
                var a := Integer(parts[0]);
                var b := Integer(parts[1]);
                if a !in orderingRules {
                    orderingRules := orderingRules[a := []];
                }
                orderingRules := orderingRules[a := orderingRules[a] + [b]];
            }
        }

        for i := 0 to |updatesString| 
        {
            if updatesString[i] != "" {
                updates := updates + [Map(Integer, split(updatesString[i], ","))];
            }
        }

    }

    predicate RulesSatisfied(orderingRules: map<int, seq<int>>, i: int, update: seq<int>)
        requires 0 <= i < |update|
    {
        if update[i] in orderingRules then 
            forall j :: 0 <= j < |orderingRules[update[i]]| ==> if orderingRules[update[i]][j] in update then (forall k :: 0 <= k < |update| && update[k] == orderingRules[update[i]][j] ==> k > i) else true
        else
            true
    }

    predicate InOrder(orderingRules: map<int, seq<int>>, update: seq<int>) {
        forall i :: 0 <= i < |update| ==> RulesSatisfied(orderingRules, i, update) 
    }

    method problem5_1(input: string) returns (x: int) {
        var orderingRules, updates := parseInput(input);
        print orderingRules, "\n";
        print updates, "\n";
        x := 0;
        for i := 0 to |updates| 
        {
            if InOrder(orderingRules, updates[i]) {
                expect |updates[i]| > 0;
                x := x + updates[i][ |updates[i]|/2 ];
            }
        }
    }

    lemma ThereIsAMinimum(s: set<int>)
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

    function SetToSequence(s: set<int>): seq<int>
        ensures var q := SetToSequence(s); forall i :: 0 <= i < |q| ==> q[i] in s
        ensures |SetToSequence(s)| == |s|
        ensures forall p :: p in s ==> p in SetToSequence(s)
    {
    if s == {} then [] else
        ThereIsAMinimum(s);
        var x :| x in s && forall y :: y in s ==> x <= y;
        [x] + SetToSequence(s - {x})
    }

    lemma SetSizeLimit(s: set<int>, n: int, p: int -> bool)
        requires n >= 0
        requires s == set i | 0 <= i < n && p(i)
        ensures |s| <= n
    {
        if n == 0 {
            assert s == {};
            assert |s| == 0;
            assert |s| <= n;
        } else if n == 1 {
            if p(0) {
                assert s == {0};
                assert |s| == 1;
                assert |s| <= n;
            } else {
                assert s == {};
                assert |s| == 0;
                assert |s| <= n;
            }

        }else{
            SetSizeLimit(s - {n-1}, n-1, p);
        }
    }


    method SortByRules(orderingRules: map<int, seq<int>>, update: seq<int>) returns (sorted: seq<int>) 
        ensures multiset(sorted) == multiset(update)
        ensures InOrder(orderingRules, sorted)
        decreases *
    {
        sorted := update;
        label cont: while !InOrder(orderingRules, sorted) 
            invariant multiset(sorted) == multiset(update)
            decreases *
        {
            print sorted, "\n";
            var i := |sorted| - 1;
            while i >= 0
                invariant multiset(sorted) == multiset(update)
            {
                if i < |sorted| && !RulesSatisfied(orderingRules, i, sorted) {
                    assert 0 <= i < |sorted|;
                    var badIndices := set j | 0 <= j < i < |sorted| && sorted[j] in orderingRules[sorted[i]];
                    SetSizeLimit(badIndices, i, j =>  0 <= j < |sorted| && sorted[j] in orderingRules[sorted[i]]);
                    assert |badIndices| <= i;
                    var badIndicesSeq := SetToSequence(badIndices);
                    assert |badIndicesSeq| < |sorted|;
                    for j := 0 to |badIndicesSeq| 
                        invariant i < |sorted|
                        invariant |badIndicesSeq| <= i
                        invariant |badIndicesSeq| < |sorted|
                        invariant forall k :: k in badIndicesSeq ==> 0 <= k < i
                        invariant multiset(sorted) == multiset(update)
                    {
                        var index := badIndicesSeq[j];
                        assert 0 <= index < i < |sorted|;
                        assert sorted == sorted[0..index]  + [sorted[index]]+ sorted[index+1..index+2] + sorted[index+2..];
                        sorted := sorted[0..index] + sorted[index+1..index+2] + [sorted[index]] + sorted[index+2..];
                    }
                    continue cont;
                }
                i := i - 1;
            }
        }
    }

    method problem5_2(input: string) returns (x: int)
        decreases *
    {
        var orderingRules, updates := parseInput(input);
        x := 0;
        for i := 0 to |updates| 
        {
            if !InOrder(orderingRules, updates[i]) {
                var sorted := SortByRules(orderingRules, updates[i]);
                expect |sorted| > 0;
                print sorted, "\n";
                x := x + sorted[ |sorted|/2 ];
            }
        }
    }
}
