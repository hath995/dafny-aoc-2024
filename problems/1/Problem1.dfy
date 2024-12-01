include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem1 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq
    import opened Std.Relations

    function abs(x: int): int {
        if x < 0 then -x else x
    }

    method parseInput(input: string) returns (left: seq<int>, right: seq<int>) 
        ensures |left| == |right|
    {
        left := [];
        right := [];
        var ids := splitOnBreak(input);
        for i := 0 to |ids| 
            invariant |left| == |right|
        {
            if ids[i] != "" {
                var idsPieces := split(ids[i], "   ");
                expect |idsPieces| == 2;
                assume {:axiom} |idsPieces| == 2;
                left := left+[Integer(idsPieces[0])];
                right := right+[Integer(idsPieces[1])];
            }
        }
    }

    predicate lte(x: int, y: int) {
        x <= y
    }

    function MapLists(left: seq<int>, right: seq<int>): seq<int> 
        requires |left| == |right|
    {
        if |left| == 0 then [] else [abs(right[0]-left[0])]+MapLists(left[1..], right[1..])
    }

    method problem1_1(input: string) returns (x: int)
    {
        var left, right := parseInput(input);
        left := MergeSortBy(lte, left);
        right := MergeSortBy(lte, right);
        return FoldLeft((sum, val) => sum + val, 0, MapLists(left, right));
    }

    method problem1_2(input: string) returns (x: int)
    {
        var left, right := parseInput(input);
        left := MergeSortBy(lte, left);
        var rightms := multiset(right);
        return  FoldLeft((sum, val) => sum + val, 0, Map((val:int) => val * rightms[val], left));
    }
}