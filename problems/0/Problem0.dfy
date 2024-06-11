include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem0 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq

    method parseInput(input: string) returns (result: seq<seq<int>>) {
        var data := splitOnDoubleBreak(input);
        result := Map(s => Map(xs => Integer(xs), Filter(xs => xs != "", splitOnBreak(s))), data);
    }

    method problem0_1(input: string) returns (x: int)
    {
        var data := parseInput(input);
        var sums: seq<int> := MergeSortBy(
            (x,y) => x >= y,
            Map((items) => FoldLeft((x: int,y: int) => x+y, 0, items), data)
        );
        //assume |sums| > 0;
        if |sums| > 0 {

            return sums[0];
        } 
        return -1;
    }

    method problem0_2(input: string) returns (x: int)
    {
        var data := parseInput(input);
        var sums: seq<int> := MergeSortBy(
            (x,y) => x >= y,
            Map((items) => FoldLeft((x,y) => x+y, 0, items), data)
        );
        //assume |sums| > 0;
        if |sums| > 2 {
            return sums[0]+ sums[1]+ sums[2];
        } 
        return -1;
    }
}