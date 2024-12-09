include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem9 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq

    method parseInput(input: string) returns (data: seq<int>) 
        ensures |data| > 0
        ensures forall x :: x in data ==> x >= 0
    {
        var lines := splitOnBreak(input);
        expect |lines| == 2;
        data := Map(Integer, split(lines[0], ""));
        expect |data| > 0;
        expect forall x :: x in data ==> x >= 0;
    }

    function sum(x: seq<int>): int
    {
        if |x| == 0 then 0 else x[0] + sum(x[1..])
    }

    lemma sumConcat(x: seq<int>, y: seq<int>)
        ensures sum(x + y) == sum(x) + sum(y)
    {
        if |x| == 0 {
            assert x + y == y;
            assert sum(x + y) == sum(y);
        }else{
            assert x == [x[0]] + x[1..];
            assert x + y == [x[0]] + x[1..] + y;
            // assert sum(x + y) == x[0] + sum(x[1..] + y);
            sumConcat(x[1..], y);
            assert sum(x) == x[0] + sum(x[1..]);
            assert sum(x[1..] + y) == sum(x[1..]) + sum(y);
            assert sum(x + y) == (x+y)[0] + sum((x+y)[1..]);
            assert (x+y)[1..]   == x[1..] + y;
            // assert sum(x + y) == sum(x) + sum(y);
        }
    }

    lemma sumNatsNat(xs: seq<int>)
        requires forall x :: x in xs ==> x >= 0
        ensures 0 <= sum(xs)
    {
        if |xs| == 0 {
            assert sum(xs) == 0;
            assert 0 <= sum(xs);
        }else{
            assert xs == [xs[0]] + xs[1..];
            assert xs[0] in xs;
            assert forall x :: x in xs[1..] ==> x in xs;
            sumNatsNat(xs[1..]);
        }
    }
    lemma sumNats(xs: seq<int>, i: int)
        requires forall x :: x in xs ==> x >= 0
        requires 0 <= i <= |xs|
        requires |xs| > 0
        ensures sum(xs[..i]) <= sum(xs)
    {
        sumNatsNat(xs);
        if i == 0 {
            assert sum(xs[..i]) == 0;
            // assert sum(xs) == xs[0];
            assert forall x :: x in xs[..i] ==> x in xs;
            assert sum(xs[..i]) <= sum(xs);
        }else{
            sumNats(xs, i-1);
            assert xs[..i] == xs[..i-1] + [xs[i-1]];
            sumConcat(xs[..i-1], [xs[i-1]]);
            assert xs[i-1] in xs;
            sumNatsNat([xs[i-1]]);
            assert forall x :: x in xs[..i] ==> x in xs;
            assert forall x :: x in xs[i..] ==> x in xs;
            // assert sum(xs[..i]) == sum(xs[..i-1]) + xs[i];
            assert sum(xs[..i-1]) <= sum(xs[..i]);
            assert xs == xs[..i] + xs[i..];
            sumNatsNat(xs[i..]);
            sumConcat(xs[..i], xs[i..]);
            assert sum(xs[..i]) <= sum(xs);
        }
    }
    datatype File = File(id: int, start: nat, length: nat)
    datatype Empty = Empty(start: nat, length: nat)
    method ExpandDrive(data: seq<int>) returns (drive: array<int>, empty: seq<(nat, nat)>, files: seq<(int, nat, nat)>)
        requires |data| > 0
        requires forall x :: x in data ==> x >= 0
        ensures fresh(drive)
    {
        var length := sum(data);
        expect length > 0;
        drive := new int[length];
        empty := [];
        files := [];
        var x := 0;
        var id := 0;
        for i := 0 to |data|
            invariant sum(data[..i]) == x
            invariant 0 <= x <= length

        {
            sumNats(data, i+1);
            if i % 2 == 0 {
                expect data[i] > 0;
                expect x < length;
                assert data == data[..i] + [data[i]] + data[i+1..];
                sumConcat(data[..i], [data[i]]);
                sumConcat(data[..i]+[data[i]], data[i+1..]);

                for j := 0 to data[i] 
                {
                    drive[x+j] := id;
                }
                assert data[..i+1] == data[..i] + [data[i]];
                files := files + [(id, x as nat, data[i] as nat)];
                sumConcat(data[..i], [data[i]]);
                x := x + data[i];
                id := id + 1;
            }else{
                if data[i] != 0 {
                    assert data[i] in data;
                    empty := empty + [(x as nat, data[i] as nat)];
                    sumConcat(data[..i], [data[i]]);
                    assert data[..i+1] == data[..i] + [data[i]];
                    for j := 0 to data[i] 
                    {
                        drive[x+j] := -1;
                    }
                    x := x + data[i];
                }else {
                    sumConcat(data[..i], [data[i]]);
                    assert data[..i+1] == data[..i] + [data[i]];
                    x := x + data[i];
                    assert x == sum(data[..i+1]);
                }
            }
        }
    }

    method printDrive(drive: array<int>)
    {
        for i := 0 to drive.Length
        {
            if drive[i] != -1 {
                print drive[i],",";
            }else{
                print ".";
            }
        }
        print "\n";
    }

    method checksumDrive(drive: array<int>) returns (x: int)
    {
        x := 0;
        for i := 0 to drive.Length
        {
            if drive[i] != -1 {
                x := x + drive[i]*i;
            }
        }
    }

    method problem9_1(input: string) returns (x: int) 
    {
        var data := parseInput(input);
        var drive, empty, files := ExpandDrive(data);
        // printDrive(drive);
        print |empty|, "\n";
        print |files|, "\n";
        while |empty| > 1 && |files| > 0
            decreases |empty| + |files|
        {
            // printDrive(drive);
            // print empty, " ", files, "\n";
            var lastFile := files[|files|-1];
            var firstEmpty := empty[0];
            if lastFile.2 < firstEmpty.1 {
                for i := 0 to lastFile.2
                {
                    expect 0 <= firstEmpty.0+i < drive.Length, "firstEmpty.0+i >= drive.Length: ";
                    drive[firstEmpty.0+i] := lastFile.0;
                    expect 0 <= lastFile.1+i < drive.Length, "lastFile.1+i >= drive.Length: ";
                    drive[lastFile.1+i] := -1;
                }
                empty := [(firstEmpty.0+lastFile.2, firstEmpty.1-lastFile.2)]+empty[1..];
                files := files[..|files|-1];
                if empty[|empty|-1].0 < lastFile.1 {
                    empty := empty + [(lastFile.1, lastFile.2)];
                }else{
                    if |empty| > 1 && empty[|empty|-2].0 + empty[|empty|-2].1 == lastFile.1 {
                        empty := empty[..|empty|-2] + [(empty[|empty|-2].0, empty[|empty|-2].1 + lastFile.2 + empty[|empty|-1].1)];
                    }else{
                        empty := empty[..|empty|-1] + [(lastFile.1, lastFile.2 + empty[|empty|-1].1)];
                    }
                }
            } else if lastFile.2 == firstEmpty.1 {
                for i := 0 to lastFile.2
                {
                    expect 0 <= firstEmpty.0+i < drive.Length, "firstEmpty.0+i >= drive.Length: ";
                    drive[firstEmpty.0+i] := lastFile.0;
                    expect 0 <= lastFile.1+i < drive.Length, "lastFile.1+i >= drive.Length: ";
                    drive[lastFile.1+i] := -1;
                }

                empty := empty[1..];
                files := files[..|files|-1];
                if empty[|empty|-1].0 < lastFile.1 {
                    empty := empty + [(lastFile.1, lastFile.2)];
                }else{
                    if |empty| > 1 && empty[|empty|-2].0 + empty[|empty|-2].1 == lastFile.1 {
                        empty := empty[..|empty|-2] + [(empty[|empty|-2].0, empty[|empty|-2].1 + lastFile.2 + empty[|empty|-1].1)];
                    }else{
                        empty := empty[..|empty|-1] + [(lastFile.1, lastFile.2 + empty[|empty|-1].1)];
                    }
                }
            } else {
                var newFile := (lastFile.0, lastFile.1, lastFile.2 - firstEmpty.1);
                for i := 0 to firstEmpty.1
                {
                    expect 0 <= firstEmpty.0+i < drive.Length, "firstEmpty.0+i >= drive.Length: ";
                    drive[firstEmpty.0+i] := lastFile.0;
                    expect 0 <= lastFile.1+lastFile.2-(i+1) < drive.Length, "lastFile.1+lastFile.2-(i+1) >= drive.Length: ";
                    drive[lastFile.1+lastFile.2-(i+1)] := -1;
                }
                files := files[..|files|-1] + [newFile];
                empty := empty[1..];
            }
            // expect multiset(drive[..]) == multiset(old(drive)[..]);
        }
        // printDrive(drive);
        x := checksumDrive(drive);
    }

    method problem9_2(input: string) returns (x: int) {
        return 4;
    }
}
