include "../../parser/split.dfy"
include "./matrix.dfy"
module Problem4 {
    import opened Split
    import opened Matrix

    method ParseInput(input: string) returns (ss: Matrix<char>) 
        ensures isMatrix(ss)
    {
        var data := splitOnBreak(input);
        expect |data| > 0;
        assume {:axiom} |data| > 0;
        var width := |data[0]|;
        expect width > 0;
        assume {:axiom} width > 0;
        var rows: seq<seq<char>> := [];
        for i := 0 to |data| 
            invariant forall row :: row in rows ==> |row| == width

        {
            if data[i] != "" {
                expect |data[i]| == width;
                assume {:axiom} |data[i]| == width;
                rows := rows + [data[i]];
            }
        }
        // print "Rows: ", rows, "\n";
        expect |rows| > 0;
        assert |rows| > 0;
        ss := Matrice(rows, |rows|, width);
    }

    function countWords(s: string, ss: seq<char>): int 
        requires |s| > 0
        decreases |ss|
    {
        if |ss| < |s| then 0 else if s <= ss then 1 + countWords(s, ss[|s|..]) else countWords(s, ss[1..])
    }

    method CountDiagonalWords(s: string, m: Matrix<char>, y: nat, x: nat) returns (count: int)
        requires isMatrix(m)
    {
        var matches := true;
        for i := 0 to |s|
        {
            if y + i < m.rows && x + i < m.columns {
                if s[i] != m.vals[y + i][x + i] {
                    matches := false;
                    break;
                }
            }else{
                matches := false;
                break;
            }
        }
        return if matches then 1 else 0;
    }

    method countWordsDiagonalLeft(s: string, m: Matrix<char>, y: nat, x: nat) returns (count: int)
        requires isMatrix(m)
    {
        var matches := true;
        for i := 0 to |s|
        {
            if 0 <= y + i < m.rows &&  0 <= x - i < m.columns {
                if s[i] != m.vals[y + i][x - i] {
                    matches := false;
                    break;
                }
            }else{
                matches := false;
                break;
            }
        }
        return if matches then 1 else 0;
    }

    method countWordsTest1() {
        var data := ['M', 'M', 'M', 'S', 'X', 'X', 'M', 'A', 'S', 'M'];
        expect countWords("XMAS", data) == 1;
    }

    method problem4_1(input: string) returns (x: int) {
        var data := ParseInput(input);
        var transposed := seqTranspose(data);
        var xmas := 0;
        var samx := 0;
        for i := 0 to data.rows
            invariant 0 <= i <= data.rows
        {
            xmas := xmas + countWords("XMAS", data.vals[i]);
            samx := samx + countWords("SAMX", data.vals[i]);
        }
        for i := 0 to transposed.rows
            invariant 0 <= i <= transposed.rows
        {
            xmas := xmas + countWords("XMAS", transposed.vals[i]);
            samx := samx + countWords("SAMX", transposed.vals[i]);
        }

        for i := 0 to data.rows
            invariant 0 <= i <= data.rows
        {
            for j := 0 to data.columns
                invariant 0 <= j <= data.columns
            {
                var dxmas := CountDiagonalWords("XMAS", data, i, j);
                var dsamx := CountDiagonalWords("SAMX", data, i, j);
                var dlxmas := countWordsDiagonalLeft("XMAS", data, i, j);
                var dlsamx := countWordsDiagonalLeft("SAMX", data, i, j);
                // print i, " ", j, " Diagonal: ", dxmas, " ", dsamx, " ", dlxmas, " ", dlsamx, "\n";
                xmas := xmas + dxmas + dlxmas;
                samx := samx + dsamx + dlsamx;
            }
        }

        return xmas + samx;
    }

    method problem4_2(input: string) returns (x: int) {
        var data := ParseInput(input);
        expect data.rows > 1;
        expect data.columns > 1;
        x := 0;

        for i := 0 to data.rows-2
            invariant 0 <= i <= data.rows-2
        {
            for j := 0 to data.columns -2
                invariant 0 <= j <= data.columns-2
            {
                var dxmas := CountDiagonalWords("MAS", data, i, j);
                var dsamx := CountDiagonalWords("SAM", data, i, j);
                var dlxmas := countWordsDiagonalLeft("MAS", data, i, j+2);
                var dlsamx := countWordsDiagonalLeft("SAM", data, i, j+2);
                if dxmas + dsamx + dlxmas + dlsamx > 1 {
                    x := x + 1;
                }
            }
        }
    }
}
