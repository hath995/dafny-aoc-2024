include "../../parser/split.dfy"
module Problem6 {
    import opened Split
    import opened Std.Collections.Seq
    method parseInput(input: string) returns (obstacles: set<(int, int)>, start: (int, int), dim: (nat, nat)) 
    {
        start := (0, 0);
        obstacles := {};
        var lines := splitOnBreak(input);
        for y := 0 to |lines| 
        {
            if lines[y] != "" {
                for x := 0 to |lines[y]| 
                {
                    if lines[y][x] == '#' {
                        obstacles := obstacles + {(x, y)};
                    }else if lines[y][x] == '^' {
                        start := (x, y);
                    }
                }
            }
        }
        expect |lines| > 0;
        dim := (|lines[0]|, |lines|-1);
    }

    datatype Direction = Up | Down | Left | Right
    function TurnRight(d: Direction): Direction 
    {
        match d {
            case Up => Right
            case Down => Left
            case Left => Up
            case Right => Down
        }
    }

    function step(d: Direction, p: (int, int)): (int, int) 
    {
        match d {
            case Up => (p.0, p.1 - 1)
            case Down => (p.0, p.1 + 1)
            case Left => (p.0 - 1, p.1)
            case Right => (p.0 + 1, p.1)
        }
    }

    predicate InBounds(p: (int, int), dim: (nat, nat)) 
    {
        0 <= p.0 < dim.0 && 0 <= p.1 < dim.1
    }

    method IsLoop(start: (int, int), obstacles: set<(int, int)>, dim: (nat, nat)) returns (b: bool)
        decreases *
    {
        var visited: set<(Direction, (int, int))> := {(Up, start)};
        var curr := start;
        var dir := Up;
        while InBounds(curr, dim)
            decreases *
        {
            visited := visited + {(dir, curr)};
            var next := step(dir, curr);
            while next in obstacles 
                decreases *
            {
                dir := TurnRight(dir);
                next := step(dir, curr);
            }
            if (dir, next) in visited {
                b := true;
                return;
            }
            curr := next;
        }
        b := false;
    }

    method problem6_1(input: string) returns (x: int) 
        decreases *
    {
        var obstacles, start, dim := parseInput(input);
        x := 0;
        var visited := {start};
        var curr := start;
        var dir := Up;
        while InBounds(curr, dim)
            decreases *
        {
            visited := visited + {curr};
            var next := step(dir, curr);
            while next in obstacles 
                decreases *
            {
                dir := TurnRight(dir);
                next := step(dir, curr);
            }
            curr := next;
        }
        x := |visited|;
    }

    method problem6_2(input: string) returns (x: int) 
        decreases *
    {
        var obstacles, start, dim := parseInput(input);
        var visited := {start};
        var curr := start;
        var dir := Up;
        x := 0;
        while InBounds(curr, dim)
            decreases *
        {
            visited := visited + {curr};
            var next := step(dir, curr);
            while next in obstacles 
                decreases *
            {
                dir := TurnRight(dir);
                next := step(dir, curr);
            }
            curr := next;
        }
        var vs := SetToSeq(visited);
        var newobs: set<(int, int)> := {};
        while vs != []
            decreases |vs|
        {
            var curr := vs[0];
            if curr == start {
                vs := vs[1..];
                continue;
            }
            var loop := IsLoop(start, obstacles+{curr}, dim);
            if loop {
                newobs := newobs + {curr};
            }
            vs := vs[1..];
        }
        x := |newobs|;
    }
}
