
//based on https://swtch.com/~rsc/regexp/regexp1.html
// include "../libraries/src/Wrappers.dfy"
module RegEx {
    import opened Std.Wrappers
    datatype RegexPiece = Char(value: char) | GroupStart(id: nat) | GroupEnd(id: nat) | Plus | Star | Optional | Alt | Concat | WildChar
    datatype Paren = Paren(natom: int, nalt: int)
    function RegToChar(re: RegexPiece): char {
        match re {
            case Char(value) => value
            case GroupStart(id) => '('
            case GroupEnd(id) => ')'
            case Alt => '|'
            case Optional => '?'
            case Plus => '+'
            case Star => '*'
            case Concat => '⊕'
            case Wild => '.'
        }
    }

    method re2post(re: string) returns (res: Result<seq<RegexPiece>, string>) {
        var buf := [];
        var nalt := 0;
        var natom := 0;
        var groupid := 1;
        var groups: seq<nat> := [];
        var parens: seq<Paren> :=[];
        var escape := false;
        var inCharacterClass := false;
        for i := 0 to |re| 
            invariant |groups| == |parens|
        {
            // print "char -> ";
            // print re[i];
            // print "\n";
            if escape {
                escape := false;
                if natom > 1 {
                    natom := natom -1;
                    buf := buf + [Concat];
                }
                buf := buf + [Char(re[i])];
                natom := natom + 1;
                continue;
            }
            match re[i] {
                case '.' => {
                    if natom > 1 {
                        natom := natom -1;
                        buf := buf + [Concat];
                    }
                    buf := buf + [WildChar];
                    natom := natom + 1;
                }
                case '[' => {
                    print "Character class begin ", i, "\n";
                    inCharacterClass := true;
                }

                case ']' => {
                    print "Character class end ", i, "\n";
                    inCharacterClass := false;
                }
                case '(' => {
                    if natom > 1 {
                        natom := natom -1;
                        buf := buf + [Concat];
                    }
                    parens := parens + [Paren(natom, nalt)];
                    buf := buf + [GroupStart(groupid)];
                    groups := groups + [groupid];
                    groupid := groupid + 1;
                    nalt := 0;
                    natom := 0;
                }
                case '|' => {
                    if natom == 0 {
                        return Failure("Missing atom");
                    }
                    natom := natom - 1;
                    while natom > 0 {
                        buf := buf + [Concat];
                        natom := natom - 1;
                    }
                    nalt := nalt + 1;
                }
                case ')' => {
                    if |parens| == 0 || |groups| == 0 || natom == 0 {
                        return Failure("missing atom or paren");
                    }
                    natom := natom - 1;
                    while natom > 0 {
                        buf := buf + [Concat];
                        natom := natom - 1;
                    }
                    while nalt > 0 {
                        buf := buf + [Alt];
                        nalt := nalt - 1;
                    }
                    var next := parens[|parens|-1];
                    nalt := next.nalt;
                    natom := next.natom;
                    parens := parens[0..|parens|-1];
                    natom := natom + 1;
                    assume {:axiom} |groups| > 0;
                    buf := buf + [GroupEnd(groups[|groups|-1])];
                    groups := groups[0..|groups|-1];
                    // print "nalt: ";
                    // print nalt;
                    // print " natom: ";
                    // print natom;
                    // print "\n";
                }
                case '*' => {
                    if natom == 0 {
                        return Failure("Missing atom");
                    }
                    buf := buf + [Star];
                }
                case '+' => {
                    if natom == 0 {
                        return Failure("Missing atom");
                    }
                    buf := buf + [Plus];
                }
                case '?' => {
                    if natom == 0 {
                        return Failure("Missing atom");
                    }
                    buf := buf + [Optional];
                }
                case '\\' => {
                    escape := true;
                }
                case _ => {
                    if natom > 1 {
                        natom := natom -1;
                        buf := buf + [Concat];
                    }
                    buf := buf + [Char(re[i])];
                    natom := natom + 1;
                }
            }
        }
        if |parens| != 0 {
            return Failure("Missing )");
        }
        natom := natom - 1;
        while natom > 0 {
            buf := buf + [Concat];
            natom := natom - 1;
        }
        while nalt > 0 {
            buf := buf + [Alt];
            nalt := nalt - 1;
        }
        return Success(buf);
    }

    datatype MatchKind = Split | Match | Wild | MatchChar(c: char) {
        function GetChar(): char
            requires MatchChar?
        {
            c
        }
    }
    class State {
        ghost var repr : set<object>
        var id: nat
        var c: MatchKind
        var negated: bool
        var out: State?
        var out1: State?
        var lastlist: nat
        var groups: set<nat>
        var origin: RegexPiece

        constructor(id: nat, c: MatchKind, out: State?, out1: State?, negated: bool) 
            ensures this.id == id
            ensures this.c == c
            ensures this.out == out
            ensures this.out1 == out1
            ensures this.negated == negated
            ensures this.groups == {}
        {
            this.id := id;
            this.c := c;
            this.out := out;
            this.out1 := out1;
            this.negated := negated;
            this.groups := {};

        }
        
        ghost predicate Valid() 
            reads this, repr, out, out1
            decreases repr
        {
            this in repr &&
            (this.out != null ==> this !in this.out.repr && this.out.repr <= repr) &&
            (this.out1 != null ==> this !in this.out1.repr && this.out1.repr <= repr) &&
            (this.out != null && this.out1 != null ==> this.out1.repr !! this.out.repr)

        }
    }
    
    datatype StateUpdate = Out(out: State) | Out1(out: State)
    datatype FragC = FragC(start: State, out: seq<StateUpdate>)

    class Frag {
        ghost var repr: set<object>
        var start: State
        var out: array<StateUpdate>

        constructor(start: State, out: array<StateUpdate>)
            ensures this.start == start 
            ensures this.out == out 
        {
            this.start := start;
            this.out := out;
        }

        // ghost predicate Valid()
        //     reads this, repr, out
        // {
        //     this in repr &&
        //     start in repr &&
        //     forall i :: 0 <= i < out.Length ==> OutSet(out[i]) in repr
        // }
    }

    // method pop<T>(stack: seq<T>) returns (e: T)
    //     requires |stack| > 0
    // {
    //     e := stack[|stack|-1];
    //     stack:=stack[..|stack|-1];
    // }
    function OutSet(ls: StateUpdate): State {
        match ls {
            case Out(out) => out
            case Out1(out1) => out1
        }
    }

    function sout(s: State): State? 
        reads s, s.out
    {
        s.out
    }

    function lout(s: State): State? 
        reads s, s.out1
    {
        s.out1
    }


    // method patch(l: Frag, s: Frag)
    //     // requires l.Valid()
    //     modifies l.repr
    //     modifies l.out
    //     modifies set i | 0 <= i < |l.out[..]| :: OutSet(l.out[i])
    //     modifies set i | 0 <= i < l.out.Length :: OutSet(l.out[i])
    //     // modifies set i | 0 <= i < l.out.Length :: sout(OutSet(l.out[i]))
    // {
    //     var i:=0;
    //     while i < l.out.Length
    //         invariant 0 <= i <= l.out.Length
    //     {
    //         match l.out[i]
    //         {
    //             case Out(out) => {
    //                 out.out := s.start;
    //             }
    //             case Out1(out) => {
    //                 out.out1 := s.start;
    //             }
    //         }
    //         i := i+1;
    //     }
    // }

    method patch(l: FragC, s: FragC)
        modifies set i | 0 <= i < |l.out| :: OutSet(l.out[i])
    {
        var i:=0;
        while i < |l.out|
            invariant 0 <= i <= |l.out|
        {
            match l.out[i]
            {
                case Out(out) => {
                    out.out := s.start;
                }
                case Out1(out) => {
                    out.out1 := s.start;
                }
            }
            i := i+1;
        }
    }

    method post2nfa(postfix: seq<RegexPiece>) returns (start: State)
        ensures fresh(start)
    {
        expect |postfix| > 0, "postfix seq should contain an element";
        var stack: seq<FragC> := [];
        var groups: map<nat, (nat, nat)> := map[];
        var states: seq<State?> := [];
        var sid := 1;
        for i:=0 to |postfix| 
            invariant forall frag :: frag in stack ==> fresh(frag.start)
            invariant forall state :: state !=null && state in states ==> fresh(state)
            invariant |states| == i
        {
            match postfix[i] {
                case WildChar => {
                    var s := new State(sid, Wild, null, null, false);
                    sid := sid+1;
                    s.origin := postfix[i];
                    states := states +[s];
                    stack := stack +[FragC(s,[Out(s)])];
                }
                case Char(c) => {
                    var s := new State(sid, MatchChar(c), null, null, false);
                    sid := sid+1;
                    s.origin := postfix[i];
                    states := states +[s];
                    stack := stack +[FragC(s,[Out(s)])];
                }
                case GroupStart(id) => {
                    groups := groups[id := (i+1,0)];
                    states := states +[null];
                }
                case GroupEnd(id) => {
                    assume {:axiom} id in groups;
                    expect id in groups, "Group id was not seen before group end";
                    var GroupStart := groups[id];
                    groups := groups[id := (GroupStart.0, i)];
                    states := states +[null];
                    assume {:axiom} GroupStart.0 < i;
                    for j := GroupStart.0 to i 
                    {
                        if(states[j] != null) {
                            assert states[j] in states;
                            states[j].groups := states[j].groups+{id};
                        }
                    }
                }
                case Concat => {
                    // var e2 := pop(stack);
                    assume {:axiom} |stack| > 1;
                    expect |stack| > 1, "stack length was not greater than 1";
                    var e2 := stack[|stack|-1];
                    stack:=stack[..|stack|-1];
                    var e1 := stack[|stack|-1];
                    stack:=stack[..|stack|-1];
                    assume {:axiom} forall i :: 0 <= i < |e1.out| ==>  fresh(OutSet(e1.out[i]));
                    states := states +[null];
                    patch(e1, e2);
                    stack := stack + [FragC(e1.start, e2.out)];
                }
                case Alt => {
                    assume {:axiom} |stack| > 1;
                    expect |stack| > 1, "stack length was not greater than 1";
                    var e2 := stack[|stack|-1];
                    stack:=stack[..|stack|-1];
                    var e1 := stack[|stack|-1];
                    stack:=stack[..|stack|-1];
                    var s := new State(sid, Split, e1.start, e2.start, false);
                    s.origin := postfix[i];
                    states := states+[s];
                    sid := sid+1;
                    stack := stack+[FragC(s, e1.out+e2.out)];
                }
                case Optional => {
                    assume {:axiom} |stack| > 0;
                    expect |stack| > 0, "stack length was not greater than 1";
                    var e1 := stack[|stack|-1];
                    stack:=stack[..|stack|-1];
                    var s := new State(sid, Split, e1.start, null, false);
                    s.origin := postfix[i];
                    states := states+[s];
                    sid := sid+1;
                    stack := stack+[FragC(s, e1.out+[Out1(s)])];
                }
                case Star => {
                    assume {:axiom} |stack| > 0;
                    expect |stack| > 0, "stack length was not greater than 1";
                    var e1 := stack[|stack|-1];
                    stack:=stack[..|stack|-1];
                    var s := new State(sid, Split, e1.start, null, false);
                    s.origin := postfix[i];
                    states := states+[s];
                    sid := sid+1;
                    assume {:axiom} forall i :: 0 <= i < |e1.out| ==>  fresh(OutSet(e1.out[i]));
                    patch(e1, FragC(s,[]));
                    stack := stack + [FragC(s, [Out1(s)])];
                }
                case Plus => {
                    assume {:axiom} |stack| > 0;
                    expect |stack| > 0, "stack length was not greater than 1";
                    var e1 := stack[|stack|-1];
                    stack:=stack[..|stack|-1];
                    var s := new State(sid, Split, e1.start, null, false);
                    s.origin := postfix[i];
                    states := states+[s];
                    sid := sid+1;
                    assume {:axiom} forall i :: 0 <= i < |e1.out| ==>  fresh(OutSet(e1.out[i]));
                    patch(e1, FragC(s, []));
                    stack := stack+[FragC(e1.start, [Out1(s)])];
                }
            }
        }
        assume  {:axiom} |stack| > 0;
        expect |stack| > 0, "stack length was not greater than 1";
        var e := stack[|stack|-1];
        var matchState := new State(sid, Match, null, null, false);
        assume  {:axiom} forall i :: 0 <= i < |e.out| ==>  fresh(OutSet(e.out[i]));
        patch(e, FragC(matchState, []));
        return e.start;
    }

    method addstate(l: seq<State>, s: State?) returns (res: Result<seq<State>, string>)
        decreases *
    {
        if s == null {
            return Failure("Added state was null");
        } else if s!=null && s.c.Split? {
            var next := addstate(l, s.out);
            if next.Success? {
                res := addstate(next.Extract(), s.out1);
            }else{
                res := next;
            }
            
        } else {
            return Success(l+[s]);
        }
    }

    type GroupCapture = map<nat, (nat,nat)>

    method step(clist: seq<State>, c: char, i: int, groupCaptures: GroupCapture, completedGroupCatures: GroupCapture)
        returns (nlist: seq<State>, ngroupCaptures: GroupCapture, ncompletedGroupCatures: GroupCapture )
        requires 0 <=i
        decreases *
    {
        nlist := [];
        ngroupCaptures := groupCaptures;
        ncompletedGroupCatures := completedGroupCatures;
        for j:=0 to |clist| {
            var s := clist[j];
            if s.c.Wild? || (s.c.MatchChar? && s.c.c == c) {
                var next := addstate(nlist, s.out);
                if next.Success? {
                    nlist := next.Extract();
                }
                var groups: set<nat> := {};
                while s.groups-groups != {} {
                    var g :| g in s.groups-groups;
                    if g !in ngroupCaptures {
                        ngroupCaptures := ngroupCaptures[g := (i as nat,0)];
                    }
                    groups := groups + {g};
                }
                if s.out != null {
                    var ngroups: set<nat> := {};
                    var soutgroups:=s.out.groups-s.groups;
                    while soutgroups - ngroups != {}
                        // decreases soutgroups - ngroups
                    {
                        var g :| g in soutgroups-ngroups;
                        if g in ngroupCaptures {
                            ngroupCaptures:=ngroupCaptures[g := (i+1, 0)];
                        }
                        ngroups := ngroups + {g};
                    }

                    var nsgroups: set<nat> := {};
                    var sgroups:=s.groups-s.out.groups;
                    while sgroups - nsgroups != {}
                        // decreases soutgroups - ngroups
                    {
                        var g :| g in sgroups-nsgroups;
                        if g in ngroupCaptures {
                            ngroupCaptures:=ngroupCaptures[g := (ngroupCaptures[g].0, i+1)];
                            ncompletedGroupCatures := ncompletedGroupCatures[g := ngroupCaptures[g]];
                        }
                        nsgroups := nsgroups + {g};
                    }

                    if s.out.c.Split? && s.out.out != null {
                        var ngroups: set<nat> := {};
                        var soutgroups:=s.out.out.groups-s.out.groups;
                        while soutgroups - ngroups != {}
                            // decreases soutgroups - ngroups
                        {
                            var g :| g in soutgroups-ngroups;
                            if g in ngroupCaptures {
                                ngroupCaptures := ngroupCaptures[g := (i+1, 0)];
                            }
                            ngroups := ngroups + {g};
                        }

                        var nsgroups: set<nat> := {};
                        var sgroups:=s.out.groups-s.out.out.groups;
                        while sgroups - nsgroups != {}
                            // decreases soutgroups - ngroups
                        {
                            var g :| g in sgroups-nsgroups;
                            if g in ngroupCaptures {
                                ngroupCaptures:=ngroupCaptures[g := (ngroupCaptures[g].0, i+1)];
                                ncompletedGroupCatures := ncompletedGroupCatures[g := ngroupCaptures[g]];
                            }
                            nsgroups := nsgroups + {g};
                        }
                    }

                    if s.out.c.Split? && s.out.out1 != null {
                        var ngroups: set<nat> := {};
                        var soutgroups:=s.out.out1.groups-s.out.groups;
                        while soutgroups - ngroups != {}
                            // decreases soutgroups - ngroups
                        {
                            var g :| g in soutgroups-ngroups;
                            if g in ngroupCaptures {
                                ngroupCaptures := ngroupCaptures[g := (i+1, 0)];
                            }
                            ngroups := ngroups + {g};
                        }

                        var nsgroups: set<nat> := {};
                        var sgroups:=s.out.groups-s.out.out1.groups;
                        while sgroups - nsgroups != {}
                            // decreases soutgroups - ngroups
                        {
                            var g :| g in sgroups-nsgroups;
                            if g in ngroupCaptures {
                                ngroupCaptures:=ngroupCaptures[g := (ngroupCaptures[g].0, i+1)];
                                ncompletedGroupCatures := ncompletedGroupCatures[g := ngroupCaptures[g]];
                            }
                            nsgroups := nsgroups + {g};
                        }
                    }
                }
            }
        }
    }

    function isMatch(clist: seq<State>): bool 
        reads clist
    {
        if |clist| > 0 then if clist[0].c == Match then true else isMatch(clist[1..]) else false
    }

    method execRe(start: State, s: string) returns (matches: bool, captures: seq<string>)
        decreases *
    {
        var groupCaptures: GroupCapture := map[];
        var completedGroupCatures: GroupCapture := map[];
        var groups: set<nat> := {};
        while |start.groups - groups| > 0 
            decreases start.groups - groups
        {
            var g :| g in start.groups - groups;
            groupCaptures := groupCaptures[g := (0,0)];
            groups := groups + {g};
        }
        var clist: seq<State> := [];
        var startList := addstate([], start);
        if startList.Success? {
            clist := startList.Extract();
            for i:=0 to |s| 
            {
                clist, groupCaptures, completedGroupCatures := step(clist, s[i], i, groupCaptures, completedGroupCatures);        
            }
            captures := [];
            for k:= 0 to |completedGroupCatures| {
                assume {:axiom} forall k :: k in completedGroupCatures ==> 0 <= completedGroupCatures[k].0 <= completedGroupCatures[k].1 <= |s|;
                if k in completedGroupCatures {
                    // assert k in completedGroupCatures;
                    captures := captures + [s[completedGroupCatures[k].0..completedGroupCatures[k].1]];
                }
            }
            matches := isMatch(clist);
        }else{
            
            matches := false;
            captures := [];
        }
    }

    method ReMatch(re: string, targetString: string) returns (matches: bool, captures: seq<string>)
        decreases *
    {
        var postfix := re2post(re);
        match postfix {
            case Success(post) => {
                var start := post2nfa([GroupStart(0)]+post+[GroupEnd(0)]);
                matches, captures := execRe(start, targetString);
            }
            case Failure(err) => {
                print err;
                matches := false;
                captures := [];
            }
        }
    }


    method test_re2post() {
        var res := re2post("[abc]");
        expect res.Success?;
        if res.Success? {
            var value := res.Extract();
            print seq(|value|, i requires 0 <= i < |value| => RegToChar(value[i]));
        }
    }

    method test_post2nfa() {

    }
    
    method test_ReMatch() 
        decreases *
    {
        var m, cap := ReMatch("abc","abc");
        expect m == true, "test 1 failed";
        var m1, cap1 := ReMatch("abc","abd");
        expect m1 == false, "test 2 failed";

        var m2, cap2 := ReMatch("a+(b|c)+","aaaccc");
        // print "\nproblem2 ",m2, cap2;
        expect cap2 == [['a','a','a','c','c','c'],['c']];
        expect m2 == true, "test 3 failed";

        var m3, cap3 := ReMatch("a+be*(c|d|f)g", "aabeefg");
        // print "\nproblem3 ",m3, cap3;
        expect m3 == true, "test 4 failed";

        var m4, cap4 := ReMatch("addxy ((0|1|2|3|4|5|6|7|8|9)+),((0|1|2|3|4|5|6|7|8|9)+)","addxy 12,345");
        // print "\nproblem4 ",m4, cap4;
        expect m4 == true, "test 4 failed";

        var m5, cap5 := ReMatch("add(.+)","addxy 12,355");
        print "\nproblem5 ",m5, cap5;
        expect m5 == true, "test 5 failed";
    }

    // method Main() 
    //     decreases *
    // {
    //     // var test := re2post("a(a+be*)(c|(d)|f)g");
    //     // var test := re2post("ac+de?(fg)*");
    //     // print test;
    //     // print "\n";
    //     // match test {
    //     //     case Success(value) => print seq(|value|, i requires 0 <= i < |value| => RegToChar(value[i]));
    //     //     case Failure(err) => print err;
    //     // }
    //     test_re2post();
    //     test_ReMatch();
    // }
    
    export provides ReMatch
}