
module QuickUnion {


    class QuickUnion {
        var n : nat
        var parent: array<nat>
        var size: array<nat>

        constructor(n: nat) 
            requires n > 0
            ensures this.n == n
            ensures this.parent.Length == this.n
            ensures this.size.Length == this.n
            ensures fresh(this)
            ensures Valid()
        {
            parent := new nat[n];
            size := new nat[n];
            this.n := n;
            new;
            assert parent.Length == n;
            assert size.Length == n;
            forall i | 0 <= i < n {
                parent[i] := i;
            }
            forall i | 0 <= i < n {
                size[i] := 1;
            }
        }

        predicate Valid()
            reads this, parent, size
        {
            this.parent.Length > 0 &&
            this.parent.Length == this.size.Length == this.n &&
            this.parent != this.size &&
            (forall i :: 0 <= i < this.parent.Length ==> 0 <= parent[i] < parent.Length)
            && (forall i :: 0 <= i < this.size.Length ==> this.size[i] > 0)
        }

        method findRoot(x: nat) returns (root: nat)
            requires Valid()
            requires 0 <= x < parent.Length
            ensures 0 <= root < parent.Length
            ensures parent.Length == old(parent.Length)
            ensures Valid()
            modifies parent
            decreases *
        {
            root := x;
            // ghost var all := multiset(parent[..]);
            // ghost var visited: set<nat> := {};
            while root != parent[root]
                invariant Valid()
                invariant 0 <= root < parent.Length
                decreases *
            {
                root := parent[root];
            }
            this.parent[x] := root;
        }

        method connected(x: nat, y: nat) returns (result: bool)
            requires 0 <= x < parent.Length
            requires 0 <= y < parent.Length
            requires Valid()
            decreases *
            modifies parent
            ensures Valid()
        {
            var xroot := this.findRoot(x);
            var yroot := this.findRoot(y);
            result := xroot == yroot;
        }

        method union(x: nat, y: nat)
            requires 0 <= x < parent.Length
            requires 0 <= y < parent.Length
            requires Valid()
            decreases *
            modifies parent, size
            ensures Valid()
        {
            var rootX := findRoot(x);
            var rootY := findRoot(y);
            if rootX != rootY {
                if size[rootX] < size[rootY] {
                    size[rootY] := size[rootY] + size[rootX];
                    parent[rootX] := rootY;
                } else {
                    size[rootX] := size[rootX] + size[rootY];
                    parent[rootY] := rootX;
                }
            }
        }
    }
}