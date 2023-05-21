Require Import List.

(* Define a node as a natural number. *)
Definition Node := nat.

(* Define a graph as a function that maps nodes to lists of adjacent nodes. *)
Definition Graph := Node -> list Node.

(* An empty graph has no edges for any node. *)
Definition empty_graph : Graph := fun _ => nil.

(* Add an edge between two nodes in the graph. *)
Definition add_edge (g : Graph) (n1 n2 : Node) : Graph :=
  fun n =>
    if n =? n1
    then n2 :: g n
    else g n.

(* Check if there is an edge between two nodes in the graph. *)
Definition has_edge (g : Graph) (n1 n2 : Node) : bool :=
  List.exists (Nat.eqb n2) (g n1).

(* Example: Create a graph with two edges. *)
Definition example_graph : Graph :=
  add_edge (add_edge empty_graph 1 2) 2 3.

(* Check if there's an edge from 1 to 2 in the example graph. *)
Example example_has_edge : has_edge example_graph 1 2 = true.
Proof. reflexivity. Qed.
