Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

(* Define a vertex wrapper around nat. *)
Structure V := mkV { unV : nat }.

(* Define a generic graph by parameterizing it with an adjacency function. *)
Structure Graph := mkGraph {
  adjacency : V -> V -> bool
}.

(* Prove that any adjacency defined in this generic graph is decidable. *)
Lemma graph_decidable : forall g : Graph, forall x y : V, {adjacency g x y = true} + {adjacency g x y = false}.
Proof.
  intros g x y.
  destruct (adjacency g x y) eqn:E.
  - left; reflexivity.
  - right; reflexivity.
Qed.

Fixpoint find_index (v : V) (vs : list V) (current_index : nat) : nat :=
  match vs with
  | [] => current_index
  | h :: t => if (unV v =? unV h) then current_index else find_index v t (S current_index)
  end.

Definition nth_bool (l : list bool) (n : nat) : bool :=
  nth n l false.