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

Definition build_row (v : V) (vs : list V) (adj : V -> V -> bool) : list bool :=
  map (adj v) vs.

Definition adj_to_adj_matrix (vs : list V) (adj : V -> V -> bool) : list (list bool) :=
  map (fun v => build_row v vs adj) vs.

Definition adj_matrix_to_adj (m : list (list bool)) (vs : list V) : V -> V -> bool :=
  fun v1 v2 =>
    let idx1 := find_index v1 vs 0 in
    let idx2 := find_index v2 vs 0 in
    match nth_error m idx1 with
    | Some row => nth_bool row idx2
    | None => false
    end.

Theorem adj_to_matrix_to_adj_isomorphic :
  forall (f : V -> V -> bool) (vs : list V),
    forall v1 v2 : V,
      let m := adj_to_adj_matrix vs f in
      let g := adj_matrix_to_adj m vs in
      f v1 v2 = g v1 v2.
Proof.
  intros f vs v1 v2.
  simpl.
  rewrite <- map_nth_error with (f := build_row v1 vs f).
  destruct (nth_error (map (build_row v1 vs f) vs) (find_index v2 vs 0)) as [row |] eqn:H_row.
  - simpl. rewrite nth_error_map. rewrite H_row. simpl. reflexivity.
  - simpl. rewrite nth_error_map. rewrite H_row. simpl. reflexivity.
Qed.

Theorem adj_matrix_to_adj_isomorphic :
  forall (m : list (list bool)) (vs : list V),
    let f := adj_matrix_to_adj m vs in
    let m' := adj_to_adj_matrix vs f in
    m = m'.
Proof.
  intros m vs f m'.
  unfold f, m'.
  apply map_ext_in.
  intros v H_in_vs.
  unfold adj_to_adj_matrix, build_row.

Qed.


