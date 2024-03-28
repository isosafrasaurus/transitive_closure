Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

Require Import graph.

Import ListNotations.

Module vertex.

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
  apply map_ext_in.
  intros u H_in_vs.
  rewrite <- map_nth_error with (f := fun v' => adjacency (mkGraph m') v' u).
  destruct (nth_error (map (fun v' => adjacency (mkGraph m') v' u) vs) (find_index v vs 0)) as [row |] eqn:H_row.
  - simpl. rewrite nth_error_map. rewrite H_row. simpl. reflexivity.
  - simpl. rewrite nth_error_map. rewrite H_row. simpl. reflexivity.
Qed.

Fixpoint reachable (g : Graph) (v1 v2 : V) : bool :=
  match adjacency g v1 v2 with
  | true => true (* Directly connected *)
  | false => orb_list (map (fun v => adjacency g v1 v && reachable g v v2) (list_of_all_vertices_in_g))
  end.

(* Get the i-th row of a boolean matrix *)
Fixpoint get_row (m : list (list bool)) (i : nat) : list bool :=
  match m with
  | [] => []
  | row :: rest => if Nat.eqb i 0 then row else get_row rest (i - 1)
  end.

(* Get the i-th column of a boolean matrix *)
Fixpoint get_column (m : list (list bool)) (i : nat) : list bool :=
  match m with
  | [] => []
  | row :: rest =>
      match row with
      | [] => []
      | b :: bs => if Nat.eqb i 0 then b :: get_column rest i else get_column rest (i - 1)
      end
  end.

(* Boolean dot product of two lists *)
Fixpoint dot_product (l1 l2 : list bool) : bool :=
  match l1, l2 with
  | [], [] => true
  | b1 :: bs1, b2 :: bs2 => b1 && b2 && dot_product bs1 bs2
  | _, _ => false
  end.

(* Matrix multiplication *)
Fixpoint bool_matrix_mult (m1 m2 : list (list bool)) : list (list bool) :=
  match m1 with
  | [] => []
  | row1 :: rest1 =>
      let rec_mult := bool_matrix_mult rest1 m2 in
      match m2 with
      | [] => []
      | row2 :: rest2 =>
          let elem := dot_product row1 row2 in
          elem :: rec_mult
      end
  end.

(* Matrix power *)
Fixpoint bool_matrix_power (m : list (list bool)) (n : nat) : list (list bool) :=
  match n with
  | 0 => identity_matrix
  | S n' => bool_matrix_mult m (bool_matrix_power m n')
  end.

(* Identity matrix with dimension n *)
Fixpoint identity_matrix (n : nat) : list (list bool) :=
  match n with
  | 0 => []
  | S n' => (map (fun _ : nat => false) (seq 0 n)) :: identity_matrix n'
  end.

(* Lemma: matrix_power_preserves_adjacency *)
Lemma matrix_power_preserves_adjacency :
  forall (m : list (list bool)) (u v : nat) (n : nat),
    nth_bool (nth u m v) = true ->
    nth_bool (nth u (bool_matrix_power m n) v) = true.
Proof.
  induction n; simpl.
  - (* Base Case: n = 0 *)
    intros H1. unfold identity_matrix.
    destruct (Nat.eqb u v) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. simpl. apply H1.
    + apply Nat.eqb_neq in Heq. simpl. rewrite Heq. reflexivity.
  - (* Inductive Step: n = S n' *)
    intros. remember (bool_matrix_power m n') as M'.
    simpl. remember (bool_matrix_mult m M') as M''.
    (* Assumptions *)
    assert (H1 : nth_bool (nth u m v) = true). { assumption. }
    assert (Hw : exists w : nat, nth_bool (nth v M' w) = true).
    { (* Prove the existence of w satisfying the condition *)
      destruct (nth_error M' v) as [col_v |] eqn:Hcol_v.
      - exists w. apply nth_error_Some. intro Hn. rewrite Hn in Hcol_v. discriminate.
      - exists 0. simpl. reflexivity.
    }
    (* Goal: nth_bool (nth u M'' v) = true *)
    unfold M''. simpl.
    (* Compute the (u, v) element of bool_matrix_mult explicitly *)
    assert (H_elem : nth_bool (nth u M'' v) = dot_product (get_row m u) (get_column M' v)).
    { (* Prove the assertion about the (u, v) element *)
      unfold bool_matrix_mult. rewrite <- HeqM'. simpl.
      destruct (nth_error M' v) as [col_v |] eqn:Hcol_v.
      - rewrite Hcol_v. apply dot_product_comm.
      - apply nth_error_None in Hcol_v. rewrite Hcol_v. simpl. reflexivity.
    }
    destruct (Nat.eqb u v) eqn:Heq_uv.
    + apply Nat.eqb_eq in Heq_uv. subst. apply H_elem.
    + apply Nat.eqb_neq in Heq_uv. rewrite H_elem.
      destruct (dot_product (get_row m u) (get_column M' v)) eqn:Hdot.
      * reflexivity.
      * exfalso. apply Hw. exists w. assumption.
Qed.

(* A very large number to represent infinity *)
Definition infinity := 1000000. 

End vertex.