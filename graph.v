Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module graph.

Definition andb_list (l : list bool) : bool :=
  fold_right andb true l.

Definition orb_list (l : list bool) : bool :=
  fold_right orb false l.

Definition dot_product (a b : list bool) : bool :=
  orb_list (map (fun ab => andb (fst ab) (snd ab)) (combine a b)).

Definition get_column (m : list (list bool)) (i : nat) : list bool :=
  map (fun row => nth i row false) m.

Definition bool_matrix_mult (m1 m2 : list (list bool)) : list (list bool) :=
  map (fun row =>
         map (fun i => dot_product row (get_column m2 i))
             (seq 0 (length (hd [] m2)))) m1.

Definition bool_matrix_square (m : list (list bool)) : list (list bool) :=
  bool_matrix_mult m m.

Definition example_matrix : list (list bool) := 
  [[true; false; false];
   [false; true; false];
   [false; false; true]].

Definition example_matrix_squared := bool_matrix_square example_matrix.

Eval compute in example_matrix_squared.

End graph.
