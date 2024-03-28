Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import graph.
Require Import vertex.
Require Import algorithm_fw.
Require Import algorithm_tarjan.

Module algorithm_purdom.

(* Purdom's Algorithm *)
Fixpoint purdom (g : graph) : list (list bool) := 
  let sccs := find_sccs g in
  let cg := condense_graph g sccs in
  let tc := transitive_closure cg in 
  fold_left (fun acc scc => dfs_expand g acc scc) sccs tc
end.

Theorem purdom_correctness : forall (g : graph) (u v : vertex),
    reachable g u v ->  (* If u is reachable from v in the original graph *)
    reachable (purdom g) u v  (* Then u is reachable from v in the result of Purdom's algorithm *)
end.
Proof. Admitted.


End algorithm_purdom.