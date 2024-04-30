Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Import ListNotations.


Definition is_even (n : nat) : Prop := exists k : nat, n = 2 * k.

(* A structure to represent the necklace problem *)
Structure necklace_problem := {
  m : nat;                            (* Total number of elements *)
  subsets : list (list nat)           (* List of subsets *)
}.

(* A structure for the solution, which is a binary sequence *)
Structure solution := {
  binary_seq : list bool              (* The binary sequence *)
}.

(* To ensure all subsets are non-empty and have an even number of elements *)
Definition even_subset (s : list nat) : Prop := is_even (length s).

(* Ensure the union of all subsets is exactly {0, 1, ..., m-1} *)
Definition valid_union (m : nat) (subs : list (list nat)) : Prop :=
  forall x : nat, x < m <-> (exists l, In l subs /\ In x l).

(* Ensure all subsets are disjoint *)
Definition disjoint_subsets (subs : list (list nat)) : Prop :=
  forall l1 l2 : list nat, In l1 subs -> In l2 subs -> l1 <> l2 -> 
  forall x : nat, ~ (In x l1 /\ In x l2).

(* Count transitions in the binary sequence *)
Fixpoint transition_count (seq : list bool) : nat :=
  match seq with
  | [] | [_] => 0
  | b1 :: (b2 :: rest as tail) => 
      (if Bool.eqb b1 b2 then 0 else 1) + transition_count tail
  end.

(* Check if a given instance of the necklace problem is valid *)

Definition instance_even (np : necklace_problem) : Prop :=
  forall Si : list nat, In Si np.(subsets) -> even_subset Si.

Definition instance_union (np : necklace_problem) : Prop :=
  valid_union np.(m) np.(subsets).

Definition instance_disjoint (np : necklace_problem) : Prop :=
  disjoint_subsets np.(subsets).

Definition valid_instance (np : necklace_problem) : Prop :=
  instance_even np /\ instance_union np /\ instance_disjoint np.


Definition valid_solution_partition (np : necklace_problem) (sol : solution) : Prop :=
  forall s : list nat, In s (subsets np) ->
    let half_sum := fold_right Nat.add 0 (map (fun i => if nth i (binary_seq sol) false then 1 else 0) s)
    in half_sum = length s / 2.

(* Check if a given solution is valid for a given necklace problem *)
Definition valid_solution (np : necklace_problem) (sol : solution) : Prop :=
  valid_solution_partition np sol /\ length (binary_seq sol) = np.(m).


(* Generate a specific instance of the necklace problem *)
Definition generate_necklace_instance (n : nat) : necklace_problem :=
  {| m := 2 * n; subsets := map (fun k => [2 * k; 2 * k + 1]) (seq 0 n) |}.


Lemma check_instance_even : forall n,
  let np := generate_necklace_instance (n) in 
  instance_even np.
Proof.
    intros n.
    intros Si.
    intros np.
    unfold generate_necklace_instance.
    intros.
    unfold generate_necklace_instance in H.
    unfold even_subset.
    unfold is_even.
    exists 1.
    simpl in H.
    simpl.
    apply in_map_iff in H.
    destruct H as [k [H1 H2]].
    inversion H1.
    subst.
    simpl.
    auto.
Qed.

Lemma check_instance_union : forall n,
  let np := generate_necklace_instance (n) in 
  instance_union np.
Admitted.



Lemma check_instance_disjoint : forall n,
  let np := generate_necklace_instance n in instance_disjoint np.
Proof.
  intros n.
  unfold disjoint_subsets, generate_necklace_instance.
  simpl.
  intros l1 l2 H1 H2 H3 x H4.
  apply in_map_iff in H1, H2.
  destruct H1 as [k1 [Hk11 Hk12]], H2 as [k2 [Hk21 Hk22]].
  inversion Hk11; inversion Hk21; subst.
  destruct H4.
  simpl in H1.
  simpl in H2.
  assert (k1 = k2).
  destruct H1 as [H1even | H1odd];
  destruct H2 as [H2even | H2odd];
  try rewrite H1even in H2even;
  try rewrite H1even in H2odd;
  try rewrite H1odd in H2even;
  try rewrite H1odd in H2odd;
  auto;
  try contradiction;
  try lia.
  assert (k1 = k2) by lia; subst.
  contradiction H3; reflexivity.
Qed.

Lemma check_valid_instance : forall n,
  let np := generate_necklace_instance n in valid_instance np.
Proof.
  intros n.
  unfold valid_instance.
  split.
  - apply check_instance_even.
  - split.
    + apply check_instance_union.
    + apply check_instance_disjoint.
Qed.


(* maybe not very useful ...*)
Lemma valid_solution_requires_transitions_per_k :
  forall n, let np := generate_necklace_instance n in
            forall sol : solution, forall k : nat,
              valid_solution np sol -> In k (seq 0 n) -> (nth (2*k) sol.(binary_seq)) <> (nth (2*k+1) sol.(binary_seq)).
Proof.
Admitted.


(* Theorem: Any valid solution for the specific instance must have at least n transitions *)
Theorem valid_solution_requires_transitions :
  forall n, let np := generate_necklace_instance n in
            forall sol : solution,
              valid_solution np sol -> transition_count (binary_seq sol) >= n.
Proof.
  intros n.
  intros np.
  intros sol.
  intros H.
  unfold transition_count.
  destruct binary_seq.
  - unfold valid_solution in H.
    split H.

Admitted.




