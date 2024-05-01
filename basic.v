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

Definition transition_count_non_recursive (seq : list bool) : nat :=
  let pairs := combine seq (tl seq) in
  let count_transitions (acc : nat) (pair : bool * bool) :=
    let (b1, b2) := pair in
    if Bool.eqb b1 b2 then acc else acc + 1 in
  List.fold_left count_transitions pairs 0.

(* This proof is wrong
Lemma transition_count_equivalence : forall seq, transition_count seq = transition_count_non_recursive seq.
Proof.
  intros seq.
  induction seq as [| b1 [| b2 rest] IH]. simpl; auto.
  - destruct (Bool.eqb b1 b2); simpl; auto.
Qed.
*)

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

Proposition mod_2_contradiction : forall x n, x mod 2 <> S (S n).
Proof.
  intros x n H.   (* Assume x mod 2 = S (S n) for contradiction *)
  assert (Hmod: x mod 2 < 2). 
  { apply Nat.mod_upper_bound. lia. } (* x mod 2 must be less than 2 because the divisor is 2 *)
  lia. (* Using lia to find contradiction between H and Hmod *)
Qed.

Proposition x_in_its_generated_pair : forall x,
  In x [2 * (x / 2); 2 * (x / 2) + 1].
Proof.
  intros x.
  destruct (x mod 2) eqn:E.  (* Destruct based on the parity of x *)
  - left.  (* Case for even x *)
    assert (Hx : x = 2 * (x / 2)).  (* Prove that x is twice its half for even x *)
      { rewrite Nat.div_exact; auto; lia. }
    rewrite <- Hx. reflexivity.
  - destruct n. right. (* Case for odd x *)
    assert (Hx : x = 2 * (x / 2) + 1).  (* Prove that x is twice its half plus one for odd x *)
    { rewrite Nat.div_mod with (x := x) (y := 2) at 1. rewrite E. auto. lia. }
    rewrite <- Hx. auto. simpl. lia.
    apply mod_2_contradiction in E. contradiction.
Qed.


Lemma check_instance_union : forall n,
  let np := generate_necklace_instance (n) in 
  instance_union np.
  Proof.
  intros n.
  unfold valid_union, generate_necklace_instance. simpl.
  intros x. split.
  - intros H_lt.
    exists [2 * (x / 2); 2 * (x / 2) + 1].
    split.
    + assert (Hk: x / 2 < n).
      { apply Nat.div_lt_upper_bound. lia. apply H_lt. }
      apply in_map_iff.
      exists (x / 2).
      split.
      * reflexivity.
      * apply in_seq.
        split; try lia; try (apply Nat.div_lt_upper_bound; lia).
    + apply x_in_its_generated_pair.
  - intros [l [H_in_l H_in_x]].
    apply in_map_iff in H_in_l.
    destruct H_in_l as [k [H_eq H_in_k]].
    apply in_seq in H_in_k.
    destruct H_in_k as [Hk1 Hk2].
    subst.
    simpl in H_in_x.
    destruct H_in_x.
    + subst. simpl. lia.
    + destruct H.
     ++  subst. simpl. lia.
     ++ contradiction.
Qed.



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

Lemma stupid_coq : forall n, n > 0 -> n + n - 1 = n + n - 2 + 1.
Proof.
  intros n.
  lia.
Qed.


(* Lemma: A valid solution must have transitions at the ends of the binary sequence *)
Lemma valid_solution_requires_transitions_at_ends :
  forall n, let np := generate_necklace_instance n in
            forall sol : solution, let s := length (binary_seq sol) in n > 0 ->
              valid_solution np sol -> (nth (s - 2) sol.(binary_seq) false) <> (nth (s - 1) sol.(binary_seq) false).
Proof.
  intros n np sol s Hgreater Hval.
  destruct Hval as [Hpart Hlen].
  unfold valid_solution_partition in Hpart.  unfold generate_necklace_instance in np; subst.
  assert (H: s = np.(m)).
  { apply Hlen. }
  assert(np.(m) = 2 * n).
  { auto. }
  assert (Hdiff: nth (s-2) (binary_seq sol) false <> nth (s-1) (binary_seq sol) false).
  { 
    specialize (Hpart [s - 2; s - 1]).
    simpl in Hpart.
    assert (Hin: In [s - 2; s - 1] (subsets np)).
    { simpl; apply in_map_iff; exists (n - 1); split; [auto| apply in_seq; try lia]. simpl. rewrite H. rewrite H0.
    simpl.
    replace (n + 0) with n by lia.
    replace (n - 1 + 0) with (n-1) by lia.
    replace (n - 1 + (n - 1)) with (n + n - 2) by lia.
    simpl.
    replace (n + n - 2 + 1) with (n + n - 1). auto. apply stupid_coq. apply Hgreater. }
    specialize (Hpart Hin).
    simpl in Hpart.
    destruct (nth (s - 2) (binary_seq sol)); destruct (nth (s - 1) (binary_seq sol));
    lia. 
  }
  exact Hdiff.
Qed.


Lemma map_ext_in : forall A B (f g : A -> B) l, (forall x, In x l -> f x = g x) -> map f l = map g l.
Proof.
  intros A B f g l H.
  induction l.
  - simpl. auto.
  - simpl. f_equal. apply H. left. auto. apply IHl. intros. apply H. right. auto.
Qed.

Lemma range_of_subsets : forall n, let np := generate_necklace_instance n in
  forall s, In s (subsets np) -> forall i, In i s -> i < 2*n.
  Admitted.

Lemma firstn_preserves : forall l: list bool, forall i, forall t,  i < t -> nth i
(binary_seq
   {| binary_seq := firstn (t) l|}) false =
nth i (l) false.
Admitted.

Lemma subsets_monotonicity: forall n,
  forall s, In s (subsets (generate_necklace_instance n)) -> In s (subsets (generate_necklace_instance (S n))).
  Admitted.


Lemma prefix_of_valid_solution_are_valid :
  forall n, let np := generate_necklace_instance (S n) in
            forall sol : solution,
              valid_solution np sol -> valid_solution (generate_necklace_instance n) {| binary_seq := firstn (2 * n) sol.(binary_seq) |}.
Proof.
  intros n np sol Hvalid.
  unfold valid_solution, valid_solution_partition, valid_instance in *.
  destruct Hvalid as [Hpart_sol Hlen_sol].
  split.
  - (* Valid Solution Partition *)
    intros s Hin.
    assert (Hin_orig : In s (subsets (generate_necklace_instance (S n)))).
    { apply subsets_monotonicity. auto. }
    apply Hpart_sol in Hin_orig.
    assert ( Hh:
      forall i, In i s -> nth i (binary_seq {| binary_seq := firstn (2 * n) (binary_seq sol) |}) false = nth i (binary_seq sol) false). {
        intros i Hin_i.
        apply (range_of_subsets n) in Hin_i; try apply Hin.
        apply (firstn_preserves (binary_seq sol)).
        auto.
      }
      assert((map
      (fun i : nat =>
       if nth i (binary_seq sol) false then 1 else 0)
      s) = (map
      (fun i : nat =>
       if
        nth i
          (binary_seq
             {| binary_seq := firstn (2 * n) (binary_seq sol) |})
          false
       then 1
       else 0) s)). {
        apply map_ext_in. intros. 
        replace (nth x (binary_seq sol) false) with(nth x  (binary_seq
        {| binary_seq := firstn (2 * n) (binary_seq sol) |})
     false).
        auto. apply Hh. auto.
       }
      rewrite <- H.
      apply Hin_orig.
  - (* Length of Binary Sequence *)
    unfold generate_necklace_instance in *.
    simpl in *.
    rewrite firstn_length.
    lia.
Qed.


Lemma transition_count_last:
  forall l: list bool, let s := length l in
  s >= 2 /\ (nth (s-2) l false) <> (nth (s-1) l false) -> transition_count l = S (transition_count (firstn (s-1) l)).
Proof.
Admitted.

Lemma transition_count_increase:
  forall l: list bool, let s := length l in
  s >= 2 -> transition_count (firstn (s-1) l) >= transition_count (firstn (s-2) l).
Proof.
  intros l.
  unfold transition_count.
Admitted.

Proposition transition_count_of_list_with_one_more_transition :
  forall l: list bool, let s := length l in 
  s >= 2 /\ (nth (s-2) l false) <> (nth (s-1) l false) -> transition_count l >= S (transition_count (firstn (s-2) l)).
Proof.
  intros l.
  intros.
  assert (s >= 2) by lia.
  apply transition_count_last in H.
  rewrite H.
  assert (s = length l) by lia.
  rewrite H1.
  assert (transition_count (firstn (s - 1) l) >= transition_count (firstn (s - 2) l)).
  { apply transition_count_increase. lia. }
  rewrite H1 in H2.
  lia.
Qed.

Proposition basic_calc_1 : forall n, n + S (n + 0) - 1 = 2 * n.
Proof.
  intros n.
  lia.
Qed.

(* Theorem: Any valid solution for the specific instance must have at least n transitions *)
Theorem valid_solution_requires_transitions :
  forall n, let np := generate_necklace_instance n in
            forall sol : solution,
              valid_solution np sol -> transition_count (binary_seq sol) >= n.
Proof.
  intros n.
  intros np.
  induction n.
  - intros sol.
    intros H.
    simpl. lia.
  - intros sol.
    intros H.
    pose proof H as H_copy.
    destruct H.
    assert (Hlength: length (binary_seq sol) = 2 * S n ).
    { apply H0. }
    assert (Hmid: let s:= length (binary_seq sol) in transition_count (binary_seq sol) >= S (transition_count (firstn (s - 2) (binary_seq sol)))).
    { apply transition_count_of_list_with_one_more_transition.
      split.
      - lia.
      - apply valid_solution_requires_transitions_at_ends with (n:= S n).
        + lia. + apply H_copy. }
    assert (Hprefix: valid_solution (generate_necklace_instance n) {| binary_seq := firstn (2 * n) (binary_seq sol) |}).
    { apply prefix_of_valid_solution_are_valid.
      apply H_copy. }
    apply IHn in Hprefix.
    assert (Htrans: transition_count (firstn (2 * n) (binary_seq sol)) >= n).
    { apply Hprefix. }
    assert (Htrans2: let s:= length (binary_seq sol) in transition_count (firstn (s - 2) (binary_seq sol)) >= n).
    { rewrite Hlength. simpl. rewrite basic_calc_1. apply Htrans. }
    apply Nat.le_trans with (m := S (transition_count (firstn (length (binary_seq sol) - 2) (binary_seq sol)))).
    + apply le_n_S in Htrans2. auto.
    + apply Hmid.
Qed.

(* Theorem: Formal Theorem *)
Theorem lower_bound_for_necklace_problem :
 forall n, exists np : necklace_problem, valid_instance np /\
  forall sol : solution, valid_solution np sol -> transition_count (binary_seq sol) >= n. 
Proof.
  intros n.
  exists (generate_necklace_instance n).
  split.
  - apply check_valid_instance.
  - apply valid_solution_requires_transitions.
Qed.

