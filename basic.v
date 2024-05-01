Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Import ListNotations.


(* A structure to represent the necklace problem *)
Structure necklace_problem := {
  m : nat;                            (* Total number of elements *)
  subsets : list (list nat)           (* List of subsets *)
}.

(* A structure for the solution, which is a binary sequence *)
Structure solution := {
  binary_seq : list bool              (* The binary sequence *)
}.

Definition is_even (n : nat) : Prop := exists k : nat, n = 2 * k.

(* To ensure all subsets have an even number of elements *)
Definition even_subset (s : list nat) : Prop := is_even (length s).

(* Ensure the union of all subsets is exactly {0, 1, ..., m-1} *)
Definition valid_union (m : nat) (subs : list (list nat)) : Prop :=
  forall x : nat, x < m <-> (exists l, In l subs /\ In x l).

(* Ensure all subsets are disjoint *)
Definition disjoint_subsets (subs : list (list nat)) : Prop :=
  forall l1 l2 : list nat, In l1 subs -> In l2 subs -> l1 <> l2 -> 
  forall x : nat, ~ (In x l1 /\ In x l2).

(* Count transitions in the binary sequence *)
Fixpoint transition_count_re (seq : list bool) : nat :=
  match seq with
  | [] | [_] => 0
  | b1 :: (b2 :: rest as tail) => 
      (if Bool.eqb b1 b2 then 0 else 1) + transition_count_re tail
  end.

Definition count_single_transitions_in_pair (acc : nat) (pair : bool * bool) : nat :=
  let (b1, b2) := pair in
  if Bool.eqb b1 b2 then acc else S acc.
  
Definition count_transitions_in_pair (pairs : list (bool * bool)) : nat :=
  List.fold_left count_single_transitions_in_pair pairs 0.

Definition transition_count_non_re (seq : list bool) : nat :=
  let pairs := combine seq (tl seq) in
  count_transitions_in_pair pairs.

Fixpoint sum_nat_list (l : list nat) : nat :=
  match l with
  | [] => 0         (* If the list is empty, the sum is 0 *)
  | x :: rest => x + sum_nat_list rest  (* Add the head to the sum of the rest of the list *)
  end.

Lemma sum_nat_list_app : forall l1 l2, sum_nat_list (l1 ++ l2) = sum_nat_list l1 + sum_nat_list l2.
Proof.
  intros l1 l2.
  induction l1 as [| x l1' IH].
  - simpl. auto.
  - simpl. rewrite IH. lia.
Qed.

Definition from_pair_to_nat (pair : bool * bool) : nat :=
  let (b1, b2) := pair in
  if Bool.eqb b1 b2 then 0 else 1.

Definition get_nat_list (seq : list bool) : list nat :=
  let s := length seq in
  map from_pair_to_nat (combine (firstn (s - 1) seq) (skipn 1 seq)).

Definition transition_count (seq : list bool) : nat :=
  sum_nat_list (get_nat_list seq).

Lemma imbalance_combine: forall seq : list bool,
  let s := length seq in
  s >= 1 ->
  combine seq (skipn 1 seq) = combine (firstn (s - 1) seq) (skipn 1 seq).
Proof.
  intros seq.
  rewrite combine_firstn_r.
  intros.
  assert (s = length seq) by lia.
  assert (s - 1 = length (skipn 1 seq)).
  { rewrite skipn_length. lia. }
  rewrite H1.
  auto.
Qed.

Lemma get_nat_list_prefix: forall seq : list bool, 
  let s := length seq in
  s >= 2 -> 
  firstn (s - 2 ) (get_nat_list seq) = 
  get_nat_list (firstn (s - 1) seq).
Proof.
  intros seq s H.
  assert (H1: s = length seq) by lia.
  
  unfold get_nat_list.
  rewrite <- H1. 
  rewrite firstn_map.
  rewrite combine_firstn.
  rewrite firstn_firstn.
  assert (Hmin: Init.Nat.min (s - 2) (s - 1) = (s-2)).
  { lia. }
  rewrite Hmin.
  rewrite skipn_firstn_comm.
  assert (Hlength: (length (firstn (s - 1) seq) - 1) = (s-2)).
  { rewrite firstn_length_le. lia. rewrite H1. lia. }
  rewrite Hlength.
  rewrite firstn_firstn.
  rewrite Hmin.
  replace (s - 2) with (s - 1 - 1) by lia.
  reflexivity.
Qed.

Lemma combine_app: forall A B (l1 l2: list A) (l3 l4: list B),
  length l1 = length l3 -> length l2 = length l4 ->
  combine (l1 ++ l2) (l3 ++ l4) = combine l1 l3 ++ combine l2 l4.
Proof.
  intros A B l1 l2.
  induction l1 as [| x1 l1' IH1] in l2 |- *.
  - simpl.
    intros l3 l4 H1 H2.
    inversion H1.
    assert (Hl3nil: l3 = []). { destruct l3. auto. simpl length in H2. discriminate H0. }
    assert (H3: l3 ++ l4 = l4). { rewrite Hl3nil. apply app_nil_l. }
    rewrite H3. auto.
  -
    intros l3 l4 H1 H2.
    destruct l3 as [| x3 l3'].
    + simpl in H1. discriminate H1.
    + simpl in H1.
      assert (H3: length l1' = length l3'). { simpl in H1. lia. }
      assert (Hsplit: combine (x1 :: l1') (x3 :: l3') = (x1, x3) :: combine l1' l3').
      { auto. }
      rewrite Hsplit.
      assert (Hcomm: (((x1, x3) :: combine l1' l3') ++ combine l2 l4) = (x1, x3) :: (combine l1' l3' ++ combine l2 l4)).
      { auto. }
      rewrite Hcomm.
      assert (Hsplit2: combine ((x1 :: l1') ++ l2) ((x3 :: l3') ++ l4) = (x1, x3) :: (combine (l1' ++ l2) (l3' ++ l4))).
      { auto. }
      rewrite Hsplit2.
      replace ((x1, x3) :: combine l1' l3' ++ combine l2 l4) with ((x1, x3) :: (combine l1' l3' ++ combine l2 l4)) by auto.
      assert (Hsame: combine (l1' ++ l2) (l3' ++ l4) = combine l1' l3' ++ combine l2 l4).
      {
        apply IH1.
        - auto.
        - simpl in H2. lia.
      }
      rewrite Hsame.
      reflexivity.
Qed.
      

Lemma get_nat_list_two_parts_form1: forall seq : list bool, 
  let s := length seq in
  s >= 2 -> 
  get_nat_list seq = get_nat_list (firstn (s - 1) seq) ++ get_nat_list (skipn (s - 2) seq). 
Proof.
  intros seq s H.
  assert (H1: s = length seq) by lia.
  unfold get_nat_list.
  assert (H2: length (firstn (s - 1) seq) = s - 1). 
    { apply firstn_length_le; lia. }
  assert (H3: length (skipn (s - 2) seq) = 2).
    { rewrite skipn_length. lia. } 
  rewrite <- H1.
  rewrite <- map_app.
  assert (H4: length (firstn (s - 2) seq) = s - 2).
  { apply firstn_length_le. lia. }
  rewrite <- combine_app.
    -
    rewrite H2.
    
    rewrite H3.
    replace (s - 1 - 1) with (s - 2) by lia.
  (*
    rewrite firstn_firstn. 
    assert (Hmin: Init.Nat.min (s - 1 - 1) (s - 1) = (s-2)).
    { lia. }
    rewrite Hmin.
  *)
    rewrite firstn_skipn_comm.
    replace (s - 2 + (2 - 1)) with (s - 1) by lia.
    rewrite firstn_skipn.
    rewrite skipn_skipn.
    replace (1 + (s-2)) with (s - 1) by lia.
    assert (Hcomm2: (skipn 1 (firstn (s - 1) seq) ++
    skipn (s - 1) seq) = (skipn 1 ((firstn (s - 1) seq) ++
    skipn (s - 1) seq))).
    {
      rewrite skipn_app. rewrite H2.
      replace (1 - (s - 1)) with 0 by lia.
      auto.
    }
    rewrite Hcomm2.
    rewrite firstn_skipn.
    reflexivity.
  (*argue about length*)
  - rewrite H2.
    rewrite firstn_firstn. 
    assert (Hmin: Init.Nat.min (s - 1 - 1) (s - 1) = (s-2)).
    { lia. }
    rewrite Hmin.
    rewrite H4.
    rewrite skipn_firstn_comm.
    assert (H5: length (firstn (s - 1 - 1) (skipn 1 seq)) = s-2).
    { rewrite firstn_length_le. lia. rewrite skipn_length. lia. }
    rewrite H5.
    reflexivity.
  (*argue about length*)
  - rewrite H3.
    rewrite skipn_length.
    rewrite H3.
    rewrite firstn_length_le.
    + reflexivity.
    + lia.
Qed.
     
Lemma transition_count_two_parts_form1: forall seq : list bool, 
  let s := length seq in
  s >= 2 -> 
  transition_count seq = transition_count (firstn (s - 1) seq) + transition_count (skipn (s - 2) seq).
Proof.
  intros seq s H.
  assert (H1: s = length seq) by lia.
  unfold transition_count.
  rewrite get_nat_list_two_parts_form1.
  rewrite sum_nat_list_app.
  reflexivity.
  auto.
Qed.

(*
Lemma get_nat_list_two_parts: forall seq : list bool, 
  let s := length seq in
  s >= 2 -> 
  get_nat_list seq = get_nat_list (firstn (s - 1) seq) ++ [from_pair_to_nat ((nth (s - 2) seq false), (nth (s - 1) seq false))]. 
Proof.
  intros seq s H.
  assert (H1: s = length seq) by lia.
  unfold get_nat_list.
  rewrite <- H1.
Admitted.
*)

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

(* Combine three previous lemmas *)
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
Proof.
  intros n np s Hs i Hi.
  apply in_map_iff in Hs.
  destruct Hs as [k [H1 H2]].
  inversion H1. subst.
  apply in_seq in H2.
  destruct H2 as [H2 H3].
  simpl in Hi.
  destruct Hi.
  - subst. lia.
  - destruct H. lia.
Qed.

Lemma firstn_preserves : forall l: list bool, forall i, forall t,  i < t -> nth i
(binary_seq
   {| binary_seq := firstn (t) l|}) false =
nth i (l) false.
Proof.
  intros l.
  induction l.
  - intros. simpl. destruct i; destruct t; try lia.
    + auto.
    + simpl. destruct i; destruct t; try lia.
  - intros. destruct t.
    + lia.
    + simpl. destruct i.
      * auto.
      * apply IHl. lia.
Qed.

Lemma subsets_monotonicity: forall n,
  forall s, In s (subsets (generate_necklace_instance n)) -> In s (subsets (generate_necklace_instance (S n))).
Proof.
  intros n s H.
  apply in_map_iff in H.
  destruct H as [k [H1 H2]].
  inversion H1. subst.
  apply in_map_iff.
  exists k.
  split.
  - reflexivity.
  - apply in_seq. split; try lia.
    apply in_seq in H2. lia.  
Qed.


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

(*
Lemma structure_of_head1: 
forall l: list bool, let s := length l in
  s >= 2 -> firstn 1 l =  (nth 0 l false) :: [].
Proof.
  intros.
  assert (H1: s = length l) by lia.
  induction l.
  - simpl in H1. rewrite H1 in H. lia.
  - simpl. auto.
Qed.

Lemma rev_unit: forall l: list bool, length l = 1 -> rev l =  l.
Proof.
  intros.
  induction l.
  - auto.
  - simpl in H.
    destruct l.
    + simpl. auto.
    + simpl in H. lia.
Qed.

Lemma structure_of_tail_tail_rev: 
forall l: list bool, let s := length l in
  s >= 2 -> skipn (s - 1) (rev l) =  (nth (s - 1) (rev l) false) :: [].
Proof.
  intros.
  assert (H1: s = length l) by lia.
  rewrite H1.
  rewrite rev_nth.
  - rewrite skipn_rev.
    replace (length l - (length l - 1)) with 1 by lia.
    replace (length l - S (length l - 1)) with 0 by lia.
    rewrite rev_unit.
    + rewrite structure_of_head1.
      * simpl. auto.
      * lia.
    + rewrite firstn_length. lia.
  - lia.
Qed.

Lemma structure_of_tail_tail: 
forall l: list bool, let s := length l in
  s >= 2 -> skipn (s - 1) l =  (nth (s - 1) l false) :: [].
Proof.
  intros.
  rewrite <- rev_involutive with (l:=l).
  rewrite structure_of_tail_tail_rev with (l := rev l).

*)

Lemma structure_of_tail: 
forall l: list bool, let s := length l in
  s >= 2 -> skipn (s - 2) l = (nth (s - 2) l false) :: (nth (s - 1) l false) :: [].
Proof.
  
Admitted.


Lemma transition_count_last_equal_to_one: 
  forall l: list bool, let s := length l in
  s >= 2 /\ (nth (s-2) l false) <> (nth (s-1) l false) -> transition_count (skipn (s - 2) l) = 1.
Proof.
  intros.
  assert (H1: s = length l) by lia.
  rewrite H1.
  destruct H.
  rewrite structure_of_tail.
  - unfold transition_count.
    simpl.
    rewrite <- H1.
    assert (Heqb: Bool.eqb (nth (s - 2) l false) (nth (s - 1) l false) = false).
    { destruct (nth (s - 2) l false), (nth (s - 1) l false);
    simpl; try reflexivity; contradiction H0; auto. }
    rewrite Heqb.
    auto.
  - auto.
Qed.


Lemma transition_count_last:
  forall l: list bool, let s := length l in
  s >= 2 /\ (nth (s-2) l false) <> (nth (s-1) l false) -> transition_count l = S (transition_count (firstn (s-1) l)).
Proof.
  intros.
  assert (H1: s = length l) by lia.
  rewrite H1.
  rewrite transition_count_two_parts_form1.
  - assert (H2: transition_count (skipn (s - 2) l) = 1).
    { apply transition_count_last_equal_to_one. auto. }
    rewrite H1 in H2.
    rewrite H2.
    lia.
  - lia.
Qed.

Lemma firstn_decrease_transition_count:
  forall l: list bool, let s := length l in
  s >= 1 ->  transition_count l >= transition_count (firstn (s-1) l) .
Proof.
  intros l s Hs.
  destruct (le_lt_dec 2 s) as [Hge2 | Hlt2].
  - apply transition_count_two_parts_form1 in Hge2.
    replace (length l - 1) with (s - 1) in Hge2 by lia.
    lia.
  - assert (Hlen: length (firstn (s-1) l) < 2) by (rewrite firstn_length, Nat.min_l; lia).
    assert (Hzero2: transition_count (firstn (s-1) l) = 0).
    * assert (s = 1) by lia. 
      replace s with 1.
      simpl.
      auto.
    * rewrite Hzero2.
      lia.
Qed.


Lemma transition_count_increase:
  forall l: list bool, let s := length l in
  s >= 2 -> transition_count (firstn (s-1) l) >= transition_count (firstn (s-2) l).
Proof.
  intros l.
  intros.
  assert (s >= 2) by lia.
  assert (Init.Nat.min (s - 2) (s - 1) = s-2) by lia.
  assert (H2: firstn (s-2) l = firstn (s-2) (firstn (s-1) l)).
  { rewrite firstn_firstn. rewrite H1. auto. }
  rewrite H2.
  assert( length (firstn (s-1) l) = s-1 ).
  { apply firstn_length_le. lia. }
  assert( length (firstn (s-1) l) >= 1 ).
  { rewrite H3. lia. }
  assert(s-2 = length (firstn (s-1) l)-1).
  { rewrite H3. lia. }
  rewrite H5.
  apply firstn_decrease_transition_count.
  apply H4.
Qed.

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

