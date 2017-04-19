Require Import Arith.
Require Import Ensembles.
Require Import Powerset_facts.
Require Import Coq.Logic.FunctionalExtensionality.

(* Some facts about sets *)
Section SetFacts.
  Lemma union_assoc2 : forall U a b c, Union U a (Union U b c) = Union U b (Union U a c).
  Proof.
    intros.
    rewrite Union_commutative. rewrite Union_associative.
    rewrite Union_commutative with (A := c) (B := a). reflexivity.
  Qed.

  Lemma subtract_not : forall U s x, not (In U s x) -> (s = Subtract U s x).
  Proof.
    intros. apply Extensionality_Ensembles. unfold Same_set. split.
    (* left: s is included in (s - x) *)
    unfold Included. intros. unfold Subtract. constructor.
    assumption. red. intro. inversion H1. subst. red in H. apply H. apply H0.
    (* right: (s - x) is included in s *)
    unfold Included. unfold Subtract. intros. red in H. unfold Setminus in H0. unfold In in H0. unfold In. apply H0.
  Qed.

  Lemma subtract_in : forall U s x, Subtract U s x = Subtract U (Union U s (Singleton U x)) x.
  Proof.
    intros.
    apply Extensionality_Ensembles. unfold Same_set. split.
    - (* left *)
      unfold Included. intros. inversion H. constructor. constructor. assumption. assumption.
    - (* right *)
      unfold Included. intros. inversion H.
      constructor.
      -- (* x0 is in s - x *)
        inversion H0; subst. assumption. exfalso. apply H1. apply H2.
      -- (* x0 is not in {x} *)
        assumption.
  Qed.

  Lemma union_already_in : forall U s x,
      In U s x ->
      (Union U (Singleton U x) s) = s.
  Proof.
    intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split.
    (* left *)
    intros. inversion H0; subst. inversion H1; subst. assumption. assumption.
    (* right *)
    intros. apply Union_intror. assumption.
  Qed.

  Lemma empty_set_empty : forall U (x : U), ~ In U (Empty_set U) x.
  Proof.
    red. intros. inversion H.
  Qed.

  Lemma empty_set_neq_union : forall U A x, ~ (Same_set U (Empty_set U) (Union U (Singleton U x) A)).
  Proof.
    red. unfold Same_set. unfold Included. intros. inversion H.
    apply (empty_set_empty U x). apply H1. constructor. constructor.
  Qed.

  Lemma same_set_comm : forall U A B, Same_set U A B -> Same_set U B A.
  Proof.
    unfold Same_set. intros. split; inversion H; auto.
  Qed.

  Lemma union_neq_empty_set : forall U A x, ~ (Same_set U (Union U (Singleton U x) A) (Empty_set U)).
  Proof.
    red. intros. apply same_set_comm in H. apply (empty_set_neq_union _ _ _ H).
  Qed.

  Lemma same_set_A_A : forall U A, Same_set U A A.
  Proof.
    unfold Same_set. intros. split; unfold Included; intros; assumption.
  Qed.

  Lemma union_diff_empty_set : forall U A x, ~ ((Union U (Singleton U x) A) = Empty_set U).
  Proof.
    red. intros.
    apply (union_neq_empty_set U A x). rewrite H. apply same_set_A_A.
  Qed.

  Lemma subtract_union_same : forall U (A : Ensemble U) (x : U),
      ~ In U A x -> Subtract U (Union U (Singleton U x) A) x = A.
  Proof.
    intros.
    apply Extensionality_Ensembles. constructor.
    - (* -> *)
      unfold Included. intros y H2. inversion H2. inversion H0; subst.
      exfalso. apply H1. apply H3.
      assumption.
    - (* <- *)
      unfold Included. intros y H2.
      constructor. apply Union_intror. assumption.
      red. intros. inversion H0; subst. apply H. apply H2.
  Qed.
End SetFacts.

(* Some facts about numbers *)
Section NatFacts.
  Require Import Omega.
  Lemma add1_sub1_same : (forall x, x + 1 - 1 = x).
  Proof. intros. omega. Qed.

  Lemma S_sub1_same : (forall x, S x - 1 = x).
  Proof. intros. omega. Qed.

  Lemma ngt_ge_eq : forall x y, ~ (x < y) -> x <= y -> x = y.
  Proof. intros. omega. Qed.

  Lemma le_and_neq : forall x y, x <= y -> x <> y -> S x <= y.
  Proof. intros. omega. Qed.
End NatFacts.

Section Mboxes.
  Variable Message : Type.
  Axiom Message_eq_dec : forall (x y : Message), (x = y) \/ (x <> y).
  Axiom Message_eq_dec2 : forall (x y : Message), {x = y} + {x <> y}.

  Inductive Mbox :=
  | MboxEmpty : Mbox
  | MboxCons : Message -> Mbox -> Mbox.

  Fixpoint enq (m : Message) (mb : Mbox) : Mbox :=
    match mb with
    | MboxEmpty => MboxCons m MboxEmpty
    | MboxCons m' mb' => MboxCons m' (enq m mb')
    end.

  Definition deq (mb : Mbox) : Ensemble (Message * Mbox)  :=
    match mb with
    | MboxEmpty => Empty_set (Message * Mbox)
    | MboxCons m' mb' => Singleton (Message * Mbox) (m', mb')
    end.

  Fixpoint size (mb : Mbox) : nat :=
    match mb with
    | MboxEmpty => O
    | MboxCons _ mb' => S (size mb')
    end.

  Lemma deq_removes_1 : forall m mb mb', In (Message * Mbox) (deq mb) (m, mb') -> size mb = S (size mb').
  Proof.
    intros. destruct mb; inversion H; subst; auto.
  Qed.

  Lemma deq_smaller : forall m mb mb', In (Message * Mbox) (deq mb) (m, mb') -> size mb' < size mb.
    intros. rewrite (deq_removes_1 m mb mb' H). constructor.
  Qed.

  Lemma enq_size_add1 : forall m mb, size (enq m mb) = S (size mb).
  Proof.
    intros. induction mb. reflexivity.
    simpl. rewrite IHmb. reflexivity.
  Qed.

  Inductive NatInf : Type :=
  | Nat : nat -> NatInf
  | Inf : NatInf.

  Inductive NatInf_subsumed (x : nat) : NatInf -> Prop :=
  | NatInf_subsumed_conc :  NatInf_subsumed x (Nat x)
  | NatInf_subsumed_inf : NatInf_subsumed x Inf.

  Lemma NatInf_subsumed_elim_S : forall n n',
      NatInf_subsumed n (Nat n') ->
      NatInf_subsumed (S n) (Nat (S n')).
  Proof.
    intros. destruct (eq_nat_dec n n'); subst.
    - (* n = n' *) constructor.
    - (* n <> n' *) inversion H; constructor.
  Qed.

  Inductive NatInf_subsumed_abs : NatInf -> NatInf -> Prop :=
  | NatInf_subsumed_abs_conc : forall x, NatInf_subsumed_abs (Nat x) (Nat x)
  | NatInf_subsumed_abs_inf : NatInf_subsumed_abs Inf Inf
  | NatInf_subsumed_abs_both : forall x, NatInf_subsumed_abs (Nat x) Inf.

  Definition enq_sound (AbsMbox : Type) (alpha : Mbox -> AbsMbox) (aenq : Message -> AbsMbox -> AbsMbox) :=
    forall (m : Message) (mb : Mbox),
      alpha (enq m mb) = aenq m (alpha mb).
  Check enq_sound.

  Definition deq_sound_overapprox (AbsMbox : Type) (alpha : Mbox -> AbsMbox) (subsumed : AbsMbox -> AbsMbox -> Prop) (adeq : AbsMbox -> Ensemble (Message * AbsMbox)) :=
    forall (m : Message) (mb mb' : Mbox),
      In (Message * Mbox) (deq mb) (m, mb') ->
      (exists absmb,
          (In (Message * AbsMbox) (adeq (alpha mb)) (m, absmb)) /\
          (subsumed (alpha mb') absmb)).
  Check deq_sound_overapprox.

  Definition deq_sound (AbsMbox : Type) (alpha : Mbox -> AbsMbox)
             (adeq : AbsMbox -> Ensemble (Message * AbsMbox)) :=
    forall (m : Message) (mb mb' : Mbox),
      In (Message * Mbox) (deq mb) (m, mb') ->
      In (Message * AbsMbox) (adeq (alpha mb)) (m, alpha mb').
  Check deq_sound.

  Definition size_sound (AbsMbox : Type) (alpha : Mbox -> AbsMbox)
                (asize : AbsMbox -> NatInf -> Prop) :=
    forall (mb : Mbox) (n : NatInf),
      asize (alpha mb) n ->
      NatInf_subsumed (size mb) n.
  Check size_sound.

  Definition empty_sound (AbsMbox : Type) (alpha : Mbox -> AbsMbox) (aempty : AbsMbox) :=
    alpha MboxEmpty = aempty.
  Hint Unfold empty_sound.
  Check empty_sound.

  Definition abstraction_sound (AbsMbox : Type) (alpha : Mbox -> AbsMbox)
             (subsumed : AbsMbox -> AbsMbox -> Prop)
             (aenq : Message -> AbsMbox -> AbsMbox)
             (adeq : AbsMbox -> Ensemble (Message * AbsMbox))
             (asize : AbsMbox -> NatInf -> Prop)
             (aempty : AbsMbox) :=
    enq_sound AbsMbox alpha aenq /\
    (deq_sound AbsMbox alpha adeq \/
     deq_sound_overapprox AbsMbox alpha subsumed adeq) /\
    size_sound AbsMbox alpha asize /\
    empty_sound AbsMbox alpha aempty.

  Section SetMboxes.
    Definition SetMbox : Type := Ensemble Message.
    Definition SetMboxEmpty : SetMbox := Empty_set Message.

    Fixpoint SetMbox_alpha (mb : Mbox) : SetMbox :=
      match mb with
      | MboxEmpty => SetMboxEmpty
      | MboxCons m mb' => Union Message (Singleton Message m) (SetMbox_alpha mb')
      end.
    Definition SetMbox_subsumed (mb mb' : SetMbox) : Prop := Same_set Message mb mb'.

    Definition SetMbox_enq (m : Message) (mb : SetMbox) : SetMbox :=
      Union Message (Singleton Message m) mb.

    Inductive SetMbox_deq (mb : SetMbox) : (Ensemble (Message * SetMbox)) :=
    | SetMbox_deq_keep : forall m: Message,
        In Message mb m -> In (Message * SetMbox) (SetMbox_deq mb) (m, mb)
    | SetMbox_deq_drop : forall m: Message,
        In Message mb m -> In (Message * SetMbox) (SetMbox_deq mb) (m, Subtract Message mb m).

    Inductive SetMbox_size : SetMbox -> NatInf -> Prop :=
    | SetMbox_size_empty : SetMbox_size SetMboxEmpty (Nat 0)
    | SetMbox_size_nonempty : forall (mb : SetMbox), Inhabited _ mb -> SetMbox_size mb Inf.

    Lemma SetMbox_alpha_after_enq : forall m mb,
        SetMbox_alpha (enq m mb) = Union Message (Singleton Message m) (SetMbox_alpha mb).
    Proof.
      intros. induction mb as [| m' mb'].
      (* mb empty *)
      - reflexivity.
      (* mb not empty *)
      - simpl. rewrite IHmb'. apply union_assoc2.
    Qed.

    Lemma SetMbox_enq_sound : enq_sound SetMbox SetMbox_alpha SetMbox_enq.
    Proof.
      unfold enq_sound. intros.
      rewrite SetMbox_alpha_after_enq. unfold SetMbox_enq. reflexivity.
    Qed.
    Hint Resolve SetMbox_enq_sound.
    Check SetMbox_enq_sound.

    Lemma deq_union_singleton_keep : forall m mb,
        In Message mb m ->
        In (Message * SetMbox)
           (SetMbox_deq (Union Message (Singleton Message m) mb))
           (m, mb).
    Proof.
      intros. rewrite (union_already_in Message mb m H).
      constructor. assumption.
    Qed.

    Lemma deq_union_singleton_drop : forall m mb,
        not (In Message mb m) ->
        In (Message * SetMbox)
           (SetMbox_deq (Union Message (Singleton Message m) mb))
           (m, mb).
    Proof.
      intros.
      rewrite (subtract_not Message mb m H) at 2.
      rewrite subtract_in.
      rewrite Union_commutative.
      apply SetMbox_deq_drop. apply Union_intror. constructor.
    Qed.

    Lemma mbox_contains_or_not : forall m mb,
        (In Message (SetMbox_alpha mb) m \/ ~ In Message (SetMbox_alpha mb) m).
    Proof.
      intros. induction mb. simpl. right. red. intros. inversion H.
      simpl. destruct IHmb.
      left. constructor 2. assumption.
      destruct (Message_eq_dec m m0); subst.
      left. constructor. constructor.
      right.
      red. intro. inversion H1; subst. inversion H2; subst. apply H0. reflexivity.
      apply H. apply H2.
    Qed.

    Lemma SetMbox_deq_sound : deq_sound SetMbox SetMbox_alpha SetMbox_deq.
    Proof.
      unfold deq_sound.
      intros. destruct mb
      (* empty mb: no message *).
      inversion H.
      (* non empty mb *)
      inversion H; subst.
      destruct (mbox_contains_or_not m mb').
      (* contains *)
      simpl. apply deq_union_singleton_keep. assumption.
      (* does not contain *)
      apply deq_union_singleton_drop. assumption.
    Qed.
    Hint Resolve SetMbox_deq_sound.
    Check SetMbox_deq_sound.

    Lemma SetMbox_size_sound : size_sound SetMbox SetMbox_alpha SetMbox_size.
    Proof.
      unfold size_sound. destruct mb; intros.
      (* empty mailbox *)
      simpl. inversion H; subst. constructor.
      simpl. inversion H; subst. inversion H1; subst. inversion H2; subst.
      (* non-empty mailbox *)
      simpl. inversion H; subst. unfold SetMboxEmpty in H1.
      exfalso.
      apply (empty_set_neq_union Message (SetMbox_alpha mb) m).
      rewrite <- H1.
      apply same_set_A_A.
      constructor.
    Qed.
    Hint Resolve SetMbox_size_sound.
    Check SetMbox_size_sound.

    Lemma SetMbox_empty_sound : empty_sound SetMbox SetMbox_alpha SetMboxEmpty.
    Proof. auto. Qed.
    Hint Resolve SetMbox_empty_sound.
   Check SetMbox_empty_sound.

    Theorem SetMbox_sound :
      abstraction_sound SetMbox SetMbox_alpha SetMbox_subsumed
                          SetMbox_enq SetMbox_deq
                          SetMbox_size SetMboxEmpty.
    Proof.
      unfold abstraction_sound.
      auto.
    Qed.
    Check SetMbox_sound.
  End SetMboxes.

  Section BList.
    Variable max : nat.
    Variable max_assumption : max > 0.

    Inductive BListMbox :=
    | BListMbox_set : SetMbox -> BListMbox
    | BListMbox_list : forall (mb : Mbox), BListMbox.
    Definition BListMboxEmpty : BListMbox := BListMbox_list MboxEmpty.

    Definition BListMbox_alpha (mb : Mbox) : BListMbox :=
      if le_dec (size mb) max then
        BListMbox_list mb
      else BListMbox_set (SetMbox_alpha mb).

    Definition BListMbox_subsumed (mb mb' : BListMbox) :=
      match (mb, mb') with
      | (BListMbox_set s1, BListMbox_set s2) => SetMbox_subsumed s1 s2
      | (BListMbox_set _, BListMbox_list _) => False
      | (BListMbox_list l1, BListMbox_list l2) => l1 = l2
      | (BListMbox_list l, BListMbox_set s) => SetMbox_subsumed (SetMbox_alpha l) s
      end.

    Lemma BListMbox_subsumed_same : forall mb, BListMbox_subsumed mb mb.
    Proof.
      intros. destruct mb.
      (* set *)
      unfold BListMbox_subsumed. unfold SetMbox_subsumed. apply same_set_A_A.
      (* list *)
      unfold BListMbox_subsumed. reflexivity.
    Qed.

    Lemma BListMbox_empty_sound : empty_sound BListMbox BListMbox_alpha BListMboxEmpty.
    Proof. auto. Qed.
    Hint Resolve BListMbox_empty_sound.
    Check BListMbox_empty_sound.

    Inductive BListMbox_size : (BListMbox -> NatInf -> Prop) :=
    | BListMbox_size_infinite : forall s, BListMbox_size (BListMbox_set s) Inf
    | BListMbox_size_finite : forall mb, BListMbox_size (BListMbox_list mb) (Nat (size mb)).

    Lemma BListMbox_size_sound : size_sound BListMbox BListMbox_alpha BListMbox_size.
    Proof.
      unfold size_sound.
      intros. inversion H; subst.
      (* inf *)
      constructor.
      (* finite *)
      unfold BListMbox_alpha in H1. destruct (le_dec (size mb) max).
      (* size mb <= max *)
      inversion H1; subst. constructor.
      (* size mb > max *)
      inversion H1.
    Qed.
    Hint Resolve BListMbox_size_sound.
    Check BListMbox_size_sound.

    Definition BListMbox_enq (m : Message) (mb : BListMbox) : BListMbox :=
      match mb with
      | BListMbox_set mb' => BListMbox_set (SetMbox_enq m mb')
      | BListMbox_list mb' => BListMbox_alpha (enq m mb')
      end.

    Lemma BListMbox_enq_sound : enq_sound BListMbox BListMbox_alpha BListMbox_enq.
    Proof.
      unfold enq_sound. intros.
      unfold BListMbox_alpha. rewrite enq_size_add1.
      destruct (le_dec (size mb) max).
      (* size mb <= max *)
      - simpl. unfold BListMbox_alpha. rewrite enq_size_add1. reflexivity.
      (* size mb > max *)
      - simpl. destruct (le_dec (S (size mb)) max).
        (* S (size mb) <= max: impossible *)
        -- exfalso. apply n. apply le_Sn_le. assumption.
        (* S (size mb) > max *)
        -- rewrite SetMbox_enq_sound. reflexivity.
    Qed.
    Hint Resolve BListMbox_enq_sound.
    Check BListMbox_enq_sound.

    Inductive BListMbox_deq (mb : BListMbox) : (Ensemble (Message * BListMbox)) :=
    | BListMbox_deq_set : forall m s s',
        mb = BListMbox_set s ->
        In (Message * SetMbox)
           (SetMbox_deq s) (m, s') ->
        In (Message * BListMbox)
           (BListMbox_deq mb) (m, BListMbox_set s')
    | BListMbox_deq_list : forall m l l',
        mb = BListMbox_list l ->
        In (Message * Mbox)
           (deq l) (m, l') ->
        In (Message * BListMbox)
           (BListMbox_deq mb) (m, BListMbox_list l').

    Lemma BListMbox_subsumed_by_set : forall mb, BListMbox_subsumed (BListMbox_alpha mb) (BListMbox_set (SetMbox_alpha mb)).
    Proof.
      intros.
      unfold BListMbox_alpha.
      destruct (le_dec (size mb) max).
      - (* size mb <= max: becomes a list, subsumed *)
        unfold BListMbox_subsumed. unfold SetMbox_subsumed. apply same_set_A_A.
      - (* size mb > max: becomes a set, same *)
        apply BListMbox_subsumed_same.
    Qed.

    Lemma BListMbox_deq_set_from_set : forall m mb mb',
        In (Message * SetMbox)
           (SetMbox_deq mb) (m, mb') ->
        In (Message * BListMbox)
           (BListMbox_deq (BListMbox_set mb)) (m, BListMbox_set mb').
    Proof.
      intros. apply (BListMbox_deq_set (BListMbox_set mb) m mb mb'); auto.
    Qed.

    Lemma BListMbox_deq_sound_overapprox : deq_sound_overapprox BListMbox BListMbox_alpha BListMbox_subsumed BListMbox_deq.
    Proof.
      unfold deq_sound_overapprox. intros.
      destruct (le_dec (size mb) max).
      - (* size mb <= max: list deq *)
        exists (BListMbox_alpha mb').
        split.
        -- (* left: show that (m, alpha mb') in deq (alpha mb) *)
          unfold BListMbox_alpha.
          destruct (le_dec (size mb) max).
          --- (* size mb <= max *)
            destruct (le_dec (size mb') max).
            ---- (* size mb' <= max *)
              apply (BListMbox_deq_list (BListMbox_list mb) m mb mb'). reflexivity.
              assumption.
            ---- (* size mb' > max: impossible *)
              exfalso. apply n.
              apply le_S_n. rewrite <- (deq_removes_1 m mb mb').
              apply le_S. assumption. assumption.
         --- (* size mb > max: impossible *)
           exfalso; apply n; apply l.
        -- (* right: show that alpha mb' = alpha mb' *)
          apply BListMbox_subsumed_same.
      - (* size mb > max *)
        destruct (Nat.eq_dec (size mb') max).
        -- (* size mb' = max: BListMbox_alpha mb' is a list, and is subsumed *)
          exists (BListMbox_set (SetMbox_alpha mb')).
          split.
          --- (* left: show that (m, alpha_PS mb') in deq (alpha mb) *)
            unfold BListMbox_alpha.
            destruct (le_dec (size mb) max).
            ---- (* size mb <= max: impossible *)
              exfalso; apply n; assumption.
            ---- (* size mb > max *)
              apply BListMbox_deq_set_from_set.
              apply SetMbox_deq_sound. assumption.
          --- (* right: show that alpha mb' subsumed alpha_PS mb' *)
            apply BListMbox_subsumed_by_set.
       -- (* size mb' > max: BListMbox_alpha mb' is a set, and is equal *)
        exists (BListMbox_alpha mb').
        split.
        --- (* left *)
          unfold BListMbox_alpha.
          destruct (le_dec (size mb)).
          ---- (* size mb <= max: impossible *)
            exfalso; apply n. apply l.
          ---- (* size mb > max *)
            destruct (le_dec (size mb') max).
            exfalso. inversion l; subst. apply n0; reflexivity.
            rewrite (deq_removes_1 m mb mb') in n1. apply n1.
            apply le_and_neq; assumption. assumption.
            (* set *)
            apply BListMbox_deq_set_from_set.
            apply SetMbox_deq_sound. assumption.
        --- (* right *)
          apply BListMbox_subsumed_same.
    Qed.
    Hint Resolve BListMbox_deq_sound_overapprox.
    Check BListMbox_deq_sound_overapprox.

    Theorem BListMbox_sound :
      abstraction_sound BListMbox BListMbox_alpha BListMbox_subsumed
                        BListMbox_enq BListMbox_deq
                        BListMbox_size BListMboxEmpty.
    Proof.
      unfold abstraction_sound.
      auto.
    Qed.
    Check BListMbox_sound.
  End BList.

  Section MultiSet.
    Definition MultiSetMbox : Type := (Message -> nat).
    Definition MultiSetMboxEmpty : MultiSetMbox := fun m => 0.

    Fixpoint MultiSetMbox_alpha (mb : Mbox) : MultiSetMbox :=
      match mb with
      | MboxEmpty => MultiSetMboxEmpty
      | MboxCons m mb' => (fun m' => if Message_eq_dec2 m m' then S ((MultiSetMbox_alpha mb') m) else (MultiSetMbox_alpha mb') m')
      end.

    Definition MultiSetMbox_subsumed (mb mb' : MultiSetMbox) := mb = mb'.

    Lemma MultiSet_empty_sound :
      empty_sound MultiSetMbox MultiSetMbox_alpha MultiSetMboxEmpty.
    Proof. auto. Qed.
    Hint Resolve MultiSet_empty_sound.
    Check MultiSet_empty_sound.

    Definition MultiSetMbox_enq (m : Message) (mb : MultiSetMbox) : MultiSetMbox :=
      fun m' => if Message_eq_dec2 m m' then S (mb m) else mb m'.

    Lemma MultiSetMbox_enq_sound : enq_sound MultiSetMbox MultiSetMbox_alpha MultiSetMbox_enq.
    Proof.
      unfold enq_sound. intros. unfold MultiSetMbox_enq.
      induction mb as [| m' mb'].
      - (* empty mb *)
        reflexivity.
      - (* non empty mb *)
        simpl. rewrite IHmb'.
        apply functional_extensionality. intro m''.
        destruct (Message_eq_dec2 m' m''); subst.
        -- (* m' = m'' *)
          destruct (Message_eq_dec2 m m''); subst; auto.
          --- (* m = m'' *)
            destruct (Message_eq_dec2 m'' m''); subst; auto.
            ---- exfalso; apply n; reflexivity.
        -- (* m' <> m'' *)
          destruct (Message_eq_dec2 m m''); subst; auto.
          --- (* m = m'' *)
            destruct (Message_eq_dec2 m' m''); subst; auto.
            ---- exfalso; apply n; reflexivity.
    Qed.
    Hint Resolve MultiSetMbox_enq_sound.
    Check MultiSetMbox_enq_sound.

    (*
    Inductive MultiSetMbox_size : (MultiSetMbox -> NatInf -> Prop) :=
    | MultiSetMbox_size_empty : MultiSetMbox_size MultiSetMboxEmpty (Nat 0)
    | MultiSetMbox_size_extend : forall n m mb,
        MultiSetMbox_size mb (Nat n) ->
        MultiSetMbox_size
          (fun m' => if Message_eq_dec2 m m' then S (mb m) else mb m')
          (Nat (S n)).

    Lemma MultiSetMbox_size_enq_S : forall mb m n,
        MultiSetMbox_size (MultiSetMbox_enq m (MultiSetMbox_alpha mb)) (Nat (S n)) ->
        MultiSetMbox_size (MultiSetMbox_alpha mb) (Nat n).
    Proof.
      intros.
      induction mb.
      (* mb empty *)
      simpl. inversion H; subst.
      unfold MultiSetMbox_enq in H0.
*)

    Inductive MultiSetMbox_size : (MultiSetMbox -> NatInf -> Prop) :=
    | MultiSetMbox_size_empty : MultiSetMbox_size MultiSetMboxEmpty (Nat 0)
    | MultiSetMbox_size_enq : forall m mb n,
        MultiSetMbox_size mb (Nat n) ->
        MultiSetMbox_size (MultiSetMbox_enq m mb) (Nat (S n)).

    Lemma empty_not_enq : forall m mb, MultiSetMbox_enq m mb <> MultiSetMboxEmpty.
    Proof.
      red; intros.
      unfold MultiSetMbox_enq in H.
      unfold MultiSetMboxEmpty in H.
      assert (forall (f g : Message -> nat), f = g -> f m = g m).
      intros. rewrite H0. reflexivity.
      apply H0 in H. destruct (Message_eq_dec2 m m).
      inversion H. apply n. reflexivity.
    Qed.

    Lemma MultiSetMbox_alpha_cons : forall mb m,
        MultiSetMbox_alpha (MboxCons m mb) = MultiSetMbox_enq m (MultiSetMbox_alpha mb).
    Proof. reflexivity. Qed.

    Lemma MultiSetMbox_size_unique : forall mb n n',
        MultiSetMbox_size mb (Nat n) ->
        MultiSetMbox_size mb (Nat n') ->
        n = n'.
    Proof.
    Admitted.

    Lemma MultiSetMbox_size_enq_S_oneway : forall mb m n,
        MultiSetMbox_size (MultiSetMbox_alpha mb) (Nat n) ->
        MultiSetMbox_size (MultiSetMbox_enq m (MultiSetMbox_alpha mb)) (Nat (S n)).
    Proof.
      intros.
      inversion H; subst.
      constructor. constructor.
      inversion H; subst. constructor. rewrite H0. assumption.
    Qed.

    Lemma MultiSetMbox_size_enq_S : forall mb m n,
        MultiSetMbox_size (MultiSetMbox_enq m (MultiSetMbox_alpha mb)) (Nat (S n)) ->
        MultiSetMbox_size (MultiSetMbox_alpha mb) (Nat n).
    Proof.
      intros. generalize dependent n; induction mb; intros.
      (* empty *)
      simpl. unfold MultiSetMbox_alpha in H.
      (* assertion *)
      assert (MultiSetMbox_size (MultiSetMbox_enq m MultiSetMboxEmpty) (Nat 1)).
      intros. constructor. constructor.
      (* end of assertion *)
      apply (MultiSetMbox_size_unique (MultiSetMbox_enq m MultiSetMboxEmpty) (S n) 1) in H. inversion H; subst. constructor.
      apply (MultiSetMbox_size_unique (MultiSetMbox_enq m MultiSetMboxEmpty) (S n) 1) in H. inversion H; subst. constructor. constructor.
      apply (MultiSetMbox_size_unique (MultiSetMbox_enq m MultiSetMboxEmpty) (S n) 1) in H. inversion H; subst. constructor. constructor. constructor. constructor.
      rewrite MultiSetMbox_alpha_cons.
      rewrite MultiSetMbox_alpha_cons in H.
      
    Admitted.

    Lemma MultiSetMbox_size_sound : size_sound MultiSetMbox MultiSetMbox_alpha MultiSetMbox_size.
    Proof.
      unfold size_sound. intros mb.
      induction mb; intros.
      (* mbox empty *)
      simpl. inversion H; subst; auto; try constructor.
      exfalso. apply (empty_not_enq m mb). assumption.
      (* mbox not empty *)
      rewrite MultiSetMbox_alpha_cons in H.
      destruct n.
      (* n is nat *)
      destruct n.
      (* n is 0 *)
      inversion H.
      exfalso. apply (empty_not_enq m (MultiSetMbox_alpha mb)).
      apply eq_sym. assumption.
      (* n is S n *)
      simpl. apply NatInf_subsumed_elim_S.
      apply (IHmb (Nat n)).
      apply (MultiSetMbox_size_enq_S mb m n).
      apply H.
      (* n is Inf *)
      constructor.
    Qed.
    Hint Resolve MultiSetMbox_size_sound.
    Check MultiSetMbox_size_sound.

    Inductive MultiSetMbox_deq (mb : MultiSetMbox) : (Ensemble (Message * MultiSetMbox)) :=
    | MultiSetMbox_deq_main : forall m,
        mb m > 0 ->
        In (Message * MultiSetMbox)
           (MultiSetMbox_deq mb) (m, fun m' => if Message_eq_dec2 m m' then (mb m) - 1 else mb m').

    Lemma MultiSetMbox_deq_sound :
      deq_sound MultiSetMbox MultiSetMbox_alpha MultiSetMbox_deq.
    Proof.
      unfold deq_sound. intros.
      destruct mb as [| m'' mb''].
      - (* empty mb: not possible *)
        inversion H.
      - (* non empty mb *)
        inversion H; subst. simpl.
        remember (fun m' => if Message_eq_dec2 m m' then S (MultiSetMbox_alpha mb' m) else MultiSetMbox_alpha mb' m') as mb''.
        (* assertion *)
        assert (MultiSetMbox_alpha mb' = fun m' => if Message_eq_dec2 m m' then (mb'' m) - 1 else mb'' m').
        apply functional_extensionality. intro.
        destruct (Message_eq_dec2 m x); subst.
        destruct (Message_eq_dec2 x x); subst.
        rewrite S_sub1_same. reflexivity.
        exfalso; apply n; reflexivity.
        destruct (Message_eq_dec2 m x); subst.
        exfalso; apply n; reflexivity.
        reflexivity.
        (* end of assertion *)
        rewrite H0.
        constructor.
        rewrite Heqmb''.
        destruct (Message_eq_dec2 m m).
        -- (* m = m *) apply gt_Sn_O.
        -- (* m <> m: impossible *) exfalso; apply n; reflexivity.
    Qed.
    Hint Resolve MultiSetMbox_deq_sound.
    Check MultiSetMbox_deq_sound.

    Theorem MultiSetMbox_sound :
      abstraction_sound MultiSetMbox MultiSetMbox_alpha
                        MultiSetMbox_subsumed
                        MultiSetMbox_enq MultiSetMbox_deq
                        MultiSetMbox_size MultiSetMboxEmpty.
    Proof.
      unfold abstraction_sound.
      auto.
    Qed.
  End MultiSet.

  Section BMultiSet.
    Variable max : nat.
    Variable max_assumption : max > 0.
    Definition BMultiSetMbox : Type := (Message -> NatInf).
    Definition BMultiSetMboxEmpty : BMultiSetMbox := fun m => Nat 0.

    Definition BMultiSetMbox_enq (m : Message) (mb : BMultiSetMbox) : BMultiSetMbox :=
      fun m' => if Message_eq_dec2 m m' then
                  match mb m with
                  | Inf => Inf
                  | Nat n => if lt_dec n max then Nat (S n) else Inf
                  end
                else mb m'.

    Fixpoint BMultiSetMbox_alpha (mb : Mbox) : BMultiSetMbox :=
      match mb with
      | MboxEmpty => BMultiSetMboxEmpty
      | MboxCons m mb' => BMultiSetMbox_enq m (BMultiSetMbox_alpha mb')
      end.

    Definition BMultiSetMbox_subsumed (mb mb' : BMultiSetMbox) := mb = mb'.

    Lemma BMultiSetMbox_empty_sound :
      empty_sound BMultiSetMbox BMultiSetMbox_alpha BMultiSetMboxEmpty.
    Proof. auto. Qed.
    Hint Resolve BMultiSetMbox_empty_sound.
    Check BMultiSetMbox_empty_sound.

    Lemma BMultiSetMbox_enq_sound :
      enq_sound BMultiSetMbox BMultiSetMbox_alpha BMultiSetMbox_enq.
    Proof.
      unfold enq_sound. intros.
      induction mb as [| m' mb'].
      - (* empty mb *)
        reflexivity.
      - (* non empty mb *)
        simpl. rewrite IHmb'. unfold BMultiSetMbox_enq.
        apply functional_extensionality. intro m''.
        destruct (Message_eq_dec2 m' m''); subst.
        -- (* m' == m'' *)
          destruct (Message_eq_dec2 m m''); subst; auto.
          --- (* m = m'' *)
            destruct (Message_eq_dec2 m'' m''); subst; auto.
            ---- exfalso; apply n; reflexivity.
        -- (* m' <> m'' *)
          destruct (Message_eq_dec2 m m''); subst; auto.
          --- (* m = m'' *)
            destruct (Message_eq_dec2 m' m''); subst; auto.
            ---- exfalso; apply n; reflexivity.
    Qed.
    Hint Resolve BMultiSetMbox_enq_sound.
    Check BMultiSetMbox_enq_sound.

    Inductive BMultiSetMbox_deq (mb : BMultiSetMbox) : (Ensemble (Message * BMultiSetMbox)) :=
    | BMultiSetMbox_deq_finite : forall m n,
        mb m = Nat n ->
        n > 0 ->
        In (Message * BMultiSetMbox)
           (BMultiSetMbox_deq mb) (m, fun m' => if Message_eq_dec2 m m' then Nat (n - 1) else mb m')
    | BMultiSetMbox_deq_infinite_stay : forall m,
        mb m = Inf ->
        In (Message * BMultiSetMbox)
           (BMultiSetMbox_deq mb) (m, mb)
    | BMultiSetMbox_deq_infinite_back : forall m,
        mb m = Inf ->
        In (Message * BMultiSetMbox)
           (BMultiSetMbox_deq mb) (m, fun m' => if Message_eq_dec2 m m' then Nat max else mb m').

    Lemma O_or_gt_dec : forall n, {n = 0} + {n > 0}.
    Proof.
      intros. destruct n; auto.
      right. apply gt_Sn_O.
    Qed.

    Lemma alpha_bounded : forall m mb n,
        Nat n = BMultiSetMbox_alpha mb m -> n <= max.
    Proof.
      intros m mb. induction mb; intros.
      (* empty mb *)
      inversion H. apply Peano.le_0_n.
      (* non empty mb *)
      simpl in H.
      unfold BMultiSetMbox_enq in H.
      destruct (Message_eq_dec2 m0 m); subst.
      (* m = m0 *)
      destruct (BMultiSetMbox_alpha mb m) as [n'|]; subst.
      (* BMultiSetMbox_alpha mb m = Nat n' *)
      destruct (lt_dec n' max); subst.
      (* n' < max *)
      inversion H; subst.
      apply lt_le_S. assumption.
      (* n' >= max *)
      inversion H.
      (* BListSetMbox_alpha mb m = Inf *)
      inversion H.
      (* m <> m0 *)
      apply IHmb. assumption.
    Qed.

    Lemma BMultiSetMbox_deq_sound :
      deq_sound BMultiSetMbox BMultiSetMbox_alpha BMultiSetMbox_deq.
    Proof.
      unfold deq_sound. intros.
      destruct mb as [| m'' mb''].
      - (* mb empty: not possible *)
        inversion H.
      - (* mb non empty *)
        inversion H; subst. simpl.
        unfold BMultiSetMbox_enq.
        remember (BMultiSetMbox_alpha mb') as amb'.
        remember (amb' m).
        destruct n.
        -- (* amb' m = Nat n *)
          destruct (lt_dec n max).
          --- (* n <= max *)
            remember (fun m' => if Message_eq_dec2 m m' then Nat (S n) else amb' m') as amb''.
            (* assertion *)
            assert (amb'' m = Nat (S n)).
            rewrite Heqamb''. destruct (Message_eq_dec2 m m). reflexivity.
            exfalso; apply n0; reflexivity.
            (* end of assertion *)
            (* assertion *)
            assert (amb' = fun m' => if Message_eq_dec2 m m' then Nat (S n - 1) else amb'' m').
            apply functional_extensionality. intro.
            rewrite Heqamb''. destruct (Message_eq_dec2 m x); subst. apply eq_sym.
            rewrite S_sub1_same. assumption. reflexivity.
            (* end of assertion *)
            rewrite H1.
            apply BMultiSetMbox_deq_finite. (* or: constructor. *)
            assumption. apply gt_Sn_O.
          --- (* n >= max *)
            rewrite Heqamb' in Heqn.
            (* assertion *)
            assert (n = max).
            apply ngt_ge_eq. assumption. apply (alpha_bounded m mb' n Heqn).
            (* end of assertion *)
            remember (fun m' => if Message_eq_dec2 m m' then Inf else amb' m') as amb''.
            (* assertion *)
            assert (amb' = fun m' => if Message_eq_dec2 m m' then Nat max else amb'' m').
            apply functional_extensionality; intro.
            destruct (Message_eq_dec2 m x); subst. apply eq_sym. assumption.
            destruct (Message_eq_dec2 m x); subst. exfalso. apply n1; reflexivity.
            reflexivity.
            (* end of assertion *)
            rewrite H1.
            constructor. rewrite Heqamb''.
            destruct (Message_eq_dec2 m m). reflexivity. exfalso; apply n1; reflexivity.
        -- (* amb' m = Inf *)
          (* assertion *)
          assert (amb' = fun m' => if Message_eq_dec2 m m' then Inf else amb' m').
          apply functional_extensionality; intro.
          destruct (Message_eq_dec2 m x); subst.
          apply eq_sym. assumption. reflexivity.
          (* end of assertion *)
          rewrite <- H0.
      constructor. apply eq_sym. assumption.
    Qed.
    Hint Resolve BMultiSetMbox_deq_sound.
    Check BMultiSetMbox_deq_sound.

    (* Same deq as in the implementation *)
    Inductive BMultiSetMbox_deq_impl (mb : BMultiSetMbox) : (Ensemble (Message * BMultiSetMbox)) :=
    | BMultiSetMbox_deq_impl_finite : forall m n,
        mb m = Nat n ->
        n > 0 ->
        In (Message * BMultiSetMbox)
           (BMultiSetMbox_deq_impl mb) (m, fun m' => if Message_eq_dec2 m m' then Nat (n - 1) else mb m')
    | BMultiSetMbox_deq_impl_infinite_stay : forall m,
        mb m = Inf ->
        In (Message * BMultiSetMbox)
           (BMultiSetMbox_deq_impl mb) (m, mb)
    | BMultiSetMbox_deq_impl_infinite_remove : forall m,
        mb m = Inf ->
        In (Message * BMultiSetMbox)
           (BMultiSetMbox_deq_impl mb) (m, fun m' => if Message_eq_dec2 m m' then Nat 0 else mb m').

    Definition BMultiSetMbox_subsumed_impl (mb mb' : BMultiSetMbox) := forall m, NatInf_subsumed_abs (mb m) (mb' m).

    Lemma BMultiSetMbox_subsumed_impl_same : forall mb, BMultiSetMbox_subsumed_impl mb mb.
    Proof.
      unfold BMultiSetMbox_subsumed_impl. intros.
      destruct (mb m); constructor.
    Qed.

    Lemma BMultiSetMbox_deq_impl_sound_overapprox :
      deq_sound_overapprox BMultiSetMbox BMultiSetMbox_alpha BMultiSetMbox_subsumed_impl BMultiSetMbox_deq_impl.
    Proof.
      unfold deq_sound_overapprox. intros. destruct mb; inversion H; subst.
      (* mb not empty *)
      simpl.
      unfold BMultiSetMbox_enq.
      remember (BMultiSetMbox_alpha mb') as amb'.
      remember (amb' m).
      destruct n.
      - (* amb' m = Nat n *)
        destruct (lt_dec n max).
        -- (* n <= max *)
          remember (fun m' => if Message_eq_dec2 m m' then Nat (S n) else amb' m') as amb''.
          (* assertion *)
          assert (amb'' m = Nat (S n)).
          rewrite Heqamb''. destruct (Message_eq_dec2 m m); auto.
          exfalso; apply n0; reflexivity.
          (* end of assertion *)
          (* assertion *)
          assert (amb' = fun m' => if Message_eq_dec2 m m' then Nat (S n - 1) else amb'' m').
          apply functional_extensionality; intro.
          rewrite Heqamb''. destruct (Message_eq_dec2 m x); subst. apply eq_sym.
          rewrite S_sub1_same. assumption. reflexivity.
          (* end of assertion *)
          rewrite H1.
          exists (fun m' => if Message_eq_dec2 m m' then Nat (S n - 1) else amb'' m').
          split.
          --- (* left *)
            constructor. assumption. apply gt_Sn_O.
          --- (* right *)
            apply BMultiSetMbox_subsumed_impl_same.
        -- (* n >= max *)
          rewrite Heqamb' in Heqn.
          (* assertion *)
          assert (n = max).
          apply ngt_ge_eq. assumption. apply (alpha_bounded m mb' n Heqn).
          remember (fun m' => if Message_eq_dec2 m m' then Inf else amb' m') as amb''.
          (* end of assertion *)
          exists amb''.
          split.
          --- (* left *)
            constructor. rewrite Heqamb''. destruct (Message_eq_dec2 m m); auto.
            exfalso; apply n1; reflexivity.
          --- (* right *)
            unfold BMultiSetMbox_subsumed_impl. intros.
            rewrite Heqamb''. rewrite Heqamb'.
            destruct (Message_eq_dec2 m m0); subst.
            ---- (* m = m0 *)
              rewrite <- Heqn.
              constructor.
            ---- (* m <> m0 *)
              apply BMultiSetMbox_subsumed_impl_same.
      - (* amb' m = Inf *)
        (* assertion *)
        assert (amb' = fun m' => if Message_eq_dec2 m m' then Inf else amb' m').
        apply functional_extensionality; intro.
        destruct (Message_eq_dec2 m x); subst.
        apply eq_sym. assumption. reflexivity.
        (* end of assertion *)
        exists amb'.
        rewrite <- H0.
        split. constructor. apply eq_sym. assumption.
        apply BMultiSetMbox_subsumed_impl_same.
    Qed.

    Definition to_ms (mb : BMultiSetMbox) (pf : ~ exists m, mb m = Inf) : MultiSetMbox :=
      fun m => match mb m with
               | Nat n => n
               | Inf => 0 (* should be disproved by pf *)
               end.

    Inductive BMultiSetMbox_size : (BMultiSetMbox -> NatInf -> Prop) :=
    | BMultiSetMbox_size_inf : forall mb,
        (exists m, mb m = Inf) -> BMultiSetMbox_size mb Inf
    | BMultiSetMbox_size_fin : forall mb n (pf : (~ exists m, mb m = Inf)),
        MultiSetMbox_size (to_ms mb pf ) (Nat n) ->
        BMultiSetMbox_size mb (Nat n).

    Lemma BMultiSetMbox_size_sound : size_sound BMultiSetMbox BMultiSetMbox_alpha BMultiSetMbox_size.
      (* One way to solve it is to prove that BMultiSetMbox_size is a sound approximation of MultiSetMbox_size, and then to follow by MultiSetMbox_size_sound *)
    Admitted.
    Hint Resolve BMultiSetMbox_size_sound.
    Theorem BMultiSetMbox_sound :
      abstraction_sound BMultiSetMbox BMultiSetMbox_alpha
                        BMultiSetMbox_subsumed
                        BMultiSetMbox_enq BMultiSetMbox_deq
                        BMultiSetMbox_size BMultiSetMboxEmpty.
    Proof. unfold abstraction_sound. auto. Qed.
  End BMultiSet.

  Section Graph.
    Inductive Graph :=
    | GraphEmpty : Graph
    | GraphNonEmpty : Ensemble Message -> Ensemble (Message * Message) -> Message -> Message -> Graph.

    Definition Graph_enq (m : Message) (mb : Graph) : Graph :=
      match mb with
      | GraphEmpty => GraphNonEmpty (Singleton _ m) (Empty_set _) m m
      | GraphNonEmpty V E f l => GraphNonEmpty (Add _ V m) (Add _ E (f, m)) m l
      end.

    Fixpoint Graph_alpha_helper (mb : Mbox) (amb : Graph) : Graph :=
      match mb with
      | MboxEmpty => amb
      | MboxCons m mb' => Graph_alpha_helper mb' (Graph_enq m amb)
      end.
    (* Note: alpha (m :: mb) = Graph_enq m (Graph_alpha mb') would be *incorrect*, because we
       preserve order, and that would therefore represent the mailbox in
       reverse order, since enqing is performed at the back *)
    Definition Graph_alpha (mb : Mbox) : Graph := Graph_alpha_helper mb GraphEmpty.

    Lemma Graph_empty_sound :
      empty_sound Graph Graph_alpha GraphEmpty.
    Proof. auto. Qed.
    Check Graph_empty_sound.

    Lemma Graph_alpha_helper_sound : forall m mb amb,
        Graph_alpha_helper (enq m mb) amb =
        Graph_enq m (Graph_alpha_helper mb amb).
    Proof.
      intros. generalize dependent amb. induction mb; auto.
      intros.
      simpl.
      rewrite IHmb. reflexivity.
    Qed.

    Lemma Graph_enq_sound :
      enq_sound Graph Graph_alpha Graph_enq.
    Proof.
      unfold enq_sound. intros.
      unfold Graph_alpha. rewrite Graph_alpha_helper_sound. reflexivity.
    Qed.
    Check Graph_enq_sound.

    Lemma Graph_enq_dont_change_last : forall V V' E E' f f' l l' m,
        Graph_enq m (GraphNonEmpty V E f l) = GraphNonEmpty V' E' f' l' ->
        l = l'.
    Proof.
      intros. simpl in H. inversion H. reflexivity.
    Qed.

    Lemma Graph_enq_change_first : forall V V' E E' f f' l l' m amb amb',
        Graph_enq m amb = GraphNonEmpty V E f l ->
        Graph_enq m amb' = GraphNonEmpty V' E' f' l' ->
        f = f'.
    Proof.
      destruct amb; destruct amb'; intros.
      rewrite H0 in H. inversion H; subst. reflexivity.
      inversion H; subst. inversion H0; subst. reflexivity.
      inversion H; subst. inversion H0; subst. reflexivity.
      inversion H; subst. inversion H0; subst. reflexivity.
    Qed.

    Lemma Graph_enq_monotone : forall V V' E E' f f' l l' m,
        Graph_enq m (GraphNonEmpty V E f l) = GraphNonEmpty V' E' f' l' ->
        l = l' /\ Included _ V V' /\ Included _ E E'.
    Admitted.

    Lemma Graph_alpha_helper_same_f : forall m mb amb amb' V V' E E' f f' l l' ,
        Graph_alpha_helper (MboxCons m mb) amb = GraphNonEmpty V E f l->
        Graph_alpha_helper (MboxCons m mb) amb' = GraphNonEmpty V' E' f' l'  ->
        f = f'.
    Proof.
      intros. generalize dependent H. generalize dependent H0. generalize dependent amb. generalize dependent amb'.
      simpl. induction mb; simpl.
      intros. eapply Graph_enq_change_first.
      apply H. apply H0.
      intros.
    Admitted.

    Inductive Graph_deq : Graph -> (Ensemble (Message * Graph)) :=
    | Graph_deq_last : forall V E f l,
        ~ (exists m, In (Message * Message) E (l, m)) ->
        In (Message * Graph)
           (Graph_deq (GraphNonEmpty V E f l))
           (l, GraphEmpty)
    | Graph_deq_main : forall V E f l l',
        In (Message * Message) E (l, l') ->
        In (Message * Graph)
           (Graph_deq (GraphNonEmpty V E f l))
           (l, GraphNonEmpty V E f l').
    Lemma Grap_deq_sound :
      deq_sound Graph Graph_alpha Graph_deq.
    Proof.
      unfold deq_sound. intros.
      destruct mb; inversion H; subst; simpl.
      (* non empty mb *)
      unfold Graph_alpha. simpl.
      remember (GraphNonEmpty (Singleton Message m) (Empty_set (Message * Message)) m m) as foo.
      induction mb'; intros.
      - simpl. subst. constructor. (* empty set is empty so that is easy to show *) admit.
      - simpl.  simpl in IHmb'.
    Admitted.
  End Graph.
End Mboxes.
