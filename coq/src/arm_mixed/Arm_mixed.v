(******************************************************************************)
(** * Definition of the ARMv8.3 memory model                                  *)
(* a fragment of the full model                                                *)
(* (omitting dmb.st, LDAR, and isb that are not used in compiled programs)    *)
(******************************************************************************)
From hahn Require Import Hahn.
From imm Require Import Events.
Require Import Execution_m.
(* Require Import Execution_eco. *)

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Arm_mixed.

Variable G : execution_m.

Notation "'E'" := G.(acts_set).
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rfb'" := G.(rfb).
Notation "'cob'" := G.(cob).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rf_on'" := G.(rf_on).
Notation "'cob_on'" := G.(cob_on).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'deps'" := G.(deps).

(* Notation "'eco'" := G.(eco). *)

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'W_ex'" := (W_ex G).

Notation "'L'" := (W ∩₁ (fun a => is_true (is_rel lab a))).
Notation "'Q'" := (R ∩₁ (fun a => is_true (is_acq lab a))).
Notation "'A'" := (R ∩₁ (fun a => is_true (is_sc  lab a))).

Notation "'F^ld'" := (F ∩₁ (fun a => is_true (is_acq lab a))).
Notation "'F^sy'" := (F ∩₁ (fun a => is_true (is_rel lab a))).

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

Definition fr_on n := (rf_on n) ^{-1} ⨾ (cob_on n).
Definition fr x y := exists n, fr_on n x y.

Definition rfe := rf \ sb.
Definition coe := co \ sb.
Definition fre := fr \ sb.
Definition rfi := rf ∩ sb.
Definition coi := co ∩ sb.
Definition fri := fr ∩ sb.

(* ca? *)
Definition ca := fr ∪ co.

(* Observed-by *)
Definition obs := rfe ∪ coe ∪ fre.

(* Dependency-ordered-before *)
Definition dob :=
   (addr ∪ data) ⨾ rfi^?
 ∪ (ctrl ∪ data) ⨾ ⦗W⦘ ⨾ coi^?
 ∪ addr ⨾ sb ⨾ ⦗W⦘.

(* Atomic-ordered-before *)
Definition aob :=
  rmw ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗Q⦘.

(* Barrier-ordered-before *)
Definition bob :=
    sb ⨾ ⦗F^sy⦘ ⨾ sb
  ∪ ⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘ ⨾ sb
  ∪ ⦗Q⦘ ⨾ sb
  ∪ sb ⨾ ⦗L⦘ ⨾ coi^?
  ∪ ⦗L⦘ ⨾ sb ⨾ ⦗A⦘.

Definition ob := obs ∪ dob ∪ aob ∪ bob.

Definition polocb n x y := sb x y /\ overlap_on G n x y.

(******************************************************************************)
(** ** Consistency *)
(******************************************************************************)

Definition rmw_atomicity := rmw ∩ (fre ⨾ coe) ⊆ ∅₂.

(* internal visibility *)
Definition sc_per_loc := forall n, acyclic (polocb n ∪ fr_on n ∪ cob_on n ∪ rf_on n).

Implicit Type WF : Wf_m G.
Implicit Type COMP : complete G.
Implicit Type ATOM : rmw_atomicity.
Implicit Type SC_PER_LOC : sc_per_loc.

Definition ArmConsistent_m :=
  ⟪ WF : Wf_m G ⟫ /\
  ⟪ COMP : complete G ⟫ /\
  ⟪ SC_PER_LOC: sc_per_loc ⟫ /\
  ⟪ POWER_ATOMICITY : rmw_atomicity ⟫ /\
  ⟪ SCA : irreflexive (rf⨾fr) ⟫ /\
  ⟪ ACYC : acyclic ob ⟫.

Implicit Type CON : ArmConsistent_m.


(******************************************************************************)
(** ** Additional derived relations to simlify our proofs *)
(******************************************************************************)

Definition obs' := rfe ∪ co ∪ fr.

Definition bob' :=
    bob ∪ ⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘ 
        ∪ sb ⨾ ⦗F^sy⦘ 
        ∪ ⦗F^ld ∪₁ F^sy⦘ ⨾ sb.

Lemma rfe_E x y :
  Wf_m G -> rfe x y -> E x /\ E y.
Proof.
  intros WF H.
  destruct H.
  apply rf_E.
  apply WF.
  apply H.
Qed.

Lemma co_E x y :
  Wf_m G -> co x y -> E x /\ E y.
Proof.
  intros WF H.
  apply WF in H.
  destruct H as [x_ [[H11 H12] [y_ [H21 [H221 H222]]]]].
  rewrite H221 in H222.
  split; easy.
Qed.

Lemma coe_E x y :
  Wf_m G -> coe x y -> E x /\ E y.
Proof.
  intros WF H.
  destruct H.
  apply co_E.
  apply WF.
  apply H.
Qed.

Lemma fr_E x y :
  Wf_m G -> fr x y -> E x /\ E y.
Proof.
  intros WF H.
  destruct H as [n H].
  unfold fr_on in H.
  destruct H as [z [H1 H2]].
  unfold "⁻¹" in H1.
  apply rf_on_rf in H1.
  apply cob_on_co in H2.
  apply co_E in H2.
  apply rf_E in H1.
  split. apply H1. apply H2.
  apply WF. apply WF.
Qed.

Lemma fre_E x y :
  Wf_m G -> fre x y -> E x /\ E y.
Proof.
  intros WF H.
  destruct H.
  apply fr_E; assumption.
Qed.

Lemma obs_E x y :
  Wf_m G -> obs x y -> E x /\ E y.
Proof.
  intros WF H.
  destruct H as [[H|H]|H].
  - apply rfe_E; assumption.
  - apply coe_E; assumption.
  - apply fre_E; assumption.
Qed.

End Arm_mixed.
