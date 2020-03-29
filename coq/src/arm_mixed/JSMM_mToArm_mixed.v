(******************************************************************************)
(** * Compilation correctness from JS to ARMv8                                *)
(******************************************************************************)

From hahn Require Import Hahn.
From imm Require Import Events.
Require Import Execution_m.
Require Import JSMM_m.
Require Import Arm_mixed.
(* Require Import Execution_eco. *)

Set Implicit Arguments.
Remove Hints plus_n_O.

Section JSMM_mToArm_mixed.

Variable G : execution_m.

Notation "'E'" := G.(acts_set).
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rfb'" := G.(rfb).
Notation "'cob'" := G.(cob).
Notation "'rf'" := G.(rf).
Notation "'rfe'" := G.(rfe).
Notation "'sw'" := G.(sw).
Notation "'hb'" := G.(hb).
Notation "'co'" := G.(co).
Notation "'coe'" := G.(coe).
Notation "'rf_on'" := G.(rf_on).
Notation "'cob_on'" := G.(cob_on).
Notation "'fr_on'" := G.(fr_on).
Notation "'fr'" := G.(fr).
Notation "'fre'" := G.(fre).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'deps'" := G.(deps).
Notation "'bob'" := G.(bob).
Notation "'obs'" := G.(obs).
Notation "'ob'" := G.(ob).

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

Notation "'SC'" := (fun a => is_true (is_sc  lab a)).

Notation "'F^ld'" := (F ∩₁ (fun a => is_true (is_acq lab a))).
Notation "'F^sy'" := (F ∩₁ (fun a => is_true (is_rel lab a))).

Hypothesis CON: ArmConsistent_m G.

Lemma A_in_Q :
  A ⊆₁ Q.
Proof.
  intros x H.
  unfold is_sc in H.
  unfold is_acq.
  destruct H as [H1 H2].
  econstructor.
  apply H1.
  unfold mode_le.
  case (mod lab x) eqn: HH; easy.
Qed.

Lemma obs_sb_strict_acyclic_helper x y :
  (L ∪₁ A) x -> (sb ⨾ (⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘)⁺)⁺ x y ->
    ((⦗L ∪₁ A⦘ ⨾ sb ⨾ ⦗L ∪₁ A⦘) ⨾ (⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘)⁺)⁺ x y.
Proof.
  intros H1 H.
  induction H as [x y H | x y z H Ha Hb Hc].
  - econstructor 1.
    destruct H as [z [H11 H12]].
    econstructor.
    split.
    + econstructor.
      split. { econstructor. reflexivity. apply H1. }
      econstructor.
      split. { apply H11. }
      apply inclusion_ct_seq_eqv_l in H12.
      destruct H12 as [z_ [[H121 H122] H13]].
      econstructor. reflexivity. assumption.
    + apply H12.
  - assert ((L ∪₁ A) y) as Haa. {
      assert ( domb ((sb ⨾ (⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘)⁺)⁺) (L ∪₁ A) ) as Haa. {
        apply ct_domb. apply seq_domb. apply ct_domb. apply seq_domb. apply domb_eqv.
      } 
      eapply Haa. apply H.
    }
    econstructor 2.
    + apply Ha. apply H1.
    + apply Hc. apply Haa.
Qed.

Lemma atomic_sb_in_bob :
  (⦗L ∪₁ A⦘ ⨾ sb ⨾ ⦗L ∪₁ A⦘) ⊆ bob.
Proof.
  intros x y H.
  unfold Arm_mixed.bob.
  destruct H as [x_ [[H11 H12] [y_ [H2 [H31 H32]]]]].
  rewrite <- H11 in H2.
  rewrite H31 in H2, H32.
  destruct H12 as [H12 | H12].
  - destruct H32 as [H32 | H32].
    + left. right. econstructor.
      split. { apply H2. }
      econstructor.
      split. { econstructor. reflexivity. apply H32. }
      econstructor. reflexivity.
    + right. econstructor.
      split. { econstructor. reflexivity. apply H12. }
      econstructor.
      split. { apply H2. }
      econstructor. reflexivity. apply H32.
  - left. left. right.
    econstructor.
    split. { econstructor. reflexivity.
      unfold is_acq. unfold is_sc in H12.
      destruct H12 as [H121 H122].
      econstructor. { apply H121. }
      unfold mode_le.
      case (mod lab x) eqn: H; try easy.
    }
    apply H2.
Qed.

Lemma atomic_sb_in_ob :
  (⦗L ∪₁ A⦘ ⨾ sb ⨾ ⦗L ∪₁ A⦘) ⊆ ob.
Proof.
  intros x y H.
  unfold Arm_mixed.ob.
  right. apply atomic_sb_in_bob. apply H.
Qed.

Lemma atomic_obs_in_ob :
  (⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘) ⊆ ob.
Proof.
  intros x y H.
  unfold Arm_mixed.ob.
  left. left. left.
  destruct H as [x_ [[H11 H12] [y_ [H21 [H221 H222]]]]].
  rewrite H221 in H21.
  rewrite <- H11 in H21.
  apply H21.
Qed.

Lemma obs_sb_strict_acyclic_helper1 :
  (⦗L ∪₁ A⦘ ⨾ sb ⨾ ⦗L ∪₁ A⦘) ⨾ (⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘)⁺ ⊆ ob⁺.
Proof.
  intros x y H.
  eapply inclusion_seq_mon in H.
  apply ct_ct.
  apply H.
  - eapply inclusion_trans.
    + apply atomic_sb_in_ob.
    + apply ct_step.
  - apply inclusion_t_t. apply atomic_obs_in_ob.
Qed.

Lemma obs_sb_strict_acyclic_helper2 :
  ((⦗L ∪₁ A⦘ ⨾ sb ⨾ ⦗L ∪₁ A⦘) ⨾ (⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘)⁺)⁺ ⊆ ob⁺.
Proof.
  intros x y H.
  apply ct_of_ct.
  eapply inclusion_t_t.
  apply obs_sb_strict_acyclic_helper1.
  apply H.
Qed.

Lemma obs_sb_strict_acyclic :
  acyclic ((⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘) ∪ sb).
Proof.
  apply acyclic_ut. { apply sb_trans. }
  split.
  - intros x H.
    apply inclusion_ct_seq_eqv_l in H.
    apply inclusion_seq_eqv_l in H.
    apply inclusion_ct_seq_eqv_r in H.
    apply inclusion_seq_eqv_r in H.
    unfold ArmConsistent_m in CON.
    destruct CON as [CON1 [CON2 [CON3 [CON4 [CON5 CON6]]]]].
    eapply CON6.
    unfold Arm_mixed.ob.
    rewrite <- (rel_extensionality (ct_of_union_ct_l _ _)).
    rewrite <- (rel_extensionality (ct_of_union_ct_l (obs ∪ dob G) _)).
    rewrite <- (rel_extensionality (ct_of_union_ct_l (obs) _)).
    econstructor. left.
    econstructor. left.
    econstructor. left.
    apply H.
  - split. { apply sb_irr. }
    intros x H.
    assert (domb (sb ⨾ (⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘)⁺)⁺ (L ∪₁ A)) as Ha. {
      apply ct_domb. apply seq_domb. apply ct_domb. apply seq_domb. apply domb_eqv.
    }
    assert (((⦗L ∪₁ A⦘ ⨾ sb ⨾ ⦗L ∪₁ A⦘) ⨾ (⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘)⁺)⁺ x x) as Haa. {
      apply obs_sb_strict_acyclic_helper.
      eapply Ha. apply H. apply H.
    }
    apply obs_sb_strict_acyclic_helper2 in Haa.
    eapply CON.
    apply Haa.
Qed.

Definition tot_ := (tot_ext acts ((⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘) ∪ sb)).

Definition tot := ⦗E⦘ ⨾ tot_ ⨾ ⦗E⦘.

Lemma tot__wf1 : strict_total_order E tot_.
Proof.
  unfold strict_total_order.
  split.
  - econstructor.
    + apply tot_ext_irr. apply obs_sb_strict_acyclic.
    + apply tot_ext_trans.
  - apply tot_ext_total.
Qed.

Lemma tot_wf1 : strict_total_order E tot.
Proof.
  pose tot__wf1 as P.
  unfold strict_total_order.
  unfold strict_total_order in P.
  destruct P as [[P11 P12] P2].
  split.
  - unfold strict_partial_order.
    split.
    + unfold irreflexive.
      intros x H.
      apply P11 with x.
      destruct H as [x_ [[H11 H12] [x__ [H21 [H221 H222]]]]].
      rewrite <- H11 in H21.
      rewrite H221 in H21,H222.
      apply H21.
    + unfold transitive.
      intros x y z H1 H2.
      destruct H1 as [x_ [[H11 H12] [x__ [H21 [H221 H222]]]]].
      rewrite <- H11 in H21.
      rewrite H221 in H21,H222.
      clear x_ x__ H221 H11.
      destruct H2 as [x_ [[H311 H312] [x__ [H321 [H3221 H3222]]]]].
      rewrite <- H311 in H321.
      rewrite H3221 in H321,H3222.
      clear x_ x__ H3221 H311.
      assert (tot_ x z) as Ha. {
        eapply P12.
        apply H21. apply H321.
      }
      econstructor.
      split. { econstructor. reflexivity. assumption. }
      econstructor.
      split. { apply Ha. }
      econstructor. reflexivity. apply H3222.
  - unfold is_total.
    intros a H1 b H3 H4.
    assert (tot_ a b \/ tot_ b a) as Ea. {
      unfold is_total in P2.
      specialize P2 with a b.
      apply P2; assumption.
    }
    destruct Ea as [Ea | Ea].
    + left. unfold tot.
      econstructor.
      split. { econstructor. reflexivity. assumption. }
      econstructor.
      split. { apply Ea. }
      econstructor. reflexivity. apply H3.
    + right. unfold tot.
      econstructor.
      split. { econstructor. reflexivity. assumption. }
      econstructor.
      split. { apply Ea. }
      econstructor. reflexivity. apply H1.
Qed.

Lemma tot__wf2 : ⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘ ⊆ tot_.
Proof.
  intros x y H.
  eapply tot_ext_extends.
  left. apply H.
Qed.

Lemma tot_wf2 : ⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘ ⊆ tot.
Proof.
  intros x y H.
  assert (tot_ x y) as Ha. { apply tot__wf2. apply H. }
  destruct H as [x_ [[H11 H12] [y_ [H221 [H2221 H2222]]]]].
  rewrite <- H11 in H221.
  rewrite H2221 in H2222,H221.
  econstructor.
  split. { econstructor. reflexivity. apply obs_E in H221. apply H221. apply CON. }
  econstructor.
  split. { apply Ha. }
  econstructor. reflexivity. apply obs_E in H221. apply H221. apply CON.
Qed.

Lemma tot__wf3 : sb ⊆ tot_.
Proof.
  intros x y H.
  eapply tot_ext_extends.
  right. apply H.
Qed.

Lemma tot_wf3 : sb ⊆ tot.
Proof.
  intros x y H.
  econstructor.
  split. { econstructor. reflexivity. apply (sb_E H). }
  econstructor.
  split. { apply tot__wf3. apply H. }
  econstructor. reflexivity. apply (sb_E H).
Qed.

Lemma tot_E x y :
  tot x y -> E x /\ E y.
Proof.
  intros H.
  destruct H as [x_ [[H11 H12] [y_ [H2 [H31 H32]]]]].
  rewrite <- H11 in H2.
  rewrite H31 in H2,H32.
  split; assumption.
Qed.

Lemma tf_wf_any : functional (rf⁻¹ ∩ same_range G).
Proof.
  unfold functional.
  intros x y z. 
  intros H1 H2.
  destruct CON as [CON1 [_ [_ [_ [CON5 _]]]]].
  destruct H1 as [H11 H12].
  destruct H2 as [H21 H22].
  unfold "⁻¹" in H11,H21.
  apply rf_rf_on in H11.
  apply rf_rf_on in H21.
  destruct H11 as [n H11].
  destruct H21 as [m H21].
  pose (wf_cob_total CON1 n) as P.
  unfold is_total in P.
  assert ((E ∩₁ W ∩₁ (fun x : actid => In n (range G x))) y) as Haa. {
    econstructor. econstructor.
    - apply rf_on_rf in H11. apply rf_E in H11. apply H11. apply CON1.
    - apply rf_on_rf in H11. eapply rf_w_r. apply CON1. apply H11.
    - apply rf_on_overlap_on in H11. unfold overlap_on in H11. unfold overlap in H11.
      apply list_intersect_rP in H11. apply H11. apply CON1.
  }
  assert ((E ∩₁ W ∩₁ (fun x : actid => In n (range G x))) z) as Haaa. {
    econstructor. econstructor.
    - apply rf_on_rf in H21. apply rf_E in H21. apply H21. apply CON1.
    - apply rf_on_rf in H21. apply rf_w_r in H21. apply H21. apply CON1.
    - apply rf_on_overlap_on in H11. unfold overlap_on in H11. unfold overlap in H11.
      apply list_intersect_rP in H11. unfold same_range in H22. rewrite H22 in H11. apply H11.
      apply CON1.
  }
  assert ((cob_on n y z \/ cob_on n z y) \/ y = z) as H. {
    case classic with (y = z) as [Y | N].
    - right. assumption.
    - left. apply P. apply Haa. apply Haaa. assumption.
  }
  clear P Haa Haaa.
  destruct H as [[H1|H2]|H3].

  - assert (fr x z) as Hfr. { constructor 1 with n. econstructor. split.
                              unfold "⁻¹". apply H11. apply H1. }
    apply rf_on_rf in H21.
    exfalso. apply CON5 with z.
    econstructor 1 with x. split; assumption.

  - pose (wf_cob_total CON1 m) as P.
    unfold is_total in P.
    assert ((E ∩₁ W ∩₁ (fun x : actid => In m (range G x))) z) as Haa. {
      econstructor. econstructor.
      - apply rf_on_rf in H21. apply rf_E in H21. apply H21. apply CON1.
      - apply rf_on_rf in H21. eapply rf_w_r. apply CON1. apply H21.
      - apply rf_on_overlap_on in H21. unfold overlap_on in H21. unfold overlap in H21.
        apply list_intersect_rP in H21. apply H21. apply CON1.
    }
    assert ((E ∩₁ W ∩₁ (fun x : actid => In m (range G x))) y) as Haaa. {
      econstructor. econstructor.
      - apply rf_on_rf in H11. apply rf_E in H11. apply H11. apply CON1.
      - apply rf_on_rf in H11. apply rf_w_r in H11. apply H11. apply CON1.
      - apply rf_on_overlap_on in H21. unfold overlap_on in H21. unfold overlap in H21.
        apply list_intersect_rP in H21. unfold same_range in H12. rewrite H12 in H21. apply H21.
        apply CON1.
    }
    assert ((cob_on m z y \/ cob_on m y z) \/ z = y) as H. {
      case classic with (z = y) as [Y | N].
      - right. assumption.
      - left. apply P. apply Haa. apply Haaa. assumption.
    }
    clear P Haa Haaa.
    destruct H as [[H|H]|H].
    + assert (fr x y) as Hfr. { constructor 1 with m. econstructor. split.
                              unfold "⁻¹". apply H21. apply H. }
      apply rf_on_rf in H11.
      exfalso. apply CON5 with y.
      econstructor 1 with x. split; assumption.
    + apply cob_on_co in H2. apply cob_on_co in H.
      exfalso. eapply (co_irr CON1). eapply (co_trans CON1). apply H. apply H2.
    + rewrite H. reflexivity.

  - assumption.

Qed.

Lemma tf_wf tf : functional (⦗tf⦘ ⨾ rf⁻¹ ∩ same_range G ⨾ ⦗tf⦘).
Proof.
  apply functional_seq.
  apply functional_eqv_rel.
  apply functional_seq.
  apply tf_wf_any.
  apply functional_eqv_rel.
Qed.

Lemma hb_in_rfe_sb_trans : hb ⊆ ((⦗L⦘ ⨾ rfe ⨾ ⦗A⦘) ∪ sb)⁺.
Proof.
  intros x y H.
  induction H as [x y H | x y z H1 H2 H3 H4].
  - destruct H as [H | H].
    + intuition.
    + destruct H as [x_ [[H11 H12] [y_ [[H21 H22] [H31 H32]]]]].
      rewrite <- H11 in H21, H22.
      rewrite H31 in H21, H22, H32.
      econstructor 1.
      case classic with (sb x y) as [Sb | Sb]. { intuition. }
      left.
      econstructor.
      split. { econstructor. reflexivity. econstructor.
               apply rf_w_r in H21. apply H21. apply CON. unfold is_rel. unfold mode_le.
               unfold is_sc in H12. case (mod lab x) eqn:M; try easy. }
      econstructor.
      split. {
        econstructor. apply H21. apply Sb.
      }
      econstructor. { reflexivity. }
      econstructor. eapply rf_w_r. apply CON. apply H21. apply H32.
  - pose (transitive_ct) as T.
    specialize T with _ (⦗L⦘ ⨾ rfe ⨾ ⦗A⦘ ∪ sb).
    eapply T.
    apply H2. apply H4.
Qed.

Lemma hb_in_obs_sb_trans : hb ⊆ ((⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘) ∪ sb)⁺.
Proof.
  intros x y H.
  induction H as [x y H | x y z H1 H2 H3 H4].
  - destruct H as [H | H].
    + intuition.
    + destruct H as [x_ [[H11 H12] [y_ [[H21 H22] [H31 H32]]]]].
      rewrite <- H11 in H21, H22.
      rewrite H31 in H21, H22, H32.
      econstructor 1.
      case classic with (sb x y) as [Sb | Sb]. { intuition. }
      left.
      econstructor.
      split. { econstructor. reflexivity. left. econstructor.
               apply rf_w_r in H21. apply H21. apply CON. unfold is_rel. unfold mode_le.
               unfold is_sc in H12. case (mod lab x) eqn:M; try easy. }
      econstructor.
      split. {
        econstructor.
        left.
        econstructor. apply H21. apply Sb.
      }
      econstructor. { reflexivity. }
      right.
      econstructor. eapply rf_w_r. apply CON. apply H21. apply H32.
  - pose (transitive_ct) as T.
    specialize T with _ (⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘ ∪ sb).
    eapply T.
    apply H2. apply H4.
Qed.

Lemma hb_in_obs_sb_trans_weak : hb ⊆ (obs ∪ sb)⁺.
Proof.
  intros x y H.
  apply inclusion_t_t with ((⦗L ∪₁ A⦘ ⨾ obs ⨾ ⦗L ∪₁ A⦘) ∪ sb).
  - intros a b H_.
    destruct H_ as [H_ | H_].
    + apply inclusion_seq_eqv_l in H_.
      apply inclusion_seq_eqv_r in H_.
      left. apply H_.
    + right. apply H_.
  - apply hb_in_obs_sb_trans. apply H.
Qed.

(* the lynchpin *)
Lemma hb_in_rfe_sb_trans_helper :
  hb ⊆ sb ∪ (sb^? ⨾ (((⦗L⦘ ⨾ rfe ⨾ ⦗A⦘) ⨾ sb^?)⁺)).
Proof.
  intros x y H.
  apply hb_in_rfe_sb_trans in H.
  apply ct_unionE in H. Search "＊" "^?".
  assert (sb＊ = sb^? ) as Ha. {
    apply rel_extensionality.
    apply rt_of_trans.
    apply sb_trans.
  }
  rewrite sb_rt_of_trans in H.
  rewrite sb_ct_of_trans in H.
  assumption.
Qed.

Lemma atomic_rfe_sb_ob : ((⦗L⦘ ⨾ rfe ⨾ ⦗A⦘) ⨾ sb^?) ⊆ ⦗L⦘ ⨾ ob⁺.
Proof.
  intros x y H.
  destruct H as [z [[x_ [[H111 H112] [z_ [H121 [H1221 H1222]]]]] H2]].
  rewrite <- H111 in H121.
  rewrite H1221 in H121, H1222.
  econstructor.
  split. { econstructor. reflexivity. apply H112. }
  destruct H2.
  - rewrite H in H121.
    econstructor 1.
    econstructor. left. left.
    econstructor. left. apply H121.
  - econstructor 2.
    + econstructor 1.
      unfold Arm_mixed.ob. left. left. left.
      econstructor. left. apply H121.
    + econstructor 1.
      unfold Arm_mixed.ob. right.
      unfold Arm_mixed.bob. left. left. right.
      econstructor.
      split. { econstructor. reflexivity. apply A_in_Q. apply H1222. }
      apply H.
Qed.

Lemma hb_frag_in_ob :
  (sb^? ⨾ (((⦗L⦘ ⨾ rfe ⨾ ⦗A⦘) ⨾ sb^?)⁺)) ⊆ ob⁺.
Proof.
  intros x y H.
  destruct H as [z [H1 H2]].
  assert ((⦗L⦘ ⨾ (ob⁺)) z y) as H. {
    apply (inclusion_t_t atomic_rfe_sb_ob) in H2.
    apply inclusion_ct_seq_eqv_l in H2.
    destruct H2 as [xx [H21 H22]].
    econstructor.
    split. { apply H21. }
    apply ct_of_ct. apply H22.
  }
  destruct H as [z_ [[Ha11 Ha12] Ha2]].
  rewrite <- Ha11 in Ha2.
  destruct H1 as [H1 | H1].
  - rewrite H1. apply Ha2.
  - econstructor 2.
    + econstructor 1.
      unfold Arm_mixed.ob.
      right.
      unfold Arm_mixed.bob. left. right.
      econstructor.
      split. { apply H1. }
      econstructor.
      split. { econstructor. reflexivity. apply Ha12. }
      econstructor 1. reflexivity.
    + apply Ha2.
Qed.

Lemma hbe_in_ob x y :
  ~ sb x y -> hb x y -> ob⁺ x y.
Proof.
  intros H1 H2.
  apply hb_in_rfe_sb_trans_helper in H2.
  apply hb_frag_in_ob.
  destruct H2 as [H2 | H2].
  - intuition.
  - assumption.
Qed.

Lemma JSMM_m_compilation_hb_tot : hb ⊆ tot.
Proof.
  intros x y H. apply hb_in_obs_sb_trans in H.
  induction H as [x y [[x_ [H11 H12]] | H2] | x y z H1 H2 H3 H4].
  - apply tot_wf2.
    econstructor.
    split. apply H11. assumption.
  - apply tot_wf3. assumption.
  - eapply tot_wf1. apply H2. apply H4.
Qed.

Lemma JSMM_m_compilation_hb_rf : irreflexive (hb ⨾ rf).
Proof.
  intros x H.
  destruct H as [y [H1 H2]].
 (* apply hbe_in_ob_trans_helper in H1. *)
  case classic with (sb y x) as [Sb | Sb].
  - assert (hb y x) as Ha. { unfold JSMM_m.hb. econstructor 1. left. apply Sb. }
    eapply (spo_hb tot_wf1 JSMM_m_compilation_hb_tot).
    eapply (spo_hb tot_wf1 JSMM_m_compilation_hb_tot).
    apply H1. apply Ha.
  - case classic with (sb x y) as [Sd | Sd].
    + destruct CON as [_ [_ [CON3 _]]].
      apply rf_rf_on in H2.
      destruct H2 as [n H2].
      eapply CON3.
      econstructor 2.
      * econstructor 1.
        right.
        apply H2.
      * econstructor 1.
        left. left. left.
        unfold polocb.
        split. { apply Sd. }
        apply overlap_on_sym. apply rf_on_overlap_on.
        apply CON.
        apply H2.
    + assert (rfe y x) as Ha. {
        econstructor. apply H2. apply Sb.
      }
      apply hb_in_rfe_sb_trans_helper in H1.
      destruct H1 as [H1 | H1]. { apply Sd. apply H1. }
      apply hb_frag_in_ob in H1.
      eapply CON.
      econstructor 2.
      * apply H1.
      * econstructor 1.
        left. left. left. left. left.
        apply Ha.
Qed.

Lemma JSMM_m_compilation_hb_rf_hb :
  forall n : nat, irreflexive (hb ⨾ (rf_on n)⁻¹ ⨾ hb ∩ overlap_on G n ⨾ ⦗W⦘).
Proof.
  intros n y H.
  destruct H as [z [H1 [x [H2 H3]]]].
  unfold transp in H2.
  destruct H3 as [y_ [[H311 H312] [H321 H322]]].
  rewrite H321 in H311, H312, H322.
  clear y_ H321.
  destruct CON as [CON1 [_ [CON3 [_ CON5]]]].
  case classic with (cob_on n y x) as [Cob | Cob].
  - case classic with (sb x y) as [Sb | Sb].
    + eapply CON3.
      econstructor 2.
      * econstructor 1. left. right. apply Cob.
      * econstructor 1. left. left. left. unfold polocb.
        split. apply Sb. apply H312.
    + case classic with (sb y x) as [Sb1 | Sb1].
      * eapply (spo_hb tot_wf1 JSMM_m_compilation_hb_tot).
        eapply (spo_hb tot_wf1 JSMM_m_compilation_hb_tot).
        apply H311.
        econstructor 1. left. apply Sb1.
      * eapply CON5.
        econstructor 2.
        apply hbe_in_ob. apply Sb. apply H311.
        econstructor 1.
        left. left. left. left. right.
        econstructor. econstructor. unfold Execution_m.cob_on in Cob.
        intros H. rewrite <- H in Cob.
        eapply in_nil. apply Cob. apply Sb1.
  - case classic with (cob_on n x y) as [Cob1 | Cob1].
    + assert (fr_on n z y) as H. {
        unfold Arm_mixed.fr_on.
        econstructor.
        split. { unfold transp. apply H2. }
        apply Cob1.
      }
      case classic with (sb y z) as [Sb | Sb]. {
        eapply CON3.
        econstructor 2.
        - econstructor 1. left. left. left.
          unfold polocb.
          split. apply Sb. eapply overlap_on_trans. apply overlap_on_sym. apply H312.
          apply rf_on_overlap_on. apply CON1. apply H2.
        - econstructor 1. left. left. right. apply H.
      } {
        case classic with (sb z y) as [Sb1 | Sb1].
        - eapply (spo_hb tot_wf1 JSMM_m_compilation_hb_tot).
          eapply (spo_hb tot_wf1 JSMM_m_compilation_hb_tot).
          apply H1.
          econstructor 1. left. apply Sb1.
        - assert (ob⁺ y z) as Hob. {
            apply hbe_in_ob. apply Sb. apply H1.
          }
          assert (ob z y) as Hob1. {
            left. left. left. right.
            econstructor. { econstructor. apply H. }
            apply Sb1.
          }
          eapply CON5.
          econstructor 2.
          + apply Hob.
          + econstructor 1. apply Hob1.
      }
    + pose (wf_cob_total CON1 n) as P.
      unfold is_total in P.
      assert ((E ∩₁ W ∩₁ (fun x : actid => In n (range G x))) x) as Haa. {
        econstructor. econstructor.
        - apply rf_on_rf in H2. apply rf_E in H2. apply H2. apply CON1.
        - apply rf_on_rf in H2. eapply rf_w_r. apply CON1. apply H2.
        - unfold overlap_on in H312. unfold overlap in H312.
          apply list_intersect_rP in H312. apply H312.
      }
      assert ((E ∩₁ W ∩₁ (fun x : actid => In n (range G x))) y) as Haaa. {
        econstructor. econstructor.
        - apply rf_on_rf in H2. apply rf_E in H2. eapply hb_E. apply CON. apply H311. apply CON.
        - apply rf_on_rf in H2. apply H322.
        - unfold overlap_on in H312. unfold overlap in H312.
          apply list_intersect_rP in H312. apply H312.
      }
      assert (cob_on n x y \/ cob_on n y x) as H. {
        apply P. apply Haa. apply Haaa.
        intros H_. rewrite H_ in H311.
        eapply (spo_hb tot_wf1 JSMM_m_compilation_hb_tot).
        apply H311.
      }
      destruct H; easy.
Qed.


Lemma tot_L_cob_on n x y :
  L x -> L y -> tot x y -> overlap_on G n x y -> cob_on n x y.
Proof.
  intros H1 H2 H H5.
  case classic with (cob_on n x y) as [Cob1 | Cob1].
  - assumption.
  - case classic with (cob_on n y x) as [Cob2 | Cob2].
    + case classic with (sb y x) as [Sb | Sb].
      * exfalso. eapply tot_wf1. eapply tot_wf1. apply H. apply tot_wf3. apply Sb.
      * exfalso.
        assert (coe y x) as Ha. { econstructor. econstructor. intros H_.
                                  unfold Execution_m.cob_on in Cob2. rewrite <- H_ in Cob2.
                                  eapply in_nil. apply Cob2. apply Sb. }
        eapply tot_wf1. eapply tot_wf1. apply H. apply tot_wf2.
        econstructor.
        split. { econstructor. reflexivity. econstructor. assumption. }
        econstructor.
        split. { left. right. apply Ha. }
        econstructor. reflexivity. econstructor. assumption.
    + assert ((E ∩₁ W ∩₁ (fun x : actid => In n (range G x))) x) as Haa. {
        econstructor. econstructor.
        - apply tot_E in H. apply H.
        - apply H1.
        - unfold overlap_on in H5. unfold overlap in H5.
          apply list_intersect_rP in H5. apply H5.
      }
      assert ((E ∩₁ W ∩₁ (fun x : actid => In n (range G x))) y) as Haaa. {
        econstructor. econstructor.
        - apply tot_E in H. apply H.
        - apply H2.
        - unfold overlap_on in H5. unfold overlap in H5.
          apply list_intersect_rP in H5. apply H5.
      }
      assert (cob_on n x y \/ cob_on n y x) as H__. {
        destruct CON as [CON1].
        epose (wf_cob_total CON1 n) as P.
        unfold is_total in P.
        apply P. apply Haa. apply Haaa.
        intros H_. rewrite H_ in H.
        eapply tot_wf1.
        apply H.
      }
    destruct H__; easy.
Qed.

Lemma JSMM_m_compilation_sc :
  irreflexive (⦗W ∩₁ SC⦘ ⨾ tot ⨾ sw⁻¹ ⨾ tot ∩ same_range G).
Proof.
  intros y H.
  destruct CON as [CON1 [CON2 [CON3 [CON4 CON5]]]].
  destruct H as [y_ [[H11 [H121 H122]] [z [H2 [x [H3 [H41 H42]]]]]]].
  rewrite <- H11 in H2.
  clear y_ H11.
  unfold "⁻¹" in H3.
  destruct H3 as [x_ [[H311 H312] [z_ [[H32211 H32212] [H32221 H32222]]]]].
  rewrite H32221 in H32222,H32211,H32212.
  clear z_ H32221.
  rewrite <- H311 in H32211,H32212.
  clear x_ H311.
  apply rf_rf_on in H32211.
  destruct H32211 as [n H32211].
  assert (cob_on n x y) as Cob1. {
    apply tot_L_cob_on.
    - unfold is_rel. econstructor. eapply rf_w_r. apply CON1. eapply rf_on_rf. apply H32211.
      unfold mode_le. unfold is_sc in H312. case (mod lab x) eqn:H__; easy.
    - unfold is_rel. econstructor. apply H121.
      unfold mode_le. unfold is_sc in H122. case (mod lab y) eqn:H__; easy.
    - assumption.
    - apply rf_on_overlap_on in H32211. eapply same_range_overlap_on. apply H32211. apply H42.
      apply CON1.
  }
  case classic with (sb z y) as [Sb | Sb].
    * eapply tot_wf1.
      eapply tot_wf1.
      apply H2.
      apply tot_wf3.
      apply Sb.
    * assert (fre z y) as Ha. {
        econstructor.
        - unfold Arm_mixed.fr.
          exists n. unfold Arm_mixed.fr_on.
          econstructor.
          split. { unfold "⁻¹". apply H32211. }
          apply Cob1.
        - apply Sb.
      }
      assert (obs z y) as Haa. {
        right. apply Ha.
      }
      apply tot_wf1 with y.
      apply tot_wf1 with z. { apply H2. }
      apply tot_wf2.
      econstructor.
      split. { econstructor. reflexivity. right. econstructor. eapply rf_w_r.
               apply CON1. eapply rf_on_rf. apply H32211. apply H32222. }
      econstructor.
      split. {apply Haa. }
      econstructor. reflexivity. left. econstructor. assumption. unfold is_sc in H122. unfold is_rel.
      unfold mode_le. case (mod lab y) eqn:H__; easy.
Qed.

Lemma JSMM_m_compilation_sc_1 :
  irreflexive (⦗W ∩₁ SC⦘ ⨾ hb ⨾ (hb ∩ rf)⁻¹ ⨾ ⦗W ∩₁ SC⦘ ⨾ tot ∩ same_range G).
Proof.
  intros y H.
  destruct CON as [CON1 [CON2 [CON3 [CON4 CON5]]]].
  destruct H as [y_ [[H11 [H111 H112]] [z [H2 [x [H3 [x_ [[H41 [H421 H422]] [H51 H52]]]]]]]]].
  rewrite <- H11 in H2. clear y_ H11.
  rewrite <- H41 in H51,H52. clear x_ H41.
  unfold "⁻¹" in H3.
  destruct H3 as [H31 H32].
  apply rf_rf_on in H32.
  destruct H32 as [n H32].
  assert (cob_on n x y) as Cob1. {
    apply tot_L_cob_on.
    - unfold is_rel. econstructor. eapply rf_w_r. apply CON1. eapply rf_on_rf. apply H32.
      unfold mode_le. unfold is_sc in H422. case (mod lab x) eqn:H__; easy.
    - unfold is_rel. econstructor. apply H111.
      unfold mode_le. unfold is_sc in H112. case (mod lab y) eqn:H__; easy.
    - assumption.
    - apply rf_on_overlap_on in H32. eapply same_range_overlap_on. apply H32. apply H52.
      apply CON1.
  }
  case classic with (sb z y) as [Sb | Sb].
  - eapply (spo_hb tot_wf1 JSMM_m_compilation_hb_tot).
    eapply (spo_hb tot_wf1 JSMM_m_compilation_hb_tot).
    apply H2.
    econstructor 1. left. apply Sb.
  - assert (fr_on n z y) as Ha. {
      unfold Arm_mixed.fr_on.
      econstructor.
      split. { unfold "⁻¹". apply H32. }
      apply Cob1.
    }
    case classic with (sb y z) as [Sb1 | Sb1].
    + eapply CON3.
      econstructor 2.
      * econstructor 1. left. left. right. apply Ha.
      * econstructor 1. left. left. left. unfold polocb.
        split. { apply Sb1. }
        apply rf_on_overlap_on in H32.
        apply overlap_on_trans with x.
        apply overlap_on_sym.
        eapply same_range_overlap_on.
        apply H32. apply H52. apply H32. apply CON1.
    + assert (fre z y). { unfold Arm_mixed.fre. econstructor.
                          - unfold Arm_mixed.fr. exists n. apply Ha.
                          - apply Sb. }
      apply CON5 with z.
      constructor 2 with y.
      * constructor 1. left. left. left. right. apply H.
      * apply hbe_in_ob. apply Sb1. apply H2.
Qed.

Lemma JSMM_m_compilation_sc_2 :
  irreflexive (⦗W ∩₁ SC⦘ ⨾ tot ∩ same_range G ⨾ ⦗A⦘ ⨾ (hb ∩ rf)⁻¹ ⨾ hb).
Proof.
  intros y H.
  destruct CON as [CON1 [CON2 [CON3 [CON4 CON5]]]].
  destruct H as [y_ [[H11 [H121 H122]] [x [H3 [x_ [[H41 [H421 H422]] [z [H5 H6]]]]]]]].
  rewrite <- H41 in H5.
  rewrite <- H11 in H3.
  clear x_ y_ H41 H11.
  destruct H3 as [H31 H32].
  unfold "⁻¹" in H5.
  destruct H5 as [H51 H52].
  apply rf_rf_on in H52.
  destruct H52 as [n H52].
  case classic with (cob_on n y z) as [Cob | Cob].
  - case classic with (sb z y) as [Sb1 | Sb1].
    + eapply CON3.
      econstructor 2.
      * econstructor 1. left. right. apply Cob.
      * econstructor 1. left. left. left. unfold polocb.
        split. apply Sb1. apply rf_on_overlap_on in H52.
        apply overlap_on_trans with x.
        apply H52. apply same_range_sym in H32. apply overlap_on_sym in H52.
        eapply same_range_overlap_on. apply H52. apply H32. apply CON1.
    + case classic with (sb y z) as [Sb2 | Sb2].
      * eapply (spo_hb tot_wf1 JSMM_m_compilation_hb_tot).
        eapply (spo_hb tot_wf1 JSMM_m_compilation_hb_tot).
        apply H6. econstructor 1. left. apply Sb2.
      * assert (coe y z). {
          unfold Arm_mixed.coe.
          econstructor. eapply cob_on_co. apply Cob. apply Sb2. }
        apply CON5 with y.
        constructor 2 with z.
        { constructor 1. left. left. left. left. right. apply H. }
        { apply hbe_in_ob. apply Sb1. apply H6. }
  - case classic with (cob_on n z y) as [Cob1 | Cob1].
    + assert (fr_on n x y) as Ha. {
        econstructor.
        split. unfold "⁻¹". apply H52. apply Cob1.
      }
      case classic with (sb x y) as [Sb1 | Sb1].
      * apply tot_wf1 with x. apply tot_wf1 with y.
        apply JSMM_m_compilation_hb_tot. econstructor 1. left. apply Sb1.
        apply H31.
      * assert (obs x y) as Haa. {
          right. econstructor 1. econstructor 1. apply Ha. apply Sb1.
        }
        assert (tot x y) as Haaa. {
          apply tot_wf2.
          econstructor.
          split. { econstructor. reflexivity. right.
                   econstructor; assumption. }
          econstructor.
          split. { apply Haa. }
          econstructor. reflexivity. left. econstructor. assumption.
          unfold is_rel. unfold mode_le. unfold is_sc in H122. case (mod lab y) eqn:H__;easy.
        }
        apply tot_wf1 with x. apply tot_wf1 with y.
        apply Haaa. apply H31.
    + assert ((E ∩₁ W ∩₁ (fun x : actid => In n (range G x))) z) as Haa. {
        econstructor. econstructor.
        - apply hb_E in H51. apply H51. apply CON1.
        - apply rf_on_rf in H52. apply rf_w_r in H52. apply H52. apply CON1.
        - apply rf_on_overlap_on in H52. unfold overlap_on in H52. unfold overlap in H52.
          apply list_intersect_rP in H52. apply H52. apply CON1.
      }
      assert ((E ∩₁ W ∩₁ (fun x : actid => In n (range G x))) y) as Haaa. {
        econstructor. econstructor.
        - apply hb_E in H6. apply H6. apply CON1.
        - apply H121.
        - apply rf_on_overlap_on in H52. unfold overlap_on in H52. unfold overlap in H52.
          apply list_intersect_rP in H52. unfold same_range in H32. rewrite <- H32 in H52.
          apply H52. apply CON1. 
      }
      assert (cob_on n z y \/ cob_on n y z) as H__. {
        epose (wf_cob_total CON1 n) as P.
        unfold is_total in P.
        apply P. apply Haa. apply Haaa.
        intros H_. rewrite H_ in H6.
        eapply (spo_hb tot_wf1 JSMM_m_compilation_hb_tot).
        apply H6.
      }
    destruct H__; easy.
Qed.

Lemma JSMM_m_compilation tf : jsmm_m_consistent G tot tf.
  econstructor. { apply tot_wf1. }
  econstructor. { apply JSMM_m_compilation_hb_tot. }
  econstructor. { apply JSMM_m_compilation_hb_rf. }
  econstructor. { intros n. apply JSMM_m_compilation_hb_rf_hb. }
  econstructor. { apply JSMM_m_compilation_sc. }
  econstructor. { apply JSMM_m_compilation_sc_1. }
  econstructor. { apply JSMM_m_compilation_sc_2. }
  { apply tf_wf. }
Qed.

End JSMM_mToArm_mixed.
