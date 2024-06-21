Require Import Autosubst2.syntax ssreflect ssrbool.
From Hammer Require Import Tactics Hammer.
From stdpp Require Import relations (rtc(..), rtc_transitive).

Reserved Infix "⤳h" (at level 60, no associativity).
Reserved Infix "⇒" (at level 60, no associativity).
Reserved Infix "⇒n" (at level 60, no associativity).

Fixpoint ne a :=
  match a with
  | var_tm _ => true
  | tAbs _ => false
  | tApp a b => ne a && nf b
  end
with nf a :=
  match a with
  | var_tm _ => true
  | tAbs a => nf a
  | tApp a b => ne a && nf b
  end.

Lemma ne_is_nfb a : ne a ==> nf a.
Proof. elim : a; hauto lqb:on. Qed.

Lemma ne_is_nf a : ne a -> nf a.
Proof. sfirstorder use:ne_is_nfb b:on. Qed.

Lemma ne_nf_renaming_iff a ξ : (ne a = ne (ren_tm ξ a)) /\ (nf a = nf (ren_tm ξ a)).
Proof. elim : a ξ => //=; hauto l:on. Qed.

Definition isAbs a :=
  match a with
  | tAbs _ => true
  | _ => false
  end.

Inductive ERed : tm -> tm -> Prop :=
| ER_App0 a0 a1 b :
  ~~ isAbs a0 ->
  a0 ⤳h a1 ->
  tApp a0 b ⤳h tApp a1 b

| ER_App1 a b0 b1 :
  ne a ->
  b0 ⤳h b1 ->
  tApp a b0 ⤳h tApp a b1

| ER_AppAbs a b :
  tApp (tAbs a) b ⤳h subst_tm (b..) a

| ER_Abs a b :
  a ⤳h b ->
  tAbs a ⤳h tAbs b

where "a ⤳h b" := (ERed a b).

Derive Inversion ered_inv with (forall a b, ERed a b).

(* Parallel reduction *)
Inductive Par : tm -> tm -> Prop :=
| P_Var i :
  var_tm i ⇒ var_tm i
| P_App a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  tApp a0 b0 ⇒ tApp a1 b1
| P_AppAbs a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  tApp (tAbs a0) b0 ⇒ subst_tm (b1..) a1
| P_Abs a0 a1 :
  a0 ⇒ a1 ->
  tAbs a0 ⇒ tAbs a1
where "a ⇒ b" := (Par a b).

Lemma P_AppAbs' a0 a1 b0 b1 t :
  t = subst_tm (b1..) a1 ->
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  tApp (tAbs a0) b0 ⇒ t.
Proof. move => > ->. by apply P_AppAbs. Qed.

Lemma Par_renaming a b :
  a ⇒ b ->
  forall ξ, ren_tm ξ a ⇒ ren_tm ξ b.
Proof.
  move => h.
  elim:a b/h.
  - sfirstorder.
  - hauto lq:on ctrs:Par.
  - move => * /=.
    apply : P_AppAbs'; eauto.
    by asimpl.
  - hauto lq:on ctrs:Par.
Qed.

Lemma morphing_suc ρ0 ρ1 :
  (forall i, ρ0 i ⇒ ρ1 i) ->
  (forall i, (up_tm_tm ρ0) i ⇒ (up_tm_tm ρ1) i).
Proof.
  move => > ? []//=.
  - sfirstorder.
  - move => n. asimpl.
    sfirstorder use:Par_renaming.
Qed.

Lemma Par_morphing a b (h : a ⇒ b):
  forall ρ0 ρ1, (forall i, ρ0 i ⇒ ρ1 i) ->
             subst_tm ρ0 a ⇒ subst_tm ρ1 b.
Proof.
  elim : a b / h.
  - sfirstorder.
  - hauto lq:on ctrs:Par.
  - move => */=.
    apply : P_AppAbs'; cycle 1.
    sfirstorder use:morphing_suc.
    sfirstorder.
    by asimpl.
  - hauto lq:on ctrs:Par use:morphing_suc.
Qed.

Lemma Par_refl a : a ⇒ a.
Proof. elim : a; hauto lq:on ctrs:Par. Qed.

(* Parallel, non-essential reduction *)
Inductive NPar : tm -> tm -> Prop :=
| PN_Var i :
  var_tm i ⇒n var_tm i

| PN_AppAbs a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  tApp (tAbs a0) b0 ⇒n tApp (tAbs a1) b1

| PN_Abs a0 a1 :
  a0 ⇒n a1 ->
  tAbs a0 ⇒n tAbs a1

| PN_App0 a0 a1 b0 b1 :
  ~~ ne a0 ->
  a0 ⇒n a1 ->
  b0 ⇒ b1 ->
  tApp a0 b0 ⇒n tApp a1 b1

| PN_App1 a b0 b1 :
  ne a ->
  b0 ⇒n b1 ->
  tApp a b0 ⇒n tApp a b1

where "a ⇒n b":= (NPar a b).

Lemma NPar_Par a b : a ⇒n b -> a ⇒ b.
Proof. induction 1; hauto lq:on ctrs:Par use:Par_refl. Qed.

Lemma ERed_Par a b : a ⤳h b -> a ⇒ b.
Proof. induction 1; hauto lq:on ctrs:Par use:Par_refl. Qed.

Lemma NPar_renaming a b :
  a ⇒n b ->
  forall ξ, ren_tm ξ a ⇒n ren_tm ξ b.
Proof.
  move => h.
  elim:a b/h.
  - sfirstorder.
  - hauto lq:on ctrs:NPar use:Par_renaming.
  - hauto lq:on ctrs:NPar.
  - hauto lq:on ctrs:NPar use:Par_renaming, ne_nf_renaming_iff.
  - hauto lq:on ctrs:NPar use:Par_renaming, ne_nf_renaming_iff.
Qed.

Lemma isAbs_renaming a ξ : isAbs a = isAbs (ren_tm ξ a).
Proof. elim : a ξ => //=. Qed.

Lemma ER_AppAbs' a b u :
  u = subst_tm (b..) a ->
  tApp (tAbs a) b ⤳h u.
Proof. move => ->. by apply ER_AppAbs. Qed.

Lemma ERed_renaming a b :
  a ⤳h b ->
  forall ξ, ren_tm ξ a ⤳h ren_tm ξ b.
Proof.
  move => h.
  elim : a b /h.
  - hauto lq:on ctrs:ERed use:isAbs_renaming.
  - hauto lq:on ctrs:ERed use:ne_nf_renaming_iff.
  - move => a b ξ /=.
    apply : ER_AppAbs'. by asimpl.
  - hauto lq:on ctrs:ERed.
Qed.

(* Takahashi's *-sequence *)
Inductive starseq : tm -> tm -> Prop :=
| S_Refl M N :
  M ⇒n N ->
  (* ------- *)
  starseq M N
| S_Step M P N :
  M ⤳h P ->
  M ⇒ N ->
  starseq P N ->
  starseq M N.

Lemma starseq_renaming ξ a b :
  starseq a b ->
  starseq (ren_tm ξ a) (ren_tm ξ b).
Proof.
  move => h.
  elim : a b /h;
    hauto lq:on ctrs:starseq use:NPar_renaming, Par_renaming, ERed_renaming.
Qed.

Lemma ne_par_id a b : a ⇒ b -> (ne a || nf a) -> a = b.
Proof.
  move => h.
  elim : a b /h => //=.
  - sfirstorder lqb:on.
  - hauto lqb:on.
Qed.

Lemma ne_red_imp a b : a ⤳h b  -> (ne a || nf a) -> False.
Proof.
  move => h. elim : a b /h; hauto lqb:on.
Qed.

Lemma starseq_app_cong1 a b0 b1 :
  ne a ->
  starseq b0 b1 ->
  starseq (tApp a b0) (tApp a b1).
Proof.
  move => + h. move : a.
  elim : b0 b1 / h.
  - hauto lq:on ctrs:starseq, NPar.
  - hauto lq:on use:Par_refl ctrs:ERed, Par, starseq.
Qed.

Lemma starseq_app_cong00 a0 a1 b0 b1 :
  ~~ ne a0 ->
  a0 ⇒n a1 ->
  starseq b0 b1 ->
  starseq (tApp a0 b0) (tApp a1 b1).
Proof.
  move => + + h. move : a0 a1. elim:b0 b1/h .
  - hauto lq:on use:NPar_Par ctrs:starseq, NPar.
  - hauto lq:on use:Par_refl, NPar_Par ctrs:ERed, Par, starseq, NPar.
Qed.

(* Erase the information about one step par from starseq *)
Lemma starseq_erase a b (h : starseq a b) :
  exists u, rtc ERed a u /\ u ⇒n b.
Proof.
  elim : a b /h; hauto lq:on ctrs:rtc.
Qed.

Lemma starseq_par a b (h : starseq a b) :
  a ⇒ b.
Proof.
  elim : a b /h; sfirstorder use:NPar_Par.
Qed.

Lemma starseq_app_cong a0 a1 b0 b1 :
  starseq a0 a1 ->
  starseq b0 b1 ->
  starseq (tApp a0 b0) (tApp a1 b1).
Proof.
  move => h. move : b0 b1. elim: a0 a1 /h.
  - move => a0 a1 ha b0 b1 hb.
    case E : (ne a0).
    + have ? : a1 = a0 by hauto q:on use:NPar_Par, ne_par_id. subst.
      sfirstorder use:starseq_app_cong1.
    + hauto lq:on use:starseq_app_cong00.
  - move => a a0 a1 ha0 ha1 ha iha b0 b1 h.
    case E : (isAbs a) => //=.
    + have : ~~ ne a by  move : E; clear; case : a => //=.
      case : a E ha0 ha1 => //=.
      hauto inv:ERed, Par use:starseq_par, S_Refl, PN_AppAbs.
    + case E0 : (ne a).
      * have ? : a0 = a by move : ha0 E0; clear; hauto q:on use:ERed_Par, ne_par_id. subst.
        apply iha=>//.
      * apply S_Step with (P := tApp a0 b0).
        hauto lq:on ctrs:ERed.
        sfirstorder use: P_App, starseq_par.
        sfirstorder.
Qed.

Lemma starseq_abs_cong M N
  (h : starseq M N) :
  starseq (tAbs M) (tAbs N).
Proof. elim:M N/h; hauto lq:on ctrs:starseq, NPar, Par, ERed. Qed.

Lemma starseq_ρ_par ρ0 ρ1 :
  (forall i : fin, starseq (ρ0 i) (ρ1 i)) ->
  (forall i : fin, Par (ρ0 i) (ρ1 i)).
Proof. firstorder using starseq_par. Qed.

Lemma ipar_starseq_morphing :
  forall M N : tm,
  M ⇒ N ->
  forall ρ0 ρ1 : fin -> tm,
    (forall i : fin, starseq (ρ0 i) (ρ1 i)) -> starseq (subst_tm ρ0 M) (subst_tm ρ1 N).
Proof.
  move => M N h. elim : M N / h.
  - sfirstorder.
  - move => a0 a1 b0 b1 ha iha hb ihb ρ0 ρ1 hρ /=.
    apply starseq_app_cong.
    sfirstorder.
    sfirstorder use:Par_morphing, starseq_ρ_par.
  - move => a0 a1 b0 b1 ha iha hb ihb ρ0 ρ1 h.
    simpl.
    apply : S_Step.
    by apply ER_AppAbs.
    apply P_AppAbs' with (a1 := subst_tm (up_tm_tm ρ1) a1) (b1 := subst_tm ρ1 b1).
    by asimpl.
    sfirstorder use:Par_morphing, starseq_ρ_par, morphing_suc.
    sfirstorder use:Par_morphing, starseq_ρ_par.
    asimpl.
    apply iha.
    case => //=.
    by apply ihb.
  - move => a0 a1 ha iha ρ0 ρ1 hρ /=.
    apply starseq_abs_cong.
    apply iha.
    case => //=; asimpl.
    hauto l:on.
    move => n. asimpl.
    sfirstorder use:starseq_renaming.
Qed.

Lemma hms_split t s (h : t ⇒ s) :
  starseq t s.
Proof.
  elim : t s /h .
  - hauto lq:on ctrs:NPar, starseq.
  - eauto using starseq_app_cong.
  - move => a0 a1 b0 b1 ha iha hb ihb.
    apply : S_Step.
    by apply ER_AppAbs.
    by apply P_AppAbs.
    hauto lq:on ctrs:starseq inv:nat use:ipar_starseq_morphing.
  - eauto using starseq_abs_cong.
Qed.

Lemma not_ne_red a : ~~ ne a -> ~~  nf a -> exists b, a ⤳h b.
Proof.
  elim : a => //=.
  - hauto lq:on inv:tm lq:on ctrs:ERed b:on.
  - move => M ihM N ihN h _.
    case E : (ne M) => //=.
    + hauto q:on inv:tm ctrs:ERed.
    + move {h}.
      case : (nf M)=> //=;
      hauto lq:on inv:tm ctrs:ERed.
Qed.

Lemma ne_characterization a : ~~ (isAbs a) -> nf a -> ne a.
Proof. elim : a => //=.
Qed.

Lemma ne_characterization' a :  ~~ ne a -> isAbs a \/ ~~ nf a.
Proof.
  hauto lq:on inv:tm use:ne_characterization.
Qed.

Lemma persistence t s1 s2 (h : t ⤳h s1) :
  t ⇒n s2 ->
  exists u, s2 ⤳h u.
Proof.
  move : s2.
  elim : t s1 /h.
  - move => a0 a1 b h0 h1 ih0 s2.
    inversion 1; subst.
    + scongruence.
    + move : ih0 (H3) => /[apply].
      move => [u]hu.
      case E : (isAbs a3) => //=.
      * hauto lq:on ctrs:ERed inv:tm.
      * hauto lq:on ctrs:ERed.
    + hauto lq:on ctrs:ERed.
  - hauto lqb:on inv:NPar ctrs:ERed.
  - hauto lqb:on inv:NPar ctrs:ERed.
  - hauto lqb:on inv:NPar ctrs:ERed.
Qed.

Lemma hms_merge t a u  :
  t ⇒n a ->
  a ⤳h u ->
  t ⇒ u.
Proof.
  move => h.
  move : u.
  elim : t a / h.
  - hauto lq:on ctrs:Par inv:ERed.
  - hauto q:on ctrs:Par inv:ERed.
  - hauto lq:on ctrs:Par inv:ERed.
  - move => a0 a1 b0 b1 nea0 ha iha hb u.
    elim /ered_inv => //= _.
    + hauto lq:on ctrs:Par.
    + move => ? ? b2 nea2 h [*]. subst.
      move /ne_characterization' : (nea0) => [].
      * case : a0 nea0 ha iha => //=.
        hauto lq:on inv:NPar ctrs:Par.
      * move => nfa0.
        have [a2 ha2] : exists a2, a0 ⤳h a2 by sfirstorder use:not_ne_red.
        exfalso. move : ha2 ha nea2; clear.
        move : persistence; repeat move/[apply].
        sfirstorder lqb:on use:ne_red_imp.
    + move => a2 b2 [*]. subst.
      hauto lq:on inv:NPar ctrs:Par use:NPar_Par.
  - move => a b0 b1 ha hb ihb u.
    inversion 1; subst => //.
    hauto lqb:on use:ne_red_imp.
    hauto lq:on ctrs:Par use:Par_refl, ERed_Par.
Qed.

Lemma local_postponement t a u  :
  t ⇒n a ->
  a ⤳h u ->
  exists q, rtc ERed t q /\ q ⇒n u.
Proof. sfirstorder use:hms_split, hms_merge, starseq_erase. Qed.
