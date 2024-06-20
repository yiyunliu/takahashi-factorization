Require Import Autosubst2.syntax ssreflect ssrbool.
From Hammer Require Import Tactics.
From stdpp Require Import relations (rtc(..), rtc_transitive).

Reserved Infix "⤳h" (at level 60, no associativity).
Reserved Infix "⇒" (at level 60, no associativity).
Reserved Infix "⇒n" (at level 60, no associativity).

Definition isAbs a :=
  match a with
  | tAbs _ => true
  | _ => false
  end.

Inductive ERed : tm -> tm -> Prop :=
| ER_App a0 a1 b :
  ~~ isAbs a0 ->
  a0 ⤳h a1 ->
  tApp a0 b ⤳h tApp a1 b

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

| PN_App a0 a1 b0 b1 :
  a0 ⇒n a1 ->
  b0 ⇒ b1 ->
  tApp a0 b0 ⇒n tApp a1 b1

where "a ⇒n b":= (NPar a b).

Lemma NPar_Par a b : a ⇒n b -> a ⇒ b.
Proof. induction 1; hauto lq:on ctrs:Par. Qed.

Lemma NPar_renaming a b :
  a ⇒n b ->
  forall ξ, ren_tm ξ a ⇒n ren_tm ξ b.
Proof.
  move => h.
  elim:a b/h.
  - sfirstorder.
  - hauto lq:on ctrs:NPar use:Par_renaming.
  - hauto lq:on ctrs:NPar.
  - hauto lq:on ctrs:NPar use:Par_renaming.
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
  - move => a b ξ /=.
    apply : ER_AppAbs'. by asimpl.
  - hauto lq:on ctrs:ERed.
Qed.

Notation "s ⤳*h t" := (rtc ERed s t) (at level 60, no associativity).

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
  - hauto lq:on inv:NPar, ERed ctrs:Par use:NPar_Par.
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

Lemma starseq_app_cong M N P Q :
  starseq M N ->
  P ⇒ Q ->
  starseq (tApp M P) (tApp N Q).
Proof.
  move => h. move : P Q. elim : M N / h.
  - sfirstorder use:S_Refl, PN_App.
  - move => M P N hMP hMN hPN ih R Q hRQ.
    case E : (isAbs M).
    + apply S_Refl.
      case : M hMP hMN E=>//.
      move => M.
      elim/ered_inv=>//_ a0 b0 hab0 [?] ? h _. subst.
      hauto lq:on inv:Par ctrs:NPar.
    + hauto lq:on ctrs:starseq, NPar, Par, ERed.
Qed.

Lemma starseq_abs_cong M N
  (h : starseq M N) :
  starseq (tAbs M) (tAbs N).
Proof. elim:M N/h; hauto lq:on ctrs:starseq, NPar, Par, ERed. Qed.

Lemma starseq_par a b :
  starseq a b ->
  a ⇒ b.
Proof. induction 1; sfirstorder use:NPar_Par. Qed.

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
    (* par cong *)
    sfirstorder use:Par_morphing, starseq_ρ_par.
  - move => a0 a1 b0 b1 ha iha hb ihb ρ0 ρ1 h.
    simpl.
    apply : S_Step.
    by apply ER_AppAbs.
    apply P_AppAbs' with (a1 := subst_tm (up_tm_tm ρ1) a1) (b1 := subst_tm ρ1 b1).
    by asimpl.
    (* par cong *)
    sfirstorder use:Par_morphing, starseq_ρ_par, morphing_suc.
    (* par cong *)
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
    (* renaming *)
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

(* Erase the information about one step par from starseq *)
Lemma starseq_erase a b (h : starseq a b) :
  exists u, a ⤳*h u /\ u ⇒n b.
Proof.
  elim : a b /h; hauto lq:on ctrs:rtc.
Qed.

Lemma local_postponement t a u  :
  t ⇒n a ->
  a ⤳h u ->
  exists q, t ⤳*h q /\ q ⇒n u.
Proof. sfirstorder use:hms_split, hms_merge, starseq_erase. Qed.
