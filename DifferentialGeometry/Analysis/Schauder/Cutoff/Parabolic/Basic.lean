import DifferentialGeometry.Analysis.Schauder.Cutoff.Elliptic.BallHessian
import DifferentialGeometry.Analysis.Schauder.Cutoff.Product

noncomputable section

open Real Set
open scoped BoundedContinuousFunction NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

def timeCutoffBoundedContinuousFunction
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    BoundedContinuousFunction Real Real :=
  ballCutoffBoundedContinuousFunction center hr hrR

def timeCutoffDerivBoundedContinuousFunction
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    BoundedContinuousFunction Real Real :=
  (ContinuousLinearMap.apply Real Real (1 : Real))
    |>.compLeftContinuousBounded Real
      (ballCutoffFDerivBoundedContinuousFunction center hr hrR)

@[simp]
theorem timeCutoffBoundedContinuousFunction_apply
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (t : Real) :
    timeCutoffBoundedContinuousFunction center hr hrR t = ballCutoff center r R t := rfl

@[simp]
theorem timeCutoffDerivBoundedContinuousFunction_apply
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (t : Real) :
    timeCutoffDerivBoundedContinuousFunction center hr hrR t =
      ballCutoffFDeriv center r R t 1 := rfl

theorem timeCutoffBoundedContinuousFunction_hasDerivAt
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (t : Real) :
    HasDerivAt (timeCutoffBoundedContinuousFunction center hr hrR : Real → Real)
      (timeCutoffDerivBoundedContinuousFunction center hr hrR t) t := by
  change HasDerivAt (ballCutoff center r R) (ballCutoffFDeriv center r R t 1) t
  exact (hasFDerivAt_ballCutoff center r R t).hasDerivAt

def timeCutoffDerivHolderConst (r R : Real) : NNReal :=
  ballCutoffFDerivHolderConst r R

theorem timeCutoffBoundedContinuousFunction_holderWith
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {beta : NNReal} (hbeta1 : beta ≤ 1) :
    HolderWith (ballCutoffHolderConst r R) beta
      (timeCutoffBoundedContinuousFunction center hr hrR : Real → Real) := by
  intro x y
  simpa only [timeCutoffBoundedContinuousFunction_apply] using
    ballCutoff_holderWith (V := Real) hr hrR bot_le hbeta1 x y

theorem timeCutoffDerivBoundedContinuousFunction_holderWith
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {beta : NNReal} (hbeta1 : beta ≤ 1) :
    HolderWith (timeCutoffDerivHolderConst r R) beta
      (timeCutoffDerivBoundedContinuousFunction center hr hrR : Real → Real) := by
  let L := ContinuousLinearMap.apply Real Real (1 : Real)
  have hbase := ballCutoffFDeriv_holderWith (V := Real) (center := center)
    hr hrR bot_le hbeta1
  have hL : LipschitzWith 1 L := by
    apply LipschitzWith.of_dist_le_mul
    intro A B
    rw [dist_eq_norm, ← map_sub]
    calc
      ‖L (A - B)‖ ≤ ‖A - B‖ * ‖(1 : Real)‖ := (A - B).le_opNorm 1
      _ = (1 : Real) * dist A B := by simp only [norm_one, mul_one, one_mul,
        dist_eq_norm]
  have hcomp := hL.holderWith.comp hbase
  change HolderWith (timeCutoffDerivHolderConst r R) beta
    (fun t ↦ ballCutoffFDeriv center r R t 1)
  intro x y
  simpa only [timeCutoffDerivHolderConst, L, Function.comp_apply,
    ContinuousLinearMap.apply_apply, NNReal.coe_one, NNReal.rpow_one,
    mul_one, one_mul] using hcomp x y

theorem timeCutoffBoundedContinuousFunction_parabolic_holderWith
    {V : Type*} [PseudoMetricSpace V]
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {alpha : NNReal} (halpha1 : alpha ≤ 1) :
    HolderWith (ballCutoffHolderConst r R) alpha
      (fun p : ParabolicPoint V ↦ timeCutoffBoundedContinuousFunction center hr hrR p.time) := by
  apply holderWith_parabolic_const_space
  apply timeCutoffBoundedContinuousFunction_holderWith center hr hrR
  exact (div_le_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    (by simpa using halpha1.trans (show (1 : NNReal) ≤ 2 by norm_num))

theorem timeCutoffDerivBoundedContinuousFunction_parabolic_holderWith
    {V : Type*} [PseudoMetricSpace V]
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {alpha : NNReal} (halpha1 : alpha ≤ 1) :
    HolderWith (timeCutoffDerivHolderConst r R) alpha
      (fun p : ParabolicPoint V ↦
        timeCutoffDerivBoundedContinuousFunction center hr hrR p.time) := by
  apply holderWith_parabolic_const_space
  apply timeCutoffDerivBoundedContinuousFunction_holderWith center hr hrR
  exact (div_le_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    (by simpa using halpha1.trans (show (1 : NNReal) ≤ 2 by norm_num))

def intervalCutoffCenter (t₀ t₁ : Real) : Real :=
  (t₀ + t₁) / 2

def intervalCutoffInnerRadius (t₀ t₁ : Real) : Real :=
  (t₁ - t₀) / 2

def intervalCutoffGap (a t₀ t₁ b : Real) : Real :=
  min (t₀ - a) (b - t₁)

def intervalCutoffOuterRadius (a t₀ t₁ b : Real) : Real :=
  intervalCutoffInnerRadius t₀ t₁ + intervalCutoffGap a t₀ t₁ b / 2

theorem intervalCutoffInnerRadius_nonneg
    {t₀ t₁ : Real} (ht : t₀ ≤ t₁) :
    0 ≤ intervalCutoffInnerRadius t₀ t₁ := by
  unfold intervalCutoffInnerRadius
  linarith

theorem intervalCutoffGap_pos
    {a t₀ t₁ b : Real} (ha : a < t₀) (hb : t₁ < b) :
    0 < intervalCutoffGap a t₀ t₁ b := by
  unfold intervalCutoffGap
  exact lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)

theorem intervalCutoffInnerRadius_lt_outerRadius
    {a t₀ t₁ b : Real} (ha : a < t₀) (hb : t₁ < b) :
    intervalCutoffInnerRadius t₀ t₁ <
      intervalCutoffOuterRadius a t₀ t₁ b := by
  unfold intervalCutoffOuterRadius
  linarith [intervalCutoffGap_pos ha hb]

theorem Icc_subset_intervalCutoff_closedBall
    (t₀ t₁ : Real) :
    Icc t₀ t₁ ⊆ Metric.closedBall
      (intervalCutoffCenter t₀ t₁)
      (intervalCutoffInnerRadius t₀ t₁) := by
  simpa only [intervalCutoffCenter, intervalCutoffInnerRadius] using
    Set.Subset.rfl (s := Icc t₀ t₁) |>.trans_eq
      (Real.Icc_eq_closedBall t₀ t₁)

theorem intervalCutoff_closedBall_subset_Ioo
    {a t₀ t₁ b : Real} (ha : a < t₀) (hb : t₁ < b) :
    Metric.closedBall (intervalCutoffCenter t₀ t₁)
        (intervalCutoffOuterRadius a t₀ t₁ b) ⊆ Ioo a b := by
  intro t ht
  rw [Real.closedBall_eq_Icc] at ht
  have hgapLeft : intervalCutoffGap a t₀ t₁ b ≤ t₀ - a :=
    min_le_left _ _
  have hgapRight : intervalCutoffGap a t₀ t₁ b ≤ b - t₁ :=
    min_le_right _ _
  have hgapPos := intervalCutoffGap_pos ha hb
  unfold intervalCutoffCenter intervalCutoffOuterRadius
    intervalCutoffInnerRadius at ht
  rcases ht with ⟨htLeft, htRight⟩
  constructor <;> linarith

def intervalCutoffBoundedContinuousFunction
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b) :
    BoundedContinuousFunction Real Real :=
  timeCutoffBoundedContinuousFunction (intervalCutoffCenter t₀ t₁)
    (intervalCutoffInnerRadius_nonneg ht)
    (intervalCutoffInnerRadius_lt_outerRadius ha hb)

def intervalCutoffDerivBoundedContinuousFunction
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b) :
    BoundedContinuousFunction Real Real :=
  timeCutoffDerivBoundedContinuousFunction (intervalCutoffCenter t₀ t₁)
    (intervalCutoffInnerRadius_nonneg ht)
    (intervalCutoffInnerRadius_lt_outerRadius ha hb)

def intervalCutoffHolderConst (a t₀ t₁ b : Real) : NNReal :=
  ballCutoffHolderConst (intervalCutoffInnerRadius t₀ t₁)
    (intervalCutoffOuterRadius a t₀ t₁ b)

def intervalCutoffDerivHolderConst (a t₀ t₁ b : Real) : NNReal :=
  timeCutoffDerivHolderConst (intervalCutoffInnerRadius t₀ t₁)
    (intervalCutoffOuterRadius a t₀ t₁ b)

def intervalCutoffDerivSupConst (a t₀ t₁ b : Real) : NNReal :=
  Real.toNNReal (ballCutoffFDerivBound
    (intervalCutoffInnerRadius t₀ t₁)
    (intervalCutoffOuterRadius a t₀ t₁ b))

theorem intervalCutoffBoundedContinuousFunction_eq_one
    {a t₀ t₁ b : Real} (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    {t : Real} (htmem : t ∈ Icc t₀ t₁) :
    intervalCutoffBoundedContinuousFunction a t₀ t₁ b ha ht hb t = 1 := by
  apply ballCutoff_eq_one_of_mem_closedBall
    (intervalCutoffInnerRadius_nonneg ht)
    (intervalCutoffInnerRadius_lt_outerRadius ha hb)
  exact Icc_subset_intervalCutoff_closedBall t₀ t₁ htmem

theorem intervalCutoffBoundedContinuousFunction_mem_Icc
    {a t₀ t₁ b : Real} (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (t : Real) :
    intervalCutoffBoundedContinuousFunction a t₀ t₁ b ha ht hb t ∈ Icc (0 : Real) 1 :=
  ballCutoff_mem_Icc _ _ _ _

theorem norm_intervalCutoffBoundedContinuousFunction_le_one
    {a t₀ t₁ b : Real} (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (t : Real) :
    ‖intervalCutoffBoundedContinuousFunction a t₀ t₁ b ha ht hb t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (intervalCutoffBoundedContinuousFunction_mem_Icc ha ht hb t).1]
  exact (intervalCutoffBoundedContinuousFunction_mem_Icc ha ht hb t).2

theorem norm_intervalCutoffDerivBoundedContinuousFunction_le
    {a t₀ t₁ b : Real} (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (t : Real) :
    ‖intervalCutoffDerivBoundedContinuousFunction a t₀ t₁ b ha ht hb t‖ ≤
      intervalCutoffDerivSupConst a t₀ t₁ b := by
  let r := intervalCutoffInnerRadius t₀ t₁
  let R := intervalCutoffOuterRadius a t₀ t₁ b
  have hr : 0 ≤ r := intervalCutoffInnerRadius_nonneg ht
  have hrR : r < R := intervalCutoffInnerRadius_lt_outerRadius ha hb
  have hbound : 0 ≤ ballCutoffFDerivBound r R :=
    ballCutoffFDerivBound_nonneg hr hrR
  calc
    ‖intervalCutoffDerivBoundedContinuousFunction a t₀ t₁ b ha ht hb t‖ =
        ‖ballCutoffFDeriv (intervalCutoffCenter t₀ t₁) r R t 1‖ := rfl
    _ ≤ ‖ballCutoffFDeriv (intervalCutoffCenter t₀ t₁) r R t‖ := by
      simpa only [norm_one, mul_one] using
        (ballCutoffFDeriv (intervalCutoffCenter t₀ t₁) r R t).le_opNorm 1
    _ ≤ ballCutoffFDerivBound r R := norm_ballCutoffFDeriv_le hr hrR t
    _ = intervalCutoffDerivSupConst a t₀ t₁ b := by
      rw [intervalCutoffDerivSupConst, Real.coe_toNNReal _ hbound]

theorem intervalCutoffBoundedContinuousFunction_tsupport_subset
    {a t₀ t₁ b : Real} (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b) :
    tsupport (intervalCutoffBoundedContinuousFunction a t₀ t₁ b ha ht hb : Real → Real) ⊆
      Ioo a b := by
  exact (ballCutoff_tsupport_subset_closedBall
    (intervalCutoffInnerRadius_nonneg ht)
    (intervalCutoffInnerRadius_lt_outerRadius ha hb)).trans
      (intervalCutoff_closedBall_subset_Ioo ha hb)

theorem intervalCutoffBoundedContinuousFunction_eq_zero_of_not_mem
    {a t₀ t₁ b : Real} (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    {t : Real} (htmem : t ∉ Ioo a b) :
    intervalCutoffBoundedContinuousFunction a t₀ t₁ b ha ht hb t = 0 := by
  by_contra hne
  exact htmem (intervalCutoffBoundedContinuousFunction_tsupport_subset ha ht hb
    (subset_tsupport _ hne))

theorem intervalCutoffDerivBoundedContinuousFunction_eq_zero_of_not_mem
    {a t₀ t₁ b : Real} (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    {t : Real} (htmem : t ∉ Ioo a b) :
    intervalCutoffDerivBoundedContinuousFunction a t₀ t₁ b ha ht hb t = 0 := by
  have hout : t ∉ Metric.ball (intervalCutoffCenter t₀ t₁)
      (intervalCutoffOuterRadius a t₀ t₁ b) := by
    intro hball
    exact htmem (intervalCutoff_closedBall_subset_Ioo ha hb
      (Metric.ball_subset_closedBall hball))
  change ballCutoffFDeriv (intervalCutoffCenter t₀ t₁)
      (intervalCutoffInnerRadius t₀ t₁)
      (intervalCutoffOuterRadius a t₀ t₁ b) t 1 = 0
  rw [ballCutoffFDeriv_eq_zero_of_not_mem_ball
    (intervalCutoffInnerRadius_nonneg ht)
    (intervalCutoffInnerRadius_lt_outerRadius ha hb) hout]
  rfl

theorem intervalCutoffBoundedContinuousFunction_hasDerivAt
    {a t₀ t₁ b : Real} (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (t : Real) :
    HasDerivAt (intervalCutoffBoundedContinuousFunction a t₀ t₁ b ha ht hb : Real → Real)
      (intervalCutoffDerivBoundedContinuousFunction a t₀ t₁ b ha ht hb t) t := by
  exact timeCutoffBoundedContinuousFunction_hasDerivAt
    (intervalCutoffCenter t₀ t₁)
    (intervalCutoffInnerRadius_nonneg ht)
    (intervalCutoffInnerRadius_lt_outerRadius ha hb) t

theorem intervalCutoffBoundedContinuousFunction_holderWith
    {a t₀ t₁ b : Real} (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    {beta : NNReal} (hbeta1 : beta ≤ 1) :
    HolderWith (intervalCutoffHolderConst a t₀ t₁ b) beta
      (intervalCutoffBoundedContinuousFunction a t₀ t₁ b ha ht hb : Real → Real) := by
  exact timeCutoffBoundedContinuousFunction_holderWith (intervalCutoffCenter t₀ t₁)
    (intervalCutoffInnerRadius_nonneg ht)
    (intervalCutoffInnerRadius_lt_outerRadius ha hb) hbeta1

theorem intervalCutoffDerivBoundedContinuousFunction_holderWith
    {a t₀ t₁ b : Real} (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    {beta : NNReal} (hbeta1 : beta ≤ 1) :
    HolderWith (intervalCutoffDerivHolderConst a t₀ t₁ b) beta
      (intervalCutoffDerivBoundedContinuousFunction a t₀ t₁ b ha ht hb : Real → Real) := by
  exact timeCutoffDerivBoundedContinuousFunction_holderWith (intervalCutoffCenter t₀ t₁)
    (intervalCutoffInnerRadius_nonneg ht)
    (intervalCutoffInnerRadius_lt_outerRadius ha hb) hbeta1

theorem intervalCutoffBoundedContinuousFunction_parabolic_holderWith
    {V : Type*} [PseudoMetricSpace V]
    {a t₀ t₁ b : Real} (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    {alpha : NNReal} (halpha1 : alpha ≤ 1) :
    HolderWith (intervalCutoffHolderConst a t₀ t₁ b) alpha
      (fun p : ParabolicPoint V ↦
        intervalCutoffBoundedContinuousFunction a t₀ t₁ b ha ht hb p.time) := by
  apply holderWith_parabolic_const_space
  apply intervalCutoffBoundedContinuousFunction_holderWith ha ht hb
  exact (div_le_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    (by simpa using halpha1.trans (show (1 : NNReal) ≤ 2 by norm_num))

theorem intervalCutoffDerivBoundedContinuousFunction_parabolic_holderWith
    {V : Type*} [PseudoMetricSpace V]
    {a t₀ t₁ b : Real} (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    {alpha : NNReal} (halpha1 : alpha ≤ 1) :
    HolderWith (intervalCutoffDerivHolderConst a t₀ t₁ b) alpha
      (fun p : ParabolicPoint V ↦
        intervalCutoffDerivBoundedContinuousFunction a t₀ t₁ b ha ht hb p.time) := by
  apply holderWith_parabolic_const_space
  apply intervalCutoffDerivBoundedContinuousFunction_holderWith ha ht hb
  exact (div_le_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    (by simpa using halpha1.trans (show (1 : NNReal) ≤ 2 by norm_num))

section Separable

variable {V F : Type*} [TopologicalSpace V]
  [NormedAddCommGroup F] [NormedSpace Real F]

def separableBoundedContinuousFunctionPath
    (eta : BoundedContinuousFunction Real Real)
    (v : BoundedContinuousFunction V F) :
    Real → BoundedContinuousFunction V F :=
  fun t ↦ eta t • v

@[simp]
theorem separableBoundedContinuousFunctionPath_apply
    (eta : BoundedContinuousFunction Real Real)
    (v : BoundedContinuousFunction V F) (t : Real) (x : V) :
    separableBoundedContinuousFunctionPath eta v t x = eta t • v x := rfl

theorem separableBoundedContinuousFunctionPath_hasDerivAt
    (eta deta : BoundedContinuousFunction Real Real)
    (v : BoundedContinuousFunction V F) (t : Real)
    (heta : HasDerivAt (eta : Real → Real) (deta t) t) :
    HasDerivAt (separableBoundedContinuousFunctionPath eta v) (deta t • v) t := by
  unfold separableBoundedContinuousFunctionPath
  exact heta.smul_const v

end Separable

section Spatial

variable {V F : Type*}
  [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem separableBoundedContinuousFunctionPath_hasFDerivAt
    (eta : BoundedContinuousFunction Real Real)
    (v : BoundedContinuousFunction V F)
    (dv : BoundedContinuousFunction V (V →L[Real] F))
    (hv : ∀ x, HasFDerivAt (v : V → F) (dv x) x)
    (t : Real) (x : V) :
    HasFDerivAt (separableBoundedContinuousFunctionPath eta v t : V → F)
      (eta t • dv x) x := by
  change HasFDerivAt (fun y => eta t • v y) (eta t • dv x) x
  exact (hv x).const_smul (eta t)

theorem separableBoundedContinuousFunctionPath_fderiv_hasFDerivAt
    (eta : BoundedContinuousFunction Real Real)
    (dv : BoundedContinuousFunction V (V →L[Real] F))
    (d2v : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hdv : ∀ x, HasFDerivAt (dv : V → V →L[Real] F) (d2v x) x)
    (t : Real) (x : V) :
    HasFDerivAt (separableBoundedContinuousFunctionPath eta dv t : V → V →L[Real] F)
      (eta t • d2v x) x := by
  change HasFDerivAt (fun y => eta t • dv y) (eta t • d2v x) x
  exact (hdv x).const_smul (eta t)

omit [NormedSpace Real V] in
theorem separableBoundedContinuousFunctionPath_holderWith_restrict
    {alpha Keta Kv Meta Mv : NNReal} {J : Set Real}
    (eta : BoundedContinuousFunction Real Real)
    (v : BoundedContinuousFunction V F)
    (heta : HolderWith Keta (alpha / 2) (eta : Real → Real))
    (hv : HolderWith Kv alpha (v : V → F))
    (hetaNorm : ∀ t, ‖eta t‖ ≤ Meta)
    (hvNorm : ∀ x, ‖v x‖ ≤ Mv) :
    HolderWith (Meta * Kv + Mv * Keta) alpha
      ((parabolicCylinder J Set.univ).domRestrict
        (fun p ↦ separableBoundedContinuousFunctionPath eta v p.time p.space)) := by
  let Q := parabolicCylinder J (Set.univ : Set V)
  have hetaFull : HolderWith Keta alpha
      (fun p : ParabolicPoint V ↦ eta p.time) :=
    holderWith_parabolic_const_space heta
  have hetaQ : HolderWith Keta alpha
      (Q.domRestrict (fun p : ParabolicPoint V ↦ eta p.time)) :=
    (hetaFull.holderOnWith Q).holderWith
  have hvQ : HolderWith Kv alpha
      (Q.domRestrict (fun p : ParabolicPoint V ↦ v p.space)) :=
    holderWith_parabolic_const_time (v : V → F) hv J
  have hproduct := holderWith_smul_of_norm_le hetaQ hvQ
    (fun p ↦ hetaNorm p.1.time) (fun p ↦ hvNorm p.1.space)
  change HolderWith (Meta * Kv + Mv * Keta) alpha
    (fun p : Q ↦ eta p.1.time • v p.1.space) at hproduct
  change HolderWith (Meta * Kv + Mv * Keta) alpha
    (fun p : parabolicCylinder J (Set.univ : Set V) ↦
      eta p.1.time • v p.1.space)
  simpa only [Q] using hproduct

end Spatial

end DifferentialGeometry.Analysis.Schauder

end
