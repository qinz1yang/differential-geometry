import DifferentialGeometry.Analysis.Schauder.ParabolicCutoff

noncomputable section

open Real Set
open scoped BoundedContinuousFunction NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]

def parabolicBallCutoff
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    Real → BoundedContinuousFunction V Real :=
  separableBcfPath (intervalCutoffBcf a t₀ t₁ b ha ht hb)
    (ballCutoffBcf center hr hrR)

def parabolicBallCutoffTimeDerivative
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    Real → BoundedContinuousFunction V Real :=
  separableBcfPath (intervalCutoffDerivBcf a t₀ t₁ b ha ht hb)
    (ballCutoffBcf center hr hrR)

def parabolicBallCutoffSpatialFDeriv
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    Real → BoundedContinuousFunction V (V →L[Real] Real) :=
  separableBcfPath (intervalCutoffBcf a t₀ t₁ b ha ht hb)
    (ballCutoffFDerivBcf center hr hrR)

def parabolicBallCutoffSpatialFDeriv2
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    Real → BoundedContinuousFunction V (V →L[Real] V →L[Real] Real) :=
  separableBcfPath (intervalCutoffBcf a t₀ t₁ b ha ht hb)
    (ballCutoffFDeriv2Bcf center hr hrR)

@[simp]
theorem parabolicBallCutoff_apply
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (t : Real) (x : V) :
    parabolicBallCutoff a t₀ t₁ b ha ht hb center hr hrR t x =
      intervalCutoffBcf a t₀ t₁ b ha ht hb t •
        ballCutoff center r R x := rfl

@[simp]
theorem parabolicBallCutoffTimeDerivative_apply
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (t : Real) (x : V) :
    parabolicBallCutoffTimeDerivative a t₀ t₁ b ha ht hb center hr hrR t x =
      intervalCutoffDerivBcf a t₀ t₁ b ha ht hb t •
        ballCutoff center r R x := rfl

@[simp]
theorem parabolicBallCutoffSpatialFDeriv_apply
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (t : Real) (x : V) :
    parabolicBallCutoffSpatialFDeriv a t₀ t₁ b ha ht hb center hr hrR t x =
      intervalCutoffBcf a t₀ t₁ b ha ht hb t •
        ballCutoffFDeriv center r R x := rfl

@[simp]
theorem parabolicBallCutoffSpatialFDeriv2_apply
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (t : Real) (x : V) :
    parabolicBallCutoffSpatialFDeriv2 a t₀ t₁ b ha ht hb center hr hrR t x =
      intervalCutoffBcf a t₀ t₁ b ha ht hb t •
        ballCutoffFDeriv2 center r R x := rfl

theorem parabolicBallCutoff_hasDerivAt
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (t : Real) :
    HasDerivAt (parabolicBallCutoff a t₀ t₁ b ha ht hb center hr hrR)
      (parabolicBallCutoffTimeDerivative
        a t₀ t₁ b ha ht hb center hr hrR t) t := by
  exact separableBcfPath_hasDerivAt
    (intervalCutoffBcf a t₀ t₁ b ha ht hb)
    (intervalCutoffDerivBcf a t₀ t₁ b ha ht hb)
    (ballCutoffBcf center hr hrR) t
    (intervalCutoffBcf_hasDerivAt ha ht hb t)

theorem parabolicBallCutoff_hasFDerivAt
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (t : Real) (x : V) :
    HasFDerivAt
      (parabolicBallCutoff a t₀ t₁ b ha ht hb center hr hrR t : V → Real)
      (parabolicBallCutoffSpatialFDeriv
        a t₀ t₁ b ha ht hb center hr hrR t x) x := by
  exact separableBcfPath_hasFDerivAt
    (intervalCutoffBcf a t₀ t₁ b ha ht hb)
    (ballCutoffBcf center hr hrR) (ballCutoffFDerivBcf center hr hrR)
    (hasFDerivAt_ballCutoff center r R) t x

theorem parabolicBallCutoffSpatialFDeriv_hasFDerivAt
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (t : Real) (x : V) :
    HasFDerivAt
      (parabolicBallCutoffSpatialFDeriv
        a t₀ t₁ b ha ht hb center hr hrR t : V → V →L[Real] Real)
      (parabolicBallCutoffSpatialFDeriv2
        a t₀ t₁ b ha ht hb center hr hrR t x) x := by
  exact separableBcfPath_fderiv_hasFDerivAt
    (intervalCutoffBcf a t₀ t₁ b ha ht hb)
    (ballCutoffFDerivBcf center hr hrR)
    (ballCutoffFDeriv2Bcf center hr hrR)
    (hasFDerivAt_ballCutoffFDeriv center r R) t x

theorem parabolicBallCutoff_eq_one
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {t : Real} (htmem : t ∈ Icc t₀ t₁)
    {x : V} (hx : x ∈ Metric.closedBall center r) :
    parabolicBallCutoff a t₀ t₁ b ha ht hb center hr hrR t x = 1 := by
  rw [parabolicBallCutoff_apply,
    intervalCutoffBcf_eq_one ha ht hb htmem,
    ballCutoff_eq_one_of_mem_closedBall hr hrR hx, one_smul]

theorem parabolicBallCutoff_eq_zero_of_time_not_mem
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {t : Real} (htmem : t ∉ Ioo a b) :
    parabolicBallCutoff a t₀ t₁ b ha ht hb center hr hrR t = 0 := by
  ext x
  rw [parabolicBallCutoff_apply,
    intervalCutoffBcf_eq_zero_of_not_mem ha ht hb htmem, zero_smul]
  rfl

theorem parabolicBallCutoffTimeDerivative_eq_zero_of_time_not_mem
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {t : Real} (htmem : t ∉ Ioo a b) :
    parabolicBallCutoffTimeDerivative
      a t₀ t₁ b ha ht hb center hr hrR t = 0 := by
  ext x
  rw [parabolicBallCutoffTimeDerivative_apply,
    intervalCutoffDerivBcf_eq_zero_of_not_mem ha ht hb htmem, zero_smul]
  rfl

theorem parabolicBallCutoff_eq_zero_of_space_not_mem
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (t : Real) {x : V} (hx : x ∉ Metric.ball center R) :
    parabolicBallCutoff a t₀ t₁ b ha ht hb center hr hrR t x = 0 := by
  rw [parabolicBallCutoff_apply,
    ballCutoff_eq_zero_of_not_mem_ball hr hrR hx, smul_zero]

theorem parabolicBallCutoffTimeDerivative_eq_zero_of_space_not_mem
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (t : Real) {x : V} (hx : x ∉ Metric.ball center R) :
    parabolicBallCutoffTimeDerivative
      a t₀ t₁ b ha ht hb center hr hrR t x = 0 := by
  rw [parabolicBallCutoffTimeDerivative_apply,
    ballCutoff_eq_zero_of_not_mem_ball hr hrR hx, smul_zero]

theorem parabolicBallCutoffSpatialFDeriv_eq_zero_of_space_not_mem
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (t : Real) {x : V} (hx : x ∉ Metric.ball center R) :
    parabolicBallCutoffSpatialFDeriv
      a t₀ t₁ b ha ht hb center hr hrR t x = 0 := by
  rw [parabolicBallCutoffSpatialFDeriv_apply,
    ballCutoffFDeriv_eq_zero_of_not_mem_ball hr hrR hx, smul_zero]

theorem parabolicBallCutoffSpatialFDeriv2_eq_zero_of_space_not_mem
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (t : Real) {x : V} (hx : x ∉ Metric.ball center R) :
    parabolicBallCutoffSpatialFDeriv2
      a t₀ t₁ b ha ht hb center hr hrR t x = 0 := by
  rw [parabolicBallCutoffSpatialFDeriv2_apply,
    ballCutoffFDeriv2_eq_zero_of_not_mem_ball hr hrR hx, smul_zero]

def parabolicBallCutoffSpatialFDerivSupConst (r R : Real) : NNReal :=
  Real.toNNReal (ballCutoffFDerivBound r R)

def parabolicBallCutoffSpatialFDeriv2SupConst (r R : Real) : NNReal :=
  Real.toNNReal (ballCutoffFDeriv2Bound r R)

def parabolicBallCutoffHolderConst
    (a t₀ t₁ b r R : Real) : NNReal :=
  ballCutoffHolderConst r R + intervalCutoffHolderConst a t₀ t₁ b

def parabolicBallCutoffTimeDerivativeHolderConst
    (a t₀ t₁ b r R : Real) : NNReal :=
  intervalCutoffDerivSupConst a t₀ t₁ b * ballCutoffHolderConst r R +
    intervalCutoffDerivHolderConst a t₀ t₁ b

def parabolicBallCutoffSpatialFDerivHolderConst
    (a t₀ t₁ b r R : Real) : NNReal :=
  ballCutoffFDerivHolderConst r R +
    parabolicBallCutoffSpatialFDerivSupConst r R *
      intervalCutoffHolderConst a t₀ t₁ b

def parabolicBallCutoffSpatialFDeriv2HolderConst
    (a t₀ t₁ b : Real) (center : V)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R) : NNReal :=
  ballCutoffFDeriv2HolderConst center hr hrR +
    parabolicBallCutoffSpatialFDeriv2SupConst r R *
      intervalCutoffHolderConst a t₀ t₁ b

theorem norm_parabolicBallCutoff_le_one
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (t : Real) (x : V) :
    ‖parabolicBallCutoff a t₀ t₁ b ha ht hb center hr hrR t x‖ ≤ 1 := by
  rw [parabolicBallCutoff_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (intervalCutoffBcf_mem_Icc ha ht hb t).1,
    Real.norm_eq_abs, abs_of_nonneg (ballCutoff_mem_Icc center r R x).1]
  exact mul_le_one₀ (intervalCutoffBcf_mem_Icc ha ht hb t).2
    (ballCutoff_mem_Icc center r R x).1
    (ballCutoff_mem_Icc center r R x).2

theorem norm_parabolicBallCutoffTimeDerivative_le
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (t : Real) (x : V) :
    ‖parabolicBallCutoffTimeDerivative
      a t₀ t₁ b ha ht hb center hr hrR t x‖ ≤
        intervalCutoffDerivSupConst a t₀ t₁ b := by
  rw [parabolicBallCutoffTimeDerivative_apply, norm_smul]
  calc
    ‖intervalCutoffDerivBcf a t₀ t₁ b ha ht hb t‖ *
        ‖ballCutoff center r R x‖ ≤
        ‖intervalCutoffDerivBcf a t₀ t₁ b ha ht hb t‖ := by
      exact mul_le_of_le_one_right (norm_nonneg _)
        (by
          rw [Real.norm_eq_abs,
            abs_of_nonneg (ballCutoff_mem_Icc center r R x).1]
          exact (ballCutoff_mem_Icc center r R x).2)
    _ ≤ intervalCutoffDerivSupConst a t₀ t₁ b :=
      norm_intervalCutoffDerivBcf_le ha ht hb t

theorem norm_parabolicBallCutoffSpatialFDeriv_le
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (t : Real) (x : V) :
    ‖parabolicBallCutoffSpatialFDeriv
      a t₀ t₁ b ha ht hb center hr hrR t x‖ ≤
        parabolicBallCutoffSpatialFDerivSupConst r R := by
  rw [parabolicBallCutoffSpatialFDeriv_apply, norm_smul]
  have hbound := ballCutoffFDerivBound_nonneg hr hrR
  calc
    ‖intervalCutoffBcf a t₀ t₁ b ha ht hb t‖ *
        ‖ballCutoffFDeriv center r R x‖ ≤
        ‖ballCutoffFDeriv center r R x‖ := by
      exact mul_le_of_le_one_left (norm_nonneg _)
        (norm_intervalCutoffBcf_le_one ha ht hb t)
    _ ≤ ballCutoffFDerivBound r R := norm_ballCutoffFDeriv_le hr hrR x
    _ = parabolicBallCutoffSpatialFDerivSupConst r R := by
      rw [parabolicBallCutoffSpatialFDerivSupConst,
        Real.coe_toNNReal _ hbound]

theorem norm_parabolicBallCutoffSpatialFDeriv2_le
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (t : Real) (x : V) :
    ‖parabolicBallCutoffSpatialFDeriv2
      a t₀ t₁ b ha ht hb center hr hrR t x‖ ≤
        parabolicBallCutoffSpatialFDeriv2SupConst r R := by
  rw [parabolicBallCutoffSpatialFDeriv2_apply, norm_smul]
  have hbound := ballCutoffFDeriv2Bound_nonneg hr hrR
  calc
    ‖intervalCutoffBcf a t₀ t₁ b ha ht hb t‖ *
        ‖ballCutoffFDeriv2 center r R x‖ ≤
        ‖ballCutoffFDeriv2 center r R x‖ := by
      exact mul_le_of_le_one_left (norm_nonneg _)
        (norm_intervalCutoffBcf_le_one ha ht hb t)
    _ ≤ ballCutoffFDeriv2Bound r R := norm_ballCutoffFDeriv2_le hr hrR x
    _ = parabolicBallCutoffSpatialFDeriv2SupConst r R := by
      rw [parabolicBallCutoffSpatialFDeriv2SupConst,
        Real.coe_toNNReal _ hbound]

theorem parabolicBallCutoff_holderWith_restrict
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {alpha : NNReal} (halpha1 : alpha ≤ 1) (J : Set Real) :
    HolderWith (parabolicBallCutoffHolderConst a t₀ t₁ b r R) alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ parabolicBallCutoff
          a t₀ t₁ b ha ht hb center hr hrR p.time p.space)) := by
  have htime := intervalCutoffBcf_holderWith ha ht hb
    ((div_le_iff₀ (by norm_num : (0 : NNReal) < 2)).2
      (by simpa using halpha1.trans (show (1 : NNReal) ≤ 2 by norm_num)))
  have hspace := ballCutoff_holderWith (V := V) (center := center)
    hr hrR (zero_le alpha) halpha1
  have h := separableBcfPath_holderWith_restrict
    (Meta := 1) (Mv := 1) (J := J)
    (intervalCutoffBcf a t₀ t₁ b ha ht hb)
    (ballCutoffBcf center hr hrR) htime hspace
    (fun t ↦ norm_intervalCutoffBcf_le_one ha ht hb t)
    (fun x ↦ by
      rw [ballCutoffBcf_apply, Real.norm_eq_abs,
        abs_of_nonneg (ballCutoff_mem_Icc center r R x).1]
      exact (ballCutoff_mem_Icc center r R x).2)
  simpa only [parabolicBallCutoffHolderConst, one_mul,
    parabolicBallCutoff] using h

theorem parabolicBallCutoffTimeDerivative_holderWith_restrict
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {alpha : NNReal} (halpha1 : alpha ≤ 1) (J : Set Real) :
    HolderWith
      (parabolicBallCutoffTimeDerivativeHolderConst a t₀ t₁ b r R)
      alpha ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ parabolicBallCutoffTimeDerivative
          a t₀ t₁ b ha ht hb center hr hrR p.time p.space)) := by
  have htime := intervalCutoffDerivBcf_holderWith ha ht hb
    ((div_le_iff₀ (by norm_num : (0 : NNReal) < 2)).2
      (by simpa using halpha1.trans (show (1 : NNReal) ≤ 2 by norm_num)))
  have hspace := ballCutoff_holderWith (V := V) (center := center)
    hr hrR (zero_le alpha) halpha1
  have h := separableBcfPath_holderWith_restrict
    (Meta := intervalCutoffDerivSupConst a t₀ t₁ b) (Mv := 1) (J := J)
    (intervalCutoffDerivBcf a t₀ t₁ b ha ht hb)
    (ballCutoffBcf center hr hrR) htime hspace
    (fun t ↦ norm_intervalCutoffDerivBcf_le ha ht hb t)
    (fun x ↦ by
      rw [ballCutoffBcf_apply, Real.norm_eq_abs,
        abs_of_nonneg (ballCutoff_mem_Icc center r R x).1]
      exact (ballCutoff_mem_Icc center r R x).2)
  simpa only [parabolicBallCutoffTimeDerivativeHolderConst,
    one_mul, parabolicBallCutoffTimeDerivative] using h

theorem parabolicBallCutoffSpatialFDeriv_holderWith_restrict
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {alpha : NNReal} (halpha1 : alpha ≤ 1) (J : Set Real) :
    HolderWith
      (parabolicBallCutoffSpatialFDerivHolderConst a t₀ t₁ b r R)
      alpha ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ parabolicBallCutoffSpatialFDeriv
          a t₀ t₁ b ha ht hb center hr hrR p.time p.space)) := by
  have htime := intervalCutoffBcf_holderWith ha ht hb
    ((div_le_iff₀ (by norm_num : (0 : NNReal) < 2)).2
      (by simpa using halpha1.trans (show (1 : NNReal) ≤ 2 by norm_num)))
  have hspace := ballCutoffFDeriv_holderWith (V := V) (center := center)
    hr hrR (zero_le alpha) halpha1
  have hbound := ballCutoffFDerivBound_nonneg hr hrR
  have h := separableBcfPath_holderWith_restrict
    (Meta := 1) (Mv := parabolicBallCutoffSpatialFDerivSupConst r R)
    (J := J)
    (intervalCutoffBcf a t₀ t₁ b ha ht hb)
    (ballCutoffFDerivBcf center hr hrR) htime hspace
    (fun t ↦ norm_intervalCutoffBcf_le_one ha ht hb t)
    (fun x ↦ by
      rw [ballCutoffFDerivBcf_apply,
        parabolicBallCutoffSpatialFDerivSupConst,
        Real.coe_toNNReal _ hbound]
      exact norm_ballCutoffFDeriv_le hr hrR x)
  simpa only [parabolicBallCutoffSpatialFDerivHolderConst,
    one_mul, parabolicBallCutoffSpatialFDeriv] using h

theorem parabolicBallCutoffSpatialFDeriv2_holderWith_restrict
    (a t₀ t₁ b : Real) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {alpha : NNReal} (halpha1 : alpha ≤ 1) (J : Set Real) :
    HolderWith
      (parabolicBallCutoffSpatialFDeriv2HolderConst
        a t₀ t₁ b center hr hrR)
      alpha ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ parabolicBallCutoffSpatialFDeriv2
          a t₀ t₁ b ha ht hb center hr hrR p.time p.space)) := by
  have htime := intervalCutoffBcf_holderWith ha ht hb
    ((div_le_iff₀ (by norm_num : (0 : NNReal) < 2)).2
      (by simpa using halpha1.trans (show (1 : NNReal) ≤ 2 by norm_num)))
  have hspace := ballCutoffFDeriv2_holderWith (V := V) (center := center)
    hr hrR (zero_le alpha) halpha1
  have hbound := ballCutoffFDeriv2Bound_nonneg hr hrR
  have h := separableBcfPath_holderWith_restrict
    (Meta := 1) (Mv := parabolicBallCutoffSpatialFDeriv2SupConst r R)
    (J := J)
    (intervalCutoffBcf a t₀ t₁ b ha ht hb)
    (ballCutoffFDeriv2Bcf center hr hrR) htime hspace
    (fun t ↦ norm_intervalCutoffBcf_le_one ha ht hb t)
    (fun x ↦ by
      rw [ballCutoffFDeriv2Bcf_apply,
        parabolicBallCutoffSpatialFDeriv2SupConst,
        Real.coe_toNNReal _ hbound]
      exact norm_ballCutoffFDeriv2_le hr hrR x)
  simpa only [parabolicBallCutoffSpatialFDeriv2HolderConst,
    one_mul, parabolicBallCutoffSpatialFDeriv2] using h

end DifferentialGeometry.Analysis.Schauder

end
