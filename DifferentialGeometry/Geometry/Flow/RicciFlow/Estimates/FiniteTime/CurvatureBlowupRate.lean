import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Curvature.NormHeatEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.HeatEquation
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff BigOperators

section Barrier

def curvatureCubicReaction (c0 a : Real) : Real :=
  c0 * (a * Real.sqrt a)

def curvatureNormSqBarrier (c0 Q0 t : Real) : Real :=
  Q0 ^ 2 / ((1 - c0 * Q0 * t / 2) * (1 - c0 * Q0 * t / 2))

def curvatureDoublingSpan (c0 Q0 : Real) : Real :=
  1 / (c0 * Q0)

private theorem cube_sub_le_of_le
    {r p q : Real} (hq0 : 0 ≤ q) (hqp : q ≤ p) (hpr : p ≤ r) :
    p * p * p - q * q * q ≤ 3 * r * (p * p - q * q) := by
  have hp0 : (0 : Real) ≤ p := le_trans hq0 hqp
  have hpq : (0 : Real) ≤ p - q := sub_nonneg.mpr hqp
  have hqq : q * q ≤ p * p := mul_le_mul hqp hqp hq0 hp0
  have hpq0 : (0 : Real) ≤ p + q := by linarith
  have h1 : 3 * p * (p + q) ≤ 3 * r * (p + q) := by
    linarith [mul_nonneg hpq0 (sub_nonneg.mpr hpr)]
  have h2 : p * p + p * q + q * q ≤ 3 * p * (p + q) := by
    linarith [mul_nonneg hp0 hq0, mul_self_nonneg p]
  have hkey : p * p + p * q + q * q ≤ 3 * r * (p + q) := by linarith
  calc
    p * p * p - q * q * q = (p - q) * (p * p + p * q + q * q) := by ring
    _ ≤ (p - q) * (3 * r * (p + q)) := mul_le_mul_of_nonneg_left hkey hpq
    _ = 3 * r * (p * p - q * q) := by ring

private theorem mul_sqrt_self_le_of_le {a b : Real} (hba : b ≤ a) :
    b * Real.sqrt b ≤ a * Real.sqrt a := by
  rcases le_total a 0 with ha | ha
  · have hb : b ≤ 0 := le_trans hba ha
    rw [Real.sqrt_eq_zero_of_nonpos ha, Real.sqrt_eq_zero_of_nonpos hb]
    simp
  · rcases le_total b 0 with hb | hb
    · rw [Real.sqrt_eq_zero_of_nonpos hb]
      have hnn : (0 : Real) ≤ a * Real.sqrt a :=
        mul_nonneg ha (Real.sqrt_nonneg a)
      linarith
    · exact mul_le_mul hba (Real.sqrt_le_sqrt hba) (Real.sqrt_nonneg b) ha

private theorem mul_sqrt_self_sub_le
    {R a b : Real} (hba : b ≤ a) (haR : a ≤ R) :
    a * Real.sqrt a - b * Real.sqrt b ≤ 3 * Real.sqrt R * (a - b) := by
  have hsR : (0 : Real) ≤ Real.sqrt R := Real.sqrt_nonneg R
  rcases le_total a 0 with ha | ha
  · have hb : b ≤ 0 := le_trans hba ha
    rw [Real.sqrt_eq_zero_of_nonpos ha, Real.sqrt_eq_zero_of_nonpos hb]
    have hnn : (0 : Real) ≤ 3 * Real.sqrt R * (a - b) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  · have hsa : Real.sqrt a ≤ Real.sqrt R := Real.sqrt_le_sqrt haR
    rcases le_total b 0 with hb | hb
    · rw [Real.sqrt_eq_zero_of_nonpos hb]
      have h1 : a * Real.sqrt a ≤ a * Real.sqrt R :=
        mul_le_mul_of_nonneg_left hsa ha
      have h2 : a * Real.sqrt R ≤ 3 * Real.sqrt R * (a - b) := by
        linarith [mul_nonneg hsR (by linarith : (0 : Real) ≤ 2 * a - 3 * b)]
      linarith
    · have hpa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha
      have hpb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb
      have hsab : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt hba
      have hcube := cube_sub_le_of_le (r := Real.sqrt R)
        (Real.sqrt_nonneg b) hsab hsa
      rw [hpa, hpb] at hcube
      exact hcube

theorem curvatureCubicReaction_monotone
    {c0 : Real} (hc0 : 0 ≤ c0) {a b : Real} (hba : b ≤ a) :
    curvatureCubicReaction c0 b ≤ curvatureCubicReaction c0 a := by
  unfold curvatureCubicReaction
  exact mul_le_mul_of_nonneg_left (mul_sqrt_self_le_of_le hba) hc0

theorem lipschitzOnWith_curvatureCubicReaction
    {c0 R : Real} (hc0 : 0 ≤ c0) :
    LipschitzOnWith (Real.toNNReal (3 * c0 * Real.sqrt R))
      (fun a : Real => curvatureCubicReaction c0 a) (Set.Iic R) := by
  have hcoe : ((Real.toNNReal (3 * c0 * Real.sqrt R) : NNReal) : Real) =
      3 * c0 * Real.sqrt R :=
    Real.coe_toNNReal _ (by positivity)
  have key : ∀ p q : Real, q ≤ p → p ≤ R →
      curvatureCubicReaction c0 p - curvatureCubicReaction c0 q ≤
        3 * c0 * Real.sqrt R * (p - q) := by
    intro p q hqp hpR
    have h := mul_sqrt_self_sub_le hqp hpR
    have h2 : c0 * (p * Real.sqrt p - q * Real.sqrt q) ≤
        c0 * (3 * Real.sqrt R * (p - q)) := mul_le_mul_of_nonneg_left h hc0
    unfold curvatureCubicReaction
    nlinarith [h2]
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro a ha b hb
  have ha' : a ≤ R := ha
  have hb' : b ≤ R := hb
  rw [Real.dist_eq, Real.dist_eq, hcoe]
  rcases le_total b a with hab | hab
  · have h1 := key a b hab ha'
    have h2 := curvatureCubicReaction_monotone hc0 hab
    rw [abs_of_nonneg (sub_nonneg.mpr h2), abs_of_nonneg (sub_nonneg.mpr hab)]
    exact h1
  · have h1 := key b a hab hb'
    have h2 := curvatureCubicReaction_monotone hc0 hab
    rw [abs_of_nonpos (sub_nonpos.mpr h2), abs_of_nonpos (sub_nonpos.mpr hab)]
    linarith

theorem curvatureNormSqBarrier_zero (c0 Q0 : Real) :
    curvatureNormSqBarrier c0 Q0 0 = Q0 ^ 2 := by
  unfold curvatureNormSqBarrier
  norm_num

theorem curvatureDoublingSpan_mul_le_one
    {c0 Q0 t : Real} (hc0 : 0 < c0) (hQ0 : 0 < Q0)
    (ht : t ≤ curvatureDoublingSpan c0 Q0) :
    c0 * Q0 * t ≤ 1 := by
  have hc0' : c0 ≠ 0 := ne_of_gt hc0
  have hQ0' : Q0 ≠ 0 := ne_of_gt hQ0
  have hpos : (0 : Real) < c0 * Q0 := mul_pos hc0 hQ0
  have hmul : c0 * Q0 * t ≤ c0 * Q0 * curvatureDoublingSpan c0 Q0 :=
    mul_le_mul_of_nonneg_left ht (le_of_lt hpos)
  have heq : c0 * Q0 * curvatureDoublingSpan c0 Q0 = 1 := by
    unfold curvatureDoublingSpan
    field_simp
  linarith [heq.symm.le, heq.le]

theorem curvatureNormSqBarrier_denominator_pos
    {c0 Q0 t : Real} (hc0 : 0 < c0) (hQ0 : 0 < Q0)
    (ht : t ≤ curvatureDoublingSpan c0 Q0) :
    (1 : Real) / 2 ≤ 1 - c0 * Q0 * t / 2 :=
  by linarith [curvatureDoublingSpan_mul_le_one hc0 hQ0 ht]

theorem curvatureNormSqBarrier_hasDerivWithinAt
    (s : Set Real) {c0 Q0 t : Real} (hc0 : 0 < c0) (hQ0 : 0 < Q0)
    (ht : t ≤ curvatureDoublingSpan c0 Q0) :
    HasDerivWithinAt (curvatureNormSqBarrier c0 Q0)
      (curvatureCubicReaction c0 (curvatureNormSqBarrier c0 Q0 t)) s t := by
  have hhalf : (1 : Real) / 2 ≤ 1 - c0 * Q0 * t / 2 :=
    curvatureNormSqBarrier_denominator_pos hc0 hQ0 ht
  have hwpos : (0 : Real) < 1 - c0 * Q0 * t / 2 := by linarith
  have hwne : (1 - c0 * Q0 * t / 2) ≠ 0 := ne_of_gt hwpos
  have hlin : HasDerivAt (fun r : Real => 1 - c0 * Q0 * r / 2) (-(c0 * Q0 / 2)) t := by
    have h1 : HasDerivAt (fun r : Real => c0 * Q0 * r / 2) (c0 * Q0 / 2) t := by
      simpa using ((hasDerivAt_id t).const_mul (c0 * Q0)).div_const 2
    simpa using h1.const_sub 1
  have hden : HasDerivAt
      (fun r : Real => (1 - c0 * Q0 * r / 2) * (1 - c0 * Q0 * r / 2))
      (-(c0 * Q0 / 2) * (1 - c0 * Q0 * t / 2) +
        (1 - c0 * Q0 * t / 2) * -(c0 * Q0 / 2)) t := hlin.mul hlin
  have hnum : HasDerivAt (fun _ : Real => Q0 ^ 2) 0 t := hasDerivAt_const t (Q0 ^ 2)
  have hquot : HasDerivAt
      (fun r : Real => Q0 ^ 2 / ((1 - c0 * Q0 * r / 2) * (1 - c0 * Q0 * r / 2)))
      ((0 * ((1 - c0 * Q0 * t / 2) * (1 - c0 * Q0 * t / 2)) -
          Q0 ^ 2 * (-(c0 * Q0 / 2) * (1 - c0 * Q0 * t / 2) +
            (1 - c0 * Q0 * t / 2) * -(c0 * Q0 / 2))) /
        ((1 - c0 * Q0 * t / 2) * (1 - c0 * Q0 * t / 2)) ^ 2) t :=
    hnum.div hden (mul_ne_zero hwne hwne)
  have hsqrt : Real.sqrt (curvatureNormSqBarrier c0 Q0 t) =
      Q0 / (1 - c0 * Q0 * t / 2) := by
    have hrw : curvatureNormSqBarrier c0 Q0 t = (Q0 / (1 - c0 * Q0 * t / 2)) ^ 2 := by
      unfold curvatureNormSqBarrier
      rw [div_pow, pow_two (1 - c0 * Q0 * t / 2)]
    rw [hrw, Real.sqrt_sq (le_of_lt (div_pos hQ0 hwpos))]
  have hvalue :
      ((0 * ((1 - c0 * Q0 * t / 2) * (1 - c0 * Q0 * t / 2)) -
          Q0 ^ 2 * (-(c0 * Q0 / 2) * (1 - c0 * Q0 * t / 2) +
            (1 - c0 * Q0 * t / 2) * -(c0 * Q0 / 2))) /
        ((1 - c0 * Q0 * t / 2) * (1 - c0 * Q0 * t / 2)) ^ 2) =
      curvatureCubicReaction c0 (curvatureNormSqBarrier c0 Q0 t) := by
    unfold curvatureCubicReaction
    rw [hsqrt]
    unfold curvatureNormSqBarrier
    field_simp
    ring
  have hfinal : HasDerivWithinAt
      (fun r : Real => Q0 ^ 2 / ((1 - c0 * Q0 * r / 2) * (1 - c0 * Q0 * r / 2)))
      (curvatureCubicReaction c0 (curvatureNormSqBarrier c0 Q0 t)) s t := by
    rw [← hvalue]
    exact hquot.hasDerivWithinAt
  exact hfinal

theorem curvatureNormSqBarrier_continuousOn
    {c0 Q0 T : Real} (hc0 : 0 < c0) (hQ0 : 0 < Q0)
    (hT : T ≤ curvatureDoublingSpan c0 Q0) :
    ContinuousOn (curvatureNormSqBarrier c0 Q0) (Set.Icc 0 T) := by
  intro t ht
  exact (curvatureNormSqBarrier_hasDerivWithinAt (Set.Icc 0 T) hc0 hQ0
    (le_trans ht.2 hT)).continuousWithinAt

theorem curvatureNormSqBarrier_le_four_mul_sq
    {c0 Q0 t : Real} (hc0 : 0 < c0) (hQ0 : 0 < Q0)
    (ht : t ≤ curvatureDoublingSpan c0 Q0) :
    curvatureNormSqBarrier c0 Q0 t ≤ 4 * Q0 ^ 2 := by
  have hhalf : (1 : Real) / 2 ≤ 1 - c0 * Q0 * t / 2 :=
    curvatureNormSqBarrier_denominator_pos hc0 hQ0 ht
  have hwpos : (0 : Real) < 1 - c0 * Q0 * t / 2 := by linarith
  have hprodpos : (0 : Real) <
      (1 - c0 * Q0 * t / 2) * (1 - c0 * Q0 * t / 2) := mul_pos hwpos hwpos
  have hsq : (1 : Real) / 4 ≤ (1 - c0 * Q0 * t / 2) * (1 - c0 * Q0 * t / 2) := by
    nlinarith
  have hQsq : (0 : Real) ≤ Q0 ^ 2 := sq_nonneg Q0
  unfold curvatureNormSqBarrier
  rw [div_le_iff₀ hprodpos]
  nlinarith [mul_nonneg (by linarith : (0 : Real) ≤ 4 * Q0 ^ 2)
    (by linarith : (0 : Real) ≤
      (1 - c0 * Q0 * t / 2) * (1 - c0 * Q0 * t / 2) - 1 / 4)]

end Barrier

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

omit [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem cubic_heat_subsolution_le_curvatureNormSqBarrier
    [CompactSpace M] [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {c0 Q0 T : Real} (hc0 : 0 < c0) (hQ0 : 0 < Q0)
    (hT0 : 0 ≤ T) (hTspan : T ≤ curvatureDoublingSpan c0 Q0)
    (u : Real -> M -> Real)
    (hsub : IsHeatPotSubsolutionOn (RealTimeInterval.closed 0 T hT0) G
      (fun t x => c0 * Real.sqrt (u t x)) u)
    (hinit : ∀ x : M, u 0 x ≤ Q0 ^ 2) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      u t x ≤ curvatureNormSqBarrier c0 Q0 t := by
  classical
  have hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T) := hsub.jointCont
  have hc_cont : ContinuousOn (curvatureNormSqBarrier c0 Q0) (Set.Icc 0 T) :=
    curvatureNormSqBarrier_continuousOn hc0 hQ0 hTspan
  have hvs : IsCompact
      (scalarWeakMaximumPrincipleValueSet (M := M) T u (curvatureNormSqBarrier c0 Q0)) :=
    scalarWeakMaximumPrincipleValueSet_isCompact (M := M) T u
      (curvatureNormSqBarrier c0 Q0) hu_cont hc_cont
  obtain ⟨R, hR⟩ := hvs.bddAbove
  have hsubset :
      scalarWeakMaximumPrincipleValueSet (M := M) T u (curvatureNormSqBarrier c0 Q0) ⊆
        Set.Iic R := fun a ha => hR ha
  have hlip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith (Real.toNNReal (3 * c0 * Real.sqrt R))
        (fun a : Real => curvatureCubicReaction c0 a)
        (scalarWeakMaximumPrincipleValueSet (M := M) T u
          (curvatureNormSqBarrier c0 Q0)) := by
    intro t _
    exact (lipschitzOnWith_curvatureCubicReaction (le_of_lt hc0)).mono hsubset
  have hc_time : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      DifferentiableWithinAt Real (curvatureNormSqBarrier c0 Q0) (Set.Icc 0 T) t := by
    intro t ht _
    exact (curvatureNormSqBarrier_hasDerivWithinAt (Set.Icc 0 T) hc0 hQ0
      (le_trans ht.2 hTspan)).differentiableWithinAt
  have hF_ge : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (fun t x => c0 * Real.sqrt (u t x)) t x * u t x ≤
        (fun a _t : Real => curvatureCubicReaction c0 a) (u t x) t := by
    intro t _ x
    unfold curvatureCubicReaction
    exact le_of_eq (by ring)
  have hode : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      derivWithin (curvatureNormSqBarrier c0 Q0) (Set.Icc 0 T) t =
        (fun a _t : Real => curvatureCubicReaction c0 a)
          (curvatureNormSqBarrier c0 Q0 t) t := by
    intro t ht htpos
    have hTpos : (0 : Real) < T := lt_of_lt_of_le htpos ht.2
    exact (curvatureNormSqBarrier_hasDerivWithinAt (Set.Icc 0 T) hc0 hQ0
      (le_trans ht.2 hTspan)).derivWithin ((uniqueDiffOn_Icc hTpos) t ht)
  have hinit' : ∀ x : M, u 0 x ≤ curvatureNormSqBarrier c0 Q0 0 := by
    intro x
    rw [curvatureNormSqBarrier_zero]
    exact hinit x
  exact scalar_weak_maximum_principle_ode_compare_subsolution_of_heat_pot
    (I := I) G T hT0 u (curvatureNormSqBarrier c0 Q0)
    (fun a _t : Real => curvatureCubicReaction c0 a)
    (Real.toNNReal (3 * c0 * Real.sqrt R))
    (fun t x => c0 * Real.sqrt (u t x)) hsub hc_cont hc_time hF_ge hode hinit' hlip

omit [I.Boundaryless] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
theorem isHeatPotSubsolutionOn_timeShift_flowG
    {D Dsub Dsub' : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (V u : Real -> M -> Real) (tau : Real)
    (hsub : IsHeatPotSubsolutionOn Dsub (flowG (I := I) S) V u)
    (hcar : ∀ s : Real, s ∈ Dsub'.carrier -> s + tau ∈ Dsub.carrier)
    (hreg : ∀ s : Real, s ∈ Dsub'.regular -> s + tau ∈ Dsub.regular) :
    IsHeatPotSubsolutionOn Dsub' (flowG (I := I) (S.timeShift tau))
      (fun s x => V (s + tau) x) (fun s x => u (s + tau) x) where
  jointSmooth := by
    have hshift : ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I)
        (∞ : WithTop ℕ∞) (fun q : Real × M => (q.1 + tau, q.2)) :=
      ContMDiff.prodMk (contMDiff_fst.add contMDiff_const) contMDiff_snd
    have hmaps : Dsub'.regular ×ˢ (Set.univ : Set M) ⊆
        (fun q : Real × M => (q.1 + tau, q.2)) ⁻¹'
          (Dsub.regular ×ˢ (Set.univ : Set M)) := by
      intro q hq
      exact ⟨hreg q.1 hq.1, trivial⟩
    exact hsub.jointSmooth.comp hshift.contMDiffOn hmaps
  jointCont := by
    have hcont : Continuous (fun q : Real × M => (q.1 + tau, q.2)) := by
      fun_prop
    have hmaps : Dsub'.carrier ×ˢ (Set.univ : Set M) ⊆
        (fun q : Real × M => (q.1 + tau, q.2)) ⁻¹'
          (Dsub.carrier ×ˢ (Set.univ : Set M)) := by
      intro q hq
      exact ⟨hcar q.1 hq.1, trivial⟩
    exact hsub.jointCont.comp hcont.continuousOn hmaps
  sliceSmooth := fun s hs => hsub.sliceSmooth (s + tau) (hcar s hs)
  timeDiff := by
    intro t ht x
    have h2 := (hsub.timeDiff (t + tau) (hreg t ht) x).hasDerivAt
    exact (HasDerivAt.comp_add_const t tau h2).differentiableAt
  equation_le := by
    intro t ht x
    have h2 := (hsub.timeDiff (t + tau) (hreg t ht) x).hasDerivAt
    have h3 : HasDerivAt (fun r : Real => u (r + tau) x)
        (deriv (fun s : Real => u s x) (t + tau)) t :=
      HasDerivAt.comp_add_const t tau h2
    have hgoal : deriv (fun r : Real => u (r + tau) x) t ≤
        laplacianAt (I := I) (flowG (I := I) S) (t + tau) (u (t + tau)) x +
          V (t + tau) x * u (t + tau) x := by
      rw [h3.deriv]
      exact hsub.equation_le (t + tau) (hreg t ht) x
    exact hgoal

omit [SigmaCompactSpace M] in
theorem curvature_norm_sq_doubling
    [CompactSpace M] [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 T c0 Q0 : Real} (hc0 : 0 < c0) (hQ0 : 0 < Q0)
    (hT0 : 0 ≤ T) (hTspan : T ≤ curvatureDoublingSpan c0 Q0)
    (hsub : IsHeatPotSubsolutionOn
      (RealTimeInterval.closed t0 (t0 + T) (le_add_of_nonneg_right hT0))
      (flowG (I := I) S)
      (fun t x => c0 * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x))
      (nablaKRm04NormSqIntrinsic (I := I) S 0))
    (hQ : ∀ x : M, nablaKRm04NormSqIntrinsic (I := I) S 0 t0 x ≤ Q0 ^ 2) :
    ∀ s : Real, s ∈ Set.Icc t0 (t0 + T) -> ∀ x : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s x ≤ 4 * Q0 ^ 2 := by
  have hcar : ∀ s : Real, s ∈ (RealTimeInterval.closed 0 T hT0).carrier ->
      s + t0 ∈ (RealTimeInterval.closed t0 (t0 + T)
        (le_add_of_nonneg_right hT0)).carrier := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : Real) T := hs
    exact ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
  have hreg : ∀ s : Real, s ∈ (RealTimeInterval.closed 0 T hT0).regular ->
      s + t0 ∈ (RealTimeInterval.closed t0 (t0 + T)
        (le_add_of_nonneg_right hT0)).regular := by
    intro s hs
    have hs' : s ∈ Set.Ioo (0 : Real) T := hs
    exact ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
  have hshift := isHeatPotSubsolutionOn_timeShift_flowG
    (Dsub' := RealTimeInterval.closed 0 T hT0) S
    (fun t x => c0 * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x))
    (nablaKRm04NormSqIntrinsic (I := I) S 0) t0 hsub hcar hreg
  have hinit : ∀ x : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 (0 + t0) x ≤ Q0 ^ 2 := by
    intro x
    simpa using hQ x
  have hle := cubic_heat_subsolution_le_curvatureNormSqBarrier
    (I := I) (flowG (I := I) (S.timeShift t0)) hc0 hQ0 hT0 hTspan
    (fun s x => nablaKRm04NormSqIntrinsic (I := I) S 0 (s + t0) x) hshift hinit
  intro s hs x
  have hs' : s - t0 ∈ Set.Icc (0 : Real) T :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hbound := hle (s - t0) hs' x
  have hbar := curvatureNormSqBarrier_le_four_mul_sq (c0 := c0) (Q0 := Q0)
    (t := s - t0) hc0 hQ0 (le_trans hs'.2 hTspan)
  have heq : s - t0 + t0 = s := by ring
  rw [heq] at hbound
  linarith

def Rm04NormSqUnboundedOn
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) : Prop :=
  ∀ K : Real, ∃ t : Real, ∃ x : M,
    t ∈ D.carrier ∧ K < nablaKRm04NormSqIntrinsic (I := I) S 0 t x

omit [SigmaCompactSpace M] in
theorem curvatureDoublingSpan_le_of_rm04NormSqUnbounded
    [CompactSpace M] [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    {t0 c0 Q0 : Real} (hc0 : 0 < c0) (hQ0 : 0 < Q0)
    (hsub : IsHeatPotSubsolutionOn
      (RealTimeInterval.closedOpen alpha omega halphaomega) (flowG (I := I) S)
      (fun t x => c0 * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 0 t x))
      (nablaKRm04NormSqIntrinsic (I := I) S 0))
    (hunb : Rm04NormSqUnboundedOn (I := I) S)
    (ht0 : t0 ∈ Set.Ico alpha omega)
    (hQ : ∀ x : M, nablaKRm04NormSqIntrinsic (I := I) S 0 t0 x ≤ Q0 ^ 2) :
    curvatureDoublingSpan c0 Q0 ≤ omega - t0 := by
  classical
  by_contra hnot
  have hlt : omega - t0 < curvatureDoublingSpan c0 Q0 := lt_of_not_ge hnot
  have hearly_cont : ContinuousOn
      (fun p : Real × M => nablaKRm04NormSqIntrinsic (I := I) S 0 p.1 p.2)
      (Set.Icc alpha t0 ×ˢ (Set.univ : Set M)) := by
    refine hsub.jointCont.mono ?_
    intro q hq
    exact ⟨⟨hq.1.1, lt_of_le_of_lt hq.1.2 ht0.2⟩, trivial⟩
  have hcompact : IsCompact (Set.Icc alpha t0 ×ˢ (Set.univ : Set M)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨B, hB⟩ := (hcompact.image_of_continuousOn hearly_cont).bddAbove
  have hearly : ∀ t : Real, ∀ x : M, alpha ≤ t -> t ≤ t0 ->
      nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ B := by
    intro t x h1 h2
    exact hB ⟨(t, x), ⟨⟨h1, h2⟩, trivial⟩, rfl⟩
  have hlate : ∀ t : Real, ∀ x : M, t0 ≤ t -> t < omega ->
      nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ 4 * Q0 ^ 2 := by
    intro t x h1 h2
    have hT0 : (0 : Real) ≤ t - t0 := by linarith
    have hTspan : t - t0 ≤ curvatureDoublingSpan c0 Q0 := by linarith
    have hcar : (RealTimeInterval.closed t0 (t0 + (t - t0))
        (le_add_of_nonneg_right hT0)).carrier ⊆
        (RealTimeInterval.closedOpen alpha omega halphaomega).carrier := by
      intro s hs
      have hs' : s ∈ Set.Icc t0 (t0 + (t - t0)) := hs
      exact ⟨by linarith [hs'.1, ht0.1], by linarith [hs'.2]⟩
    have hreg : (RealTimeInterval.closed t0 (t0 + (t - t0))
        (le_add_of_nonneg_right hT0)).regular ⊆
        (RealTimeInterval.closedOpen alpha omega halphaomega).regular := by
      intro s hs
      have hs' : s ∈ Set.Ioo t0 (t0 + (t - t0)) := hs
      exact ⟨by linarith [hs'.1, ht0.1], by linarith [hs'.2]⟩
    have hsub' := hsub.mono hcar hreg
    exact curvature_norm_sq_doubling (I := I) S hc0 hQ0 hT0 hTspan hsub' hQ t
      ⟨h1, by linarith⟩ x
  obtain ⟨t, x, ht, hgt⟩ := hunb (max B (4 * Q0 ^ 2))
  have ht' : t ∈ Set.Ico alpha omega := ht
  rcases le_total t t0 with hcase | hcase
  · have := hearly t x ht'.1 hcase
    have hmax : B ≤ max B (4 * Q0 ^ 2) := le_max_left _ _
    linarith
  · have := hlate t x hcase ht'.2
    have hmax : 4 * Q0 ^ 2 ≤ max B (4 * Q0 ^ 2) := le_max_right _ _
    linarith

end Geometry

section OrderZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem rm04NormSqInFrame_cubic_heat_inequality
    {D : RealTimeInterval}
    (Rm04 : Real -> Tensor04Section (I := I) (M := M))
    (gInv : Real -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rmNormLap nablaRmNormSq : Real -> M -> Real)
    (hheat : Rm04NormHeatEquationOn (D := D)
      (rm04NormSqInFrame (I := I) Rm04 gInv frame) rmNormLap nablaRmNormSq
      (rmReactionInFrame (I := I) Rm04 gInv frame))
    (horth : ∀ (t : Real) (x : M), InverseMetricOrthonormalAt (M := M) gInv t x)
    (hnabla : ∀ (t : Real) (x : M), 0 ≤ nablaRmNormSq t x)
    (t : RealTimeInterval.RegularTime D) (x : M) :
    ∃ d : Real,
      HasDerivWithinAt
        (fun s : Real => rm04NormSqInFrame (I := I) Rm04 gInv frame s x) d
        D.carrier (t : Real) ∧
      d ≤ rmNormLap (t : Real) x +
        16 * (Fintype.card Idx : Real) ^ 6 *
          rm04NormSqInFrame (I := I) Rm04 gInv frame (t : Real) x ^ (3 / 2 : Real) := by
  refine ⟨_, hheat t x, ?_⟩
  have habs := abs_rmReactionInFrame_le (I := I) Rm04 gInv frame (t : Real) x
    (horth (t : Real) x)
  have hre := le_of_abs_le habs
  have hn := hnabla (t : Real) x
  linarith

omit [SigmaCompactSpace M] [T2Space M] in
theorem rm04NormSqInFrame_cubic_heat_inequality_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Tensor04Section (I := I) (M := M))
    (gInv : Real -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (rmNormLap roughLapInner nablaRmNormSq : Real -> M -> Real)
    (h_raw : Rm04NormRawDerivativeEquationOn (I := I) S Rm04 gInv frame rm04Dt)
    (h_simplify : Rm04NormDerivativeSimplifiesInFrame (I := I) S Rm04 gInv frame
      rm04Dt roughLapInner (rmReactionInFrame (I := I) Rm04 gInv frame))
    (h_lap : Rm04NormLaplacianComponentsOn rmNormLap roughLapInner nablaRmNormSq)
    (horth : ∀ (t : Real) (x : M), InverseMetricOrthonormalAt (M := M) gInv t x)
    (hnabla : ∀ (t : Real) (x : M), 0 ≤ nablaRmNormSq t x)
    (t : RealTimeInterval.RegularTime D) (x : M) :
    ∃ d : Real,
      HasDerivWithinAt
        (fun s : Real => rm04NormSqInFrame (I := I) Rm04 gInv frame s x) d
        D.carrier (t : Real) ∧
      d ≤ rmNormLap (t : Real) x +
        16 * (Fintype.card Idx : Real) ^ 6 *
          rm04NormSqInFrame (I := I) Rm04 gInv frame (t : Real) x ^ (3 / 2 : Real) :=
  rm04NormSqInFrame_cubic_heat_inequality (I := I) Rm04 gInv frame rmNormLap
    nablaRmNormSq
    (rm04NormHeatEquationOn_of_solution (I := I) S Rm04 gInv frame rm04Dt
      rmNormLap roughLapInner nablaRmNormSq h_raw h_simplify h_lap)
    horth hnabla t x

end OrderZero

end DifferentialGeometry.PDE.RicciFlow
