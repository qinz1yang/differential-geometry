import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Evolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.LeastArea
import DifferentialGeometry.Geometry.Metric.Family.Comparison

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] {D : RealTimeInterval} {a b : ℝ}

theorem RicciBackground.inner_le_exp_mul_inner
    (B : RicciBackground (I := I) (M := M) D a b)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (p : M) (v : TangentSpace I p) :
    (B.family.metric s).inner p v v ≤
      Real.exp (2 * B.B₀ * |s - t|) * (B.family.metric t).inner p v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply DifferentialGeometry.inner_le_exp_mul_inner_of_abs_deriv_le B.family.metric p v ?_ hs ht
  intro r hr
  refine ⟨-2 * B.family.ricciAt r p (vec2 v v), ?_, ?_⟩
  · have h := metric_derivWithin_eq_neg_two_ricci
      (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩) B.equation
      ⟨r, B.regular hr⟩ p v v
    exact h.mono (fun u hu => D.regular_subset (B.regular hu))
  · have habs := abs_apply_le_norm0S (B.family.metric r) p 2
      (B.family.ricciAt r p) (vec2 v v)
    have hprod : (∏ i : Fin 2, Real.sqrt ((B.family.metric r).inner p
        ((vec2 v v) i) ((vec2 v v) i))) = (B.family.metric r).inner p v v := by
      rw [Fin.prod_univ_two]
      simp only [vec2, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      exact Real.mul_self_sqrt (DifferentialGeometry.metric_inner_self_nonneg
        (B.family.metric r) p v)
    rw [hprod] at habs
    have hnorm : Real.sqrt (normSq0S (B.family.metric r) p 2 (B.family.ricciAt r p)) ≤ B.B₀ :=
      Real.sqrt_le_iff.mpr ⟨B.B₀_nonneg, B.ricci_bound r hr p⟩
    have hb := habs.trans (mul_le_mul_of_nonneg_right hnorm
      (DifferentialGeometry.metric_inner_self_nonneg (B.family.metric r) p v))
    rw [abs_mul, abs_neg, abs_two]
    nlinarith

end

section

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]

theorem RicciBackground.leastArea_le_exp_mul_leastArea
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (γ : ContinuousFreeLoop M) (hctr : IsContractibleLoop γ)
    (hlip_s : Width.IsLipschitzLoop (B.family.metric s) γ)
    (hlip_t : Width.IsLipschitzLoop (B.family.metric t) γ) :
    Width.leastArea (B.family.metric t) γ hctr hlip_t ≤
      Real.exp (2 * B.B₀ * |t - s|) *
        Width.leastArea (B.family.metric s) γ hctr hlip_s := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let d : ℝ := |t - s|
  let A : ℝ := Real.exp (2 * B.B₀ * d)
  have hA : 0 < A := by
    exact Real.exp_pos _
  have hAeq : (Real.exp (-B.B₀ * d)) ^ 2 = A⁻¹ := by
    dsimp only [A]
    rw [pow_two, ← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  have hBeq : (Real.exp (B.B₀ * d)) ^ 2 = A := by
    dsimp only [A]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hmetric : ∀ q (v : TangentSpace I q),
      (Real.exp (-B.B₀ * d)) ^ 2 * (B.family.metric s).inner q v v ≤
        (B.family.metric t).inner q v v ∧
      (B.family.metric t).inner q v v ≤
        (Real.exp (B.B₀ * d)) ^ 2 * (B.family.metric s).inner q v v := by
    intro q v
    have hst' := B.inner_le_exp_mul_inner hs ht q v
    have hts' := B.inner_le_exp_mul_inner ht hs q v
    have hfirst : (B.family.metric s).inner q v v ≤
        A * (B.family.metric t).inner q v v := by
      simpa only [A, d, abs_sub_comm s t] using hst'
    have hsecond : (B.family.metric t).inner q v v ≤
        A * (B.family.metric s).inner q v v := by
      exact hts'
    have hleft : A⁻¹ * (B.family.metric s).inner q v v ≤
        (B.family.metric t).inner q v v := by
      exact (inv_mul_le_iff₀ hA).mpr hfirst
    rw [hAeq, hBeq]
    exact ⟨hleft, hsecond⟩
  have hexp : Real.exp (-B.B₀ * d) ≤ Real.exp (B.B₀ * d) := by
    apply Real.exp_le_exp.mpr
    have hd : 0 ≤ B.B₀ * d := mul_nonneg B.B₀_nonneg (abs_nonneg _)
    nlinarith
  have hcomp := Width.leastArea_metric_comparison
    (B.family.metric s) (B.family.metric t) (Real.exp_pos _)
    hexp hmetric γ hctr hlip_s hlip_t
  simpa only [hBeq, A, d] using hcomp.2

theorem RicciBackground.leastArea_le_exp_mul_leastArea_of_le
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (γ : ContinuousFreeLoop M) (hctr : IsContractibleLoop γ)
    (hlip_s : Width.IsLipschitzLoop (B.family.metric s) γ)
    (hlip_t : Width.IsLipschitzLoop (B.family.metric t) γ) :
    Width.leastArea (B.family.metric t) γ hctr hlip_t ≤
      Real.exp (2 * B.B₀ * (t - s)) *
        Width.leastArea (B.family.metric s) γ hctr hlip_s := by
  simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using
    B.leastArea_le_exp_mul_leastArea hs ht γ hctr hlip_s hlip_t

end

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
