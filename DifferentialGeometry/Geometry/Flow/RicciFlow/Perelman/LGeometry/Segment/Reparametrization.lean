import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length
import DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M] {D : RealTimeInterval}

theorem isFiniteActionLCurve_squareRootReparametrization
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ)
    (Ω : Set (M × ℝ)) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (alpha : ℝ → M) (halpha : ContMDiffOn 𝓘(ℝ, ℝ) I 1 alpha (Icc a b))
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b)
    (hΩ : ∀ s ∈ Icc a b, (alpha s, T - s ^ 2) ∈ Ω) :
    isFiniteActionLCurve S T Ω (a ^ 2) (b ^ 2) (squareRootReparametrization alpha) := by
  have hb : 0 ≤ b := ha.trans hab
  have habSq : a ^ 2 ≤ b ^ 2 := (sq_le_sq₀ ha hb).2 hab
  refine ⟨?_, ?_, (intervalIntegrable_lDensity_squareRootReparametrization_sq_iff
    S T alpha a b ha hb).mpr hLag, ?_⟩
  · let g := S.base.metric T
    let cg : ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨cg.toRiemannianMetric⟩
    let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace
    let _ : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
    obtain ⟨K, hLip⟩ :=
      (halpha.locallyLipschitzOn (convex_Icc a b)).exists_lipschitzOnWith_of_compact isCompact_Icc
    have hMaps : MapsTo Real.sqrt (uIcc (a ^ 2) (b ^ 2)) (Icc a b) := by
      intro tau htau
      rw [uIcc_of_le habSq] at htau
      refine ⟨Real.le_sqrt_of_sq_le htau.1, ?_⟩
      simpa only [Real.sqrt_sq hb] using Real.sqrt_le_sqrt htau.2
    change AbsolutelyContinuousOnInterval (alpha ∘ Real.sqrt) (a ^ 2) (b ^ 2)
    exact hLip.comp_absolutelyContinuousOnInterval
      (Real.absolutelyContinuousOnInterval_sqrt (a ^ 2) (b ^ 2)) hMaps
  · rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [Ioo_ae_eq_Icc (μ := volume)] with tau htau
    intro htauIcc
    have htauIoo : tau ∈ Ioo (a ^ 2) (b ^ 2) := htau.mpr htauIcc
    have htauPos : 0 < tau := (sq_nonneg a).trans_lt htauIoo.1
    have hsqrt : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.sqrt tau :=
      mdifferentiableAt_iff_differentiableAt.mpr
        (Real.hasDerivAt_sqrt htauPos.ne').differentiableAt
    have hsIoo : Real.sqrt tau ∈ Ioo a b :=
      ⟨(Real.lt_sqrt ha).2 htauIoo.1, (Real.sqrt_lt htauPos.le hb).2 htauIoo.2⟩
    have halphaAt : MDifferentiableAt 𝓘(ℝ, ℝ) I alpha (Real.sqrt tau) :=
      ((halpha (Real.sqrt tau) ⟨hsIoo.1.le, hsIoo.2.le⟩).contMDiffAt
        (Icc_mem_nhds hsIoo.1 hsIoo.2)).mdifferentiableAt (by norm_num)
    change MDifferentiableAt 𝓘(ℝ, ℝ) I (alpha ∘ Real.sqrt) tau
    exact halphaAt.comp tau hsqrt
  · intro tau htau
    have htauNonneg : 0 ≤ tau := (sq_nonneg a).trans htau.1
    have hroot : Real.sqrt tau ∈ Icc a b := by
      refine ⟨Real.le_sqrt_of_sq_le htau.1, ?_⟩
      simpa only [Real.sqrt_sq hb] using Real.sqrt_le_sqrt htau.2
    simpa only [squareRootReparametrization, Real.sq_sqrt htauNonneg] using
      hΩ (Real.sqrt tau) hroot

theorem isFiniteActionLCurve_squareRootReparametrization_of_contMDiff
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ)
    (Ω : Set (M × ℝ)) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b)
    (hΩ : ∀ s ∈ Icc a b, (alpha s, T - s ^ 2) ∈ Ω) :
    isFiniteActionLCurve S T Ω (a ^ 2) (b ^ 2) (squareRootReparametrization alpha) :=
  isFiniteActionLCurve_squareRootReparametrization S T Ω a b ha hab alpha
    halpha.contMDiffOn hLag hΩ

end DifferentialGeometry.PDE.RicciFlow.Perelman
