import DifferentialGeometry.Geometry.Measure.EuclideanChart
import DifferentialGeometry.Geometry.Metric.ChartLipschitz.DistanceComparison
import DifferentialGeometry.Analysis.Calculus.Derivative.AlmostEverywhereLipschitz
import DifferentialGeometry.Topology.LocalLipschitzVariation

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set MeasureTheory Filter DifferentialGeometry
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Measure
open scoped Manifold Topology ContDiff ENNReal NNReal
namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space M] [SigmaCompactSpace M] [RegularSpace M] [RegularSpace N]
  [I.Boundaryless] [J.Boundaryless]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → N)
  (hf : ∀ p, ∃ L : ℝ≥0, ∃ t ∈ 𝓝 p, ∀ x ∈ t, ∀ y ∈ t,
    riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y)
  (hdf : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
    MDifferentiableAt I J f x → ∀ v : TangentSpace I x,
      Real.sqrt (h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x v)) ≤
        Real.sqrt (g.inner x v v))

include hf hdf

theorem exists_open_riemannianEDistOf_le_of_ae_mfderiv
    (p : M) {K : ℝ≥0} (hK : 1 < K) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, ∀ y ∈ U,
      riemannianEDistOf h (f x) (f y) ≤ (K ^ 4 : ℝ≥0) * riemannianEDistOf g x y := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x =>
    continuousAt_of_local_riemannianEDistOf_le g h f x (hf x)
  obtain ⟨s, hso, hps, hs⟩ := exists_open_ae_norm_fderiv_euclideanChartExpression_le
    g h f hc hdf p (K := (K : ℝ)) (by exact_mod_cast hK)
  obtain ⟨r, _hr, _L, hUo, hpU, hreserve, hLip, hback⟩ :=
    exists_ball_lipschitzOnWith_euclideanChartExpression g h f p hK (hf p) s (hso.mem_nhds hps)
  let A := metricChartEuclideanEquiv g p
  let φ := extChartAt I p
  let B := Metric.ball (A (φ p)) r
  have hD : ∀ᵐ z ∂(euclideanChartHaar g p).restrict B,
      ‖fderiv ℝ (euclideanChartExpression g h f p (f p)) z‖ ≤ (K ^ 2 : ℝ≥0) := by
    simpa only [NNReal.coe_pow] using hs B measurableSet_ball
      (fun z hz => ⟨(hreserve z hz).1, (hreserve z hz).2.1⟩)
  have hsharp : LipschitzOnWith (K ^ 2) (euclideanChartExpression g h f p (f p)) B :=
    DifferentialGeometry.Analysis.lipschitzOnWith_of_ae_norm_fderiv_le Metric.isOpen_ball
      (convex_ball _ _) hLip hD
  refine ⟨φ.source ∩ (fun x => A (φ x)) ⁻¹' B, hUo, hpU, ?_⟩
  simpa only [← pow_add, show 2 + 2 = (4 : ℕ) from rfl] using hback (K ^ 2) hsharp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eVariationOn_comp_le_of_ae_mfderiv
    (γ : ℝ → M) (a b : ℝ) (hγ : ContinuousOn γ (Icc a b)) :
    (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
       ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
     letI : PseudoEMetricSpace M := .ofRiemannianMetric I M
     letI : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
       ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
     letI : PseudoEMetricSpace N := .ofRiemannianMetric J N
     eVariationOn (f ∘ γ) (Icc a b) ≤ eVariationOn γ (Icc a b)) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  let : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace N := .ofRiemannianMetric J N
  have hK (K : ℝ≥0) (hK : 1 < K) :
      eVariationOn (f ∘ γ) (Icc a b) ≤ (K ^ 4 : ℝ≥0) * eVariationOn γ (Icc a b) := by
    apply DifferentialGeometry.Topology.eVariationOn_comp_le_of_locally_lipschitzOn hγ
    intro x _hx
    obtain ⟨U, hUo, hxU, hbound⟩ :=
      exists_open_riemannianEDistOf_le_of_ae_mfderiv g h f hf hdf x hK
    exact ⟨U, hUo.mem_nhds hxU, fun y hy z hz => hbound y hy z hz⟩
  have ht : Tendsto (fun K : ℝ≥0 => ((K ^ 4 : ℝ≥0) : ℝ≥0∞))
      (𝓝[>] (1 : ℝ≥0)) (𝓝 (1 : ℝ≥0∞)) := by
    have hc : Continuous (fun K : ℝ≥0 => ((K ^ 4 : ℝ≥0) : ℝ≥0∞)) :=
      ENNReal.continuous_coe.comp (continuous_id.pow 4)
    simpa only [one_pow, ENNReal.coe_one] using
      (hc.continuousAt (x := (1 : ℝ≥0))).tendsto.mono_left nhdsWithin_le_nhds
  have hlim := ENNReal.Tendsto.mul_const ht (b := eVariationOn γ (Icc a b)) (Or.inl one_ne_zero)
  rw [one_mul] at hlim
  have hev : ∀ᶠ K : ℝ≥0 in 𝓝[>] (1 : ℝ≥0),
      eVariationOn (f ∘ γ) (Icc a b) ≤ (K ^ 4 : ℝ≥0) * eVariationOn γ (Icc a b) :=
    eventually_nhdsWithin_of_forall fun K hgt => hK K hgt
  exact ge_of_tendsto hlim hev

omit hf in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eVariationOn_comp_le_of_locallyLipschitz_ae_mfderiv
    (γ : ℝ → M) (a b : ℝ) (hγ : ContinuousOn γ (Icc a b)) :
    (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
       ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
     letI : PseudoEMetricSpace M := .ofRiemannianMetric I M
     letI : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
       ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
     letI : PseudoEMetricSpace N := .ofRiemannianMetric J N
     LocallyLipschitz f →
       eVariationOn (f ∘ γ) (Icc a b) ≤ eVariationOn γ (Icc a b)) := by
  intro hloc
  exact eVariationOn_comp_le_of_ae_mfderiv g h f
    ((locallyLipschitz_iff_local_riemannianEDistOf_le g h f).mp hloc) hdf γ a b hγ

omit hf in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem boundedVariationOn_comp_of_locallyLipschitz_ae_mfderiv
    (γ : ℝ → M) (a b : ℝ) (hγ : ContinuousOn γ (Icc a b)) :
    (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
       ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
     letI : PseudoEMetricSpace M := .ofRiemannianMetric I M
     letI : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
       ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
     letI : PseudoEMetricSpace N := .ofRiemannianMetric J N
     LocallyLipschitz f → BoundedVariationOn γ (Icc a b) →
       BoundedVariationOn (f ∘ γ) (Icc a b)) := by
  intro hloc hvar
  exact ne_top_of_le_ne_top hvar
    (eVariationOn_comp_le_of_locallyLipschitz_ae_mfderiv g h f hdf γ a b hγ hloc)

end DifferentialGeometry.Geometry.Metric
