import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricConvergence
import DifferentialGeometry.Analysis.Integration.Measure.PullbackPartial
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.CompactExtension
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Filter MeasureTheory TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open Integral.Measure

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private local instance (P : PointedRiemannianManifold.{u, uE, uH} I) :
    MeasurableSpace P.M := borel P.M
private local instance (P : PointedRiemannianManifold.{u, uE, uH} I) :
    BorelSpace P.M := ⟨rfl⟩

theorem PointedRiemannianConvergenceMaps.tendsto_setLIntegral_image
    {X : PointedRiemannianSeq.{u, uE, uH} I} {P : PointedRiemannianManifold.{u, uE, uH} I}
    {phi : ℕ → ℕ} (Phi : PointedRiemannianConvergenceMaps X P phi)
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    {K : Set P.M} (hK : IsCompact K)
    (fs : ∀ i, (X.obj i).M → ℝ≥0∞) (hmeas : ∀ i, Measurable (fs i))
    {f : P.M → ℝ≥0∞} {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hbound : ∀ᶠ i in atTop, ∀ x ∈ K, fs (phi i) (Phi.map i x) ≤ B)
    (hlim : ∀ x ∈ K, Tendsto (fun i => fs (phi i) (Phi.map i x)) atTop (𝓝 (f x))) :
    Tendsto (fun i => ∫⁻ y in Phi.map i '' K, fs (phi i) y
      ∂riemannianVolumeMeasure (I := I) (M := (X.obj (phi i)).M) (X.obj (phi i)).metric)
      atTop (𝓝 (∫⁻ x in K, f x ∂riemannianVolumeMeasure (I := I) (M := P.M) P.metric)) := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 P.M := IsManifold.of_le (n := ∞) (by decide)
  let _ : LocallyCompactSpace P.M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hK
  obtain ⟨N, hN⟩ := Phi.source_subset hK'
  have hsrc (i : ℕ) : K' ⊆ (Phi.partialDiffeomorph (i + N)).source := hN (i + N) (by omega)
  choose gs hgs using fun i => exists_smooth_riemannian_metric_eq_pullback_on_compact
    (Phi.partialDiffeomorph (i + N)) hK' (hsrc i) (X.obj (phi (i + N))).metric P.metric
  let U : Opens P.M := ⟨interior K', isOpen_interior⟩
  have hU (i : ℕ) : (U : Set P.M) ⊆ (Phi.partialDiffeomorph (i + N)).source :=
    interior_subset.trans (hsrc i)
  have hmetric : TendstoUniformlyOn (fun i x => metricDerivNorm (I := I) 0 (gs i) P.metric P.metric x)
      (fun _ => 0) atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := C.converges K hK 0 ε hε
    filter_upwards [eventually_ge_atTop k] with i hi
    have hb := (hk (i + N) (by omega)).2
    rw [hcanonical (i + N), canonicalSourceData_derivNormSupOn_eq_of_pullback
      Phi (i + N) (gs i) K U 0 U.isOpen hKK' (hU i)
      (fun x hx v w => hgs i x (interior_subset hx) v w)] at hb
    intro x hx
    have hn : 0 ≤ metricDerivNorm (I := I) 0 (gs i) P.metric P.metric x := Real.sqrt_nonneg _
    have hp := derivNorm_le_sup (I := I) hK (a := 0) (p := 0) le_rfl
      (gs i) P.metric P.metric (x := x) hx
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hn] using hp.trans_lt hb
  let μ := riemannianVolumeMeasure (I := I) (M := P.M) P.metric
  let _ : IsFiniteMeasureOnCompacts μ := riemannianVolumeMeasure_isFiniteMeasureOnCompacts P.metric
  have hfs : ∀ᶠ i in atTop, AEMeasurable
      (fun x => fs (phi (i + N)) (Phi.map (i + N) x)) (μ.restrict K) := by
    apply Eventually.of_forall
    intro i
    apply (hmeas _).comp_aemeasurable
    exact ((Phi.partialDiffeomorph (i + N)).contMDiffOn_toFun.continuousOn.mono
      (hKK'.trans (hU i))).aemeasurable hK.measurableSet
  have hb : ∀ᶠ i in atTop, ∀ᵐ x ∂μ.restrict K,
      fs (phi (i + N)) (Phi.map (i + N) x) ≤ B := by
    filter_upwards [(tendsto_add_atTop_nat N).eventually hbound] with i hi
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hi x hx
  have hfin : ∫⁻ _ in K, B ∂μ ≠ ⊤ := by
    rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top hB hK.measure_lt_top.ne
  have hl : ∀ᵐ x ∂μ.restrict K,
      Tendsto (fun i => fs (phi (i + N)) (Phi.map (i + N) x)) atTop (𝓝 (f x)) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact (hlim x hx).comp (tendsto_add_atTop_nat N)
  have hd := tendsto_setLIntegral_of_dominated_convergence_of_metricDerivNorm gs P.metric
    hK.measurableSet hmetric (fun _ => B) hfs hb hfin hl
  rw [← tendsto_add_atTop_iff_nat N]
  apply hd.congr'
  apply Eventually.of_forall
  intro i
  dsimp only
  exact (setLIntegral_image_partialDiffeomorph (Phi.partialDiffeomorph (i + N))
    (gs i) (X.obj (phi (i + N))).metric U (hU i)
    (fun x hx v w => hgs i x (interior_subset hx) v w)
    hK.measurableSet hKK' (fs (phi (i + N)))).symm

end DifferentialGeometry.CheegerGromovCompactness
