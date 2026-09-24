import Mathlib.Topology.Order.Compact
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.TensorError
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Parameter
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ChartConvergence

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature
namespace DifferentialGeometry.CheegerGromovCompactness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

open Filter Set DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Measure
open scoped _root_.Topology
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [I.Boundaryless]

private theorem metricDerivNorm_tendsto_of_joint_chart_smooth
    (g h R : P → SmoothRiemannianMetric I M) (x : M)
    {A : Set P} {V : Set E} (hV : IsOpen V) (hVt : V ⊆ (extChartAt I x).target)
    (hg : ∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun q : P × E => chartGramOnE (g q.1) x i j q.2) (A ×ˢ V))
    (hh : ∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun q : P × E => chartGramOnE (h q.1) x i j q.2) (A ×ˢ V))
    (hR : ∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun q : P × E => chartGramOnE (R q.1) x i j q.2) (A ×ˢ V))
    (τ : ℕ → P) (hτ : ∀ n, τ n ∈ A) {p : P} (hp : p ∈ A)
    (hτp : Tendsto τ atTop (𝓝 p))
    {K : Set E} (hK : IsCompact K) (hKV : K ⊆ V)
    (z : ℕ → E) (hzK : ∀ n, z n ∈ K) {z₀ : E} (hz₀ : z₀ ∈ K)
    (hz : Tendsto z atTop (𝓝 z₀)) (r : ℕ) :
    Tendsto (fun n => metricDerivNorm (I := I) r (g (τ n)) (h (τ n)) (R (τ n))
      ((extChartAt I x).symm (z n))) atTop
      (𝓝 (metricDerivNorm (I := I) r (g p) (h p) (R p) ((extChartAt I x).symm z₀))) := by
  let T (q : P) := metricTensorField (I := I) (g q) - metricTensorField (I := I) (h q)
  have hT (slots : Fin 2 → Fin (Module.finrank ℝ E)) : MapCInfConvergenceOnCompacts V
      (fun n y => T (τ n) ((extChartAt I x).symm y)
        (fun j => chartBasisVecFiber (I := I) x (slots j) ((extChartAt I x).symm y)))
      (fun y => T p ((extChartAt I x).symm y)
        (fun j => chartBasisVecFiber (I := I) x (slots j) ((extChartAt I x).symm y))) := by
    have hc := mapCInfConvergenceOnCompacts_of_tendsto_parameter
      (G := fun q y => chartGramOnE (g q) x (slots 0) (slots 1) y -
        chartGramOnE (h q) x (slots 0) (slots 1) y)
      hV ((hg (slots 0) (slots 1)).sub (hh (slots 0) (slots 1))) τ hτ hp hτp
    simpa only [T, ContMDiffSection.coe_sub, Pi.sub_apply,
      Tensor0SSpace.sub_apply, metricTensorField_apply, chartGramOnE,
      chartGramMatrix_apply] using hc
  have hn := tensor02_covariant_norm_tendsto_of_smooth_chart_convergence
      (fun n => R (τ n)) (R p) (fun n => T (τ n)) (T p) x hV hVt
      (fun i j => mapCInfConvergenceOnCompacts_of_tendsto_parameter
        (G := fun q y => chartGramOnE (R q) x i j y) hV (hR i j) τ hτ hp hτp)
      hT hK hKV z hzK hz₀ hz r
  simpa only [T, tensor02CovDerivNormWith_metricTensorField_sub_eq_metricDerivNorm] using hn

private theorem metricDerivNorm_continuousOn_of_joint_chart_smooth
    (g h R : P → SmoothRiemannianMetric I M) (x : M)
    {A : Set P} {V : Set E} (hV : IsOpen V) (hVt : V ⊆ (extChartAt I x).target)
    (hg : ∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun q : P × E => chartGramOnE (g q.1) x i j q.2) (A ×ˢ V))
    (hh : ∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun q : P × E => chartGramOnE (h q.1) x i j q.2) (A ×ˢ V))
    (hR : ∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun q : P × E => chartGramOnE (R q.1) x i j q.2) (A ×ˢ V)) (r : ℕ) :
    ContinuousOn (fun q : P × E => metricDerivNorm (I := I) r
      (g q.1) (h q.1) (R q.1) ((extChartAt I x).symm q.2)) (A ×ˢ V) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply continuous_iff_seqContinuous.mpr
  intro q q₀ hq
  have hval := continuous_subtype_val.tendsto q₀ |>.comp hq
  have hp := continuous_fst.tendsto q₀.val |>.comp hval
  have hz := continuous_snd.tendsto q₀.val |>.comp hval
  exact metricDerivNorm_tendsto_of_joint_chart_smooth g h R x hV hVt hg hh hR
    (fun n => (q n).val.1) (fun n => (q n).property.1) q₀.property.1 hp
    hz.isCompact_insert_range
    (by
      rintro y (rfl | ⟨n, rfl⟩)
      · exact q₀.property.2
      · exact (q n).property.2)
    (fun n => (q n).val.2) (fun n => mem_insert_of_mem _ (mem_range_self n))
    (mem_insert _ _) hz r

theorem metricDerivNorm_joint_continuousOn
    (g h R : P → SmoothRiemannianMetric I M) {A : Set P} {U : Set M}
    (hlocal : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ extChartAt I x x ∈ V ∧
      V ⊆ (extChartAt I x).target ∧ ∀ i j : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞ (fun q : P × E => chartGramOnE (g q.1) x i j q.2) (A ×ˢ V) ∧
        ContDiffOn ℝ ∞ (fun q : P × E => chartGramOnE (h q.1) x i j q.2) (A ×ˢ V) ∧
        ContDiffOn ℝ ∞ (fun q : P × E => chartGramOnE (R q.1) x i j q.2) (A ×ˢ V)) (r : ℕ) :
    ContinuousOn (fun q : P × M => metricDerivNorm (I := I) r (g q.1) (h q.1) (R q.1) q.2)
      (A ×ˢ U) := by
  intro q hq
  obtain ⟨V, hV, hxV, hVt, hc⟩ := hlocal q.2 hq.2
  have hchart := metricDerivNorm_continuousOn_of_joint_chart_smooth g h R q.2 hV hVt
    (fun i j => (hc i j).1) (fun i j => (hc i j).2.1) (fun i j => (hc i j).2.2) r
  have harg : ContinuousAt (fun w : P × M => (w.1, extChartAt I q.2 w.2)) q :=
    continuousAt_fst.prodMk ((continuousAt_extChartAt q.2).comp continuousAt_snd)
  have hmem : (fun w : P × M => (w.1, extChartAt I q.2 w.2)) ⁻¹' (A ×ˢ V) ∈
      𝓝[A ×ˢ U] q := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (harg.snd.preimage_mem_nhds (hV.mem_nhds hxV))] with w hw hwy
    exact ⟨hw.1, hwy⟩
  have hn := (hchart (q.1, extChartAt I q.2 q.2) ⟨hq.1, hxV⟩).comp_of_preimage_mem_nhdsWithin
    (f := fun w : P × M => (w.1, extChartAt I q.2 w.2)) harg.continuousWithinAt hmem
  apply hn.congr_of_eventuallyEq_of_mem _ hq
  have hs : ∀ᶠ w : P × M in 𝓝[A ×ˢ U] q, w.2 ∈ (extChartAt I q.2).source :=
    nhdsWithin_le_nhds (continuousAt_snd.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) q.2).mem_nhds (mem_extChartAt_source q.2)))
  filter_upwards [hs] with w hw
  simp only [Function.comp_apply, (extChartAt I q.2).left_inv hw]

theorem metricDerivNorm_tendstoUniformlyOn
    (g h R : P → SmoothRiemannianMetric I M) {A : Set P} {U : Set M}
    (hlocal : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ extChartAt I x x ∈ V ∧
      V ⊆ (extChartAt I x).target ∧ ∀ i j : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞ (fun q : P × E => chartGramOnE (g q.1) x i j q.2) (A ×ˢ V) ∧
        ContDiffOn ℝ ∞ (fun q : P × E => chartGramOnE (h q.1) x i j q.2) (A ×ˢ V) ∧
        ContDiffOn ℝ ∞ (fun q : P × E => chartGramOnE (R q.1) x i j q.2) (A ×ˢ V))
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) {p : P} (hp : p ∈ A) (r : ℕ) :
    TendstoUniformlyOn (fun q x => metricDerivNorm (I := I) r (g q) (h q) (R q) x)
      (fun x => metricDerivNorm (I := I) r (g p) (h p) (R p) x) (𝓝[A] p) K := by
  have hc := metricDerivNorm_joint_continuousOn g h R hlocal r
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨W, hW, hsmall⟩ := hK.mem_uniformity_of_prod
    (f := fun q x => metricDerivNorm (I := I) r (g q) (h q) (R q) x)
    (hc.mono (prod_mono_right hKU)) hp (Metric.dist_mem_uniformity hε)
  filter_upwards [hW] with q hq
  intro x hx
  simpa only [Set.mem_ofPred_eq, dist_comm] using hsmall q hq x hx

theorem metricDerivNormSupOn_continuousOn
    (g h R : P → SmoothRiemannianMetric I M) {A : Set P} {U : Set M}
    (hlocal : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ extChartAt I x x ∈ V ∧
      V ⊆ (extChartAt I x).target ∧ ∀ i j : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞ (fun q : P × E => chartGramOnE (g q.1) x i j q.2) (A ×ˢ V) ∧
        ContDiffOn ℝ ∞ (fun q : P × E => chartGramOnE (h q.1) x i j q.2) (A ×ˢ V) ∧
        ContDiffOn ℝ ∞ (fun q : P × E => chartGramOnE (R q.1) x i j q.2) (A ×ˢ V))
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) (r : ℕ) :
    ContinuousOn (fun q => metricDerivNormSupOn (I := I) K r (g q) (h q) (R q)) A := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc (a : Fin (r + 1)) : Continuous (fun q : A × K =>
      metricDerivNorm (I := I) a.val (g q.1.val) (h q.1.val) (R q.1.val) q.2.val) := by
    have hnorm := metricDerivNorm_joint_continuousOn g h R hlocal a.val
    have harg : Continuous (fun q : A × K => ((q.1 : P), (q.2 : M))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact hnorm.comp_continuous (f := fun q : A × K => ((q.1 : P), (q.2 : M))) harg
      (fun q => ⟨q.1.property, hKU q.2.property⟩)
  have hc₀ : Continuous (fun q : Fin (r + 1) × (A × K) =>
      metricDerivNorm (I := I) q.1.val (g q.2.1.val) (h q.2.1.val) (R q.2.1.val) q.2.2.val) :=
    continuous_prod_of_discrete_left.mpr hc
  let f (q : A) (w : Fin (r + 1) × K) :=
    metricDerivNorm (I := I) w.1.val (g q.val) (h q.val) (R q.val) w.2.val
  have hperm : Continuous (fun q : A × (Fin (r + 1) × K) => (q.2.1, (q.1, q.2.2))) :=
    continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)
  have hf : Continuous (Function.uncurry f) := by
    have hh := hc₀.comp hperm
    exact hh
  have hsup := (isCompact_univ : IsCompact (univ : Set (Fin (r + 1) × K))).continuous_sSup (f := f) hf
  have heq (q : A) : metricDerivNormSupOn (I := I) K r (g q.val) (h q.val) (R q.val) =
      sSup (f q '' univ) := by
    apply congrArg sSup
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, heq⟩
      exact ⟨(⟨a, by omega⟩, ⟨x, hx⟩), mem_univ _, heq⟩
    · rintro ⟨⟨a, x⟩, _, heq⟩
      exact ⟨a.val, by omega, x.val, x.property, heq⟩
  exact continuousOn_iff_continuous_domRestrict.mpr (hsup.congr fun q => (heq q).symm)

end DifferentialGeometry.CheegerGromovCompactness
