import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteMetricFlow
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteOrder

/-!
# G5-M at moving times (an LFR18 / LC50 ingredient for finite-order metrics)

`finite_geodesicFlow_tendsto_at_moving_time`: under the hypotheses of G5-M on `[a, b]`, for an
interior time `t ∈ (a, b)` and times `time i → t`, the states `(h i).geodesicFlow (p i) (time i)`
converge to `g.geodesicFlow p∞ t` (one tangent chart around the limit state, uniform chart
convergence on a small time interval). This is the finite-order analogue of Codex's smooth
`geodesicFlow_tendsto_at_moving_time_of_metricCP`; in LFR18 the times are the source lengths
`ℓ_i → ℓ` of the minimizing segments.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **G5-M at moving times.** `C^{r+1}` metrics (`1 ≤ r`) `h i → g` in `C¹` in every extended
chart, orbits defined on `[a, b]`, states converging at time `a`, `t ∈ (a, b)` and `time i → t`:
`(h i).geodesicFlow (p i) (time i) → g.geodesicFlow p∞ t`. -/
theorem finite_geodesicFlow_tendsto_at_moving_time {r : ℕ∞} (hr : 1 ≤ r)
    (h : ℕ → ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hconv : ∀ (x : M) (C : Set E), IsCompact C → C ⊆ (extChartAt I x).target →
      MapCPConvergenceOn C 1 (fun i => chartCoeff (h i) x) (chartCoeff g x))
    (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M) {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hdom : ∀ i, ∀ s ∈ Icc a b, (p i, s) ∈ (h i).geodesicFlowDomain)
    (hdomInf : ∀ s ∈ Icc a b, (pInf, s) ∈ g.geodesicFlowDomain)
    (hinit : Tendsto (fun i => (h i).geodesicFlow (p i) a) atTop (𝓝 (g.geodesicFlow pInf a)))
    (time : ℕ → ℝ) (htime : Tendsto time atTop (𝓝 t)) :
    Tendsto (fun i => (h i).geodesicFlow (p i) (time i)) atTop (𝓝 (g.geodesicFlow pInf t)) := by
  have hab : a ≤ b := ht.1.le.trans ht.2.le
  have hpointwise := finite_geodesicFlow_tendsto_on_Icc hr h g hconv p pInf hab hdom hdomInf hinit
  let q := g.geodesicFlow pInf t
  let e :=
    (DifferentialGeometry.PartialDiffeomorph.extChartAt I.tangent ∞ q).toOpenPartialHomeomorph
  have heSource (x : TangentBundle I M) : x ∈ e.source ↔
      x.proj ∈ (chartAt H q.proj).source := by
    change x ∈ (extChartAt I.tangent q).source ↔ _
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
  have hcont : ContinuousWithinAt (g.geodesicFlow pInf) (Icc a b) t :=
    (g.isMIntegralCurveOn_geodesicFlow hr pInf t (hdomInf t (Ioo_subset_Icc_self ht))).1.mono
      (fun s hs => hdomInf s hs)
  have hnh : (g.geodesicFlow pInf) ⁻¹' e.source ∈ 𝓝[Icc a b] t :=
    hcont.preimage_mem_nhdsWithin (e.open_source.mem_nhds
      (mem_extChartAt_source (I := I.tangent) q))
  obtain ⟨δ, hδ, hchart⟩ := Metric.mem_nhdsWithin_iff.mp hnh
  let u := max a (t - δ / 2)
  let v := min b (t + δ / 2)
  have hut : u < t := max_lt ht.1 (by linarith)
  have htv : t < v := lt_min ht.2 (by linarith)
  have hau : a ≤ u := le_max_left _ _
  have hvb : v ≤ b := min_le_left _ _
  have huv : u ≤ v := hut.le.trans htv.le
  have hchartInf : ∀ s ∈ Icc u v,
      (g.geodesicFlow pInf s).proj ∈ (chartAt H q.proj).source := by
    intro s hs
    apply (heSource _).mp
    apply hchart
    refine ⟨?_, Icc_subset_Icc hau hvb hs⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    have hulo : t - δ / 2 ≤ u := le_max_right _ _
    have hvhi : v ≤ t + δ / 2 := min_le_right _ _
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨hstay, huniform⟩ := finite_geodesicFlow_chart_confinement hr h g hconv q p pInf huv
    (fun i s hs => hdom i s (Icc_subset_Icc hau hvb hs))
    (fun s hs => hdomInf s (Icc_subset_Icc hau hvb hs)) hchartInf
    (hpointwise u ⟨hau, huv.trans hvb⟩)
  have htimes : ∀ᶠ i in atTop, time i ∈ Icc u v :=
    (htime.eventually (isOpen_Ioo.mem_nhds ⟨hut, htv⟩)).mono
      (fun i hi => Ioo_subset_Icc_self hi)
  have hwithin : Tendsto time atTop (𝓝[Icc u v] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨htime, htimes⟩
  have hsource := (heSource _).mpr (hchartInf t ⟨hut.le, htv.le⟩)
  have hcoordCont : ContinuousWithinAt (fun s => e (g.geodesicFlow pInf s)) (Icc u v) t :=
    (e.continuousAt hsource).comp_continuousWithinAt (hcont.mono (Icc_subset_Icc hau hvb))
  have hcoordinate := huniform.tendsto_comp hcoordCont hwithin
  have hnative := (e.symm.continuousAt (e.map_source hsource)).tendsto.comp hcoordinate
  rw [e.left_inv hsource] at hnative
  apply hnative.congr'
  filter_upwards [hstay, htimes] with i hi hs
  exact e.left_inv ((heSource _).mpr (hi (time i) hs))

/-- **Consumer.** For one `C^{r+1}` metric (`1 ≤ r`), the geodesic flow is jointly sequentially
continuous in the initial vector and an interior time of a common domain interval. -/
theorem finite_geodesicFlow_tendsto_joint {r : ℕ∞} (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : ℕ → TangentBundle I M} {pInf : TangentBundle I M} (hp : Tendsto p atTop (𝓝 pInf))
    {b t : ℝ} (ht : t ∈ Ioo 0 b)
    (hdom : ∀ i, ∀ s ∈ Icc 0 b, (p i, s) ∈ g.geodesicFlowDomain)
    (hdomInf : ∀ s ∈ Icc 0 b, (pInf, s) ∈ g.geodesicFlowDomain)
    (time : ℕ → ℝ) (htime : Tendsto time atTop (𝓝 t)) :
    Tendsto (fun i => g.geodesicFlow (p i) (time i)) atTop (𝓝 (g.geodesicFlow pInf t)) := by
  refine finite_geodesicFlow_tendsto_at_moving_time hr (fun _ => g) g
    (fun _ _ _ _ => MapCPConvergenceOn.const_seq _) p pInf ht hdom hdomInf ?_ time htime
  simp only [ContMDiffRiemannianMetric.geodesicFlow_zero _ hr]
  exact hp

end DifferentialGeometry.Geometry.Riemannian.Geodesic
