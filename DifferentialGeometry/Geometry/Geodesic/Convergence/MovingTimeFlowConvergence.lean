import DifferentialGeometry.Geometry.Geodesic.Convergence.IntervalFlowConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Original geodesic-flow convergence at moving times

The native closed-interval propagation and one actual chart near the limit time control the
original moving states. The conclusion retains the native tangent bundle and original metrics.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem geodesicFlow_tendsto_at_moving_time_of_metricCP
    (g : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : ∀ C : Set M, IsCompact C → MetricCPConvergenceOn C 1 g gInf gRef)
    (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M)
    {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hdom : ∀ i, ∀ s ∈ Icc a b, (p i, s) ∈ (g i).geodesicFlowDomain)
    (hdomInf : ∀ s ∈ Icc a b, (pInf, s) ∈ gInf.geodesicFlowDomain)
    (hinit : Tendsto (fun i => (g i).geodesicFlow (p i) a)
      atTop (𝓝 (gInf.geodesicFlow pInf a)))
    (time : ℕ → ℝ) (htime : Tendsto time atTop (𝓝 t)) :
    Tendsto (fun i => (g i).geodesicFlow (p i) (time i))
      atTop (𝓝 (gInf.geodesicFlow pInf t)) := by
  have hab : a ≤ b := ht.1.le.trans ht.2.le
  have hpointwise := geodesicFlow_tendsto_on_Icc_of_metricCP g gInf gRef hconv p pInf
    hab hdom hdomInf hinit
  let q := gInf.geodesicFlow pInf t
  let e :=
    (DifferentialGeometry.PartialDiffeomorph.extChartAt I.tangent ∞ q).toOpenPartialHomeomorph
  have heSource (x : TangentBundle I M) : x ∈ e.source ↔
      x.proj ∈ (chartAt H q.proj).source := by
    change x ∈ (extChartAt I.tangent q).source ↔ _
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
  have hcont : ContinuousWithinAt (gInf.geodesicFlow pInf) (Icc a b) t :=
    (gInf.isMIntegralCurveOn_geodesicFlow (r := ⊤) le_top pInf t
      (hdomInf t (Ioo_subset_Icc_self ht))).1.mono (fun s hs => hdomInf s hs)
  have hnh : (gInf.geodesicFlow pInf) ⁻¹' e.source ∈ 𝓝[Icc a b] t :=
    hcont.preimage_mem_nhdsWithin (e.open_source.mem_nhds
      (mem_extChartAt_source (I := I.tangent) q))
  obtain ⟨delta, hdelta, hchart⟩ := Metric.mem_nhdsWithin_iff.mp hnh
  let u := max a (t - delta / 2)
  let v := min b (t + delta / 2)
  have hut : u < t := max_lt ht.1 (by linarith)
  have htv : t < v := lt_min ht.2 (by linarith)
  have hau : a ≤ u := le_max_left _ _
  have hvb : v ≤ b := min_le_left _ _
  have huv : u ≤ v := hut.le.trans htv.le
  have hchartInf : ∀ s ∈ Icc u v,
      (gInf.geodesicFlow pInf s).proj ∈ (chartAt H q.proj).source := by
    intro s hs
    apply (heSource _).mp
    apply hchart
    refine ⟨?_, Icc_subset_Icc hau hvb hs⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    have hulo : t - delta / 2 ≤ u := le_max_right _ _
    have hvhi : v ≤ t + delta / 2 := min_le_right _ _
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨hstay, huniform⟩ := geodesicFlow_chart_confinement_of_metricCP g gInf gRef hconv
    q p pInf huv (fun i s hs => hdom i s (Icc_subset_Icc hau hvb hs))
      (fun s hs => hdomInf s (Icc_subset_Icc hau hvb hs)) hchartInf
      (hpointwise u ⟨hau, huv.trans hvb⟩)
  have htimes : ∀ᶠ i in atTop, time i ∈ Icc u v :=
    (htime.eventually (isOpen_Ioo.mem_nhds ⟨hut, htv⟩)).mono
      (fun i hi => Ioo_subset_Icc_self hi)
  have hwithin : Tendsto time atTop (𝓝[Icc u v] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨htime, htimes⟩
  have hsource := (heSource _).mpr (hchartInf t ⟨hut.le, htv.le⟩)
  have hcoordCont : ContinuousWithinAt (fun s => e (gInf.geodesicFlow pInf s))
      (Icc u v) t := (e.continuousAt hsource).comp_continuousWithinAt
        (hcont.mono (Icc_subset_Icc hau hvb))
  have hcoordinate := huniform.tendsto_comp hcoordCont hwithin
  have hnative := (e.symm.continuousAt (e.map_source hsource)).tendsto.comp hcoordinate
  rw [e.left_inv hsource] at hnative
  apply hnative.congr'
  filter_upwards [hstay, htimes] with i hi hs
  exact e.left_inv ((heSource _).mpr (hi (time i) hs))

theorem realZero_geodesicFlow_converges_at_moving_time :
    let g := euclideanMetric (E := ℝ)
    let p : TangentBundle 𝓘(ℝ, ℝ) ℝ := ⟨0, 0⟩
    Tendsto (fun i : ℕ => g.geodesicFlow p (1 + 1 / (i + 1 : ℝ)))
      atTop (𝓝 (g.geodesicFlow p 1)) := by
  let g := euclideanMetric (E := ℝ)
  let p : TangentBundle 𝓘(ℝ, ℝ) ℝ := ⟨0, 0⟩
  have hdom (t : ℝ) : (p, t) ∈ g.geodesicFlowDomain :=
    g.mem_geodesicFlowDomain_zeroSection 0 t
  apply geodesicFlow_tendsto_at_moving_time_of_metricCP (fun _i : ℕ => g) g g
    (fun C _hC epsilon hepsilon => ⟨0, fun _i _hi => by
      rw [metricDerivNormSupOn_self]; exact hepsilon⟩) (fun _i : ℕ => p) p
    (a := 0) (b := 2) (t := 1) (by constructor <;> norm_num)
    (fun _i s _hs => hdom s) (fun s _hs => hdom s) tendsto_const_nhds
    (fun i : ℕ => 1 + 1 / (i + 1 : ℝ))
  simpa using (tendsto_const_nhds.add
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

end DifferentialGeometry.Geometry.Riemannian.Geodesic
