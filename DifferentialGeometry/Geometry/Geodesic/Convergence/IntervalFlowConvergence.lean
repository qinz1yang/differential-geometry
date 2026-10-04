import DifferentialGeometry.Geometry.Geodesic.Convergence.ChartFlowConfinement
import Mathlib.Topology.Order.IntermediateValue

/-!
# Native geodesic-flow convergence on a whole closed interval

Chart confinement propagates the original native initial convergence along the limit curve.
A supremum argument reaches the endpoint without choosing another metric or tangent bundle.
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

private theorem nativeFlow_converges_on_chart_interval
    (g : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : ∀ C : Set M, IsCompact C → MetricCPConvergenceOn C 1 g gInf gRef)
    (q : TangentBundle I M) (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M)
    {a b : ℝ} (hab : a ≤ b)
    (hdom : ∀ i, ∀ t ∈ Icc a b, (p i, t) ∈ (g i).geodesicFlowDomain)
    (hdomInf : ∀ t ∈ Icc a b, (pInf, t) ∈ gInf.geodesicFlowDomain)
    (hchartInf : ∀ t ∈ Icc a b,
      (gInf.geodesicFlow pInf t).proj ∈ (chartAt H q.proj).source)
    (hinit : Tendsto (fun i => (g i).geodesicFlow (p i) a)
      atTop (𝓝 (gInf.geodesicFlow pInf a))) :
    ∀ t ∈ Icc a b, Tendsto (fun i => (g i).geodesicFlow (p i) t)
      atTop (𝓝 (gInf.geodesicFlow pInf t)) := by
  obtain ⟨hstay, huniform⟩ := geodesicFlow_chart_confinement_of_metricCP g gInf gRef hconv
    q p pInf hab hdom hdomInf hchartInf hinit
  let e :=
    (DifferentialGeometry.PartialDiffeomorph.extChartAt I.tangent ∞ q).toOpenPartialHomeomorph
  have heSource (x : TangentBundle I M) : x ∈ e.source ↔
      x.proj ∈ (chartAt H q.proj).source := by
    change x ∈ (extChartAt I.tangent q).source ↔ _
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
  intro t ht
  have hlimsource := (heSource _).mpr (hchartInf t ht)
  have hchart := huniform.tendsto_at ht
  have hnative := (e.symm.continuousAt (e.map_source hlimsource)).tendsto.comp hchart
  rw [e.left_inv hlimsource] at hnative
  apply hnative.congr'
  filter_upwards [hstay] with i hi
  exact e.left_inv ((heSource _).mpr (hi t ht))

theorem geodesicFlow_tendsto_on_Icc_of_metricCP
    (g : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : ∀ C : Set M, IsCompact C → MetricCPConvergenceOn C 1 g gInf gRef)
    (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M)
    {a b : ℝ} (hab : a ≤ b)
    (hdom : ∀ i, ∀ t ∈ Icc a b, (p i, t) ∈ (g i).geodesicFlowDomain)
    (hdomInf : ∀ t ∈ Icc a b, (pInf, t) ∈ gInf.geodesicFlowDomain)
    (hinit : Tendsto (fun i => (g i).geodesicFlow (p i) a)
      atTop (𝓝 (gInf.geodesicFlow pInf a))) :
    ∀ t ∈ Icc a b, Tendsto (fun i => (g i).geodesicFlow (p i) t)
      atTop (𝓝 (gInf.geodesicFlow pInf t)) := by
  let good (t : ℝ) := Tendsto (fun i => (g i).geodesicFlow (p i) t)
    atTop (𝓝 (gInf.geodesicFlow pInf t))
  let A : Set ℝ := {t ∈ Icc a b | ∀ s ∈ Icc a t, good s}
  have hcontinuous : ContinuousOn (gInf.geodesicFlow pInf) (Icc a b) := by
    intro t ht
    exact (gInf.isMIntegralCurveOn_geodesicFlow (r := ⊤) le_top pInf t
      (hdomInf t ht)).1.mono (fun s hs => hdomInf s hs)
  have hlocal (t : ℝ) (ht : t ∈ Icc a b) : ∃ delta > 0,
      ∀ s ∈ ball t delta ∩ Icc a b,
        (gInf.geodesicFlow pInf s).proj ∈
          (chartAt H (gInf.geodesicFlow pInf t).proj).source := by
    let q := gInf.geodesicFlow pInf t
    have hnh : (gInf.geodesicFlow pInf) ⁻¹' (extChartAt I.tangent q).source ∈
        𝓝[Icc a b] t := (hcontinuous t ht).preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source (I := I.tangent) q).mem_nhds
        (mem_extChartAt_source (I := I.tangent) q))
    obtain ⟨delta, hdelta, hsubset⟩ := Metric.mem_nhdsWithin_iff.mp hnh
    refine ⟨delta, hdelta, fun s hs => ?_⟩
    have hh := hsubset hs
    change gInf.geodesicFlow pInf s ∈ (extChartAt I.tangent q).source at hh
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff] at hh
    exact hh
  have hpropagate (q : TangentBundle I M) {u v : ℝ} (hu : a ≤ u) (hv : v ≤ b)
      (huv : u ≤ v) (hchart : ∀ s ∈ Icc u v,
        (gInf.geodesicFlow pInf s).proj ∈ (chartAt H q.proj).source)
      (hgood : good u) : ∀ s ∈ Icc u v, good s :=
    nativeFlow_converges_on_chart_interval g gInf gRef hconv q p pInf huv
      (fun i s hs => hdom i s (Icc_subset_Icc hu hv hs))
      (fun s hs => hdomInf s (Icc_subset_Icc hu hv hs)) hchart hgood
  have ha : a ∈ A := ⟨left_mem_Icc.mpr hab, fun s hs => by
    have heq : s = a := le_antisymm hs.2 hs.1
    simpa only [heq, good] using hinit⟩
  have hne : A.Nonempty := ⟨a, ha⟩
  have hbounded : BddAbove A := ⟨b, fun t ht => ht.1.2⟩
  let T := sSup A
  have hT : T ∈ Icc a b := ⟨le_csSup hbounded ha,
    csSup_le hne (fun t ht => ht.1.2)⟩
  have hbefore : ∀ s ∈ Ico a T, good s := by
    intro s hs
    obtain ⟨u, hu, hsu⟩ := (lt_csSup_iff hbounded hne).mp hs.2
    exact hu.2 s ⟨hs.1, hsu.le⟩
  have hgoodT : good T := by
    rcases hT.1.eq_or_lt with hTa | hTa
    · simpa only [← hTa, good] using hinit
    obtain ⟨delta, hdelta, hchart⟩ := hlocal T hT
    have hmax : max a (T - delta / 2) < T :=
      max_lt hTa (by linarith)
    obtain ⟨u, hu, hmaxu⟩ := (lt_csSup_iff hbounded hne).mp hmax
    have huT : u ≤ T := le_csSup hbounded hu
    apply hpropagate (gInf.geodesicFlow pInf T) hu.1.1 hT.2 huT
      (fun s hs => hchart s ⟨?_, Icc_subset_Icc hu.1.1 hT.2 hs⟩) (hu.2 u ⟨hu.1.1, le_rfl⟩)
      T ⟨huT, le_rfl⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    have huLower := (le_max_right a (T - delta / 2)).trans_lt hmaxu
    constructor <;> linarith [hs.1, hs.2]
  have hTA : T ∈ A := ⟨hT, fun s hs => by
    rcases hs.2.lt_or_eq with hlt | heq
    · exact hbefore s ⟨hs.1, hlt⟩
    · exact heq ▸ hgoodT⟩
  have hTb : T = b := by
    apply le_antisymm hT.2
    by_contra hnot
    have hlt : T < b := lt_of_not_ge hnot
    obtain ⟨delta, hdelta, hchart⟩ := hlocal T hT
    let c := min b (T + delta / 2)
    have hTc : T < c := lt_min hlt (by linarith)
    have hcb : c ≤ b := min_le_left _ _
    have hlocals : ∀ s ∈ Icc T c, good s :=
      hpropagate (gInf.geodesicFlow pInf T) hT.1 hcb hTc.le
        (fun s hs => hchart s ⟨?_, Icc_subset_Icc hT.1 hcb hs⟩) hgoodT
    · have hcA : c ∈ A := ⟨⟨hT.1.trans hTc.le, hcb⟩, fun s hs => by
        rcases le_or_gt s T with hle | hgt
        · exact hTA.2 s ⟨hs.1, hle⟩
        · exact hlocals s ⟨hgt.le, hs.2⟩⟩
      exact (not_le_of_gt hTc) (le_csSup hbounded hcA)
    · rw [mem_ball, Real.dist_eq, abs_lt]
      have hcUpper : c ≤ T + delta / 2 := min_le_right _ _
      constructor <;> linarith [hs.1, hs.2]
  simpa only [hTb] using hTA.2

theorem realZero_geodesicFlow_converges_on_Icc {T : ℝ} (hT : 0 ≤ T) :
    let g := euclideanMetric (E := ℝ)
    let p : TangentBundle 𝓘(ℝ, ℝ) ℝ := ⟨0, 0⟩
    ∀ t ∈ Icc 0 T, Tendsto (fun _i : ℕ => g.geodesicFlow p t)
      atTop (𝓝 (g.geodesicFlow p t)) := by
  let g := euclideanMetric (E := ℝ)
  let p : TangentBundle 𝓘(ℝ, ℝ) ℝ := ⟨0, 0⟩
  have hdom (t : ℝ) : (p, t) ∈ g.geodesicFlowDomain :=
    g.mem_geodesicFlowDomain_zeroSection 0 t
  exact geodesicFlow_tendsto_on_Icc_of_metricCP (fun _i : ℕ => g) g g
    (fun C _hC epsilon hepsilon => ⟨0, fun _i _hi => by
      rw [metricDerivNormSupOn_self]; exact hepsilon⟩) (fun _i : ℕ => p) p hT
    (fun _i t _ht => hdom t) (fun t _ht => hdom t) tendsto_const_nhds

end DifferentialGeometry.Geometry.Riemannian.Geodesic
