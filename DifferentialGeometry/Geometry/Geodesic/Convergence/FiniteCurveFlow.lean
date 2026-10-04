import DifferentialGeometry.Geometry.Geodesic.Convergence.FinitePullbackSpray

/-!
# LC50′, propagation step: curves solving converging chart equations converge to a geodesic

Curve version of CM-L4's G5-M (`finite_geodesicFlow_chart_confinement`,
`finite_geodesicFlow_tendsto_on_Icc`, FiniteMetricFlow.lean), for the finite-order twin of X84's
LC50 chain. The approximants are arbitrary continuous curves `Γ i : ℝ → TN`, not flows of metrics
on `N`: in the tangent chart at every `q` they solve, while over the base chart, an equation with
a field `v q.proj i`, and these fields converge locally uniformly on the chart targets to the
metric spray of a `C^{r+1}` metric `G` (`1 ≤ r`). If the states converge at time `a` to a
`G`-geodesic state, they converge at every time of `[a, b]`.

* `finite_curve_chart_confinement`: one chart along the limit orbit (X84's metric-free first-exit
  kernels `eventually_mapsTo_chart_of_coordinate_ODE`, `tendstoUniformlyOn_chart_of_coordinate_ODE`).
* `finite_curve_tendsto_on_Icc`: the whole interval (supremum argument over charts).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.MetricKoszul
open DifferentialGeometry.Geometry.MetricSmoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

private local instance curveFlowDual : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

/-- **One chart along the limit orbit, for curves.** Curves `Γ i` continuous on `[a, b]` solving in
the tangent chart at `q`, while over its base chart, equations with fields `v q.proj i` that
converge locally uniformly on the chart target to the spray of a `C^{r+1}` metric `G` (`1 ≤ r`);
the `G`-orbit of `pInf` defined on `[a, b]` and over the base chart; convergence at time `a`.
Then eventually the curves stay over the chart, and they converge uniformly in the chart. -/
theorem finite_curve_chart_confinement {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (v : N → ℕ → E × E → E × E)
    (hvconv : ∀ (x : N) (C : Set (E × E)), IsCompact C →
      C ⊆ (extChartAt I x).target ×ˢ univ →
      TendstoUniformlyOn (v x) (metricSpray (chartCoeff G x)) atTop C)
    (q : TangentBundle I N) (Γ : ℕ → ℝ → TangentBundle I N) (pInf : TangentBundle I N)
    {a b : ℝ} (hab : a ≤ b) (hcont : ∀ i, ContinuousOn (Γ i) (Icc a b))
    (hderiv : ∀ i, ∀ t ∈ Icc a b, (Γ i t).proj ∈ (chartAt H q.proj).source →
      HasDerivWithinAt (fun s => extChartAt I.tangent q (Γ i s))
        (v q.proj i (extChartAt I.tangent q (Γ i t))) (Icc a b) t)
    (hdomInf : ∀ t ∈ Icc a b, (pInf, t) ∈ G.geodesicFlowDomain)
    (hchartInf : ∀ t ∈ Icc a b, (G.geodesicFlow pInf t).proj ∈ (chartAt H q.proj).source)
    (hinit : Tendsto (fun i => Γ i a) atTop (𝓝 (G.geodesicFlow pInf a))) :
    (∀ᶠ i in atTop, ∀ t ∈ Icc a b, (Γ i t).proj ∈ (chartAt H q.proj).source) ∧
    TendstoUniformlyOn (fun i t => extChartAt I.tangent q (Γ i t))
      (fun t => extChartAt I.tangent q (G.geodesicFlow pInf t)) atTop (Icc a b) := by
  let e :=
    (DifferentialGeometry.PartialDiffeomorph.extChartAt I.tangent ∞ q).toOpenPartialHomeomorph
  have heTarget : e.target ⊆ (extChartAt I q.proj).target ×ˢ univ := by
    change (extChartAt I.tangent q).target ⊆ _
    rw [FiberBundle.extChartAt_target]
    exact fun x hx => ⟨hx.1.1, hx.2⟩
  have heSource (x : TangentBundle I N) : x ∈ e.source ↔
      x.proj ∈ (chartAt H q.proj).source := by
    change x ∈ (extChartAt I.tangent q).source ↔ _
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
  let gammaInf := G.geodesicFlow pInf
  have hsourceInf : MapsTo gammaInf (Icc a b) e.source :=
    fun t ht => (heSource _).mpr (hchartInf t ht)
  have hlimitODE : ∀ t ∈ Icc a b, HasDerivWithinAt (e ∘ gammaInf)
      (metricSpray (chartCoeff G q.proj) (e (gammaInf t))) (Icc a b) t := fun t ht =>
    (G.hasDerivAt_geodesicFlow_chart hr (hdomInf t ht) q (hchartInf t ht)).hasDerivWithinAt
  have hfield : ContDiffOn ℝ 1 (metricSpray (chartCoeff G q.proj)) e.target :=
    (contDiffOn_metricSpray_chartCoeff hr G q.proj).mono heTarget
  have hfieldConv : ∀ C : Set (E × E), IsCompact C → C ⊆ e.target →
      TendstoUniformlyOn (v q.proj) (metricSpray (chartCoeff G q.proj)) atTop C :=
    fun C hC hCe => hvconv q.proj C hC (hCe.trans heTarget)
  have hstageODE : ∀ i, ∀ t ∈ Icc a b, Γ i t ∈ e.source →
      HasDerivWithinAt (e ∘ Γ i) (v q.proj i (e (Γ i t))) (Icc a b) t :=
    fun i t ht hs => hderiv i t ht ((heSource _).mp hs)
  have hstay := eventually_mapsTo_chart_of_coordinate_ODE e hab Γ gammaInf (v q.proj)
    (metricSpray (chartCoeff G q.proj)) hcont hsourceInf hstageODE hlimitODE hfield hfieldConv
    hinit
  refine ⟨?_, tendstoUniformlyOn_chart_of_coordinate_ODE e hab Γ gammaInf (v q.proj)
    (metricSpray (chartCoeff G q.proj)) hcont hsourceInf hstageODE hlimitODE hfield hfieldConv
    hinit⟩
  filter_upwards [hstay] with i hi t ht
  exact (heSource _).mp (hi ht)

private theorem continuousOn_geodesicFlow_Icc {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (pInf : TangentBundle I N) {a b : ℝ}
    (hdomInf : ∀ t ∈ Icc a b, (pInf, t) ∈ G.geodesicFlowDomain) :
    ContinuousOn (G.geodesicFlow pInf) (Icc a b) := fun t ht =>
  (G.isMIntegralCurveOn_geodesicFlow hr pInf t (hdomInf t ht)).1.mono
    (fun s hs => hdomInf s hs)

private theorem finite_curve_converges_on_chart_interval {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (v : N → ℕ → E × E → E × E)
    (hvconv : ∀ (x : N) (C : Set (E × E)), IsCompact C →
      C ⊆ (extChartAt I x).target ×ˢ univ →
      TendstoUniformlyOn (v x) (metricSpray (chartCoeff G x)) atTop C)
    (q : TangentBundle I N) (Γ : ℕ → ℝ → TangentBundle I N) (pInf : TangentBundle I N)
    {a b : ℝ} (hab : a ≤ b) (hcont : ∀ i, ContinuousOn (Γ i) (Icc a b))
    (hderiv : ∀ i, ∀ t ∈ Icc a b, (Γ i t).proj ∈ (chartAt H q.proj).source →
      HasDerivWithinAt (fun s => extChartAt I.tangent q (Γ i s))
        (v q.proj i (extChartAt I.tangent q (Γ i t))) (Icc a b) t)
    (hdomInf : ∀ t ∈ Icc a b, (pInf, t) ∈ G.geodesicFlowDomain)
    (hchartInf : ∀ t ∈ Icc a b, (G.geodesicFlow pInf t).proj ∈ (chartAt H q.proj).source)
    (hinit : Tendsto (fun i => Γ i a) atTop (𝓝 (G.geodesicFlow pInf a))) :
    ∀ t ∈ Icc a b, Tendsto (fun i => Γ i t) atTop (𝓝 (G.geodesicFlow pInf t)) := by
  obtain ⟨hstay, huniform⟩ := finite_curve_chart_confinement hr G v hvconv q Γ pInf hab hcont
    hderiv hdomInf hchartInf hinit
  let e :=
    (DifferentialGeometry.PartialDiffeomorph.extChartAt I.tangent ∞ q).toOpenPartialHomeomorph
  have heSource (x : TangentBundle I N) : x ∈ e.source ↔
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

/-- **Whole interval, for curves.** Curves `Γ i` continuous on `[a, b]` solving, in the tangent
chart at EVERY `q` and while over its base chart, equations with fields `v q.proj i` converging
locally uniformly to the spray of a `C^{r+1}` metric `G` (`1 ≤ r`); the `G`-orbit of `pInf`
defined on `[a, b]`; convergence of the states at time `a`. Then `Γ i t → G.geodesicFlow pInf t`
for every `t ∈ [a, b]`. -/
theorem finite_curve_tendsto_on_Icc {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (v : N → ℕ → E × E → E × E)
    (hvconv : ∀ (x : N) (C : Set (E × E)), IsCompact C →
      C ⊆ (extChartAt I x).target ×ˢ univ →
      TendstoUniformlyOn (v x) (metricSpray (chartCoeff G x)) atTop C)
    (Γ : ℕ → ℝ → TangentBundle I N) (pInf : TangentBundle I N)
    {a b : ℝ} (hab : a ≤ b) (hcont : ∀ i, ContinuousOn (Γ i) (Icc a b))
    (hderiv : ∀ (q : TangentBundle I N) (i : ℕ), ∀ t ∈ Icc a b,
      (Γ i t).proj ∈ (chartAt H q.proj).source →
      HasDerivWithinAt (fun s => extChartAt I.tangent q (Γ i s))
        (v q.proj i (extChartAt I.tangent q (Γ i t))) (Icc a b) t)
    (hdomInf : ∀ t ∈ Icc a b, (pInf, t) ∈ G.geodesicFlowDomain)
    (hinit : Tendsto (fun i => Γ i a) atTop (𝓝 (G.geodesicFlow pInf a))) :
    ∀ t ∈ Icc a b, Tendsto (fun i => Γ i t) atTop (𝓝 (G.geodesicFlow pInf t)) := by
  let good (t : ℝ) := Tendsto (fun i => Γ i t) atTop (𝓝 (G.geodesicFlow pInf t))
  let A : Set ℝ := {t ∈ Icc a b | ∀ s ∈ Icc a t, good s}
  have hcontinuous := continuousOn_geodesicFlow_Icc hr G pInf hdomInf
  have hlocal (t : ℝ) (ht : t ∈ Icc a b) : ∃ δ > 0, ∀ s ∈ ball t δ ∩ Icc a b,
      (G.geodesicFlow pInf s).proj ∈ (chartAt H (G.geodesicFlow pInf t).proj).source := by
    let q := G.geodesicFlow pInf t
    have hnh : (G.geodesicFlow pInf) ⁻¹' (extChartAt I.tangent q).source ∈ 𝓝[Icc a b] t :=
      (hcontinuous t ht).preimage_mem_nhdsWithin
        ((isOpen_extChartAt_source (I := I.tangent) q).mem_nhds
          (mem_extChartAt_source (I := I.tangent) q))
    obtain ⟨δ, hδ, hsubset⟩ := Metric.mem_nhdsWithin_iff.mp hnh
    refine ⟨δ, hδ, fun s hs => ?_⟩
    have hh := hsubset hs
    change G.geodesicFlow pInf s ∈ (extChartAt I.tangent q).source at hh
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff] at hh
    exact hh
  have hpropagate (q : TangentBundle I N) {u w : ℝ} (hu : a ≤ u) (hw : w ≤ b) (huw : u ≤ w)
      (hchart : ∀ s ∈ Icc u w, (G.geodesicFlow pInf s).proj ∈ (chartAt H q.proj).source)
      (hgood : good u) : ∀ s ∈ Icc u w, good s :=
    finite_curve_converges_on_chart_interval hr G v hvconv q Γ pInf huw
      (fun i => (hcont i).mono (Icc_subset_Icc hu hw))
      (fun i s hs hsc => (hderiv q i s (Icc_subset_Icc hu hw hs) hsc).mono
        (Icc_subset_Icc hu hw))
      (fun s hs => hdomInf s (Icc_subset_Icc hu hw hs)) hchart hgood
  have ha : a ∈ A := ⟨left_mem_Icc.mpr hab, fun s hs => by
    have heq : s = a := le_antisymm hs.2 hs.1
    simpa only [heq, good] using hinit⟩
  have hne : A.Nonempty := ⟨a, ha⟩
  have hbounded : BddAbove A := ⟨b, fun t ht => ht.1.2⟩
  let T := sSup A
  have hT : T ∈ Icc a b := ⟨le_csSup hbounded ha, csSup_le hne (fun t ht => ht.1.2)⟩
  have hbefore : ∀ s ∈ Ico a T, good s := by
    intro s hs
    obtain ⟨u, hu, hsu⟩ := (lt_csSup_iff hbounded hne).mp hs.2
    exact hu.2 s ⟨hs.1, hsu.le⟩
  have hgoodT : good T := by
    rcases hT.1.eq_or_lt with hTa | hTa
    · simpa only [← hTa, good] using hinit
    obtain ⟨δ, hδ, hchart⟩ := hlocal T hT
    have hmax : max a (T - δ / 2) < T := max_lt hTa (by linarith)
    obtain ⟨u, hu, hmaxu⟩ := (lt_csSup_iff hbounded hne).mp hmax
    have huT : u ≤ T := le_csSup hbounded hu
    apply hpropagate (G.geodesicFlow pInf T) hu.1.1 hT.2 huT
      (fun s hs => hchart s ⟨?_, Icc_subset_Icc hu.1.1 hT.2 hs⟩) (hu.2 u ⟨hu.1.1, le_rfl⟩)
      T ⟨huT, le_rfl⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    have huLower := (le_max_right a (T - δ / 2)).trans_lt hmaxu
    constructor <;> linarith [hs.1, hs.2]
  have hTA : T ∈ A := ⟨hT, fun s hs => by
    rcases hs.2.lt_or_eq with hlt | heq
    · exact hbefore s ⟨hs.1, hlt⟩
    · exact heq ▸ hgoodT⟩
  have hTb : T = b := by
    apply le_antisymm hT.2
    by_contra hnot
    have hlt : T < b := lt_of_not_ge hnot
    obtain ⟨δ, hδ, hchart⟩ := hlocal T hT
    let c := min b (T + δ / 2)
    have hTc : T < c := lt_min hlt (by linarith)
    have hcb : c ≤ b := min_le_left _ _
    have hlocals : ∀ s ∈ Icc T c, good s :=
      hpropagate (G.geodesicFlow pInf T) hT.1 hcb hTc.le
        (fun s hs => hchart s ⟨?_, Icc_subset_Icc hT.1 hcb hs⟩) hgoodT
    · have hcA : c ∈ A := ⟨⟨hT.1.trans hTc.le, hcb⟩, fun s hs => by
        rcases le_or_gt s T with hle | hgt
        · exact hTA.2 s ⟨hs.1, hle⟩
        · exact hlocals s ⟨hgt.le, hs.2⟩⟩
      exact (not_le_of_gt hTc) (le_csSup hbounded hcA)
    · rw [mem_ball, Real.dist_eq, abs_lt]
      have hcUpper : c ≤ T + δ / 2 := min_le_right _ _
      constructor <;> linarith [hs.1, hs.2]
  simpa only [hTb] using hTA.2

end DifferentialGeometry.Geometry.Riemannian.Geodesic
