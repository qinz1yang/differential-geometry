import DifferentialGeometry.Geometry.Geodesic.Flow.FiniteMetric
import DifferentialGeometry.Geometry.Geodesic.Convergence.ChartFirstExit
import DifferentialGeometry.Geometry.Geodesic.Equation.MetricSprayFiniteRegularity
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Smoothing
import DifferentialGeometry.Analysis.ODE.GeodesicLimits.MetricChristoffel
import DifferentialGeometry.Analysis.ODE.GeodesicLimits.ChristoffelLimit
import DifferentialGeometry.Analysis.FiniteDimensional.BilinearPositivity
import Mathlib.Topology.Order.IntermediateValue

/-!
# G5-M: continuity of the finite-metric geodesic flow in the metric and the initial data

CM-P's geodesic flow `ContMDiffRiemannianMetric.geodesicFlow` of a `C^{r+1}` metric, `1 ≤ r`
(so the chart Christoffel field of the limit is `C¹`), depends continuously on the metric in the
chart `C¹` topology and on the initial data, uniformly on compact time intervals inside the
flow domains.

The metrics converge in `C¹` in every extended chart, stated inline through the chart
coefficients `chartCoeff (h i) x → chartCoeff g x` (`MapCPConvergenceOn C 1` on compact subsets
`C` of the chart target). This is the finite-order analogue of Codex's smooth-metric
`geodesicFlow_tendsto_on_Icc_of_metricCP` (`IntervalFlowConvergence.lean`), and uses the same
generic first-exit kernel `eventually_mapsTo_chart_of_coordinate_ODE`.

* `tendstoUniformlyOn_metricSpray_of_mapCPConvergenceOn`: `C¹` convergence of chart coefficient
  fields (coercive limit) gives uniform convergence of the metric sprays on compact phase sets.
* `finite_geodesicFlow_chart_confinement`: one chart along the limit orbit — eventual chart
  confinement of the approximating orbits and uniform convergence in the tangent chart.
* `finite_geodesicFlow_tendsto_on_Icc`: the whole interval (supremum argument over charts).
* `tendsto_geodesicFlow_of_chart_C1_tendsto`: **G5-M** — `p i → p∞` and the metrics converge:
  `(h i).geodesicFlow (p i) t → g.geodesicFlow p∞ t` for `t ∈ [0, T]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis.ODE.GeodesicLimits
open DifferentialGeometry.MetricKoszul
open DifferentialGeometry.Geometry.MetricSmoothing

section Spray

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ContinuousDualEquiv E]

/-- `C¹` convergence of chart coefficient fields on the compact subsets of an open `U` (coercive
limit) gives uniform convergence of the metric sprays on compact subsets of `U × E`. -/
theorem tendstoUniformlyOn_metricSpray_of_mapCPConvergenceOn
    {U : Set E} (hU : IsOpen U)
    (b : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ) (bInf : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ i, ContDiffOn ℝ 1 (b i) U) (hbInf : ContDiffOn ℝ 1 bInf U)
    (hco : ∀ x ∈ U, IsCoercive (bInf x))
    (hconv : ∀ C : Set E, IsCompact C → C ⊆ U → MapCPConvergenceOn C 1 b bInf)
    {C : Set (E × E)} (hC : IsCompact C) (hCU : C ⊆ U ×ˢ univ) :
    TendstoUniformlyOn (fun i => metricSpray (b i)) (metricSpray bInf) atTop C := by
  let Gamma (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) := raisedKoszulOp (B x) (fderiv ℝ B x)
  have hfstC : IsCompact (Prod.fst '' C) := hC.image continuous_fst
  have hfstU : Prod.fst '' C ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    exact (hCU hy).1
  have hGamma := tendstoUniformlyOn_raisedKoszulOp_of_mapCPConvergenceOn hU hfstC hfstU
    b bInf hb hbInf (fun x hx => hco x (hfstU hx)) (hconv _ hfstC hfstU)
  have hGammaC : TendstoUniformlyOn (fun (i : ℕ) (y : E × E) => Gamma (b i) y.1)
      (fun y => Gamma bInf y.1) atTop C := by
    rw [Metric.tendstoUniformlyOn_iff] at hGamma ⊢
    intro ε hε
    filter_upwards [hGamma ε hε] with i hi y hy
    exact hi y.1 (mem_image_of_mem Prod.fst hy)
  have hsnd : TendstoUniformlyOn (fun _ : ℕ => fun y : E × E => y.2) Prod.snd atTop C := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun _ _ _ => by simpa using hε
  have hGammaCont := continuousOn_raisedKoszulOp_fderiv hU hfstU hbInf
    (fun x hx => hco x (hfstU hx))
  have hK : IsCompact ((Gamma bInf '' (Prod.fst '' C)) ×ˢ (Prod.snd '' C)) :=
    (hfstC.image_of_continuousOn hGammaCont).prod (hC.image continuous_snd)
  let Psi : (E →L[ℝ] E →L[ℝ] E) × E → E × E := fun y => (y.2, -(y.1 y.2 y.2))
  have hPsi : Continuous Psi :=
    continuous_snd.prodMk ((continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd).neg
  exact (tendstoUniformlyOn_prodMk hGammaC hsnd).comp_continuousAt_of_isCompact hK
    (fun y hy => ⟨mem_image_of_mem (Gamma bInf) (mem_image_of_mem Prod.fst hy),
      mem_image_of_mem Prod.snd hy⟩) (fun y _ => hPsi.continuousAt)

end Spray

section Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance finiteFlowDual : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem two_le_succ {r : ℕ∞} (hr : 1 ≤ r) : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
  have h1 : (1 : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
  calc (2 : ℕ∞ω) = 1 + 1 := one_add_one_eq_two.symm
    _ ≤ (r : ℕ∞ω) + 1 := add_le_add_left h1 1

/-- **One chart along the limit orbit.** `C^{r+1}` metrics (`1 ≤ r`) `h i → g` in `C¹` in every
extended chart, orbits defined on `[a, b]`, the limit orbit inside the chart at `q`, and
convergence of the states at time `a`: eventually the approximating orbits stay in the chart and
converge uniformly in the tangent chart at `q`. -/
theorem finite_geodesicFlow_chart_confinement {r : ℕ∞} (hr : 1 ≤ r)
    (h : ℕ → ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hconv : ∀ (x : M) (C : Set E), IsCompact C → C ⊆ (extChartAt I x).target →
      MapCPConvergenceOn C 1 (fun i => chartCoeff (h i) x) (chartCoeff g x))
    (q : TangentBundle I M) (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M)
    {a b : ℝ} (hab : a ≤ b)
    (hdom : ∀ i, ∀ t ∈ Icc a b, (p i, t) ∈ (h i).geodesicFlowDomain)
    (hdomInf : ∀ t ∈ Icc a b, (pInf, t) ∈ g.geodesicFlowDomain)
    (hchartInf : ∀ t ∈ Icc a b, (g.geodesicFlow pInf t).proj ∈ (chartAt H q.proj).source)
    (hinit : Tendsto (fun i => (h i).geodesicFlow (p i) a) atTop (𝓝 (g.geodesicFlow pInf a))) :
    (∀ᶠ i in atTop, ∀ t ∈ Icc a b,
      ((h i).geodesicFlow (p i) t).proj ∈ (chartAt H q.proj).source) ∧
    TendstoUniformlyOn (fun i t => extChartAt I.tangent q ((h i).geodesicFlow (p i) t))
      (fun t => extChartAt I.tangent q (g.geodesicFlow pInf t)) atTop (Icc a b) := by
  have hn := two_le_succ hr
  let U := (extChartAt I q.proj).target
  have hU : IsOpen U := isOpen_extChartAt_target q.proj
  let e :=
    (DifferentialGeometry.PartialDiffeomorph.extChartAt I.tangent ∞ q).toOpenPartialHomeomorph
  have hb (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)) :
      ContDiffOn ℝ 2 (chartCoeff G q.proj) U :=
    contDiffOn_chartCoeff G hn q.proj
  have hco : ∀ x ∈ U, IsCoercive (chartCoeff g q.proj x) := fun x hx =>
    DifferentialGeometry.Analysis.isCoercive_of_pos_diagonal _ fun _ hv =>
      chartCoeff_pos g q.proj hx hv
  have heTarget : e.target ⊆ U ×ˢ univ := by
    change (extChartAt I.tangent q).target ⊆ U ×ˢ univ
    rw [FiberBundle.extChartAt_target]
    exact fun x hx => ⟨hx.1.1, hx.2⟩
  have heSource (x : TangentBundle I M) : x ∈ e.source ↔
      x.proj ∈ (chartAt H q.proj).source := by
    change x ∈ (extChartAt I.tangent q).source ↔ _
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
  let gamma (i : ℕ) := (h i).geodesicFlow (p i)
  let gammaInf := g.geodesicFlow pInf
  have hcontinuous : ∀ i, ContinuousOn (gamma i) (Icc a b) := fun i t ht =>
    ((h i).isMIntegralCurveOn_geodesicFlow hr (p i) t (hdom i t ht)).1.mono
      (fun s hs => hdom i s hs)
  have hsourceInf : MapsTo gammaInf (Icc a b) e.source :=
    fun t ht => (heSource _).mpr (hchartInf t ht)
  have hderiv (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
      (v : TangentBundle I M) (t : ℝ) (ht : (v, t) ∈ G.geodesicFlowDomain)
      (hsource : G.geodesicFlow v t ∈ e.source) :
      HasDerivWithinAt (e ∘ G.geodesicFlow v)
        (metricSpray (chartCoeff G q.proj) (e (G.geodesicFlow v t))) (Icc a b) t :=
    (G.hasDerivAt_geodesicFlow_chart hr ht q ((heSource _).mp hsource)).hasDerivWithinAt
  have hfield : ContDiffOn ℝ 1 (metricSpray (chartCoeff g q.proj)) e.target :=
    (metricSpray_contDiffOn_succ (n := 1) hU ((hb g).of_le (by norm_num)) hco).mono heTarget
  have hfieldConv : ∀ C : Set (E × E), IsCompact C → C ⊆ e.target →
      TendstoUniformlyOn (fun i => metricSpray (chartCoeff (h i) q.proj))
        (metricSpray (chartCoeff g q.proj)) atTop C := fun C hC hCe =>
    tendstoUniformlyOn_metricSpray_of_mapCPConvergenceOn hU (fun i => chartCoeff (h i) q.proj)
      (chartCoeff g q.proj) (fun i => (hb (h i)).of_le (by norm_num)) ((hb g).of_le (by norm_num))
      hco (hconv q.proj) hC (hCe.trans heTarget)
  have hstageODE := fun i t ht hs => hderiv (h i) (p i) t (hdom i t ht) hs
  have hlimitODE := fun t ht => hderiv g pInf t (hdomInf t ht) (hsourceInf ht)
  have hstay := eventually_mapsTo_chart_of_coordinate_ODE e hab gamma gammaInf
    (fun i => metricSpray (chartCoeff (h i) q.proj)) (metricSpray (chartCoeff g q.proj))
    hcontinuous hsourceInf hstageODE hlimitODE hfield hfieldConv hinit
  refine ⟨?_, tendstoUniformlyOn_chart_of_coordinate_ODE e hab gamma gammaInf
    (fun i => metricSpray (chartCoeff (h i) q.proj)) (metricSpray (chartCoeff g q.proj))
    hcontinuous hsourceInf hstageODE hlimitODE hfield hfieldConv hinit⟩
  filter_upwards [hstay] with i hi t ht
  exact (heSource _).mp (hi ht)

private theorem finite_flow_converges_on_chart_interval {r : ℕ∞} (hr : 1 ≤ r)
    (h : ℕ → ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hconv : ∀ (x : M) (C : Set E), IsCompact C → C ⊆ (extChartAt I x).target →
      MapCPConvergenceOn C 1 (fun i => chartCoeff (h i) x) (chartCoeff g x))
    (q : TangentBundle I M) (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M)
    {a b : ℝ} (hab : a ≤ b)
    (hdom : ∀ i, ∀ t ∈ Icc a b, (p i, t) ∈ (h i).geodesicFlowDomain)
    (hdomInf : ∀ t ∈ Icc a b, (pInf, t) ∈ g.geodesicFlowDomain)
    (hchartInf : ∀ t ∈ Icc a b, (g.geodesicFlow pInf t).proj ∈ (chartAt H q.proj).source)
    (hinit : Tendsto (fun i => (h i).geodesicFlow (p i) a) atTop (𝓝 (g.geodesicFlow pInf a))) :
    ∀ t ∈ Icc a b, Tendsto (fun i => (h i).geodesicFlow (p i) t) atTop
      (𝓝 (g.geodesicFlow pInf t)) := by
  obtain ⟨hstay, huniform⟩ := finite_geodesicFlow_chart_confinement hr h g hconv q p pInf hab
    hdom hdomInf hchartInf hinit
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

/-- **Whole interval.** `C^{r+1}` metrics (`1 ≤ r`) `h i → g` in `C¹` in every extended chart,
orbits defined on `[a, b]`, convergence of the states at time `a`: the states converge at every
time of `[a, b]`. -/
theorem finite_geodesicFlow_tendsto_on_Icc {r : ℕ∞} (hr : 1 ≤ r)
    (h : ℕ → ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hconv : ∀ (x : M) (C : Set E), IsCompact C → C ⊆ (extChartAt I x).target →
      MapCPConvergenceOn C 1 (fun i => chartCoeff (h i) x) (chartCoeff g x))
    (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M) {a b : ℝ} (hab : a ≤ b)
    (hdom : ∀ i, ∀ t ∈ Icc a b, (p i, t) ∈ (h i).geodesicFlowDomain)
    (hdomInf : ∀ t ∈ Icc a b, (pInf, t) ∈ g.geodesicFlowDomain)
    (hinit : Tendsto (fun i => (h i).geodesicFlow (p i) a) atTop (𝓝 (g.geodesicFlow pInf a))) :
    ∀ t ∈ Icc a b, Tendsto (fun i => (h i).geodesicFlow (p i) t) atTop
      (𝓝 (g.geodesicFlow pInf t)) := by
  let good (t : ℝ) := Tendsto (fun i => (h i).geodesicFlow (p i) t) atTop
    (𝓝 (g.geodesicFlow pInf t))
  let A : Set ℝ := {t ∈ Icc a b | ∀ s ∈ Icc a t, good s}
  have hcontinuous : ContinuousOn (g.geodesicFlow pInf) (Icc a b) := fun t ht =>
    (g.isMIntegralCurveOn_geodesicFlow hr pInf t (hdomInf t ht)).1.mono
      (fun s hs => hdomInf s hs)
  have hlocal (t : ℝ) (ht : t ∈ Icc a b) : ∃ δ > 0, ∀ s ∈ ball t δ ∩ Icc a b,
      (g.geodesicFlow pInf s).proj ∈ (chartAt H (g.geodesicFlow pInf t).proj).source := by
    let q := g.geodesicFlow pInf t
    have hnh : (g.geodesicFlow pInf) ⁻¹' (extChartAt I.tangent q).source ∈ 𝓝[Icc a b] t :=
      (hcontinuous t ht).preimage_mem_nhdsWithin
        ((isOpen_extChartAt_source (I := I.tangent) q).mem_nhds
          (mem_extChartAt_source (I := I.tangent) q))
    obtain ⟨δ, hδ, hsubset⟩ := Metric.mem_nhdsWithin_iff.mp hnh
    refine ⟨δ, hδ, fun s hs => ?_⟩
    have hh := hsubset hs
    change g.geodesicFlow pInf s ∈ (extChartAt I.tangent q).source at hh
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff] at hh
    exact hh
  have hpropagate (q : TangentBundle I M) {u v : ℝ} (hu : a ≤ u) (hv : v ≤ b) (huv : u ≤ v)
      (hchart : ∀ s ∈ Icc u v, (g.geodesicFlow pInf s).proj ∈ (chartAt H q.proj).source)
      (hgood : good u) : ∀ s ∈ Icc u v, good s :=
    finite_flow_converges_on_chart_interval hr h g hconv q p pInf huv
      (fun i s hs => hdom i s (Icc_subset_Icc hu hv hs))
      (fun s hs => hdomInf s (Icc_subset_Icc hu hv hs)) hchart hgood
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
    apply hpropagate (g.geodesicFlow pInf T) hu.1.1 hT.2 huT
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
      hpropagate (g.geodesicFlow pInf T) hT.1 hcb hTc.le
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

/-- **G5-M.** CM-P's geodesic flow of `C^{r+1}` metrics (`1 ≤ r`) is continuous in the metric
(chart `C¹` convergence in every extended chart) and in the initial data: if `p i → p∞`, and the
orbits of `p i` for `h i` and of `p∞` for `g` are defined on `[0, T]`, then
`(h i).geodesicFlow (p i) t → g.geodesicFlow p∞ t` for every `t ∈ [0, T]`. -/
theorem tendsto_geodesicFlow_of_chart_C1_tendsto {r : ℕ∞} (hr : 1 ≤ r)
    (h : ℕ → ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hconv : ∀ (x : M) (C : Set E), IsCompact C → C ⊆ (extChartAt I x).target →
      MapCPConvergenceOn C 1 (fun i => chartCoeff (h i) x) (chartCoeff g x))
    {p : ℕ → TangentBundle I M} {pInf : TangentBundle I M} (hp : Tendsto p atTop (𝓝 pInf))
    {T : ℝ} (hT : 0 ≤ T) (hdom : ∀ t ∈ Icc 0 T, (pInf, t) ∈ g.geodesicFlowDomain)
    (hdomi : ∀ i, ∀ t ∈ Icc 0 T, (p i, t) ∈ (h i).geodesicFlowDomain) :
    ∀ t ∈ Icc 0 T, Tendsto (fun i => (h i).geodesicFlow (p i) t) atTop
      (𝓝 (g.geodesicFlow pInf t)) := by
  refine finite_geodesicFlow_tendsto_on_Icc hr h g hconv p pInf hT hdomi hdom ?_
  simp only [ContMDiffRiemannianMetric.geodesicFlow_zero _ hr]
  exact hp

end Flow

end DifferentialGeometry.Geometry.Riemannian.Geodesic
