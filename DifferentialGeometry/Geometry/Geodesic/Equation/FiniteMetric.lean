import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity
import DifferentialGeometry.Bundle.TangentChart
import DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetric
import DifferentialGeometry.Geometry.Geodesic.Equation.MetricSprayFiniteRegularity
import DifferentialGeometry.Geometry.Geodesic.Naturality.MetricSpray
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCoefficients
import Mathlib.Geometry.Manifold.VectorField.Pullback

set_option autoImplicit false

noncomputable section ChartNaturality

open Bundle Set
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

open DifferentialGeometry.MetricKoszul (metricSpray fderiv_tangent_lift_metricSpray)
open private pullbackCoefficients isCoercive_chartCoefficients chartCoefficients_transition from
  DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DifferentialGeometry.ContinuousDualEquiv E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

private theorem fderiv_tangent_lift_chart_metricSpray {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hn : 1 ≤ n) (φ ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 3)
    {z : E × E} (hz : z.1 ∈ (φ.trans ψ.symm).source) :
    let b := fun x => (g.inner (φ x) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
      (mfderiv 𝓘(ℝ, E) I φ x : E →L[ℝ] E) (mfderiv 𝓘(ℝ, E) I φ x : E →L[ℝ] E)
    let c := fun x => (g.inner (ψ x) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
      (mfderiv 𝓘(ℝ, E) I ψ x : E →L[ℝ] E) (mfderiv 𝓘(ℝ, E) I ψ x : E →L[ℝ] E)
    let T := φ.trans ψ.symm
    fderiv ℝ (fun p : E × E => (T p.1, fderiv ℝ T p.1 p.2)) z (metricSpray b z) =
      metricSpray c (T z.1, fderiv ℝ T z.1 z.2) := by
  let T := φ.trans ψ.symm
  change fderiv ℝ (fun p : E × E => (T p.1, fderiv ℝ T p.1 p.2)) z
      (metricSpray (pullbackCoefficients g φ) z) =
    metricSpray (pullbackCoefficients g ψ) (T z.1, fderiv ℝ T z.1 z.2)
  apply fderiv_tangent_lift_metricSpray T.open_source ψ.open_source
    (g.contDiffOn_pullback_inner hn (by norm_num) ψ.open_source ψ.contMDiffOn_toFun)
  · intro x hx v w
    exact g.symm (ψ x) _ _
  · intro x hx
    exact isCoercive_chartCoefficients g ψ hx
  · exact T.contMDiffOn_toFun.contDiffOn.of_le (by norm_num)
  · intro x hx
    exact ψ.map_target hx.2
  · intro x hx
    let A := (T.isLocalDiffeomorphAt _ _ _ hx).mfderivToContinuousLinearEquiv (by norm_num)
    refine ⟨(NormedSpace.fromTangentSpace x).symm.trans
      (A.trans (NormedSpace.fromTangentSpace (T x))), ?_⟩
    ext v
    change (NormedSpace.fromTangentSpace (T x))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) T x ((NormedSpace.fromTangentSpace x).symm v)) = _
    rw [mfderiv_eq_fderiv]
    rfl
  · intro x hx v w
    exact congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v w)
      (chartCoefficients_transition g φ ψ hx)
  · exact hz

end Bundle.ContMDiffRiemannianMetric

end ChartNaturality

set_option autoImplicit false

noncomputable section TangentCharts

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

open private chartDerivative_transition from
  DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [I.Boundaryless] in
private theorem tangent_chart_apply (a p : TangentBundle I M)
    (hp : p.proj ∈ (chartAt H a.proj).source) :
    extChartAt I.tangent a p =
      (extChartAt I a.proj p.proj, mfderiv I 𝓘(ℝ, E) (extChartAt I a.proj) p.proj p.snd) := by
  apply Prod.ext
  · exact TangentBundle.extChartAt_tangent_apply_fst a
  · rw [TangentBundle.extChartAt_tangent_apply_snd a hp,
      TangentBundle.continuousLinearMapAt_trivializationAt hp]
    rfl

private theorem tangent_chart_transition_apply (a b : TangentBundle I M) {z : E × E}
    (hz : z ∈ (extChartAt I.tangent a).target)
    (hb : ((extChartAt I.tangent a).symm z).proj ∈ (chartAt H b.proj).source) :
    let T := (DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 a.proj).symm.trans
      (DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 b.proj)
    extChartAt I.tangent b ((extChartAt I.tangent a).symm z) =
      (T z.1, fderiv ℝ T z.1 z.2) := by
  let p := (extChartAt I.tangent a).symm z
  let e := DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 a.proj
  let f := DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 b.proj
  have hp : p.proj ∈ (chartAt H a.proj).source := by
    have h := (extChartAt I.tangent a).map_target hz
    simpa only [extChartAt_source, TangentBundle.mem_chart_source_iff] using h
  have he : p.proj ∈ e.source := by
    change p.proj ∈ (extChartAt I a.proj).source
    simpa only [extChartAt_source] using hp
  have hf : p.proj ∈ f.source := by
    change p.proj ∈ (extChartAt I b.proj).source
    simpa only [extChartAt_source] using hb
  have hz' : extChartAt I.tangent a p = z := (extChartAt I.tangent a).right_inv hz
  have hx : e p.proj = z.1 := by
    exact (congrArg Prod.fst (tangent_chart_apply a p hp)).symm.trans (congrArg Prod.fst hz')
  have hv : mfderiv I 𝓘(ℝ, E) e p.proj p.snd = z.2 := by
    exact (congrArg Prod.snd (tangent_chart_apply a p hp)).symm.trans (congrArg Prod.snd hz')
  change extChartAt I.tangent b p =
    ((e.symm.trans f) z.1, fderiv ℝ (e.symm.trans f) z.1 z.2)
  rw [tangent_chart_apply b p hb, ← hx, ← hv]
  apply Prod.ext
  · exact (congrArg f (e.left_inv he)).symm
  · exact (congrArg (fun L : E →L[ℝ] E => L p.snd)
      (chartDerivative_transition e f he hf)).symm

private theorem tangent_chart_transition_eventuallyEq (a b p : TangentBundle I M)
    (ha : p.proj ∈ (chartAt H a.proj).source)
    (hb : p.proj ∈ (chartAt H b.proj).source) :
    let T := (DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 a.proj).symm.trans
      (DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 b.proj)
    (extChartAt I.tangent b ∘ (extChartAt I.tangent a).symm) =ᶠ[𝓝 (extChartAt I.tangent a p)]
      (fun z : E × E => (T z.1, fderiv ℝ T z.1 z.2)) := by
  have haT : p ∈ (extChartAt I.tangent a).source := by
    simpa only [extChartAt_source, TangentBundle.mem_chart_source_iff] using ha
  have hbT : p ∈ (extChartAt I.tangent b).source := by
    simpa only [extChartAt_source, TangentBundle.mem_chart_source_iff] using hb
  let e := DifferentialGeometry.PartialDiffeomorph.extChartAt I.tangent 3 a
  have hz : e p ∈ e.target := e.map_source haT
  have hcont : ContinuousAt e.symm (e p) :=
    e.contMDiffOn_invFun.continuousOn.continuousAt (e.open_target.mem_nhds hz)
  have hpre : e.symm ⁻¹' (extChartAt I.tangent b).source ∈ 𝓝 (e p) :=
    hcont.preimage_mem_nhds (by
      change (extChartAt I.tangent b).source ∈ 𝓝 ((extChartAt I.tangent a).symm
        (extChartAt I.tangent a p))
      rw [(extChartAt I.tangent a).left_inv haT]
      exact (isOpen_extChartAt_source b).mem_nhds hbT)
  filter_upwards [e.open_target.mem_nhds hz, hpre] with z hz' hb'
  change (extChartAt I.tangent a).symm z ∈ (extChartAt I.tangent b).source at hb'
  exact tangent_chart_transition_apply a b hz' (by
    simpa only [extChartAt_source, TangentBundle.mem_chart_source_iff] using hb')

end Bundle.ContMDiffRiemannianMetric

end TangentCharts

set_option autoImplicit false

noncomputable section IntrinsicSpray

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

open DifferentialGeometry.MetricKoszul (metricSpray metricSpray_contDiffOn_succ)
open private pullbackCoefficients isCoercive_chartCoefficients from
  DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local instance : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

def geodesicSpray {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (p : TangentBundle I M) : TangentSpace I.tangent p :=
  metricSpray (pullbackCoefficients g (extChartAt I p.proj).symm)
    (extChartAt I p.proj p.proj, p.snd)

omit [I.Boundaryless] in
@[simp]
theorem geodesicSpray_fst {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (p : TangentBundle I M) : (g.geodesicSpray p).1 = p.snd := rfl

omit [I.Boundaryless] in
theorem mfderiv_proj_geodesicSpray {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (p : TangentBundle I M) :
    mfderiv I.tangent I (TotalSpace.proj : TangentBundle I M → M) p
      (g.geodesicSpray p) = p.snd := by
  have heq : extChartAt I p.proj ∘ (TotalSpace.proj : TangentBundle I M → M) =
      Prod.fst ∘ extChartAt I.tangent p := by
    funext q
    exact (TangentBundle.extChartAt_tangent_apply_fst p).symm
  have hd := congrArg
    (fun f : TangentBundle I M → E => mvfderiv I.tangent f p (g.geodesicSpray p)) heq
  change mfderiv I.tangent 𝓘(ℝ, E)
      (extChartAt I p.proj ∘ (TotalSpace.proj : TangentBundle I M → M)) p
      (g.geodesicSpray p) =
    mfderiv I.tangent 𝓘(ℝ, E) (Prod.fst ∘ extChartAt I.tangent p) p
      (g.geodesicSpray p) at hd
  rw [mfderiv_comp p
      (mdifferentiableAt_extChartAt (mem_chart_source H p.proj))
      (Bundle.mdifferentiable_proj (TangentSpace I) p),
    mfderiv_comp p
      (differentiableAt_fst.mdifferentiableAt)
      (mdifferentiableAt_extChartAt (mem_chart_source (ModelProd H E) p))] at hd
  simp only [ContinuousLinearMap.comp_apply] at hd
  erw [mfderiv_extChartAt_self, mfderiv_extChartAt_self] at hd
  change mfderiv I.tangent I (TotalSpace.proj : TangentBundle I M → M) p
      (g.geodesicSpray p) =
    mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) Prod.fst (extChartAt I.tangent p p)
      (g.geodesicSpray p) at hd
  rw [mfderiv_eq_fderiv, fderiv_fst] at hd
  exact hd

theorem mfderiv_geodesicSpray_chart {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hn : 1 ≤ n) (q p : TangentBundle I M)
    (hp : p.proj ∈ (chartAt H q.proj).source) :
    mfderiv I.tangent 𝓘(ℝ, E × E) (extChartAt I.tangent q) p (g.geodesicSpray p) =
      metricSpray (fun x => (g.inner ((extChartAt I q.proj).symm x) :
        E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
          (mfderiv 𝓘(ℝ, E) I (extChartAt I q.proj).symm x : E →L[ℝ] E)
          (mfderiv 𝓘(ℝ, E) I (extChartAt I q.proj).symm x : E →L[ℝ] E))
        (extChartAt I.tangent q p) := by
  let e := DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 p.proj
  let f := DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 q.proj
  let T := e.symm.trans f
  let z := extChartAt I.tangent p p
  have hself : p.proj ∈ (chartAt H p.proj).source := mem_chart_source H p.proj
  have hpT : p ∈ (extChartAt I.tangent q).source := by
    simpa only [extChartAt_source, TangentBundle.mem_chart_source_iff] using hp
  have he : p.proj ∈ e.source := by
    change p.proj ∈ (extChartAt I p.proj).source
    exact mem_extChartAt_source p.proj
  have hf : p.proj ∈ f.source := by
    change p.proj ∈ (extChartAt I q.proj).source
    simpa only [extChartAt_source] using hp
  have hz : z = (e p.proj, (p.snd : E)) := by
    dsimp only [z]
    rw [tangent_chart_apply p p hself, mfderiv_extChartAt_self]
    rfl
  have hzT : z.1 ∈ T.source := by
    rw [hz]
    refine ⟨e.map_source he, ?_⟩
    change (extChartAt I p.proj).symm (extChartAt I p.proj p.proj) ∈ f.source
    rw [(extChartAt I p.proj).left_inv (mem_extChartAt_source p.proj)]
    exact hf
  have hchart := tangent_chart_transition_eventuallyEq p q p hself hp
  have hderiv : fderiv ℝ (fun w : E × E => (T w.1, fderiv ℝ T w.1 w.2)) z =
      mfderiv I.tangent 𝓘(ℝ, E × E) (extChartAt I.tangent q) p := by
    rw [← hchart.fderiv_eq]
    let c := DifferentialGeometry.PartialDiffeomorph.extChartAt I.tangent 3 p
    have hpc : p ∈ c.source := mem_extChartAt_source p
    have hz' : z ∈ c.target := c.map_source hpc
    have hinv : c.symm z = p := c.left_inv hpc
    have hqdiff :=
      (DifferentialGeometry.PartialDiffeomorph.extChartAt I.tangent 3 q).mdifferentiableAt
        (by norm_num) hpT
    have hselfinv : mfderiv 𝓘(ℝ, E × E) I.tangent c.symm z =
        ContinuousLinearMap.id ℝ (E × E) := by
      have h := mfderivWithin_range_extChartAt_symm (I := I.tangent) (x := p)
      rw [I.tangent.range_eq_univ, mfderivWithin_univ] at h
      exact h
    apply ContinuousLinearMap.ext
    intro v
    have hd := mfderiv_comp_apply_of_eq z hqdiff
      (c.symm.mdifferentiableAt (by norm_num) hz') hinv v
    rw [mfderiv_eq_fderiv] at hd
    change fderiv ℝ (extChartAt I.tangent q ∘ (extChartAt I.tangent p).symm) z v =
      mfderiv I.tangent 𝓘(ℝ, E × E) (extChartAt I.tangent q) p
        (mfderiv 𝓘(ℝ, E × E) I.tangent c.symm z v) at hd
    erw [hselfinv] at hd
    exact hd
  have hspray := g.fderiv_tangent_lift_chart_metricSpray hn e.symm f.symm hzT
  change fderiv ℝ (fun w : E × E => (T w.1, fderiv ℝ T w.1 w.2)) z
      (metricSpray (pullbackCoefficients g e.symm) z) =
    metricSpray (pullbackCoefficients g f.symm) (T z.1, fderiv ℝ T z.1 z.2) at hspray
  have htarget : (T z.1, fderiv ℝ T z.1 z.2) = extChartAt I.tangent q p := by
    have h := hchart.eq_of_nhds
    dsimp only [Function.comp_apply] at h
    rw [(extChartAt I.tangent p).left_inv (mem_extChartAt_source p)] at h
    exact h.symm
  rw [hderiv, htarget] at hspray
  exact (congrArg (fun w : E × E =>
    mfderiv I.tangent 𝓘(ℝ, E × E) (extChartAt I.tangent q) p
      (metricSpray (pullbackCoefficients g e.symm) w)) hz).symm.trans hspray

theorem contMDiff_geodesicSpray {r : ℕ∞}
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)) :
    ContMDiff I.tangent I.tangent.tangent r
      (fun p : TangentBundle I M =>
        (⟨p, g.geodesicSpray p⟩ : TangentBundle I.tangent (TangentBundle I M))) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro p
  let e := DifferentialGeometry.PartialDiffeomorph.extChartAt I ∞ p.proj
  let b := pullbackCoefficients g e.symm
  let V : E × E → E × E := metricSpray b
  have hb : ContDiffOn ℝ ((r : ℕ∞ω) + 1) b e.target :=
    g.contDiffOn_pullback_inner le_rfl (by simp) e.open_target e.contMDiffOn_invFun
  have hco : ∀ x ∈ e.target, IsCoercive (b x) := by
    intro x hx
    exact isCoercive_chartCoefficients g
      (DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 p.proj).symm hx
  have hV := metricSpray_contDiffOn_succ e.open_target hb hco
  have hp₁ : (extChartAt I.tangent p p).1 ∈ e.target := by
    rw [TangentBundle.extChartAt_tangent_apply_fst]
    exact e.map_source (mem_extChartAt_source p.proj)
  have hVAt : ContDiffAt ℝ (r : ℕ∞ω) V (extChartAt I.tangent p p) :=
    hV.contDiffAt ((e.open_target.prod isOpen_univ).mem_nhds ⟨hp₁, mem_univ _⟩)
  have hsection : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E × E).tangent r
      (fun z : E × E => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E × E) (E × E)))
      (extChartAt I.tangent p p) := by
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    apply hVAt.contMDiffAt.congr_of_eventuallyEq
    filter_upwards with z
    rw [trivializationAt_model_space_apply]
  have hlocal := hsection.mpullback_vectorField_preimage
    (contMDiffAt_extChartAt (I := I.tangent) (n := ∞) (x := p))
    (isInvertible_mfderiv_extChartAt (I := I.tangent) (mem_extChartAt_source p))
    (by simp)
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := I.tangent) p).mem_nhds
    (mem_extChartAt_source p)] with q hq
  have hq' : q.proj ∈ (chartAt H p.proj).source := by
    simpa only [extChartAt_source, TangentBundle.mem_chart_source_iff] using hq
  have hread := g.mfderiv_geodesicSpray_chart
    (le_add_of_nonneg_left (show (0 : ℕ∞ω) ≤ r from zero_le)) p q hq'
  have hinv := isInvertible_mfderiv_extChartAt (I := I.tangent) hq
  have heq : VectorField.mpullback I.tangent 𝓘(ℝ, E × E)
      (extChartAt I.tangent p) V q = g.geodesicSpray q := by
    apply hinv.inverse_apply_eq.mpr
    exact hread.symm
  exact congrArg (fun v : TangentSpace I.tangent q =>
    (⟨q, v⟩ : TangentBundle I.tangent (TangentBundle I M))) heq.symm

omit [I.Boundaryless] in
@[simp]
theorem geodesicSpray_zero {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x : M) :
    g.geodesicSpray (⟨x, 0⟩ : TangentBundle I M) = 0 := by
  apply Prod.ext
  · rfl
  · change -(_ : E →L[ℝ] E →L[ℝ] E) (0 : E) (0 : E) = 0
    rw [map_zero, neg_zero]


end Bundle.ContMDiffRiemannianMetric

end IntrinsicSpray
