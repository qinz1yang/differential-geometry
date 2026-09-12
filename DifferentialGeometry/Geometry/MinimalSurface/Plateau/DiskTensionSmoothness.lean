import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskCovariantCoordinates
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong

noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Topology ContDiff Bundle Manifold ENat BigOperators

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem deriv_comp_line {F : ℂ → E} {z v : ℂ} (hF : DifferentiableAt ℝ F z) :
    deriv (fun t : ℝ => F (z + t • v)) 0 = fderiv ℝ F z v := by
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hz : (fun t : ℝ => z + t • v) 0 = z := by simp
  exact (hF.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) hline hz.symm).deriv

set_option backward.isDefEq.respectTransparency false in
theorem diskMapPartial_trivAt_eq_fderiv {U : ℂ → M} {α : M} {z : ℂ} (w : ℂ)
    (hsrc : U z ∈ (chartAt E α).source)
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) α).continuousLinearMapAt ℝ (U z)
        (diskMapPartial U z w)
      = fderiv ℝ (fun q => extChartAt 𝓘(ℝ, E) α (U q)) z w := by
  have h : ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) α).continuousLinearMapAt ℝ (U z)).comp
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) =
      fderiv ℝ ((extChartAt 𝓘(ℝ, E) α) ∘ U) z := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := 𝓘(ℝ, E)) hsrc,
      ← mfderiv_comp z (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E)) hsrc) hU,
      mfderiv_eq_fderiv]
  exact congrArg (fun L => L w) h

variable [FiniteDimensional ℝ E]

theorem diskMapCovariantPartial_trivAt_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {α : M}
    (hsrc : ∀ z ∈ s, U z ∈ (chartAt E α).source) {z : ℂ} (hz : z ∈ s) (v w : ℂ) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) α).continuousLinearMapAt ℝ (U z)
        (diskMapCovariantPartial g U z v w)
      = fderiv ℝ (fun q => fderiv ℝ (fun r => extChartAt 𝓘(ℝ, E) α (U r)) q w) z v
        + chartChristoffelContraction g α
            (fderiv ℝ (fun r => extChartAt 𝓘(ℝ, E) α (U r)) z v)
            (fderiv ℝ (fun r => extChartAt 𝓘(ℝ, E) α (U r)) z w)
            (extChartAt 𝓘(ℝ, E) α (U z)) := by
  set γ : ℝ → M := fun t => U (z + t • v) with hγdef
  set Vf : ∀ t, TangentSpace 𝓘(ℝ, E) (γ t) :=
    fun t => mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (z + t • v) w with hVdef
  set G : ℂ → E := fun r => extChartAt 𝓘(ℝ, E) α (U r) with hGdef
  have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (fun t : ℝ => z + t • v) 0 := by
    have hc : ContDiff ℝ ∞ (fun t : ℝ => z + t • v) := by fun_prop
    exact hc.contDiffAt.contMDiffAt
  have hz0 : (fun t : ℝ => z + t • v) 0 ∈ s := by
    simpa only [zero_smul, add_zero] using hz
  have hUat : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U ((fun t : ℝ => z + t • v) 0) :=
    hU.contMDiffAt (hs.mem_nhds hz0)
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0 := by
    have h := (hUat.comp 0 hline).mdifferentiableAt (by simp)
    simpa only [hγdef, Function.comp_def] using h
  have hsecAt : ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z' => TotalSpace.mk' E (U z') (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z' w))
      ((fun t : ℝ => z + t • v) 0) :=
    (contMDiffOn_source_partial hs hU le_rfl w).contMDiffAt (hs.mem_nhds hz0)
  have hsec : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun t : ℝ => TotalSpace.mk' E (γ t) (Vf t)) 0 := by
    have h := hsecAt.comp 0 hline
    simpa only [hγdef, hVdef, Function.comp_def] using h
  have hVdiff : DifferentiableAt ℝ (chartRepAt γ Vf 0) 0 :=
    (contDiffAt_chartRepAt_of_section hsec).differentiableAt (by simp)
  have hβ : γ 0 ∈ (chartAt E α).source := by
    rw [hγdef]
    simpa only [zero_smul, add_zero] using hsrc z hz
  have hcov := covDeriv_chartAt g γ Vf 0 α hγ hβ hVdiff
  have hb : γ 0 ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hβ
  have hkey : (trivializationAt E (TangentSpace 𝓘(ℝ, E)) α).continuousLinearMapAt ℝ (γ 0)
      (covDerivAlong g γ Vf 0)
      = chartCovDerivAlong g α γ (chartRepAtBase α γ Vf) 0 := by
    rw [← hcov]
    exact (trivializationAt E (TangentSpace 𝓘(ℝ, E)) α).continuousLinearMapAt_symmL (R := ℝ) hb _
  have hrep : chartRepAtBase (I := 𝓘(ℝ, E)) α γ Vf =ᶠ[𝓝 (0 : ℝ)]
      fun t : ℝ => fderiv ℝ G (z + t • v) w := by
    have hcont : ContinuousAt γ 0 := hγ.continuousAt
    filter_upwards [hline.continuousAt.preimage_mem_nhds (hs.mem_nhds hz0),
      hcont.eventually ((chartAt E α).open_source.mem_nhds hβ)] with t ht hγt
    rw [chartRepAtBase_apply, hγdef, hVdef]
    have hH := diskMapPartial_trivAt_eq_fderiv (E := E) (U := U) (α := α) (z := z + t • v) w
      (by rw [hγdef] at hγt; exact hγt)
      ((hU.contMDiffAt (hs.mem_nhds ht)).mdifferentiableAt (by simp))
    simpa only [hGdef, diskMapPartial] using hH
  have hGdiffAt : ContDiffAt ℝ ∞ G z := by
    have h1 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U z := hU.contMDiffAt (hs.mem_nhds hz)
    have h2 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (extChartAt 𝓘(ℝ, E) α) (U z) :=
      contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (x := α) (n := ∞) (hsrc z hz)
    have h3 := h2.comp z h1
    rw [hGdef]
    simpa only [Function.comp_def] using h3.contDiffAt
  have hGc1 : ContDiffAt ℝ ∞ (fun q : ℂ => fderiv ℝ G q) z :=
    hGdiffAt.fderiv_right (m := ∞) (by simp)
  have hGc2 : ContDiffAt ℝ ∞ (fun q : ℂ => fderiv ℝ G q w) z :=
    (((ContinuousLinearMap.apply ℝ E w).contDiff).contDiffAt).comp z hGc1
  have hderiv_rep : deriv (chartRepAtBase (I := 𝓘(ℝ, E)) α γ Vf) 0
      = fderiv ℝ (fun q => fderiv ℝ G q w) z v := by
    rw [hrep.deriv_eq]
    exact deriv_comp_line (hGc2.differentiableAt (by simp))
  have hcurve_eq : chartCurve (I := 𝓘(ℝ, E)) α γ = fun t : ℝ => G (z + t • v) := by
    funext t; rw [chartCurve_def, hGdef, hγdef]
  have hderiv_curve : deriv (chartCurve (I := 𝓘(ℝ, E)) α γ) 0 = fderiv ℝ G z v := by
    rw [hcurve_eq]
    exact deriv_comp_line (hGdiffAt.differentiableAt (by simp))
  have hrep0 : chartRepAtBase (I := 𝓘(ℝ, E)) α γ Vf 0 = fderiv ℝ G z w := by
    rw [hrep.eq_of_nhds]
    simp only [zero_smul, add_zero]
  have hcurve0 : chartCurve (I := 𝓘(ℝ, E)) α γ 0 = G z := by
    rw [hcurve_eq]
    simp only [zero_smul, add_zero]
  have hLHS : (trivializationAt E (TangentSpace 𝓘(ℝ, E)) α).continuousLinearMapAt ℝ (U z)
        (diskMapCovariantPartial g U z v w)
      = (trivializationAt E (TangentSpace 𝓘(ℝ, E)) α).continuousLinearMapAt ℝ (γ 0)
        (covDerivAlong g γ Vf 0) := by
    have hγ0 : γ 0 = U z := by rw [hγdef]; simp
    rw [← hγ0]
    congr 1
  rw [hLHS, hkey, chartCovDerivAlong_def, hderiv_rep, hderiv_curve, hrep0, hcurve0]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem contDiffOn_diskMapCovariantPartial_trivAt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {α : M}
    (hsrc : ∀ z ∈ s, U z ∈ (chartAt E α).source) (v w : ℂ) :
    ContDiffOn ℝ ∞ (fun z => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) α).continuousLinearMapAt ℝ
      (U z) (diskMapCovariantPartial g U z v w)) s := by
  set G : ℂ → E := fun r => extChartAt 𝓘(ℝ, E) α (U r) with hGdef
  have hGcm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ G s := by
    intro z hz
    have h1 : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s z := hU z hz
    have h2 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (extChartAt 𝓘(ℝ, E) α) (U z) :=
      contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (x := α) (n := ∞) (hsrc z hz)
    have h3 := h2.comp_contMDiffWithinAt z h1
    simpa only [hGdef, Function.comp_def] using h3
  have hG : ContDiffOn ℝ ∞ G s := hGcm.contDiffOn
  have hH : ContDiffOn ℝ ∞ (fderiv ℝ G) s := hG.fderiv_of_isOpen hs (by simp)
  have hK : ContDiffOn ℝ ∞ (fun q : ℂ => fderiv ℝ G q w) s :=
    ((ContinuousLinearMap.apply ℝ E w).contDiff.contDiffOn).comp hH (fun _ _ => mem_univ _)
  have hKd : ContDiffOn ℝ ∞ (fderiv ℝ (fun q : ℂ => fderiv ℝ G q w)) s :=
    hK.fderiv_of_isOpen hs (by simp)
  have h1 : ContDiffOn ℝ ∞ (fun z : ℂ => fderiv ℝ (fun q : ℂ => fderiv ℝ G q w) z v) s :=
    ((ContinuousLinearMap.apply ℝ E v).contDiff.contDiffOn).comp hKd (fun _ _ => mem_univ _)
  have h2 : ContDiffOn ℝ ∞ (fun z : ℂ => fderiv ℝ G z v) s :=
    ((ContinuousLinearMap.apply ℝ E v).contDiff.contDiffOn).comp hH (fun _ _ => mem_univ _)
  have h3 : ContDiffOn ℝ ∞ (fun z : ℂ => fderiv ℝ G z w) s :=
    ((ContinuousLinearMap.apply ℝ E w).contDiff.contDiffOn).comp hH (fun _ _ => mem_univ _)
  have hΓ : ContDiffOn ℝ ∞ (fun z : ℂ => chartChristoffelContraction g α
      (fderiv ℝ G z v) (fderiv ℝ G z w) (G z)) s := by
    intro z hz
    have hmem : U z ∈ (extChartAt 𝓘(ℝ, E) α).source := by
      rw [DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source (I := 𝓘(ℝ, E))]
      exact hsrc z hz
    have hy : G z ∈ interior (extChartAt 𝓘(ℝ, E) α).target := by
      have h' := DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
        (I := 𝓘(ℝ, E)) α ((extChartAt 𝓘(ℝ, E) α).map_source hmem)
      simpa only [hGdef] using h'
    refine ((contDiffAt_chartChristoffelContraction g α (fderiv ℝ G z v) (fderiv ℝ G z w) (G z) hy).comp
      (x := z) (g := fun p : E × E × E => chartChristoffelContraction g α p.1 p.2.1 p.2.2)
      (f := fun z : ℂ => (fderiv ℝ G z v, fderiv ℝ G z w, G z)) ?_).contDiffWithinAt
    exact (h2.contDiffAt (hs.mem_nhds hz)).prodMk
      ((h3.contDiffAt (hs.mem_nhds hz)).prodMk (hG.contDiffAt (hs.mem_nhds hz)))
  have hchart : ContDiffOn ℝ ∞ (fun z : ℂ => fderiv ℝ (fun q : ℂ => fderiv ℝ G q w) z v
      + chartChristoffelContraction g α (fderiv ℝ G z v) (fderiv ℝ G z w) (G z)) s :=
    h1.add hΓ
  refine hchart.congr (fun z hz => ?_)
  simpa only [hGdef] using (diskMapCovariantPartial_trivAt_eq g hs hU hsrc hz v w)

theorem contDiffOn_diskMapTension_trivAt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {α : M}
    (hsrc : ∀ z ∈ s, U z ∈ (chartAt E α).source) :
    ContDiffOn ℝ ∞ (fun z => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) α).continuousLinearMapAt ℝ
      (U z) (diskMapTension g U z)) s := by
  have h1 := contDiffOn_diskMapCovariantPartial_trivAt g hs hU hsrc 1 1
  have h2 := contDiffOn_diskMapCovariantPartial_trivAt g hs hU hsrc Complex.I Complex.I
  refine (h1.add h2).congr (fun z hz => ?_)
  simp only [diskMapTension, map_add]

theorem contDiffAt_trivialized_diskMapTension
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {z₀ : ℂ} (hz₀ : z₀ ∈ s)
    (hsrc : ∀ z ∈ s, U z ∈ (chartAt E (U z₀)).source) :
    ContDiffAt ℝ ∞ (fun z => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z₀)).continuousLinearMapAt ℝ
      (U z) (diskMapTension g U z)) z₀ :=
  (contDiffOn_diskMapTension_trivAt g hs hU hsrc).contDiffAt (hs.mem_nhds hz₀)


theorem contMDiffOn_totalSpace_diskMapTension
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (diskMapTension g U z)) s := by
  intro z₀ hz₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨hU z₀ hz₀, ?_⟩
  have hUcont : ContinuousAt U z₀ := (hU.contMDiffAt (hs.mem_nhds hz₀)).continuousAt
  have hpre : U ⁻¹' (chartAt E (U z₀)).source ∈ 𝓝 z₀ :=
    hUcont.preimage_mem_nhds ((chartAt E (U z₀)).open_source.mem_nhds (mem_chart_source E (U z₀)))
  have hs' : IsOpen (s ∩ U ⁻¹' (chartAt E (U z₀)).source) :=
    hU.continuousOn.isOpen_inter_preimage hs (chartAt E (U z₀)).open_source
  have hz₀' : z₀ ∈ s ∩ U ⁻¹' (chartAt E (U z₀)).source :=
    ⟨hz₀, mem_chart_source E (U z₀)⟩
  have hU' : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (s ∩ U ⁻¹' (chartAt E (U z₀)).source) :=
    hU.mono inter_subset_left
  have hsrc' : ∀ z ∈ s ∩ U ⁻¹' (chartAt E (U z₀)).source,
      U z ∈ (chartAt E (U z₀)).source := fun _ hz => hz.2
  have hchart : ContDiffAt ℝ ∞ (fun z => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z₀)).continuousLinearMapAt ℝ
      (U z) (diskMapTension g U z)) z₀ :=
    contDiffAt_trivialized_diskMapTension g hs' hU' hz₀' hsrc'
  have hA : ContDiffAt ℝ ∞ (fun z => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z₀)
      ⟨U z, diskMapTension g U z⟩).2) z₀ := by
    refine hchart.congr_of_eventuallyEq ?_
    filter_upwards [hpre] with z hz
    have hb : U z ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z₀)).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hz
    exact (Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hb (diskMapTension g U z)).symm
  exact hA.contDiffWithinAt.contMDiffWithinAt

omit [FiniteDimensional ℝ E] in
theorem diskMapConformalAt_of_ball (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall (0 : ℂ) 1 ⊆ s)
    (hball : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt g U z := by
  have hc (v w : ℂ) : ContinuousOn
      (fun z => g.inner (U z) (diskMapPartial U z v) (diskMapPartial U z w))
      (Metric.closedBall (0 : ℂ) 1) :=
    (contDiffOn_diskMapMetricPairing g hs hU v w).continuousOn.mono hDs
  intro z hz
  refine ⟨?_, ?_⟩
  · refine (Set.EqOn.of_subset_closure (s := Metric.ball (0 : ℂ) 1)
      (t := Metric.closedBall (0 : ℂ) 1)
      (f := fun z => g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I))
      (g := fun _ => (0 : ℝ)) (fun z hz => (hball z hz).1) (hc 1 Complex.I)
      continuousOn_const Metric.ball_subset_closedBall ?_) hz
    rw [closure_ball (0 : ℂ) (by norm_num)]
  · refine (Set.EqOn.of_subset_closure (s := Metric.ball (0 : ℂ) 1)
      (t := Metric.closedBall (0 : ℂ) 1)
      (f := fun z => g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1))
      (g := fun z => g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I))
      (fun z hz => (hball z hz).2) (hc 1 1) (hc Complex.I Complex.I)
      Metric.ball_subset_closedBall ?_) hz
    rw [closure_ball (0 : ℂ) (by norm_num)]

theorem diskMapTension_eq_zero_of_ball (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M}
    {s : Set ℂ} (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall (0 : ℂ) 1 ⊆ s)
    (hball : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U z = 0) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, diskMapTension g U z = 0 := by
  intro z hz
  set p : M := U z with hp
  have hV : IsOpen (s ∩ U ⁻¹' (chartAt E p).source) :=
    hU.continuousOn.isOpen_inter_preimage hs (chartAt E p).open_source
  have hU' : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (s ∩ U ⁻¹' (chartAt E p).source) :=
    hU.mono inter_subset_left
  have hsrc' : ∀ w ∈ s ∩ U ⁻¹' (chartAt E p).source, U w ∈ (chartAt E p).source :=
    fun _ hw => hw.2
  have hzV : z ∈ s ∩ U ⁻¹' (chartAt E p).source :=
    ⟨hDs hz, by rw [hp]; exact mem_chart_source E (U z)⟩
  have hψ : ContDiffOn ℝ ∞ (fun w => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ
      (U w) (diskMapTension g U w)) (s ∩ U ⁻¹' (chartAt E p).source) :=
    contDiffOn_diskMapTension_trivAt g hV hU' hsrc'
  have hEqOn : EqOn (fun w => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ
      (U w) (diskMapTension g U w)) (fun _ => (0 : E))
      (Metric.ball (0 : ℂ) 1 ∩ (s ∩ U ⁻¹' (chartAt E p).source)) := by
    intro w hw
    simp only [hball w hw.1, map_zero]
  have hsub : Metric.closedBall (0 : ℂ) 1 ∩ (s ∩ U ⁻¹' (chartAt E p).source) ⊆
      closure (Metric.ball (0 : ℂ) 1 ∩ (s ∩ U ⁻¹' (chartAt E p).source)) := by
    intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hx.2)
    have hxball : x ∈ closure (Metric.ball (0 : ℂ) 1) := by
      rw [closure_ball (0 : ℂ) (by norm_num)]
      exact hx.1
    rw [Metric.mem_closure_iff] at hxball
    obtain ⟨y, hyb, hxy⟩ := hxball (min ε δ) (lt_min hε hδpos)
    refine ⟨y, ⟨hyb, hδsub ?_⟩, lt_of_lt_of_le hxy (min_le_left ε δ)⟩
    refine Metric.mem_ball.mpr ?_
    rw [dist_comm]
    exact lt_of_lt_of_le hxy (min_le_right ε δ)
  have hmain := hEqOn.of_subset_closure
    (hψ.continuousOn.mono inter_subset_right) continuousOn_const
    (fun x hx => ⟨Metric.ball_subset_closedBall hx.1, hx.2⟩) hsub
  have hzψ : (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ (U z)
      (diskMapTension g U z) = 0 := hmain ⟨hz, hzV⟩
  have hb : U z ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, hp]
    exact mem_chart_source E (U z)
  have hsymm := Trivialization.symmL_continuousLinearMapAt
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p) (R := ℝ) hb (diskMapTension g U z)
  rw [hzψ, map_zero] at hsymm
  exact hsymm.symm

end DifferentialGeometry.Geometry
