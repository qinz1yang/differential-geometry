import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Connection
import DifferentialGeometry.Geometry.Connection.LeviCivita.AlongCurve
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.CorrectionAtBasepoint
import DifferentialGeometry.Geometry.Curvature.Coordinates.ChristoffelContraction
open Bundle Manifold Set
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [hBoundary : I.Boundaryless]
include hBoundary

omit [CompleteSpace E] [SigmaCompactSpace M] hBoundary in
theorem connectionForm_leviCivita_apply_chart
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (X : TangentSpace I x) (v : E) :
    (LeviCivita g).connectionForm (trivializationAt E (TangentSpace I) α) x X v =
      chartChristoffelContraction g α (trivToE (I := I) α x X) v (extChartAt I α x) := by
  let e := trivializationAt E (TangentSpace I) α
  have he : x ∈ e.baseSet := chartLeviCivitaGoodSet_mem_baseSet hx
  let σ := fun y => e.symmL ℝ y v
  have hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% σ) x := by
    rw [e.mdifferentiableAt_section_iff I σ he]
    apply (mdifferentiableAt_const (c := v)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hy]
    exact e.continuousLinearMapAt_symmL hy v
  have hrepr (y : M) (hy : y ∈ e.baseSet) : chartESectionRepr (I := I) α σ y = v := by
    rw [chartE_section_repr_eq_trivToE]
    exact e.continuousLinearMapAt_symmL hy v
  have hconst : (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm) =ᶠ[𝓝 (extChartAt I α x)]
      fun _ => v := by
    filter_upwards [isOpen_interior.mem_nhds
      (chartLeviCivitaGoodSet_extChartAt_mem_interior hx)] with z hz
    apply hrepr
    have h := (extChartAt I α).map_target (interior_subset hz)
    simpa only [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using h
  have hD : fderiv ℝ (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
      (extChartAt I α x) = 0 := by
    rw [hconst.fderiv_eq, fderiv_const_apply]
  rw [CovariantDerivative.connectionForm_apply _ _ he,
    LeviCivita_chart_apply g α hx hσ X, chartLeviCivita_apply g α σ hx X,
    hD, zero_apply, zero_add, hrepr x he]
  change e.continuousLinearMapAt ℝ x (e.symmL ℝ x (christoffelCorrection g α x v X)) = _
  rw [e.continuousLinearMapAt_symmL he, correction_eq_contr]

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem Dt_eq_derivAlongWithin (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M)
    (J : Set ℝ) (V : c.Field (I := I)) (x t : ℝ)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (fun r => c.lift x r) J t)
    (hγc : ContinuousWithinAt (fun r => c.lift x r) J t)
    (hxs : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t) :
    c.Dt g J V x t =
      (LeviCivita (g t)).derivAlongWithin (fun r => c.lift x r) (fun r => V x r) J t := by
  classical
  set γ : ℝ → M := fun r => c.lift x r with hγdef
  set e := trivializationAt E (TangentSpace I) (γ t) with he
  have hgood : γ t ∈ chartLeviCivitaGoodSet (I := I) (γ t) :=
    self_mem_chartLeviCivitaGoodSet (I := I) (γ t)
  have hvel : trivToE (I := I) (γ t) (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
      = derivWithin (chartCurve (I := I) (γ t) γ) J t := by
    change (Trivialization.continuousLinearMapAt ℝ
          (trivializationAt E (TangentSpace I) (γ t)) (γ t))
        ((mfderivWithin 𝓘(ℝ, ℝ) I γ J t : ℝ →L[ℝ] _) (1 : ℝ))
      = (fderivWithin ℝ (fun s : ℝ => extChartAt I (γ t) (γ s)) J t) (1 : ℝ)
    exact Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderivWithin_along_curve_eq_fderivWithin
      (I := I) (γ := γ) (J := J) (t₀ := t) (α := γ t) hγ hγc hxs (mem_chart_source H (γ t))
  have hZ : (fun s : ℝ => e.continuousLinearMapAt ℝ (γ s) (V x s))
      = chartRepAt (I := I) γ (V x) t := rfl
  rw [Dt_eq_symmL_chart (c := c) (g := g) (J := J) (V := V) (x := x) (t := t)]
  simp only [CovariantDerivative.derivAlongWithin]
  rw [hZ, connectionForm_leviCivita_apply_chart (g t) (γ t) hgood
    (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
    (e.continuousLinearMapAt ℝ (γ t) (V x t)), hvel]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem Dx_eq_derivAlongWithin (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M)
    (V : c.Field (I := I)) (x t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u => c.lift u t) x) :
    c.Dx g V x t =
      (LeviCivita (g t)).derivAlongWithin (fun u => c.lift u t) (fun u => V u t) univ x := by
  classical
  rw [show c.Dx g V x t =
      covDerivAlong (I := I) (g t) (fun u => c.lift u t) (fun u => V u t) x from rfl]
  rw [covDerivAlong_def]
  simp only [CovariantDerivative.derivAlongWithin, chartCovDerivAlong_def, derivWithin_univ,
    mfderivWithin_univ]
  congr 1
  rw [connectionForm_leviCivita_apply_chart (g t) (c.lift x t)
      (self_mem_chartLeviCivitaGoodSet (I := I) (c.lift x t))
      (mfderiv 𝓘(ℝ, ℝ) I (fun u => c.lift u t) x ((NormedSpace.fromTangentSpace x).symm 1))
      ((trivializationAt E (TangentSpace I) (c.lift x t)).continuousLinearMapAt ℝ
        (c.lift x t) (V x t))]
  congr 1
  congr 1
  change (fderiv ℝ (fun u : ℝ => extChartAt I (c.lift x t) (c.lift u t)) x) (1 : ℝ)
    = (Trivialization.continuousLinearMapAt ℝ
        (trivializationAt E (TangentSpace I) (c.lift x t)) (c.lift x t))
      ((mfderiv 𝓘(ℝ, ℝ) I (fun u => c.lift u t) x : ℝ →L[ℝ] _) (1 : ℝ))
  exact (Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
    (I := I) hγ (c.lift x t) (mem_chart_source H (c.lift x t))).symm



variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem derivWithin_prod_fst_of_hasFDerivWithinAt
    (F : ℝ × X → Y) (F' : (ℝ × X) →L[ℝ] Y) {J : Set ℝ} {U : Set X}
    {t : ℝ} {y₀ : X} (hy₀ : y₀ ∈ U) (huniq : UniqueDiffWithinAt ℝ J t)
    (hF : HasFDerivWithinAt F F' (J ×ˢ U) (t, y₀)) :
    derivWithin (fun r : ℝ => F (r, y₀)) J t = F' (1, 0) := by
  have hι : HasFDerivWithinAt (fun r : ℝ => (r, y₀))
      (ContinuousLinearMap.inl ℝ ℝ X) J t :=
    (hasFDerivAt_prodMk_left t y₀).hasFDerivWithinAt
  have hmap : MapsTo (fun r : ℝ => (r, y₀)) J (J ×ˢ U) := fun r hr => ⟨hr, hy₀⟩
  have hcomp := hF.comp t hι hmap
  exact (hcomp.hasDerivWithinAt.congr (fun r _ => rfl) rfl).derivWithin huniq

theorem fderiv_prod_snd_of_hasFDerivWithinAt
    (F : ℝ × X → Y) (F' : (ℝ × X) →L[ℝ] Y) {J : Set ℝ} {U : Set X}
    {t : ℝ} {y₀ : X} (ht : t ∈ J) (hU : U ∈ 𝓝 y₀)
    (hF : HasFDerivWithinAt F F' (J ×ˢ U) (t, y₀)) (y' : X) :
    fderiv ℝ (fun y : X => F (t, y)) y₀ y' = F' (0, y') := by
  have hι : HasFDerivAt (fun y : X => (t, y)) (ContinuousLinearMap.inr ℝ ℝ X) y₀ :=
    hasFDerivAt_prodMk_right t y₀
  have hmem : ∀ᶠ y : X in 𝓝 y₀, (t, y) ∈ J ×ˢ U := by
    filter_upwards [hU] with y hy
    exact ⟨ht, hy⟩
  have hcomp := hF.comp_hasFDerivAt y₀ hι hmem
  have h1 : fderiv ℝ (fun y : X => F (t, y)) y₀
      = F'.comp (ContinuousLinearMap.inr ℝ ℝ X) := hcomp.fderiv
  rw [h1]
  rfl

theorem hasDerivWithinAt_prod_curve
    (F : ℝ × X → Y) (F' : (ℝ × X) →L[ℝ] Y) (y : ℝ → X) (y' : X) {J : Set ℝ} {U : Set X}
    {t : ℝ} {y₀ : X} (hy : y t = y₀) (hF : HasFDerivWithinAt F F' (J ×ˢ U) (t, y₀))
    (hy' : HasDerivWithinAt y y' J t) (hmap : ∀ r ∈ J, y r ∈ U) :
    HasDerivWithinAt (fun r : ℝ => F (r, y r)) (F' (1, 0) + F' (0, y')) J t := by
  have hF' : HasFDerivWithinAt F F' (J ×ˢ U) (t, y t) := by rw [hy]; exact hF
  have hid : HasFDerivWithinAt (fun r : ℝ => r) (1 : ℝ →L[ℝ] ℝ) J t :=
    (hasFDerivAt_id t).hasFDerivWithinAt
  have hpair : HasFDerivWithinAt (fun r : ℝ => (r, y r))
      ((1 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.toSpanSingleton ℝ y')) J t :=
    hid.prodMk hy'.hasFDerivWithinAt
  have hmap' : MapsTo (fun r : ℝ => (r, y r)) J (J ×ˢ U) := fun r hr => ⟨hr, hmap r hr⟩
  have hcomp := hF'.comp t hpair hmap'
  have hval : ((F' : (ℝ × X) →L[ℝ] Y) ∘SL
      ((1 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.toSpanSingleton ℝ y'))) (1 : ℝ)
      = F' (1, 0) + F' (0, y') := by
    change F' (((1 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.toSpanSingleton ℝ y')) 1) = _
    have h : ((1 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.toSpanSingleton ℝ y')) 1
        = ((1 : ℝ), y') := by
      simp [ContinuousLinearMap.prod_apply]
    rw [h]
    rw [show ((1 : ℝ), y') = (1, 0) + ((0 : ℝ), y') by simp, map_add]
  have h := hcomp.hasDerivWithinAt.congr (fun r _ => rfl) rfl
  rw [hval] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
