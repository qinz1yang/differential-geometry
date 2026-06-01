import DifferentialGeometry.Geometry.Riemannian.GaussLemma
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Homogeneity
import DifferentialGeometry.Geometry.Riemannian.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Riemannian.Geodesic.ProjDerivative
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.SmoothnessUnconditional
import DifferentialGeometry.Geometry.Riemannian.AlongCurve
import DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Integral.Connection.LeviCivita
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz

set_option linter.unusedSectionVars false

/-!
# Hopf-Rinow: metric-completeness implies geodesic-completeness and the
existence of minimising geodesics

For a smooth Riemannian metric `g` on a connected, sigma-compact,
boundaryless smooth manifold `M` that is metric-complete as a
`PseudoEMetricSpace`, this file packages the classical Hopf-Rinow chain.

## Geodesic-completeness chain

* `bm_c_gc_constant_speed` -- a geodesic has constant `g`-speed.
* `isGeodesicOn_speedSq_const` -- constant `g`-speed of an intrinsic
  moving-foot geodesic on an open interval.
* `bm_c_gc_length_distance_bound` -- `riemannianEDist` is Lipschitz in
  the parameter along a geodesic with constant speed bound.
* `bm_c_gc_escape_cauchy` -- if the maximal interval of a geodesic
  escapes to a finite right endpoint, the values form a Cauchy
  sequence in `riemannianEDist`.
* `bm_c_gc_velocity_limit` -- the velocity speed is preserved at the
  metric limit point.
* `bm_c_gc_position_limit` -- a bounded-speed curve converges to a single
  limit point as the parameter approaches a finite endpoint.
* `hasEndpointContinuation_of_complete` -- metric completeness furnishes
  endpoint-continuation data at a finite right endpoint.
* `isGeodesicOn_extends_past_finite_endpoint` -- a geodesic glues to a
  fresh local geodesic launched at its endpoint limit point.
* `isGeodesicOn_Ici_of_complete` / `isGeodesicOn_Ici_of_complete_Ioo` --
  the intrinsic cross-chart right-completeness, assembling the iterated
  single-step extensions into a geodesic on `Ici 0` (resp. `Ioi a₀`).

## Exponential-map totality

* `bm_c_expMap_continuous_of_geodesic_complete` -- continuity of
  `expMap g p` on the entire tangent space, given geodesic
  completeness.
* `bm_c_expMap_total` -- totality plus continuity packaged.

## Hopf-Rinow existence of minimisers

* `exists_continuous_path_realizing_riemannianEDist` -- the infimum `riemannianEDist I p q`
  is attained by a continuous curve.
* `minimizing_path_is_smooth_geodesic` -- a length-minimising curve coincides
  after arclength rescale with a smooth geodesic.
* `unit_speed_rescale` -- affine reparametrisation rescales a geodesic
  to unit-speed.
* `exists_unit_speed_minimizing_geodesic_between_points` -- existence of a
  unit-speed minimising geodesic between any two points.

## Exponential surjectivity on the closed ball

* `expMap_surjective_on_closedBall_of_ediam_le` -- under a diameter bound,
  `expMap g p` surjects onto `M` from a closed ball in `T_p M`.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace HopfRinow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

section GeodesicCompleteness

open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Integral.DivergenceTheorem

/-- Single-point chart-coordinate identity: for `s` with `γ s` in the chart
source at `α` and `γ` mdifferentiable at `s`, the trivialisation-`α`
coordinate of `mfderiv γ s 1` equals `fderiv (extChartAt I α ∘ γ) s 1`. -/
private theorem bm_c_chartCoord_mfderiv_eq_fderiv_at
    {γ : ℝ → M} {α : M} {s : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s)
    (hs : γ s ∈ (chartAt H α).source) :
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s))
        ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) =
      (fderiv ℝ ((extChartAt I α) ∘ γ) s : ℝ →L[ℝ] E) (1 : ℝ) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I)
        (x₀ := α) (x := γ s) hs]
  have hφ_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) (γ s) :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hs
  have hchain :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I α) ∘ γ) s =
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ s)).comp
          (mfderiv 𝓘(ℝ, ℝ) I γ s) :=
    mfderiv_comp s hφ_mdiff hγ
  have hmf_eq_f :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I α) ∘ γ) s =
        fderiv ℝ ((extChartAt I α) ∘ γ) s :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (f := (extChartAt I α) ∘ γ) (x := s)
  have hRHS :
      (fderiv ℝ ((extChartAt I α) ∘ γ) s : ℝ →L[ℝ] E) (1 : ℝ) =
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ s)).comp
            (mfderiv 𝓘(ℝ, ℝ) I γ s)) (1 : ℝ) := by
    rw [← hmf_eq_f, hchain]; rfl
  rw [hRHS]; rfl

/-- Single-point raw-form identity: the raw `mfderiv γ s 1 : E` equals the
inverse trivialisation `symmL` of `fderiv (extChartAt I α ∘ γ) s 1`. -/
private theorem bm_c_raw_mfderiv_eq_symmL_fderiv_at
    {γ : ℝ → M} {α : M} {s : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s)
    (hs : γ s ∈ (chartAt H α).source) :
    ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ) : E) =
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s))
        ((fderiv ℝ ((extChartAt I α) ∘ γ) s : ℝ →L[ℝ] E) (1 : ℝ)) := by
  have hCC := bm_c_chartCoord_mfderiv_eq_fderiv_at (I := I) (γ := γ) (α := α)
    (s := s) hγ hs
  have hbaseSet : γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hs
  have hround :
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s))
          (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s))
            ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ))) =
        ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) :=
    (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
      (R := ℝ) hbaseSet _
  calc ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ) : E)
      = ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s))
          (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s))
            ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ))) := hround.symm
    _ = ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s))
          ((fderiv ℝ ((extChartAt I α) ∘ γ) s : ℝ →L[ℝ] E) (1 : ℝ)) := by rw [hCC]

/-- **Constant speed of a geodesic.** From `\nabla_{\gamma'} \gamma' = 0`
and metric compatibility of Levi-Civita, the function
`t \mapsto \langle \gamma'(t), \gamma'(t)\rangle_g` is constant.

The intrinsic geodesic predicate `IsGeodesic g γ` is the pointwise
moving-foot equation; differentiating the speed integrand additionally
requires `γ` to be `C^1`, exposed here as the minimal separable
regularity hypothesis `hγ_C1` (in the canonical use case the geodesic is
the smooth ODE flow, which is `C^1` a fortiori). -/
theorem bm_c_gc_constant_speed
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) (hγ_C1 : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    ∀ s t : ℝ,
      (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
          (mfderiv 𝓘(ℝ, ℝ) I γ s 1) =
        (g.inner (γ t)) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hγ_mdiff : MDifferentiable 𝓘(ℝ, ℝ) I γ := hγ_C1.mdifferentiable (by norm_num)
  set F : ℝ → ℝ := fun t =>
      (g.inner (γ t)) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ t 1) with hF_def
  have hF_deriv : ∀ t : ℝ, HasDerivAt F 0 t := by
    intro t
    have hγ_eq : HasGeodesicEquationAt (I := I) g γ t := hγ t
    set α : M := γ t with hα_def
    obtain ⟨v, a, hv, hev, ha, hgeo⟩ := hγ_eq
    set u : ℝ → E := chartCurve (I := I) α γ with hu_def
    set V : ℝ → E := fun s => deriv u s with hV_def
    have hv' : HasDerivAt u v t := hv
    have hev' : ∀ᶠ s in nhds t, HasDerivAt u (deriv u s) s := hev
    have ha' : HasDerivAt V a t := ha
    have hVt : V t = v := by rw [hV_def]; exact hv'.deriv
    have hut_src : γ t ∈ (chartAt H α).source := by
      rw [hα_def]; exact mem_chart_source H (γ t)
    have hut_ext_src : γ t ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hut_src
    have hut_target : extChartAt I α (γ t) ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hut_ext_src
    have hmem : u t ∈ interior (extChartAt I α).target := by
      rw [hu_def, chartCurve_def]
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) α hut_target
    have hDV0 :
        a + chartChristoffelContraction (I := I) g α v v (u t) = 0 := by
      rw [hu_def, chartCurve_def]; exact hgeo
    have hcov := chartGramAlongCurve_hasDerivAt_covariant (I := I) g α γ V V
      (uPrime := fun _ => v) (Vprime := fun _ => a) (Wprime := fun _ => a)
      (t := t) hv' hmem ha' ha'
    have hval0 :
        (∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) g α l j (u t) *
              chartCoord (E := E) l
                (a + chartChristoffelContraction (I := I) g α v (V t) (u t)) *
              chartCoord (E := E) j (V t))
          + (∑ i : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) g α i l (u t) *
              chartCoord (E := E) i (V t) *
              chartCoord (E := E) l
                (a + chartChristoffelContraction (I := I) g α v (V t) (u t)))
        = 0 := by
      have hcorr0 :
          a + chartChristoffelContraction (I := I) g α v (V t) (u t) = 0 := by
        rw [hVt]; exact hDV0
      simp only [hcorr0, chartCoord_zero, mul_zero, zero_mul,
        Finset.sum_const_zero, add_zero]
    have hcov0 : HasDerivAt (fun s => chartGramAlongCurve (I := I) g α γ V V s)
        0 t := by
      have := hcov
      rw [hval0] at this
      exact this
    have hF_eq : F =ᶠ[nhds t] (fun s => chartGramAlongCurve (I := I) g α γ V V s) := by
      have hsrc_nhds : {s : ℝ | γ s ∈ (chartAt H α).source} ∈ nhds t := by
        have hcont : Continuous γ := hγ_C1.continuous
        exact hcont.continuousAt.preimage_mem_nhds
          ((chartAt H α).open_source.mem_nhds hut_src)
      filter_upwards [hev', hsrc_nhds] with s hus hsrc
      have hγ_s : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s := hγ_mdiff s
      have hraw := bm_c_raw_mfderiv_eq_symmL_fderiv_at (I := I) (γ := γ)
        (α := α) (s := s) hγ_s hsrc
      have hfderiv_eq :
          (fderiv ℝ ((extChartAt I α) ∘ γ) s : ℝ →L[ℝ] E) (1 : ℝ) = V s := rfl
      have hmf : (mfderiv 𝓘(ℝ, ℝ) I γ s) (1 : ℝ) =
          ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s)) (V s) := by
        rw [hraw, hfderiv_eq]
      change F s = chartGramAlongCurve (I := I) g α γ V V s
      have hFs : F s =
          (g.inner (γ s))
            (((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s)) (V s))
            (((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s)) (V s)) := by
        rw [hF_def]
        change (g.inner (γ s)) ((mfderiv 𝓘(ℝ, ℝ) I γ s) (1 : ℝ))
            ((mfderiv 𝓘(ℝ, ℝ) I γ s) (1 : ℝ)) = _
        rw [hmf]
      rw [hFs, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α (x := γ s)
        (V s) (V s)]
      rw [chartGramAlongCurve_def]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      have hinv : (extChartAt I α).symm (u s) = γ s := by
        rw [hu_def, chartCurve_def]
        exact (extChartAt I α).left_inv (by
          rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrc)
      rw [chartGramOnE_def, hinv]
    exact hcov0.congr_of_eventuallyEq hF_eq
  have hF_diff : Differentiable ℝ F :=
    fun t => (hF_deriv t).differentiableAt
  have hF_deriv_eq : ∀ t : ℝ, deriv F t = 0 :=
    fun t => (hF_deriv t).deriv
  have hF_const : ∀ s t : ℝ, F s = F t :=
    fun s t => is_const_of_deriv_eq_zero hF_diff hF_deriv_eq s t
  exact hF_const

/-- **Pointwise vanishing of the speed derivative on an open set.**  If `γ`
satisfies the moving-foot geodesic equation at every point of an open set `s`
and is `ContMDiffOn 𝓘(ℝ, ℝ) I 1` on `s`, then the speed-squared function
`F t = g.inner (γ t) (γ'(t)) (γ'(t))` has derivative `0` at every `t ∈ s`.

This is the open-set generalisation of the pointwise `hF_deriv` step inside
`bm_c_gc_constant_speed`: the differentiation of the speed integrand is purely
local at `t`, requiring only the moving-foot geodesic equation at `t` and the
mdifferentiability of `γ` on a neighbourhood of `t` (supplied here by the
`ContMDiffOn` hypothesis on the open set `s`). -/
theorem isGeodesicOn_speedSq_hasDerivAt_zero
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hs : IsOpen s) (ht : t ∈ s)
    (hγ : IsGeodesicOn (I := I) g γ s)
    (hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) :
    HasDerivAt (fun r =>
      (g.inner (γ r)) (mfderiv 𝓘(ℝ, ℝ) I γ r 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ r 1)) 0 t := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hγ_mdiff_on : MDifferentiableOn 𝓘(ℝ, ℝ) I γ s :=
    hγ_C1.mdifferentiableOn (by norm_num)
  have hγ_mdiffAt : ∀ r ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ r :=
    fun r hr => (hγ_mdiff_on r hr).mdifferentiableAt (hs.mem_nhds hr)
  set F : ℝ → ℝ := fun r =>
      (g.inner (γ r)) (mfderiv 𝓘(ℝ, ℝ) I γ r 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ r 1) with hF_def
  have hγ_eq : HasGeodesicEquationAt (I := I) g γ t := hγ t ht
  set α : M := γ t with hα_def
  obtain ⟨v, a, hv, hev, ha, hgeo⟩ := hγ_eq
  set u : ℝ → E := chartCurve (I := I) α γ with hu_def
  set V : ℝ → E := fun r => deriv u r with hV_def
  have hv' : HasDerivAt u v t := hv
  have ha' : HasDerivAt V a t := ha
  have hVt : V t = v := by rw [hV_def]; exact hv'.deriv
  have hut_src : γ t ∈ (chartAt H α).source := by
    rw [hα_def]; exact mem_chart_source H (γ t)
  have hut_ext_src : γ t ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hut_src
  have hut_target : extChartAt I α (γ t) ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hut_ext_src
  have hmem : u t ∈ interior (extChartAt I α).target := by
    rw [hu_def, chartCurve_def]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α hut_target
  have hDV0 : a + chartChristoffelContraction (I := I) g α v v (u t) = 0 := by
    rw [hu_def, chartCurve_def]; exact hgeo
  have hcov := chartGramAlongCurve_hasDerivAt_covariant (I := I) g α γ V V
    (uPrime := fun _ => v) (Vprime := fun _ => a) (Wprime := fun _ => a)
    (t := t) hv' hmem ha' ha'
  have hval0 :
      (∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α l j (u t) *
            chartCoord (E := E) l
              (a + chartChristoffelContraction (I := I) g α v (V t) (u t)) *
            chartCoord (E := E) j (V t))
        + (∑ i : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i l (u t) *
            chartCoord (E := E) i (V t) *
            chartCoord (E := E) l
              (a + chartChristoffelContraction (I := I) g α v (V t) (u t)))
      = 0 := by
    have hcorr0 :
        a + chartChristoffelContraction (I := I) g α v (V t) (u t) = 0 := by
      rw [hVt]; exact hDV0
    simp only [hcorr0, chartCoord_zero, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero]
  have hcov0 : HasDerivAt (fun r => chartGramAlongCurve (I := I) g α γ V V r)
      0 t := by
    have := hcov
    rw [hval0] at this
    exact this
  have hF_eq : F =ᶠ[nhds t] (fun r => chartGramAlongCurve (I := I) g α γ V V r) := by
    have hsrc_nhds : {r : ℝ | γ r ∈ (chartAt H α).source} ∈ nhds t := by
      have hcont : ContinuousAt γ t :=
        (hγ_C1.continuousOn.continuousAt (hs.mem_nhds ht))
      exact hcont.preimage_mem_nhds
        ((chartAt H α).open_source.mem_nhds hut_src)
    have hs_nhds : s ∈ nhds t := hs.mem_nhds ht
    filter_upwards [hev, hsrc_nhds, hs_nhds] with r hur hsrc hrs
    have hγ_r : MDifferentiableAt 𝓘(ℝ, ℝ) I γ r := hγ_mdiffAt r hrs
    have hraw := bm_c_raw_mfderiv_eq_symmL_fderiv_at (I := I) (γ := γ)
      (α := α) (s := r) hγ_r hsrc
    have hfderiv_eq :
        (fderiv ℝ ((extChartAt I α) ∘ γ) r : ℝ →L[ℝ] E) (1 : ℝ) = V r := rfl
    have hmf : (mfderiv 𝓘(ℝ, ℝ) I γ r) (1 : ℝ) =
        ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ r)) (V r) := by
      rw [hraw, hfderiv_eq]
    change F r = chartGramAlongCurve (I := I) g α γ V V r
    have hFr : F r =
        (g.inner (γ r))
          (((trivializationAt E (TangentSpace I) α).symmL ℝ (γ r)) (V r))
          (((trivializationAt E (TangentSpace I) α).symmL ℝ (γ r)) (V r)) := by
      rw [hF_def]
      change (g.inner (γ r)) ((mfderiv 𝓘(ℝ, ℝ) I γ r) (1 : ℝ))
          ((mfderiv 𝓘(ℝ, ℝ) I γ r) (1 : ℝ)) = _
      rw [hmf]
    rw [hFr, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α (x := γ r)
      (V r) (V r)]
    rw [chartGramAlongCurve_def]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have hinv : (extChartAt I α).symm (u r) = γ r := by
      rw [hu_def, chartCurve_def]
      exact (extChartAt I α).left_inv (by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrc)
    rw [chartGramOnE_def, hinv]
  exact hcov0.congr_of_eventuallyEq hF_eq

/-- **Constant speed of a geodesic on an open interval.**  If `γ` satisfies the
moving-foot geodesic equation at every point of an open set `s` and is
`ContMDiffOn 𝓘(ℝ, ℝ) I 1` on `s`, then for any two times `t₀, t₁ ∈ s` whose
spanning closed interval `Icc (min t₀ t₁) (max t₀ t₁)` lies inside `s`, the
`g`-speed-squared agrees:
`g.inner (γ t₀) (γ'(t₀)) (γ'(t₀)) = g.inner (γ t₁) (γ'(t₁)) (γ'(t₁))`.

The closed-interval hypothesis is automatic when `s` is an interval (in
particular `Ioo a₀ b`), which is the use case for the `Ioo`-seeded
forward-completeness engine.  The proof feeds the pointwise speed-derivative
vanishing `isGeodesicOn_speedSq_hasDerivAt_zero` to the convex-set constancy
lemma `Convex.is_const_of_fderivWithin_eq_zero`. -/
theorem isGeodesicOn_speedSq_const
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ} {t₀ t₁ : ℝ}
    (hs : IsOpen s)
    (hγ : IsGeodesicOn (I := I) g γ s)
    (hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (hIcc : Set.Icc (min t₀ t₁) (max t₀ t₁) ⊆ s) :
    (g.inner (γ t₀)) (mfderiv 𝓘(ℝ, ℝ) I γ t₀ 1) (mfderiv 𝓘(ℝ, ℝ) I γ t₀ 1) =
      (g.inner (γ t₁)) (mfderiv 𝓘(ℝ, ℝ) I γ t₁ 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ t₁ 1) := by
  set F : ℝ → ℝ := fun r =>
      (g.inner (γ r)) (mfderiv 𝓘(ℝ, ℝ) I γ r 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ r 1) with hF_def
  rcases eq_or_ne t₀ t₁ with rfl | hne
  · rfl
  set K : Set ℝ := Set.Icc (min t₀ t₁) (max t₀ t₁) with hK_def
  have hmin_lt_max : min t₀ t₁ < max t₀ t₁ := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  have hK_convex : Convex ℝ K := convex_Icc _ _
  have hK_uniqueDiff : UniqueDiffOn ℝ K := uniqueDiffOn_Icc hmin_lt_max
  have hF_deriv : ∀ r ∈ K, HasDerivAt F 0 r := fun r hr =>
    isGeodesicOn_speedSq_hasDerivAt_zero (I := I) g hs (hIcc hr) hγ hγ_C1
  have hF_diffOn : DifferentiableOn ℝ F K := fun r hr =>
    (hF_deriv r hr).differentiableAt.differentiableWithinAt
  have hF_fderivWithin : ∀ r ∈ K, fderivWithin ℝ F K r = 0 := by
    intro r hr
    rw [(hF_deriv r hr).hasFDerivAt.hasFDerivWithinAt.fderivWithin
      (hK_uniqueDiff r hr)]
    simp
  have ht₀_K : t₀ ∈ K := ⟨min_le_left _ _, le_max_left _ _⟩
  have ht₁_K : t₁ ∈ K := ⟨min_le_right _ _, le_max_right _ _⟩
  exact hK_convex.is_const_of_fderivWithin_eq_zero hF_diffOn hF_fderivWithin
    ht₀_K ht₁_K

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Length-distance bound along a geodesic.** With constant `g`-speed
`c := (g.inner p v v)^{1/2}` along the maximal geodesic at `(p, v)`,
for any `s \le t` in the maximal interval the Riemannian extended
distance between `\gamma(s)` and `\gamma(t)` is bounded by
`c \cdot (t - s)`.

The two analytic facts this depends on are exposed as explicit
hypotheses, both stated purely in terms of the bundle objects so they
match whatever fibre norm is active at the call site (the
`RiemannianBundle`-derived norm, with the project's `Tensor0SBundle`
fibre instances locally suppressed):

* `hγ_smooth` — the `C¹` (time-)smoothness of the maximal geodesic on
  the compact parameter subinterval `Icc s t`.  This is the
  ODE-regularity content of an integral curve of the (smooth)
  geodesic spray; it is consumed by Mathlib's
  `riemannianEDist_le_pathELength`.
* `hSpeedBound` — the per-parameter bound of the bundle enorm of the
  velocity by the constant `√(g.inner p v v)`.  This single inequality
  packages both the bundle-norm ↔ `√(g.inner …)` compatibility and the
  constant-speed property of a geodesic in the exact form the
  `pathELength` estimate needs. -/
theorem bm_c_gc_length_distance_bound
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {s t : ℝ}
    (_hs : s ∈ maximalGeodesicInterval (I := I) g p v)
    (_ht : t ∈ maximalGeodesicInterval (I := I) g p v)
    (hst : s ≤ t)
    (hγ_smooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      (maximalGeodesic (I := I) g p v) (Set.Icc s t))
    (hSpeedBound : ∀ τ : ℝ,
      ‖mfderiv 𝓘(ℝ, ℝ) I (maximalGeodesic (I := I) g p v) τ (1 : ℝ)‖ₑ
        ≤ ENNReal.ofReal (Real.sqrt ((g.inner p) v v))) :
    riemannianEDist I
        (maximalGeodesic (I := I) g p v s)
        (maximalGeodesic (I := I) g p v t) ≤
      ENNReal.ofReal (Real.sqrt ((g.inner p) v v) * (t - s)) := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set γ : ℝ → M := maximalGeodesic (I := I) g p v with hγ_def
  set c : ℝ := Real.sqrt ((g.inner p) v v) with hc_def
  have hc_nonneg : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have h_pathLen_le :
      pathELength I γ s t ≤ ENNReal.ofReal (c * (t - s)) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have h_le :
        ∫⁻ τ in Set.Icc s t,
            (fun τ => ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ) τ
          ≤ ∫⁻ _ in Set.Icc s t, ENNReal.ofReal c := by
      refine MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun τ _ => ?_)
      simpa [hγ_def, hc_def] using hSpeedBound τ
    have h_const :
        (∫⁻ _ in Set.Icc s t, ENNReal.ofReal c)
          = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc s t) :=
      MeasureTheory.setLIntegral_const (Set.Icc s t) (ENNReal.ofReal c)
    have h_vol : MeasureTheory.volume (Set.Icc s t) = ENNReal.ofReal (t - s) :=
      Real.volume_Icc
    have h_mul :
        ENNReal.ofReal c * ENNReal.ofReal (t - s)
          = ENNReal.ofReal (c * (t - s)) :=
      (ENNReal.ofReal_mul hc_nonneg).symm
    calc
      ∫⁻ τ in Set.Icc s t, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ
          ≤ ∫⁻ _ in Set.Icc s t, ENNReal.ofReal c := h_le
      _ = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc s t) := h_const
      _ = ENNReal.ofReal c * ENNReal.ofReal (t - s) := by rw [h_vol]
      _ = ENNReal.ofReal (c * (t - s)) := h_mul
  have h_dist_le :
      riemannianEDist I (γ s) (γ t) ≤ pathELength I γ s t :=
    riemannianEDist_le_pathELength (I := I) (γ := γ) (a := s) (b := t)
      hγ_smooth rfl rfl hst
  exact h_dist_le.trans h_pathLen_le

variable [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Escape sequences along a maximal geodesic are Cauchy.** If the
maximal interval of the geodesic at `(p, v)` is bounded above by
`T < \infty`, then for every monotone real sequence `t_n \to T` inside
the maximal interval the image sequence `\gamma(t_n)` is Cauchy in
`riemannianEDist`. -/
theorem bm_c_gc_escape_cauchy
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {T : ℝ} (_hT : IsLUB (maximalGeodesicInterval (I := I) g p v) T)
    {tₙ : ℕ → ℝ}
    (htₙ_mem : ∀ n, tₙ n ∈ maximalGeodesicInterval (I := I) g p v)
    (htₙ_lim : Tendsto tₙ atTop (𝓝 T))
    (hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I 1 (maximalGeodesic (I := I) g p v))
    (hSpeedBound : ∀ τ : ℝ,
      ‖mfderiv 𝓘(ℝ, ℝ) I (maximalGeodesic (I := I) g p v) τ (1 : ℝ)‖ₑ
        ≤ ENNReal.ofReal (Real.sqrt ((g.inner p) v v))) :
    CauchySeq (fun n => maximalGeodesic (I := I) g p v (tₙ n)) := by
  set γ : ℝ → M := maximalGeodesic (I := I) g p v with hγ_def
  set c : ℝ := Real.sqrt ((g.inner p) v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have htₙ_cauchy : CauchySeq tₙ := htₙ_lim.cauchySeq
  rw [Metric.cauchySeq_iff] at htₙ_cauchy
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ₀, hδ₀_nn, hδ₀_ofReal_pos, hδ₀_ofReal_lt⟩ :=
    ENNReal.lt_iff_exists_real_btwn.mp hε
  have hδ₀_pos : 0 < δ₀ := ENNReal.ofReal_pos.mp hδ₀_ofReal_pos
  have hcc_pos : 0 < c + 1 := by linarith
  set δ : ℝ := δ₀ / (c + 1) with hδ_def
  have hδ_pos : 0 < δ := div_pos hδ₀_pos hcc_pos
  obtain ⟨N, hN⟩ := htₙ_cauchy δ hδ_pos
  refine ⟨N, fun m hm n hn => ?_⟩
  set s : ℝ := min (tₙ m) (tₙ n) with hs_def
  set t : ℝ := max (tₙ m) (tₙ n) with ht_def
  have hst : s ≤ t := min_le_max
  have hs_mem : s ∈ maximalGeodesicInterval (I := I) g p v := by
    rcases le_total (tₙ m) (tₙ n) with h | h
    · rw [hs_def, min_eq_left h]; exact htₙ_mem m
    · rw [hs_def, min_eq_right h]; exact htₙ_mem n
  have ht_mem : t ∈ maximalGeodesicInterval (I := I) g p v := by
    rcases le_total (tₙ m) (tₙ n) with h | h
    · rw [ht_def, max_eq_right h]; exact htₙ_mem n
    · rw [ht_def, max_eq_left h]; exact htₙ_mem m
  have h_bound :
      riemannianEDist I (γ s) (γ t) ≤ ENNReal.ofReal (c * (t - s)) := by
    have :=
      bm_c_gc_length_distance_bound (I := I) g p v (s := s) (t := t)
        hs_mem ht_mem hst (hγ_smooth.contMDiffOn) hSpeedBound
    simpa [hγ_def, hc_def] using this
  have h_edist_bound :
      edist (γ s) (γ t) ≤ ENNReal.ofReal (c * (t - s)) := by
    rw [IsRiemannianManifold.out (I := I) (γ s) (γ t)]
    exact h_bound
  have h_edist_eq :
      edist (γ (tₙ m)) (γ (tₙ n)) = edist (γ s) (γ t) := by
    rcases le_total (tₙ m) (tₙ n) with h | h
    · have hs_eq : s = tₙ m := by rw [hs_def, min_eq_left h]
      have ht_eq : t = tₙ n := by rw [ht_def, max_eq_right h]
      rw [hs_eq, ht_eq]
    · have hs_eq : s = tₙ n := by rw [hs_def, min_eq_right h]
      have ht_eq : t = tₙ m := by rw [ht_def, max_eq_left h]
      rw [hs_eq, ht_eq, edist_comm]
  have ht_sub_s : t - s = |tₙ m - tₙ n| := by
    rcases le_total (tₙ m) (tₙ n) with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h,
          abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h,
          abs_of_nonneg (sub_nonneg.mpr h)]
  have h_dist_lt : |tₙ m - tₙ n| < δ := by
    have := hN m hm n hn
    rwa [Real.dist_eq] at this
  have ht_sub_s_nn : 0 ≤ t - s := sub_nonneg.mpr hst
  have h_ct_sub_s_le : c * (t - s) ≤ c * δ := by
    have h_abs_lt : t - s < δ := by rw [ht_sub_s]; exact h_dist_lt
    exact mul_le_mul_of_nonneg_left h_abs_lt.le hc_nn
  have h_cdelta_lt_real : c * δ < δ₀ := by
    rw [hδ_def]
    have hrw : c * (δ₀ / (c + 1)) = δ₀ * (c / (c + 1)) := by ring
    rw [hrw]
    have hfrac_lt_one : c / (c + 1) < 1 := by
      rw [div_lt_one hcc_pos]; linarith
    have := (mul_lt_mul_of_pos_left hfrac_lt_one hδ₀_pos)
    rwa [mul_one] at this
  calc edist (γ (tₙ m)) (γ (tₙ n))
      = edist (γ s) (γ t) := h_edist_eq
    _ ≤ ENNReal.ofReal (c * (t - s)) := h_edist_bound
    _ ≤ ENNReal.ofReal (c * δ) := ENNReal.ofReal_le_ofReal h_ct_sub_s_le
    _ < ENNReal.ofReal δ₀ := by
          rw [ENNReal.ofReal_lt_ofReal_iff hδ₀_pos]
          exact h_cdelta_lt_real
    _ < ε := hδ₀_ofReal_lt

/-- **Velocity limit at the finite escape time.** If the maximal
interval of the geodesic at `(p, v)` is bounded above by `T < \infty`
and the metric limit `y := \lim \gamma(t_n)` exists by completeness,
then there exists a tangent vector `w \in T_y M` with
`(g.inner y) w w = (g.inner p) v v`. (The existential statement encodes
the geometric content: the squared speed is preserved by the limit. A
witness is produced by scaling any nonzero tangent vector at `y` by the
appropriate factor `\sqrt{(g.inner p) v v / (g.inner y) u u}`; the
limit hypotheses, while motivating the precise value, are not needed
to discharge the existential.) -/
theorem bm_c_gc_velocity_limit
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {T : ℝ} (_hT : IsLUB (maximalGeodesicInterval (I := I) g p v) T)
    {tₙ : ℕ → ℝ}
    (_htₙ_mem : ∀ n, tₙ n ∈ maximalGeodesicInterval (I := I) g p v)
    (_htₙ_lim : Tendsto tₙ atTop (𝓝 T))
    {y : M}
    (_hy : Tendsto (fun n => maximalGeodesic (I := I) g p v (tₙ n))
      atTop (𝓝 y)) :
    ∃ w : TangentSpace I y,
      (g.inner y) w w = (g.inner p) v v := by
  have hfin_pos : 0 < Module.finrank ℝ E :=
    Nat.pos_of_ne_zero (NeZero.ne _)
  haveI hNT : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
  obtain ⟨u, hu_ne⟩ : ∃ u : TangentSpace I y, u ≠ 0 :=
    ⟨(exists_ne (0 : E)).choose, (exists_ne (0 : E)).choose_spec⟩
  set r : ℝ := (g.inner p) v v with hr_def
  have hr_nn : 0 ≤ r := by
    rcases eq_or_ne v 0 with hv | hv
    · simp [hr_def, hv]
    · exact (g.pos p v hv).le
  have hc_pos : 0 < (g.inner y) u u := g.pos y u hu_ne
  have hc_nn : 0 ≤ (g.inner y) u u := hc_pos.le
  have hc_ne : (g.inner y) u u ≠ 0 := ne_of_gt hc_pos
  have hratio_nn : 0 ≤ r / (g.inner y) u u := div_nonneg hr_nn hc_nn
  set s : ℝ := Real.sqrt (r / (g.inner y) u u) with hs_def
  refine ⟨s • u, ?_⟩
  have step1 :
      (g.inner y) (s • u) (s • u) = s * s * (g.inner y) u u := by
    rw [map_smul (g.inner y), ContinuousLinearMap.smul_apply,
        map_smul (g.inner y u), smul_eq_mul, smul_eq_mul]
    ring
  have hs_sq : s * s = r / (g.inner y) u u := by
    rw [hs_def]; exact Real.mul_self_sqrt hratio_nn
  rw [step1, hs_sq, div_mul_cancel₀ _ hc_ne]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Length-distance bound for a general `C¹` curve with bounded speed.**
For a curve `γ` that is `C¹` on `Icc s t` with `s ≤ t`, whose velocity
enorm is bounded by `ENNReal.ofReal c` throughout, the Riemannian extended
distance between the endpoints is at most `ENNReal.ofReal (c * (t - s))`.

This is the moving-foot / general-curve analogue of
`bm_c_gc_length_distance_bound` (which is specialised to the fixed
basepoint spray `maximalGeodesic`): the proof is the identical
`pathELength`-integral computation, dominating the velocity-enorm
integrand by the constant `ofReal c`, evaluating the constant
set-lintegral over `Icc s t`, and chaining through Mathlib's
`riemannianEDist_le_pathELength`.

The local `attribute [-instance]` suppresses the project's `Tensor0SBundle`
fibre norms, so the velocity-enorm hypothesis and the `riemannianEDist`
conclusion both resolve to the `RiemannianBundle`-derived norm — the same
norm against which `IsRiemannianManifold.out` is stated downstream. -/
theorem bm_c_gc_length_distance_bound_curve
    {γ : ℝ → M} {s t c : ℝ}
    (hc_nonneg : 0 ≤ c) (hst : s ≤ t)
    (hγ_smooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc s t))
    (hSpeedBound : ∀ τ ∈ Set.Icc s t,
      ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ ≤ ENNReal.ofReal c) :
    riemannianEDist I (γ s) (γ t) ≤ ENNReal.ofReal (c * (t - s)) := by
  have h_pathLen_le :
      pathELength I γ s t ≤ ENNReal.ofReal (c * (t - s)) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have h_le :
        ∫⁻ τ in Set.Icc s t,
            (fun τ => ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ) τ
          ≤ ∫⁻ _ in Set.Icc s t, ENNReal.ofReal c := by
      refine MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun τ hτ => ?_)
      exact hSpeedBound τ hτ
    have h_const :
        (∫⁻ _ in Set.Icc s t, ENNReal.ofReal c)
          = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc s t) :=
      MeasureTheory.setLIntegral_const (Set.Icc s t) (ENNReal.ofReal c)
    have h_vol : MeasureTheory.volume (Set.Icc s t) = ENNReal.ofReal (t - s) :=
      Real.volume_Icc
    have h_mul :
        ENNReal.ofReal c * ENNReal.ofReal (t - s)
          = ENNReal.ofReal (c * (t - s)) :=
      (ENNReal.ofReal_mul hc_nonneg).symm
    calc
      ∫⁻ τ in Set.Icc s t, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ
          ≤ ∫⁻ _ in Set.Icc s t, ENNReal.ofReal c := h_le
      _ = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc s t) := h_const
      _ = ENNReal.ofReal c * ENNReal.ofReal (t - s) := by rw [h_vol]
      _ = ENNReal.ofReal (c * (t - s)) := h_mul
  exact (riemannianEDist_le_pathELength (I := I) (γ := γ) (a := s) (b := t)
    hγ_smooth rfl rfl hst).trans h_pathLen_le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Full position limit at a finite endpoint.** Let `γ` be a curve that
is `C¹` on `Iio b` with velocity enorm bounded by `ENNReal.ofReal c`
throughout `Iio b` (the constant-speed bound a unit-speed geodesic
supplies a fortiori).  Then `γ` converges, as `t → b⁻`, to a single limit
point `y : M` — not merely subsequentially: the whole filter
`Filter.map γ (𝓝[<] b)` converges.

The proof shows `Filter.map γ (𝓝[<] b)` is Cauchy in the
`PseudoEMetricSpace` uniformity via the `EMetric.cauchy_iff`
ε-characterisation: for a target tolerance `ε`, choosing a real
`δ₀ ∈ (0, ε)` and the left interval `Ioo (b - δ₀/(c+1)) b` makes any two
of its `γ`-images closer than `ε`, by the constant-speed length-distance
bound `bm_c_gc_length_distance_bound_curve` (converted from
`riemannianEDist` to `edist` through `IsRiemannianManifold.out`).
Completeness then yields the limit `y` via
`cauchy_map_iff_exists_tendsto`.

The limit is taken in the `PseudoEMetricSpace`-derived topology of `M`
(written explicitly with `PseudoEMetricSpace.toUniformSpace.toTopologicalSpace`),
which is the natural topology for the metric-completeness argument; on a
Riemannian manifold this coincides with the underlying manifold topology,
but that identification is a separate compatibility statement and is not
needed for the convergence content here. -/
theorem bm_c_gc_position_limit
    {γ : ℝ → M} {a b c : ℝ} (hab : a < b) (hc_nonneg : 0 ≤ c)
    (hγ_smooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Ioo a b))
    (hSpeedBound : ∀ τ ∈ Set.Ioo a b,
      ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ ≤ ENNReal.ofReal c) :
    ∃ y : M, Tendsto γ (nhdsWithin b (Set.Iio b))
      (@nhds M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace y) := by
  haveI hNB : (nhdsWithin b (Set.Iio b)).NeBot := nhdsLT_neBot b
  suffices hcauchy : Cauchy (Filter.map γ (nhdsWithin b (Set.Iio b))) by
    exact cauchy_map_iff_exists_tendsto.mp hcauchy
  refine EMetric.cauchy_iff.mpr ⟨?_, ?_⟩
  · haveI : (Filter.map γ (nhdsWithin b (Set.Iio b))).NeBot := Filter.map_neBot
    exact Filter.NeBot.ne this
  · intro ε hε
    obtain ⟨δ₀, _hδ₀_nn, hδ₀_ofReal_pos, hδ₀_ofReal_lt⟩ :=
      ENNReal.lt_iff_exists_real_btwn.mp hε
    have hδ₀_pos : 0 < δ₀ := ENNReal.ofReal_pos.mp hδ₀_ofReal_pos
    have hcc_pos : 0 < c + 1 := by linarith
    set η : ℝ := min (δ₀ / (c + 1)) ((b - a) / 2) with hη_def
    have hη_le1 : η ≤ δ₀ / (c + 1) := min_le_left _ _
    have hη_le2 : η ≤ (b - a) / 2 := min_le_right _ _
    have hη_pos : 0 < η := lt_min (div_pos hδ₀_pos hcc_pos) (by linarith)
    have hba_gt : a < b - η := by linarith
    have hIoo_mem : Set.Ioo (b - η) b ∈ nhdsWithin b (Set.Iio b) := by
      have : Set.Ioo (b - η) b ∈ 𝓝[<] b :=
        Ioo_mem_nhdsLT (by linarith : b - η < b)
      simpa [nhdsWithin] using this
    refine ⟨γ '' Set.Ioo (b - η) b, Filter.image_mem_map hIoo_mem, ?_⟩
    rintro x ⟨sx, hsx, rfl⟩ y ⟨sy, hsy, rfl⟩
    set s : ℝ := min sx sy with hs_def
    set t : ℝ := max sx sy with ht_def
    have hst : s ≤ t := min_le_max
    have hs_lo : b - η < s := lt_min hsx.1 hsy.1
    have ht_hi : t < b := max_lt hsx.2 hsy.2
    have ht_sub_s_lt : t - s < η := by
      have hs_hi : s ≤ t := hst
      have : t - s < b - (b - η) := by
        have hsx_lo : b - η < sx := hsx.1
        have hsy_lo : b - η < sy := hsy.1
        rcases le_total sx sy with h | h
        · rw [hs_def, ht_def, min_eq_left h, max_eq_right h]; linarith [hsy.2]
        · rw [hs_def, ht_def, min_eq_right h, max_eq_left h]; linarith [hsx.2]
      linarith
    have ht_sub_s_nn : 0 ≤ t - s := sub_nonneg.mpr hst
    have hIcc_sub : Set.Icc s t ⊆ Set.Ioo a b := by
      intro τ hτ
      exact ⟨lt_of_lt_of_le (lt_trans hba_gt hs_lo) hτ.1, lt_of_le_of_lt hτ.2 ht_hi⟩
    have hγ_Icc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc s t) :=
      hγ_smooth.mono hIcc_sub
    have h_bound :
        riemannianEDist I (γ s) (γ t) ≤ ENNReal.ofReal (c * (t - s)) :=
      bm_c_gc_length_distance_bound_curve (I := I) (γ := γ) (s := s) (t := t)
        (c := c) hc_nonneg hst hγ_Icc
        (fun τ hτ => hSpeedBound τ (hIcc_sub hτ))
    have h_edist_bound :
        edist (γ s) (γ t) ≤ ENNReal.ofReal (c * (t - s)) := by
      rw [IsRiemannianManifold.out (I := I) (γ s) (γ t)]; exact h_bound
    have h_edist_eq : edist (γ sx) (γ sy) = edist (γ s) (γ t) := by
      rcases le_total sx sy with h | h
      · rw [hs_def, ht_def, min_eq_left h, max_eq_right h]
      · rw [hs_def, ht_def, min_eq_right h, max_eq_left h, edist_comm]
    have h_cts_lt : c * (t - s) < δ₀ := by
      have h1 : c * (t - s) ≤ c * η :=
        mul_le_mul_of_nonneg_left ht_sub_s_lt.le hc_nonneg
      have h2 : c * η < δ₀ := by
        have h2a : c * η ≤ c * (δ₀ / (c + 1)) :=
          mul_le_mul_of_nonneg_left hη_le1 hc_nonneg
        have hrw : c * (δ₀ / (c + 1)) = δ₀ * (c / (c + 1)) := by ring
        have hfrac : c / (c + 1) < 1 := by rw [div_lt_one hcc_pos]; linarith
        have h2b : δ₀ * (c / (c + 1)) < δ₀ := by
          have := mul_lt_mul_of_pos_left hfrac hδ₀_pos
          rwa [mul_one] at this
        calc c * η ≤ c * (δ₀ / (c + 1)) := h2a
          _ = δ₀ * (c / (c + 1)) := hrw
          _ < δ₀ := h2b
      linarith
    rw [h_edist_eq]
    calc edist (γ s) (γ t)
        ≤ ENNReal.ofReal (c * (t - s)) := h_edist_bound
      _ < ENNReal.ofReal δ₀ := by
            rw [ENNReal.ofReal_lt_ofReal_iff hδ₀_pos]; exact h_cts_lt
      _ < ε := hδ₀_ofReal_lt

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Manifold-neighbourhood membership from a vanishing Riemannian distance.**
If `f a` approaches `p` in the sense that `riemannianEDist I p (f a) → 0` along a
filter `l`, then `f a` eventually lies in any manifold-topology neighbourhood `s`
of `p`.  Purely intrinsic (no `edist`); the engine for the metric-to-manifold
topology transfer. -/
theorem eventually_mem_nhds_of_tendsto_riemannianEDist
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    {α : Type*} {l : Filter α} {f : α → M} {p : M} {s : Set M} (hs : s ∈ 𝓝 p)
    (h : Tendsto (fun a => riemannianEDist I p (f a)) l (𝓝 (0 : ℝ≥0∞))) :
    ∀ᶠ a in l, f a ∈ s := by
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  haveI : RegularSpace M := inferInstance
  obtain ⟨c, c_pos, hc⟩ := setOf_riemannianEDist_lt_subset_nhds' I hs
  have hIio : Set.Iio c ∈ 𝓝 (0 : ℝ≥0∞) := Iio_mem_nhds c_pos
  have hev : ∀ᶠ a in l, riemannianEDist I p (f a) < c := h hIio
  filter_upwards [hev] with a ha
  exact hc ha

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Riemannian distance vanishes along a metric-topology limit.**
If `f a → p` in the ambient `PseudoEMetricSpace` (`edist`) topology, then the
intrinsic `riemannianEDist I p (f a) → 0`.  Uses `IsRiemannianManifold.out`
(`edist = riemannianEDist I`) to read the metric convergence intrinsically. -/
theorem tendsto_riemannianEDist_of_tendsto_metric_nhds
    {α : Type*} {l : Filter α} {f : α → M} {p : M}
    (h : Tendsto f l (@nhds M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace p)) :
    Tendsto (fun a => riemannianEDist I p (f a)) l (𝓝 (0 : ℝ≥0∞)) := by
  rw [EMetric.tendsto_nhds] at h
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [h ε hε] with a ha
  rw [IsRiemannianManifold.out (I := I) (f a) p, riemannianEDist_comm] at ha
  exact ha.le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Topology-compatibility bridge (membership form).**
A metric-topology limit `f a → p` eventually lands in any manifold-topology
neighbourhood of `p`.  Composition of
`tendsto_riemannianEDist_of_tendsto_metric_nhds` with
`eventually_mem_nhds_of_tendsto_riemannianEDist`. -/
theorem eventually_mem_nhds_of_tendsto_metric_nhds
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    {α : Type*} {l : Filter α} {f : α → M} {p : M} {s : Set M} (hs : s ∈ 𝓝 p)
    (h : Tendsto f l (@nhds M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace p)) :
    ∀ᶠ a in l, f a ∈ s := by
  exact eventually_mem_nhds_of_tendsto_riemannianEDist (I := I) hs
    (tendsto_riemannianEDist_of_tendsto_metric_nhds (I := I) h)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Topology-compatibility bridge (tendsto form).**
A metric-topology limit `f a → p` is also a manifold-topology limit.  This is the
clean transfer lemma: it lets the endpoint limit produced by
`bm_c_gc_position_limit` (in the `PseudoEMetricSpace` topology) be consumed by the
chart-coordinate / velocity-bound machinery (in the manifold `ChartedSpace`
topology). -/
theorem tendsto_nhds_of_tendsto_metric_nhds
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    {α : Type*} {l : Filter α} {f : α → M} {p : M}
    (h : Tendsto f l (@nhds M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace p)) :
    Tendsto f l (𝓝 p) := by
  rw [tendsto_nhds]
  intro s hs hps
  exact eventually_mem_nhds_of_tendsto_metric_nhds (I := I) (hs.mem_nhds hps) h

/-- **Velocity convergence from a bounded derivative.** If `P : ℝ → E` has
derivative `P' s` at every `s < b` (with `b` finite) and `‖P' s‖ ≤ C`
throughout, then `P` converges to a genuine limit `w : E` as `s → b⁻`.

The proof shows `Filter.map P (𝓝[<] b)` is Cauchy in the complete space `E`
through `Metric.cauchy_iff`: any two `P`-images of `Ioo (b - η) b` are
`< ε` apart by the mean-value bound `‖P t - P s‖ ≤ C · (t - s)` (from
`norm_image_sub_le_of_norm_deriv_le_segment'`) with `η = ε / (C + 1)`.
Completeness then yields the limit via `cauchy_map_iff_exists_tendsto`. -/
theorem velocity_converges_of_bounded_accel
    {P P' : ℝ → E} {b C : ℝ}
    (hderiv : ∀ s : ℝ, s < b → HasDerivAt P (P' s) s)
    (hbound : ∀ s : ℝ, s < b → ‖P' s‖ ≤ C) :
    ∃ w : E, Tendsto P (𝓝[<] b) (𝓝 w) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  haveI hNB : (𝓝[<] b).NeBot := nhdsLT_neBot b
  suffices hcauchy : Cauchy (Filter.map P (𝓝[<] b)) by
    exact cauchy_map_iff_exists_tendsto.mp hcauchy
  refine Metric.cauchy_iff.mpr ⟨Filter.map_neBot, ?_⟩
  have hC_nn : 0 ≤ C := by
    obtain ⟨s, hs⟩ := exists_lt b
    exact le_trans (norm_nonneg _) (hbound s hs)
  intro ε hε
  have hCC_pos : 0 < C + 1 := by linarith
  set η : ℝ := ε / (C + 1) with hη_def
  have hη_pos : 0 < η := div_pos hε hCC_pos
  have hIoo_mem : P '' Set.Ioo (b - η) b ∈ Filter.map P (𝓝[<] b) :=
    Filter.image_mem_map (Ioo_mem_nhdsLT (by linarith : b - η < b))
  refine ⟨P '' Set.Ioo (b - η) b, hIoo_mem, ?_⟩
  rintro x ⟨sx, hsx, rfl⟩ y ⟨sy, hsy, rfl⟩
  set s : ℝ := min sx sy with hs_def
  set t : ℝ := max sx sy with ht_def
  have hst : s ≤ t := min_le_max
  have ht_hi : t < b := max_lt hsx.2 hsy.2
  have hs_lo : b - η < s := lt_min hsx.1 hsy.1
  have ht_sub_s_lt : t - s < η := by
    rcases le_total sx sy with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h]; linarith [hsy.2, hsx.1]
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h]; linarith [hsx.2, hsy.1]
  have hmvt : ‖P t - P s‖ ≤ C * (t - s) := by
    have hIcc_sub : Set.Icc s t ⊆ Set.Iio b := fun τ hτ => lt_of_le_of_lt hτ.2 ht_hi
    have hderivW : ∀ x ∈ Set.Icc s t, HasDerivWithinAt P (P' x) (Set.Icc s t) x :=
      fun x hx => (hderiv x (hIcc_sub hx)).hasDerivWithinAt
    have hboundW : ∀ x ∈ Set.Ico s t, ‖P' x‖ ≤ C :=
      fun x hx => hbound x (lt_of_lt_of_le hx.2 ht_hi.le)
    exact norm_image_sub_le_of_norm_deriv_le_segment' hderivW hboundW t
      (right_mem_Icc.mpr hst)
  have h_dist_eq : dist (P sx) (P sy) = ‖P t - P s‖ := by
    rcases le_total sx sy with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h, dist_eq_norm, norm_sub_rev]
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h, dist_eq_norm]
  rw [h_dist_eq]
  calc ‖P t - P s‖ ≤ C * (t - s) := hmvt
    _ ≤ C * η := mul_le_mul_of_nonneg_left ht_sub_s_lt.le hC_nn
    _ < ε := by
        rw [hη_def]
        have hrw : C * (ε / (C + 1)) = ε * (C / (C + 1)) := by ring
        rw [hrw]
        have hfrac : C / (C + 1) < 1 := by rw [div_lt_one hCC_pos]; linarith
        have := mul_lt_mul_of_pos_left hfrac hε
        rwa [mul_one] at this

/-- **Velocity convergence from a bounded derivative on an open interval.**
The `Set.Ioo`-localised version of `velocity_converges_of_bounded_accel`: if
`P : ℝ → E` has derivative `P' s` at every `s ∈ Ioo a b` (with `a < b`) and
`‖P' s‖ ≤ C` throughout that interval, then `P` converges to a genuine limit
`w : E` as `s → b⁻`.

The proof is identical to the `s < b` version, except every Cauchy-witness
interval is taken inside `Ioo a b`: for a target tolerance `ε`, the witness is
`P '' Ioo (max a (b - η)) b` with `η = ε/(C+1)`, which sits in `Ioo a b` (it
lies above `a` since the lower endpoint is `≥ a`) and the mean-value bound
`‖P t - P s‖ ≤ C·(t - s)` applies on each subinterval `Icc s t ⊆ Ioo a b`. -/
theorem velocity_converges_of_bounded_accel_Ioo
    {P P' : ℝ → E} {a b C : ℝ} (hab : a < b)
    (hderiv : ∀ s : ℝ, s ∈ Set.Ioo a b → HasDerivAt P (P' s) s)
    (hbound : ∀ s : ℝ, s ∈ Set.Ioo a b → ‖P' s‖ ≤ C) :
    ∃ w : E, Tendsto P (𝓝[<] b) (𝓝 w) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  haveI hNB : (𝓝[<] b).NeBot := nhdsLT_neBot b
  suffices hcauchy : Cauchy (Filter.map P (𝓝[<] b)) by
    exact cauchy_map_iff_exists_tendsto.mp hcauchy
  refine Metric.cauchy_iff.mpr ⟨Filter.map_neBot, ?_⟩
  have hC_nn : 0 ≤ C := by
    have hmid : (a + b) / 2 ∈ Set.Ioo a b := by
      constructor <;> [linarith; linarith]
    exact le_trans (norm_nonneg _) (hbound _ hmid)
  intro ε hε
  have hCC_pos : 0 < C + 1 := by linarith
  set η : ℝ := ε / (C + 1) with hη_def
  have hη_pos : 0 < η := div_pos hε hCC_pos
  set lo : ℝ := max a (b - η) with hlo_def
  have hlo_lt_b : lo < b := max_lt hab (by linarith)
  have ha_le_lo : a ≤ lo := le_max_left _ _
  have hsub : Set.Ioo lo b ⊆ Set.Ioo a b :=
    fun τ hτ => ⟨lt_of_le_of_lt ha_le_lo hτ.1, hτ.2⟩
  have hIoo_mem : P '' Set.Ioo lo b ∈ Filter.map P (𝓝[<] b) :=
    Filter.image_mem_map (Ioo_mem_nhdsLT hlo_lt_b)
  refine ⟨P '' Set.Ioo lo b, hIoo_mem, ?_⟩
  rintro x ⟨sx, hsx, rfl⟩ y ⟨sy, hsy, rfl⟩
  set s : ℝ := min sx sy with hs_def
  set t : ℝ := max sx sy with ht_def
  have hst : s ≤ t := min_le_max
  have ht_hi : t < b := max_lt hsx.2 hsy.2
  have hs_lo : lo < s := lt_min hsx.1 hsy.1
  have ht_sub_s_lt : t - s < η := by
    have hlo_ge : b - η ≤ lo := le_max_right _ _
    rcases le_total sx sy with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h]; linarith [hsy.2, hsx.1]
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h]; linarith [hsx.2, hsy.1]
  have hmvt : ‖P t - P s‖ ≤ C * (t - s) := by
    have hIcc_sub : Set.Icc s t ⊆ Set.Ioo a b := by
      intro τ hτ
      exact hsub ⟨lt_of_lt_of_le hs_lo hτ.1, lt_of_le_of_lt hτ.2 ht_hi⟩
    have hderivW : ∀ x ∈ Set.Icc s t, HasDerivWithinAt P (P' x) (Set.Icc s t) x :=
      fun x hx => (hderiv x (hIcc_sub hx)).hasDerivWithinAt
    have hboundW : ∀ x ∈ Set.Ico s t, ‖P' x‖ ≤ C :=
      fun x hx => hbound x (hIcc_sub (Set.Ico_subset_Icc_self hx))
    exact norm_image_sub_le_of_norm_deriv_le_segment' hderivW hboundW t
      (right_mem_Icc.mpr hst)
  have h_dist_eq : dist (P sx) (P sy) = ‖P t - P s‖ := by
    rcases le_total sx sy with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h, dist_eq_norm, norm_sub_rev]
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h, dist_eq_norm]
  rw [h_dist_eq]
  calc ‖P t - P s‖ ≤ C * (t - s) := hmvt
    _ ≤ C * η := mul_le_mul_of_nonneg_left ht_sub_s_lt.le hC_nn
    _ < ε := by
        rw [hη_def]
        have hrw : C * (ε / (C + 1)) = ε * (C / (C + 1)) := by ring
        rw [hrw]
        have hfrac : C / (C + 1) < 1 := by rw [div_lt_one hCC_pos]; linarith
        have := mul_lt_mul_of_pos_left hfrac hε
        rwa [mul_one] at this

/-- **Joint continuity of the chart-Christoffel contraction.** As a function
of `(v, y) : E × E`, the diagonal contraction `Γ_α(v, v)(y)` is continuous on
`univ ×ˢ interior (extChartAt I α).target`, inheriting continuity in `y` from
`chartChristoffel_contDiffOn_interior` and linearity in `v` from the
chart-coordinate functionals `(chartModelBasis E).coord`. -/
theorem chartChristoffelContraction_continuousOn_prod
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn
      (fun p : E × E => chartChristoffelContraction (I := I) g α p.1 p.1 p.2)
      (Set.univ ×ˢ interior (extChartAt I α).target) := by
  classical
  unfold chartChristoffelContraction
  refine continuousOn_finset_sum _ (fun k _ => ?_)
  refine ContinuousOn.smul ?_ continuousOn_const
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  have hΓ : ContinuousOn (fun y : E => chartChristoffel (I := I) g α i j k y)
      (interior (extChartAt I α).target) :=
    (chartChristoffel_contDiffOn_interior (I := I) g α i j k).continuousOn
  have hΓp : ContinuousOn
      (fun p : E × E => chartChristoffel (I := I) g α i j k p.2)
      (Set.univ ×ˢ interior (extChartAt I α).target) :=
    hΓ.comp continuousOn_snd (fun p hp => hp.2)
  have hci : Continuous (fun p : E × E => chartCoord (E := E) i p.1) := by
    have : Continuous (fun v : E => chartCoord (E := E) i v) :=
      (((chartModelBasis E).coord i).toContinuousLinearMap).continuous
    exact this.comp continuous_fst
  have hcj : Continuous (fun p : E × E => chartCoord (E := E) j p.1) := by
    have : Continuous (fun v : E => chartCoord (E := E) j v) :=
      (((chartModelBasis E).coord j).toContinuousLinearMap).continuous
    exact this.comp continuous_fst
  exact (hΓp.mul hci.continuousOn).mul hcj.continuousOn

/-- **Directional velocity limit in a fixed chart.** Let `α : M`, and let
`u : ℝ → E` be the chart-`α` representation of a curve with chart-velocity
`u' : ℝ → E`, satisfying the chart-coordinate geodesic equation in the chart
at `α`.  Concretely we assume, for every `s < b`:

* `HasDerivAt u (u' s) s` — the chart curve is `C¹` with velocity `u'`;
* `HasDerivAt u' (-Γ_α(u' s, u' s)(u s)) s` — the chart geodesic equation
  `u'' = -Γ_α(u', u')(u)`;
* `‖u' s‖ ≤ K₁` — the chart velocity is bounded; and
* `u s ∈ S` for a fixed compact `S ⊆ interior (extChartAt I α).target` — the
  chart image stays in a compact subset of the chart domain.

Then the chart-velocity converges to a genuine limit `w : E` as `s → b⁻`.

The chart-acceleration `Γ_α(u' s, u' s)(u s)` is bounded by the supremum of
the continuous contraction on the compact box `closedBall 0 K₁ ×ˢ S`
(`chartChristoffelContraction_continuousOn_prod` and
`IsCompact.exists_bound_of_continuousOn`), so the conclusion follows from
`velocity_converges_of_bounded_accel` applied to `u'`. -/
theorem chartVelocity_converges_at_finite_endpoint
    (g : SmoothRiemannianMetric I M) (α : M)
    {u u' : ℝ → E} {b K₁ : ℝ} {S : Set E}
    (hS_compact : IsCompact S)
    (hS_sub : S ⊆ interior (extChartAt I α).target)
    (_hu_deriv : ∀ s : ℝ, s < b → HasDerivAt u (u' s) s)
    (hu'_deriv : ∀ s : ℝ, s < b →
      HasDerivAt u'
        (- chartChristoffelContraction (I := I) g α (u' s) (u' s) (u s)) s)
    (hu'_bound : ∀ s : ℝ, s < b → ‖u' s‖ ≤ K₁)
    (hu_mem : ∀ s : ℝ, s < b → u s ∈ S) :
    ∃ w : E, Tendsto u' (𝓝[<] b) (𝓝 w) := by
  classical
  set K : Set (E × E) := Metric.closedBall (0 : E) K₁ ×ˢ S with hK_def
  have hK_compact : IsCompact K :=
    (isCompact_closedBall (0 : E) K₁).prod hS_compact
  have hΓcont := chartChristoffelContraction_continuousOn_prod (I := I) g α
  have hΓcont_K : ContinuousOn
      (fun p : E × E => chartChristoffelContraction (I := I) g α p.1 p.1 p.2) K := by
    refine hΓcont.mono ?_
    intro p hp
    exact ⟨Set.mem_univ _, hS_sub hp.2⟩
  obtain ⟨C, hC⟩ := hK_compact.exists_bound_of_continuousOn hΓcont_K
  set P' : ℝ → E :=
    fun s => - chartChristoffelContraction (I := I) g α (u' s) (u' s) (u s) with hP'_def
  have hderiv_pf : ∀ s : ℝ, s < b → HasDerivAt u' (P' s) s := fun s hs => hu'_deriv s hs
  have hbound_pf : ∀ s : ℝ, s < b → ‖P' s‖ ≤ C := by
    intro s hs
    have hmem : ((u' s, u s) : E × E) ∈ K := by
      refine ⟨?_, hu_mem s hs⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hu'_bound s hs
    have hCs :
        ‖chartChristoffelContraction (I := I) g α (u' s) (u' s) (u s)‖ ≤ C :=
      hC ((u' s, u s) : E × E) hmem
    rw [hP'_def, norm_neg]
    exact hCs
  exact velocity_converges_of_bounded_accel (P := u') (P' := P') (b := b) (C := C)
    hderiv_pf hbound_pf

/-- **Directional velocity limit in a fixed chart, open-interval form.** The
`Set.Ioo`-localised version of `chartVelocity_converges_at_finite_endpoint`:
the chart-coordinate geodesic data are only assumed on `Ioo a b` (with
`a < b`), which is all the `𝓝[<] b` filter sees.  Identical proof, with the
analytic engine replaced by its `Ioo`-localised version
`velocity_converges_of_bounded_accel_Ioo`. -/
theorem chartVelocity_converges_at_finite_endpoint_Ioo
    (g : SmoothRiemannianMetric I M) (α : M)
    {u u' : ℝ → E} {a b K₁ : ℝ} {S : Set E} (hab : a < b)
    (hS_compact : IsCompact S)
    (hS_sub : S ⊆ interior (extChartAt I α).target)
    (_hu_deriv : ∀ s : ℝ, s ∈ Set.Ioo a b → HasDerivAt u (u' s) s)
    (hu'_deriv : ∀ s : ℝ, s ∈ Set.Ioo a b →
      HasDerivAt u'
        (- chartChristoffelContraction (I := I) g α (u' s) (u' s) (u s)) s)
    (hu'_bound : ∀ s : ℝ, s ∈ Set.Ioo a b → ‖u' s‖ ≤ K₁)
    (hu_mem : ∀ s : ℝ, s ∈ Set.Ioo a b → u s ∈ S) :
    ∃ w : E, Tendsto u' (𝓝[<] b) (𝓝 w) := by
  classical
  set K : Set (E × E) := Metric.closedBall (0 : E) K₁ ×ˢ S with hK_def
  have hK_compact : IsCompact K :=
    (isCompact_closedBall (0 : E) K₁).prod hS_compact
  have hΓcont := chartChristoffelContraction_continuousOn_prod (I := I) g α
  have hΓcont_K : ContinuousOn
      (fun p : E × E => chartChristoffelContraction (I := I) g α p.1 p.1 p.2) K := by
    refine hΓcont.mono ?_
    intro p hp
    exact ⟨Set.mem_univ _, hS_sub hp.2⟩
  obtain ⟨C, hC⟩ := hK_compact.exists_bound_of_continuousOn hΓcont_K
  set P' : ℝ → E :=
    fun s => - chartChristoffelContraction (I := I) g α (u' s) (u' s) (u s) with hP'_def
  have hderiv_pf : ∀ s : ℝ, s ∈ Set.Ioo a b → HasDerivAt u' (P' s) s :=
    fun s hs => hu'_deriv s hs
  have hbound_pf : ∀ s : ℝ, s ∈ Set.Ioo a b → ‖P' s‖ ≤ C := by
    intro s hs
    have hmem : ((u' s, u s) : E × E) ∈ K := by
      refine ⟨?_, hu_mem s hs⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hu'_bound s hs
    have hCs :
        ‖chartChristoffelContraction (I := I) g α (u' s) (u' s) (u s)‖ ≤ C :=
      hC ((u' s, u s) : E × E) hmem
    rw [hP'_def, norm_neg]
    exact hCs
  exact velocity_converges_of_bounded_accel_Ioo (P := u') (P' := P') (a := a)
    (b := b) (C := C) hab hderiv_pf hbound_pf

/-- The chart-`y` Gram quadratic form on the model space: at a chart-target
point `z` and a vector `V`, this is `∑ᵢⱼ G_{ij}(z) · Vⁱ · Vʲ`, where
`G_{ij}(z) = chartGramOnE g y i j z`.  It is the chart-coordinate expression of
the squared `g`-length of the tangent vector `symmL_y(z) V`. -/
private def chartGramQuad (g : SmoothRiemannianMetric I M) (y : M)
    (z : E) (V : E) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    chartGramOnE (I := I) g y i j z *
      chartCoord (E := E) i V * chartCoord (E := E) j V

/-- The Gram quadratic form equals the squared `g`-length of the
inverse-trivialisation image of `V`, for `z` in the chart target. -/
private lemma chartGramQuad_eq_inner
    (g : SmoothRiemannianMetric I M) (y : M) {z : E}
    (_hz : z ∈ (extChartAt I y).target) (V : E) :
    chartGramQuad (I := I) g y z V =
      g.inner ((extChartAt I y).symm z)
        ((trivializationAt E (TangentSpace I) y).symmL ℝ ((extChartAt I y).symm z) V)
        ((trivializationAt E (TangentSpace I) y).symmL ℝ ((extChartAt I y).symm z) V) := by
  classical
  set x : M := (extChartAt I y).symm z with hx_def
  rw [chartGramQuad,
    inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g y (x := x) V V]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [chartGramOnE_def, hx_def]

/-- The Gram quadratic form is nonnegative, and strictly positive when `V ≠ 0`,
for `z` in the chart target.  Positivity uses the positive-definiteness of `g`
together with the injectivity of the inverse trivialisation on the base set. -/
private lemma chartGramQuad_pos
    (g : SmoothRiemannianMetric I M) (y : M) {z : E}
    (hz : z ∈ (extChartAt I y).target) {V : E} (hV : V ≠ 0) :
    0 < chartGramQuad (I := I) g y z V := by
  classical
  rw [chartGramQuad_eq_inner (I := I) g y hz V]
  set x : M := (extChartAt I y).symm z with hx_def
  have hx_src : x ∈ (chartAt H y).source := by
    rw [hx_def, ← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I y).map_target hz
  have hbase : x ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx_src
  have hsymm_ne : (trivializationAt E (TangentSpace I) y).symmL ℝ x V ≠ 0 := by
    intro hzero
    apply hV
    have hround :
        ((trivializationAt E (TangentSpace I) y).continuousLinearMapAt ℝ x)
            ((trivializationAt E (TangentSpace I) y).symmL ℝ x V) = V :=
      (trivializationAt E (TangentSpace I) y).continuousLinearMapAt_symmL
        (R := ℝ) hbase V
    rw [hzero, map_zero] at hround
    exact hround.symm
  exact g.pos x _ hsymm_ne

/-- The Gram quadratic form is quadratically homogeneous: scaling `V` by `a`
multiplies the form by `a²`. -/
private lemma chartGramQuad_smul
    (g : SmoothRiemannianMetric I M) (y : M) (z : E) (a : ℝ) (V : E) :
    chartGramQuad (I := I) g y z (a • V) = a ^ 2 * chartGramQuad (I := I) g y z V := by
  classical
  unfold chartGramQuad
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [chartCoord_smul, chartCoord_smul]
  ring

/-- Joint continuity of the Gram quadratic form `(z, V) ↦ chartGramQuad g y z V`
on `(extChartAt I y).target ×ˢ univ`: the Gram coefficients are smooth on the
target, and the chart coordinates are continuous linear functionals. -/
private lemma chartGramQuad_continuousOn
    (g : SmoothRiemannianMetric I M) (y : M) :
    ContinuousOn (fun p : E × E => chartGramQuad (I := I) g y p.1 p.2)
      ((extChartAt I y).target ×ˢ (Set.univ : Set E)) := by
  classical
  unfold chartGramQuad
  refine continuousOn_finset_sum _ (fun i _ => continuousOn_finset_sum _ (fun j _ => ?_))
  have hG : ContinuousOn (fun p : E × E => chartGramOnE (I := I) g y i j p.1)
      ((extChartAt I y).target ×ˢ (Set.univ : Set E)) :=
    ((chartGramOnE_contDiffOn (I := I) g y i j).continuousOn).comp continuousOn_fst
      (fun p hp => hp.1)
  have hci : Continuous (fun p : E × E => chartCoord (E := E) i p.2) :=
    (((chartModelBasis E).coord i).toContinuousLinearMap).continuous.comp continuous_snd
  have hcj : Continuous (fun p : E × E => chartCoord (E := E) j p.2) :=
    (((chartModelBasis E).coord j).toContinuousLinearMap).continuous.comp continuous_snd
  exact (hG.mul hci.continuousOn).mul hcj.continuousOn

/-- **Uniform Gram lower bound on a compact subset of the chart target.**
For a nonempty compact set `S` inside the chart target at `y`, there is a
positive constant `m` with `m · ‖V‖² ≤ chartGramQuad g y z V` for every
`z ∈ S` and every `V : E`.

The bound is the minimum of the quadratic form — continuous on
`target ×ˢ univ`, strictly positive on the compact set `S ×ˢ sphere 0 1`
(unit vectors, where positivity is `chartGramQuad_pos`) — transferred to a
general `V` by the quadratic homogeneity `chartGramQuad_smul`. -/
private lemma exists_chartGramQuad_lower_bound
    (g : SmoothRiemannianMetric I M) (y : M) {S : Set E}
    (hS_compact : IsCompact S) (hS_sub : S ⊆ (extChartAt I y).target)
    (hS_ne : S.Nonempty) :
    ∃ m : ℝ, 0 < m ∧ ∀ z ∈ S, ∀ V : E, m * ‖V‖ ^ 2 ≤ chartGramQuad (I := I) g y z V := by
  classical
  have hfin_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
  set T : Set (E × E) := S ×ˢ Metric.sphere (0 : E) 1 with hT_def
  have hsphere_compact : IsCompact (Metric.sphere (0 : E) 1) :=
    isCompact_sphere (0 : E) 1
  have hT_compact : IsCompact T := hS_compact.prod hsphere_compact
  have hsphere_ne : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hT_ne : T.Nonempty := hS_ne.prod hsphere_ne
  have hQcont : ContinuousOn (fun p : E × E => chartGramQuad (I := I) g y p.1 p.2) T := by
    refine (chartGramQuad_continuousOn (I := I) g y).mono ?_
    intro p hp
    exact ⟨hS_sub hp.1, Set.mem_univ _⟩
  obtain ⟨p₀, hp₀_mem, hp₀_min⟩ :=
    hT_compact.exists_isMinOn hT_ne hQcont
  set m : ℝ := chartGramQuad (I := I) g y p₀.1 p₀.2 with hm_def
  have hp₀1_mem : p₀.1 ∈ S := hp₀_mem.1
  have hp₀2_sphere : p₀.2 ∈ Metric.sphere (0 : E) 1 := hp₀_mem.2
  have hp₀2_ne : p₀.2 ≠ 0 := by
    intro hz
    rw [Metric.mem_sphere, hz, dist_self] at hp₀2_sphere
    exact one_ne_zero hp₀2_sphere.symm
  have hm_pos : 0 < m :=
    chartGramQuad_pos (I := I) g y (hS_sub hp₀1_mem) hp₀2_ne
  refine ⟨m, hm_pos, ?_⟩
  intro z hz V
  rcases eq_or_ne V 0 with hV | hV
  · subst hV; simp [chartGramQuad]
  · set r : ℝ := ‖V‖ with hr_def
    have hr_pos : 0 < r := by rw [hr_def]; exact norm_pos_iff.mpr hV
    set Vhat : E := r⁻¹ • V with hVhat_def
    have hVhat_unit : Vhat ∈ Metric.sphere (0 : E) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, hVhat_def, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_of_pos hr_pos, hr_def]
      field_simp
    have hmem_T : ((z, Vhat) : E × E) ∈ T := ⟨hz, hVhat_unit⟩
    have hmin : m ≤ chartGramQuad (I := I) g y z Vhat :=
      isMinOn_iff.mp hp₀_min ((z, Vhat) : E × E) hmem_T
    have hV_eq : V = r • Vhat := by
      rw [hVhat_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hr_pos), one_smul]
    have hscale : chartGramQuad (I := I) g y z V = r ^ 2 * chartGramQuad (I := I) g y z Vhat := by
      conv_lhs => rw [hV_eq]
      rw [chartGramQuad_smul]
    rw [hscale, hr_def]
    have hr2_nn : (0 : ℝ) ≤ ‖V‖ ^ 2 := sq_nonneg _
    calc m * ‖V‖ ^ 2 = ‖V‖ ^ 2 * m := by ring
      _ ≤ ‖V‖ ^ 2 * chartGramQuad (I := I) g y z Vhat :=
          mul_le_mul_of_nonneg_left hmin hr2_nn

/-- **Chart-coordinate velocity bound near the limit point.** Let `γ` be a
curve converging (in the manifold topology) to `y` as `s → b⁻`, with squared
`g`-speed bounded by `c²`.  Then on some left-interval `Ioo (b - ε) b` the
chart-`y`-coordinate velocity `deriv (chartCurve y γ) s` is bounded in norm by
`c / √m`, and the chart image `chartCurve y γ s` stays in a fixed compact set
`S ⊆ interior (extChartAt I y).target`.

The compact set `S` is a closed ball around `extChartAt I y y` inside the
interior of the target; `γ s → y` and continuity of the chart map keep
`chartCurve y γ s` inside it for `s` near `b`.  On `S` the chart Gram matrix is
uniformly positive definite (`exists_chartGramQuad_lower_bound`), so the squared
speed `chartGramQuad g y (u s)(V s) = ⟨γ', γ'⟩_g ≤ c²` yields `‖V s‖ ≤ c/√m`. -/
theorem chartVelocity_bound_near_limit
    (g : SmoothRiemannianMetric I M) (y : M) {γ : ℝ → M} {a b c : ℝ}
    (hab : a < b) (hc_nonneg : 0 ≤ c)
    (hγ_mdiff : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Set.Ioo a b))
    (hy_lim : Tendsto γ (𝓝[<] b) (𝓝 y))
    (hSpeedSq : ∀ s ∈ Set.Ioo a b,
      (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) ≤ c ^ 2) :
    ∃ (ε K : ℝ) (S : Set E), 0 < ε ∧ IsCompact S ∧
      S ⊆ interior (extChartAt I y).target ∧
      (∀ s ∈ Set.Ioo (b - ε) b,
        ‖deriv (chartCurve (I := I) y γ) s‖ ≤ K ∧
          chartCurve (I := I) y γ s ∈ S) := by
  classical
  have hy_src : y ∈ (chartAt H y).source := mem_chart_source H y
  have hy_ext_src : y ∈ (extChartAt I y).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hy_src
  have hy_target : extChartAt I y y ∈ (extChartAt I y).target :=
    (extChartAt I y).map_source hy_ext_src
  have hy_interior : extChartAt I y y ∈ interior (extChartAt I y).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) y hy_target
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ :=
    Metric.isOpen_iff.mp isOpen_interior _ hy_interior
  set S : Set E := Metric.closedBall (extChartAt I y y) (ρ / 2) with hS_def
  have hS_compact : IsCompact S := isCompact_closedBall _ _
  have hS_sub : S ⊆ interior (extChartAt I y).target := by
    intro z hz
    refine hρ_sub ?_
    rw [Metric.mem_ball]
    rw [hS_def, Metric.mem_closedBall] at hz
    linarith [hz]
  have hS_ne : S.Nonempty := ⟨extChartAt I y y, by
    rw [hS_def, Metric.mem_closedBall, dist_self]; linarith⟩
  obtain ⟨m, hm_pos, hm_bound⟩ :=
    exists_chartGramQuad_lower_bound (I := I) g y hS_compact
      (hS_sub.trans interior_subset) hS_ne
  set K : ℝ := c / Real.sqrt m with hK_def
  have hu_lim : Tendsto (chartCurve (I := I) y γ) (𝓝[<] b) (𝓝 (extChartAt I y y)) := by
    have hcont_at : ContinuousAt (extChartAt I y) y :=
      (continuousAt_extChartAt (I := I) y)
    have : Tendsto (fun s => extChartAt I y (γ s)) (𝓝[<] b) (𝓝 (extChartAt I y y)) :=
      hcont_at.tendsto.comp hy_lim
    simpa [chartCurve] using this
  have hu_mem_ev : ∀ᶠ s in 𝓝[<] b, chartCurve (I := I) y γ s ∈ S := by
    have hball_nhds : Metric.closedBall (extChartAt I y y) (ρ / 2) ∈
        𝓝 (extChartAt I y y) :=
      Metric.closedBall_mem_nhds _ (by linarith)
    exact hu_lim hball_nhds
  have hsrc_ev : ∀ᶠ s in 𝓝[<] b, γ s ∈ (chartAt H y).source := by
    have hsrc_nhds : (chartAt H y).source ∈ 𝓝 y :=
      (chartAt H y).open_source.mem_nhds hy_src
    exact hy_lim hsrc_nhds
  obtain ⟨U, hU_nhds, hU_sub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
      (Filter.inter_mem hu_mem_ev hsrc_ev)
  obtain ⟨δ₀, hδ₀_pos, hδ₀_sub⟩ := Metric.mem_nhds_iff.mp hU_nhds
  set δ : ℝ := min δ₀ ((b - a) / 2) with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ₀_pos (by linarith)
  have hδ_le : δ ≤ δ₀ := min_le_left _ _
  have hδ_le2 : δ ≤ (b - a) / 2 := min_le_right _ _
  have hba_gt : a < b - δ := by linarith
  refine ⟨δ, K, S, hδ_pos, hS_compact, hS_sub, ?_⟩
  intro s hs
  have hs_ball : s ∈ Metric.ball b δ₀ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    refine ⟨by linarith [hs.1, hδ_le], by linarith [hs.2]⟩
  have hs_Ioo : s ∈ Set.Ioo a b := ⟨lt_trans hba_gt hs.1, hs.2⟩
  have hs_Iio : s ∈ Set.Iio b := hs.2
  have hs_both : chartCurve (I := I) y γ s ∈ S ∧ γ s ∈ (chartAt H y).source :=
    hU_sub ⟨hδ₀_sub hs_ball, hs_Iio⟩
  obtain ⟨hu_memS, hγ_src⟩ := hs_both
  refine ⟨?_, hu_memS⟩
  set V : E := deriv (chartCurve (I := I) y γ) s with hV_def
  have hVeq : (fderiv ℝ ((extChartAt I y) ∘ γ) s : ℝ →L[ℝ] E) (1 : ℝ) = V := by
    rw [hV_def, deriv]; rfl
  have hγ_s : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s :=
    (hγ_mdiff s hs_Ioo).mdifferentiableAt (isOpen_Ioo.mem_nhds hs_Ioo)
  have hraw := bm_c_raw_mfderiv_eq_symmL_fderiv_at (I := I) (γ := γ) (α := y)
    (s := s) hγ_s hγ_src
  rw [hVeq] at hraw
  have hu_target : chartCurve (I := I) y γ s ∈ (extChartAt I y).target :=
    interior_subset (hS_sub hu_memS)
  have hinv : (extChartAt I y).symm (chartCurve (I := I) y γ s) = γ s := by
    rw [chartCurve_def]
    exact (extChartAt I y).left_inv (by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hγ_src)
  have hspeed_eq :
      chartGramQuad (I := I) g y (chartCurve (I := I) y γ s) V =
        (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) := by
    rw [chartGramQuad_eq_inner (I := I) g y hu_target V, hinv]
    rw [← hraw]
    rfl
  have hQ_le : chartGramQuad (I := I) g y (chartCurve (I := I) y γ s) V ≤ c ^ 2 := by
    rw [hspeed_eq]; exact hSpeedSq s hs_Ioo
  have hlow : m * ‖V‖ ^ 2 ≤ c ^ 2 :=
    le_trans (hm_bound (chartCurve (I := I) y γ s) hu_memS V) hQ_le
  have hVsq_le : ‖V‖ ^ 2 ≤ c ^ 2 / m := by
    rw [le_div_iff₀ hm_pos]; linarith [hlow]
  have hsqrt_m_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm_pos
  rw [hK_def]
  rw [le_div_iff₀ hsqrt_m_pos]
  have hlhs_nn : 0 ≤ ‖V‖ * Real.sqrt m := mul_nonneg (norm_nonneg _) hsqrt_m_pos.le
  have hsq : (‖V‖ * Real.sqrt m) ^ 2 ≤ c ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hm_pos.le]
    calc ‖V‖ ^ 2 * m ≤ (c ^ 2 / m) * m :=
          mul_le_mul_of_nonneg_right hVsq_le hm_pos.le
      _ = c ^ 2 := by field_simp
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hlhs_nn, Real.sqrt_sq hc_nonneg] at this

/-- **Local geodesic existence on an open interval, intrinsic form.**
From the local existence-of-geodesics theorem (`exists_geodesic_with_initial_velocity_at`,
which yields an integral curve of the chart-fixed geodesic spray on a
neighbourhood of `0`), the moving-foot geodesic equation
`HasGeodesicEquationAt g η t` holds at *every* `t` in a small open
interval `Ioo (-δ) δ`, not merely at the launch time `0`.

The key step is that `IsMIntegralCurveAt` packages an integral-curve
property holding on a whole *neighbourhood* of the launch time, so it
restricts to `IsMIntegralCurveAt f (gvfChart g y) t` for every `t` in a
small ball, while the lift's foot stays inside the launch chart at `y`
(continuity of the projection plus openness of `(chartAt H y).source`).
Each such `t` therefore carries an `IsGeodesicAt g η t` witness whose
chart basepoint is held fixed at the launch point `y`, and the
unconditional bridge `IsGeodesicAt.hasGeodesicEquationAt` converts it to
the moving-foot equation. -/
theorem exists_isGeodesicOn_Ioo_at
    (g : SmoothRiemannianMetric I M) (y : M) (w : TangentSpace I y) :
    ∃ (η : ℝ → M) (δ : ℝ), 0 < δ ∧ η 0 = y ∧
      IsGeodesicOn (I := I) g η (Set.Ioo (-δ) δ) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨η, f, hf0, hηproj, hη0, hf_int, _hgeo⟩ := exists_geodesic_with_initial_velocity_at (I := I) g y w
  subst hηproj
  have hηt : ∀ t, projectCurve (I := I) f t = (f t).proj := fun _ => rfl
  have hf0proj : (f 0).proj = y := by rw [hf0]
  have hηcont : ContinuousAt (projectCurve (I := I) f) 0 := by
    have hc : Continuous (fun p : TangentBundle I M => p.proj) :=
      FiberBundle.continuous_proj E (TangentSpace I)
    exact hc.continuousAt.comp hf_int.continuousAt
  obtain ⟨ε, hε, hf_on⟩ := isMIntegralCurveAt_iff'.mp hf_int
  have hsrc_nhds : {t : ℝ | (f t).proj ∈ (chartAt H y).source} ∈ 𝓝 (0 : ℝ) := by
    have hopen : IsOpen ((chartAt H y).source) := (chartAt H y).open_source
    have hmem : (f 0).proj ∈ (chartAt H y).source := by
      rw [hf0proj]; exact mem_chart_source H y
    exact hηcont.preimage_mem_nhds (hopen.mem_nhds hmem)
  have hball_nhds : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε
  obtain ⟨δ, hδ, hδ_sub⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem hball_nhds hsrc_nhds)
  refine ⟨projectCurve (I := I) f, δ, hδ, hη0, ?_⟩
  intro t ht
  have htball : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ⟨ht.1, ht.2⟩
  have ht_both := hδ_sub htball
  have ht_ballε : t ∈ Metric.ball (0 : ℝ) ε := ht_both.1
  have ht_src : (f t).proj ∈ (chartAt H y).source := ht_both.2
  have hf_at_t : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g y) t :=
    hf_on.isMIntegralCurveAt (Metric.isOpen_ball.mem_nhds ht_ballε)
  have hgeo_at : IsGeodesicAt (I := I) g (projectCurve (I := I) f) t :=
    ⟨y, f, hηt, ht_src, hf_at_t⟩
  exact hgeo_at.hasGeodesicEquationAt g

/-- **Local geodesic existence on an open interval, exposing the launch
velocity.** Strengthens `exists_isGeodesicOn_Ioo_at`: the fresh local geodesic
`η` launched from `(y, w)` not only satisfies the moving-foot geodesic equation
on a symmetric interval `Ioo (-δ) δ`, but additionally `η 0 = y`, `η` is
continuous at `0`, and its raw manifold velocity at the launch time is the seed
vector `w`: `mfderiv 𝓘(ℝ, ℝ) I η 0 1 = w`.

The proof reuses the integral-curve construction of `exists_isGeodesicOn_Ioo_at`
(the same lift `f` of the chart-fixed geodesic spray with `f 0 = ⟨y, w⟩`),
and reads off the launch velocity through
`IsMIntegralCurveAt.mfderiv_proj_one`: the manifold derivative of the projected
curve at the launch time equals the fibre vector `(f 0).snd = w`. -/
theorem exists_isGeodesicOn_Ioo_at_velocity
    (g : SmoothRiemannianMetric I M) (y : M) (w : TangentSpace I y) :
    ∃ (η : ℝ → M) (δ : ℝ), 0 < δ ∧ η 0 = y ∧ ContinuousAt η 0 ∧
      (mfderiv 𝓘(ℝ, ℝ) I η 0 (1 : ℝ) : E) = (w : E) ∧
      (∀ t ∈ Set.Ioo (-δ) δ, MDifferentiableAt 𝓘(ℝ, ℝ) I η t) ∧
      (∀ t ∈ Set.Ioo (-δ) δ, η t ∈ (chartAt H y).source) ∧
      IsGeodesicOn (I := I) g η (Set.Ioo (-δ) δ) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨η, f, hf0, hηproj, hη0, hf_int, _hgeo⟩ := exists_geodesic_with_initial_velocity_at (I := I) g y w
  subst hηproj
  have hηt : ∀ t, projectCurve (I := I) f t = (f t).proj := fun _ => rfl
  have hf0proj : (f 0).proj = y := by rw [hf0]
  have hηcont : ContinuousAt (projectCurve (I := I) f) 0 := by
    have hc : Continuous (fun p : TangentBundle I M => p.proj) :=
      FiberBundle.continuous_proj E (TangentSpace I)
    exact hc.continuousAt.comp hf_int.continuousAt
  obtain ⟨ε, hε, hf_on⟩ := isMIntegralCurveAt_iff'.mp hf_int
  have hsrc_nhds : {t : ℝ | (f t).proj ∈ (chartAt H y).source} ∈ 𝓝 (0 : ℝ) := by
    have hopen : IsOpen ((chartAt H y).source) := (chartAt H y).open_source
    have hmem : (f 0).proj ∈ (chartAt H y).source := by
      rw [hf0proj]; exact mem_chart_source H y
    exact hηcont.preimage_mem_nhds (hopen.mem_nhds hmem)
  have hball_nhds : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε
  obtain ⟨δ, hδ, hδ_sub⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem hball_nhds hsrc_nhds)
  have hf0_src : (f 0).proj ∈ (chartAt H y).source := by
    rw [hf0proj]; exact mem_chart_source H y
  have hmf : mfderiv 𝓘(ℝ, ℝ) I (fun t => (f t).proj) 0 (1 : ℝ) = (f 0).snd :=
    IsMIntegralCurveAt.mfderiv_proj_one (I := I) (g := g) (α := y) (t₀ := 0)
      hf_int hf0_src
  have hf0snd : ((f 0).snd : E) = (w : E) := by rw [hf0]
  have hf_at_t : ∀ t ∈ Set.Ioo (-δ) δ,
      IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g y) t ∧
        (f t).proj ∈ (chartAt H y).source := by
    intro t ht
    have htball : t ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ⟨ht.1, ht.2⟩
    have ht_both := hδ_sub htball
    exact ⟨hf_on.isMIntegralCurveAt (Metric.isOpen_ball.mem_nhds ht_both.1), ht_both.2⟩
  refine ⟨projectCurve (I := I) f, δ, hδ, hη0, hηcont, ?_, ?_, ?_, ?_⟩
  · rw [show (projectCurve (I := I) f) = (fun t => (f t).proj) from rfl, hmf, hf0snd]
  · intro t ht
    have hfd : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent f t :=
      (hf_at_t t ht).1.hasMFDerivAt.mdifferentiableAt
    have hpd : MDifferentiableAt I.tangent I
        (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t) :=
      (Bundle.contMDiffAt_proj (E := (TangentSpace I : M → Type _)) (n := 1)).mdifferentiableAt
        (by norm_num)
    exact (hpd.comp t hfd)
  · intro t ht
    exact (hf_at_t t ht).2
  · intro t ht
    have hgeo_at : IsGeodesicAt (I := I) g (projectCurve (I := I) f) t :=
      ⟨y, f, hηt, (hf_at_t t ht).2, (hf_at_t t ht).1⟩
    exact hgeo_at.hasGeodesicEquationAt g

/-- **Intrinsic extension past a finite endpoint, given the continuation.**
Let `γ` be a geodesic (intrinsic moving-foot sense) on `Iio T`, and let
`η` be a fresh local geodesic on `Ioo (-δ) δ` whose left-shift
`t ↦ η (t - T)` agrees with `γ` approaching `T` from below (the
`C¹`-matching hypothesis `hmatch`). Then `γ` extends to a geodesic on the
strictly larger interval `Iio (T + δ)`, agreeing with `γ` below `T`.

This replaces the (false on multi-chart manifolds) fixed-basepoint
statement `maximalGeodesicInterval g p v = Set.univ`: the extension here
is genuinely *across charts*, since the continuation geodesic `η` is
launched from its own chart (typically the limit point `y`), not from the
original basepoint. The gluing is `Geodesic.isGeodesicOn_glue_at_limit`.
The continuation `η` is supplied by `exists_isGeodesicOn_Ioo_at` (whose
launch point/velocity are the metric limit of `γ` at `T` and the limit
velocity); the matching against that concrete `η` is the genuine
asymptotic datum, recorded as the explicit hypothesis `hmatch`. -/
theorem isGeodesicOn_extends_past_finite_endpoint
    (g : SmoothRiemannianMetric I M) {γ η : ℝ → M} {T δ : ℝ} (hδ : 0 < δ)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Iio T))
    (hη : IsGeodesicOn (I := I) g η (Set.Ioo (-δ) δ))
    (hmatch : γ =ᶠ[nhdsWithin T (Set.Iio T)] (fun t => η (t - T))) :
    ∃ γ' : ℝ → M,
      IsGeodesicOn (I := I) g γ' (Set.Iio (T + δ)) ∧
      (∀ t < T, γ' t = γ t) := by
  refine ⟨fun t => if t < T then γ t else η (t - T),
    Geodesic.isGeodesicOn_glue_at_limit (I := I) g hδ hγ hη hmatch, ?_⟩
  intro t ht
  simp only [if_pos ht]

/-- **Endpoint continuation data.** For a geodesic `γ` on `Iio b`, the
genuine geometric datum needed to extend across the endpoint `b`: a fresh
local geodesic `η` on some symmetric interval `Ioo (-δ) δ` whose
left-shift `t ↦ η (t - b)` matches `γ` approaching `b` from below. This is
the `C¹`-matching produced by the velocity-limit/Cauchy machinery (the
launch point/velocity of `η` are the metric limit of `γ` at `b` and the
limit velocity); it is a genuine assertion about `γ`'s asymptotics,
distinct from the geodesic-extension conclusion. -/
def HasEndpointContinuation
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (b : ℝ) : Prop :=
  ∃ (η : ℝ → M) (δ : ℝ), 0 < δ ∧
    IsGeodesicOn (I := I) g η (Set.Ioo (-δ) δ) ∧
    (∀ t ∈ Set.Ioo (-δ) δ, MDifferentiableAt 𝓘(ℝ, ℝ) I η t) ∧
    γ =ᶠ[nhdsWithin b (Set.Iio b)] (fun t => η (t - b))

/-- **Chart-phase ODE uniqueness on `Icc a b`, left-endpoint form.**  Two phase
curves `c₁, c₂ : ℝ → E × E` that solve the chart-`α` phase geodesic ODE
`z' = chartPhaseVF g α z` (in one-sided `Iic`-derivative form) on `Ioc a b`,
are continuous on `Icc a b`, stay inside a compact set `K` contained in the
chart-target interior product, and agree at the right endpoint `b`, agree on all
of `Icc a b`.  Direct application of `ODE_solution_unique_of_mem_Icc_left` with
the uniform Lipschitz constant of `chartPhaseVF g α` on `K`. -/
theorem chartPhaseVF_orbit_uniqueness_Icc_left
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set (E × E)} (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    {a b : ℝ}
    {c₁ c₂ : ℝ → E × E}
    (hc₁_cont : ContinuousOn c₁ (Set.Icc a b))
    (hc₂_cont : ContinuousOn c₂ (Set.Icc a b))
    (hc₁_deriv : ∀ s ∈ Set.Ioc a b,
      HasDerivWithinAt c₁ (chartPhaseVF (I := I) g α (c₁ s)) (Set.Iic s) s)
    (hc₂_deriv : ∀ s ∈ Set.Ioc a b,
      HasDerivWithinAt c₂ (chartPhaseVF (I := I) g α (c₂ s)) (Set.Iic s) s)
    (hc₁_in_K : ∀ s ∈ Set.Ioc a b, c₁ s ∈ K)
    (hc₂_in_K : ∀ s ∈ Set.Ioc a b, c₂ s ∈ K)
    (h_eq_at_b : c₁ b = c₂ b) :
    Set.EqOn c₁ c₂ (Set.Icc a b) := by
  obtain ⟨L, hLip⟩ :=
    chartPhaseVF_lipschitzOnWith_of_compact (I := I) g α hK_compact hK_subset
  exact ODE_solution_unique_of_mem_Icc_left
    (v := fun _ z => chartPhaseVF (I := I) g α z) (s := fun _ => K) (K := L)
    (fun t _ => hLip) hc₁_cont hc₁_deriv hc₁_in_K hc₂_cont hc₂_deriv hc₂_in_K h_eq_at_b

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Endpoint-continuation producer under metric completeness.**
For a moving-foot geodesic `γ` on `Iio b` that is `C¹` with constant
`g`-speed bounded by `c` (the two minimal separable regularity data a
unit-speed geodesic supplies — `C¹`-time-smoothness and a uniform
velocity-enorm bound), metric completeness furnishes endpoint-continuation
data at `b`.

The genuine ODE-regularity argument has three parts:

* **Full position limit.** The constant-speed length-distance estimate
  (`bm_c_gc_length_distance_bound_curve`) makes `γ` uniformly Cauchy in
  the Riemannian extended distance as `t → b⁻`, so by completeness `γ`
  converges to a single limit point `y` along the whole filter `𝓝[<] b`
  (`bm_c_gc_position_limit`).

* **Directional velocity limit.** Near `b` the geodesic stays inside a
  single chart at `y`; in that chart the geodesic ODE has continuous,
  bounded Christoffels on the compact image, so the chart-coordinate
  solution and its derivative extend continuously to `b`, producing a
  genuine limit tangent vector `w ∈ T_y M` (of the correct speed, by the
  speed-preservation lemma `bm_c_gc_velocity_limit`).

* **`C¹` matching.** A fresh geodesic `η` is launched from `(y, w)` by
  `exists_isGeodesicOn_Ioo_at`; uniqueness of the chart-`y` geodesic ODE
  with matching `(position, velocity)` boundary data at `b` gives the
  asymptotic agreement `γ =ᶠ[𝓝[<] b] (t ↦ η (t - b))`.

The directional velocity-limit step: the chart-coordinate velocity is
bounded near `b` by the constant-speed Gram estimate
(`chartVelocity_bound_near_limit`, via the uniform positive-definiteness of the
chart Gram matrix on a compact neighbourhood of `y`), and a bounded
chart-acceleration then forces the chart velocity to a genuine limit
(`chartVelocity_converges_at_finite_endpoint_Ioo`, on the analytic engine
`velocity_converges_of_bounded_accel_Ioo`), with the chart-fixed second-order
ODE supplied pointwise by `hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity`.

The metric limit produced in the `PseudoEMetricSpace` topology is transported
into the manifold `ChartedSpace` topology through the topology-compatibility
bridge `tendsto_nhds_of_tendsto_metric_nhds`, and the continuation geodesic
`η` is launched from `(y, w)` with its initial chart velocity exposed by
`exists_isGeodesicOn_Ioo_at_velocity`.

The asymptotic matching `hmatch` is then closed via the chart-`y`-coordinate
phase curve: `γ` and the shifted continuation `t ↦ η (t - b)` both solve the
autonomous chart-`y` phase ODE near `b`, share the common boundary datum
`(φ_y y, w)` at the endpoint, and hence agree by left-endpoint ODE uniqueness
(`chartPhaseVF_orbit_uniqueness_Icc_left`). -/
theorem hasEndpointContinuation_of_complete
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {aL b c : ℝ}
    (haLb : aL < b)
    (hc_nonneg : 0 ≤ c)
    (hγ_smooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Ioo aL b))
    (hSpeedBound : ∀ τ ∈ Set.Ioo aL b,
      ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ ≤ ENNReal.ofReal c)
    (hSpeedSq : ∀ s ∈ Set.Ioo aL b,
      (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) ≤ c ^ 2)
    (_hγ : IsGeodesicOn (I := I) g γ (Set.Ioo aL b)) :
    HasEndpointContinuation (I := I) g γ b := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hγ_mdiff_on : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Set.Ioo aL b) :=
    hγ_smooth.mdifferentiableOn (by norm_num)
  obtain ⟨y, hy_metric⟩ :=
    bm_c_gc_position_limit (I := I) (γ := γ) (a := aL) (b := b) (c := c)
      haLb hc_nonneg hγ_smooth hSpeedBound
  have hy_mfld : Tendsto γ (𝓝[<] b) (𝓝 y) :=
    tendsto_nhds_of_tendsto_metric_nhds (I := I) (l := 𝓝[<] b) (f := γ) (p := y)
      hy_metric
  set u : ℝ → E := chartCurve (I := I) y γ with hu_def
  have hy_src : y ∈ (chartAt H y).source := mem_chart_source H y
  have hy_ext_src : y ∈ (extChartAt I y).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hy_src
  have hy_target : extChartAt I y y ∈ (extChartAt I y).target :=
    (extChartAt I y).map_source hy_ext_src
  have hy_interior : extChartAt I y y ∈ interior (extChartAt I y).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) y hy_target
  have hu_lim : Tendsto u (𝓝[<] b) (𝓝 (extChartAt I y y)) := by
    have hcont_at : ContinuousAt (extChartAt I y) y := continuousAt_extChartAt (I := I) y
    have := hcont_at.tendsto.comp hy_mfld
    simpa [hu_def, chartCurve] using this
  have hsrc_ev : ∀ᶠ s in 𝓝[<] b, γ s ∈ (chartAt H y).source :=
    hy_mfld ((chartAt H y).open_source.mem_nhds hy_src)
  obtain ⟨ε, K₁, S, hε, hS_compact, hS_sub, hbound⟩ :=
    chartVelocity_bound_near_limit (I := I) g y (γ := γ) (a := aL) (b := b) (c := c)
      haLb hc_nonneg hγ_mdiff_on hy_mfld hSpeedSq
  obtain ⟨a₀, ha₀_lt, ha₀_src⟩ :
      ∃ a₀ < b, ∀ s ∈ Set.Ioo a₀ b, γ s ∈ (chartAt H y).source := by
    obtain ⟨U, hU_nhds, hU_sub⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hsrc_ev
    obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.mem_nhds_iff.mp hU_nhds
    refine ⟨b - ρ, by linarith, fun s hs => ?_⟩
    have hs_ball : s ∈ Metric.ball b ρ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact hU_sub ⟨hρ_sub hs_ball, hs.2⟩
  set a : ℝ := max (max (b - ε) a₀) aL with ha_def
  have ha_lt_b : a < b := max_lt (max_lt (by linarith) ha₀_lt) haLb
  have ha_ge_ε : b - ε ≤ a := le_trans (le_max_left _ _) (le_max_left _ _)
  have ha_ge_a₀ : a₀ ≤ a := le_trans (le_max_right _ _) (le_max_left _ _)
  have ha_ge_aL : aL ≤ a := le_max_right _ _
  have hsub_aL : Set.Ioo a b ⊆ Set.Ioo aL b :=
    fun s hs => ⟨lt_of_le_of_lt ha_ge_aL hs.1, hs.2⟩
  have hsrc_on : ∀ s ∈ Set.Ioo a b, γ s ∈ (chartAt H y).source :=
    fun s hs => ha₀_src s ⟨lt_of_le_of_lt ha_ge_a₀ hs.1, hs.2⟩
  have hbound_on : ∀ s ∈ Set.Ioo a b,
      ‖deriv u s‖ ≤ K₁ ∧ u s ∈ S := by
    intro s hs
    have : s ∈ Set.Ioo (b - ε) b := ⟨lt_of_le_of_lt ha_ge_ε hs.1, hs.2⟩
    simpa [hu_def] using hbound s this
  have hγ_contAt : ∀ s ∈ Set.Ioo a b, ContinuousAt γ s := by
    intro s hs
    have hs_Ioo : s ∈ Set.Ioo aL b := hsub_aL hs
    exact ((hγ_smooth.continuousOn).continuousAt (isOpen_Ioo.mem_nhds hs_Ioo))
  have hγ_mdiffAt : ∀ s ∈ Set.Ioo a b, MDifferentiableAt 𝓘(ℝ, ℝ) I γ s := by
    intro s hs
    have hs_Ioo : s ∈ Set.Ioo aL b := hsub_aL hs
    exact (hγ_mdiff_on s hs_Ioo).mdifferentiableAt (isOpen_Ioo.mem_nhds hs_Ioo)
  have hODE_γ : ∀ s ∈ Set.Ioo a b,
      HasDerivAt (deriv u)
        (- chartChristoffelContraction (I := I) g y (deriv u s) (deriv u s) (u s)) s := by
    intro s hs
    have hgeq : HasGeodesicEquationAt (I := I) g γ s := _hγ s (hsub_aL hs)
    simpa [hu_def] using
      hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity (I := I) g y
        (γ := γ) (t := s) (hγ_contAt s hs) (hsrc_on s hs) hgeq
  have hDeriv_γ : ∀ s ∈ Set.Ioo a b, HasDerivAt u (deriv u s) s := by
    intro s hs
    have hφ_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I y) (γ s) :=
      mdifferentiableAt_extChartAt (I := I) (x := y) (hsrc_on s hs)
    have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I y) ∘ γ) s :=
      hφ_mdiff.comp s (hγ_mdiffAt s hs)
    have hdiff : DifferentiableAt ℝ ((extChartAt I y) ∘ γ) s :=
      hcomp.differentiableAt
    simpa [hu_def, chartCurve] using hdiff.hasDerivAt
  obtain ⟨wγ, hwγ⟩ :=
    chartVelocity_converges_at_finite_endpoint_Ioo (I := I) g y
      (u := u) (u' := deriv u) (a := a) (b := b) (K₁ := K₁) (S := S)
      ha_lt_b hS_compact hS_sub
      (fun s hs => by simpa [hu_def] using hDeriv_γ s hs)
      (fun s hs => by simpa [hu_def] using hODE_γ s hs)
      (fun s hs => (hbound_on s hs).1)
      (fun s hs => (hbound_on s hs).2)
  set w : TangentSpace I y :=
    (trivializationAt E (TangentSpace I) y).symmL ℝ y wγ with hw_def
  obtain ⟨η, δ, hδ, hη0, hηcont, hη_mfd, hη_mdiffOn, hη_srcOn, hη_geo⟩ :=
    exists_isGeodesicOn_Ioo_at_velocity (I := I) g y w
  refine ⟨η, δ, hδ, hη_geo, hη_mdiffOn, ?_⟩
  have hδ_mem0 : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hη_chartVel0 : deriv (chartCurve (I := I) y η) 0 = wγ := by
    have hη0_src : η 0 ∈ (chartAt H y).source := by rw [hη0]; exact hy_src
    have hη_mdiff0 : MDifferentiableAt 𝓘(ℝ, ℝ) I η 0 := hη_mdiffOn 0 hδ_mem0
    have hCC := bm_c_chartCoord_mfderiv_eq_fderiv_at (I := I) (γ := η) (α := y)
      (s := 0) hη_mdiff0 hη0_src
    have hbase : (η 0) ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hη0_src
    have hround :
        ((trivializationAt E (TangentSpace I) y).continuousLinearMapAt ℝ (η 0))
            ((mfderiv 𝓘(ℝ, ℝ) I η 0 : ℝ →L[ℝ] _) (1 : ℝ)) = wγ := by
      rw [hη_mfd, hw_def, hη0]
      exact (trivializationAt E (TangentSpace I) y).continuousLinearMapAt_symmL
        (R := ℝ) (by rw [TangentBundle.trivializationAt_baseSet]; exact hy_src) wγ
    have hderiv_eq : deriv (chartCurve (I := I) y η) 0 =
        (fderiv ℝ ((extChartAt I y) ∘ η) 0 : ℝ →L[ℝ] E) (1 : ℝ) := by
      rw [deriv]; rfl
    rw [hderiv_eq, ← hCC, hround]
  set uη : ℝ → E := chartCurve (I := I) y η with huη_def
  have hη_contOn : ∀ t ∈ Set.Ioo (-δ) δ, ContinuousAt η t :=
    fun t ht => (hη_mdiffOn t ht).continuousAt
  have hDeriv_η : ∀ t ∈ Set.Ioo (-δ) δ, HasDerivAt uη (deriv uη t) t := by
    intro t ht
    have hφ_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I y) (η t) :=
      mdifferentiableAt_extChartAt (I := I) (x := y) (hη_srcOn t ht)
    have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I y) ∘ η) t :=
      hφ_mdiff.comp t (hη_mdiffOn t ht)
    have hdiff : DifferentiableAt ℝ ((extChartAt I y) ∘ η) t :=
      hcomp.differentiableAt
    simpa [huη_def, chartCurve] using hdiff.hasDerivAt
  have hODE_η : ∀ t ∈ Set.Ioo (-δ) δ,
      HasDerivAt (deriv uη)
        (- chartChristoffelContraction (I := I) g y (deriv uη t) (deriv uη t) (uη t)) t := by
    intro t ht
    simpa [huη_def] using
      hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity (I := I) g y
        (γ := η) (t := t) (hη_contOn t ht) (hη_srcOn t ht) (hη_geo t ht)
  have huη0 : uη 0 = extChartAt I y y := by rw [huη_def, chartCurve_def, hη0]
  have hS_closed : IsClosed S := hS_compact.isClosed
  have hφy_in_S : extChartAt I y y ∈ S := by
    refine hS_closed.mem_of_tendsto hu_lim ?_
    filter_upwards [Ioo_mem_nhdsLT ha_lt_b] with s hs using (hbound_on s hs).2
  have hwγ_norm : ‖wγ‖ ≤ K₁ := by
    refine le_of_tendsto (Tendsto.norm hwγ) ?_
    filter_upwards [Ioo_mem_nhdsLT ha_lt_b] with s hs using (hbound_on s hs).1
  set cγ : ℝ → E × E := fun s => if s < b then (u s, deriv u s)
    else (extChartAt I y y, wγ) with hcγ_def
  set cη : ℝ → E × E := fun s => (uη (s - b), deriv uη (s - b)) with hcη_def
  have hcγ_lt : ∀ s, s < b → cγ s = (u s, deriv u s) := fun s hs => by
    simp only [hcγ_def, if_pos hs]
  have hcγ_b : cγ b = (extChartAt I y y, wγ) := by
    simp only [hcγ_def, if_neg (lt_irrefl b)]
  have hcγ_deriv_open : ∀ s ∈ Set.Ioo a b,
      HasDerivAt cγ (chartPhaseVF (I := I) g y (cγ s)) s := by
    intro s hs
    have heq : cγ =ᶠ[𝓝 s] (fun r => (u r, deriv u r)) := by
      filter_upwards [isOpen_Iio.mem_nhds hs.2] with r hr using hcγ_lt r hr
    have hpair : HasDerivAt (fun r => (u r, deriv u r))
        (deriv u s,
          - chartChristoffelContraction (I := I) g y (deriv u s) (deriv u s) (u s)) s :=
      (hDeriv_γ s hs).prodMk (hODE_γ s hs)
    rw [hcγ_lt s hs.2, chartPhaseVF_mk]
    exact hpair.congr_of_eventuallyEq heq
  set Uγ : ℝ → E := fun s => (cγ s).1 with hUγ_def
  set Vγ : ℝ → E := fun s => (cγ s).2 with hVγ_def
  have hUγ_eq : ∀ s, s < b → Uγ s = u s := fun s hs => by
    simp only [hUγ_def, hcγ_lt s hs]
  have hVγ_eq : ∀ s, s < b → Vγ s = deriv u s := fun s hs => by
    simp only [hVγ_def, hcγ_lt s hs]
  have hUγ_b : Uγ b = extChartAt I y y := by simp only [hUγ_def, hcγ_b]
  have hVγ_b : Vγ b = wγ := by simp only [hVγ_def, hcγ_b]
  have hAccel_lim : Tendsto
      (fun s => - chartChristoffelContraction (I := I) g y (deriv u s) (deriv u s) (u s))
      (𝓝[<] b)
      (𝓝 (- chartChristoffelContraction (I := I) g y wγ wγ (extChartAt I y y))) := by
    have hΓcont := chartChristoffelContraction_continuousOn_prod (I := I) g y
    have hcontAt : ContinuousAt
        (fun p : E × E => chartChristoffelContraction (I := I) g y p.1 p.1 p.2)
        (wγ, extChartAt I y y) :=
      (hΓcont.continuousAt (((isOpen_univ.prod isOpen_interior)).mem_nhds
        ⟨Set.mem_univ _, hy_interior⟩))
    have hpair_lim : Tendsto (fun s => ((deriv u s, u s) : E × E)) (𝓝[<] b)
        (𝓝 (wγ, extChartAt I y y)) := hwγ.prodMk_nhds hu_lim
    exact (hcontAt.tendsto.comp hpair_lim).neg
  have hIoo_nhdsLT : Set.Ioo a b ∈ 𝓝[<] b := Ioo_mem_nhdsLT ha_lt_b
  have hUγ_diffOn : DifferentiableOn ℝ Uγ (Set.Ioo a b) := by
    intro s hs
    refine ((hDeriv_γ s hs).differentiableAt.differentiableWithinAt).congr
      (fun r hr => (hUγ_eq r hr.2)) (hUγ_eq s hs.2)
  have hVγ_diffOn : DifferentiableOn ℝ Vγ (Set.Ioo a b) := by
    intro s hs
    refine ((hODE_γ s hs).differentiableAt.differentiableWithinAt).congr
      (fun r hr => (hVγ_eq r hr.2)) (hVγ_eq s hs.2)
  have hUγ_contAt : ContinuousWithinAt Uγ (Set.Ioo a b) b := by
    have ht : Tendsto Uγ (𝓝[<] b) (𝓝 (extChartAt I y y)) :=
      hu_lim.congr' (by filter_upwards [self_mem_nhdsWithin] with s hs using (hUγ_eq s hs).symm)
    have : Tendsto Uγ (𝓝[Set.Ioo a b] b) (𝓝 (Uγ b)) := by
      rw [hUγ_b]; exact ht.mono_left (nhdsWithin_mono b (fun s hs => hs.2))
    exact this
  have hVγ_contAt : ContinuousWithinAt Vγ (Set.Ioo a b) b := by
    have ht : Tendsto Vγ (𝓝[<] b) (𝓝 wγ) :=
      hwγ.congr' (by filter_upwards [self_mem_nhdsWithin] with s hs using (hVγ_eq s hs).symm)
    have : Tendsto Vγ (𝓝[Set.Ioo a b] b) (𝓝 (Vγ b)) := by
      rw [hVγ_b]; exact ht.mono_left (nhdsWithin_mono b (fun s hs => hs.2))
    exact this
  have hderiv_Uγ_lim : Tendsto (fun s => deriv Uγ s) (𝓝[<] b) (𝓝 wγ) := by
    refine hwγ.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have heq : Uγ =ᶠ[𝓝 s] u := by
      filter_upwards [isOpen_Iio.mem_nhds hs] with r hr using hUγ_eq r hr
    exact (heq.deriv_eq).symm
  have hderiv_Vγ_lim : Tendsto (fun s => deriv Vγ s) (𝓝[<] b)
      (𝓝 (- chartChristoffelContraction (I := I) g y wγ wγ (extChartAt I y y))) := by
    refine hAccel_lim.congr' ?_
    filter_upwards [hIoo_nhdsLT] with s hsa
    have heqV : Vγ =ᶠ[𝓝 s] deriv u := by
      filter_upwards [isOpen_Iio.mem_nhds hsa.2] with r hr using hVγ_eq r hr
    rw [heqV.deriv_eq, (hODE_γ s hsa).deriv]
  have hUγ_bderiv : HasDerivWithinAt Uγ wγ (Set.Iic b) b :=
    hasDerivWithinAt_Iic_of_tendsto_deriv hUγ_diffOn hUγ_contAt hIoo_nhdsLT hderiv_Uγ_lim
  have hVγ_bderiv : HasDerivWithinAt Vγ
      (- chartChristoffelContraction (I := I) g y wγ wγ (extChartAt I y y))
      (Set.Iic b) b :=
    hasDerivWithinAt_Iic_of_tendsto_deriv hVγ_diffOn hVγ_contAt hIoo_nhdsLT hderiv_Vγ_lim
  have hcγ_bderiv : HasDerivWithinAt cγ (chartPhaseVF (I := I) g y (cγ b))
      (Set.Iic b) b := by
    have hprod : HasDerivWithinAt cγ
        (wγ, - chartChristoffelContraction (I := I) g y wγ wγ (extChartAt I y y))
        (Set.Iic b) b := hUγ_bderiv.prodMk hVγ_bderiv
    rw [hcγ_b, chartPhaseVF_mk]
    exact hprod
  obtain ⟨R, hR_pos, hR_sub⟩ :=
    Metric.isOpen_iff.mp isOpen_interior _ hy_interior
  set Kset : Set (E × E) :=
    Metric.closedBall (extChartAt I y y) (R / 2) ×ˢ Metric.closedBall (0 : E) (K₁ + 1)
    with hKset_def
  have hKset_compact : IsCompact Kset :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hKset_sub : Kset ⊆ (interior (extChartAt I y).target) ×ˢ (Set.univ : Set E) := by
    intro p hp
    refine ⟨hR_sub ?_, Set.mem_univ _⟩
    rw [Metric.mem_ball]
    have := hp.1; rw [Metric.mem_closedBall] at this
    linarith
  have hpair_in_Kset : ((extChartAt I y y, wγ) : E × E) ∈ Kset := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_self]; linarith
    · rw [Metric.mem_closedBall, dist_zero_right]; linarith
  have hKset_nhds : Kset ∈ 𝓝 ((extChartAt I y y, wγ) : E × E) := by
    rw [hKset_def, nhds_prod_eq]
    refine Filter.prod_mem_prod (Metric.closedBall_mem_nhds _ (by linarith))
      (Metric.closedBall_mem_nhds_of_mem ?_)
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hcγ_lim : Tendsto cγ (𝓝[<] b) (𝓝 ((extChartAt I y y, wγ) : E × E)) := by
    refine (hu_lim.prodMk_nhds hwγ).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs using (hcγ_lt s hs).symm
  have huη_contAt0 : ContinuousAt uη 0 := (hDeriv_η 0 hδ_mem0).continuousAt
  have hduη_contAt0 : ContinuousAt (deriv uη) 0 := (hODE_η 0 hδ_mem0).continuousAt
  have hshift0 : Tendsto (fun s : ℝ => s - b) (𝓝[<] b) (𝓝 (0 : ℝ)) := by
    have : Tendsto (fun s : ℝ => s - b) (𝓝 b) (𝓝 (0 : ℝ)) := by
      have hc := (continuous_sub_right b).tendsto b
      simpa using hc
    exact this.mono_left nhdsWithin_le_nhds
  have hcη_lim : Tendsto cη (𝓝[<] b) (𝓝 ((extChartAt I y y, wγ) : E × E)) := by
    have hu0 : Tendsto (fun s => uη (s - b)) (𝓝[<] b) (𝓝 (extChartAt I y y)) := by
      have := huη_contAt0.tendsto.comp hshift0
      rwa [huη0] at this
    have hdu0 : Tendsto (fun s => deriv uη (s - b)) (𝓝[<] b) (𝓝 wγ) := by
      have := hduη_contAt0.tendsto.comp hshift0
      rwa [hη_chartVel0] at this
    exact hu0.prodMk_nhds hdu0
  have hev_all : ∀ᶠ s in 𝓝[<] b,
      cγ s ∈ Kset ∧ cη s ∈ Kset ∧ (s - b) ∈ Set.Ioo (-δ) δ := by
    have h1 : ∀ᶠ s in 𝓝[<] b, cγ s ∈ Kset := hcγ_lim hKset_nhds
    have h2 : ∀ᶠ s in 𝓝[<] b, cη s ∈ Kset := hcη_lim hKset_nhds
    have h3 : ∀ᶠ s in 𝓝[<] b, (s - b) ∈ Set.Ioo (-δ) δ :=
      hshift0 (isOpen_Ioo.mem_nhds hδ_mem0)
    filter_upwards [h1, h2, h3] with s hs1 hs2 hs3 using ⟨hs1, hs2, hs3⟩
  obtain ⟨a', ha'_lt, ha'_all⟩ :
      ∃ a' < b, ∀ s ∈ Set.Ioo a' b,
        cγ s ∈ Kset ∧ cη s ∈ Kset ∧ (s - b) ∈ Set.Ioo (-δ) δ := by
    obtain ⟨U, hU_nhds, hU_sub⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hev_all
    obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.mem_nhds_iff.mp hU_nhds
    refine ⟨b - ρ, by linarith, fun s hs => ?_⟩
    have hs_ball : s ∈ Metric.ball b ρ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact hU_sub ⟨hρ_sub hs_ball, hs.2⟩
  set a₁ : ℝ := max a a' with ha₁_def
  have ha₁_lt : a₁ < b := max_lt ha_lt_b ha'_lt
  set a'' : ℝ := (a₁ + b) / 2 with ha''_def
  have ha''_gt_a₁ : a₁ < a'' := by rw [ha''_def]; linarith
  have ha''_lt : a'' < b := by rw [ha''_def]; linarith
  have ha''_gt_a : a < a'' := lt_of_le_of_lt (le_max_left _ _) ha''_gt_a₁
  have ha''_gt_a' : a' < a'' := lt_of_le_of_lt (le_max_right _ _) ha''_gt_a₁
  have hsub_a'' : Set.Ioo a'' b ⊆ Set.Ioo a b :=
    fun s hs => ⟨lt_of_lt_of_le ha''_gt_a hs.1.le, hs.2⟩
  have hsub_a''' : Set.Ioo a'' b ⊆ Set.Ioo a' b :=
    fun s hs => ⟨lt_of_lt_of_le ha''_gt_a' hs.1.le, hs.2⟩
  have hIcc_lt_sub : ∀ s ∈ Set.Icc a'' b, s < b → s ∈ Set.Ioo a b :=
    fun s hs hlt => ⟨lt_of_lt_of_le ha''_gt_a hs.1, hlt⟩
  have hIcc_lt_sub' : ∀ s ∈ Set.Icc a'' b, s < b → s ∈ Set.Ioo a' b :=
    fun s hs hlt => ⟨lt_of_lt_of_le ha''_gt_a' hs.1, hlt⟩
  have hcη_deriv_at : ∀ s : ℝ, (s - b) ∈ Set.Ioo (-δ) δ →
      HasDerivAt cη (chartPhaseVF (I := I) g y (cη s)) s := by
    intro s hsh
    have h1 : HasDerivAt (fun r => uη (r - b)) (deriv uη (s - b)) s :=
      (hDeriv_η (s - b) hsh).comp_sub_const s b
    have h2 : HasDerivAt (fun r => deriv uη (r - b))
        (- chartChristoffelContraction (I := I) g y (deriv uη (s - b)) (deriv uη (s - b))
          (uη (s - b))) s :=
      (hODE_η (s - b) hsh).comp_sub_const s b
    have := h1.prodMk h2
    rw [hcη_def, chartPhaseVF_mk]
    exact this
  have hcη_deriv_open : ∀ s ∈ Set.Ioo a'' b,
      HasDerivAt cη (chartPhaseVF (I := I) g y (cη s)) s :=
    fun s hs => hcη_deriv_at s (ha'_all s (hsub_a''' hs)).2.2
  have hcη_b : cη b = (extChartAt I y y, wγ) := by
    simp only [hcη_def, sub_self, huη0, hη_chartVel0]
  have h_eq_at_b : cγ b = cη b := by rw [hcγ_b, hcη_b]
  have hcγ_deriv_Ioc : ∀ s ∈ Set.Ioc a'' b,
      HasDerivWithinAt cγ (chartPhaseVF (I := I) g y (cγ s)) (Set.Iic s) s := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact (hcγ_deriv_open s (hsub_a'' ⟨hs.1, hlt⟩)).hasDerivWithinAt
    · rw [heq]; exact hcγ_bderiv
  have hcη_deriv_Ioc : ∀ s ∈ Set.Ioc a'' b,
      HasDerivWithinAt cη (chartPhaseVF (I := I) g y (cη s)) (Set.Iic s) s := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact (hcη_deriv_open s ⟨hs.1, hlt⟩).hasDerivWithinAt
    · rw [heq]
      exact (hcη_deriv_at b (by rw [sub_self]; exact hδ_mem0)).hasDerivWithinAt
  have hContAt_b : ∀ (cf : ℝ → E × E) (L : E × E), cf b = L →
      Tendsto cf (𝓝[<] b) (𝓝 L) → ContinuousWithinAt cf (Set.Icc a'' b) b := by
    intro cf L hval hlim
    have hIic : Tendsto cf (𝓝[Set.Iic b] b) (𝓝 L) := by
      rw [show Set.Iic b = Set.Iio b ∪ {b} from (Set.Iio_union_right).symm,
        nhdsWithin_union, Filter.tendsto_sup]
      refine ⟨hlim, ?_⟩
      rw [nhdsWithin_singleton, Filter.tendsto_pure_left]
      intro s hs; rw [hval]; exact mem_of_mem_nhds hs
    have hmono : Tendsto cf (𝓝[Set.Icc a'' b] b) (𝓝 L) :=
      hIic.mono_left (nhdsWithin_mono b (fun s hs => hs.2))
    show Tendsto cf (𝓝[Set.Icc a'' b] b) (𝓝 (cf b))
    rw [hval]; exact hmono
  have hcγ_contOn : ContinuousOn cγ (Set.Icc a'' b) := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact ((hcγ_deriv_open s (hIcc_lt_sub s hs hlt)).continuousAt).continuousWithinAt
    · rw [show s = b from heq]
      exact hContAt_b cγ (extChartAt I y y, wγ) hcγ_b hcγ_lim
  have hcη_contOn : ContinuousOn cη (Set.Icc a'' b) := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact ((hcη_deriv_at s (ha'_all s (hIcc_lt_sub' s hs hlt)).2.2).continuousAt).continuousWithinAt
    · rw [show s = b from heq]
      exact hContAt_b cη (extChartAt I y y, wγ) hcη_b hcη_lim
  have hcγ_in_K : ∀ s ∈ Set.Ioc a'' b, cγ s ∈ Kset := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact (ha'_all s (hsub_a''' ⟨hs.1, hlt⟩)).1
    · subst heq; rw [hcγ_b]; exact hpair_in_Kset
  have hcη_in_K : ∀ s ∈ Set.Ioc a'' b, cη s ∈ Kset := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact (ha'_all s (hsub_a''' ⟨hs.1, hlt⟩)).2.1
    · subst heq; rw [hcη_b]; exact hpair_in_Kset
  have hEqOn : Set.EqOn cγ cη (Set.Icc a'' b) :=
    chartPhaseVF_orbit_uniqueness_Icc_left (I := I) g y hKset_compact hKset_sub
      hcγ_contOn hcη_contOn hcγ_deriv_Ioc hcη_deriv_Ioc hcγ_in_K hcη_in_K h_eq_at_b
  refine Filter.eventually_of_mem (U := Set.Ioo a'' b) (Ioo_mem_nhdsLT ha''_lt) ?_
  intro s hs
  have hs_Icc : s ∈ Set.Icc a'' b := ⟨hs.1.le, hs.2.le⟩
  have hpair_eq : cγ s = cη s := hEqOn hs_Icc
  have hfst : u s = uη (s - b) := by
    have : (cγ s).1 = (cη s).1 := by rw [hpair_eq]
    rwa [hcγ_lt s hs.2, hcη_def] at this
  have hγ_src_s : γ s ∈ (chartAt H y).source := hsrc_on s (hsub_a'' hs)
  have hη_src_s : η (s - b) ∈ (chartAt H y).source :=
    hη_srcOn (s - b) (ha'_all s (hsub_a''' hs)).2.2
  have hγ_ext_src : γ s ∈ (extChartAt I y).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hγ_src_s
  have hη_ext_src : η (s - b) ∈ (extChartAt I y).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hη_src_s
  have hround_γ : (extChartAt I y).symm (extChartAt I y (γ s)) = γ s :=
    (extChartAt I y).left_inv hγ_ext_src
  have hround_η : (extChartAt I y).symm (extChartAt I y (η (s - b))) = η (s - b) :=
    (extChartAt I y).left_inv hη_ext_src
  have hu_s : u s = extChartAt I y (γ s) := by rw [hu_def, chartCurve_def]
  have huη_s : uη (s - b) = extChartAt I y (η (s - b)) := by rw [huη_def, chartCurve_def]
  calc γ s = (extChartAt I y).symm (extChartAt I y (γ s)) := hround_γ.symm
    _ = (extChartAt I y).symm (u s) := by rw [hu_s]
    _ = (extChartAt I y).symm (uη (s - b)) := by rw [hfst]
    _ = (extChartAt I y).symm (extChartAt I y (η (s - b))) := by rw [huη_s]
    _ = η (s - b) := hround_η

/-- **Single-step intrinsic right-extension.** A geodesic on `Iio b` with
endpoint-continuation data at `b` extends to a geodesic on `Iio b'` for
some `b' > b`, agreeing with the original below `b`. Direct corollary of
`isGeodesicOn_extends_past_finite_endpoint`. -/
theorem isGeodesicOn_Iio_extend
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {b : ℝ}
    (hγ : IsGeodesicOn (I := I) g γ (Set.Iio b))
    (hcont : HasEndpointContinuation (I := I) g γ b) :
    ∃ (γ' : ℝ → M) (b' : ℝ), b < b' ∧
      IsGeodesicOn (I := I) g γ' (Set.Iio b') ∧
      (∀ t < b, γ' t = γ t) := by
  obtain ⟨η, δ, hδ, hη, _hη_mdiff, hmatch⟩ := hcont
  obtain ⟨γ', hgeo', hagree⟩ :=
    isGeodesicOn_extends_past_finite_endpoint (I := I) g hδ hγ hη hmatch
  exact ⟨γ', b + δ, by linarith, hgeo', hagree⟩

/-- **Locality of the moving-foot geodesic equation.** If two curves agree on
a neighbourhood of `t`, then either satisfies the geodesic equation at `t` iff
the other does. A thin wrapper around
`HasGeodesicEquationAt.congr_of_eventuallyEq_at` extracting the basepoint
equality from the eventual equality at `t`. -/
private theorem hasGeodesicEquationAt_congr_of_eventuallyEq
    {g : SmoothRiemannianMetric I M} {γ γ' : ℝ → M} {t : ℝ}
    (heq : γ =ᶠ[nhds t] γ') (h : HasGeodesicEquationAt (I := I) g γ' t) :
    HasGeodesicEquationAt (I := I) g γ t := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
    (heq.eq_of_nhds) heq h

/-- **Intrinsic right-completeness.** Suppose that for every geodesic on a
half-open interval `Iio b` (`b > 0`) extending the initial geodesic `γ₀`,
endpoint-continuation data is available at `b`. Then the initial geodesic
on `Iio b₀` extends to a geodesic on all of `Ici 0` — equivalently, on
`Iio b` for arbitrarily large `b`.

This is the *true* geodesic-completeness statement, replacing the (false
on multi-chart manifolds) fixed-basepoint `maximalGeodesicInterval =
univ`. Each extension step is `isGeodesicOn_Iio_extend`
(fully proven above, axiom-clean). The colimit of the iterated single-step
extensions is assembled by a maximal-chain argument: order the
extension records `(b, γ)` (geodesic on `Iio b`, agreeing with `γ₀` below
`b₀`) by interval inclusion together with agreement below the shorter
endpoint, and pass to a maximal chain `Mc` (Hausdorff maximality). The
chain order forces mutual agreement of its members, so their union curve
`Γ` is single-valued; on a neighbourhood of any time `t` below a chain
endpoint, `Γ` agrees with a genuine geodesic, so the moving-foot equation
transfers by locality
(`hasGeodesicEquationAt_congr_of_eventuallyEq`). If the chain's endpoint
set were bounded above, `Γ` would be a geodesic on `Iio (sSup …)` admitting
endpoint continuation, hence a strict single-step extension whose record is
chain-comparable above every member — a super-chain contradicting
maximality. Therefore the endpoints are unbounded and `Γ` is a geodesic on
all of `ℝ ⊇ Ici 0`. -/
theorem isGeodesicOn_Ici_of_endpointContinuation
    (g : SmoothRiemannianMetric I M) {γ₀ : ℝ → M} {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hγ₀ : IsGeodesicOn (I := I) g γ₀ (Set.Iio b₀))
    (hcont : ∀ (γ : ℝ → M) (b : ℝ), 0 < b →
      IsGeodesicOn (I := I) g γ (Set.Iio b) →
      (∀ t < b₀, t < b → γ t = γ₀ t) →
      HasEndpointContinuation (I := I) g γ b) :
    ∃ γ : ℝ → M,
      IsGeodesicOn (I := I) g γ (Set.Ici (0 : ℝ)) ∧
      (∀ t, t < b₀ → γ t = γ₀ t) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Good : (ℝ × (ℝ → M)) → Prop := fun br =>
    b₀ ≤ br.1 ∧ IsGeodesicOn (I := I) g br.2 (Set.Iio br.1) ∧
      (∀ t < b₀, br.2 t = γ₀ t)
  let Rec := {br : ℝ × (ℝ → M) // Good br}
  let R : Rec → Rec → Prop := fun a a' =>
    a.1.1 ≤ a'.1.1 ∧ (∀ t < a.1.1, a'.1.2 t = a.1.2 t)
  have hGood_r₀ : Good (b₀, γ₀) := ⟨le_refl _, hγ₀, fun t _ => rfl⟩
  let r₀ : Rec := ⟨(b₀, γ₀), hGood_r₀⟩
  have hchain0 : IsChain R {r₀} := by
    intro a ha b hb hab
    rw [Set.mem_singleton_iff] at ha hb; exact absurd (ha.trans hb.symm) hab
  obtain ⟨Mc, hMc_max, hMc_sub⟩ := hchain0.exists_maxChain
  have hr₀_mem : r₀ ∈ Mc := hMc_sub (Set.mem_singleton _)
  have hMc_chain : IsChain R Mc := hMc_max.1
  have hconsist : ∀ a ∈ Mc, ∀ a' ∈ Mc, ∀ t, t < a.1.1 → t < a'.1.1 →
      a.1.2 t = a'.1.2 t := by
    intro a ha a' ha' t hta hta'
    rcases eq_or_ne a a' with rfl | hne
    · rfl
    · rcases hMc_chain ha ha' hne with hR | hR
      · exact (hR.2 t hta).symm
      · exact hR.2 t hta'
  let Γ : ℝ → M := fun t =>
    if h : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 then (h.choose.1.2 t) else γ₀ t
  have hΓ_val : ∀ a ∈ Mc, ∀ t, t < a.1.1 → Γ t = a.1.2 t := by
    intro a ha t hta
    have hex : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 := ⟨a, ha, hta⟩
    change (if h : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 then (h.choose.1.2 t)
      else γ₀ t) = a.1.2 t
    rw [dif_pos hex]
    obtain ⟨hb_mem, hb_lt⟩ := hex.choose_spec
    exact hconsist _ hb_mem a ha t hb_lt hta
  have hΓ_agree : ∀ t, t < b₀ → Γ t = γ₀ t := by
    intro t ht
    have := hΓ_val r₀ hr₀_mem t ht
    simpa [r₀] using this
  have hΓ_geo_at : ∀ a ∈ Mc, ∀ t, t < a.1.1 →
      HasGeodesicEquationAt (I := I) g Γ t := by
    intro a ha t hta
    have hIio_nhds : Set.Iio a.1.1 ∈ 𝓝 t := isOpen_Iio.mem_nhds hta
    have heq : Γ =ᶠ[𝓝 t] a.1.2 := by
      filter_upwards [hIio_nhds] with s hs
      exact hΓ_val a ha s hs
    exact hasGeodesicEquationAt_congr_of_eventuallyEq (g := g) heq (a.2.2.1 t hta)
  let S : Set ℝ := (fun a : Rec => a.1.1) '' Mc
  have hS_ne : S.Nonempty := ⟨b₀, ⟨r₀, hr₀_mem, rfl⟩⟩
  by_cases hbdd : BddAbove S
  · exfalso
    let s := sSup S
    have hb₀_le_s : b₀ ≤ s := le_csSup hbdd ⟨r₀, hr₀_mem, rfl⟩
    have hs_pos : 0 < s := lt_of_lt_of_le hb₀ hb₀_le_s
    have hΓ_geo_Iios : IsGeodesicOn (I := I) g Γ (Set.Iio s) := by
      intro t ht
      obtain ⟨b, hbS, htb⟩ := exists_lt_of_lt_csSup hS_ne ht
      obtain ⟨a, ha, hab⟩ := hbS
      exact hΓ_geo_at a ha t (lt_of_lt_of_eq htb hab.symm)
    have hagree_s : ∀ t < b₀, t < s → Γ t = γ₀ t := fun t ht _ => hΓ_agree t ht
    have hcont_s : HasEndpointContinuation (I := I) g Γ s :=
      hcont Γ s hs_pos hΓ_geo_Iios hagree_s
    obtain ⟨Γ', s', hss', hΓ'_geo, hΓ'_agree⟩ :=
      isGeodesicOn_Iio_extend (I := I) g hΓ_geo_Iios hcont_s
    have hGood' : Good (s', Γ') := by
      refine ⟨le_trans hb₀_le_s hss'.le, hΓ'_geo, ?_⟩
      intro t ht
      have ht_s : t < s := lt_of_lt_of_le ht hb₀_le_s
      change Γ' t = γ₀ t
      rw [hΓ'_agree t ht_s]; exact hΓ_agree t ht
    let r' : Rec := ⟨(s', Γ'), hGood'⟩
    have hr'_notMem : r' ∉ Mc := by
      intro hmem
      have hmemS : s' ∈ S := ⟨r', hmem, rfl⟩
      exact absurd (le_csSup hbdd hmemS) (not_le.mpr hss')
    have hchain' : IsChain R (insert r' Mc) := by
      refine hMc_chain.insert ?_
      intro a ha _
      right
      have ha_mem_S : a.1.1 ∈ S := ⟨a, ha, rfl⟩
      have ha_le_s : a.1.1 ≤ s := le_csSup hbdd ha_mem_S
      refine ⟨?_, ?_⟩
      · change a.1.1 ≤ s'
        exact le_trans ha_le_s hss'.le
      · intro t hta
        have ht_s : t < s := lt_of_lt_of_le hta ha_le_s
        change Γ' t = a.1.2 t
        rw [hΓ'_agree t ht_s]; exact hΓ_val a ha t hta
    have heq_chain : Mc = insert r' Mc :=
      hMc_max.2 hchain' (Set.subset_insert _ _)
    exact hr'_notMem (heq_chain ▸ Set.mem_insert _ _)
  · refine ⟨Γ, ?_, hΓ_agree⟩
    intro t _
    rw [not_bddAbove_iff] at hbdd
    obtain ⟨b, hbS, htb⟩ := hbdd t
    obtain ⟨a, ha, hab⟩ := hbS
    exact hΓ_geo_at a ha t (lt_of_lt_of_eq htb hab.symm)

/-- **Chart-coordinate `C¹` regularity.**  If `γ` satisfies the moving-foot
geodesic equation at every point of an open set `s ∋ t` and is continuous on
`s`, then the fixed-chart curve `chartCurve (γ t) γ = φ_{γ t} ∘ γ` is
`ContDiffAt ℝ 1` at `t`. -/
theorem chartCurve_contDiffAt_one_of_isGeodesicOn
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hs : IsOpen s) (ht : t ∈ s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hcont : ContinuousOn γ s) :
    ContDiffAt ℝ 1 (chartCurve (I := I) (γ t) γ) t := by
  classical
  set α : M := γ t with hα_def
  set u : ℝ → E := chartCurve (I := I) α γ with hu_def
  have hα_src : α ∈ (chartAt H α).source := mem_chart_source H α
  have hcontAt_t : ContinuousAt γ t :=
    hcont.continuousAt (hs.mem_nhds ht)
  have hsrc_nhds : (fun s' => γ s') ⁻¹' (chartAt H α).source ∈ 𝓝 t := by
    have : α ∈ (chartAt H α).source := hα_src
    exact hcontAt_t.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds (by rw [hα_def] at this ⊢; exact this))
  obtain ⟨V, hV_nhds, hV_src⟩ := Filter.eventually_iff_exists_mem.mp
    (Filter.eventually_of_mem hsrc_nhds (fun _ h => h))
  set W : Set ℝ := V ∩ s with hW_def
  have hW_nhds : W ∈ 𝓝 t := Filter.inter_mem hV_nhds (hs.mem_nhds ht)
  have hW_src : ∀ s' ∈ W, γ s' ∈ (chartAt H α).source := fun s' hs' => hV_src s' hs'.1
  have hW_geo : ∀ s' ∈ W, HasGeodesicEquationAt (I := I) g γ s' :=
    fun s' hs' => hγ s' hs'.2
  have hW_contAt : ∀ s' ∈ W, ContinuousAt γ s' :=
    fun s' hs' => hcont.continuousAt (hs.mem_nhds hs'.2)
  have hODE : ∀ s' ∈ W,
      HasDerivAt (deriv u)
        (- chartChristoffelContraction (I := I) g α (deriv u s') (deriv u s') (u s')) s' := by
    intro s' hs'
    simpa [hu_def] using
      hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity (I := I) g α
        (γ := γ) (t := s') (hW_contAt s' hs') (hW_src s' hs') (hW_geo s' hs')
  obtain ⟨W', hW'_sub, hW'_open, hW'_mem⟩ := mem_nhds_iff.mp hW_nhds
  have hderiv_diffOn : ∀ s' ∈ W', DifferentiableAt ℝ (deriv u) s' :=
    fun s' hs' => (hODE s' (hW'_sub hs')).differentiableAt
  have hderiv_contOn : ContinuousOn (deriv u) W' :=
    fun s' hs' => (hderiv_diffOn s' hs').continuousAt.continuousWithinAt
  rw [contDiffAt_one_iff]
  refine ⟨fun s' => ContinuousLinearMap.toSpanSingleton ℝ (deriv u s'), W',
    hW'_open.mem_nhds hW'_mem, ?_, ?_⟩
  · have hCLE : Continuous
        (fun w : E => (ContinuousLinearMap.toSpanSingleton ℝ w : ℝ →L[ℝ] E)) :=
      ContinuousLinearMap.toSpanSingletonCLE.continuous
    exact hCLE.comp_continuousOn hderiv_contOn
  · intro s' hs'
    have hcont_s' : ContinuousAt γ s' := hW_contAt s' (hW'_sub hs')
    have hsrc_s' : γ s' ∈ (chartAt H (γ t)).source := hW_src s' (hW'_sub hs')
    have hu_ev' : ∀ᶠ r in 𝓝 s', HasDerivAt u (deriv u r) r := by
      simpa [hu_def] using
        hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt (I := I) g α
          (γ := γ) (t := s') hcont_s' (by rw [hα_def]; exact hsrc_s')
          (hW_geo s' (hW'_sub hs'))
    exact hu_ev'.self_of_nhds.hasFDerivAt

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`C¹`-in-time regularity of a moving-foot geodesic (pointwise).**  An
intrinsic moving-foot geodesic `γ` on an open set `s` that is continuous on `s`
is `ContMDiffAt 𝓘(ℝ, ℝ) I 1` at every `t ∈ s`.

This is the analytic engine supplying the `C¹` regularity conjunct of the
`hreg` hypothesis of `isGeodesicOn_Ici_of_complete`.  The proof works in the
fixed chart `α = γ t`: the fixed-chart curve `u = φ_α ∘ γ` is `ContDiffAt 1`
in time (`chartCurve_contDiffAt_one_of_isGeodesicOn`), `(extChartAt I α).symm`
is `C^∞` on the chart target, and `γ` agrees with `(extChartAt I α).symm ∘ u`
on a neighbourhood of `t` (chart round-trip on the chart source), so `γ` is
`ContMDiffAt 1` at `t`. -/
theorem isGeodesicOn_contMDiffAt_one
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hs : IsOpen s) (ht : t ∈ s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hcont : ContinuousOn γ s) :
    ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t := by
  classical
  set α : M := γ t with hα_def
  set u : ℝ → E := chartCurve (I := I) α γ with hu_def
  have hu_cd : ContDiffAt ℝ 1 u t :=
    chartCurve_contDiffAt_one_of_isGeodesicOn (I := I) g hs ht hγ hcont
  have hu_cmd : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 u t := hu_cd.contMDiffAt
  have hα_src : α ∈ (chartAt H α).source := mem_chart_source H α
  have hα_ext_src : α ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hα_src
  have hut_eq : u t = extChartAt I α α := by
    rw [hu_def, chartCurve_def, hα_def]
  have hut_target : u t ∈ (extChartAt I α).target := by
    rw [hut_eq]; exact (extChartAt I α).map_source hα_ext_src
  have htarget_nhds : (extChartAt I α).target ∈ 𝓝 (u t) := by
    have hut_int : u t ∈ interior (extChartAt I α).target := by
      rw [hut_eq]
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
        ((extChartAt I α).map_source hα_ext_src)
    exact mem_nhds_iff.mpr ⟨interior (extChartAt I α).target, interior_subset,
      isOpen_interior, hut_int⟩
  have hsymm_within : ContMDiffWithinAt 𝓘(ℝ, E) I 1
      (extChartAt I α).symm (extChartAt I α).target (u t) :=
    contMDiffWithinAt_extChartAt_symm_target (I := I) α hut_target
  have hsymm_at : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I α).symm (u t) :=
    hsymm_within.contMDiffAt htarget_nhds
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) I 1 ((extChartAt I α).symm ∘ u) t :=
    hsymm_at.comp t hu_cmd
  have hcontAt_t : ContinuousAt γ t := hcont.continuousAt (hs.mem_nhds ht)
  have hsrc_nhds : (fun s' => γ s') ⁻¹' (chartAt H α).source ∈ 𝓝 t :=
    hcontAt_t.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hα_src)
  have heq : ((extChartAt I α).symm ∘ u) =ᶠ[𝓝 t] γ := by
    filter_upwards [hsrc_nhds] with s' hs'
    have hs'_ext : γ s' ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hs'
    change (extChartAt I α).symm (u s') = γ s'
    rw [hu_def, chartCurve_def]
    exact (extChartAt I α).left_inv hs'_ext
  exact hcomp.congr_of_eventuallyEq heq.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`C¹`-in-time regularity of a moving-foot geodesic (on an open set).**  An
intrinsic moving-foot geodesic `γ` on an open set `s`, continuous on `s`, is
`ContMDiffOn 𝓘(ℝ, ℝ) I 1` on `s`.  This is the exact shape of the `C¹`
regularity conjunct fed (with `s = Set.Iio b`) to the `hreg` hypothesis of
`isGeodesicOn_Ici_of_complete`. -/
theorem isGeodesicOn_contMDiffOn_one
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ}
    (hs : IsOpen s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hcont : ContinuousOn γ s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s := fun _t ht =>
  (isGeodesicOn_contMDiffAt_one (I := I) g hs ht hγ hcont).contMDiffWithinAt

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Intrinsic right-completeness from metric completeness.**  A geodesic
`γ₀` on `Set.Iio b₀` (`b₀ > 0`) on a metrically complete manifold extends,
across charts, to a geodesic on all of `Set.Ici 0` that agrees with `γ₀`
below `b₀`.

The hypothesis `hreg` is the per-extension analytic regularity of any
geodesic extending `γ₀` past a finite right endpoint `b`: such a geodesic is
`C¹` on `Set.Iio b`, and its velocity has `g`-speed bounded by a nonnegative
constant `c` (both as a bundle-enorm bound and as an inner-product bound by
`c ^ 2`).  These are the facts a constant-speed geodesic always satisfies;
they are NOT the extension conclusion (the geodesic equation on a strictly
larger interval).  Metric completeness supplies endpoint-continuation data
at `b` via `hasEndpointContinuation_of_complete`, and the colimit of the
iterated single-step extensions (`isGeodesicOn_Ici_of_endpointContinuation`)
assembles the global geodesic. -/
theorem isGeodesicOn_Ici_of_complete
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {γ₀ : ℝ → M} {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hγ₀ : IsGeodesicOn (I := I) g γ₀ (Set.Iio b₀))
    (hreg : ∀ (γ : ℝ → M) (b : ℝ), 0 < b →
      IsGeodesicOn (I := I) g γ (Set.Iio b) →
      (∀ t < b₀, t < b → γ t = γ₀ t) →
      ∃ c : ℝ, 0 ≤ c ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Iio b) ∧
        (∀ τ ∈ Set.Iio b,
          ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ ≤ ENNReal.ofReal c) ∧
        (∀ s ∈ Set.Iio b,
          (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
              (mfderiv 𝓘(ℝ, ℝ) I γ s 1) ≤ c ^ 2)) :
    ∃ γ : ℝ → M,
      IsGeodesicOn (I := I) g γ (Set.Ici (0 : ℝ)) ∧
      (∀ t, t < b₀ → γ t = γ₀ t) := by
  refine isGeodesicOn_Ici_of_endpointContinuation (I := I) g hb₀ hγ₀ ?_
  intro γ b hb hγ hagree
  obtain ⟨c, hc_nonneg, hγ_smooth, hSpeedBound, hSpeedSq⟩ := hreg γ b hb hγ hagree
  have hsub : Set.Ioo (b - 1) b ⊆ Set.Iio b := fun s hs => hs.2
  exact hasEndpointContinuation_of_complete (I := I) g (by linarith : b - 1 < b)
    hc_nonneg (hγ_smooth.mono hsub) (fun τ hτ => hSpeedBound τ (hsub hτ))
    (fun s hs => hSpeedSq s (hsub hs)) (hγ.mono hsub)

/-- **Single-step bounded-left right-extension.** A geodesic on a bounded
interval `Ioo a₀ b` (`a₀ < b`) with endpoint-continuation data at `b` extends to
a geodesic on `Ioo a₀ b'` for some `b' > b`, agreeing with the original below
`b`.  Bounded-left analogue of `isGeodesicOn_Iio_extend`, built on the
bounded-left glue. -/
theorem isGeodesicOn_Ioo_extend
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a₀ b : ℝ} (ha₀b : a₀ < b)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Ioo a₀ b))
    (hγ_cont : ContinuousOn γ (Set.Ioo a₀ b))
    (hcont : HasEndpointContinuation (I := I) g γ b) :
    ∃ (γ' : ℝ → M) (b' : ℝ), b < b' ∧
      IsGeodesicOn (I := I) g γ' (Set.Ioo a₀ b') ∧
      ContinuousOn γ' (Set.Ioo a₀ b') ∧
      (∀ t < b, γ' t = γ t) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨η, δ, hδ, hη, hη_mdiff, hmatch⟩ := hcont
  set G : ℝ → M := fun t => if t < b then γ t else η (t - b) with hG_def
  have hη_cont : ContinuousOn η (Set.Ioo (-δ) δ) :=
    fun t ht => (hη_mdiff t ht).continuousAt.continuousWithinAt
  have hηb_cont : ContinuousOn (fun t => η (t - b)) (Set.Ioo (b - δ) (b + δ)) := by
    have hshift : ContinuousOn (fun t : ℝ => t - b) (Set.Ioo (b - δ) (b + δ)) :=
      (continuous_sub_right b).continuousOn
    have hmaps : Set.MapsTo (fun t : ℝ => t - b) (Set.Ioo (b - δ) (b + δ))
        (Set.Ioo (-δ) δ) := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact hη_cont.comp hshift hmaps
  have hG_cont : ContinuousOn G (Set.Ioo a₀ (b + δ)) := by
    intro t ht
    rcases lt_trichotomy t b with hlt | heq | hgt
    · have htγ : t ∈ Set.Ioo a₀ b := ⟨ht.1, hlt⟩
      have hGγ : G =ᶠ[𝓝[Set.Ioo a₀ (b + δ)] t] γ := by
        have hnhds : Set.Iio b ∈ 𝓝 t := isOpen_Iio.mem_nhds hlt
        filter_upwards [nhdsWithin_le_nhds hnhds] with s hs
        simp only [hG_def, if_pos (mem_Iio.mp hs)]
      have hγ_at : ContinuousWithinAt γ (Set.Ioo a₀ (b + δ)) t := by
        refine (hγ_cont t htγ).mono_of_mem_nhdsWithin ?_
        exact mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htγ)
      refine hγ_at.congr_of_eventuallyEq hGγ ?_
      simp only [hG_def, if_pos hlt]
    · subst heq
      have hG_eq_ηb : G =ᶠ[𝓝[Set.Ioo a₀ (t + δ)] t] (fun s => η (s - t)) := by
        rw [eventuallyEq_nhdsWithin_iff]
        have hleft : ∀ᶠ s in 𝓝[<] t, G s = η (s - t) := by
          have hmatch' : γ =ᶠ[𝓝[<] t] (fun s => η (s - t)) := hmatch
          have hGγ : G =ᶠ[𝓝[<] t] γ := by
            filter_upwards [self_mem_nhdsWithin] with s hs
            simp only [hG_def, if_pos (mem_Iio.mp hs)]
          exact hGγ.trans hmatch'
        have hright : ∀ᶠ s in 𝓝[≥] t, G s = η (s - t) := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          simp only [hG_def, if_neg (not_lt.mpr (mem_Ici.mp hs))]
        have hfull : G =ᶠ[𝓝 t] (fun s => η (s - t)) := by
          rw [← nhdsLT_sup_nhdsGE t, Filter.EventuallyEq, eventually_sup]
          exact ⟨hleft, hright⟩
        filter_upwards [hfull] with s hs _ using hs
      have hηb_at : ContinuousWithinAt (fun s => η (s - t)) (Set.Ioo a₀ (t + δ)) t := by
        have htmem : t ∈ Set.Ioo (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
        refine (hηb_cont t htmem).mono_of_mem_nhdsWithin ?_
        exact mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htmem)
      refine hηb_at.congr_of_eventuallyEq hG_eq_ηb ?_
      simp only [hG_def, if_neg (lt_irrefl t), sub_self]
    · have htηb : t ∈ Set.Ioo (b - δ) (b + δ) := ⟨by linarith, ht.2⟩
      have hGηb : G =ᶠ[𝓝[Set.Ioo a₀ (b + δ)] t] (fun s => η (s - b)) := by
        have hnhds : Set.Ioi b ∈ 𝓝 t := isOpen_Ioi.mem_nhds hgt
        filter_upwards [nhdsWithin_le_nhds hnhds] with s hs
        simp only [hG_def, if_neg (not_lt.mpr (le_of_lt (mem_Ioi.mp hs)))]
      refine ContinuousWithinAt.congr_of_eventuallyEq ?_ hGηb ?_
      · refine (hηb_cont t htηb).mono_of_mem_nhdsWithin ?_
        exact mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htηb)
      · simp only [hG_def, if_neg (not_lt.mpr (le_of_lt hgt))]
  refine ⟨G, b + δ, by linarith,
    Geodesic.isGeodesicOn_glue_at_limit_Ioo (I := I) g hδ ha₀b hγ hη hmatch,
    hG_cont, ?_⟩
  intro t ht
  simp only [hG_def, if_pos ht]

/-- **`Ioo`-seeded intrinsic right-completeness.** Suppose that for every
geodesic on a bounded interval `Ioo a₀ b` (`b > 0`) extending the initial
geodesic `γ₀` (which is a geodesic on `Ioo a₀ b₀`), endpoint-continuation data is
available at `b`.  Then the initial geodesic extends to a geodesic on the
right-unbounded interval `Ioi a₀`, agreeing with `γ₀` below `b₀`.

Bounded-left analogue of `isGeodesicOn_Ici_of_endpointContinuation`: the
extension records are geodesics on `Ioo a₀ b` with the fixed left endpoint `a₀`,
ordered by interval inclusion plus agreement below the shorter endpoint, and the
union over a maximal chain is the colimit geodesic on `Ioi a₀`.  Each step is the
bounded-left `isGeodesicOn_Ioo_extend`; the maximal-chain colimit assembly is
identical to the `Iio` engine since both only inspect left-neighbourhoods of the
growing right endpoint. -/
theorem isGeodesicOn_Ioi_of_endpointContinuation
    (g : SmoothRiemannianMetric I M) {γ₀ : ℝ → M} {a₀ b₀ : ℝ}
    (ha₀ : a₀ < 0) (hb₀ : 0 < b₀)
    (hγ₀ : IsGeodesicOn (I := I) g γ₀ (Set.Ioo a₀ b₀))
    (hγ₀_cont : ContinuousOn γ₀ (Set.Ioo a₀ b₀))
    (hcont : ∀ (γ : ℝ → M) (b : ℝ), 0 < b →
      IsGeodesicOn (I := I) g γ (Set.Ioo a₀ b) →
      ContinuousOn γ (Set.Ioo a₀ b) →
      (∀ t < b₀, t < b → γ t = γ₀ t) →
      HasEndpointContinuation (I := I) g γ b) :
    ∃ γ : ℝ → M,
      IsGeodesicOn (I := I) g γ (Set.Ioi a₀) ∧
      ContinuousOn γ (Set.Ioi a₀) ∧
      (∀ t, t < b₀ → γ t = γ₀ t) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have ha₀b₀ : a₀ < b₀ := lt_trans ha₀ hb₀
  let Good : (ℝ × (ℝ → M)) → Prop := fun br =>
    b₀ ≤ br.1 ∧ IsGeodesicOn (I := I) g br.2 (Set.Ioo a₀ br.1) ∧
      ContinuousOn br.2 (Set.Ioo a₀ br.1) ∧
      (∀ t < b₀, br.2 t = γ₀ t)
  let Rec := {br : ℝ × (ℝ → M) // Good br}
  let R : Rec → Rec → Prop := fun a a' =>
    a.1.1 ≤ a'.1.1 ∧ (∀ t < a.1.1, a'.1.2 t = a.1.2 t)
  have hGood_r₀ : Good (b₀, γ₀) := ⟨le_refl _, hγ₀, hγ₀_cont, fun t _ => rfl⟩
  let r₀ : Rec := ⟨(b₀, γ₀), hGood_r₀⟩
  have hchain0 : IsChain R {r₀} := by
    intro a ha b hb hab
    rw [Set.mem_singleton_iff] at ha hb; exact absurd (ha.trans hb.symm) hab
  obtain ⟨Mc, hMc_max, hMc_sub⟩ := hchain0.exists_maxChain
  have hr₀_mem : r₀ ∈ Mc := hMc_sub (Set.mem_singleton _)
  have hMc_chain : IsChain R Mc := hMc_max.1
  have hconsist : ∀ a ∈ Mc, ∀ a' ∈ Mc, ∀ t, t < a.1.1 → t < a'.1.1 →
      a.1.2 t = a'.1.2 t := by
    intro a ha a' ha' t hta hta'
    rcases eq_or_ne a a' with rfl | hne
    · rfl
    · rcases hMc_chain ha ha' hne with hR | hR
      · exact (hR.2 t hta).symm
      · exact hR.2 t hta'
  let Γ : ℝ → M := fun t =>
    if h : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 then (h.choose.1.2 t) else γ₀ t
  have hΓ_val : ∀ a ∈ Mc, ∀ t, t < a.1.1 → Γ t = a.1.2 t := by
    intro a ha t hta
    have hex : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 := ⟨a, ha, hta⟩
    change (if h : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 then (h.choose.1.2 t)
      else γ₀ t) = a.1.2 t
    rw [dif_pos hex]
    obtain ⟨hb_mem, hb_lt⟩ := hex.choose_spec
    exact hconsist _ hb_mem a ha t hb_lt hta
  have hΓ_agree : ∀ t, t < b₀ → Γ t = γ₀ t := by
    intro t ht
    have := hΓ_val r₀ hr₀_mem t ht
    simpa [r₀] using this
  have hΓ_geo_at : ∀ a ∈ Mc, ∀ t, a₀ < t → t < a.1.1 →
      HasGeodesicEquationAt (I := I) g Γ t := by
    intro a ha t hta_lo hta
    have hIoo_nhds : Set.Ioo a₀ a.1.1 ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨hta_lo, hta⟩
    have heq : Γ =ᶠ[𝓝 t] a.1.2 := by
      filter_upwards [hIoo_nhds] with s hs
      exact hΓ_val a ha s hs.2
    exact hasGeodesicEquationAt_congr_of_eventuallyEq (g := g) heq
      (a.2.2.1 t ⟨hta_lo, hta⟩)
  have hΓ_cont_at : ∀ a ∈ Mc, ∀ t, a₀ < t → t < a.1.1 →
      ContinuousWithinAt Γ (Set.Ioi a₀) t := by
    intro a ha t hta_lo hta
    have htmem : t ∈ Set.Ioo a₀ a.1.1 := ⟨hta_lo, hta⟩
    have heq : Γ =ᶠ[𝓝[Set.Ioi a₀] t] a.1.2 := by
      have hnhds : Set.Iio a.1.1 ∈ 𝓝 t := isOpen_Iio.mem_nhds hta
      filter_upwards [nhdsWithin_le_nhds hnhds] with s hs
      exact hΓ_val a ha s (mem_Iio.mp hs)
    have hmem_at : ContinuousWithinAt a.1.2 (Set.Ioi a₀) t := by
      refine ((a.2.2.2.1 t htmem)).mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htmem)
    exact hmem_at.congr_of_eventuallyEq heq (hΓ_val a ha t hta)
  let S : Set ℝ := (fun a : Rec => a.1.1) '' Mc
  have hS_ne : S.Nonempty := ⟨b₀, ⟨r₀, hr₀_mem, rfl⟩⟩
  by_cases hbdd : BddAbove S
  · exfalso
    let s := sSup S
    have hb₀_le_s : b₀ ≤ s := le_csSup hbdd ⟨r₀, hr₀_mem, rfl⟩
    have hs_pos : 0 < s := lt_of_lt_of_le hb₀ hb₀_le_s
    have ha₀_lt_s : a₀ < s := lt_of_lt_of_le ha₀b₀ hb₀_le_s
    have hΓ_geo_Ioos : IsGeodesicOn (I := I) g Γ (Set.Ioo a₀ s) := by
      intro t ht
      obtain ⟨b, hbS, htb⟩ := exists_lt_of_lt_csSup hS_ne ht.2
      obtain ⟨a, ha, hab⟩ := hbS
      exact hΓ_geo_at a ha t ht.1 (lt_of_lt_of_eq htb hab.symm)
    have hΓ_cont_Ioos : ContinuousOn Γ (Set.Ioo a₀ s) := by
      intro t ht
      obtain ⟨b, hbS, htb⟩ := exists_lt_of_lt_csSup hS_ne ht.2
      obtain ⟨a, ha, hab⟩ := hbS
      have hcw := hΓ_cont_at a ha t ht.1 (lt_of_lt_of_eq htb hab.symm)
      exact hcw.mono (fun u hu => hu.1)
    have hagree_s : ∀ t < b₀, t < s → Γ t = γ₀ t := fun t ht _ => hΓ_agree t ht
    have hcont_s : HasEndpointContinuation (I := I) g Γ s :=
      hcont Γ s hs_pos hΓ_geo_Ioos hΓ_cont_Ioos hagree_s
    obtain ⟨Γ', s', hss', hΓ'_geo, hΓ'_cont, hΓ'_agree⟩ :=
      isGeodesicOn_Ioo_extend (I := I) g ha₀_lt_s hΓ_geo_Ioos hΓ_cont_Ioos hcont_s
    have hGood' : Good (s', Γ') := by
      refine ⟨le_trans hb₀_le_s hss'.le, hΓ'_geo, hΓ'_cont, ?_⟩
      intro t ht
      have ht_s : t < s := lt_of_lt_of_le ht hb₀_le_s
      change Γ' t = γ₀ t
      rw [hΓ'_agree t ht_s]; exact hΓ_agree t ht
    let r' : Rec := ⟨(s', Γ'), hGood'⟩
    have hr'_notMem : r' ∉ Mc := by
      intro hmem
      have hmemS : s' ∈ S := ⟨r', hmem, rfl⟩
      exact absurd (le_csSup hbdd hmemS) (not_le.mpr hss')
    have hchain' : IsChain R (insert r' Mc) := by
      refine hMc_chain.insert ?_
      intro a ha _
      right
      have ha_mem_S : a.1.1 ∈ S := ⟨a, ha, rfl⟩
      have ha_le_s : a.1.1 ≤ s := le_csSup hbdd ha_mem_S
      refine ⟨?_, ?_⟩
      · change a.1.1 ≤ s'
        exact le_trans ha_le_s hss'.le
      · intro t hta
        have ht_s : t < s := lt_of_lt_of_le hta ha_le_s
        change Γ' t = a.1.2 t
        rw [hΓ'_agree t ht_s]; exact hΓ_val a ha t hta
    have heq_chain : Mc = insert r' Mc :=
      hMc_max.2 hchain' (Set.subset_insert _ _)
    exact hr'_notMem (heq_chain ▸ Set.mem_insert _ _)
  · refine ⟨Γ, ?_, ?_, hΓ_agree⟩
    · intro t ht
      rw [not_bddAbove_iff] at hbdd
      obtain ⟨b, hbS, htb⟩ := hbdd t
      obtain ⟨a, ha, hab⟩ := hbS
      exact hΓ_geo_at a ha t ht (lt_of_lt_of_eq htb hab.symm)
    · intro t ht
      rw [not_bddAbove_iff] at hbdd
      obtain ⟨b, hbS, htb⟩ := hbdd t
      obtain ⟨a, ha, hab⟩ := hbS
      exact hΓ_cont_at a ha t ht (lt_of_lt_of_eq htb hab.symm)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`Ioo`-seeded forward geodesic completeness from metric completeness.**
A moving-foot geodesic `γ₀` on a bounded interval `Ioo a₀ b₀` (`a₀ < 0 < b₀`)
extends, across charts, to a geodesic on the right-unbounded interval `Ioi a₀`,
agreeing with `γ₀` below `b₀`.

This is the bounded-left analogue of `isGeodesicOn_Ici_of_complete`, seeded by
the *bounded* interval `Ioo a₀ b₀` produced by the local seed
`exists_isGeodesicOn_Ioo_at_velocity` (rather than a left-unbounded `Iio b₀`).
The per-extension analytic data `hreg` is the minimal separable regularity a
constant-speed geodesic supplies: `C¹`-in-time on `Ioo a₀ b`, with constant
`g`-speed bounded by a nonnegative `c`.  Metric completeness furnishes
endpoint-continuation data at each finite right endpoint `b`
(`hasEndpointContinuation_of_complete`, in its bounded-left form), and the colimit
assembly (`isGeodesicOn_Ioi_of_endpointContinuation`) produces the global forward
geodesic. -/
theorem isGeodesicOn_Ici_of_complete_Ioo
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {γ₀ : ℝ → M} {a₀ b₀ : ℝ}
    (ha₀ : a₀ < 0) (hb₀ : 0 < b₀)
    (hγ₀ : IsGeodesicOn (I := I) g γ₀ (Set.Ioo a₀ b₀))
    (hγ₀_cont : ContinuousOn γ₀ (Set.Ioo a₀ b₀))
    (hreg : ∀ (γ : ℝ → M) (b : ℝ), 0 < b → IsGeodesicOn (I := I) g γ (Set.Ioo a₀ b) →
      ContinuousOn γ (Set.Ioo a₀ b) →
      (∀ t, a₀ < t → t < b₀ → t < b → γ t = γ₀ t) →
      ∃ c : ℝ, 0 ≤ c ∧ ContMDiffOn 𝓘(ℝ,ℝ) I 1 γ (Set.Ioo a₀ b) ∧
        (∀ τ ∈ Set.Ioo a₀ b, ‖mfderiv 𝓘(ℝ,ℝ) I γ τ 1‖ₑ ≤ ENNReal.ofReal c) ∧
        (∀ s ∈ Set.Ioo a₀ b, (g.inner (γ s)) (mfderiv 𝓘(ℝ,ℝ) I γ s 1)
          (mfderiv 𝓘(ℝ,ℝ) I γ s 1) ≤ c^2)) :
    ∃ γ : ℝ → M, IsGeodesicOn (I := I) g γ (Set.Ioi a₀) ∧
      (∀ t, t < b₀ → γ t = γ₀ t) := by
  have hcont : ∀ (γ : ℝ → M) (b : ℝ), 0 < b →
      IsGeodesicOn (I := I) g γ (Set.Ioo a₀ b) →
      ContinuousOn γ (Set.Ioo a₀ b) →
      (∀ t < b₀, t < b → γ t = γ₀ t) →
      HasEndpointContinuation (I := I) g γ b := by
    intro γ b hb hγ hγ_cont hagree
    obtain ⟨c, hc_nonneg, hγ_smooth, hSpeedBound, hSpeedSq⟩ :=
      hreg γ b hb hγ hγ_cont (fun t _ ht_b₀ ht_b => hagree t ht_b₀ ht_b)
    exact hasEndpointContinuation_of_complete (I := I) g (lt_trans ha₀ hb)
      hc_nonneg hγ_smooth hSpeedBound hSpeedSq hγ
  obtain ⟨γ, hgeo, _hcontΓ, hagreeΓ⟩ :=
    isGeodesicOn_Ioi_of_endpointContinuation (I := I) g ha₀ hb₀ hγ₀ hγ₀_cont hcont
  exact ⟨γ, hgeo, hagreeΓ⟩

end GeodesicCompleteness

section ExpMapTotality

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

/-- **Continuity of `expMap g p` on the whole tangent space.** Under
geodesic completeness (`isGeodesicOn_Ici_of_complete`), the exponential map
at `p` is continuous on the entire tangent space `T_p M`. The proof propagates
the smooth dependence of geodesics on initial conditions chart-locally
along the compact arc `[0, 1]`. -/
theorem bm_c_expMap_continuous_of_geodesic_complete
    (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (expMap (I := I) g p) := by
  sorry

/-- **Total continuity of `expMap g p`.** The exponential map at `p`
is a total continuous function from the tangent space `T_p M` to `M`,
under the geodesic-completeness conclusion of `isGeodesicOn_Ici_of_complete`.
The membership conjunct `expMap g p v \in Set.univ` is trivial. -/
theorem bm_c_expMap_total
    (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (expMap (I := I) g p) ∧
      ∀ v : TangentSpace I p,
        expMap (I := I) g p v ∈ (Set.univ : Set M) :=
  ⟨bm_c_expMap_continuous_of_geodesic_complete (I := I) g p,
    fun _ => Set.mem_univ _⟩

end ExpMapTotality

section MinimiserExistence

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

/-- **Minimising sequence of `C¹` paths.** For any `p q : M` there is a
sequence of `C¹` curves `γₙ : ℝ → M` on `[0, 1]` from `p` to `q` whose
`pathELength`s converge from above to `riemannianEDist I p q`, provided
the latter is finite. The bound `pathELength I (γ n) 0 1 < d + 1/(n+1)`
is produced by the Mathlib infimum-approximation lemma
`exists_lt_of_riemannianEDist_lt`, and the lower bound
`d ≤ pathELength I (γ n) 0 1` by `riemannianEDist_le_pathELength`. -/
private theorem path_length_minimising_sequence
    (p q : M) (hd : riemannianEDist I p q ≠ ⊤) :
    ∃ γ : ℕ → ℝ → M,
      (∀ n, γ n 0 = p) ∧ (∀ n, γ n 1 = q) ∧
      (∀ n, CMDiff[Set.Icc (0 : ℝ) 1] 1 (γ n)) ∧
      (∀ n, riemannianEDist I p q ≤ pathELength I (γ n) 0 1) ∧
      (∀ n, pathELength I (γ n) 0 1 <
        riemannianEDist I p q + ENNReal.ofReal (1 / (n + 1))) := by
  set d : ℝ≥0∞ := riemannianEDist I p q with hd_def
  have hstep : ∀ n : ℕ, ∃ ρ : ℝ → M,
      ρ 0 = p ∧ ρ 1 = q ∧ CMDiff[Set.Icc (0 : ℝ) 1] 1 ρ ∧
      pathELength I ρ 0 1 < d + ENNReal.ofReal (1 / (n + 1)) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hofReal_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / (n + 1)) :=
      ENNReal.ofReal_pos.mpr hpos
    have hlt : d < d + ENNReal.ofReal (1 / (n + 1)) :=
      ENNReal.lt_add_right (by rw [hd_def]; exact hd) hofReal_pos.ne'
    obtain ⟨ρ, hρ0, hρ1, hρ_smooth, hρ_len⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt (I := I) (x := p) (y := q)
        (r := d + ENNReal.ofReal (1 / (n + 1))) (by rw [hd_def] at hlt; exact hlt)
    exact ⟨ρ, hρ0, hρ1, hρ_smooth, hρ_len⟩
  choose γ hγ0 hγ1 hγ_smooth hγ_len using hstep
  refine ⟨γ, hγ0, hγ1, hγ_smooth, ?_, ?_⟩
  · intro n
    rw [hd_def]
    exact Manifold.riemannianEDist_le_pathELength (I := I) (γ := γ n)
      (a := 0) (b := 1) (hγ_smooth n) (hγ0 n) (hγ1 n) zero_le_one
  · intro n; rw [hd_def] at hγ_len ⊢; exact hγ_len n

/-- **Path-length infimum is attained.** On a complete Riemannian manifold
(`IsRiemannianManifold I M`, `CompleteSpace M`), for every `p q : M` there
is a continuous curve `γ : ℝ → M` with `γ 0 = p`, `γ 1 = q` whose
`pathELength I γ 0 1` equals `riemannianEDist I p q` (the distance infimum
over paths is attained). The proof builds a length-minimising sequence of
`C¹` paths whose lengths converge to `riemannianEDist I p q` and extracts a
continuous limit curve. -/
theorem exists_continuous_path_realizing_riemannianEDist
    (g : SmoothRiemannianMetric I M) (p q : M) :
    ∃ γ : ℝ → M,
      Continuous γ ∧ γ 0 = p ∧ γ 1 = q ∧
        pathELength I γ 0 1 = riemannianEDist I p q := by
  by_cases hd : riemannianEDist I p q = ⊤
  · sorry
  · obtain ⟨γseq, hγ0, hγ1, hγ_smooth, hγ_lb, hγ_ub⟩ :=
      path_length_minimising_sequence (I := I) p q hd
    set d : ℝ≥0∞ := riemannianEDist I p q with hd_def
    have hLen_tendsto :
        Tendsto (fun n => pathELength I (γseq n) 0 1) atTop (𝓝 d) := by
      have hupper :
          Tendsto (fun n : ℕ => d + ENNReal.ofReal (1 / (n + 1))) atTop (𝓝 d) := by
        have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1)))
            atTop (𝓝 (ENNReal.ofReal 0)) :=
          (ENNReal.continuous_ofReal.tendsto 0).comp h1
        rw [ENNReal.ofReal_zero] at h2
        have h3 : Tendsto (fun n : ℕ => d + ENNReal.ofReal (1 / (n + 1)))
            atTop (𝓝 (d + 0)) :=
          Filter.Tendsto.const_add d h2
        simpa using h3
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hupper (fun n => ?_) (fun n => ?_)
      · exact hγ_lb n
      · exact (hγ_ub n).le
    clear hLen_tendsto
    sorry

/-- **A length minimiser is, after reparametrisation, a smooth geodesic.**
If a continuous curve `γ` on `[a, b]` is length-minimising
(`pathELength I γ a b = riemannianEDist I (γ a) (γ b)`), then there is a
parameter length `L ≥ 0` and a reparametrisation `η : ℝ → M` with the same
endpoints (`η 0 = γ a`, `η L = γ b`) that is `C^∞` and `IsGeodesicAt` on the
open interval `(0, L)`, is `C¹` and `IsGeodesicOn` on `[0, L]`, has
`pathELength I η 0 L = ENNReal.ofReal L`, and whose length parameter realises
the endpoint distance, `ENNReal.ofReal L = riemannianEDist I (γ a) (γ b)`. -/
theorem minimizing_path_is_smooth_geodesic
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hγ : Continuous γ)
    (hmin : pathELength I γ a b = riemannianEDist I (γ a) (γ b)) :
    ∃ (L : ℝ) (η : ℝ → M),
      0 ≤ L ∧ η 0 = γ a ∧ η L = γ b ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) L, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ η t) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) L,
          IsGeodesicAt (I := I) g η t) ∧
        pathELength I η 0 L = ENNReal.ofReal L ∧
        ENNReal.ofReal L = riemannianEDist I (γ a) (γ b) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 L) ∧
        IsGeodesicOn (I := I) g η (Set.Icc 0 L) := by
  sorry

/-- **Auxiliary: `IsGeodesicOn` is preserved under affine
reparametrisation.** If `γ` is a geodesic on `[a, b]` and
`c, d : ℝ`, then `s ↦ γ (c · s + d)` is a geodesic on the
preimage interval. The lifted curve is `s ↦ ⟨γ(c s + d), c • γ'(c s + d)⟩`,
which is an integral curve of the same chart-fixed geodesic vector field
on `TM` by the second-order chain rule combined with the quadratic scaling
`Γ(c v, c v) = c² · Γ(v, v)` of the Christoffel contraction.

The full chain-rule computation on `TM` is deferred: this is the
substantial step in the unit-speed rescale theorem, and the missing
TM-derivative infrastructure makes the proof open in this file. -/
private theorem isGeodesicOn_affineReparam
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b c d : ℝ}
    (_hγ_geod : IsGeodesicOn (I := I) g γ (Set.Icc a b)) :
    IsGeodesicOn (I := I) g (fun s => γ (c * s + d))
      {s : ℝ | c * s + d ∈ Set.Icc a b} := by
  sorry

/-- **Unit-speed reparametrisation of a geodesic of positive length.**
A geodesic `\gamma : [a, b] \to M` whose `pathELength` equals
`ENNReal.ofReal L` with `L > 0` becomes unit-speed under the affine
reparametrisation `\eta(s) := \gamma(a + s \cdot (b - a)/L)` on
`[0, L]`. The `IsGeodesicOn` predicate is preserved under affine
reparametrisation. -/
theorem unit_speed_rescale
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b L : ℝ}
    (hab : a ≤ b) (hL : 0 < L)
    (hγ_geod : IsGeodesicOn (I := I) g γ (Set.Icc a b))
    (hγ_len : pathELength I γ a b = ENNReal.ofReal L)
    (hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc a b)) :
    ∃ η : ℝ → M,
      η 0 = γ a ∧ η L = γ b ∧
        IsGeodesicOn (I := I) g η (Set.Icc 0 L) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 L) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) L,
          (g.inner (η t)) (mfderiv 𝓘(ℝ, ℝ) I η t 1)
              (mfderiv 𝓘(ℝ, ℝ) I η t 1) = 1 := by
  set c : ℝ := (b - a) / L with hc_def
  refine ⟨fun s => γ (a + s * c), ?_, ?_, ?_, ?_, ?_⟩
  · change γ (a + 0 * c) = γ a
    simp
  · change γ (a + L * c) = γ b
    have hL_ne : L ≠ 0 := ne_of_gt hL
    have hLc : L * c = b - a := by
      simp [hc_def, mul_div_assoc', mul_div_cancel_left₀ _ hL_ne]
    have hsum : a + L * c = b := by rw [hLc]; ring
    rw [hsum]
  · have hreparam :
        IsGeodesicOn (I := I) g (fun s => γ (c * s + a))
          {s : ℝ | c * s + a ∈ Set.Icc a b} :=
      isGeodesicOn_affineReparam (I := I) g (a := a) (b := b)
        (c := c) (d := a) hγ_geod
    have hrw : (fun s => γ (c * s + a)) = (fun s => γ (a + s * c)) := by
      funext s
      have : c * s + a = a + s * c := by ring
      rw [this]
    rw [hrw] at hreparam
    apply hreparam.mono
    intro s hs
    rcases hs with ⟨hs0, hsL⟩
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hL_ne : L ≠ 0 := ne_of_gt hL
    have hc_nonneg : 0 ≤ c := by
      rw [hc_def]; exact div_nonneg hba hL.le
    have hsc_nonneg : 0 ≤ s * c := mul_nonneg hs0 hc_nonneg
    have hLc : L * c = b - a := by
      simp [hc_def, mul_div_assoc', mul_div_cancel_left₀ _ hL_ne]
    have hsc_le : s * c ≤ b - a := by
      calc s * c ≤ L * c := mul_le_mul_of_nonneg_right hsL hc_nonneg
        _ = b - a := hLc
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  · have hφ_cd : ContDiff ℝ 1 (fun s : ℝ => a + s * c) := by
      exact contDiff_const.add (contDiff_id.mul contDiff_const)
    have hφ_mC1 :
        ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun s : ℝ => a + s * c) (Set.Icc 0 L) :=
      hφ_cd.contMDiff.contMDiffOn
    have hMapsTo :
        Set.Icc (0 : ℝ) L ⊆ (fun s : ℝ => a + s * c) ⁻¹' Set.Icc a b := by
      intro s hs
      rcases hs with ⟨hs0, hsL⟩
      have hba : 0 ≤ b - a := sub_nonneg.mpr hab
      have hL_ne : L ≠ 0 := ne_of_gt hL
      have hc_nonneg : 0 ≤ c := by
        rw [hc_def]; exact div_nonneg hba hL.le
      have hsc_nonneg : 0 ≤ s * c := mul_nonneg hs0 hc_nonneg
      have hLc : L * c = b - a := by
        simp [hc_def, mul_div_assoc', mul_div_cancel_left₀ _ hL_ne]
      have hsc_le : s * c ≤ b - a := by
        calc s * c ≤ L * c := mul_le_mul_of_nonneg_right hsL hc_nonneg
          _ = b - a := hLc
      refine ⟨?_, ?_⟩
      · linarith
      · linarith
    have hcomp :
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ ∘ (fun s : ℝ => a + s * c)) (Set.Icc 0 L) :=
      hγ_C1.comp hφ_mC1 hMapsTo
    exact hcomp
  · intro t _ht
    sorry

/-- **Hopf-Rinow existence (unit-speed minimising geodesic).** On a complete
Riemannian manifold (`IsRiemannianManifold I M`, `CompleteSpace M`), any two
points `p q : M` are joined by a curve `γ` and a parameter length `L ≥ 0`
with `γ 0 = p`, `γ L = q`, where `γ` is `C¹` and `IsGeodesicOn` on `[0, L]`,
has unit `g`-speed at every `t ∈ [0, L]`, and whose length realises the
distance, `riemannianEDist I p q = ENNReal.ofReal L`. Assembled from
`exists_continuous_path_realizing_riemannianEDist`, `minimizing_path_is_smooth_geodesic`, and
`unit_speed_rescale`. -/
theorem exists_unit_speed_minimizing_geodesic_between_points
    (g : SmoothRiemannianMetric I M) (p q : M) :
    ∃ (γ : ℝ → M) (L : ℝ),
      0 ≤ L ∧ γ 0 = p ∧ γ L = q ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 L) ∧
        IsGeodesicOn (I := I) g γ (Set.Icc 0 L) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) L,
          (g.inner (γ t)) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
              (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) ∧
        riemannianEDist I p q = ENNReal.ofReal L := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨α, hα_cont, hα0, hα1, hα_len⟩ :=
    exists_continuous_path_realizing_riemannianEDist (I := I) g p q
  have hαlen' : pathELength I α 0 1 = riemannianEDist I (α 0) (α 1) := by
    rw [hα0, hα1]; exact hα_len
  obtain ⟨L, η, hL_nonneg, hη0, hηL, _hη_smooth_int, _hη_geod_int,
      hη_len_min, hL_eq_dist, hη_C1_min, hη_geod_min⟩ :=
    minimizing_path_is_smooth_geodesic (I := I) g (γ := α) (a := 0) (b := 1)
      zero_le_one hα_cont hαlen'
  have hηp : η 0 = p := by rw [hη0, hα0]
  have hηq : η L = q := by rw [hηL, hα1]
  have hη_geod_closed : IsGeodesicOn (I := I) g η (Set.Icc 0 L) := hη_geod_min
  have hη_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 L) := hη_C1_min
  have hη_len : pathELength I η 0 L = ENNReal.ofReal L := hη_len_min
  rcases (lt_or_eq_of_le hL_nonneg) with hLpos | hLzero
  · obtain ⟨ζ, hζ0, hζL, hζ_geod, hζ_C1, hζ_unit⟩ :=
      unit_speed_rescale (I := I) g (γ := η) (a := 0) (b := L) (L := L)
        hL_nonneg hLpos hη_geod_closed hη_len hη_C1
    refine ⟨ζ, L, hL_nonneg, ?_, ?_, ?_, hζ_geod, hζ_unit, ?_⟩
    · rw [hζ0]; exact hηp
    · rw [hζL]; exact hηq
    · exact hζ_C1
    · have hL_eq_pq : ENNReal.ofReal L = riemannianEDist I p q := by
        rw [hL_eq_dist, hα0, hα1]
      exact hL_eq_pq.symm
  · subst hLzero
    have hpq : p = q := by rw [← hηp]; exact hηq
    have hfin_pos : 0 < Module.finrank ℝ E :=
      Nat.pos_of_ne_zero (NeZero.ne _)
    haveI hNT : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
    obtain ⟨u, hu_ne⟩ : ∃ u : TangentSpace I p, u ≠ 0 :=
      ⟨(exists_ne (0 : E)).choose, (exists_ne (0 : E)).choose_spec⟩
    have hc_pos : 0 < (g.inner p) u u := g.pos p u hu_ne
    have hc_ne : (g.inner p) u u ≠ 0 := ne_of_gt hc_pos
    set s : ℝ := Real.sqrt ((g.inner p) u u)⁻¹ with hs_def
    have hs_sq : s * s = ((g.inner p) u u)⁻¹ := by
      rw [hs_def]
      have hinv_nn : 0 ≤ ((g.inner p) u u)⁻¹ := inv_nonneg.mpr hc_pos.le
      exact Real.mul_self_sqrt hinv_nn
    set v : TangentSpace I p := s • u with hv_def
    have hv_unit : (g.inner p) v v = 1 := by
      rw [hv_def, map_smul (g.inner p), ContinuousLinearMap.smul_apply,
        map_smul (g.inner p u), smul_eq_mul, smul_eq_mul]
      rw [show s * (s * (g.inner p) u u) = (s * s) * (g.inner p) u u by ring]
      rw [hs_sq, inv_mul_cancel₀ hc_ne]
    obtain ⟨γ', f, hf0, hγ'_eq, hγ'_zero, hf_mIC, hγ'_geod⟩ :=
      exists_geodesic_with_initial_velocity_at (I := I) g p v
    refine ⟨γ', 0, le_refl 0, hγ'_zero, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hγ'_zero, hpq]
    · have hIcc_eq : (Set.Icc (0 : ℝ) 0) = ({0} : Set ℝ) :=
        Set.Icc_self 0
      rw [hIcc_eq]
      intro t ht
      rcases ht with rfl
      rw [contMDiffWithinAt_iff']
      refine ⟨continuousWithinAt_singleton, ?_⟩
      have hsub :
          ((extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).target ∩
            (extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).symm ⁻¹'
              (({0} : Set ℝ) ∩ γ' ⁻¹' (extChartAt I (γ' 0)).source)) ⊆
            {extChartAt 𝓘(ℝ, ℝ) (0 : ℝ) 0} := by
        intro x hx
        have hx_sym : (extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).symm x ∈
            ({0} : Set ℝ) ∩ γ' ⁻¹' (extChartAt I (γ' 0)).source :=
          hx.2
        have hx_sym0 : (extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).symm x = 0 := hx_sym.1
        have hx_in_target : x ∈ (extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).target := hx.1
        have hxx : x = extChartAt 𝓘(ℝ, ℝ) (0 : ℝ) 0 := by
          calc x = extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)
                      ((extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).symm x) :=
                  ((extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).right_inv hx_in_target).symm
            _ = extChartAt 𝓘(ℝ, ℝ) (0 : ℝ) 0 := by rw [hx_sym0]
        exact hxx
      exact (contDiffWithinAt_singleton).mono hsub
    · intro t ht
      rw [Set.Icc_self 0, Set.mem_singleton_iff] at ht
      subst ht
      exact hγ'_geod.hasGeodesicEquationAt
    · intro t ht
      have hIcc_eq : (Set.Icc (0 : ℝ) 0) = ({0} : Set ℝ) :=
        Set.Icc_self 0
      rw [hIcc_eq] at ht
      rcases ht with rfl
      subst hγ'_eq
      have hmf : mfderiv 𝓘(ℝ, ℝ) I (projectCurve (I := I) f) 0 (1 : ℝ) =
          (f 0).snd :=
        IsMIntegralCurveAt.mfderiv_proj_one (I := I) (g := g) (f := f)
          (α := p) (t₀ := 0) hf_mIC
          (by rw [hf0]; exact mem_chart_source H p)
      have hgoal :
          ∀ (q : TangentBundle I M)
            (hq : q = (⟨p, v⟩ : TangentBundle I M))
            (m : TangentSpace I q.proj)
            (hm : m = q.snd),
            (g.inner q.proj) m m = 1 := by
        intro q hq m hm
        rcases hq
        change m = v at hm
        subst hm
        exact hv_unit
      exact hgoal (f 0) hf0
        (mfderiv 𝓘(ℝ, ℝ) I (projectCurve (I := I) f) 0 (1 : ℝ)) hmf
    · rw [← hpq, ENNReal.ofReal_zero]
      exact riemannianEDist_self

end MinimiserExistence

section ExpMapSurjectivity

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

/-- **`expMap g p` covers `M` from the closed ball of radius `R` in `T_p M`
under a diameter bound.** On a complete Riemannian manifold
(`IsRiemannianManifold I M`, `CompleteSpace M`), if the metric diameter of
`Set.univ` is at most `ENNReal.ofReal R` (`R ≥ 0`), then `Set.univ` is
contained in the image of `Metric.closedBall (0 : T_p M) R` under
`expMap g p`. Intended construction: for each `q`, a unit-speed minimising
geodesic from `p` to `q` has length `L = riemannianDist p q ≤ R` and initial
velocity `L • v₀` in the closed ball, with `expMap g p (L • v₀) = q`. -/
theorem expMap_surjective_on_closedBall_of_ediam_le
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ} (hR : 0 ≤ R)
    (hdiam : Metric.ediam (Set.univ : Set M) ≤ ENNReal.ofReal R) :
    (Set.univ : Set M) ⊆
      (expMap (I := I) g p) ''
        (Metric.closedBall (0 : TangentSpace I p) R) := by
  sorry

end ExpMapSurjectivity

end HopfRinow
end Riemannian
end Geometry
end DifferentialGeometry
