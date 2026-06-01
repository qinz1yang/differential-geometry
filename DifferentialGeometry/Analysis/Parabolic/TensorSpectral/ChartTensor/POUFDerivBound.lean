import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceReverse
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifold
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Leibniz decomposition and uniform sup bound for the chart-pushed POU weight

For a closed Riemannian manifold `(M, g)` and a chart `α : M`, the
chart-pushed POU weight

  `chartPushed (chartAtlasPOU I M) α (chartAtlasPOU I M α) y =
     (POU_α (symm y)) * (POU_α (symm y))`,

viewed as a function on the Euclidean chart target, decomposes as the
product of two smoother pieces:

* the globally `C^∞` extension `chartSmoothExt α (POU_α : M → ℝ)`,
* the globally `C^∞` extension `chartSmoothExt α (POU_α * POU_α : M → ℝ)`.

The first form is enough to derive a Leibniz formula for the derivative of
`chartPushed (chartAtlasPOU I M) α u` against any smooth scalar `u : M → ℝ`,
pointwise on the open chart target. The second form, specialised to
`u = POU_α`, exhibits the chart-pushed POU weight as a globally `C^∞`
compactly supported function on the Euclidean ambient space, hence its
Fréchet derivative is continuous with compact support, and therefore
uniformly bounded.

## Main results

* `fderiv_chartPushed_pou_eq_leibniz_on_target`: pointwise Leibniz
  decomposition of `fderiv (chartPushed ρ_α u)` on the open chart target,
  for smooth `u : M → ℝ`.
* `exists_fderiv_chartPushed_pou_uniform_bound`: a uniform sup bound on
  the operator norm of `fderiv (chartPushed ρ_α (POU_α : M → ℝ))` over the
  chart target.

All public theorems consume only the smoothness of `u` (where applicable)
and the closed-Riemannian-manifold hypotheses. No new axioms are
introduced.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- Pointwise rewrite `POU_α · 1 = POU_α`, used to specialise the
multiplicative-version smoothness lemma. -/
private lemma chartAtlasPOU_mul_one_eq (α : M) :
    (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        (1 : ℝ)) =
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
  funext x; ring

/-- Smoothness of the globally extended POU weight `chartSmoothExt α (POU_α)`
on the whole Euclidean ambient space. -/
theorem contDiff_chartSmoothExt_chartAtlasPOU (α : M) :
    ContDiff ℝ ∞
      (chartSmoothExt (I := I) (M := M) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
  have hone : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (1 : ℝ)) := contMDiff_const
  have hsmooth :=
    contDiff_chartSmoothExt_pou_mul (I := I) (M := M) α
      (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M) hone
  rw [chartAtlasPOU_mul_one_eq (I := I) (M := M)] at hsmooth
  exact hsmooth

/-- Compact support of the globally extended POU weight. -/
theorem hasCompactSupport_chartSmoothExt_chartAtlasPOU (α : M) :
    HasCompactSupport
      (chartSmoothExt (I := I) (M := M) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
  have hsupp :=
    hasCompactSupport_chartSmoothExt_pou_mul (I := I) (M := M) α
      (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M) (fun _ => 1)
  rw [chartAtlasPOU_mul_one_eq (I := I) (M := M)] at hsupp
  exact hsupp

/-- On the chart target, `chartPushed ρ_α u` factors as the pointwise product
of the two chart-pushed pieces `chartSmoothExt α POU_α` and `chartSmoothExt α u`. -/
theorem chartPushed_pou_eq_smoothExt_mul_smoothExt_on_target
    (α : M) (u : M → ℝ) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u y =
      chartSmoothExt (I := I) (M := M) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y *
        chartSmoothExt (I := I) (M := M) α u y := by
  classical
  have h_symm_target :
      (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  unfold chartPushed
  change ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
      u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
    chartSmoothExt (I := I) (M := M) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y *
      chartSmoothExt (I := I) (M := M) α u y
  have hPOU :
      chartSmoothExt (I := I) (M := M) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y =
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
    change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
        _ else (0 : ℝ)) = _
    rw [if_pos h_symm_target]
  have hU :
      chartSmoothExt (I := I) (M := M) α u y =
        u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
    change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
        _ else (0 : ℝ)) = _
    rw [if_pos h_symm_target]
  rw [hPOU, hU]

/-- `chartPushed ρ_α u =ᶠ[nhds y] chartSmoothExt α POU_α · chartSmoothExt α u`
at every chart-target point. -/
theorem chartPushed_eventuallyEq_smoothExt_mul (α : M) (u : M → ℝ)
    {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u =ᶠ[nhds y]
      (fun z : EuclN E =>
        chartSmoothExt (I := I) (M := M) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
          chartSmoothExt (I := I) (M := M) α u z) := by
  refine Filter.eventually_of_mem
    ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy) ?_
  intro z hz
  exact chartPushed_pou_eq_smoothExt_mul_smoothExt_on_target
    (I := I) (M := M) α u hz

/-- `chartSmoothExt α u` is `C^∞` in a neighbourhood of every chart-target
point, for any smooth `u : M → ℝ`. -/
theorem contDiffAt_chartSmoothExt_of_chartTarget
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (chartSmoothExt (I := I) (M := M) α u) y := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_scalar : ContDiffOn ℝ ∞
      (fun z : E => u ((extChartAt I α).symm z))
      (extChartAt I α).target :=
    DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
      (I := I) α hu
  have h_maps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
    intro z hz
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hz
    exact hz
  have h_compOn : ContDiffOn ℝ ∞
      (fun z : EuclN E => u ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_scalar.comp (ContinuousLinearEquiv.contDiff _).contDiffOn h_maps
  have h_formula_at : ContDiffAt ℝ ∞
      (fun z : EuclN E =>
        u ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) y :=
    (h_compOn y hy).contDiffAt (h_open.mem_nhds hy)
  refine h_formula_at.congr_of_eventuallyEq ?_
  filter_upwards [h_open.mem_nhds hy] with z hz
  have h_symm_target :
      (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hz
    exact hz
  change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
      u ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    else (0 : ℝ)) = _
  rw [if_pos h_symm_target]

/-- Fréchet differentiability of `chartSmoothExt α u` at any chart-target point. -/
theorem differentiableAt_chartSmoothExt_of_chartTarget
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    DifferentiableAt ℝ (chartSmoothExt (I := I) (M := M) α u) y := by
  have h := contDiffAt_chartSmoothExt_of_chartTarget (I := I) (M := M) α hu hy
  exact h.differentiableAt (by decide)

/-- Fréchet differentiability of `chartSmoothExt α (POU_α)`. -/
theorem differentiable_chartSmoothExt_chartAtlasPOU (α : M) :
    Differentiable ℝ
      (chartSmoothExt (I := I) (M := M) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
  have h := contDiff_chartSmoothExt_chartAtlasPOU (I := I) (M := M) α
  exact h.differentiable (by decide)

/-- **Leibniz decomposition for `fderiv (chartPushed ρ_α u)` on the chart
target.** For smooth `u : M → ℝ` and any point `y` of the open chart target,

  `fderiv (chartPushed ρ_α u) y =
     chartSmoothExt α POU_α y • fderiv (chartSmoothExt α u) y +
     chartSmoothExt α u y • fderiv (chartSmoothExt α POU_α) y`,

with `ρ_α := chartAtlasPOU I M`. Proof: on the chart target, `chartPushed ρ_α u`
is locally a product of the two smooth extensions; Mathlib's product rule
finishes. -/
theorem fderiv_chartPushed_pou_eq_leibniz_on_target
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    fderiv ℝ (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u) y =
      chartSmoothExt (I := I) (M := M) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y •
          fderiv ℝ (chartSmoothExt (I := I) (M := M) α u) y +
        chartSmoothExt (I := I) (M := M) α u y •
          fderiv ℝ
            (chartSmoothExt (I := I) (M := M) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y := by
  classical
  rw [Filter.EventuallyEq.fderiv_eq
        (chartPushed_eventuallyEq_smoothExt_mul (α := α) (u := u) hy)]
  exact fderiv_fun_mul
    ((differentiable_chartSmoothExt_chartAtlasPOU (I := I) (M := M) α) y)
    (differentiableAt_chartSmoothExt_of_chartTarget
      (I := I) (M := M) α hu hy)

/-- Smoothness of the globally extended `POU_α · POU_α`. Specialises the
multiplicative version of `contDiff_chartSmoothExt_pou_mul` with
`u := POU_α`. -/
theorem contDiff_chartSmoothExt_chartAtlasPOU_sq (α : M) :
    ContDiff ℝ ∞
      (chartSmoothExt (I := I) (M := M) α
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  have hPOU_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  exact contDiff_chartSmoothExt_pou_mul (I := I) (M := M) α
    (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M) hPOU_smooth

/-- Compact support of the globally extended `POU_α · POU_α`. -/
theorem hasCompactSupport_chartSmoothExt_chartAtlasPOU_sq (α : M) :
    HasCompactSupport
      (chartSmoothExt (I := I) (M := M) α
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  hasCompactSupport_chartSmoothExt_pou_mul (I := I) (M := M) α
    (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M)
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)

/-- Pointwise equality of the Fréchet derivatives of `chartPushed ρ_α POU_α`
and the globally smooth `chartSmoothExt α (POU_α · POU_α)` at any
chart-target point. -/
theorem fderiv_chartPushed_pou_self_eq_fderiv_chartSmoothExt_sq
    (α : M) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    fderiv ℝ (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y =
      fderiv ℝ
        (chartSmoothExt (I := I) (M := M) α
          (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) y := by
  refine Filter.EventuallyEq.fderiv_eq
    (Filter.eventually_of_mem
      ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy) ?_)
  intro z hz
  exact (DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartSmoothExt_eq_chartPushed_pou_on_target
    (I := I) (M := M) α
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) hz).symm

/-- **Uniform sup bound for the Fréchet derivative of the chart-pushed POU
weight on the chart target.** The chart-pushed POU weight
`chartPushed ρ_α POU_α` agrees on the open chart target with the globally
`C^∞` and compactly-supported function `chartSmoothExt α (POU_α · POU_α)`,
whose Fréchet derivative is therefore continuous with compact support, and
hence uniformly bounded on the whole Euclidean ambient space. The bound
transfers to the original chart-pushed function via the pointwise
`fderiv`-agreement on the chart target. -/
theorem exists_fderiv_chartPushed_pou_uniform_bound (α : M) :
    ∃ M_pou : ℝ, 0 ≤ M_pou ∧
      ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
        ‖fderiv ℝ
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y‖ ≤ M_pou := by
  classical
  set F : EuclN E → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hF_def
  have hF_smooth : ContDiff ℝ ∞ F :=
    contDiff_chartSmoothExt_chartAtlasPOU_sq (I := I) (M := M) α
  have hF_supp : HasCompactSupport F :=
    hasCompactSupport_chartSmoothExt_chartAtlasPOU_sq (I := I) (M := M) α
  have hF_fderiv_cont : Continuous (fderiv ℝ F) :=
    hF_smooth.continuous_fderiv (by decide)
  have hF_fderiv_supp : HasCompactSupport (fderiv ℝ F) :=
    hF_supp.fderiv ℝ
  set K : Set (EuclN E) := tsupport (fderiv ℝ F) with hK_def
  have hK_compact : IsCompact K := hF_fderiv_supp
  have h_zero_off_K : ∀ y : EuclN E, y ∉ K → fderiv ℝ F y = 0 := by
    intro y hy_K
    by_contra h_ne
    exact hy_K (subset_tsupport _ h_ne)
  have h_transfer : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      fderiv ℝ (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y = fderiv ℝ F y := by
    intro y hy_target
    exact fderiv_chartPushed_pou_self_eq_fderiv_chartSmoothExt_sq
      (I := I) (M := M) α hy_target
  by_cases hKne : K.Nonempty
  · obtain ⟨y₀, _hy₀_mem, hy₀_max⟩ :=
      hK_compact.exists_isMaxOn hKne hF_fderiv_cont.norm.continuousOn
    refine ⟨‖fderiv ℝ F y₀‖, norm_nonneg _, ?_⟩
    intro y hy_target
    rw [h_transfer y hy_target]
    by_cases hy_K : y ∈ K
    · exact hy₀_max hy_K
    · rw [h_zero_off_K y hy_K, norm_zero]; exact norm_nonneg _
  · refine ⟨0, le_refl _, ?_⟩
    intro y hy_target
    rw [Set.not_nonempty_iff_eq_empty] at hKne
    have hy_notK : y ∉ K := by rw [hKne]; exact Set.notMem_empty y
    rw [h_transfer y hy_target, h_zero_off_K y hy_notK, norm_zero]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
