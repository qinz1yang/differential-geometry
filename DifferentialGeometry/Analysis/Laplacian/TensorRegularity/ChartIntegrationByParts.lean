import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.ChartPrimitives
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives

/-!
# Integration by parts for the chart-Euclidean partial derivative

This file provides a clean integration-by-parts identity for the chart-Euclidean
partial derivative `euclidPartial` on the open Euclidean chart target
`chartTargetEuclid α`. It is the analytic device that moves a derivative off a
compactly-supported test function and onto a smooth coefficient.

Throughout, the model fibre `E` is a finite-dimensional real inner-product space
and `n := Module.finrank ℝ E`. Functions live on the standard Euclidean model
space `EuclideanSpace ℝ (Fin n)`. The reference measure is the pushforward
`Measure.map toEuclidean modelHaar` of the model Haar measure under the canonical
linear isometry `toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin n)`; by
`map_toEuclidean_modelHaar_eq_volume` this pushforward is the Lebesgue/Haar
measure `volume` on `EuclideanSpace ℝ (Fin n)`.

## Main result

* `chartTarget_integral_byParts` — for an index `l`, a coefficient `f` that is
  `C^∞` on the open chart target, and a test function `g` that is `C^∞` on the
  chart target with compact topological support contained in the chart target,
  ```
  ∫ y in chartTargetEuclid α, f y * euclidPartial l g y ∂(map toEuclidean modelHaar)
    = - ∫ y in chartTargetEuclid α, euclidPartial l f y * g y ∂(map toEuclidean modelHaar).
  ```

The proof transports the chart-Euclidean integral to the standard Lebesgue
measure, observes that the integrands vanish off the compact support of `g`
(hence the chart-target integral equals the whole-space integral), and applies
the Fréchet-derivative integration-by-parts identity
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`. The local-to-global
smoothness needed for integrability is supplied by a gluing lemma: a function
that is `C^∞` on an open set and vanishes outside a closed subset of that open
set is globally `C^∞`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

/-- A function that is `C^∞` on an open set `U` and vanishes off a closed set
`K ⊆ U` is globally `C^∞`. -/
private lemma contDiff_of_contDiffOn_zero_off_closed
    {P : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    {U K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hP : ContDiffOn ℝ ∞ P U)
    (hzero : ∀ y, y ∉ K → P y = 0) :
    ContDiff ℝ ∞ P := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact hP.contDiffAt (hU.mem_nhds hy)
  · have hyK : y ∉ K := fun hyK => hy (hKU hyK)
    have hKc_open : IsOpen (Kᶜ) := hK.isOpen_compl
    have hy_nhds : Kᶜ ∈ 𝓝 y := hKc_open.mem_nhds hyK
    have hP_zero_evt : P =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
      Filter.eventually_of_mem hy_nhds (fun y' hy' => hzero y' hy')
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ => (0 : ℝ)) y).congr_of_eventuallyEq
      hP_zero_evt

/-- The chart-Euclidean partial derivative of a function vanishes off the
topological support of the function. -/
private lemma euclidPartial_eq_zero_of_notMem_tsupport
    {g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (l : Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∉ tsupport g) :
    euclidPartial (E := E) l g y = 0 := by
  classical
  have hKc_open : IsOpen ((tsupport g)ᶜ) := (isClosed_tsupport g).isOpen_compl
  have hy_nhds : (tsupport g)ᶜ ∈ 𝓝 y := hKc_open.mem_nhds hy
  have hg_zero_evt : g =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem hy_nhds
      (fun y' hy' => image_eq_zero_of_notMem_tsupport hy')
  rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hg_zero_evt,
    fderiv_const_apply, ContinuousLinearMap.zero_apply]

/-- A test function that is `C^∞` on the chart target with topological support
contained in the chart target is globally `C^∞`. -/
private lemma contDiff_of_contDiffOn_chartTarget
    (α : M)
    {g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hg : ContDiffOn ℝ ∞ g (chartTargetEuclid (I := I) (M := M) α))
    (hg_tsub : tsupport g ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContDiff ℝ ∞ g :=
  contDiff_of_contDiffOn_zero_off_closed (E := E)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (isClosed_tsupport g) hg_tsub hg
    (fun _ hy => image_eq_zero_of_notMem_tsupport hy)

/-- The chart-Euclidean partial derivative of a function that is `C^∞` on the
open chart target is `C^∞` on the chart target. -/
private lemma euclidPartial_contDiffOn_chartTarget
    (α : M)
    {f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (euclidPartial (E := E) l f)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hU : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hcomp : euclidPartial (E := E) l f =
      (fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
        L (EuclideanSpace.single l 1)) ∘ (fun y => fderiv ℝ f y) := by
    funext y; rfl
  rw [hcomp]
  intro x hx
  have hf_at : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
  have hfd : ContDiffAt ℝ ∞ (fun y => fderiv ℝ f y) x :=
    hf_at.fderiv_right (m := ∞)
      (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl])
  have hat : ContDiffAt ℝ ∞
      ((fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
        L (EuclideanSpace.single l 1)) ∘ (fun y => fderiv ℝ f y)) x :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single l 1)).contDiff.contDiffAt.comp x hfd
  exact hat.contDiffWithinAt

/-- The product of the coefficient and the test function is globally `C^∞`. -/
private lemma contDiff_coeff_mul_test
    (α : M)
    {f g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (chartTargetEuclid (I := I) (M := M) α))
    (hg : ContDiffOn ℝ ∞ g (chartTargetEuclid (I := I) (M := M) α))
    (hg_tsub : tsupport g ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContDiff ℝ ∞ (fun y => f y * g y) := by
  refine contDiff_of_contDiffOn_zero_off_closed (E := E)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (isClosed_tsupport g) hg_tsub (hf.mul hg) ?_
  intro y hy
  rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

/-- The product of the coefficient and the chart-Euclidean partial of the test
function is globally `C^∞`. -/
private lemma contDiff_coeff_mul_partial_test
    (α : M) (l : Fin (Module.finrank ℝ E))
    {f g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (chartTargetEuclid (I := I) (M := M) α))
    (hg : ContDiffOn ℝ ∞ g (chartTargetEuclid (I := I) (M := M) α))
    (hg_tsub : tsupport g ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContDiff ℝ ∞ (fun y => f y * euclidPartial (E := E) l g y) := by
  refine contDiff_of_contDiffOn_zero_off_closed (E := E)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (isClosed_tsupport g) hg_tsub
    (hf.mul (euclidPartial_contDiffOn_chartTarget (I := I) (M := M) α hg l)) ?_
  intro y hy
  rw [euclidPartial_eq_zero_of_notMem_tsupport (E := E) l hy, mul_zero]

/-- The product of the chart-Euclidean partial of the coefficient and the test
function is globally `C^∞`. -/
lemma contDiff_partial_coeff_mul_test
    (α : M) (l : Fin (Module.finrank ℝ E))
    {f g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (chartTargetEuclid (I := I) (M := M) α))
    (hg : ContDiffOn ℝ ∞ g (chartTargetEuclid (I := I) (M := M) α))
    (hg_tsub : tsupport g ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContDiff ℝ ∞ (fun y => euclidPartial (E := E) l f y * g y) := by
  refine contDiff_of_contDiffOn_zero_off_closed (E := E)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (isClosed_tsupport g) hg_tsub
    ((euclidPartial_contDiffOn_chartTarget (I := I) (M := M) α hf l).mul hg) ?_
  intro y hy
  rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

/-- The product of the coefficient and the test function has compact support. -/
private lemma hasCompactSupport_coeff_mul_test
    {f g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hg_supp : HasCompactSupport g) :
    HasCompactSupport (fun y => f y * g y) :=
  hg_supp.mul_left

/-- The product of the coefficient and the chart-Euclidean partial of the test
function has compact support. -/
private lemma hasCompactSupport_coeff_mul_partial_test
    (l : Fin (Module.finrank ℝ E))
    {f g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hg_supp : HasCompactSupport g) :
    HasCompactSupport (fun y => f y * euclidPartial (E := E) l g y) := by
  classical
  have hpartial_supp : HasCompactSupport (euclidPartial (E := E) l g) := by
    refine HasCompactSupport.of_support_subset_isCompact hg_supp ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hy'
    exact hy (euclidPartial_eq_zero_of_notMem_tsupport (E := E) l hy')
  exact hpartial_supp.mul_left

/-- The product of the chart-Euclidean partial of the coefficient and the test
function has compact support. -/
lemma hasCompactSupport_partial_coeff_mul_test
    (l : Fin (Module.finrank ℝ E))
    {f g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hg_supp : HasCompactSupport g) :
    HasCompactSupport (fun y => euclidPartial (E := E) l f y * g y) :=
  hg_supp.mul_left

/-- **Integration by parts for the chart-Euclidean partial derivative.** For a
chart `α`, a direction `l`, a coefficient `f` that is `C^∞` on the open chart
target `chartTargetEuclid α`, and a test function `g` that is `C^∞` on the chart
target with compact topological support contained in the chart target,
```
∫ y in chartTargetEuclid α, f y * euclidPartial l g y ∂(map toEuclidean modelHaar)
  = - ∫ y in chartTargetEuclid α, euclidPartial l f y * g y ∂(map toEuclidean modelHaar).
```

The reference measure `Measure.map toEuclidean modelHaar` is the pushforward of
the model Haar measure under the canonical linear isometry; it equals the
Lebesgue/Haar measure on `EuclideanSpace ℝ (Fin n)`. -/
theorem chartTarget_integral_byParts
    (α : M) (l : Fin (Module.finrank ℝ E))
    {f g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (chartTargetEuclid (I := I) (M := M) α))
    (hg : ContDiffOn ℝ ∞ g (chartTargetEuclid (I := I) (M := M) α))
    (hg_supp : HasCompactSupport g)
    (hg_tsub : tsupport g ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        f y * euclidPartial (E := E) l g y
        ∂(MeasureTheory.Measure.map
            (toEuclidean : E → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
            (modelHaar (E := E))) =
      -∫ y in chartTargetEuclid (I := I) (M := M) α,
          euclidPartial (E := E) l f y * g y
          ∂(MeasureTheory.Measure.map
              (toEuclidean : E → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
              (modelHaar (E := E))) := by
  classical
  have hU : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  rw [DifferentialGeometry.Integral.Measure.map_toEuclidean_modelHaar_eq_volume
    (E := E)]
  have hg_global : ContDiff ℝ ∞ g :=
    contDiff_of_contDiffOn_chartTarget (I := I) (M := M) α hg hg_tsub
  have hcontDiff_fg : ContDiff ℝ ∞ (fun y => f y * g y) :=
    contDiff_coeff_mul_test (I := I) (M := M) α hf hg hg_tsub
  have hcontDiff_f_dg :
      ContDiff ℝ ∞ (fun y => f y * euclidPartial (E := E) l g y) :=
    contDiff_coeff_mul_partial_test (I := I) (M := M) α l hf hg hg_tsub
  have hcontDiff_df_g :
      ContDiff ℝ ∞ (fun y => euclidPartial (E := E) l f y * g y) :=
    contDiff_partial_coeff_mul_test (I := I) (M := M) α l hf hg hg_tsub
  have hsupp_fg : HasCompactSupport (fun y => f y * g y) :=
    hasCompactSupport_coeff_mul_test (E := E) hg_supp
  have hsupp_f_dg :
      HasCompactSupport (fun y => f y * euclidPartial (E := E) l g y) :=
    hasCompactSupport_coeff_mul_partial_test (E := E) l hg_supp
  have hsupp_df_g :
      HasCompactSupport (fun y => euclidPartial (E := E) l f y * g y) :=
    hasCompactSupport_partial_coeff_mul_test (E := E) l hg_supp
  have hint_df_g :
      Integrable (fun x =>
          fderiv ℝ f x (EuclideanSpace.single l 1) * g x) volume := by
    have hcont :
        Continuous (fun x =>
          fderiv ℝ f x (EuclideanSpace.single l 1) * g x) := by
      have := hcontDiff_df_g.continuous
      simpa only [euclidPartial_def] using this
    have hsupp :
        HasCompactSupport (fun x =>
          fderiv ℝ f x (EuclideanSpace.single l 1) * g x) := by
      have := hsupp_df_g
      simpa only [euclidPartial_def] using this
    exact hcont.integrable_of_hasCompactSupport (μ := volume) hsupp
  have hint_f_dg :
      Integrable (fun x =>
          f x * fderiv ℝ g x (EuclideanSpace.single l 1)) volume := by
    have hcont :
        Continuous (fun x =>
          f x * fderiv ℝ g x (EuclideanSpace.single l 1)) := by
      have := hcontDiff_f_dg.continuous
      simpa only [euclidPartial_def] using this
    have hsupp :
        HasCompactSupport (fun x =>
          f x * fderiv ℝ g x (EuclideanSpace.single l 1)) := by
      have := hsupp_f_dg
      simpa only [euclidPartial_def] using this
    exact hcont.integrable_of_hasCompactSupport (μ := volume) hsupp
  have hint_fg : Integrable (fun x => f x * g x) volume :=
    (hcontDiff_fg.continuous).integrable_of_hasCompactSupport (μ := volume)
      hsupp_fg
  have hf_diff : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x := by
    intro x hx
    exact (hf.contDiffAt (hU.mem_nhds (hg_tsub hx))).differentiableAt (by simp)
  have hg_diff : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x :=
    fun x _ => hg_global.differentiable (by simp) x
  have hIBP :
      ∫ x, f x * fderiv ℝ g x (EuclideanSpace.single l 1) ∂volume =
        -∫ x, fderiv ℝ f x (EuclideanSpace.single l 1) * g x ∂volume :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (v := EuclideanSpace.single l 1)
      hint_df_g hint_f_dg hint_fg hf_diff hg_diff
  have hzero_f_dg : ∀ y, y ∉ chartTargetEuclid (I := I) (M := M) α →
      f y * fderiv ℝ g y (EuclideanSpace.single l 1) = 0 := by
    intro y hy
    have hy' : y ∉ tsupport g := fun hyg => hy (hg_tsub hyg)
    have := euclidPartial_eq_zero_of_notMem_tsupport (E := E) l hy'
    rw [euclidPartial_def] at this
    rw [this, mul_zero]
  have hzero_df_g : ∀ y, y ∉ chartTargetEuclid (I := I) (M := M) α →
      fderiv ℝ f y (EuclideanSpace.single l 1) * g y = 0 := by
    intro y hy
    have hy' : y ∉ tsupport g := fun hyg => hy (hg_tsub hyg)
    rw [image_eq_zero_of_notMem_tsupport hy', mul_zero]
  simp only [euclidPartial_def]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero_f_dg,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero_df_g]
  exact hIBP

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
