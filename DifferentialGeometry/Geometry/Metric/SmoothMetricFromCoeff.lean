import DifferentialGeometry.Geometry.Metric.MetricExistence
import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Smooth Riemannian metric from local frame components (Brick C-G)

The **metric realization bridge**: given pointwise intrinsic data — a fibrewise bilinear
form `gm x : T_xM →L T_xM →L ℝ` that is symmetric and positive-definite — together with the
*local frame-component smoothness* of `gm`, we assemble a genuine
`SmoothRiemannianMetric I M` whose `inner` is `gm`.

This is the inverse of the component (Gram) layer: `ChartGram.lean` proves the *forward*
direction (a `SmoothRiemannianMetric` has smooth chart-frame Gram entries); here we go the
other way.  It is the "we have thus constructed a limit metric" step of MSM135 lbl351 and is
shared with Ch4 Thm 3.9 (`metricCompactness`), which constructs its limit metric the same way.

## What is *not* a new analytic input

* `symm` / `pos` are the hypotheses verbatim.
* `isVonNBounded` is **free**: `posDef_isVonNBounded` (in `MetricExistence.lean`) already shows
  positive-definiteness on a finite-dimensional inner-product space is coercive.
* Only the `contMDiff` field is real content, discharged by the local-frame route: writing the
  section in the tangent trivialization, its coordinate representation is a finite sum
  `∑ᵢⱼ (gm · frameᵢ frameⱼ) • Bᵢⱼ` of the (smooth, by hypothesis) components against the
  *constant* model matrix-unit forms `Bᵢⱼ`.

## Frame convention (adjustment vs the plan's abstract `frame_u`)

The local frame is the tangent trivialization's inverse-coordinate image of the model basis
`Module.finBasis ℝ E`, i.e. `frameVec x₀ i x = (trivAt x₀).symmL ℝ x (eᵢ)`.  This is the same
construction as `ChartGram.chartBasisVecFiber` (which uses `chartModelBasis E`); a consumer with
components in a different frame converts by the constant change-of-basis matrix.

## Main result

* `smoothMetric_of_localCoeff` : intrinsic pointwise `(inner, symm, pos)` + local frame-component
  smoothness ⇒ `∃ g : SmoothRiemannianMetric I M, g.inner = gm`.
-/

noncomputable section

open Bundle Manifold Set ContinuousLinearMap Bornology
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The fixed model basis used to index local-frame components. -/
private def mdlBasis (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  Module.finBasis ℝ E

/-- The `i`-th model coordinate functional, as a continuous linear map (finite dimension). -/
private def coCLM (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  ((mdlBasis E).coord i).toContinuousLinearMap

@[simp] private lemma coCLM_apply (i : Fin (Module.finrank ℝ E)) (v : E) :
    coCLM (E := E) i v = (mdlBasis E).coord i v := rfl

/-- The constant model matrix-unit bilinear form `(v, w) ↦ eᵢ*(v) · eⱼ*(w)`. -/
private def munit (i j : Fin (Module.finrank ℝ E)) : E →L[ℝ] E →L[ℝ] ℝ :=
  (coCLM (E := E) i).smulRight (coCLM (E := E) j)

@[simp] private lemma munit_apply (i j : Fin (Module.finrank ℝ E)) (v w : E) :
    munit (E := E) i j v w = (mdlBasis E).coord i v * (mdlBasis E).coord j w := by
  simp [munit, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-- Bilinear expansion of any form against the model basis. -/
private lemma bilin_expand (φ : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    φ v w = ∑ i, ∑ j,
      (mdlBasis E).coord i v * (mdlBasis E).coord j w * φ (mdlBasis E i) (mdlBasis E j) := by
  set b := mdlBasis E with hb
  have hcoord : ∀ (u : E) (i : Fin (Module.finrank ℝ E)), b.coord i u = b.repr u i :=
    fun u i => Module.Basis.coord_apply b i u
  have e1 : φ v = ∑ i, b.repr v i • φ (b i) := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
  have e2 : ∀ i, φ (b i) w = ∑ j, b.repr w j • φ (b i) (b j) := by
    intro i
    conv_lhs => rw [← b.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul]
  calc φ v w
      = (∑ i, b.repr v i • φ (b i)) w := by rw [e1]
    _ = ∑ i, b.repr v i • φ (b i) w := by
          rw [ContinuousLinearMap.sum_apply]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [ContinuousLinearMap.smul_apply]
    _ = ∑ i, b.repr v i • ∑ j, b.repr w j • φ (b i) (b j) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [e2 i]
    _ = ∑ i, ∑ j, b.coord i v * b.coord j w * φ (b i) (b j) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [smul_eq_mul, smul_eq_mul, hcoord, hcoord]
          ring

/-- Any form equals the sum of its model-basis components against the constant matrix units. -/
private lemma clm_eq_sum (φ : E →L[ℝ] E →L[ℝ] ℝ) :
    φ = ∑ i, ∑ j, φ (mdlBasis E i) (mdlBasis E j) • munit (E := E) i j := by
  ext v w
  rw [bilin_expand (E := E) φ v w]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, munit_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- The chart-local tangent frame at `x₀`: the inverse trivialization coordinate image of the
`i`-th model basis vector. Same construction as `ChartGram.chartBasisVecFiber` (with the model
basis `Module.finBasis ℝ E`). -/
def frameVec (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) : TangentSpace I x :=
  (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (mdlBasis E i)

/-- The coordinate representation of a fibrewise form in the `(0,2)`-tensor trivialization,
evaluated on model vectors, is the form applied to the symm-frame vectors. Generic in the form
`φ` (mirrors `MetricExistence.inCoordinates_localFiber`, stopping before the localFiber-specific
cancellation). -/
private lemma coordSnd_apply (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (φ : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (v w : E) :
    ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
          (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀)
        ⟨x, φ⟩).2 v w
      = φ ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x v)
          ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x w) := by
  have h := hom_trivializationAt_apply (RingHom.id ℝ) (F₁ := E) (E₁ := TangentSpace I)
    (F₂ := E →L[ℝ] ℝ) (E₂ := fun y => TangentSpace I y →L[ℝ] ℝ) x₀
    ⟨x, φ⟩
  rw [congrArg Prod.snd h]
  rw [ContinuousLinearMap.inCoordinates]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [oneForm_continuousLinearMapAt x₀ hx]
  simp only [ContinuousLinearMap.comp_apply]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The metric section is smooth on the base set of the trivialization at `x₀`, from the
local-frame component smoothness hypothesis. -/
private lemma metric_contMDiffOn (gm : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x₀ : M)
    (hcoeff : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun x => gm x (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x))
        (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (gm b))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hbsub : (trivializationAt E (TangentSpace I) x₀).baseSet ⊆
      (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀).baseSet := by
    rw [hom_trivializationAt (RingHom.id ℝ) x₀, Bundle.Trivialization.baseSet_continuousLinearMap]
    intro y hy
    refine ⟨hy, ?_⟩
    rw [hom_trivializationAt (RingHom.id ℝ) x₀, Bundle.Trivialization.baseSet_continuousLinearMap]
    exact ⟨hy, mem_baseSet_trivializationAt ℝ (Bundle.Trivial M ℝ) x₀⟩
  rw [Bundle.Trivialization.contMDiffOn_section_iff
      (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀)
      (trivializationAt E (TangentSpace I) x₀).open_baseSet hbsub]
  have hsmooth : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => ∑ i, ∑ j,
        gm x (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x) • munit (E := E) i j)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
    refine contMDiffOn_finset_sum (fun i _ => ?_)
    refine contMDiffOn_finset_sum (fun j _ => ?_)
    exact (hcoeff i j).smul contMDiffOn_const
  refine hsmooth.congr ?_
  intro x hx
  rw [clm_eq_sum (E := E)
    ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀)
      ⟨x, gm x⟩).2]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [frameVec]
  rw [coordSnd_apply (I := I) x₀ hx (gm x) (mdlBasis E i) (mdlBasis E j)]

/-- **The metric realization bridge.** Pointwise intrinsic data — a fibrewise bilinear form
`gm` that is symmetric and positive-definite — whose local frame components are smooth assembles
into a `SmoothRiemannianMetric` with that inner product. -/
theorem smoothMetric_of_localCoeff
    (gm : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsymm : ∀ (x : M) (v w : TangentSpace I x), gm x v w = gm x w v)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < gm x v v)
    (hcoeff : ∀ x₀ : M, ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun x => gm x (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x))
        (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∃ g : SmoothRiemannianMetric I M,
      ∀ (x : M) (v w : TangentSpace I x), g.inner x v w = gm x v w := by
  refine ⟨{
    inner := gm
    symm := hsymm
    pos := hpos
    isVonNBounded := fun x => posDef_isVonNBounded (E := E) (gm x) (fun v hv => hpos x v hv)
    contMDiff := ?_ }, fun x v w => rfl⟩
  intro x₀
  refine ContMDiffOn.contMDiffAt (metric_contMDiffOn (I := I) gm x₀ (hcoeff x₀)) ?_
  exact (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E (TangentSpace I) x₀)

end Geometry
end DifferentialGeometry
