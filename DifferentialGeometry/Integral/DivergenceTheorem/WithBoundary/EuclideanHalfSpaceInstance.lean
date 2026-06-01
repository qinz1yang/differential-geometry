import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.ModelBoundary
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Orientation
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# `HasSmoothBoundary` instance for the Euclidean half-space model

This file equips the canonical `n`-dimensional model with corners
`modelWithCornersEuclideanHalfSpace n : ModelWithCorners ℝ
  (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n)` with the
`HasSmoothBoundary` typeclass, for every `n : ℕ` with `[NeZero n]`.

The construction is concrete and entirely linear:

* The boundary normed model is `EuclideanSpace ℝ (Fin (n - 1))`.
* The boundary topological model is the same `EuclideanSpace ℝ (Fin (n - 1))`,
  treated via the boundaryless model `modelWithCornersSelf ℝ _`.
* The inclusion `inclEuclidean` maps a tuple `x : Fin (n - 1) → ℝ` to the
  tuple `Fin n → ℝ` whose `0`-th coordinate is `0` and whose `i`-th coordinate
  for `i ≠ 0` is the corresponding entry of `x`.
* The projection `projEuclidean` maps a tuple `y : Fin n → ℝ` to the tuple
  `Fin (n - 1) → ℝ` whose `i`-th coordinate is the `(i + 1)`-th coordinate of
  `y`.

These two maps are continuous-linear; the smoothness conditions of
`HasSmoothBoundary` follow at `C^∞`. The range identity
`Set.range (I ∘ inclH) = frontier (Set.range I)` reduces to
`{y : EuclideanSpace ℝ (Fin n) | y 0 = 0}` on both sides, using
`range_euclideanHalfSpace` and `frontier_halfSpace`.

The compatibility identity `projE ∘ I ∘ inclH = boundaryI` collapses to the
identity on `EuclideanSpace ℝ (Fin (n - 1))`, since `boundaryI` is the
self-model.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary
namespace EuclideanHalfSpaceInstance

/-- For a positive natural number, `(n - 1) + 1 = n`. -/
private theorem n_sub_one_add_one (n : ℕ) [NeZero n] : (n - 1) + 1 = n :=
  Nat.sub_one_add_one_eq_of_pos (Nat.pos_of_neZero n)

/-- Given `[NeZero n]`, the index-shift map sending `j : Fin (n - 1)` to
`Fin n` by adding one (i.e., `j ↦ j.succ` after a length cast). -/
private def succIndex (n : ℕ) [NeZero n] : Fin (n - 1) → Fin n :=
  fun j => Fin.cast (n_sub_one_add_one n) j.succ

/-- The shifted index is never `0`. -/
private theorem succIndex_ne_zero (n : ℕ) [NeZero n] (j : Fin (n - 1)) :
    succIndex n j ≠ 0 := by
  intro h
  have hval : (succIndex n j).val = (0 : Fin n).val := by rw [h]
  have hsucc : (succIndex n j).val = j.val + 1 := rfl
  rw [hsucc, Fin.val_zero] at hval
  exact Nat.succ_ne_zero _ hval

/-- For any nonzero `i : Fin n`, the predecessor lives in `Fin (n - 1)`. -/
private def predIndex (n : ℕ) [NeZero n] (i : Fin n) (h : i ≠ 0) : Fin (n - 1) :=
  ⟨i.val - 1, by
    have hi : i.val < n := i.isLt
    have hipos : 0 < i.val := by
      rcases Nat.eq_zero_or_pos i.val with h0 | h0
      · exact absurd (Fin.ext (h0.trans rfl) : i = 0) h
      · exact h0
    omega⟩

/-- `succIndex` is a left-inverse of `predIndex` (when applied at a nonzero index). -/
private theorem succIndex_predIndex (n : ℕ) [NeZero n] (i : Fin n) (h : i ≠ 0) :
    succIndex n (predIndex n i h) = i := by
  have hipos : 0 < i.val := by
    rcases Nat.eq_zero_or_pos i.val with h0 | h0
    · exact absurd (Fin.ext (h0.trans rfl) : i = 0) h
    · exact h0
  apply Fin.ext
  change (i.val - 1) + 1 = i.val
  omega

/-- `predIndex` is a left-inverse of `succIndex`. -/
private theorem predIndex_succIndex (n : ℕ) [NeZero n] (j : Fin (n - 1)) :
    predIndex n (succIndex n j) (succIndex_ne_zero n j) = j := by
  apply Fin.ext
  change (j.val + 1) - 1 = j.val
  omega

/-- Coordinate-level inclusion: insert `0` at index `0`. Sends
`x : Fin (n - 1) → ℝ` to the function `Fin n → ℝ` defined by
`f 0 = 0`, `f (succIndex n j) = x j`. -/
private def consZeroFun (n : ℕ) [NeZero n] (x : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  fun i =>
    if h : i = (0 : Fin n) then 0
    else x (predIndex n i h)

/-- Coordinate-level projection: drop index `0`. Sends `y : Fin n → ℝ`
to `Fin (n - 1) → ℝ` defined by `f j = y (succIndex n j)`. -/
private def tailFun (n : ℕ) [NeZero n] (y : Fin n → ℝ) : Fin (n - 1) → ℝ :=
  fun j => y (succIndex n j)

/-- The 0-th coordinate of `consZeroFun n x` is `0`. -/
private theorem consZeroFun_zero (n : ℕ) [NeZero n] (x : Fin (n - 1) → ℝ) :
    consZeroFun n x 0 = 0 := dif_pos rfl

/-- For any `j : Fin (n - 1)`, `consZeroFun n x (succIndex n j) = x j`. -/
private theorem consZeroFun_succIndex (n : ℕ) [NeZero n]
    (x : Fin (n - 1) → ℝ) (j : Fin (n - 1)) :
    consZeroFun n x (succIndex n j) = x j := by
  unfold consZeroFun
  rw [dif_neg (succIndex_ne_zero n j), predIndex_succIndex]

/-- The coordinate-level projection is left-inverse to the coordinate-level
inclusion: `tailFun (consZeroFun x) = x`. -/
private theorem tailFun_consZeroFun (n : ℕ) [NeZero n] (x : Fin (n - 1) → ℝ) :
    tailFun n (consZeroFun n x) = x := by
  funext j
  exact consZeroFun_succIndex n x j

/-- The coordinate-level inclusion recovers any function whose value at `0`
is `0` from its tail. -/
private theorem consZeroFun_tailFun (n : ℕ) [NeZero n] (y : Fin n → ℝ)
    (hy : y 0 = 0) :
    consZeroFun n (tailFun n y) = y := by
  funext i
  unfold consZeroFun tailFun
  by_cases h : i = (0 : Fin n)
  · rw [dif_pos h, h]; exact hy.symm
  · rw [dif_neg h, succIndex_predIndex]

/-- The continuous linear inclusion `(Fin (n - 1) → ℝ) →L[ℝ] (Fin n → ℝ)`
inserting a `0` at index `0`. -/
private def consZeroCLM (n : ℕ) [NeZero n] :
    (Fin (n - 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    if h : i = (0 : Fin n) then 0
    else
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n - 1) => ℝ)
        (predIndex n i h)

/-- `consZeroCLM` agrees with `consZeroFun` as a function. -/
private theorem consZeroCLM_apply (n : ℕ) [NeZero n] (x : Fin (n - 1) → ℝ) :
    consZeroCLM n x = consZeroFun n x := by
  funext i
  unfold consZeroCLM consZeroFun
  rw [ContinuousLinearMap.pi_apply]
  by_cases h : i = (0 : Fin n)
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h]; rfl

/-- The continuous linear projection `(Fin n → ℝ) →L[ℝ] (Fin (n - 1) → ℝ)`
dropping index `0`. -/
private def tailCLM (n : ℕ) [NeZero n] :
    (Fin n → ℝ) →L[ℝ] (Fin (n - 1) → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (succIndex n j)

/-- `tailCLM` agrees with `tailFun` as a function. -/
private theorem tailCLM_apply (n : ℕ) [NeZero n] (y : Fin n → ℝ) :
    tailCLM n y = tailFun n y := by
  funext j
  unfold tailCLM tailFun
  rw [ContinuousLinearMap.pi_apply]
  rfl

/-- The continuous linear inclusion of `EuclideanSpace ℝ (Fin (n - 1))` into
`EuclideanSpace ℝ (Fin n)` inserting a `0` at index `0`. -/
def inclEuclideanCLM (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin (n - 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
    ((consZeroCLM n).comp
      (EuclideanSpace.equiv (Fin (n - 1)) ℝ).toContinuousLinearMap)

/-- The continuous linear projection of `EuclideanSpace ℝ (Fin n)` onto
`EuclideanSpace ℝ (Fin (n - 1))` dropping index `0`. -/
def projEuclideanCLM (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
  (EuclideanSpace.equiv (Fin (n - 1)) ℝ).symm.toContinuousLinearMap.comp
    ((tailCLM n).comp
      (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap)

/-- Plain-function form of the inclusion: insert `0` at index `0`. -/
def inclEuclidean (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin (n - 1)) → EuclideanSpace ℝ (Fin n) :=
  inclEuclideanCLM n

/-- Plain-function form of the projection: drop index `0`. -/
def projEuclidean (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) :=
  projEuclideanCLM n

/-- Coordinate-access agreement: `inclEuclideanCLM n x i` (treating both
sides as functions of `Fin n`) equals `consZeroFun n (ofLp x) i`, where
`ofLp x : Fin (n - 1) → ℝ` is the underlying tuple of `x`. -/
private theorem inclEuclideanCLM_apply_coord (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℝ (Fin (n - 1))) (i : Fin n) :
    (inclEuclideanCLM n x) i = consZeroFun n x i := by
  change (((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
          ((consZeroCLM n).comp
            (EuclideanSpace.equiv (Fin (n - 1)) ℝ).toContinuousLinearMap)) x) i
        = consZeroFun n x i
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [consZeroCLM_apply]
  rfl

/-- Coordinate-access agreement for the projection. -/
private theorem projEuclideanCLM_apply_coord (n : ℕ) [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) (j : Fin (n - 1)) :
    (projEuclideanCLM n y) j = tailFun n y j := by
  change (((EuclideanSpace.equiv (Fin (n - 1)) ℝ).symm.toContinuousLinearMap.comp
          ((tailCLM n).comp
            (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap)) y) j
        = tailFun n y j
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [tailCLM_apply]
  rfl

/-- The 0-th coordinate of `inclEuclidean n x` is `0`. -/
theorem inclEuclidean_zero_coord (n : ℕ) [NeZero n] (x : EuclideanSpace ℝ (Fin (n - 1))) :
    inclEuclidean n x 0 = 0 := by
  change (inclEuclideanCLM n x) (0 : Fin n) = 0
  rw [inclEuclideanCLM_apply_coord]
  exact consZeroFun_zero n _

/-- The plain-function inverse identity: `projEuclidean (inclEuclidean x) = x`. -/
theorem projEuclidean_inclEuclidean (n : ℕ) [NeZero n] (x : EuclideanSpace ℝ (Fin (n - 1))) :
    projEuclidean n (inclEuclidean n x) = x := by
  apply (EuclideanSpace.equiv (Fin (n - 1)) ℝ).injective
  funext j
  change (projEuclideanCLM n (inclEuclideanCLM n x)) j = (x : Fin (n - 1) → ℝ) j
  rw [projEuclideanCLM_apply_coord]
  unfold tailFun
  rw [inclEuclideanCLM_apply_coord]
  exact consZeroFun_succIndex n _ _

/-- The inclusion `inclEuclidean` is `C^∞`. -/
theorem inclEuclidean_contDiff (n : ℕ) [NeZero n] :
    ContDiff ℝ ∞ (inclEuclidean n) :=
  (inclEuclideanCLM n).contDiff

/-- The projection `projEuclidean` is `C^∞`. -/
theorem projEuclidean_contDiff (n : ℕ) [NeZero n] :
    ContDiff ℝ ∞ (projEuclidean n) :=
  (projEuclideanCLM n).contDiff

/-- The inclusion `inclEuclidean` is continuous. -/
theorem inclEuclidean_continuous (n : ℕ) [NeZero n] :
    Continuous (inclEuclidean n) :=
  (inclEuclideanCLM n).continuous

/-- The projection `projEuclidean` is continuous. -/
theorem projEuclidean_continuous (n : ℕ) [NeZero n] :
    Continuous (projEuclidean n) :=
  (projEuclideanCLM n).continuous

/-- The inclusion `inclEuclidean` is injective. -/
theorem inclEuclidean_injective (n : ℕ) [NeZero n] :
    Function.Injective (inclEuclidean n) := by
  intro x y hxy
  have hx := projEuclidean_inclEuclidean n x
  have hy := projEuclidean_inclEuclidean n y
  rw [hxy] at hx
  exact hx.symm.trans hy

/-- The image of `inclEuclidean` is exactly the hyperplane `{y | y 0 = 0}`. -/
theorem range_inclEuclidean (n : ℕ) [NeZero n] :
    Set.range (inclEuclidean n) =
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} := by
  ext y
  simp only [mem_range, mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact inclEuclidean_zero_coord n x
  · intro hy
    refine ⟨projEuclidean n y, ?_⟩
    apply (EuclideanSpace.equiv (Fin n) ℝ).injective
    funext i
    change (inclEuclideanCLM n (projEuclideanCLM n y)) i = (y : Fin n → ℝ) i
    rw [inclEuclideanCLM_apply_coord]
    by_cases h : i = (0 : Fin n)
    · rw [h, consZeroFun_zero]
      exact hy.symm
    · unfold consZeroFun
      rw [dif_neg h]
      rw [projEuclideanCLM_apply_coord]
      unfold tailFun
      rw [succIndex_predIndex]

/-- The image of `inclEuclidean` is closed in `EuclideanSpace ℝ (Fin n)`. -/
theorem inclEuclidean_isClosed_range (n : ℕ) [NeZero n] :
    IsClosed (Set.range (inclEuclidean n)) := by
  rw [range_inclEuclidean]
  have heq : {y : EuclideanSpace ℝ (Fin n) | y 0 = 0}
      = (fun y : EuclideanSpace ℝ (Fin n) => y 0) ⁻¹' {0} := rfl
  rw [heq]
  refine IsClosed.preimage ?_ isClosed_singleton
  exact (PiLp.continuous_apply 2 _ 0)

/-- The inclusion `inclEuclidean` is a topological inducing map. -/
theorem inclEuclidean_isInducing (n : ℕ) [NeZero n] :
    IsInducing (inclEuclidean n) := by
  refine ⟨?_⟩
  apply le_antisymm
  · exact (inclEuclidean_continuous n).le_induced
  · intro U hU
    refine ⟨(projEuclidean n)⁻¹' U,
        (projEuclidean_continuous n).isOpen_preimage U hU, ?_⟩
    ext x
    simp [projEuclidean_inclEuclidean]

/-- The boundary inclusion lifted to `EuclideanHalfSpace n`. -/
def inclH (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin (n - 1)) → EuclideanHalfSpace n :=
  fun x => ⟨inclEuclidean n x, by
    rw [inclEuclidean_zero_coord]⟩

/-- Subtype-value identity: `(inclH n x).val = inclEuclidean n x`. -/
theorem inclH_val (n : ℕ) [NeZero n] (x : EuclideanSpace ℝ (Fin (n - 1))) :
    (inclH n x).val = inclEuclidean n x := rfl

/-- `inclH` is continuous. -/
theorem inclH_continuous (n : ℕ) [NeZero n] : Continuous (inclH n) :=
  Continuous.subtype_mk (inclEuclidean_continuous n) _

/-- `inclH` is injective. -/
theorem inclH_injective (n : ℕ) [NeZero n] : Function.Injective (inclH n) := by
  intro x y hxy
  have hval : (inclH n x).val = (inclH n y).val := by rw [hxy]
  rw [inclH_val, inclH_val] at hval
  exact inclEuclidean_injective n hval

/-- `inclH` is a topological inducing map. -/
theorem inclH_isInducing (n : ℕ) [NeZero n] : IsInducing (inclH n) := by
  have h_comp_inducing :
      IsInducing ((Subtype.val : EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n))
                    ∘ inclH n) := by
    change IsInducing (inclEuclidean n)
    exact inclEuclidean_isInducing n
  exact IsInducing.of_comp (inclH_continuous n) continuous_subtype_val h_comp_inducing

/-- The image of `inclH` after `modelWithCornersEuclideanHalfSpace n` is
exactly the hyperplane `{y | y 0 = 0}`. -/
theorem range_modelWithCorners_comp_inclH (n : ℕ) [NeZero n] :
    Set.range (modelWithCornersEuclideanHalfSpace n ∘ inclH n) =
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} := by
  ext y
  simp only [mem_range, Function.comp_apply, mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    change inclEuclidean n x 0 = 0
    exact inclEuclidean_zero_coord n x
  · intro hy
    have hin : y ∈ Set.range (inclEuclidean n) := by
      rw [range_inclEuclidean]; exact hy
    obtain ⟨x, hx⟩ := hin
    refine ⟨x, ?_⟩
    change (inclH n x).val = y
    rw [inclH_val]
    exact hx

/-- The frontier of the range of `modelWithCornersEuclideanHalfSpace n` is the
hyperplane `{y | y 0 = 0}`. This packages
`frontier_range_modelWithCornersEuclideanHalfSpace` from Mathlib in the
`y 0 = 0` orientation. -/
theorem frontier_range_modelWithCornersEuclideanHalfSpace_eq (n : ℕ) [NeZero n] :
    frontier (Set.range (modelWithCornersEuclideanHalfSpace n)) =
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} := by
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  ext y
  exact eq_comm

/-- The composite `I ∘ inclH ∘ boundaryI.symm` agrees with `inclEuclidean`.
Because `boundaryI = modelWithCornersSelf ℝ _` is the identity model, the
composition collapses to `Subtype.val ∘ inclH n = inclEuclidean n`. -/
theorem comp_modelWithCornersEuclideanHalfSpace_inclH_self_symm (n : ℕ) [NeZero n] :
    (modelWithCornersEuclideanHalfSpace n :
        EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n))
        ∘ inclH n
        ∘ (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).symm
    = inclEuclidean n := by
  funext x
  rfl

/-- The `0`-th coordinate of the standard inward direction is `1`. -/
private theorem single_zero_one_apply_zero (n : ℕ) [NeZero n] :
    (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) 0 = 1 := by
  rw [show (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) =
        PiLp.single 2 (0 : Fin n) (1 : ℝ) from rfl]
  rw [PiLp.single_apply]
  simp

/-- The standard inward direction is not in the hyperplane `{y | y 0 = 0}`. -/
private theorem single_zero_one_notMem_hyperplane (n : ℕ) [NeZero n] :
    EuclideanSpace.single (0 : Fin n) (1 : ℝ) ∉
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} := by
  intro hmem
  have : (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) 0 = 1 :=
    single_zero_one_apply_zero n
  have : (1 : ℝ) = 0 := this ▸ hmem
  exact one_ne_zero this

/-- The Fréchet derivative of the inclusion `inclEuclidean n` is the constant
continuous linear map `inclEuclideanCLM n`. -/
private theorem fderiv_inclEuclidean (n : ℕ) [NeZero n]
    (y : EuclideanSpace ℝ (Fin (n - 1))) :
    fderiv ℝ (inclEuclidean n) y = inclEuclideanCLM n := by
  change fderiv ℝ (inclEuclideanCLM n : EuclideanSpace ℝ (Fin (n - 1)) →
      EuclideanSpace ℝ (Fin n)) y = inclEuclideanCLM n
  exact (inclEuclideanCLM n).fderiv

/-- The range of the continuous-linear inclusion `inclEuclideanCLM` equals the
range of the underlying function `inclEuclidean`. -/
private theorem range_inclEuclideanCLM (n : ℕ) [NeZero n] :
    Set.range (inclEuclideanCLM n) = Set.range (inclEuclidean n) := rfl

/-- The standard inward direction `e_0` is transverse to the boundary
hyperplane: it does not lie in the image of the inclusion's derivative. -/
private theorem single_zero_one_transverse (n : ℕ) [NeZero n] :
    ∀ y : EuclideanSpace ℝ (Fin (n - 1)),
      EuclideanSpace.single (0 : Fin n) (1 : ℝ) ∉
        Set.range (fderiv ℝ
          ((modelWithCornersEuclideanHalfSpace n :
              EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n))
            ∘ inclH n
            ∘ (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).symm) y) := by
  intro y
  rw [comp_modelWithCornersEuclideanHalfSpace_inclH_self_symm,
      fderiv_inclEuclidean n y, range_inclEuclideanCLM, range_inclEuclidean]
  exact single_zero_one_notMem_hyperplane n

/-- The hyperplane `{y : EuclideanSpace ℝ (Fin n) | y 0 = 0}` is the kernel of
the continuous linear functional `EuclideanSpace.proj 0`. As a strict linear
subspace of a finite-dim normed space, it has zero additive Haar measure (for
any choice of additive Haar measure on the space). -/
private theorem hyperplane_basisAddHaar_zero (n : ℕ) [NeZero n] :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    haveI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ((Module.finBasis ℝ (EuclideanSpace ℝ (Fin n))).addHaar :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} = 0 := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  haveI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  set ker : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    (EuclideanSpace.proj 0 :
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).toLinearMap.ker with hker_def
  have hsubm : ({y : EuclideanSpace ℝ (Fin n) | y 0 = 0} :
        Set (EuclideanSpace ℝ (Fin n))) = (ker : Set _) := by
    ext y
    simp [hker_def, LinearMap.mem_ker, EuclideanSpace.proj]
  rw [hsubm]
  refine MeasureTheory.Measure.addHaar_submodule
    (μ := (Module.finBasis ℝ (EuclideanSpace ℝ (Fin n))).addHaar) ker ?_
  intro hker_eq
  have h_in_top : EuclideanSpace.single (0 : Fin n) (1 : ℝ) ∈
      (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := Submodule.mem_top
  rw [← hker_eq] at h_in_top
  have h_proj_zero : (EuclideanSpace.proj (0 : Fin n) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = 0 := by
    have := h_in_top
    simp only [hker_def, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at this
    exact this
  have h_eval : (EuclideanSpace.proj (0 : Fin n) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) =
      (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) 0 := rfl
  rw [single_zero_one_apply_zero n] at h_eval
  exact one_ne_zero (h_proj_zero.symm.trans h_eval).symm

/-- The model-level boundary `frontier (Set.range (modelWithCornersEuclideanHalfSpace n))`
has zero `Module.finBasis`-Haar measure. Combines the explicit identification
of the frontier as the hyperplane `{y | y 0 = 0}` with the strict-subspace
null-measure fact. -/
private theorem frontier_range_modelWithCorners_basisAddHaar_zero
    (n : ℕ) [NeZero n] :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    haveI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ((Module.finBasis ℝ (EuclideanSpace ℝ (Fin n))).addHaar :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
      (frontier (Set.range (modelWithCornersEuclideanHalfSpace n))) = 0 := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  haveI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  rw [frontier_range_modelWithCornersEuclideanHalfSpace_eq]
  exact hyperplane_basisAddHaar_zero n

/-- The Euclidean half-space `EuclideanHalfSpace n` (for any `n` with `[NeZero n]`)
is a model with smooth boundary, with boundary modelled on the boundaryless
`EuclideanSpace ℝ (Fin (n - 1))` via the self-model. -/
instance instHasSmoothBoundary (n : ℕ) [NeZero n] :
    HasSmoothBoundary
      (EuclideanSpace ℝ (Fin n))
      (EuclideanHalfSpace n)
      (modelWithCornersEuclideanHalfSpace n) where
  boundaryE := EuclideanSpace ℝ (Fin (n - 1))
  boundaryENormedGroup := inferInstance
  boundaryENormedSpace := inferInstance
  boundaryEInnerProductSpace := inferInstance
  boundaryEFiniteDimensional := inferInstance
  boundaryH := EuclideanSpace ℝ (Fin (n - 1))
  boundaryHTopologicalSpace := inferInstance
  boundaryI := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))
  boundaryIBoundaryless := inferInstance
  inclH := inclH n
  inclH_continuous := inclH_continuous n
  inclH_injective := inclH_injective n
  inclH_isInducing := inclH_isInducing n
  inclH_isClosed_image := by
    rw [range_modelWithCorners_comp_inclH]
    have heq :
        {y : EuclideanSpace ℝ (Fin n) | y 0 = 0}
          = (fun y : EuclideanSpace ℝ (Fin n) => y 0) ⁻¹' {0} := rfl
    rw [heq]
    refine IsClosed.preimage ?_ isClosed_singleton
    exact PiLp.continuous_apply 2 _ 0
  projE := projEuclidean n
  projE_continuous := projEuclidean_continuous n
  projE_contDiff := projEuclidean_contDiff n
  I_inclH_boundaryI_symm_contDiff := by
    rw [comp_modelWithCornersEuclideanHalfSpace_inclH_self_symm]
    exact inclEuclidean_contDiff n
  range_I_inclH := by
    rw [range_modelWithCorners_comp_inclH,
        frontier_range_modelWithCornersEuclideanHalfSpace_eq]
  proj_inclH_compat := by
    intro x
    change projEuclidean n (inclEuclidean n x) = x
    exact projEuclidean_inclEuclidean n x
  inwardCoordE := EuclideanSpace.single (0 : Fin n) (1 : ℝ)
  inwardCoordE_transverse := single_zero_one_transverse n
  range_frontier_basis_addHaar_zero := by
    intro _
    exact frontier_range_modelWithCorners_basisAddHaar_zero n
  finrank_boundaryE_succ := by
    intro _
    rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    exact Nat.sub_one_add_one_eq_of_pos (Nat.pos_of_neZero n)

/-- Test: the boundary normed model of the half-space instance is the
`(n - 1)`-dimensional Euclidean space. -/
example (n : ℕ) [NeZero n] :
    HasSmoothBoundary.boundaryModelE
      (modelWithCornersEuclideanHalfSpace n)
      = EuclideanSpace ℝ (Fin (n - 1)) := rfl

/-- Test: the boundary topological model of the half-space instance is the
same `(n - 1)`-dimensional Euclidean space. -/
example (n : ℕ) [NeZero n] :
    HasSmoothBoundary.boundaryModelH
      (modelWithCornersEuclideanHalfSpace n)
      = EuclideanSpace ℝ (Fin (n - 1)) := rfl

/-- Test: the boundary model with corners is the boundaryless self-model. -/
example (n : ℕ) [NeZero n] :
    HasSmoothBoundary.boundaryModel
      (modelWithCornersEuclideanHalfSpace n)
      = modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1))) := rfl

/-- Test: the projection drops the first coordinate, as a `C^∞` map. -/
example (n : ℕ) [NeZero n] :
    ContDiff ℝ ∞ (instHasSmoothBoundary n).projE := projEuclidean_contDiff n

/-- The "trivial" base-coordinate identification on the canonical self-charted
model `EuclideanHalfSpace n`. The inverse trivialisation of the tangent bundle
at any base point, evaluated at any other point in the chart source, sends
`inwardCoordE` back to `inwardCoordE` (under the type alias
`TangentSpace (𝓡∂ n) y = EuclideanSpace ℝ (Fin n)`). -/
private theorem inwardCoordAt_self_charted_eq
    (n : ℕ) [NeZero n]
    (α y : DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.BoundaryManifold
      (modelWithCornersEuclideanHalfSpace n) (EuclideanHalfSpace n))
    (hy : (y : EuclideanHalfSpace n) ∈
      (chartAt (EuclideanHalfSpace n) (α : EuclideanHalfSpace n)).source) :
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt
      (M := EuclideanHalfSpace n) α y =
      (instHasSmoothBoundary n).inwardCoordE := by
  change ((trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (modelWithCornersEuclideanHalfSpace n)) (α : EuclideanHalfSpace n)).symm
        (y : EuclideanHalfSpace n)) (instHasSmoothBoundary n).inwardCoordE =
      (instHasSmoothBoundary n).inwardCoordE
  have h_symmL :
      ((trivializationAt (EuclideanSpace ℝ (Fin n))
          (TangentSpace (modelWithCornersEuclideanHalfSpace n))
          (α : EuclideanHalfSpace n)).symmL ℝ (y : EuclideanHalfSpace n)) =
        (tangentBundleCore (modelWithCornersEuclideanHalfSpace n) (EuclideanHalfSpace n)).coordChange
          (achart (EuclideanHalfSpace n) (α : EuclideanHalfSpace n))
          (achart (EuclideanHalfSpace n) (y : EuclideanHalfSpace n))
          (y : EuclideanHalfSpace n) :=
    TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) hy
  have h_symm_to_symmL :
      ((trivializationAt (EuclideanSpace ℝ (Fin n))
          (TangentSpace (modelWithCornersEuclideanHalfSpace n))
          (α : EuclideanHalfSpace n)).symm
            (y : EuclideanHalfSpace n)) (instHasSmoothBoundary n).inwardCoordE =
        ((trivializationAt (EuclideanSpace ℝ (Fin n))
            (TangentSpace (modelWithCornersEuclideanHalfSpace n))
            (α : EuclideanHalfSpace n)).symmL ℝ (y : EuclideanHalfSpace n))
              (instHasSmoothBoundary n).inwardCoordE := rfl
  rw [h_symm_to_symmL, h_symmL]
  rw [tangentBundleCore_coordChange_achart]
  set z₀ : EuclideanSpace ℝ (Fin n) := extChartAt (modelWithCornersEuclideanHalfSpace n)
                                          (α : EuclideanHalfSpace n) (y : EuclideanHalfSpace n)
  have h_z₀_in_range :
      z₀ ∈ Set.range (modelWithCornersEuclideanHalfSpace n :
                        EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n)) := by
    show z₀ ∈ Set.range (modelWithCornersEuclideanHalfSpace n)
    refine ⟨(y : EuclideanHalfSpace n), ?_⟩
    change (modelWithCornersEuclideanHalfSpace n) (y : EuclideanHalfSpace n) = z₀
    change (modelWithCornersEuclideanHalfSpace n) (y : EuclideanHalfSpace n) =
        extChartAt (modelWithCornersEuclideanHalfSpace n) (α : EuclideanHalfSpace n)
          (y : EuclideanHalfSpace n)
    rfl
  have h_phi_eq_id_on_range :
      ∀ z ∈ Set.range (modelWithCornersEuclideanHalfSpace n :
                        EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n)),
        ((extChartAt (modelWithCornersEuclideanHalfSpace n) (y : EuclideanHalfSpace n)) ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace n) (α : EuclideanHalfSpace n)).symm) z = z := by
    intro z hz
    rcases hz with ⟨h, rfl⟩
    change (modelWithCornersEuclideanHalfSpace n) ((modelWithCornersEuclideanHalfSpace n).symm
            (modelWithCornersEuclideanHalfSpace n h)) =
          (modelWithCornersEuclideanHalfSpace n) h
    rw [(modelWithCornersEuclideanHalfSpace n).left_inv h]
  have h_eq_on_range :
      Set.EqOn ((extChartAt (modelWithCornersEuclideanHalfSpace n) (y : EuclideanHalfSpace n)) ∘
                  (extChartAt (modelWithCornersEuclideanHalfSpace n) (α : EuclideanHalfSpace n)).symm)
                (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
                (Set.range (modelWithCornersEuclideanHalfSpace n)) := by
    intro z hz
    exact h_phi_eq_id_on_range z hz
  have h_fderiv_phi :
      fderivWithin ℝ ((extChartAt (modelWithCornersEuclideanHalfSpace n) (y : EuclideanHalfSpace n)) ∘
                       (extChartAt (modelWithCornersEuclideanHalfSpace n) (α : EuclideanHalfSpace n)).symm)
        (Set.range (modelWithCornersEuclideanHalfSpace n)) z₀ =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have h_unique :
        UniqueDiffWithinAt ℝ (Set.range (modelWithCornersEuclideanHalfSpace n)) z₀ :=
      (modelWithCornersEuclideanHalfSpace n).uniqueDiffOn z₀ h_z₀_in_range
    rw [fderivWithin_congr h_eq_on_range (h_eq_on_range h_z₀_in_range), fderivWithin_id h_unique]
  rw [h_fderiv_phi]
  rfl

/-- The orientation property holds for the canonical self-charted
`EuclideanHalfSpace n`: for any two boundary base points `α₀, α₁` and any
boundary point `y` in their chart sources, the chart-α₀ and chart-α₁
inward-direction representatives at `y` agree. Hence `c = 1` realises the
orientation. -/
instance instHasOrientableBoundary_self_EuclideanHalfSpace
    (n : ℕ) [NeZero n] :
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasOrientableBoundary
      (E := EuclideanSpace ℝ (Fin n))
      (H := EuclideanHalfSpace n)
      (I := modelWithCornersEuclideanHalfSpace n)
      (EuclideanHalfSpace n) where
  inwardCoord_chart_consistent := by
    intro α₀ α₁ y hα₀ hα₁
    refine ⟨1, by norm_num, ?_⟩
    have h₀ := inwardCoordAt_self_charted_eq n α₀ y hα₀
    have h₁ := inwardCoordAt_self_charted_eq n α₁ y hα₁
    rw [h₀, h₁]
    simp only [one_smul, sub_self]
    exact ⟨0, map_zero _⟩

end EuclideanHalfSpaceInstance

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
