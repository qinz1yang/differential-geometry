import DifferentialGeometry.Integral.L2.CompactSupport
import DifferentialGeometry.Integral.L2.Pairing.CauchySchwarz
import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Topology.Algebra.Support
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

/-!
# Compactly-supported smooth `(r, s)`-tensor sections

Let `M` be a smooth finite-dimensional manifold modelled on a real normed
space `E` equipped with a smooth Riemannian metric `g`.  The mixed
`(r, s)`-tensor bundle of `M` has fixed model fiber
`TensorRSModel r s ℝ E`, and we consider here its smooth sections whose
underlying map `M → TensorRSModel r s ℝ E` has compact support.

This file packages two views of these sections:

* `compactlySupportedSmoothTensorSections I M r s` — the `ℝ`-submodule of
  `Cₛ^∞⟮I; TensorRSModel r s ℝ E, fun x : M => TensorRSSpace r s I x⟯`
  cut out by the compact-support condition; closure under pointwise
  addition and real scalar multiplication follows from the standard
  `HasCompactSupport` closure lemmas.
* `SmoothCcTensor g r s` — a structure wrapper carrying the same data as
  the submodule alongside an explicit Riemannian-metric parameter `g`.
  The parameter `g` does not appear in the carrier, but having it as a
  type-level parameter allows downstream files to attach
  metric-dependent inner-product / norm instances cleanly without diamond
  risk.

The wrapper carries the standard `AddCommGroup` and `Module ℝ` structure
inherited from the underlying section type via `Function.Injective`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open Manifold Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The `ℝ`-submodule of smooth `(r, s)`-tensor sections whose underlying
map to the model fiber `TensorRSModel r s ℝ E` (via
`TensorRSSpace.toModel`) has compact support.  Closure under pointwise
addition and real scalar multiplication follows from the standard
`HasCompactSupport` closure lemmas. -/
def compactlySupportedSmoothTensorSections
    (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (r s : ℕ) :
    Submodule ℝ (Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) where
  carrier :=
    { S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯ |
        HasCompactSupport
          (fun x : M => TensorRSSpace.toModel (S x)) }
  zero_mem' := by
    change HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        ((0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x))
    have h : (fun x : M => TensorRSSpace.toModel
        ((0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x)) =
        (fun _ : M => (0 : TensorRSModel r s ℝ E)) := by
      funext x
      simp [ContMDiffSection.coe_zero,
        TensorRSSpace.toModel_zero]
    rw [h]
    exact HasCompactSupport.zero
  add_mem' := by
    intro S T hS hT
    change HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        ((S + T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x))
    have h : (fun x : M => TensorRSSpace.toModel
        ((S + T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x)) =
        (fun x : M => TensorRSSpace.toModel (S x)) +
          (fun x : M => TensorRSSpace.toModel (T x)) := by
      funext x
      simp [ContMDiffSection.coe_add, Pi.add_apply,
        TensorRSSpace.toModel_add]
    rw [h]
    exact hS.add hT
  smul_mem' := by
    intro c S hS
    change HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        ((c • S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x))
    have h : (fun x : M => TensorRSSpace.toModel
        ((c • S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x)) =
        (fun _ : M => c) •
          (fun x : M => TensorRSSpace.toModel (S x)) := by
      funext x
      simp [ContMDiffSection.coe_smul, Pi.smul_apply,
        TensorRSSpace.toModel_smul]
    rw [h]
    exact hS.smul_left

@[simp]
lemma mem_compactlySupportedSmoothTensorSections {r s : ℕ}
    {S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯} :
    S ∈ compactlySupportedSmoothTensorSections I M r s ↔
      HasCompactSupport
        (fun x : M => TensorRSSpace.toModel (S x)) := Iff.rfl

/-- A smooth, compactly-supported `(r, s)`-tensor section, packaged
together with an explicit Riemannian-metric parameter `g`.

The metric `g` does not appear in the underlying data fields; its role is
solely to make `SmoothCcTensor g r s` a different Lean type for each
metric, so that downstream files can attach metric-dependent
inner-product / norm instances cleanly. -/
structure SmoothCcTensor (g : SmoothRiemannianMetric I M) (r s : ℕ) where
  /-- The underlying smooth section. -/
  toSection : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
    (fun x : M => TensorRSSpace r s I x)⟯
  /-- The underlying map to the model fiber has compact support. -/
  hasCompactSupport :
    HasCompactSupport (fun x : M => TensorRSSpace.toModel (toSection x))

namespace SmoothCcTensor

set_option linter.unusedSectionVars false in
/-- Function-coercion of a `SmoothCcTensor` to its underlying map
`M → TensorRSModel r s ℝ E`. -/
def toFun {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) : M → TensorRSModel r s ℝ E :=
  fun x => TensorRSSpace.toModel (S.toSection x)

set_option linter.unusedSectionVars false in
@[simp] lemma toFun_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (x : M) :
    S.toFun x = TensorRSSpace.toModel (S.toSection x) := rfl

set_option linter.unusedSectionVars false in
@[ext] lemma ext
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S T : SmoothCcTensor g r s} (h : S.toSection = T.toSection) :
    S = T := by
  cases S; cases T; congr

end SmoothCcTensor

section Algebra

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

set_option linter.unusedSectionVars false in
instance : Zero (SmoothCcTensor g r s) where
  zero :=
    { toSection := 0
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            (fun _ : M => (0 : TensorRSModel r s ℝ E)) := by
          funext x
          simp [ContMDiffSection.coe_zero,
            TensorRSSpace.toModel_zero]
        rw [h]
        exact HasCompactSupport.zero }

set_option linter.unusedSectionVars false in
instance : Add (SmoothCcTensor g r s) where
  add S T :=
    { toSection := S.toSection + T.toSection
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((S.toSection + T.toSection :
              Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            (fun x : M => TensorRSSpace.toModel (S.toSection x)) +
              (fun x : M => TensorRSSpace.toModel (T.toSection x)) := by
          funext x
          simp [ContMDiffSection.coe_add, Pi.add_apply,
            TensorRSSpace.toModel_add]
        rw [h]
        exact S.hasCompactSupport.add T.hasCompactSupport }

set_option linter.unusedSectionVars false in
instance : Neg (SmoothCcTensor g r s) where
  neg S :=
    { toSection := -S.toSection
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((-S.toSection : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            -(fun x : M => TensorRSSpace.toModel (S.toSection x)) := by
          funext x
          simp [ContMDiffSection.coe_neg, Pi.neg_apply,
            TensorRSSpace.toModel_neg]
        rw [h]
        exact S.hasCompactSupport.neg }

set_option linter.unusedSectionVars false in
instance : Sub (SmoothCcTensor g r s) where
  sub S T :=
    { toSection := S.toSection - T.toSection
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((S.toSection - T.toSection :
              Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            (fun x : M => TensorRSSpace.toModel (S.toSection x)) -
              (fun x : M => TensorRSSpace.toModel (T.toSection x)) := by
          funext x
          simp [ContMDiffSection.coe_sub, Pi.sub_apply,
            TensorRSSpace.toModel_sub]
        rw [h]
        exact S.hasCompactSupport.sub T.hasCompactSupport }

set_option linter.unusedSectionVars false in
instance : SMul ℝ (SmoothCcTensor g r s) where
  smul c S :=
    { toSection := c • S.toSection
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((c • S.toSection :
              Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            (fun _ : M => c) •
              (fun x : M => TensorRSSpace.toModel (S.toSection x)) := by
          funext x
          simp [ContMDiffSection.coe_smul, Pi.smul_apply,
            TensorRSSpace.toModel_smul]
        rw [h]
        exact S.hasCompactSupport.smul_left }

set_option linter.unusedSectionVars false in
/-- The natural projection `SmoothCcTensor g r s → Cₛ^∞⟮…⟯` is injective. -/
lemma SmoothCcTensor.toSection_injective :
    Function.Injective (fun S : SmoothCcTensor g r s => S.toSection) := by
  intro S T h
  exact SmoothCcTensor.ext h

set_option linter.unusedSectionVars false in
@[simp] lemma SmoothCcTensor.toSection_zero :
    (0 : SmoothCcTensor g r s).toSection = 0 := rfl

set_option linter.unusedSectionVars false in
@[simp] lemma SmoothCcTensor.toSection_add (S T : SmoothCcTensor g r s) :
    (S + T).toSection = S.toSection + T.toSection := rfl

set_option linter.unusedSectionVars false in
@[simp] lemma SmoothCcTensor.toSection_neg (S : SmoothCcTensor g r s) :
    (-S).toSection = -S.toSection := rfl

set_option linter.unusedSectionVars false in
@[simp] lemma SmoothCcTensor.toSection_sub (S T : SmoothCcTensor g r s) :
    (S - T).toSection = S.toSection - T.toSection := rfl

set_option linter.unusedSectionVars false in
@[simp] lemma SmoothCcTensor.toSection_smul (c : ℝ) (S : SmoothCcTensor g r s) :
    (c • S).toSection = c • S.toSection := rfl

set_option linter.unusedSectionVars false in
instance : SMul ℕ (SmoothCcTensor g r s) := ⟨nsmulRec⟩

set_option linter.unusedSectionVars false in
instance : SMul ℤ (SmoothCcTensor g r s) := ⟨zsmulRec⟩

set_option linter.unusedSectionVars false in
@[simp] lemma SmoothCcTensor.toSection_nsmul (S : SmoothCcTensor g r s) (n : ℕ) :
    (n • S).toSection = n • S.toSection := by
  induction n with
  | zero =>
    change (nsmulRec 0 S).toSection = (0 : ℕ) • S.toSection
    simp [nsmulRec]
  | succ n ih =>
    change (nsmulRec (n + 1) S).toSection = (n + 1) • S.toSection
    change (nsmulRec n S + S).toSection = (n + 1) • S.toSection
    have hn : (nsmulRec n S).toSection = n • S.toSection := ih
    rw [SmoothCcTensor.toSection_add, hn, succ_nsmul]

set_option linter.unusedSectionVars false in
@[simp] lemma SmoothCcTensor.toSection_zsmul (S : SmoothCcTensor g r s) (z : ℤ) :
    (z • S).toSection = z • S.toSection := by
  rcases z with n | n
  · change (n • S).toSection = (Int.ofNat n) • S.toSection
    rw [SmoothCcTensor.toSection_nsmul]
    simp
  · change (-((n + 1) • S)).toSection = (Int.negSucc n) • S.toSection
    rw [SmoothCcTensor.toSection_neg, SmoothCcTensor.toSection_nsmul]
    show -((n + 1) • S.toSection) =
      Int.negSucc n • S.toSection
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

set_option linter.unusedSectionVars false in
instance : AddCommGroup (SmoothCcTensor g r s) :=
  SmoothCcTensor.toSection_injective.addCommGroup
    (fun S => S.toSection)
    SmoothCcTensor.toSection_zero
    SmoothCcTensor.toSection_add
    SmoothCcTensor.toSection_neg
    SmoothCcTensor.toSection_sub
    SmoothCcTensor.toSection_nsmul
    SmoothCcTensor.toSection_zsmul

set_option linter.unusedSectionVars false in
/-- The additive monoid homomorphism from `SmoothCcTensor g r s` to the
underlying smooth section type. -/
def SmoothCcTensor.toSectionAddHom :
    SmoothCcTensor g r s →+ Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯ where
  toFun := fun S => S.toSection
  map_zero' := SmoothCcTensor.toSection_zero
  map_add' := SmoothCcTensor.toSection_add

set_option linter.unusedSectionVars false in
instance : Module ℝ (SmoothCcTensor g r s) :=
  SmoothCcTensor.toSection_injective.module ℝ
    SmoothCcTensor.toSectionAddHom
    SmoothCcTensor.toSection_smul

set_option linter.unusedSectionVars false in
@[simp] lemma SmoothCcTensor.toFun_zero :
    (0 : SmoothCcTensor g r s).toFun = 0 := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_zero,
    ContMDiffSection.coe_zero, TensorRSSpace.toModel_zero]

set_option linter.unusedSectionVars false in
@[simp] lemma SmoothCcTensor.toFun_add (S T : SmoothCcTensor g r s) :
    (S + T).toFun = S.toFun + T.toFun := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_add, Pi.add_apply, TensorRSSpace.toModel_add]

set_option linter.unusedSectionVars false in
@[simp] lemma SmoothCcTensor.toFun_neg (S : SmoothCcTensor g r s) :
    (-S).toFun = -S.toFun := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_neg,
    ContMDiffSection.coe_neg, Pi.neg_apply, TensorRSSpace.toModel_neg]

set_option linter.unusedSectionVars false in
@[simp] lemma SmoothCcTensor.toFun_sub (S T : SmoothCcTensor g r s) :
    (S - T).toFun = S.toFun - T.toFun := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply, TensorRSSpace.toModel_sub]

set_option linter.unusedSectionVars false in
@[simp] lemma SmoothCcTensor.toFun_smul (c : ℝ) (S : SmoothCcTensor g r s) :
    (c • S).toFun = c • S.toFun := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_smul,
    ContMDiffSection.coe_smul, Pi.smul_apply, TensorRSSpace.toModel_smul]

end Algebra

end L2
end Integral
end DifferentialGeometry

end
