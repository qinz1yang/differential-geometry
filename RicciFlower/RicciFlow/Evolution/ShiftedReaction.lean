import RicciFlower.DimensionThree.RicciControlsRm
import RicciFlower.MaximumPrinciple.TensorWeak.TensorBackedReaction

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Shifted pinching reaction algebra

This file contains the tensor-backed algebra for the shifted pinching tensor
`S = Ric - δ R g` used in Hamilton's Section 9 tensor WMP application.
It sits below `RicciPreservation.lean`, so the preservation file can consume
canonical reaction producers without creating import cycles.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Realized
open Bundle
open Tensor0SBundle
open scoped BigOperators Manifold ContDiff

/-! ## Pure three-dimensional reaction algebra -/

/-- Matrix square of Ricci components in an orthonormal `Fin 3` basis. -/
def ricciSq3 (Ric : Fin 3 -> Fin 3 -> Real) (i j : Fin 3) : Real :=
  ∑ k : Fin 3, Ric i k * Ric k j

/-- Ricci component trace in an orthonormal `Fin 3` basis. -/
def ricciScal3 (Ric : Fin 3 -> Fin 3 -> Real) : Real :=
  ∑ i : Fin 3, Ric i i

/-- Ricci component norm square in an orthonormal `Fin 3` basis. -/
def ricciNorm3 (Ric : Fin 3 -> Fin 3 -> Real) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3, Ric i j * Ric i j

/-- Ricci-flow Ricci reaction in dimension three:
`2 R_ikjl Ric_kl - 2 Ric_i^k Ric_kj`, in an orthonormal basis. -/
def ricciPresReact
    (Rm : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (Ric : Fin 3 -> Fin 3 -> Real) (i j : Fin 3) : Real :=
  2 * (∑ k : Fin 3, ∑ l : Fin 3, Rm i k j l * Ric k l) -
    2 * ricciSq3 Ric i j

/-- Shifted pinching reaction for `S = Ric - delta R g` in an orthonormal basis. -/
def pinchReact
    (delta : Real)
    (Rm : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (Ric : Fin 3 -> Fin 3 -> Real) (i j : Fin 3) : Real :=
  ricciPresReact Rm Ric i j -
    2 * delta * (ricciNorm3 Ric * RicciFlower.DimensionThree.delta3 i j -
      ricciScal3 Ric * Ric i j)

/-- Standard three-dimensional Riemann-from-Ricci component model for an
arbitrary Ricci matrix in an orthonormal `Fin 3` basis. -/
def stdRmOfRic3
    (Ric : Fin 3 -> Fin 3 -> Real)
    (i j k l : Fin 3) : Real :=
  RicciFlower.DimensionThree.delta3 i k * Ric j l
    - RicciFlower.DimensionThree.delta3 i l * Ric j k
    - RicciFlower.DimensionThree.delta3 j k * Ric i l
    + RicciFlower.DimensionThree.delta3 j l * Ric i k
    - (1 / 2 : Real) * ricciScal3 Ric *
        (RicciFlower.DimensionThree.delta3 i k *
            RicciFlower.DimensionThree.delta3 j l -
          RicciFlower.DimensionThree.delta3 i l *
            RicciFlower.DimensionThree.delta3 j k)

/-- Adding a scalar multiple of the orthonormal metric to Ricci changes the
shifted reaction only linearly.  The quadratic terms cancel in the shifted
combination. -/
theorem pinchReact_add_g00
    (delta a : Real) (Ric : Fin 3 -> Fin 3 -> Real) :
    pinchReact delta
        (stdRmOfRic3
          (fun p q : Fin 3 =>
            Ric p q + a * RicciFlower.DimensionThree.delta3 p q))
        (fun p q : Fin 3 =>
          Ric p q + a * RicciFlower.DimensionThree.delta3 p q) 0 0 -
      pinchReact delta (stdRmOfRic3 Ric) Ric 0 0 =
        a * (2 * delta - 1) *
          (3 * Ric 0 0 - ricciScal3 Ric) := by
  unfold pinchReact ricciPresReact ricciSq3 ricciNorm3 stdRmOfRic3
    RicciFlower.DimensionThree.delta3
  simp [Fin.sum_univ_three, ricciScal3]
  ring_nf

/-- Lemma 9.1 reaction algebra at a Ricci-null eigenvector. -/
theorem ricciReactNull
    (l1 l2 l3 : Real) (hnull : l1 = 0) :
    ricciPresReact (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0 =
      (l2 - l3) ^ 2 := by
  subst l1
  unfold ricciPresReact ricciSq3 RicciFlower.DimensionThree.stdRmDiag3
    RicciFlower.DimensionThree.ricciDiag3 RicciFlower.DimensionThree.ricciEigenScalar3
    RicciFlower.DimensionThree.delta3
  simp [Fin.sum_univ_three]
  ring

/-- Nonnegativity form of `ricciReactNull`. -/
theorem ricciReact_ge
    (l1 l2 l3 : Real) (hnull : l1 = 0) :
    0 <= ricciPresReact (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0 := by
  rw [ricciReactNull l1 l2 l3 hnull]
  positivity

/-- Lemma 9.2 shifted reaction algebra at a pinching-null eigenvector. -/
theorem pinchReactNull
    (delta l1 l2 l3 : Real)
    (hnull : l1 = delta * RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3) :
    pinchReact delta (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0 =
      delta ^ 2 * (1 - 3 * delta) *
          RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3 ^ 2 +
        (1 - delta) * (l2 - l3) ^ 2 := by
  let lhs :=
    pinchReact delta (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0
  let rhs :=
    delta ^ 2 * (1 - 3 * delta) *
        RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3 ^ 2 +
      (1 - delta) * (l2 - l3) ^ 2
  change lhs = rhs
  have hrel : delta * (l1 + l2 + l3) - l1 = 0 := by
    unfold RicciFlower.DimensionThree.ricciEigenScalar3 at hnull
    nlinarith
  have hfactor :
      lhs - rhs =
        (delta * (l1 + l2 + l3) - l1) *
          (3 * delta ^ 2 * l1 + 3 * delta ^ 2 * l2 + 3 * delta ^ 2 * l3 +
            2 * delta * l1 - delta * l2 - delta * l3 + 2 * l1 - l2 - l3) := by
    dsimp [lhs, rhs]
    unfold pinchReact ricciPresReact ricciSq3 ricciNorm3 ricciScal3
      RicciFlower.DimensionThree.stdRmDiag3 RicciFlower.DimensionThree.ricciDiag3
      RicciFlower.DimensionThree.ricciEigenScalar3 RicciFlower.DimensionThree.delta3
    simp [Fin.sum_univ_three]
    ring
  have hzero : lhs - rhs = 0 := by
    rw [hfactor, hrel]
    ring
  nlinarith

/-- Nonnegativity form of `pinchReactNull` for `0 <= delta <= 1/3`. -/
theorem pinchReact_ge
    (delta l1 l2 l3 : Real)
    (hdelta0 : 0 <= delta) (hdelta13 : delta <= (1 : Real) / 3)
    (hnull : l1 = delta * RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3) :
    0 <= pinchReact delta (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0 := by
  rw [pinchReactNull delta l1 l2 l3 hnull]
  have h1 : 0 <= delta ^ 2 * (1 - 3 * delta) *
      RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3 ^ 2 := by
    have hdelta_sq : 0 <= delta ^ 2 := sq_nonneg delta
    have hcoeff : 0 <= 1 - 3 * delta := by nlinarith
    have hscalar_sq : 0 <= RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3 ^ 2 :=
      sq_nonneg _
    positivity
  have h2 : 0 <= (1 - delta) * (l2 - l3) ^ 2 := by
    have hcoeff : 0 <= 1 - delta := by nlinarith
    have hsquare : 0 <= (l2 - l3) ^ 2 := sq_nonneg _
    positivity
  exact add_nonneg h1 h2

/-! ## Strict shifted first-null algebra -/

/-- Scalar reconstructed from a diagonal shifted first-null tensor
`diag(0,a,b) = Ric - delta * R g` in dimension three. -/
def shiftScal3 (delta a b : Real) : Real :=
  (a + b) / (1 - 3 * delta)

def shiftRic1 (delta a b : Real) : Real := delta * shiftScal3 delta a b
def shiftRic2 (delta a b : Real) : Real := a + delta * shiftScal3 delta a b
def shiftRic3 (delta a b : Real) : Real := b + delta * shiftScal3 delta a b

/-- Trace identity for the reconstructed diagonal Ricci tensor. -/
theorem shiftScal3_eq
    (delta a b : Real) (hdelta13 : delta < (1 : Real) / 3) :
    RicciFlower.DimensionThree.ricciEigenScalar3
      (shiftRic1 delta a b) (shiftRic2 delta a b) (shiftRic3 delta a b) =
      shiftScal3 delta a b := by
  have hden : 1 - 3 * delta ≠ 0 := by
    nlinarith
  have hden' : 1 - delta * 3 ≠ 0 := by
    nlinarith
  unfold RicciFlower.DimensionThree.ricciEigenScalar3
    shiftRic1 shiftRic2 shiftRic3 shiftScal3
  field_simp [hden, hden']
  ring

/-- The reconstructed first Ricci eigenvalue is exactly `delta * R`. -/
theorem shiftNull3
    (delta a b : Real) (hdelta13 : delta < (1 : Real) / 3) :
    shiftRic1 delta a b =
      delta * RicciFlower.DimensionThree.ricciEigenScalar3
        (shiftRic1 delta a b) (shiftRic2 delta a b) (shiftRic3 delta a b) := by
  rw [shiftScal3_eq delta a b hdelta13]
  rfl

/-- Strict-delta shifted pinching null reaction in diagonal form. -/
theorem pinchShiftNull_ge
    (delta a b : Real)
    (hdelta0 : 0 <= delta) (hdelta13 : delta < (1 : Real) / 3) :
    0 <= pinchReact delta
      (RicciFlower.DimensionThree.stdRmDiag3
        (shiftRic1 delta a b) (shiftRic2 delta a b) (shiftRic3 delta a b))
      (RicciFlower.DimensionThree.ricciDiag3
        (shiftRic1 delta a b) (shiftRic2 delta a b) (shiftRic3 delta a b))
      0 0 := by
  exact pinchReact_ge delta
    (shiftRic1 delta a b) (shiftRic2 delta a b) (shiftRic3 delta a b)
    hdelta0 (le_of_lt hdelta13) (shiftNull3 delta a b hdelta13)

/-- Scalar target for the shifted pinching reaction at a reconstructed
first-null diagonal tensor. -/
def shiftReact3 (delta a b : Real) : Real :=
  pinchReact delta
    (RicciFlower.DimensionThree.stdRmDiag3
      (shiftRic1 delta a b) (shiftRic2 delta a b) (shiftRic3 delta a b))
    (RicciFlower.DimensionThree.ricciDiag3
      (shiftRic1 delta a b) (shiftRic2 delta a b) (shiftRic3 delta a b))
    0 0

/-- Strict-delta nonnegativity of the compact shifted reaction target. -/
theorem shiftReact3_nonneg
    (delta a b : Real)
    (hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3) :
    0 <= shiftReact3 delta a b := by
  exact pinchShiftNull_ge delta a b (le_of_lt hdelta0) hdelta13

/-- Components of a shifted first-null block
`S = Ric - delta * R * g` in an orthonormal basis whose first vector is null:
`[[0,0,0],[0,a,c],[0,c,b]]`. -/
def shiftBlockS3 (a b c : Real) (i j : Fin 3) : Real :=
  if i = 0 then 0
  else if j = 0 then 0
  else if i = 1 then
    if j = 1 then a else c
  else
    if j = 1 then c else b

/-- Ricci components reconstructed from a shifted first-null block. -/
def shiftRicBlock3 (delta a b c : Real) (i j : Fin 3) : Real :=
  shiftBlockS3 a b c i j +
    delta * shiftScal3 delta a b * RicciFlower.DimensionThree.delta3 i j

/-- Shifted pinching reaction at a first-null block, using the full
three-dimensional Riemann-from-Ricci model rather than a diagonal model. -/
def shiftReactBlock3 (delta a b c : Real) : Real :=
  pinchReact delta
    (stdRmOfRic3 (shiftRicBlock3 delta a b c))
    (shiftRicBlock3 delta a b c) 0 0

/-- Explicit block expansion of the shifted first-null reaction. -/
theorem shiftReactBlock3_eq
    (delta a b c : Real) (hdelta13 : delta < (1 : Real) / 3) :
    shiftReactBlock3 delta a b c =
      delta ^ 2 * (1 - 3 * delta) * shiftScal3 delta a b ^ 2 +
        (1 - delta) * ((a - b) ^ 2 + 4 * c ^ 2) := by
  have hden : 1 - 3 * delta ≠ 0 := by nlinarith
  have hden' : 1 - delta * 3 ≠ 0 := by nlinarith
  have hden2 : 1 - delta * 6 + delta ^ 2 * 9 ≠ 0 := by
    have hsq : (1 - delta * 3) ^ 2 ≠ 0 := pow_ne_zero 2 hden'
    convert hsq using 1
    ring
  unfold shiftReactBlock3 pinchReact ricciPresReact ricciSq3 ricciNorm3
    stdRmOfRic3 shiftRicBlock3 shiftBlockS3 shiftScal3
    RicciFlower.DimensionThree.delta3
  simp [Fin.sum_univ_three, ricciScal3]
  field_simp [hden, hden', hden2]
  ring_nf

/-- Nonnegativity of the shifted first-null block reaction for all
`delta < 1/3`.  This includes the Ricci-preservation case `delta = 0`. -/
theorem shiftReactBlock3_nonneg_of_lt
    (delta a b c : Real) (hdelta13 : delta < (1 : Real) / 3) :
    0 <= shiftReactBlock3 delta a b c := by
  rw [shiftReactBlock3_eq delta a b c hdelta13]
  have hcoeff1 : 0 <= 1 - 3 * delta := by nlinarith
  have hcoeff2 : 0 <= 1 - delta := by nlinarith
  have hR2 : 0 <= shiftScal3 delta a b ^ 2 := sq_nonneg _
  have hsq : 0 <= (a - b) ^ 2 + 4 * c ^ 2 := by
    have h1 : 0 <= (a - b) ^ 2 := sq_nonneg _
    have h2 : 0 <= 4 * c ^ 2 := by positivity
    exact add_nonneg h1 h2
  have hterm1 :
      0 <= delta ^ 2 * (1 - 3 * delta) * shiftScal3 delta a b ^ 2 := by
    have hdelta_sq : 0 <= delta ^ 2 := sq_nonneg delta
    positivity
  have hterm2 :
      0 <= (1 - delta) * ((a - b) ^ 2 + 4 * c ^ 2) := by
    positivity
  exact add_nonneg hterm1 hterm2

/-- Strict-delta nonnegativity of the shifted first-null block reaction. -/
theorem shiftReactBlock3_nonneg
    (delta a b c : Real)
    (_hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3) :
    0 <= shiftReactBlock3 delta a b c := by
  exact shiftReactBlock3_nonneg_of_lt delta a b c hdelta13

/-! ## Tensor-backed shifted reconstruction -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- A pointwise shifted first-null block in an orthonormal `Fin 3` basis.

This only records the geometric block shape of the raw tensor.  It does not
assert any reaction formula, and it does not choose the orthonormal basis. -/
structure ShiftBlockAt
    (g : SmoothRiemannianMetric I M)
    (A : RawTwoTensorField (I := I) (M := M)) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (a b c : Real) : Prop where
  orthonormal : DimensionThree.OrthonormalBasisAt (I := I) g x basis
  components :
    ∀ i j : Fin 3,
      A x (basis i) (basis j) = shiftBlockS3 a b c i j

/-- A nonzero scalar multiple of a raw bilinear null vector is null in the
reverse direction. -/
theorem raw_null_of_smul
    {A : RawTwoTensorField (I := I) (M := M)} {x : M}
    {v e : TangentSpace I x} {r : Real}
    (hbilin : TwoTensorBilinearAt (I := I) (M := M) A x)
    (hnull : A x v v = 0) (hscale : v = r • e) (hr : r ≠ 0) :
    A x e e = 0 := by
  have hscale_eval : A x v v = (r * r) * A x e e := by
    rw [hscale, hbilin.smul_left r e (r • e),
      hbilin.smul_right r e e]
    ring
  have hmul : (r * r) * A x e e = 0 := by
    simpa [hscale_eval] using hnull
  have hr2 : r * r ≠ 0 := mul_ne_zero hr hr
  exact (mul_eq_zero.mp hmul).resolve_left hr2

/-- A PSD symmetric bilinear first-null tensor has shifted block components in
any supplied orthonormal basis whose first vector is a normalization of the
null direction. -/
theorem shiftBlockOfNull
    {g : SmoothRiemannianMetric I M}
    {A : RawTwoTensorField (I := I) (M := M)} {x : M}
    {v : TangentSpace I x} {r : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (hsym : TwoTensorSymmetricAt (I := I) (M := M) A x)
    (hbilin : TwoTensorBilinearAt (I := I) (M := M) A x)
    (hpsd : TwoTensorNonnegativeAt (I := I) (M := M) A x)
    (hnull : A x v v = 0) (hscale : v = r • basis 0) (hr : r ≠ 0) :
    ShiftBlockAt (I := I) (M := M) g A x basis
      (A x (basis 1) (basis 1))
      (A x (basis 2) (basis 2))
      (A x (basis 1) (basis 2)) := by
  refine ⟨horth, ?_⟩
  have hnull0 : A x (basis 0) (basis 0) = 0 :=
    raw_null_of_smul (I := I) (M := M) hbilin hnull hscale hr
  have hleft :
      ∀ w : TangentSpace I x, A x (basis 0) w = 0 :=
    psd_null_left_raw (I := I) (M := M) hsym hbilin hpsd hnull0
  have hright :
      ∀ w : TangentSpace I x, A x w (basis 0) = 0 :=
    psd_null_right_raw (I := I) (M := M) hsym hbilin hpsd hnull0
  intro i j
  fin_cases i <;> fin_cases j
  · simp [shiftBlockS3, hnull0]
  · simp [shiftBlockS3, hleft]
  · simp [shiftBlockS3, hleft]
  · simp [shiftBlockS3, hright]
  · simp [shiftBlockS3]
  · simp [shiftBlockS3]
  · simp [shiftBlockS3, hright]
  · simpa [shiftBlockS3] using hsym (basis 2) (basis 1)
  · simp [shiftBlockS3]

/-- An orthonormal `Fin 3` basis adapted to a nonzero null vector.

The first basis vector is a nonzero scalar multiple of `v`; the scalar is
recorded in the orientation used by `shiftBlockOfNull`, namely
`v = r • basis 0`. -/
structure NullOrthonormalBasis3At
    (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) : Type _ where
  basis : Module.Basis (Fin 3) Real (TangentSpace I x)
  orthonormal : DimensionThree.OrthonormalBasisAt (I := I) g x basis
  scale : ∃ r : Real, r ≠ 0 ∧ v = r • basis 0

/-- A nonzero tangent vector in a three-dimensional tangent fiber can be
completed to an orthonormal `Fin 3` basis whose first vector is its
normalization. -/
theorem exists_nullOrthonormalBasis3At
    (g : SmoothRiemannianMetric I M) {x : M}
    {v : TangentSpace I x}
    (hdim : Module.finrank Real (TangentSpace I x) = 3) (hv : v ≠ 0) :
    Nonempty (NullOrthonormalBasis3At (I := I) g x v) := by
  classical
  let D := (tangentMetricData (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _
      D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let e0 : TangentSpace I x := (‖v‖)⁻¹ • v
  let f : Fin 3 -> TangentSpace I x := fun i => if i = 0 then e0 else 0
  let s : Set (Fin 3) := fun i => i = 0
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have he0_norm : ‖e0‖ = 1 := by
    dsimp [e0]
    rw [norm_smul]
    have hinv_nonneg : 0 ≤ (‖v‖)⁻¹ := inv_nonneg.mpr (norm_nonneg v)
    rw [Real.norm_of_nonneg hinv_nonneg]
    exact inv_mul_cancel₀ hvnorm
  have he0_inner : Inner.inner Real e0 e0 = 1 := by
    exact inner_self_eq_one_of_norm_eq_one he0_norm
  have horth : Orthonormal Real (s.restrict f) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := by
      exact Subtype.ext (i.2.trans j.2.symm)
    subst j
    have hval : s.restrict f i = e0 := by
      change f i = e0
      dsimp [f]
      have hi0 : (i : Fin 3) = 0 := i.2
      rw [if_pos hi0]
    rw [hval]
    simp [he0_norm]
  have hcard : Module.finrank Real (TangentSpace I x) = Fintype.card (Fin 3) := by
    simpa using hdim
  obtain ⟨ob, hob⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := Real) (E := TangentSpace I x) (ι := Fin 3)
      hcard horth
  let basis : Module.Basis (Fin 3) Real (TangentSpace I x) := ob.toBasis
  have horth_basis :
      DimensionThree.OrthonormalBasisAt (I := I) g x basis := by
    intro i j
    have hinner :
        Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      MetricFiberData.toCore_inner D (ob i) (ob j)
    change g.inner x (basis i) (basis j) = DimensionThree.delta3 i j
    rw [← TangentMetricData.inner_eq (tangentMetricData (I := I) g x)
      (basis i) (basis j)]
    change D.inner (ob i) (ob j) = DimensionThree.delta3 i j
    rw [← hinner]
    simpa [DimensionThree.delta3] using ob.inner_eq_ite i j
  have hscale : v = ‖v‖ • basis 0 := by
    have hb0 : ob 0 = e0 := by
      have h0s : (0 : Fin 3) ∈ s := by
        rfl
      simpa [f] using hob 0 h0s
    change v = ‖v‖ • ob 0
    rw [hb0]
    dsimp [e0]
    rw [smul_smul]
    rw [mul_inv_cancel₀ hvnorm]
    simp
  exact ⟨⟨basis, horth_basis, ⟨‖v‖, hvnorm, hscale⟩⟩⟩

/-- The scalar reconstructed from a bundled shifted tensor in dimension three:
if `A = Ric - δ R g`, then `R = tr_g A / (1 - 3δ)`. -/
def shiftScalar3At
    (δ : Real) (g : SmoothRiemannianMetric I M) {x : M}
    (A : Tensor02At (I := I) (M := M) x) : Real :=
  metricTracePair0SAt (I := I) g A / (1 - 3 * δ)

/-- Reconstruct the Ricci tensor from a bundled shifted tensor in dimension
three. -/
def shiftRic3At
    (δ : Real) (g : SmoothRiemannianMetric I M) {x : M}
    (A : Tensor02At (I := I) (M := M) x) :
    Tensor02At (I := I) (M := M) x :=
  A + (δ * shiftScalar3At (I := I) (M := M) δ g A) •
    metricTensorField (I := I) g x

/-- The metric tensor has trace three in an orthonormal `Fin 3` basis. -/
theorem metricTrace_metric3
    {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis) :
    metricTracePair0SAt (I := I) g
        (metricTensorField (I := I) g x) = 3 := by
  have hinv : MetricInverseInBasis (I := I) g x basis DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis horth
  have horth' :
      ∀ i j : Fin 3, g.inner x (basis i) (basis j) =
        DimensionThree.delta3 i j := horth
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
    DimensionThree.delta3 hinv]
  norm_num [Fin.sum_univ_three, DimensionThree.delta3, metricTensorField_apply,
    horth', vec2, RicciFlower.Curvature.vec2]

/-- Adding `c g` to a shifted tensor adds `3c / (1 - 3 delta)` to the
reconstructed scalar. -/
theorem shiftScalar_add_g
    {δ c : Real} {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (A : Tensor02At (I := I) (M := M) x) :
    shiftScalar3At (I := I) (M := M) δ g
        (A + c • metricTensorField (I := I) g x) =
      shiftScalar3At (I := I) (M := M) δ g A +
        (3 * c) / (1 - 3 * δ) := by
  have hinv : MetricInverseInBasis (I := I) g x basis DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis horth
  have horth' :
      ∀ i j : Fin 3, g.inner x (basis i) (basis j) =
        DimensionThree.delta3 i j := horth
  rw [shiftScalar3At, shiftScalar3At]
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
    DimensionThree.delta3 hinv
      (A + c • metricTensorField (I := I) g x)]
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
    DimensionThree.delta3 hinv A]
  norm_num [Fin.sum_univ_three, DimensionThree.delta3, metricTensorField_apply,
    horth', vec2, RicciFlower.Curvature.vec2,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  ring

/-- Adding `c g` to a shifted tensor adds `c / (1 - 3 delta)` times the
metric to the reconstructed Ricci tensor. -/
theorem shiftRic_add_g
    {δ c : Real} {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (hδ : δ < (1 : Real) / 3)
    (A : Tensor02At (I := I) (M := M) x) :
    shiftRic3At (I := I) (M := M) δ g
        (A + c • metricTensorField (I := I) g x) =
      shiftRic3At (I := I) (M := M) δ g A +
        (c / (1 - 3 * δ)) • metricTensorField (I := I) g x := by
  have hden : 1 - 3 * δ ≠ 0 := by nlinarith
  have hden' : 1 - δ * 3 ≠ 0 := by nlinarith
  apply ContinuousMultilinearMap.ext
  intro slots
  simp [shiftRic3At, shiftScalar_add_g (I := I) (M := M) basis horth A,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  field_simp [hden, hden']
  ring_nf

/-- Reconstructing the scalar from `Ric - δ R g` recovers `R` in dimension
three, away from the singular value `δ = 1 / 3`. -/
theorem shiftScalar3At_pinch
    {δ : Real} {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (hδ : δ < (1 : Real) / 3)
    (Ric : Tensor02At (I := I) (M := M) x) :
    shiftScalar3At (I := I) (M := M) δ g
        (Ric - (δ * metricTracePair0SAt (I := I) g Ric) •
          metricTensorField (I := I) g x) =
      metricTracePair0SAt (I := I) g Ric := by
  let R : Real := metricTracePair0SAt (I := I) g Ric
  have hinv : MetricInverseInBasis (I := I) g x basis DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis horth
  have hR :
      R =
        Ric (vec2 (I := I) (basis 0) (basis 0)) +
          Ric (vec2 (I := I) (basis 1) (basis 1)) +
            Ric (vec2 (I := I) (basis 2) (basis 2)) := by
    dsimp [R]
    rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
      DimensionThree.delta3 hinv]
    norm_num [Fin.sum_univ_three, DimensionThree.delta3]
  have hden : 1 - 3 * δ ≠ 0 := by
    nlinarith
  have horth' :
      ∀ i j : Fin 3, g.inner x (basis i) (basis j) =
        DimensionThree.delta3 i j := horth
  rw [shiftScalar3At]
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
    DimensionThree.delta3 hinv]
  rw [show metricTracePair0SAt (I := I) g Ric = R by rfl]
  rw [hR]
  norm_num [Fin.sum_univ_three, DimensionThree.delta3, metricTensorField_apply,
    horth', vec2, RicciFlower.Curvature.vec2,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  field_simp [hden]

/-- Reconstructing Ricci from `Ric - δ R g` recovers the original Ricci tensor
in dimension three, away from the singular value `δ = 1 / 3`. -/
theorem shiftRic3At_pinch
    {δ : Real} {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (hδ : δ < (1 : Real) / 3)
    (Ric : Tensor02At (I := I) (M := M) x) :
    shiftRic3At (I := I) (M := M) δ g
        (Ric - (δ * metricTracePair0SAt (I := I) g Ric) •
          metricTensorField (I := I) g x) =
      Ric := by
  apply ContinuousMultilinearMap.ext
  intro slots
  rw [shiftRic3At, shiftScalar3At_pinch
    (I := I) (M := M) basis horth hδ Ric]
  simp

/-- The invariant shifted scalar agrees with the block scalar in an
orthonormal first-null block. -/
theorem shiftScalar3At_of_shiftBlock
    {δ : Real} {g : SmoothRiemannianMetric I M}
    {Araw : RawTwoTensorField (I := I) (M := M)} {x : M}
    {A : Tensor02At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {a b c : Real}
    (hreal : Tensor02RealizesRawAt (I := I) (M := M) Araw x A)
    (hblock : ShiftBlockAt (I := I) (M := M) g Araw x basis a b c) :
    shiftScalar3At (I := I) (M := M) δ g A = shiftScal3 δ a b := by
  have hinv : MetricInverseInBasis (I := I) g x basis DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis hblock.orthonormal
  rw [shiftScalar3At, shiftScal3,
    metricTracePair0SAt_eq_sum_basis (I := I) g basis DimensionThree.delta3 hinv A]
  norm_num [Fin.sum_univ_three, DimensionThree.delta3]
  rw [hreal (basis 0) (basis 0), hreal (basis 1) (basis 1),
    hreal (basis 2) (basis 2), hblock.components 0 0,
    hblock.components 1 1, hblock.components 2 2]
  simp [shiftBlockS3]

/-- The invariant Ricci reconstruction agrees with the finite block model in
an orthonormal first-null block. -/
theorem shiftRic3At_comp_of_shiftBlock
    {δ : Real} {g : SmoothRiemannianMetric I M}
    {Araw : RawTwoTensorField (I := I) (M := M)} {x : M}
    {A : Tensor02At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {a b c : Real}
    (hreal : Tensor02RealizesRawAt (I := I) (M := M) Araw x A)
    (hblock : ShiftBlockAt (I := I) (M := M) g Araw x basis a b c)
    (i j : Fin 3) :
    shiftRic3At (I := I) (M := M) δ g A
        (vec2 (I := I) (basis i) (basis j)) =
      shiftRicBlock3 δ a b c i j := by
  rw [shiftRic3At, shiftRicBlock3, shiftScalar3At_of_shiftBlock
    (I := I) (M := M) hreal hblock]
  have hmetric :
      metricTensorField (I := I) g x
          (vec2 (I := I) (basis i) (basis j)) =
        DimensionThree.delta3 i j := by
    simp [metricTensorField_apply, hblock.orthonormal i j,
      vec2, RicciFlower.Curvature.vec2]
  simp [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply,
    hreal (basis i) (basis j), hblock.components i j, hmetric, smul_eq_mul]

/-- Slot permutation sending a product `(0,2) ⊗ (0,2)` to
`A(0,2) * B(1,3)`. -/
def perm0213 : Equiv.Perm (Fin 4) where
  toFun := fun i =>
    if i = (0 : Fin 4) then 0
    else if i = (1 : Fin 4) then 2
    else if i = (2 : Fin 4) then 1
    else 3
  invFun := fun i =>
    if i = (0 : Fin 4) then 0
    else if i = (1 : Fin 4) then 2
    else if i = (2 : Fin 4) then 1
    else 3
  left_inv := by
    intro i
    fin_cases i <;> simp
  right_inv := by
    intro i
    fin_cases i <;> simp

/-- Slot permutation sending a product `(0,2) ⊗ (0,2)` to
`A(0,3) * B(1,2)`. -/
def perm0312 : Equiv.Perm (Fin 4) where
  toFun := fun i =>
    if i = (0 : Fin 4) then 0
    else if i = (1 : Fin 4) then 3
    else if i = (2 : Fin 4) then 1
    else 2
  invFun := fun i =>
    if i = (0 : Fin 4) then 0
    else if i = (1 : Fin 4) then 2
    else if i = (2 : Fin 4) then 3
    else 1
  left_inv := by
    intro i
    fin_cases i <;> simp
  right_inv := by
    intro i
    fin_cases i <;> simp

/-- Slot permutation sending a product `(0,2) ⊗ (0,2)` to
`A(1,2) * B(0,3)`. -/
def perm1203 : Equiv.Perm (Fin 4) where
  toFun := fun i =>
    if i = (0 : Fin 4) then 1
    else if i = (1 : Fin 4) then 2
    else if i = (2 : Fin 4) then 0
    else 3
  invFun := fun i =>
    if i = (0 : Fin 4) then 2
    else if i = (1 : Fin 4) then 0
    else if i = (2 : Fin 4) then 1
    else 3
  left_inv := by
    intro i
    fin_cases i <;> simp
  right_inv := by
    intro i
    fin_cases i <;> simp

/-- Slot permutation sending a product `(0,2) ⊗ (0,2)` to
`A(1,3) * B(0,2)`. -/
def perm1302 : Equiv.Perm (Fin 4) where
  toFun := fun i =>
    if i = (0 : Fin 4) then 1
    else if i = (1 : Fin 4) then 3
    else if i = (2 : Fin 4) then 0
    else 2
  invFun := fun i =>
    if i = (0 : Fin 4) then 2
    else if i = (1 : Fin 4) then 0
    else if i = (2 : Fin 4) then 3
    else 1
  left_inv := by
    intro i
    fin_cases i <;> simp
  right_inv := by
    intro i
    fin_cases i <;> simp

/-- Product of two two-tensors, with a final slot relabeling. -/
def tensor04Pair
    {x : M} (A B : Tensor02At (I := I) (M := M) x)
    (σ : Equiv.Perm (Fin 4)) :
    Tensor04At (I := I) (M := M) x :=
  (Bundle.continuousMultilinearMap.product_fun
    (𝕜 := Real) (F := E) (E := TangentSpace I) (s := 2) (q := 2) A B).domDomCongr σ

theorem tensor04Pair_apply
    {x : M} (A B : Tensor02At (I := I) (M := M) x)
    (σ : Equiv.Perm (Fin 4)) (slots : Fin 4 -> TangentSpace I x) :
    tensor04Pair (I := I) (M := M) A B σ slots =
      A (slots ∘ σ ∘ Fin.castAdd 2) *
        B (slots ∘ σ ∘ Fin.natAdd 2) := by
  rw [tensor04Pair]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [Bundle.continuousMultilinearMap.product_fun_apply]
  rfl

@[simp]
theorem tensor04Pair_perm0213_vec4
    {x : M} (A B : Tensor02At (I := I) (M := M) x)
    (W X Y Z : TangentSpace I x) :
    tensor04Pair (I := I) (M := M) A B perm0213 (vec4 (I := I) W X Y Z) =
      A (vec2 (I := I) W Y) * B (vec2 (I := I) X Z) := by
  rw [tensor04Pair_apply]
  congr <;> funext q <;> fin_cases q <;>
    simp [perm0213, vec2, vec4, RicciFlower.Curvature.vec2,
      RicciFlower.Curvature.vec4, Function.comp_def]

@[simp]
theorem tensor04Pair_perm0312_vec4
    {x : M} (A B : Tensor02At (I := I) (M := M) x)
    (W X Y Z : TangentSpace I x) :
    tensor04Pair (I := I) (M := M) A B perm0312 (vec4 (I := I) W X Y Z) =
      A (vec2 (I := I) W Z) * B (vec2 (I := I) X Y) := by
  rw [tensor04Pair_apply]
  congr <;> funext q <;> fin_cases q <;>
    simp [perm0312, vec2, vec4, RicciFlower.Curvature.vec2,
      RicciFlower.Curvature.vec4, Function.comp_def]

@[simp]
theorem tensor04Pair_perm1203_vec4
    {x : M} (A B : Tensor02At (I := I) (M := M) x)
    (W X Y Z : TangentSpace I x) :
    tensor04Pair (I := I) (M := M) A B perm1203 (vec4 (I := I) W X Y Z) =
      A (vec2 (I := I) X Y) * B (vec2 (I := I) W Z) := by
  rw [tensor04Pair_apply]
  congr <;> funext q <;> fin_cases q <;>
    simp [perm1203, vec2, vec4, RicciFlower.Curvature.vec2,
      RicciFlower.Curvature.vec4, Function.comp_def]

@[simp]
theorem tensor04Pair_perm1302_vec4
    {x : M} (A B : Tensor02At (I := I) (M := M) x)
    (W X Y Z : TangentSpace I x) :
    tensor04Pair (I := I) (M := M) A B perm1302 (vec4 (I := I) W X Y Z) =
      A (vec2 (I := I) X Z) * B (vec2 (I := I) W Y) := by
  rw [tensor04Pair_apply]
  congr <;> funext q <;> fin_cases q <;>
    simp [perm1302, vec2, vec4, RicciFlower.Curvature.vec2,
      RicciFlower.Curvature.vec4, Function.comp_def]

/-- Invariant three-dimensional Riemann-from-Ricci builder in the slot order
used by the shifted pinching reaction algebra. -/
def rm04OfRic3At
    (g : SmoothRiemannianMetric I M) {x : M}
    (Ric : Tensor02At (I := I) (M := M) x) :
    Tensor04At (I := I) (M := M) x :=
  let G := metricTensorField (I := I) g x
  let R := metricTracePair0SAt (I := I) g Ric
  tensor04Pair (I := I) (M := M) G Ric perm0213 -
    tensor04Pair (I := I) (M := M) G Ric perm0312 -
    tensor04Pair (I := I) (M := M) G Ric perm1203 +
    tensor04Pair (I := I) (M := M) G Ric perm1302 -
    ((1 / 2 : Real) * R) •
      (tensor04Pair (I := I) (M := M) G G perm0213 -
        tensor04Pair (I := I) (M := M) G G perm0312)

/-- In an orthonormal `Fin 3` basis, `rm04OfRic3At` has the checked finite
Riemann-from-Ricci component model.  This audits the slot convention used by
the shifted reaction algebra. -/
theorem rm04OfRic3At_comp_orthonormal
    {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (Ric : Tensor02At (I := I) (M := M) x)
    (i j k l : Fin 3) :
    rm04OfRic3At (I := I) (M := M) g Ric
        (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)) =
      stdRmOfRic3 (fun a b : Fin 3 => Ric (vec2 (I := I) (basis a) (basis b)))
        i j k l := by
  have hinv : MetricInverseInBasis (I := I) g x basis DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis horth
  have htrace :
      metricTracePair0SAt (I := I) g Ric =
        ricciScal3
          (fun a b : Fin 3 => Ric (vec2 (I := I) (basis a) (basis b))) := by
    rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
      DimensionThree.delta3 hinv Ric]
    norm_num [Fin.sum_univ_three, DimensionThree.delta3, ricciScal3]
  have horth' :
      ∀ a b : Fin 3, g.inner x (basis a) (basis b) =
        DimensionThree.delta3 a b := horth
  simp [rm04OfRic3At, stdRmOfRic3, htrace, metricTensorField_apply, horth',
    vec2, vec4, RicciFlower.Curvature.vec2,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]

/-! ## Canonical shifted reaction tensor -/

/-- Continuous-linear version of the Ricci endomorphism obtained by raising
the first slot of a `(0,2)` tensor. -/
def ricciEndCLMAt
    (g : SmoothRiemannianMetric I M) {x : M}
    (Ric : Tensor02At (I := I) (M := M) x) :
    TangentSpace I x →L[Real] TangentSpace I x :=
  ⟨DimensionThree.ricciEndAt (I := I) g Ric,
    LinearMap.continuous_of_finiteDimensional _⟩

@[simp]
theorem ricciEndCLMAt_apply
    (g : SmoothRiemannianMetric I M) {x : M}
    (Ric : Tensor02At (I := I) (M := M) x)
    (X : TangentSpace I x) :
    ricciEndCLMAt (I := I) (M := M) g Ric X =
      DimensionThree.ricciEndAt (I := I) g Ric X := by
  rfl

/-- The quadratic contraction `Ric_i^k Ric_kj`, defined invariantly by the
Ricci endomorphism. -/
def ricciQuadAt
    (g : SmoothRiemannianMetric I M) {x : M}
    (Ric : Tensor02At (I := I) (M := M) x) :
    Tensor02At (I := I) (M := M) x :=
  Ric.compContinuousLinearMap
    (fun i : Fin 2 =>
      if i = 0 then
        ricciEndCLMAt (I := I) (M := M) g Ric
      else
        ContinuousLinearMap.id Real (TangentSpace I x))

@[simp]
theorem ricciQuadAt_apply
    (g : SmoothRiemannianMetric I M) {x : M}
    (Ric : Tensor02At (I := I) (M := M) x)
    (X Y : TangentSpace I x) :
    ricciQuadAt (I := I) (M := M) g Ric
        (vec2 (I := I) X Y) =
      Ric (vec2 (I := I)
        (DimensionThree.ricciEndAt (I := I) g Ric X) Y) := by
  unfold ricciQuadAt
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> simp [vec2, RicciFlower.Curvature.vec2]

/-- Freeze a lowered four-tensor to the two slots contracted against Ricci in
`R_ikjl Ric^kl`. -/
def rm04Mid02At
    {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (X Y : TangentSpace I x) :
    Tensor02At (I := I) (M := M) x :=
  (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 3 x
      (Rm04.domDomCongr perm0213)) X)) Y

@[simp]
theorem rm04Mid02At_apply
    {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (X Y K L : TangentSpace I x) :
    rm04Mid02At (I := I) (M := M) Rm04 X Y
        (vec2 (I := I) K L) =
      Rm04 (vec4 (I := I) X K Y L) := by
  unfold rm04Mid02At
  rw [Realized.metricTrace_tensor0S_curry_apply_cons]
  rw [Realized.metricTrace_tensor0S_curry_apply_cons]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Curried continuous-linear form of `rm04Mid02At`. -/
def rm04MidCLMAt
    {x : M} (Rm04 : Tensor04At (I := I) (M := M) x) :
    TangentSpace I x →L[Real]
      TangentSpace I x →L[Real]
        Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x).toContinuousLinearMap).comp
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 3 x)
      (Rm04.domDomCongr perm0213))

@[simp]
theorem rm04MidCLMAt_apply
    {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (X Y : TangentSpace I x) :
    rm04MidCLMAt (I := I) (M := M) Rm04 X Y =
      rm04Mid02At (I := I) (M := M) Rm04 X Y := by
  unfold rm04MidCLMAt rm04Mid02At
  rfl

/-- Continuous-linear functional `B ↦ <A, B>_g` on `(0,2)` tensors. -/
def inner02RightCLM
    (g : SmoothRiemannianMetric I M) {x : M}
    (A : Tensor02At (I := I) (M := M) x) :
    Tensor02At (I := I) (M := M) x →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    ((flat0S (I := I) g x 2) A)

@[simp]
theorem inner02RightCLM_apply
    (g : SmoothRiemannianMetric I M) {x : M}
    (A B : Tensor02At (I := I) (M := M) x) :
    inner02RightCLM (I := I) (M := M) g A B =
      inner0S (I := I) g x 2 A B := by
  rfl

/-- Right-slot linear form for the curvature-Ricci contraction after freezing
the first slot. -/
def rm04ContrRightCLM
    (g : SmoothRiemannianMetric I M) {x : M}
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (Ric : Tensor02At (I := I) (M := M) x)
    (X : TangentSpace I x) :
    TangentSpace I x →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Y =>
        inner02RightCLM (I := I) (M := M) g Ric
          (rm04Mid02At (I := I) (M := M) Rm04 X Y)
      map_add' := by
        intro Y Z
        rw [← rm04MidCLMAt_apply (I := I) (M := M) Rm04 X (Y + Z),
          ← rm04MidCLMAt_apply (I := I) (M := M) Rm04 X Y,
          ← rm04MidCLMAt_apply (I := I) (M := M) Rm04 X Z]
        rw [map_add]
        change
          inner02RightCLM (I := I) (M := M) g Ric
              (rm04Mid02At (I := I) (M := M) Rm04 X Y +
                rm04Mid02At (I := I) (M := M) Rm04 X Z) =
            inner02RightCLM (I := I) (M := M) g Ric
                (rm04Mid02At (I := I) (M := M) Rm04 X Y) +
              inner02RightCLM (I := I) (M := M) g Ric
                (rm04Mid02At (I := I) (M := M) Rm04 X Z)
        rw [map_add]
      map_smul' := by
        intro c Y
        rw [← rm04MidCLMAt_apply (I := I) (M := M) Rm04 X (c • Y),
          ← rm04MidCLMAt_apply (I := I) (M := M) Rm04 X Y]
        rw [map_smul]
        change
          inner02RightCLM (I := I) (M := M) g Ric
              (c • rm04Mid02At (I := I) (M := M) Rm04 X Y) =
            c • inner02RightCLM (I := I) (M := M) g Ric
              (rm04Mid02At (I := I) (M := M) Rm04 X Y)
        rw [map_smul] }

@[simp]
theorem rm04ContrRightCLM_apply
    (g : SmoothRiemannianMetric I M) {x : M}
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (Ric : Tensor02At (I := I) (M := M) x)
    (X Y : TangentSpace I x) :
    rm04ContrRightCLM (I := I) (M := M) g Rm04 Ric X Y =
      inner0S (I := I) g x 2 Ric
        (rm04Mid02At (I := I) (M := M) Rm04 X Y) := by
  rfl

/-- Curried scalar map for the invariant curvature-Ricci contraction. -/
def rm04ContrCurried
    (g : SmoothRiemannianMetric I M) {x : M}
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (Ric : Tensor02At (I := I) (M := M) x) :
    TangentSpace I x →L[Real]
      ContinuousMultilinearMap Real (fun _ : Fin 1 => TangentSpace I x) Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X =>
        (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
          (rm04ContrRightCLM (I := I) (M := M) g Rm04 Ric X)
      map_add' := by
        intro X Y
        apply ContinuousMultilinearMap.ext
        intro m
        change
          rm04ContrRightCLM (I := I) (M := M) g Rm04 Ric (X + Y) (m 0) =
            rm04ContrRightCLM (I := I) (M := M) g Rm04 Ric X (m 0) +
              rm04ContrRightCLM (I := I) (M := M) g Rm04 Ric Y (m 0)
        rw [rm04ContrRightCLM_apply, rm04ContrRightCLM_apply,
          rm04ContrRightCLM_apply]
        rw [← rm04MidCLMAt_apply (I := I) (M := M) Rm04 (X + Y) (m 0),
          ← rm04MidCLMAt_apply (I := I) (M := M) Rm04 X (m 0),
          ← rm04MidCLMAt_apply (I := I) (M := M) Rm04 Y (m 0)]
        rw [map_add]
        change
          inner02RightCLM (I := I) (M := M) g Ric
              (rm04Mid02At (I := I) (M := M) Rm04 X (m 0) +
                rm04Mid02At (I := I) (M := M) Rm04 Y (m 0)) =
            inner02RightCLM (I := I) (M := M) g Ric
                (rm04Mid02At (I := I) (M := M) Rm04 X (m 0)) +
              inner02RightCLM (I := I) (M := M) g Ric
                (rm04Mid02At (I := I) (M := M) Rm04 Y (m 0))
        rw [map_add]
      map_smul' := by
        intro c X
        apply ContinuousMultilinearMap.ext
        intro m
        change
          rm04ContrRightCLM (I := I) (M := M) g Rm04 Ric (c • X) (m 0) =
            c • rm04ContrRightCLM (I := I) (M := M) g Rm04 Ric X (m 0)
        rw [rm04ContrRightCLM_apply, rm04ContrRightCLM_apply]
        rw [← rm04MidCLMAt_apply (I := I) (M := M) Rm04 (c • X) (m 0),
          ← rm04MidCLMAt_apply (I := I) (M := M) Rm04 X (m 0)]
        rw [map_smul]
        change
          inner02RightCLM (I := I) (M := M) g Ric
              (c • rm04Mid02At (I := I) (M := M) Rm04 X (m 0)) =
            c • inner02RightCLM (I := I) (M := M) g Ric
              (rm04Mid02At (I := I) (M := M) Rm04 X (m 0))
        rw [map_smul] }

/-- The invariant curvature-Ricci contraction `R_ikjl Ric^kl`. -/
def rm04RicciContrAt
    (g : SmoothRiemannianMetric I M) {x : M}
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (Ric : Tensor02At (I := I) (M := M) x) :
    Tensor02At (I := I) (M := M) x :=
  ContinuousLinearMap.uncurryLeft
    (𝕜 := Real) (n := 1) (Ei := fun _ : Fin 2 => TangentSpace I x) (G := Real)
    (rm04ContrCurried (I := I) (M := M) g Rm04 Ric)

@[simp]
theorem rm04RicciContrAt_apply
    (g : SmoothRiemannianMetric I M) {x : M}
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (Ric : Tensor02At (I := I) (M := M) x)
    (X Y : TangentSpace I x) :
    rm04RicciContrAt (I := I) (M := M) g Rm04 Ric
        (vec2 (I := I) X Y) =
      inner0S (I := I) g x 2 Ric
        (rm04Mid02At (I := I) (M := M) Rm04 X Y) := by
  unfold rm04RicciContrAt
  rw [ContinuousLinearMap.uncurryLeft_apply]
  change
    (rm04ContrCurried (I := I) (M := M) g Rm04 Ric X)
        (Fin.tail (vec2 (I := I) X Y)) =
      inner0S (I := I) g x 2 Ric
        (rm04Mid02At (I := I) (M := M) Rm04 X Y)
  have htail :
      Fin.tail (vec2 (I := I) X Y) = fun _ : Fin 1 => Y := by
    funext i
    fin_cases i
    rfl
  rw [htail]
  change
    rm04ContrRightCLM (I := I) (M := M) g Rm04 Ric X Y =
      inner0S (I := I) g x 2 Ric
        (rm04Mid02At (I := I) (M := M) Rm04 X Y)
  rfl

/-- Ricci-flow Ricci reaction tensor
`2 R_ikjl Ric^kl - 2 Ric_i^k Ric_kj`, defined invariantly. -/
def ricciReaction3At
    (g : SmoothRiemannianMetric I M) {x : M}
    (Ric : Tensor02At (I := I) (M := M) x) :
    Tensor02At (I := I) (M := M) x :=
  2 • rm04RicciContrAt (I := I) (M := M) g
      (rm04OfRic3At (I := I) (M := M) g Ric) Ric -
    2 • ricciQuadAt (I := I) (M := M) g Ric

/-- Canonical shifted reaction core for `S = Ric - delta R g` in dimension
three. -/
def shiftNAt (delta : Real) : Tensor02ReactionAt (I := I) (M := M) :=
  fun _t g x A =>
    let Ric := shiftRic3At (I := I) (M := M) delta g A
    let R := metricTracePair0SAt (I := I) g Ric
    let RicNormSq := inner0S (I := I) g x 2 Ric Ric
    ricciReaction3At (I := I) (M := M) g Ric -
      (2 * delta) •
        (RicNormSq • metricTensorField (I := I) g x - R • Ric)

/-- Raw WMP adapter for the canonical shifted reaction. -/
def shiftNRaw (delta : Real) : TwoTensorReaction (I := I) (M := M) :=
  Tensor02ReactionAt.toRawSymm (I := I) (M := M)
    (shiftNAt (I := I) (M := M) delta)

theorem shiftNRaw_symmInputOn
    (G : Real -> SmoothRiemannianMetric I M) (U : Set Real) (delta : Real) :
    TensorReactionSymmInputOn (I := I) (M := M) G
      (shiftNRaw (I := I) (M := M) delta) U :=
  Tensor02ReactionAt.toRawSymm_symmInputOn (I := I) (M := M) G
    (shiftNAt (I := I) (M := M) delta) U

/-- On an honest shifted pinching tensor `Ric - δ R g`, the canonical shifted
reaction is the Ricci reaction minus the scalar-metric correction term. -/
theorem shiftNAt_pinch
    {δ t : Real} {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (hδ : δ < (1 : Real) / 3)
    (Ric : Tensor02At (I := I) (M := M) x) :
    shiftNAt (I := I) (M := M) δ t g x
        (Ric - (δ * metricTracePair0SAt (I := I) g Ric) •
          metricTensorField (I := I) g x) =
      ricciReaction3At (I := I) (M := M) g Ric -
        (2 * δ) •
          (inner0S (I := I) g x 2 Ric Ric •
              metricTensorField (I := I) g x -
            metricTracePair0SAt (I := I) g Ric • Ric) := by
  rw [shiftNAt, shiftRic3At_pinch (I := I) (M := M) basis horth hδ Ric]

theorem finCons1_eq_vec2
    {x : M} (X Y : TangentSpace I x) :
    Fin.cons X (fun _ : Fin 1 => Y) = vec2 (I := I) X Y := by
  funext q
  fin_cases q <;> rfl

theorem fin2_const_eq_vec2
    {x : M} (X : TangentSpace I x) :
    (fun _ : Fin 2 => X) = vec2 (I := I) X X := by
  funext q
  fin_cases q <;> rfl

theorem fin2_if_eq_vec2
    {x : M} (X Y : TangentSpace I x) :
    (fun q : Fin 2 => if q = 0 then X else Y) = vec2 (I := I) X Y := by
  funext q
  fin_cases q <;> rfl

theorem ricciEnd_repr_orthonormal
    {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (Ric : Tensor02At (I := I) (M := M) x)
    (i k : Fin 3) :
    basis.repr (DimensionThree.ricciEndAt (I := I) g Ric (basis i)) k =
      Ric (vec2 (I := I) (basis i) (basis k)) := by
  have hinv : MetricInverseInBasis (I := I) g x basis DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis horth
  rw [basis_repr_eq_sum_inv_inner (I := I) g x basis DimensionThree.delta3
    hinv]
  fin_cases k <;>
    simp [DimensionThree.delta3, DimensionThree.ricciEnd_inner]

theorem ricciQuadAt_comp_orthonormal
    {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (Ric : Tensor02At (I := I) (M := M) x)
    (i j : Fin 3) :
    ricciQuadAt (I := I) (M := M) g Ric
        (vec2 (I := I) (basis i) (basis j)) =
      ricciSq3 (fun a b : Fin 3 =>
        Ric (vec2 (I := I) (basis a) (basis b))) i j := by
  rw [ricciQuadAt_apply]
  have hEnd :
      DimensionThree.ricciEndAt (I := I) g Ric (basis i) =
        ∑ k : Fin 3,
          basis.repr (DimensionThree.ricciEndAt (I := I) g Ric (basis i)) k •
            basis k := by
    exact (basis.sum_repr
      (DimensionThree.ricciEndAt (I := I) g Ric (basis i))).symm
  rw [hEnd]
  rw [show
      vec2 (I := I)
          (∑ k : Fin 3,
            basis.repr (DimensionThree.ricciEndAt (I := I) g Ric (basis i)) k •
              basis k)
          (basis j) =
        Fin.cons
          (∑ k : Fin 3,
            basis.repr (DimensionThree.ricciEndAt (I := I) g Ric (basis i)) k •
              basis k)
          (fun _ : Fin 1 => basis j) by
    funext q
    fin_cases q <;> rfl]
  rw [← Realized.metricTrace_tensor0S_curry_apply_cons
    (I := I) (M := M) (s := 1) Ric
      (∑ k : Fin 3,
        basis.repr (DimensionThree.ricciEndAt (I := I) g Ric (basis i)) k •
          basis k)
      (fun _ : Fin 1 => basis j)]
  change
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x Ric)
        (∑ k : Fin 3,
          basis.repr (DimensionThree.ricciEndAt (I := I) g Ric (basis i)) k •
            basis k))
        (fun _ : Fin 1 => basis j) =
      ricciSq3
        (fun a b : Fin 3 => Ric (vec2 (I := I) (basis a) (basis b))) i j
  rw [map_sum]
  simp [Realized.metricTrace_tensor0S_curry_apply_cons, finCons1_eq_vec2,
    smul_eq_mul]
  simp [ricciEnd_repr_orthonormal (I := I) (M := M) basis horth Ric,
    ricciSq3]

theorem ricciNorm3_comp_orthonormal
    {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (Ric : Tensor02At (I := I) (M := M) x) :
    inner0S (I := I) g x 2 Ric Ric =
      ricciNorm3 (fun a b : Fin 3 =>
        Ric (vec2 (I := I) (basis a) (basis b))) := by
  have hinv : MetricInverseInBasis (I := I) g x basis DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis horth
  rw [inner0S_two_eq_coord (I := I) g x basis DimensionThree.delta3 hinv]
  norm_num [Fin.sum_univ_three, DimensionThree.delta3, ricciNorm3,
    vec2, RicciFlower.Curvature.vec2]
  simp [fin2_const_eq_vec2, fin2_if_eq_vec2]

theorem metricTrace_comp_orthonormal
    {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (Ric : Tensor02At (I := I) (M := M) x) :
    metricTracePair0SAt (I := I) g Ric =
      ricciScal3 (fun a b : Fin 3 =>
        Ric (vec2 (I := I) (basis a) (basis b))) := by
  have hinv : MetricInverseInBasis (I := I) g x basis DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis horth
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
    DimensionThree.delta3 hinv Ric]
  norm_num [Fin.sum_univ_three, DimensionThree.delta3, ricciScal3]

theorem rm04Contr_comp_orthonormal
    {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (Ric : Tensor02At (I := I) (M := M) x)
    (i j : Fin 3) :
    rm04RicciContrAt (I := I) (M := M) g Rm04 Ric
        (vec2 (I := I) (basis i) (basis j)) =
      ∑ k : Fin 3, ∑ l : Fin 3,
        Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          Ric (vec2 (I := I) (basis k) (basis l)) := by
  have hinv : MetricInverseInBasis (I := I) g x basis DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis horth
  rw [rm04RicciContrAt_apply]
  rw [inner0S_two_eq_coord (I := I) g x basis DimensionThree.delta3 hinv]
  norm_num [Fin.sum_univ_three, DimensionThree.delta3, rm04Mid02At_apply,
    vec2, vec4, RicciFlower.Curvature.vec2, RicciFlower.Curvature.vec4]
  simp [fin2_const_eq_vec2, fin2_if_eq_vec2, rm04Mid02At_apply]
  ring_nf

theorem ricciReaction3At_comp_orthonormal
    {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (Ric : Tensor02At (I := I) (M := M) x)
    (i j : Fin 3) :
    ricciReaction3At (I := I) (M := M) g Ric
        (vec2 (I := I) (basis i) (basis j)) =
      ricciPresReact
        (fun a b c d : Fin 3 =>
          rm04OfRic3At (I := I) (M := M) g Ric
            (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
        (fun a b : Fin 3 =>
          Ric (vec2 (I := I) (basis a) (basis b))) i j := by
  simp [ricciReaction3At, ricciPresReact,
    rm04Contr_comp_orthonormal (I := I) (M := M) basis horth,
    ricciQuadAt_comp_orthonormal (I := I) (M := M) basis horth]

theorem shiftNAt_comp_orthonormal
    {delta t : Real} {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (A : Tensor02At (I := I) (M := M) x)
    (i j : Fin 3) :
    shiftNAt (I := I) (M := M) delta t g x A
        (vec2 (I := I) (basis i) (basis j)) =
      pinchReact delta
        (fun a b c d : Fin 3 =>
          rm04OfRic3At (I := I) (M := M) g
              (shiftRic3At (I := I) (M := M) delta g A)
            (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
        (fun a b : Fin 3 =>
          shiftRic3At (I := I) (M := M) delta g A
            (vec2 (I := I) (basis a) (basis b))) i j := by
  have hmetric :
      metricTensorField (I := I) g x
          (vec2 (I := I) (basis i) (basis j)) =
        DimensionThree.delta3 i j := by
    simp [metricTensorField_apply, horth i j,
      vec2, RicciFlower.Curvature.vec2]
  simp [shiftNAt, pinchReact,
    ricciReaction3At_comp_orthonormal (I := I) (M := M) basis horth,
    ricciNorm3_comp_orthonormal (I := I) (M := M) basis horth,
    metricTrace_comp_orthonormal (I := I) (M := M) basis horth,
    hmetric, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]

/-- Component form of the metric-shift linearity of the canonical shifted
reaction.  In dimension three the `c^2` terms cancel. -/
theorem shiftNAt_add_g_comp
    {delta c t : Real} {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (hdelta : delta < (1 : Real) / 3)
    (A : Tensor02At (I := I) (M := M) x) :
    shiftNAt (I := I) (M := M) delta t g x
        (A + c • metricTensorField (I := I) g x)
        (vec2 (I := I) (basis 0) (basis 0)) -
      shiftNAt (I := I) (M := M) delta t g x A
        (vec2 (I := I) (basis 0) (basis 0)) =
        (c / (1 - 3 * delta)) * (2 * delta - 1) *
          (3 *
              shiftRic3At (I := I) (M := M) delta g A
                (vec2 (I := I) (basis 0) (basis 0)) -
            metricTracePair0SAt (I := I) g
                (shiftRic3At (I := I) (M := M) delta g A)) := by
  let Ric : Fin 3 -> Fin 3 -> Real := fun p q =>
    shiftRic3At (I := I) (M := M) delta g A
      (vec2 (I := I) (basis p) (basis q))
  let a : Real := c / (1 - 3 * delta)
  have hRicAdd : ∀ p q : Fin 3,
      shiftRic3At (I := I) (M := M) delta g
          (A + c • metricTensorField (I := I) g x)
          (vec2 (I := I) (basis p) (basis q)) =
        Ric p q + a * DimensionThree.delta3 p q := by
    intro p q
    rw [shiftRic_add_g (I := I) (M := M) basis horth hdelta A]
    simp [Ric, a, metricTensorField_apply, horth p q,
      vec2, RicciFlower.Curvature.vec2, smul_eq_mul]
  have hRmAdd : ∀ p q r s : Fin 3,
      rm04OfRic3At (I := I) (M := M) g
          (shiftRic3At (I := I) (M := M) delta g
            (A + c • metricTensorField (I := I) g x))
          (vec4 (I := I) (basis p) (basis q) (basis r) (basis s)) =
        stdRmOfRic3
          (fun u v : Fin 3 => Ric u v + a * DimensionThree.delta3 u v)
          p q r s := by
    intro p q r s
    rw [rm04OfRic3At_comp_orthonormal (I := I) (M := M) basis horth]
    simp [hRicAdd]
  have hRm : ∀ p q r s : Fin 3,
      rm04OfRic3At (I := I) (M := M) g
          (shiftRic3At (I := I) (M := M) delta g A)
          (vec4 (I := I) (basis p) (basis q) (basis r) (basis s)) =
        stdRmOfRic3 Ric p q r s := by
    intro p q r s
    rw [rm04OfRic3At_comp_orthonormal (I := I) (M := M) basis horth]
  have htrace :
      metricTracePair0SAt (I := I) g
          (shiftRic3At (I := I) (M := M) delta g A) =
        ricciScal3 Ric := by
    rw [metricTrace_comp_orthonormal (I := I) (M := M) basis horth]
  rw [shiftNAt_comp_orthonormal (I := I) (M := M) basis horth
      (A + c • metricTensorField (I := I) g x) 0 0,
    shiftNAt_comp_orthonormal (I := I) (M := M) basis horth A 0 0]
  simp [hRicAdd, hRmAdd, hRm, htrace, Ric, a,
    pinchReact_add_g00]

/-- Quadratic evaluation form of the metric-shift linearity of the canonical
shifted reaction. -/
theorem shiftNAt_add_g_quad
    {delta c t : Real} {g : SmoothRiemannianMetric I M} {x : M}
    (hdelta : delta < (1 : Real) / 3)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (A : Tensor02At (I := I) (M := M) x) (v : TangentSpace I x) :
    shiftNAt (I := I) (M := M) delta t g x
        (A + c • metricTensorField (I := I) g x)
        (vec2 (I := I) v v) -
      shiftNAt (I := I) (M := M) delta t g x A
        (vec2 (I := I) v v) =
        (c / (1 - 3 * delta)) * (2 * delta - 1) *
          ((3 : Real) • shiftRic3At (I := I) (M := M) delta g A -
              metricTracePair0SAt (I := I) g
                  (shiftRic3At (I := I) (M := M) delta g A) •
                metricTensorField (I := I) g x)
            (vec2 (I := I) v v) := by
  have tensor_zero
      (T : Tensor02At (I := I) (M := M) x) :
      T (vec2 (I := I) (0 : TangentSpace I x) 0) = 0 := by
    have h := tensor02_smul2 (I := I) (M := M) T
      (0 : Real) (0 : TangentSpace I x)
    simpa [quad02, vec2_self_eq_const] using h
  by_cases hv : v = 0
  · subst v
    simp [tensor_zero]
  · obtain ⟨nb⟩ :=
      exists_nullOrthonormalBasis3At (I := I) (M := M) g
        (x := x) (v := v) hdim hv
    rcases nb.scale with ⟨r, _hr, hscale⟩
    let C : Tensor02At (I := I) (M := M) x :=
      (3 : Real) • shiftRic3At (I := I) (M := M) delta g A -
        metricTracePair0SAt (I := I) g
            (shiftRic3At (I := I) (M := M) delta g A) •
          metricTensorField (I := I) g x
    have hplus :
        shiftNAt (I := I) (M := M) delta t g x
            (A + c • metricTensorField (I := I) g x)
            (vec2 (I := I) v v) =
          r ^ 2 *
            shiftNAt (I := I) (M := M) delta t g x
              (A + c • metricTensorField (I := I) g x)
              (vec2 (I := I) (nb.basis 0) (nb.basis 0)) := by
      simpa [hscale, quad02, vec2_self_eq_const, pow_two] using
        tensor02_smul2 (I := I) (M := M)
        (shiftNAt (I := I) (M := M) delta t g x
          (A + c • metricTensorField (I := I) g x))
        r (nb.basis 0)
    have hbase :
        shiftNAt (I := I) (M := M) delta t g x A
            (vec2 (I := I) v v) =
          r ^ 2 *
            shiftNAt (I := I) (M := M) delta t g x A
              (vec2 (I := I) (nb.basis 0) (nb.basis 0)) := by
      simpa [hscale, quad02, vec2_self_eq_const, pow_two] using
        tensor02_smul2 (I := I) (M := M)
        (shiftNAt (I := I) (M := M) delta t g x A)
        r (nb.basis 0)
    have hC :
        C (vec2 (I := I) v v) =
          r ^ 2 * C (vec2 (I := I) (nb.basis 0) (nb.basis 0)) := by
      simpa [hscale, quad02, vec2_self_eq_const, pow_two] using
        tensor02_smul2 (I := I) (M := M) C r (nb.basis 0)
    have hcomp :=
      shiftNAt_add_g_comp (I := I) (M := M)
        (delta := delta) (c := c) (t := t)
        nb.basis nb.orthonormal
        hdelta A
    have hmetric00 :
        metricTensorField (I := I) g x
            (vec2 (I := I) (nb.basis 0) (nb.basis 0)) = 1 := by
      simpa [metricTensorField_apply, vec2, RicciFlower.Curvature.vec2,
        DimensionThree.delta3] using nb.orthonormal 0 0
    have hC0 :
        C (vec2 (I := I) (nb.basis 0) (nb.basis 0)) =
          3 *
              shiftRic3At (I := I) (M := M) delta g A
                (vec2 (I := I) (nb.basis 0) (nb.basis 0)) -
            metricTracePair0SAt (I := I) g
              (shiftRic3At (I := I) (M := M) delta g A) := by
      simp [C, hmetric00, smul_eq_mul]
    rw [hplus, hbase, hC, hC0]
    let P : Real :=
      shiftNAt (I := I) (M := M) delta t g x
        (A + c • metricTensorField (I := I) g x)
        (vec2 (I := I) (nb.basis 0) (nb.basis 0))
    let B : Real :=
      shiftNAt (I := I) (M := M) delta t g x A
        (vec2 (I := I) (nb.basis 0) (nb.basis 0))
    let Q : Real :=
      3 *
          shiftRic3At (I := I) (M := M) delta g A
            (vec2 (I := I) (nb.basis 0) (nb.basis 0)) -
        metricTracePair0SAt (I := I) g
          (shiftRic3At (I := I) (M := M) delta g A)
    let k : Real := (c / (1 - 3 * delta)) * (2 * delta - 1)
    change r ^ 2 * P - r ^ 2 * B = k * (r ^ 2 * Q)
    have hcomp' : P - B = k * Q := by
      simpa [P, B, Q, k] using hcomp
    calc
      r ^ 2 * P - r ^ 2 * B = r ^ 2 * (P - B) := by ring
      _ = r ^ 2 * (k * Q) := by rw [hcomp']
      _ = k * (r ^ 2 * Q) := by ring

/-- The canonical shifted reaction realizes the checked first-null block target
in any supplied orthonormal first-null block. -/
theorem shiftNAt_comp_shiftBlock
    {delta t : Real} {g : SmoothRiemannianMetric I M}
    {Araw : RawTwoTensorField (I := I) (M := M)} {x : M}
    {A : Tensor02At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {a b c : Real}
    (hreal : Tensor02RealizesRawAt (I := I) (M := M) Araw x A)
    (hblock : ShiftBlockAt (I := I) (M := M) g Araw x basis a b c) :
    shiftNAt (I := I) (M := M) delta t g x A
        (vec2 (I := I) (basis 0) (basis 0)) =
      shiftReactBlock3 delta a b c := by
  have hRic :
      ∀ i j : Fin 3,
        shiftRic3At (I := I) (M := M) delta g A
            (vec2 (I := I) (basis i) (basis j)) =
          shiftRicBlock3 delta a b c i j :=
    shiftRic3At_comp_of_shiftBlock (I := I) (M := M) hreal hblock
  have hRm :
      ∀ i j k l : Fin 3,
        rm04OfRic3At (I := I) (M := M) g
            (shiftRic3At (I := I) (M := M) delta g A)
            (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)) =
          stdRmOfRic3 (shiftRicBlock3 delta a b c) i j k l := by
    intro i j k l
    rw [rm04OfRic3At_comp_orthonormal (I := I) (M := M) basis hblock.orthonormal]
    simp [hRic]
  rw [shiftNAt_comp_orthonormal (I := I) (M := M) basis
    hblock.orthonormal A 0 0]
  simp [shiftReactBlock3, hRic, hRm]

/-- The raw symmetric adapter for the canonical shifted reaction realizes the
first-null block target whenever the supplied raw tensor has that block shape.
This is still a basis-level realization theorem, not the full WMP null
condition. -/
theorem shiftNRaw_realizes_block
    {delta t : Real} {g : SmoothRiemannianMetric I M}
    {Araw : RawTwoTensorField (I := I) (M := M)} {x : M}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {a b c : Real}
    (hsym : TwoTensorSymmetricAt (I := I) (M := M) Araw x)
    (hbilin : TwoTensorBilinearAt (I := I) (M := M) Araw x)
    (hblock : ShiftBlockAt (I := I) (M := M) g Araw x basis a b c) :
    (shiftNRaw (I := I) (M := M) delta t g Araw) x (basis 0) (basis 0) =
      shiftReactBlock3 delta a b c := by
  rw [shiftNRaw, Tensor02ReactionAt.toRawSymm_eval_of_bilin
    (I := I) (M := M) (shiftNAt (I := I) (M := M) delta) t g Araw x hbilin]
  let T : Tensor02At (I := I) (M := M) x :=
    tensor02OfRawAt (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Araw) x
      (rawSym2_bilin (I := I) (M := M) hbilin)
  have hreal : Tensor02RealizesRawAt (I := I) (M := M) Araw x T := by
    intro v w
    change
      tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Araw) x
          (rawSym2_bilin (I := I) (M := M) hbilin)
          (vec2 (I := I) v w) =
        Araw x v w
    rw [tensor02OfRawAt_realizes (I := I) (M := M)]
    exact rawSym2_eq_of_symm (I := I) (M := M) hsym v w
  change shiftNAt (I := I) (M := M) delta t g x T
      (vec2 (I := I) (basis 0) (basis 0)) =
    shiftReactBlock3 delta a b c
  exact shiftNAt_comp_shiftBlock (I := I) (M := M) hreal hblock

/-- The canonical shifted reaction satisfies Hamilton's symmetric-input
null-eigenvector condition in dimension three for every `delta < 1/3`. -/
theorem shiftNRaw_null_symm_of_lt
    {G : Real -> SmoothRiemannianMetric I M} {U : Set Real} {delta : Real}
    (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3) :
    TensorNullEigenvectorConditionSymm (I := I) (M := M) G
      (shiftNRaw (I := I) (M := M) delta) U := by
  intro t ht A x hsym hbilin hpsd v hv
  have hBout :
      TwoTensorBilinearAt (I := I) (M := M)
        (shiftNRaw (I := I) (M := M) delta t (G t) A) x := by
    simpa [shiftNRaw] using
      (Tensor02ReactionAt.toRawSymm_output_bilin (I := I) (M := M) G
        (shiftNAt (I := I) (M := M) delta) U t ht A x)
  by_cases hv0 : v = 0
  · subst v
    have hzero :
        (shiftNRaw (I := I) (M := M) delta t (G t) A) x 0 0 = 0 := by
      have h := hBout.smul_left 0
        (0 : TangentSpace I x) (0 : TangentSpace I x)
      simpa using h
    rw [hzero]
  · obtain ⟨nb⟩ :=
      exists_nullOrthonormalBasis3At (I := I) (M := M) (G t)
        (x := x) (v := v) (hdim x) hv0
    rcases nb.scale with ⟨r, hr, hscale⟩
    let a : Real := A x (nb.basis 1) (nb.basis 1)
    let b : Real := A x (nb.basis 2) (nb.basis 2)
    let c : Real := A x (nb.basis 1) (nb.basis 2)
    have hblock :
        ShiftBlockAt (I := I) (M := M) (G t) A x nb.basis a b c :=
      shiftBlockOfNull (I := I) (M := M) nb.orthonormal hsym hbilin
        hpsd hv hscale hr
    have heval :
        (shiftNRaw (I := I) (M := M) delta t (G t) A) x v v =
          r ^ 2 * shiftReactBlock3 delta a b c := by
      rw [hscale]
      rw [hBout.smul_left r (nb.basis 0) (r • nb.basis 0)]
      rw [hBout.smul_right r (nb.basis 0) (nb.basis 0)]
      rw [shiftNRaw_realizes_block (I := I) (M := M)
        (delta := delta) (t := t) (g := G t)
        (Araw := A) (basis := nb.basis) (a := a) (b := b) (c := c)
        hsym hbilin hblock]
      ring
    rw [heval]
    exact mul_nonneg (sq_nonneg r)
      (shiftReactBlock3_nonneg_of_lt delta a b c hdelta13)

/-- The canonical shifted reaction satisfies Hamilton's symmetric-input
null-eigenvector condition in dimension three for `0 < delta < 1/3`. -/
theorem shiftNRaw_null_symm
    {G : Real -> SmoothRiemannianMetric I M} {U : Set Real} {delta : Real}
    (_hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3) :
    TensorNullEigenvectorConditionSymm (I := I) (M := M) G
      (shiftNRaw (I := I) (M := M) delta) U := by
  exact shiftNRaw_null_symm_of_lt (I := I) (M := M)
    (G := G) (U := U) hdelta13 hdim

/-- Reconstruct a bundled `(0,2)` tensor from `Fin 3` components in a supplied
basis.  This is a local component model, not a canonical basis-independent
producer. -/
def tensor02FromBasis
    {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (C : Fin 3 -> Fin 3 -> Real) :
    Tensor02At (I := I) (M := M) x :=
  (coordEquiv0S (I := I) basis 2).symm
    (fun slots : Fin 2 -> Fin 3 => C (slots 0) (slots 1))

@[simp]
theorem tensor02FromBasis_component
    {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (C : Fin 3 -> Fin 3 -> Real) (i j : Fin 3) :
    component0S (I := I) basis
        (tensor02FromBasis (I := I) (M := M) basis C) (slots2 i j) =
      C i j := by
  rw [← coordEquiv0S_apply (I := I) basis
    (tensor02FromBasis (I := I) (M := M) basis C)]
  simp [tensor02FromBasis, slots2]

@[simp]
theorem tensor02FromBasis_apply
    {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (C : Fin 3 -> Fin 3 -> Real) (i j : Fin 3) :
    tensor02FromBasis (I := I) (M := M) basis C
        (vec2 (I := I) (basis i) (basis j)) =
      C i j := by
  simpa [component0S_apply, slots2, vec2, RicciFlower.Curvature.vec2] using
    tensor02FromBasis_component (I := I) (M := M) basis C i j

/-- A `(0,2)` tensor is quadratic under scaling both input slots by the same
scalar. -/
theorem tensor02_smul2
    {x : M} (T : Tensor02At (I := I) (M := M) x)
    (r : Real) (X Y : TangentSpace I x) :
    T (vec2 (I := I) (r • X) (r • Y)) =
      r ^ 2 * T (vec2 (I := I) X Y) := by
  classical
  let m0 : Fin 2 -> TangentSpace I x := vec2 (I := I) X Y
  have h0 := T.map_update_smul m0 (0 : Fin 2) r X
  have h0left :
      Function.update m0 (0 : Fin 2) (r • X) =
        vec2 (I := I) (r • X) Y := by
    funext i
    fin_cases i <;> simp [m0, vec2, RicciFlower.Curvature.vec2, Function.update]
  have h0right :
      Function.update m0 (0 : Fin 2) X =
        vec2 (I := I) X Y := by
    funext i
    fin_cases i <;> simp [m0, vec2, RicciFlower.Curvature.vec2, Function.update]
  have h0eq :
      T (vec2 (I := I) (r • X) Y) =
        r * T (vec2 (I := I) X Y) := by
    simpa [h0left, h0right, smul_eq_mul] using h0
  let m1 : Fin 2 -> TangentSpace I x := vec2 (I := I) (r • X) Y
  have h1 := T.map_update_smul m1 (1 : Fin 2) r Y
  have h1left :
      Function.update m1 (1 : Fin 2) (r • Y) =
        vec2 (I := I) (r • X) (r • Y) := by
    funext i
    fin_cases i <;> simp [m1, vec2, RicciFlower.Curvature.vec2, Function.update]
  have h1right :
      Function.update m1 (1 : Fin 2) Y =
        vec2 (I := I) (r • X) Y := by
    funext i
    fin_cases i <;> simp [m1, vec2, RicciFlower.Curvature.vec2, Function.update]
  have h1eq :
      T (vec2 (I := I) (r • X) (r • Y)) =
        r * T (vec2 (I := I) (r • X) Y) := by
    simpa [h1left, h1right, smul_eq_mul] using h1
  rw [h1eq, h0eq]
  ring

/-- Scaled version of the canonical shifted-reaction block theorem. -/
theorem shiftNScaled
    {delta t : Real} {g : SmoothRiemannianMetric I M}
    {Araw : RawTwoTensorField (I := I) (M := M)} {x : M}
    {A : Tensor02At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {v : TangentSpace I x} {r a b c : Real}
    (hreal : Tensor02RealizesRawAt (I := I) (M := M) Araw x A)
    (hblock : ShiftBlockAt (I := I) (M := M) g Araw x basis a b c)
    (hscale : v = r • basis 0) :
    shiftNAt (I := I) (M := M) delta t g x A
        (vec2 (I := I) v v) =
      r ^ 2 * shiftReactBlock3 delta a b c := by
  rw [hscale]
  rw [tensor02_smul2 (I := I) (M := M)
    (shiftNAt (I := I) (M := M) delta t g x A) r (basis 0) (basis 0)]
  rw [shiftNAt_comp_shiftBlock (I := I) (M := M) hreal hblock]

/-- Basis-local tensor model for the shifted Ricci-flow reaction.  This bundles
the finite Hamilton reaction components in the supplied basis.  It is useful as
a local first-null bridge; a later reusable API should replace it with a
basis-independent raised-contraction producer. -/
def shiftNAtBasis
    (δ : Real) (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : Tensor02At (I := I) (M := M) x) :
    Tensor02At (I := I) (M := M) x :=
  let Ric := shiftRic3At (I := I) (M := M) δ g A
  let Rm := rm04OfRic3At (I := I) (M := M) g Ric
  tensor02FromBasis (I := I) (M := M) basis
    (fun i j =>
      pinchReact δ
        (fun a b c d => Rm (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
        (fun a b => Ric (vec2 (I := I) (basis a) (basis b))) i j)

@[simp]
theorem shiftNAtBasis_apply_basis
    (δ : Real) (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : Tensor02At (I := I) (M := M) x) (i j : Fin 3) :
    shiftNAtBasis (I := I) (M := M) δ g basis A
        (vec2 (I := I) (basis i) (basis j)) =
      pinchReact δ
        (fun a b c d =>
          rm04OfRic3At (I := I) (M := M) g
              (shiftRic3At (I := I) (M := M) δ g A)
            (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
        (fun a b =>
          shiftRic3At (I := I) (M := M) δ g A
            (vec2 (I := I) (basis a) (basis b))) i j := by
  simp [shiftNAtBasis]

/-- The basis-local shifted reaction realizes the checked first-null block
target.  This is the local bridge requested for the Section 9 frontier; it is
not yet the final canonical raw WMP reaction. -/
theorem shiftNAtBasis_comp_shiftBlock
    {δ : Real} {g : SmoothRiemannianMetric I M}
    {Araw : RawTwoTensorField (I := I) (M := M)} {x : M}
    {A : Tensor02At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {a b c : Real}
    (hreal : Tensor02RealizesRawAt (I := I) (M := M) Araw x A)
    (hblock : ShiftBlockAt (I := I) (M := M) g Araw x basis a b c) :
    shiftNAtBasis (I := I) (M := M) δ g basis A
        (vec2 (I := I) (basis 0) (basis 0)) =
      shiftReactBlock3 δ a b c := by
  have hRic :
      ∀ i j : Fin 3,
        shiftRic3At (I := I) (M := M) δ g A
            (vec2 (I := I) (basis i) (basis j)) =
          shiftRicBlock3 δ a b c i j :=
    shiftRic3At_comp_of_shiftBlock (I := I) (M := M) hreal hblock
  have hRm :
      ∀ i j k l : Fin 3,
        rm04OfRic3At (I := I) (M := M) g
            (shiftRic3At (I := I) (M := M) δ g A)
            (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)) =
          stdRmOfRic3 (shiftRicBlock3 δ a b c) i j k l := by
    intro i j k l
    rw [rm04OfRic3At_comp_orthonormal (I := I) (M := M) basis hblock.orthonormal]
    simp [hRic]
  simp [shiftReactBlock3, hRic, hRm]

/-- Scaled version of `shiftNAtBasis_comp_shiftBlock`.

If the WMP null vector is `r` times the first vector of the adapted basis, the
local tensor reaction evaluates to `r^2` times the checked block reaction. -/
theorem shiftNBasisScaled
    {delta : Real} {g : SmoothRiemannianMetric I M}
    {Araw : RawTwoTensorField (I := I) (M := M)} {x : M}
    {A : Tensor02At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {v : TangentSpace I x} {r a b c : Real}
    (hreal : Tensor02RealizesRawAt (I := I) (M := M) Araw x A)
    (hblock : ShiftBlockAt (I := I) (M := M) g Araw x basis a b c)
    (hscale : v = r • basis 0) :
    shiftNAtBasis (I := I) (M := M) delta g basis A
        (vec2 (I := I) v v) =
      r ^ 2 * shiftReactBlock3 delta a b c := by
  rw [hscale]
  rw [tensor02_smul2 (I := I) (M := M)
    (shiftNAtBasis (I := I) (M := M) delta g basis A) r (basis 0) (basis 0)]
  rw [shiftNAtBasis_comp_shiftBlock (I := I) (M := M) hreal hblock]

end RicciFlow
end RicciFlower
