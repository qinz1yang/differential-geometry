import RicciFlower.Curvature.Components
import RicciFlower.RoughLaplacian
import RicciFlower.LeviCivita.Basic
import RicciFlower.LeviCivita.Torsion
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Connection

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Bianchi Identity Interfaces

This file records the realized tensor statements for first Bianchi, second
Bianchi, and contracted Bianchi.  The identities are stated on bundled or
pointwise tensors; constructing the relevant curvature and covariant-derivative
tensors from a connection is kept as a separate producer frontier.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Bundle Tensor0SBundle
open scoped Topology Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem mdifferentiableAt_tangentConstAt_of_mem
    (x₀ : M) (v : TangentSpace I x₀) {p : M}
    (hp : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MDiffAt
      (T% (LeviCivita.tangentConstAt (I := I) x₀ v :
        (q : M) -> TangentSpace I q)) p := by
  unfold LeviCivita.tangentConstAt
  exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
    (𝕜 := Real) (I := I) (x₀ := x₀) (p := p) v hp

private theorem contMDiffAt_tangentConstAt_self_minTwo
    (x₀ : M) (v : TangentSpace I x₀) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : ℕ∞)
      (T% (LeviCivita.tangentConstAt (I := I) x₀ v :
        (p : M) -> TangentSpace I p)) x₀ := by
  let e := trivializationAt E (TangentSpace I) x₀
  have hx : x₀ ∈ e.baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x₀
  haveI : IsManifold I ((minSmoothness Real 2) + 1) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_num
    exact (inferInstance : IsManifold I 3 M)
  haveI : IsManifold I (((2 : ℕ∞) : WithTop ℕ∞) + 1) M := by
    change IsManifold I (3 : WithTop ℕ∞) M
    exact (inferInstance : IsManifold I 3 M)
  have h_on :
      ContMDiffOn I (I.prod 𝓘(Real, E)) (2 : ℕ∞)
        (T% (LeviCivita.tangentConstAt (I := I) x₀ v :
          (p : M) -> TangentSpace I p)) e.baseSet := by
    simpa [e, LeviCivita.tangentConstAt] using
      (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
        (𝕜 := Real) (I := I) (M := M)
        (n := (2 : ℕ∞)) x₀ v)
  exact (h_on x₀ hx).contMDiffAt (e.open_baseSet.mem_nhds hx)

private theorem contMDiffAt_tangentConstAt_mlieBracket_self_one
    (x₀ : M) (v w : TangentSpace I x₀) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : ℕ∞)
      (T% (VectorField.mlieBracket I
        (LeviCivita.tangentConstAt (I := I) x₀ v)
        (LeviCivita.tangentConstAt (I := I) x₀ w))) x₀ := by
  have hv : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : ℕ∞)
      (T% (LeviCivita.tangentConstAt (I := I) x₀ v :
        (p : M) -> TangentSpace I p)) x₀ :=
    contMDiffAt_tangentConstAt_self_minTwo (I := I) x₀ v
  have hw : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : ℕ∞)
      (T% (LeviCivita.tangentConstAt (I := I) x₀ w :
        (p : M) -> TangentSpace I p)) x₀ :=
    contMDiffAt_tangentConstAt_self_minTwo (I := I) x₀ w
  haveI : IsManifold I (minSmoothness Real 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (inferInstance : IsManifold I 2 M)
  haveI : IsManifold I (((2 : ℕ∞) : WithTop ℕ∞) + 1) M := by
    change IsManifold I (3 : WithTop ℕ∞) M
    exact (inferInstance : IsManifold I 3 M)
  exact
    ContMDiffAt.mlieBracket_vectorField (I := I) (m := (1 : ℕ∞))
      (n := (2 : ℕ∞)) hv hw (by
        rw [minSmoothness_of_isRCLikeNormedField]
        norm_num)

private theorem mdifferentiableAt_tangentConstAt_mlieBracket_self
    (x₀ : M) (v w : TangentSpace I x₀) :
    MDiffAt (T% (VectorField.mlieBracket I
      (LeviCivita.tangentConstAt (I := I) x₀ v)
      (LeviCivita.tangentConstAt (I := I) x₀ w))) x₀ :=
  (contMDiffAt_tangentConstAt_mlieBracket_self_one (I := I) x₀ v w).mdifferentiableAt
    (by norm_num : ((1 : ℕ∞) : WithTop ℕ∞) ≠ 0)

private theorem tangentConst_torsion_derivative_eq_add
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (htf : LeviCivita.IsTorsionFree (I := I) cov)
    (x : M) (A B C : TangentSpace I x) :
    (cov (fun p : M =>
        (cov (LeviCivita.tangentConstAt (I := I) x B) p)
          (LeviCivita.tangentConstAt (I := I) x A p)) x)
      (LeviCivita.tangentConstAt (I := I) x C x) =
      (cov (fun p : M =>
          (cov (LeviCivita.tangentConstAt (I := I) x A) p)
            (LeviCivita.tangentConstAt (I := I) x B p)) x)
        (LeviCivita.tangentConstAt (I := I) x C x) +
        (cov (VectorField.mlieBracket I
            (LeviCivita.tangentConstAt (I := I) x A)
            (LeviCivita.tangentConstAt (I := I) x B)) x)
          (LeviCivita.tangentConstAt (I := I) x C x) := by
  let Ac : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x A
  let Bc : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x B
  let Cc : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x C
  let ABc : (p : M) -> TangentSpace I p := fun p => (cov Bc p) (Ac p)
  let BAc : (p : M) -> TangentSpace I p := fun p => (cov Ac p) (Bc p)
  let BrAB : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Ac Bc
  have hAB : MDiffAt (T% ABc) x := by
    simpa [ABc, Ac, Bc, LeviCivita.tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := A) (w := B)
  have hBA : MDiffAt (T% BAc) x := by
    simpa [BAc, Ac, Bc, LeviCivita.tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := B) (w := A)
  have hBr : MDiffAt (T% BrAB) x := by
    simpa [BrAB, Ac, Bc] using
      mdifferentiableAt_tangentConstAt_mlieBracket_self (I := I) x A B
  have hsum : MDiffAt (T% (BAc + BrAB)) x :=
    mdifferentiableAt_add_section hBA hBr
  have heq : ABc =ᶠ[𝓝 x] BAc + BrAB := by
    let e := trivializationAt E (TangentSpace I) x
    filter_upwards [e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x)] with p hp
    have hAp : MDiffAt (T% Ac) p := by
      simpa [Ac] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x A
        (by simpa [e] using hp)
    have hBp : MDiffAt (T% Bc) p := by
      simpa [Bc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x B
        (by simpa [e] using hp)
    have hzero :=
      congrArg
        (fun T : TangentSpace I p →L[Real] TangentSpace I p →L[Real] TangentSpace I p =>
          T (Ac p) (Bc p))
        (htf p)
    change cov.torsion p (Ac p) (Bc p) = 0 at hzero
    rw [cov.torsion_apply hAp hBp] at hzero
    have ht :
        (cov Bc p) (Ac p) - (cov Ac p) (Bc p) =
          VectorField.mlieBracket I Ac Bc p := by
      exact sub_eq_zero.mp hzero
    dsimp [ABc, BAc, BrAB] at ht ⊢
    rw [← ht]
    abel
  have hcongr : cov ABc x = cov (BAc + BrAB) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hAB hsum (by simp) heq
  have happly :=
    congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x => L (Cc x)) hcongr
  rw [cov.isCovariantDerivativeOnUniv.add hBA hBr] at happly
  simpa [Ac, Bc, Cc, ABc, BAc, BrAB, Pi.add_apply] using happly

private theorem tangentConst_torsion_bracket_eq_add
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (htf : LeviCivita.IsTorsionFree (I := I) cov)
    (x : M) (A B C : TangentSpace I x) :
    (cov (VectorField.mlieBracket I
        (LeviCivita.tangentConstAt (I := I) x A)
        (LeviCivita.tangentConstAt (I := I) x B)) x)
      (LeviCivita.tangentConstAt (I := I) x C x) =
      (cov (LeviCivita.tangentConstAt (I := I) x C) x)
        ((VectorField.mlieBracket I
          (LeviCivita.tangentConstAt (I := I) x A)
          (LeviCivita.tangentConstAt (I := I) x B)) x) +
        VectorField.mlieBracket I (LeviCivita.tangentConstAt (I := I) x C)
          (VectorField.mlieBracket I
            (LeviCivita.tangentConstAt (I := I) x A)
            (LeviCivita.tangentConstAt (I := I) x B)) x := by
  let Ac : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x A
  let Bc : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x B
  let Cc : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x C
  let BrAB : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Ac Bc
  have hC : MDiffAt (T% Cc) x := by
    simpa [Cc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x C
      (mem_baseSet_trivializationAt E (TangentSpace I) x)
  have hBr : MDiffAt (T% BrAB) x := by
    simpa [BrAB, Ac, Bc] using
      mdifferentiableAt_tangentConstAt_mlieBracket_self (I := I) x A B
  have hzero :=
    congrArg
      (fun T : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x =>
        T (Cc x) (BrAB x))
      (htf x)
  change cov.torsion x (Cc x) (BrAB x) = 0 at hzero
  rw [cov.torsion_apply hC hBr] at hzero
  have ht :
      (cov BrAB x) (Cc x) - (cov Cc x) (BrAB x) =
        VectorField.mlieBracket I Cc BrAB x := by
    exact sub_eq_zero.mp hzero
  simpa [Ac, Bc, Cc, BrAB] using (sub_eq_iff_eq_add.mp ht).trans (by abel)

private theorem tangentConst_mlieBracket_jacobi_cyclic
    (x : M) (X Y Z : TangentSpace I x) :
    let Xc : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x X
    let Yc : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x Y
    let Zc : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x Z
    let BrYZ : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Yc Zc
    let BrZX : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Zc Xc
    let BrXY : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Xc Yc
    VectorField.mlieBracket I Xc BrYZ x +
      VectorField.mlieBracket I Yc BrZX x +
        VectorField.mlieBracket I Zc BrXY x = 0 := by
  let Xc : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x X
  let Yc : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x Y
  let Zc : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x Z
  let BrYZ : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Yc Zc
  let BrZX : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Zc Xc
  let BrXY : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Xc Yc
  haveI : IsManifold I (minSmoothness Real 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (inferInstance : IsManifold I 3 M)
  have h0 :
      VectorField.mlieBracket I Xc BrYZ x =
        VectorField.mlieBracket I BrXY Zc x +
          VectorField.mlieBracket I Yc (VectorField.mlieBracket I Xc Zc) x := by
    simpa [Xc, Yc, Zc, BrYZ, BrXY] using
      (VectorField.leibniz_identity_mlieBracket_apply (I := I)
        (U := Xc) (V := Yc) (W := Zc) (x := x)
        (by
          simpa [Xc, minSmoothness_of_isRCLikeNormedField] using
            contMDiffAt_tangentConstAt_self_minTwo (I := I) x X)
        (by
          simpa [Yc, minSmoothness_of_isRCLikeNormedField] using
            contMDiffAt_tangentConstAt_self_minTwo (I := I) x Y)
        (by
          simpa [Zc, minSmoothness_of_isRCLikeNormedField] using
            contMDiffAt_tangentConstAt_self_minTwo (I := I) x Z))
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := BrXY) (W := Zc) (x := x)] at h0
  have hZX_mdiff : MDiffAt (T% BrZX) x := by
    simpa [BrZX, Zc, Xc] using
      mdifferentiableAt_tangentConstAt_mlieBracket_self (I := I) x Z X
  have hXZ : VectorField.mlieBracket I Xc Zc = (-1 : Real) • BrZX := by
    funext p
    simp [BrZX, VectorField.mlieBracket_swap_apply (I := I) (V := Xc) (W := Zc) (x := p)]
  rw [hXZ] at h0
  rw [VectorField.mlieBracket_const_smul_right (I := I) (c := (-1 : Real))
    (V := Yc) (W := BrZX) hZX_mdiff] at h0
  simp at h0
  change
    VectorField.mlieBracket I Xc BrYZ x +
      VectorField.mlieBracket I Yc BrZX x +
        VectorField.mlieBracket I Zc BrXY x = 0
  rw [h0]
  abel

/-- Feed five explicit tangent vectors into a `Fin 5` tensor.  For a covariant
derivative of a `(0,4)` tensor, the first slot is the derivative direction. -/
def vec5 {x : M} (A B C D F : TangentSpace I x) :
    Fin 5 -> TangentSpace I x :=
  fun i =>
    if i = 0 then A
    else if i = 1 then B
    else if i = 2 then C
    else if i = 3 then D
    else F

/-- First Bianchi identity for a lowered Riemann tensor:
`R(W,X,Y,Z) + R(W,Y,Z,X) + R(W,Z,X,Y) = 0`. -/
def FirstBianchiAt {x : M} (Rm04 : Tensor04At (I := I) (M := M) x) : Prop :=
  ∀ W X Y Z : TangentSpace I x,
    Rm04 (vec4 W X Y Z) + Rm04 (vec4 W Y Z X) + Rm04 (vec4 W Z X Y) = 0

theorem first_bianchi {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (h : FirstBianchiAt (I := I) Rm04)
    (W X Y Z : TangentSpace I x) :
    Rm04 (vec4 W X Y Z) + Rm04 (vec4 W Y Z X) + Rm04 (vec4 W Z X Y) = 0 :=
  h W X Y Z

/-- Section-level first Bianchi identity. -/
def FirstBianchiSection (Rm04 : Tensor04Section (I := I) (M := M)) : Prop :=
  ∀ x : M, FirstBianchiAt (I := I) (Rm04 x)

theorem first_bianchi_apply
    (Rm04 : Tensor04Section (I := I) (M := M))
    (h : FirstBianchiSection (I := I) Rm04)
    (x : M) (W X Y Z : TangentSpace I x) :
    Rm04 x (vec4 W X Y Z) + Rm04 x (vec4 W Y Z X) +
      Rm04 x (vec4 W Z X Y) = 0 :=
  h x W X Y Z

/-- Operator-level first Bianchi identity for a torsion-free connection,
specialized to tangent-constant extensions at one point.

This is the geometric producer frontier behind the lowered tensor statement:
differentiate the torsion-free identity, use the Jacobi identity for the Lie
bracket, and cancel the cyclic terms. -/
theorem connectionRiemannCurvatureField_tangentConst_first_bianchi_of_torsionFree
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (htf : LeviCivita.IsTorsionFree (I := I) cov)
    (x : M) (X Y Z : TangentSpace I x) :
    connectionRiemannCurvatureField (I := I) cov
        (LeviCivita.tangentConstAt (I := I) x X)
        (LeviCivita.tangentConstAt (I := I) x Y)
        (LeviCivita.tangentConstAt (I := I) x Z) x +
      connectionRiemannCurvatureField (I := I) cov
        (LeviCivita.tangentConstAt (I := I) x Y)
        (LeviCivita.tangentConstAt (I := I) x Z)
        (LeviCivita.tangentConstAt (I := I) x X) x +
      connectionRiemannCurvatureField (I := I) cov
        (LeviCivita.tangentConstAt (I := I) x Z)
        (LeviCivita.tangentConstAt (I := I) x X)
        (LeviCivita.tangentConstAt (I := I) x Y) x = 0 := by
  unfold RicciFlower.Realized.connectionRiemannCurvatureField
    RicciFlower.Curvature.connectionRiemannCurvatureField
  rw [tangentConst_torsion_derivative_eq_add (I := I) cov hcov htf x Y Z X]
  rw [tangentConst_torsion_derivative_eq_add (I := I) cov hcov htf x Z X Y]
  rw [tangentConst_torsion_derivative_eq_add (I := I) cov hcov htf x X Y Z]
  rw [tangentConst_torsion_bracket_eq_add (I := I) cov htf x Y Z X]
  rw [tangentConst_torsion_bracket_eq_add (I := I) cov htf x Z X Y]
  rw [tangentConst_torsion_bracket_eq_add (I := I) cov htf x X Y Z]
  have hJac := tangentConst_mlieBracket_jacobi_cyclic (I := I) x X Y Z
  dsimp only at hJac
  abel_nf
  simpa [add_assoc] using hJac

/-- Second Bianchi identity for the covariant derivative of lowered Riemann.
The tensor slots are `(derivative, W, X, Y, Z)`. -/
def SecondBianchiAt {x : M}
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x) :
    Prop :=
  ∀ A W X Y Z : TangentSpace I x,
    nablaRm04 (vec5 A W X Y Z) +
      nablaRm04 (vec5 X W Y A Z) +
        nablaRm04 (vec5 Y W A X Z) = 0

theorem second_bianchi {x : M}
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (h : SecondBianchiAt (I := I) nablaRm04)
    (A W X Y Z : TangentSpace I x) :
    nablaRm04 (vec5 A W X Y Z) +
      nablaRm04 (vec5 X W Y A Z) +
        nablaRm04 (vec5 Y W A X Z) = 0 :=
  h A W X Y Z

/-- Section-level second Bianchi identity. -/
def SecondBianchiSection
    (nablaRm04 : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x) :
    Prop :=
  ∀ x : M, SecondBianchiAt (I := I) (nablaRm04 x)

theorem second_bianchi_apply
    (nablaRm04 : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (h : SecondBianchiSection (I := I) nablaRm04)
    (x : M) (A W X Y Z : TangentSpace I x) :
    nablaRm04 x (vec5 A W X Y Z) +
      nablaRm04 x (vec5 X W Y A Z) +
        nablaRm04 x (vec5 Y W A X Z) = 0 :=
  h x A W X Y Z

/-- Contracted second Bianchi in a tangent basis:
`div Ric = (1/2) d scalar`.  The slots of `nablaRic` are
`(derivative, first Ricci slot, second Ricci slot)`. -/
def ContractedBianchiAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Prop :=
  ∀ X : TangentSpace I x,
    (∑ i : Idx, ∑ j : Idx,
      gInv i j * nablaRic (vec3 (basis i) (basis j) X)) =
        (1 / 2 : Real) * dScalar (fun _ : Fin 1 => X)

theorem contracted_bianchi
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (h : ContractedBianchiAt (I := I) basis gInv nablaRic dScalar)
    (X : TangentSpace I x) :
    (∑ i : Idx, ∑ j : Idx,
      gInv i j * nablaRic (vec3 (basis i) (basis j) X)) =
        (1 / 2 : Real) * dScalar (fun _ : Fin 1 => X) :=
  h X

/-- Explicit bridge saying that a second-Bianchi proof supplies the contracted
Bianchi identity after the metric trace and Ricci/scalar trace reductions have
been performed.  This keeps the hard contraction proof as a named producer. -/
def ContractedBianchiOfSecondAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Prop :=
  SecondBianchiAt (I := I) nablaRm04 ->
    ContractedBianchiAt (I := I) basis gInv nablaRic dScalar

theorem contracted_bianchi_of_second
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hcontract : ContractedBianchiOfSecondAt (I := I) basis gInv nablaRm04
      nablaRic dScalar)
    (hsecond : SecondBianchiAt (I := I) nablaRm04) :
    ContractedBianchiAt (I := I) basis gInv nablaRic dScalar :=
  hcontract hsecond

end Realized
end RicciFlower
