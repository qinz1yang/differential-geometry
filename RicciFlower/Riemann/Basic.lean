import RicciFlower.Curvature.Tensor
import RicciFlower.Tensor.RSTensor.NablaOnTensors
import RicciFlower.VectorBundle.TangentConst
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Pointwise Riemann and Ricci tensors

This file starts a definition-first curvature layer.  The auxiliary curvature
operator is the usual vector-field formula, and the pointwise tensors are the
objects intended for downstream use.  The constructors use chart-constant
tangent-field representatives; arbitrary smooth-field tensoriality is a separate
extension theorem frontier, not part of these definitions.
-/

noncomputable section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Bundle Tensor0SBundle RicciFlower.Curvature
open scoped BigOperators Manifold ContDiff Topology

namespace RicciFlower.Riemann

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type _} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CovariantDerivative

private noncomputable def tangentConstAt (x : M) (v : TangentSpace I x) (p : M) :
    TangentSpace I p :=
  TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v p

@[simp] private theorem tangentConstAt_self (x : M) (v : TangentSpace I x) :
    tangentConstAt (I := I) x v x = v := by
  unfold tangentConstAt
  rw [TensorLieDeriv.tangentConstInChart_apply]
  have hL :
      (trivializationAt E (TangentSpace I) x).symmL Real x =
        (1 : E →L[Real] E) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core
      (𝕜 := Real) (I := I) (b₀ := x) (b := x) (mem_chart_source H x)]
    ext w
    exact (tangentBundleCore I M).coordChange_self (achart H x) x
      (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H x) w
  rw [hL]
  rfl

private theorem mdifferentiableAt_tangentConstAt_self
    (x : M) (v : TangentSpace I x) :
    MDiffAt (T% (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p)) x := by
  unfold tangentConstAt
  exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
    (𝕜 := Real) (I := I) (x₀ := x) (p := x) v
    (mem_baseSet_trivializationAt E (TangentSpace I) x)

@[simp] private theorem tangentConstAt_add (x : M) (v w : TangentSpace I x) :
    (tangentConstAt (I := I) x (v + w) : (p : M) → TangentSpace I p) =
      (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p) +
        tangentConstAt (I := I) x w := by
  unfold tangentConstAt
  exact TensorLieDeriv.tangentConstInChart_add (𝕜 := Real) (I := I) x v w

@[simp] private theorem tangentConstAt_smul (x : M) (a : Real) (v : TangentSpace I x) :
    (tangentConstAt (I := I) x (a • v) : (p : M) → TangentSpace I p) =
      a • (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p) := by
  unfold tangentConstAt
  exact TensorLieDeriv.tangentConstInChart_smul (𝕜 := Real) (I := I) x a v

private theorem cov_tangentConst_apply_mdiffAt_self
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (v w : TangentSpace I x) :
    MDiffAt
      (T% (fun p : M => (cov (tangentConstAt (I := I) x v) p)
        (tangentConstAt (I := I) x w p))) x := by
  unfold tangentConstAt
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  haveI : IsManifold I (((∞ : WithTop ℕ∞) + 1) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have h_on :
      CMDiff[e.baseSet] ∞
        (T% (fun p : M =>
          (cov (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v) p)
            (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x w p))) := by
    have hσ :
        CMDiff[e.baseSet] (∞ + 1)
          (T% (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v :
            (p : M) → TangentSpace I p)) := by
      simpa [e] using
        (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := Real) (I := I) (M := M) (n := (∞ : WithTop ℕ∞) + 1) x v)
    have hcovσ :
        ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) ∞
          (fun p : M =>
            (⟨p, cov
              (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v) p⟩ :
              TotalSpace (E →L[Real] E)
                (fun p : M => TangentSpace I p →L[Real] TangentSpace I p)))
          e.baseSet := by
      exact (hcov e.open_baseSet).contMDiff hσ
    have hX :
        CMDiff[e.baseSet] ∞
          (T% (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x w :
            (p : M) → TangentSpace I p)) := by
      simpa [e] using
        (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := Real) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) x w)
    simpa [e] using hcovσ.clm_bundle_apply hX
  have h_at : CMDiffAt ∞
      (T% (fun p : M =>
        (cov (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v) p)
          (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x w p))) x :=
    (h_on x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)
  exact h_at.mdifferentiableAt (by simp)

private theorem cov_tangentConst_add_apply_eventuallyEq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (v₁ v₂ w : TangentSpace I x) :
    (fun p : M => (cov (tangentConstAt (I := I) x (v₁ + v₂)) p)
        (tangentConstAt (I := I) x w p))
      =ᶠ[𝓝 x]
    (fun p : M =>
      (cov (tangentConstAt (I := I) x v₁) p) (tangentConstAt (I := I) x w p) +
        (cov (tangentConstAt (I := I) x v₂) p) (tangentConstAt (I := I) x w p)) := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  filter_upwards [e.open_baseSet.mem_nhds hx] with p hp
  have hv₁ : MDiffAt (T% (tangentConstAt (I := I) x v₁ : (p : M) → TangentSpace I p)) p := by
    unfold tangentConstAt
    exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := Real) (I := I) (x₀ := x) (p := p) v₁ (by simpa [e] using hp)
  have hv₂ : MDiffAt (T% (tangentConstAt (I := I) x v₂ : (p : M) → TangentSpace I p)) p := by
    unfold tangentConstAt
    exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := Real) (I := I) (x₀ := x) (p := p) v₂ (by simpa [e] using hp)
  rw [tangentConstAt_add]
  rw [cov.isCovariantDerivativeOnUniv.add hv₁ hv₂]
  simp

private theorem cov_tangentConst_smul_apply_eventuallyEq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (a : Real) (v w : TangentSpace I x) :
    (fun p : M => (cov (tangentConstAt (I := I) x (a • v)) p)
        (tangentConstAt (I := I) x w p))
      =ᶠ[𝓝 x]
    (fun p : M =>
      a • (cov (tangentConstAt (I := I) x v) p) (tangentConstAt (I := I) x w p)) := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  filter_upwards [e.open_baseSet.mem_nhds hx] with p hp
  have hv : MDiffAt (T% (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p)) p := by
    unfold tangentConstAt
    exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := Real) (I := I) (x₀ := x) (p := p) v (by simpa [e] using hp)
  rw [tangentConstAt_smul]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hv]
  simp [Pi.smul_apply]

/-- The curvature operator of a covariant derivative, before tensorial descent.

The sign convention is
`∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.
-/
def riemannCurvatureAux
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : (p : M) → TangentSpace I p) (x : M) : TangentSpace I x :=
  (cov (fun p => (cov Z p) (Y p)) x) (X x) -
    (cov (fun p => (cov Z p) (X p)) x) (Y x) -
      (cov Z x) (VectorField.mlieBracket I X Y x)

@[simp]
theorem riemannCurvatureAux_eq_connectionRiemannCurvatureField
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : (p : M) → TangentSpace I p) (x : M) :
    riemannCurvatureAux cov X Y Z x =
      connectionRiemannCurvatureField cov X Y Z x := rfl

private theorem riemannCurvatureAux_tangentConst_add_first
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X₁ X₂ Y Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x (X₁ + X₂))
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x =
      riemannCurvatureAux cov
          (tangentConstAt (I := I) x X₁)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x +
        riemannCurvatureAux cov
          (tangentConstAt (I := I) x X₂)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x := by
  let X₁c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X₁
  let X₂c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X₂
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  have hX₁ : MDiffAt (T% X₁c) x := mdifferentiableAt_tangentConstAt_self (I := I) x X₁
  have hX₂ : MDiffAt (T% X₂c) x := mdifferentiableAt_tangentConstAt_self (I := I) x X₂
  have hZX₁ : MDiffAt (T% (fun p : M => (cov Zc p) (X₁c p))) x := by
    simpa [X₁c, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z X₁
  have hZX₂ : MDiffAt (T% (fun p : M => (cov Zc p) (X₂c p))) x := by
    simpa [X₂c, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z X₂
  have hmid :
      (fun p : M => (cov Zc p) ((X₁c + X₂c) p)) =
        (fun p : M => (cov Zc p) (X₁c p)) +
          (fun p : M => (cov Zc p) (X₂c p)) := by
    funext p
    simp [Pi.add_apply, map_add]
  rw [tangentConstAt_add]
  change
    riemannCurvatureAux cov (X₁c + X₂c) Yc Zc x =
      riemannCurvatureAux cov X₁c Yc Zc x +
        riemannCurvatureAux cov X₂c Yc Zc x
  unfold riemannCurvatureAux
  rw [hmid]
  rw [cov.isCovariantDerivativeOnUniv.add hZX₁ hZX₂]
  rw [VectorField.mlieBracket_add_left (I := I) hX₁ hX₂]
  simp [Pi.add_apply, map_add]
  module

private theorem riemannCurvatureAux_tangentConst_smul_first
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (a : Real) (X Y Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x (a • X))
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x =
      a • riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  have hX : MDiffAt (T% Xc) x := mdifferentiableAt_tangentConstAt_self (I := I) x X
  have hZX : MDiffAt (T% (fun p : M => (cov Zc p) (Xc p))) x := by
    simpa [Xc, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z X
  have hmid :
      (fun p : M => (cov Zc p) ((a • Xc) p)) =
        a • (fun p : M => (cov Zc p) (Xc p)) := by
    funext p
    simp [Pi.smul_apply, map_smul]
  rw [tangentConstAt_smul]
  change
    riemannCurvatureAux cov (a • Xc) Yc Zc x =
      a • riemannCurvatureAux cov Xc Yc Zc x
  unfold riemannCurvatureAux
  rw [hmid]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZX]
  rw [VectorField.mlieBracket_const_smul_left (I := I) (c := a) hX]
  simp [Pi.smul_apply, map_smul]
  module

private theorem riemannCurvatureAux_tangentConst_add_second
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X Y₁ Y₂ Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x (Y₁ + Y₂))
        (tangentConstAt (I := I) x Z) x =
      riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y₁)
          (tangentConstAt (I := I) x Z) x +
        riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y₂)
          (tangentConstAt (I := I) x Z) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Y₁c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y₁
  let Y₂c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y₂
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  have hY₁ : MDiffAt (T% Y₁c) x := mdifferentiableAt_tangentConstAt_self (I := I) x Y₁
  have hY₂ : MDiffAt (T% Y₂c) x := mdifferentiableAt_tangentConstAt_self (I := I) x Y₂
  have hZY₁ : MDiffAt (T% (fun p : M => (cov Zc p) (Y₁c p))) x := by
    simpa [Y₁c, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z Y₁
  have hZY₂ : MDiffAt (T% (fun p : M => (cov Zc p) (Y₂c p))) x := by
    simpa [Y₂c, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z Y₂
  have hmid :
      (fun p : M => (cov Zc p) ((Y₁c + Y₂c) p)) =
        (fun p : M => (cov Zc p) (Y₁c p)) +
          (fun p : M => (cov Zc p) (Y₂c p)) := by
    funext p
    simp [Pi.add_apply, map_add]
  rw [tangentConstAt_add]
  change
    riemannCurvatureAux cov Xc (Y₁c + Y₂c) Zc x =
      riemannCurvatureAux cov Xc Y₁c Zc x +
        riemannCurvatureAux cov Xc Y₂c Zc x
  unfold riemannCurvatureAux
  rw [hmid]
  rw [cov.isCovariantDerivativeOnUniv.add hZY₁ hZY₂]
  rw [VectorField.mlieBracket_add_right (I := I) hY₁ hY₂]
  simp [Pi.add_apply, map_add]
  module

private theorem riemannCurvatureAux_tangentConst_smul_second
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (a : Real) (X Y Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x (a • Y))
        (tangentConstAt (I := I) x Z) x =
      a • riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  have hY : MDiffAt (T% Yc) x := mdifferentiableAt_tangentConstAt_self (I := I) x Y
  have hZY : MDiffAt (T% (fun p : M => (cov Zc p) (Yc p))) x := by
    simpa [Yc, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z Y
  have hmid :
      (fun p : M => (cov Zc p) ((a • Yc) p)) =
        a • (fun p : M => (cov Zc p) (Yc p)) := by
    funext p
    simp [Pi.smul_apply, map_smul]
  rw [tangentConstAt_smul]
  change
    riemannCurvatureAux cov Xc (a • Yc) Zc x =
      a • riemannCurvatureAux cov Xc Yc Zc x
  unfold riemannCurvatureAux
  rw [hmid]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZY]
  rw [VectorField.mlieBracket_const_smul_right (I := I) (c := a) hY]
  simp [Pi.smul_apply, map_smul]
  module

private theorem riemannCurvatureAux_tangentConst_add_third
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X Y Z₁ Z₂ : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x (Z₁ + Z₂)) x =
      riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z₁) x +
        riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z₂) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Z₁c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z₁
  let Z₂c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z₂
  let Z₁₂c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x (Z₁ + Z₂)
  have hZ₁ : MDiffAt (T% Z₁c) x := mdifferentiableAt_tangentConstAt_self (I := I) x Z₁
  have hZ₂ : MDiffAt (T% Z₂c) x := mdifferentiableAt_tangentConstAt_self (I := I) x Z₂
  have hZ₁₂Y : MDiffAt (T% (fun p : M => (cov Z₁₂c p) (Yc p))) x := by
    simpa [Z₁₂c, Yc] using
      cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x (Z₁ + Z₂) Y
  have hZ₁Y : MDiffAt (T% (fun p : M => (cov Z₁c p) (Yc p))) x := by
    simpa [Z₁c, Yc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z₁ Y
  have hZ₂Y : MDiffAt (T% (fun p : M => (cov Z₂c p) (Yc p))) x := by
    simpa [Z₂c, Yc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z₂ Y
  have hZ₁₂X : MDiffAt (T% (fun p : M => (cov Z₁₂c p) (Xc p))) x := by
    simpa [Z₁₂c, Xc] using
      cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x (Z₁ + Z₂) X
  have hZ₁X : MDiffAt (T% (fun p : M => (cov Z₁c p) (Xc p))) x := by
    simpa [Z₁c, Xc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z₁ X
  have hZ₂X : MDiffAt (T% (fun p : M => (cov Z₂c p) (Xc p))) x := by
    simpa [Z₂c, Xc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z₂ X
  have hsumY :
      MDiffAt
        (T% ((fun p : M => (cov Z₁c p) (Yc p)) +
          fun p : M => (cov Z₂c p) (Yc p))) x :=
    mdifferentiableAt_add_section hZ₁Y hZ₂Y
  have hsumX :
      MDiffAt
        (T% ((fun p : M => (cov Z₁c p) (Xc p)) +
          fun p : M => (cov Z₂c p) (Xc p))) x :=
    mdifferentiableAt_add_section hZ₁X hZ₂X
  have hcongrY :
      cov (fun p : M => (cov Z₁₂c p) (Yc p)) x =
        cov ((fun p : M => (cov Z₁c p) (Yc p)) +
          fun p : M => (cov Z₂c p) (Yc p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZ₁₂Y hsumY
      (by simp)
      (by simpa [Z₁₂c, Z₁c, Z₂c, Yc] using
        cov_tangentConst_add_apply_eventuallyEq (I := I) cov x Z₁ Z₂ Y)
  have hcongrX :
      cov (fun p : M => (cov Z₁₂c p) (Xc p)) x =
        cov ((fun p : M => (cov Z₁c p) (Xc p)) +
          fun p : M => (cov Z₂c p) (Xc p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZ₁₂X hsumX
      (by simp)
      (by simpa [Z₁₂c, Z₁c, Z₂c, Xc] using
        cov_tangentConst_add_apply_eventuallyEq (I := I) cov x Z₁ Z₂ X)
  change
    riemannCurvatureAux cov Xc Yc Z₁₂c x =
      riemannCurvatureAux cov Xc Yc Z₁c x +
        riemannCurvatureAux cov Xc Yc Z₂c x
  unfold riemannCurvatureAux
  rw [hcongrY, hcongrX]
  rw [show Z₁₂c = Z₁c + Z₂c by
    simp [Z₁₂c, Z₁c, Z₂c]]
  rw [cov.isCovariantDerivativeOnUniv.add hZ₁Y hZ₂Y]
  rw [cov.isCovariantDerivativeOnUniv.add hZ₁X hZ₂X]
  rw [cov.isCovariantDerivativeOnUniv.add hZ₁ hZ₂]
  simp
  module

private theorem riemannCurvatureAux_tangentConst_smul_third
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (a : Real) (X Y Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x (a • Z)) x =
      a • riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  let Za : (p : M) → TangentSpace I p := tangentConstAt (I := I) x (a • Z)
  have hZ : MDiffAt (T% Zc) x := mdifferentiableAt_tangentConstAt_self (I := I) x Z
  have hZaY : MDiffAt (T% (fun p : M => (cov Za p) (Yc p))) x := by
    simpa [Za, Yc] using
      cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x (a • Z) Y
  have hZY : MDiffAt (T% (fun p : M => (cov Zc p) (Yc p))) x := by
    simpa [Zc, Yc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z Y
  have hZaX : MDiffAt (T% (fun p : M => (cov Za p) (Xc p))) x := by
    simpa [Za, Xc] using
      cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x (a • Z) X
  have hZX : MDiffAt (T% (fun p : M => (cov Zc p) (Xc p))) x := by
    simpa [Zc, Xc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z X
  have hsmulY :
      MDiffAt (T% (a • fun p : M => (cov Zc p) (Yc p))) x :=
    mdifferentiableAt_const.smul_section hZY
  have hsmulX :
      MDiffAt (T% (a • fun p : M => (cov Zc p) (Xc p))) x :=
    mdifferentiableAt_const.smul_section hZX
  have hcongrY :
      cov (fun p : M => (cov Za p) (Yc p)) x =
        cov (a • fun p : M => (cov Zc p) (Yc p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZaY hsmulY
      (by simp)
      (by simpa [Za, Zc, Yc] using
        cov_tangentConst_smul_apply_eventuallyEq (I := I) cov x a Z Y)
  have hcongrX :
      cov (fun p : M => (cov Za p) (Xc p)) x =
        cov (a • fun p : M => (cov Zc p) (Xc p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZaX hsmulX
      (by simp)
      (by simpa [Za, Zc, Xc] using
        cov_tangentConst_smul_apply_eventuallyEq (I := I) cov x a Z X)
  change
    riemannCurvatureAux cov Xc Yc Za x =
      a • riemannCurvatureAux cov Xc Yc Zc x
  unfold riemannCurvatureAux
  rw [hcongrY, hcongrX]
  rw [show Za = a • Zc by
    simp [Za, Zc]]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZY]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZX]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZ]
  simp [Pi.smul_apply]
  module

private noncomputable def riemannCurvatureZCLM
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    TangentSpace I x →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z =>
        cotangentToDual α
          (riemannCurvatureAux cov
            (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
            (tangentConstAt (I := I) x Z) x)
      map_add' := by
        intro Z₁ Z₂
        change
          cotangentToDual α
              (riemannCurvatureAux cov
                (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                (tangentConstAt (I := I) x (Z₁ + Z₂)) x) =
            cotangentToDual α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                  (tangentConstAt (I := I) x Z₁) x) +
              cotangentToDual α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                  (tangentConstAt (I := I) x Z₂) x)
        rw [riemannCurvatureAux_tangentConst_add_third cov hcov x X Y Z₁ Z₂]
        exact map_add (cotangentToDual α) _ _
      map_smul' := by
        intro a Z
        change
          cotangentToDual α
              (riemannCurvatureAux cov
                (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                (tangentConstAt (I := I) x (a • Z)) x) =
            a • cotangentToDual α
              (riemannCurvatureAux cov
                (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                (tangentConstAt (I := I) x Z) x)
        rw [riemannCurvatureAux_tangentConst_smul_third cov hcov x a X Y Z]
        exact map_smul (cotangentToDual α) a _ }

@[simp] private theorem riemannCurvatureZCLM_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
    riemannCurvatureZCLM cov hcov x α X Y Z =
      cotangentToDual α
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := rfl

private noncomputable def riemannCurvatureYZModel
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X : TangentSpace I x) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ :=
  ContinuousLinearMap.uncurryLeft
    (𝕜 := Real) (n := 1) (Ei := fun _ : Fin 2 => TangentSpace I x) (G := Real)
    (LinearMap.toContinuousLinearMap
      { toFun := fun Y =>
          (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
            (riemannCurvatureZCLM cov hcov x α X Y)
        map_add' := by
          intro Y₁ Y₂
          apply (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).injective
          ext Z
          change
            cotangentToDual α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x (Y₁ + Y₂))
                  (tangentConstAt (I := I) x Z) x) =
              cotangentToDual α
                  (riemannCurvatureAux cov
                    (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y₁)
                    (tangentConstAt (I := I) x Z) x) +
                cotangentToDual α
                  (riemannCurvatureAux cov
                    (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y₂)
                    (tangentConstAt (I := I) x Z) x)
          rw [riemannCurvatureAux_tangentConst_add_second cov hcov x X Y₁ Y₂ Z]
          exact map_add (cotangentToDual α) _ _
        map_smul' := by
          intro a Y
          apply (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).injective
          ext Z
          change
            cotangentToDual α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x (a • Y))
                  (tangentConstAt (I := I) x Z) x) =
              a • cotangentToDual α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                  (tangentConstAt (I := I) x Z) x)
          rw [riemannCurvatureAux_tangentConst_smul_second cov hcov x a X Y Z]
          exact map_smul (cotangentToDual α) a _ })

@[simp] private theorem riemannCurvatureYZModel_apply_vec2
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
  riemannCurvatureYZModel cov hcov x α X (vec2 Y Z) =
      cotangentToDual α
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  unfold riemannCurvatureYZModel
  rw [ContinuousLinearMap.uncurryLeft_apply]
  change
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
      (riemannCurvatureZCLM cov hcov x α X Y))
      (fun i : Fin 1 => vec2 Y Z i.succ) =
    cotangentToDual α
      (riemannCurvatureAux cov
        (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x)
  rw [show (fun i : Fin 1 => vec2 Y Z i.succ) = fun _ : Fin 1 => Z by
    funext i
    fin_cases i
    simp [vec2]]
  rfl

private noncomputable def riemannCurvatureModel
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I x) ℝ :=
  ContinuousLinearMap.uncurryLeft
    (𝕜 := Real) (n := 2) (Ei := fun _ : Fin 3 => TangentSpace I x) (G := Real)
    (LinearMap.toContinuousLinearMap
      { toFun := fun X => riemannCurvatureYZModel cov hcov x α X
        map_add' := by
          intro X₁ X₂
          apply ContinuousMultilinearMap.ext
          intro v
          have hv : v = vec2 (v 0) (v 1) := by
            funext i
            fin_cases i <;> simp [vec2]
          rw [hv]
          simp only [riemannCurvatureYZModel_apply_vec2]
          rw [riemannCurvatureAux_tangentConst_add_first cov hcov x X₁ X₂ (v 0) (v 1)]
          exact map_add (cotangentToDual α) _ _
        map_smul' := by
          intro a X
          apply ContinuousMultilinearMap.ext
          intro v
          have hv : v = vec2 (v 0) (v 1) := by
            funext i
            fin_cases i <;> simp [vec2]
          rw [hv]
          simp only [riemannCurvatureYZModel_apply_vec2]
          rw [riemannCurvatureAux_tangentConst_smul_first cov hcov x a X (v 0) (v 1)]
          exact map_smul (cotangentToDual α) a _ })

/-- The pointwise `(1,3)` Riemann curvature tensor of a covariant derivative. -/
noncomputable def riemannCurvatureAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    Tensor13At (I := I) (M := M) x :=
  TensorRSSpace.ofModel (I := I) (x := x)
    (LinearMap.toContinuousLinearMap
    { toFun := fun α =>
        riemannCurvatureModel cov hcov x
          (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α)
      map_add' := by
        intro α β
        apply ContinuousMultilinearMap.ext
        intro v
        let R := riemannCurvatureAux cov
          (tangentConstAt (I := I) x (v 0)) (tangentConstAt (I := I) x (v 1))
          (tangentConstAt (I := I) x (v 2)) x
        change cotangentToDual (I := I)
            (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (α + β)) R =
          cotangentToDual (I := I)
              (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α) R +
            cotangentToDual (I := I)
              (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) β) R
        have hαβ :
            Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (α + β) =
              Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α +
                Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) β := by
          exact map_add
            (tensor0SSpace_continuousLinearEquiv (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x).symm α β
        rw [hαβ]
        rfl
      map_smul' := by
        intro c α
        apply ContinuousMultilinearMap.ext
        intro v
        let R := riemannCurvatureAux cov
          (tangentConstAt (I := I) x (v 0)) (tangentConstAt (I := I) x (v 1))
          (tangentConstAt (I := I) x (v 2)) x
        change cotangentToDual (I := I)
            (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (c • α)) R =
          c • cotangentToDual (I := I)
            (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α) R
        have hα :
            Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (c • α) =
              c • Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α := by
          exact map_smul
            (tensor0SSpace_continuousLinearEquiv (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x).symm c α
        rw [hα]
        rfl })

@[simp]
theorem riemannCurvatureAt_apply_const
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
    riemannCurvatureAt cov hcov x α (vec3 X Y Z) =
      cotangentToDual α
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  change (riemannCurvatureModel cov hcov x α) (vec3 X Y Z) =
    cotangentToDual α
      (riemannCurvatureAux cov
        (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x)
  rfl

private noncomputable def tangentFlatCotangentModelCLM
    (g : SmoothRiemannianMetric I M) (x : M) :
    E →L[Real] ContinuousMultilinearMap Real (fun _ : Fin 1 => E) Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun W =>
        (continuousMultilinearCurryFin1 Real E Real).symm
          (LinearMap.toContinuousLinearMap ((tangentFlatLinear (I := I) g x) W))
      map_add' := by
        intro W W'
        apply (continuousMultilinearCurryFin1 Real E Real).injective
        ext V
        change
          ((tangentFlatLinear (I := I) g x) (W + W')) V =
            (((tangentFlatLinear (I := I) g x) W) +
              ((tangentFlatLinear (I := I) g x) W')) V
        exact congrArg (fun L : Module.Dual Real (TangentSpace I x) => L V)
          ((tangentFlatLinear (I := I) g x).map_add W W')
      map_smul' := by
        intro c W
        apply (continuousMultilinearCurryFin1 Real E Real).injective
        ext V
        change
          ((tangentFlatLinear (I := I) g x) (c • W)) V =
            (c • ((tangentFlatLinear (I := I) g x) W)) V
        exact congrArg (fun L : Module.Dual Real (TangentSpace I x) => L V)
          ((tangentFlatLinear (I := I) g x).map_smul c W) }

@[simp] private theorem tangentFlatCotangentModelCLM_apply
    (g : SmoothRiemannianMetric I M) (x : M) (W : TangentSpace I x) :
    tangentFlatCotangentModelCLM (I := I) g x W =
      (continuousMultilinearCurryFin1 Real E Real).symm
        (LinearMap.toContinuousLinearMap ((tangentFlatLinear (I := I) g x) W)) := by
  simp [tangentFlatCotangentModelCLM]

/-- The lowered pointwise `(0,4)` Riemann curvature tensor. -/
noncomputable def riemannCurvature04At
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    Tensor04At (I := I) (M := M) x :=
  Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (ContinuousLinearMap.uncurryLeft
      (𝕜 := Real) (n := 3) (Ei := fun _ : Fin 4 => E) (G := Real)
      (((TensorRSSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (riemannCurvatureAt cov hcov x)).comp
        (tangentFlatCotangentModelCLM (I := I) g x)) :
        E →L[Real] ContinuousMultilinearMap Real (fun _ : Fin 3 => E) Real))

@[simp]
theorem riemannCurvature04At_apply_const
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) {x : M}
    (W X Y Z : TangentSpace I x) :
    riemannCurvature04At g cov hcov x (vec4 W X Y Z) =
      g.inner x W
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  change
    (ContinuousLinearMap.uncurryLeft
        (𝕜 := Real) (n := 3) (Ei := fun _ : Fin 4 => E) (G := Real)
        (((TensorRSSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (riemannCurvatureAt cov hcov x)).comp
          (tangentFlatCotangentModelCLM (I := I) g x)) :
          E →L[Real] ContinuousMultilinearMap Real (fun _ : Fin 3 => E) Real))
        (vec4 W X Y Z) =
      g.inner x W
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)
  rw [ContinuousLinearMap.uncurryLeft_apply]
  change
    riemannCurvatureAt cov hcov x
        (Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (tangentFlatCotangentModelCLM (I := I) g x W))
        (fun i : Fin 3 => vec4 W X Y Z i.succ) =
      g.inner x W
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)
  rw [show (fun i : Fin 3 => vec4 W X Y Z i.succ) = vec3 X Y Z by
    funext i
    fin_cases i <;> simp [vec3, vec4]]
  rw [riemannCurvatureAt_apply_const]
  rw [cotangentToDual_apply]
  change
    (tangentFlatCotangentModelCLM (I := I) g x W)
        (fun _ : Fin 1 =>
          riemannCurvatureAux cov
            (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
            (tangentConstAt (I := I) x Z) x) =
      g.inner x W
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)
  rw [tangentFlatCotangentModelCLM_apply]
  rfl

/-- The pointwise Ricci tensor, obtained by tracing the `(1,3)` tensor. -/
noncomputable def ricciCurvatureAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    Tensor02At (I := I) (M := M) x :=
  ricciFromRm13At (riemannCurvatureAt cov hcov x)

@[simp]
theorem ricciCurvatureAt_eq_trace
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    ricciCurvatureAt cov hcov x = ricciFromRm13At (riemannCurvatureAt cov hcov x) := rfl

/-- The lowered `(0,4)` tensor is evaluation of the metric on the `(1,3)` tensor. -/
theorem riemannCurvature04At_eq_lower_riemannCurvatureAt
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) {x : M}
    (W X Y Z : TangentSpace I x) :
    riemannCurvature04At g cov hcov x (vec4 W X Y Z) =
      riemannCurvatureAt cov hcov x (dualToCotangent ((tangentFlatLinear g x) W))
        (vec3 X Y Z) := by
  rw [riemannCurvature04At_apply_const, riemannCurvatureAt_apply_const]
  simp [tangentFlatLinear_apply]

end CovariantDerivative

end RicciFlower.Riemann

