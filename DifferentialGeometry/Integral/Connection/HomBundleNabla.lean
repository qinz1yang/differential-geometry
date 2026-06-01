import DifferentialGeometry.Realized.Realization.TensorNabla
import DifferentialGeometry.Realized.Realization.SmoothSections
import DifferentialGeometry.Realized.Realization.Connection
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

/-!
# Generic Hom-bundle covariant derivative on `Hom(U, V)`

Given two smooth vector bundles `U` and `V` over `M` (with model fibers `E_U` and `F`
respectively) equipped with covariant derivatives `cov_U : CovariantDerivative I E_U U`
and `cov_V : CovariantDerivative I F V`, this file constructs the induced covariant
derivative on the Hom-bundle
`Hom(U, V) = fun x => U x →L[ℝ] V x`.

This is the full generalization of `homBundleCovariantDerivative` (file `HomNabla.lean`)
to an arbitrary source bundle `U` (in place of the tangent bundle `TM`). The (r,s)-tensor
covariant derivative on `Hom(T_r M, T_s M)` is obtained as a specialization in
`TensorRSNabla.lean`.

## Main definition

* `homBundleCovariantDerivativeGen` : the induced `CovariantDerivative` on
  `fun x => U x →L[ℝ] V x`.

## Strategy

For a Hom-bundle section `τ : Π x : M, U x →L[ℝ] V x`, a vector field `V_field`
differentiable at `x`, and a `U`-section `Y` differentiable at `x`, the value
(a vector in the fiber `V x`)
```
Ψ(τ, V_field, Y)(x) :=
  cov_V (fun y => τ y (Y y)) x (V_field x) − τ x (cov_U Y x (V_field x))
```
is *tensorial* in BOTH `V_field` (the differentiation direction, of type `TangentSpace I`)
and `Y` (the `U`-section), at `x`. The `V_field`-tensoriality is automatic from continuous
linearity of both `cov_V (...) x` and `τ x ∘L cov_U Y x` in the tangent argument. The
`Y`-tensoriality is the standard product-rule cancellation using `cov_V`'s Leibniz rule
(with values in the `V` fiber) and `cov_U`'s Leibniz rule (on the `U` source).

By `TensorialAt.mkHom₂`, this gives a continuous bilinear map
`T_xM →L[ℝ] U x →L[ℝ] V x` representing `(∇^Hom_v τ)(w)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative

namespace HomConnectionGen

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  (E_U : Type*) [NormedAddCommGroup E_U] [NormedSpace ℝ E_U]
  [FiniteDimensional ℝ E_U] [CompleteSpace E_U]
  (U : M → Type*) [∀ x, AddCommGroup (U x)] [∀ x, Module ℝ (U x)]
  [∀ x, TopologicalSpace (U x)]
  [TopologicalSpace (TotalSpace E_U U)] [FiberBundle E_U U] [VectorBundle ℝ E_U U]
  [∀ x, IsTopologicalAddGroup (U x)] [∀ x, ContinuousSMul ℝ (U x)]
  [ContMDiffVectorBundle ∞ E_U U I]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [ContMDiffVectorBundle ∞ F V I]

/-- "τ is differentiable at x" for a Hom-bundle section `τ : Π x, U x →L V x`,
in total-space form. -/
private abbrev MDiffAtHom
    (τ : Π x : M, (U x →L[ℝ] V x)) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E_U →L[ℝ] F))
    (fun y => TotalSpace.mk' (E_U →L[ℝ] F)
      (E := fun x : M => (U x →L[ℝ] V x)) y (τ y)) x

/-- "Y is differentiable at x" for a section `Y` of the source bundle `U`,
in total-space form. -/
private abbrev MDiffAtU (Y : Π x : M, U x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E_U))
    (fun y => TotalSpace.mk' E_U (E := U) y (Y y)) x

/-- "σ is differentiable at x" for a section `σ` of the target bundle `V`,
in total-space form. -/
private abbrev MDiffAtV (σ : Π x : M, V x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, F))
    (fun y => TotalSpace.mk' F (E := V) y (σ y)) x

/-- Pairing `τ(Y)` is a differentiable section of `V` when `τ` and `Y` are differentiable.
This is the generic-source analog of `HomConnection.mdiffAt_apply`. -/
private theorem mdiffAt_apply
    {τ : Π x : M, (U x →L[ℝ] V x)}
    {Y : Π x : M, U x} {x : M}
    (hτ : MDiffAtHom I M E_U U F V τ x) (hY : MDiffAtU I M E_U U Y x) :
    MDiffAtV I M F V (fun y => τ y (Y y)) x := by
  exact MDifferentiableAt.clm_bundle_apply (b := id) hτ hY

/-- The raw V-valued operator
`Ψ(τ, V_field, Y)(x) := cov_V (τ·Y) x (V_field x) − τ x (cov_U Y x (V_field x))`. -/
private def Psi
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    (V_field : Π x : M, TangentSpace I x)
    (Y : Π x : M, U x) (x : M) : V x :=
  cov_V (fun y => τ y (Y y)) x (V_field x) - τ x (cov_U Y x (V_field x))

private theorem Psi_add_left
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {V_field V_field' : Π x : M, TangentSpace I x}
    {Y : Π x : M, U x} {x : M} :
    Psi I M E_U U F V cov_U cov_V τ (V_field + V_field') Y x =
      Psi I M E_U U F V cov_U cov_V τ V_field Y x +
        Psi I M E_U U F V cov_U cov_V τ V_field' Y x := by
  have h_add : (V_field + V_field' : Π x : M, TangentSpace I x) x = V_field x + V_field' x := rfl
  simp only [Psi, h_add, ContinuousLinearMap.map_add]
  abel

private theorem Psi_smul_left
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {f : M → ℝ} {V_field : Π x : M, TangentSpace I x}
    {Y : Π x : M, U x} {x : M} :
    Psi I M E_U U F V cov_U cov_V τ (f • V_field) Y x =
      f x • Psi I M E_U U F V cov_U cov_V τ V_field Y x := by
  have h_smul : (f • V_field : Π x : M, TangentSpace I x) x = f x • V_field x := rfl
  simp only [Psi, h_smul, ContinuousLinearMap.map_smul]
  rw [smul_sub]

private theorem Psi_add_right
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {V_field : Π x : M, TangentSpace I x}
    {Y Y' : Π x : M, U x} {x : M}
    (hτ : MDiffAtHom I M E_U U F V τ x)
    (hY : MDiffAtU I M E_U U Y x) (hY' : MDiffAtU I M E_U U Y' x) :
    Psi I M E_U U F V cov_U cov_V τ V_field (Y + Y') x =
      Psi I M E_U U F V cov_U cov_V τ V_field Y x +
        Psi I M E_U U F V cov_U cov_V τ V_field Y' x := by
  have hτY : MDiffAtV I M F V (fun y => τ y (Y y)) x := mdiffAt_apply I M E_U U F V hτ hY
  have hτY' : MDiffAtV I M F V (fun y => τ y (Y' y)) x := mdiffAt_apply I M E_U U F V hτ hY'
  have h_add_fun : (fun y => τ y ((Y + Y') y)) =
      (fun y => τ y (Y y)) + (fun y => τ y (Y' y)) := by
    funext y
    simp [Pi.add_apply, ContinuousLinearMap.map_add]
  have hY_T : MDiffAt (T% fun y => Y y) x := hY
  have hY'_T : MDiffAt (T% fun y => Y' y) x := hY'
  simp only [Psi]
  rw [h_add_fun, cov_V.isCovariantDerivativeOn.add hτY hτY']
  rw [show (Y + Y' : Π x : M, U x) = (fun x => Y x) + (fun x => Y' x) from rfl,
      cov_U.isCovariantDerivativeOn.add hY_T hY'_T]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
  abel

private theorem Psi_smul_right
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {V_field : Π x : M, TangentSpace I x}
    {Y : Π x : M, U x} {f : M → ℝ} {x : M}
    (hτ : MDiffAtHom I M E_U U F V τ x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hY : MDiffAtU I M E_U U Y x) :
    Psi I M E_U U F V cov_U cov_V τ V_field (f • Y) x =
      f x • Psi I M E_U U F V cov_U cov_V τ V_field Y x := by
  have hτY : MDiffAtV I M F V (fun y => τ y (Y y)) x := mdiffAt_apply I M E_U U F V hτ hY
  have h_fun : (fun y => τ y ((f • Y) y)) = f • (fun y => τ y (Y y)) := by
    funext y
    exact ContinuousLinearMap.map_smul (τ y) (f y) (Y y)
  have hY_T : MDiffAt (T% fun y => Y y) x := hY
  simp only [Psi]
  rw [h_fun]
  rw [cov_V.isCovariantDerivativeOn.leibniz hτY hf]
  rw [show (f • Y : Π x : M, U x) = f • (fun x => Y x) from rfl,
      cov_U.isCovariantDerivativeOn.leibniz hY_T hf]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
    ContinuousLinearMap.map_smul]
  rw [smul_sub]
  abel

/-- Tensoriality in V_field (left argument) at x — for any Y. -/
private theorem Psi_tensorialAt_left
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {x : M} (Y : Π x : M, U x) :
    TensorialAt I E (fun V_field => Psi I M E_U U F V cov_U cov_V τ V_field Y x) x where
  smul := fun _ _ => Psi_smul_left I M E_U U F V cov_U cov_V τ
  add := fun _ _ => Psi_add_left I M E_U U F V cov_U cov_V τ

/-- Tensoriality in Y (right argument) at x — when τ is differentiable at x. -/
private theorem Psi_tensorialAt_right
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {x : M} (hτ : MDiffAtHom I M E_U U F V τ x)
    (V_field : Π x : M, TangentSpace I x) :
    TensorialAt I E_U (fun Y => Psi I M E_U U F V cov_U cov_V τ V_field Y x) x where
  smul := fun hf hY => Psi_smul_right I M E_U U F V cov_U cov_V τ hτ hf hY
  add := fun hY hY' => Psi_add_right I M E_U U F V cov_U cov_V τ hτ hY hY'

private theorem hom_section_mdiff
    (τ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x => U x →L[ℝ] V x)⟯)
    (x : M) : MDiffAtHom I M E_U U F V (τ : Π x : M, (U x →L[ℝ] V x)) x :=
  τ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

private theorem u_section_mdiff
    (Y : Cₛ^∞⟮I; E_U, U⟯) (x : M) :
    MDiffAtU I M E_U U (Y : Π x : M, U x) x :=
  Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

private theorem vec_section_mdiff
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
  Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

/-- The generic Hom-bundle covariant derivative pointwise function. For each Hom-bundle section
`τ : Π x, U x →L[ℝ] V x` and point `x`, returns a CLM
`T_xM →L[ℝ] (U x →L[ℝ] V x)`.

If `τ` is differentiable at `x`, the value is the bilinear map built via `TensorialAt.mkHom₂`.
For non-differentiable τ, returns the junk value `0`. -/
noncomputable def homBundleCovariantDerivativeGenFun
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    (x : M) :
    TangentSpace I x →L[ℝ] (U x →L[ℝ] V x) := by
  classical
  by_cases hτ : MDiffAtHom I M E_U U F V τ x
  · exact TensorialAt.mkHom₂ (F := E) (F' := E_U)
      (V := (TangentSpace I : M → Type _)) (V' := U)
      (A := V x)
      (fun V_field Y => Psi I M E_U U F V cov_U cov_V τ V_field Y x) x
      (fun Y _ => Psi_tensorialAt_left I M E_U U F V cov_U cov_V τ Y)
      (fun V_field _ => Psi_tensorialAt_right I M E_U U F V cov_U cov_V τ hτ V_field)
  · exact 0

/-- Specification: when `τ`, `V_field`, `Y` are all differentiable at `x`, the generic Hom-bundle
covariant derivative applied bilinearly to `V_field x` and `Y x` returns
`Psi cov_U cov_V τ V_field Y x`. -/
private theorem homBundleCovariantDerivativeGenFun_apply
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {x : M} (hτ : MDiffAtHom I M E_U U F V τ x)
    {V_field : Π x : M, TangentSpace I x}
    {Y : Π x : M, U x}
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (V_field y)) x)
    (hY : MDiffAtU I M E_U U Y x) :
    homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x (V_field x) (Y x) =
      Psi I M E_U U F V cov_U cov_V τ V_field Y x := by
  unfold homBundleCovariantDerivativeGenFun
  rw [dif_pos hτ]
  exact TensorialAt.mkHom₂_apply
    (Φ := fun V_field Y => Psi I M E_U U F V cov_U cov_V τ V_field Y x)
    (fun Y _ => Psi_tensorialAt_left I M E_U U F V cov_U cov_V τ Y)
    (fun V_field _ => Psi_tensorialAt_right I M E_U U F V cov_U cov_V τ hτ V_field) hV hY

/-- Junk: when τ is not differentiable at x, the generic Hom-bundle covariant derivative is zero. -/
private theorem homBundleCovariantDerivativeGenFun_of_not_mdiff
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {x : M} (hτ : ¬ MDiffAtHom I M E_U U F V τ x) :
    homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x = 0 := by
  unfold homBundleCovariantDerivativeGenFun
  rw [dif_neg hτ]

/-- The generic Hom-bundle covariant derivative satisfies `IsCovariantDerivativeOn`
on `Set.univ`. -/
private theorem homBundleCovariantDerivativeGenFun_isCovOn
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V) :
    IsCovariantDerivativeOn (E_U →L[ℝ] F)
      (homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V) Set.univ where
  add := by
    intro τ₁ τ₂ x hτ₁ hτ₂ _hx
    have hτ₁' : MDiffAtHom I M E_U U F V τ₁ x := hτ₁
    have hτ₂' : MDiffAtHom I M E_U U F V τ₂ x := hτ₂
    have hτ_sum : MDiffAtHom I M E_U U F V (τ₁ + τ₂) x :=
      mdifferentiableAt_add_section (F := E_U →L[ℝ] F) hτ₁ hτ₂
    ext v w
    obtain ⟨V_field, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E_U)
      (V := U) (n := (⊤ : ℕ∞)) x w
    have hV_diff := vec_section_mdiff I M V_field x
    have hY_diff := u_section_mdiff I M E_U U Y x
    rw [show (v : TangentSpace I x) = (V_field : Π x : M, TangentSpace I x) x from hVx.symm]
    rw [show (w : U x) = (Y : Π x : M, U x) x from hYx.symm]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    rw [homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V (τ₁ + τ₂)
      hτ_sum hV_diff hY_diff]
    rw [homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V τ₁
      hτ₁' hV_diff hY_diff]
    rw [homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V τ₂
      hτ₂' hV_diff hY_diff]
    have h_funeq : (fun y => (τ₁ + τ₂) y (Y y)) =
        (fun y => τ₁ y (Y y)) + (fun y => τ₂ y (Y y)) := by
      funext y
      simp [Pi.add_apply, ContinuousLinearMap.add_apply]
    have hτ₁Y : MDiffAtV I M F V (fun y => τ₁ y (Y y)) x :=
      mdiffAt_apply I M E_U U F V hτ₁' hY_diff
    have hτ₂Y : MDiffAtV I M F V (fun y => τ₂ y (Y y)) x :=
      mdiffAt_apply I M E_U U F V hτ₂' hY_diff
    simp only [Psi]
    rw [h_funeq, cov_V.isCovariantDerivativeOn.add hτ₁Y hτ₂Y]
    simp only [ContinuousLinearMap.add_apply, Pi.add_apply]
    abel
  leibniz := by
    intro τ g x hτ hg _hx
    have hτ' : MDiffAtHom I M E_U U F V τ x := hτ
    have hgτ : MDiffAtHom I M E_U U F V (g • τ) x :=
      hg.smul_section (F := E_U →L[ℝ] F) hτ
    ext v w
    obtain ⟨V_field, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E_U)
      (V := U) (n := (⊤ : ℕ∞)) x w
    have hV_diff := vec_section_mdiff I M V_field x
    have hY_diff := u_section_mdiff I M E_U U Y x
    rw [show (v : TangentSpace I x) = (V_field : Π x : M, TangentSpace I x) x from hVx.symm]
    rw [show (w : U x) = (Y : Π x : M, U x) x from hYx.symm]
    rw [homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V (g • τ)
      hgτ hV_diff hY_diff]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V τ
      hτ' hV_diff hY_diff]
    have h_funeq : (fun y => (g • τ) y (Y y)) = g • (fun y => τ y (Y y)) := by
      funext y
      rfl
    have hτY : MDiffAtV I M F V (fun y => τ y (Y y)) x :=
      mdiffAt_apply I M E_U U F V hτ' hY_diff
    simp only [Psi]
    rw [h_funeq]
    rw [cov_V.isCovariantDerivativeOn.leibniz hτY hg]
    have hgτ_apply : (g • τ) x = g x • τ x := rfl
    rw [hgτ_apply]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [smul_sub]
    abel

/-- The generic Hom-bundle covariant derivative on `Hom(U, V)`, packaged as a
`CovariantDerivative`. -/
noncomputable def homBundleCovariantDerivativeGen
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V) :
    CovariantDerivative I (E_U →L[ℝ] F)
      (fun x => U x →L[ℝ] V x) where
  toFun := homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V
  isCovariantDerivativeOnUniv :=
    homBundleCovariantDerivativeGenFun_isCovOn I M E_U U F V cov_U cov_V

/-- Public function-level apply: when `τ`, `V_field`, `Y` are all
manifold-differentiable at `x` (in total-space form), the value of
`homBundleCovariantDerivativeGen` applied bilinearly to `V_field x` and `Y x`
equals the product-rule expression
`cov_V (fun y => τ y (Y y)) x (V_field x) − τ x (cov_U Y x (V_field x))`. -/
theorem homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {x : M}
    (hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U →L[ℝ] F))
      (fun y : M => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun x : M => (U x →L[ℝ] V x)) y (τ y)) x)
    {V_field : Π x : M, TangentSpace I x}
    {Y : Π x : M, U x}
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (V_field y)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U))
      (fun y => TotalSpace.mk' E_U (E := U) y (Y y)) x) :
    (homBundleCovariantDerivativeGen I M E_U U F V cov_U cov_V τ x (V_field x)) (Y x) =
      cov_V (fun y => τ y (Y y)) x (V_field x) - τ x (cov_U Y x (V_field x)) := by
  change homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x
      (V_field x) (Y x) = _
  exact homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V τ
    hτ hV hY

/-- For a smooth Hom-bundle section τ and a smooth `U`-section Y, the V-valued section
`y ↦ ⟨y, τ y (Y y)⟩` is smooth. This is the generic-source analog of
`HomConnection.contMDiff_hom_apply_section`. -/
private theorem contMDiff_hom_apply_section
    (τ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x => U x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E_U, U⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun y => TotalSpace.mk' F (E := V) y (τ y (Y y))) :=
  ContMDiff.clm_bundle_apply (b := id) τ.contMDiff Y.contMDiff

/-- For smooth `Y ∈ Γ(TM)` and smooth `Z ∈ Γ(U)`, the `U`-valued section
`x ↦ cov_U Z x (Y x)` is smooth. -/
private theorem contMDiff_cov_U_apply_section
    (cov_U : CovariantDerivative I E_U U)
    [ContMDiffCovariantDerivative cov_U ∞]
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Z : Cₛ^∞⟮I; E_U, U⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E_U)) ∞
      (fun x => TotalSpace.mk' E_U (E := U) x (cov_U Z x (Y x))) := by
  have hZ_plus : ContMDiff I (I.prod 𝓘(ℝ, E_U)) (∞ + 1) (T% fun x => Z x) := by
    rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]
    exact Z.contMDiff
  have hcov_U_smooth :=
    (‹ContMDiffCovariantDerivative cov_U ∞›).contMDiff.contMDiff hZ_plus.contMDiffOn
  have hcov_U_global : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E_U)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E_U)
        (E := fun x : M => TangentSpace I x →L[ℝ] U x) x (cov_U Z x)) := by
    rwa [← contMDiffOn_univ]
  exact ContMDiff.clm_bundle_apply (b := id) hcov_U_global Y.contMDiff

/-- For smooth τ (Hom(U, V)-section) and smooth Y (TM-section), the `Hom(U, V)`-section
`x ↦ (homBundleCovariantDerivativeGenFun cov_U cov_V τ x)(Y x)` is smooth.

This is the generic-source analog of `HomConnection.homBundleCov_section_smooth`. -/
private theorem homBundleCovGen_section_smooth
    (cov_U : CovariantDerivative I E_U U)
    [ContMDiffCovariantDerivative cov_U ∞]
    (cov_V : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov_V ∞]
    (τ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x => U x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E_U →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun x : M => (U x →L[ℝ] V x))
        x ((homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x) (Y x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := U) (V₂ := V)
    (φ := fun x => (homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x) (Y x))
  intro Z
  have hτZ_section : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun y => TotalSpace.mk' F (E := V) y (τ y (Z y))) :=
    contMDiff_hom_apply_section I M E_U U F V τ Z
  let τZ : Cₛ^∞⟮I; F, V⟯ := ⟨fun y => τ y (Z y), hτZ_section⟩
  have hcov_V_τZ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] F)
        (E := fun x : M => (TangentSpace I x →L[ℝ] V x)) x (cov_V τZ x)) := by
    have hτZ_plus : ContMDiff I (I.prod 𝓘(ℝ, F)) (∞ + 1) (T% fun x => τZ x) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]
      exact τZ.contMDiff
    have hcov_V_smooth :=
      (‹ContMDiffCovariantDerivative cov_V ∞›).contMDiff.contMDiff hτZ_plus.contMDiffOn
    rwa [← contMDiffOn_univ]
  have h_first : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F (E := V) x (cov_V τZ x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id) hcov_V_τZ Y.contMDiff
  have h_covUZY : ContMDiff I (I.prod 𝓘(ℝ, E_U)) ∞
      (fun x => TotalSpace.mk' E_U (E := U) x (cov_U Z x (Y x))) :=
    contMDiff_cov_U_apply_section I M E_U U cov_U Y Z
  have h_second : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F (E := V) x (τ x (cov_U Z x (Y x)))) :=
    ContMDiff.clm_bundle_apply (b := id) τ.contMDiff h_covUZY
  have h_eq : ∀ x,
      (homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x) (Y x) (Z x) =
      cov_V τZ x (Y x) - τ x (cov_U Z x (Y x)) := by
    intro x
    have hτ_diff := hom_section_mdiff I M E_U U F V τ x
    have hY_diff := vec_section_mdiff I M Y x
    have hZ_diff := u_section_mdiff I M E_U U Z x
    rw [homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V τ
      hτ_diff hY_diff hZ_diff]
    rfl
  have h_diff : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F (E := V) x
        (cov_V τZ x (Y x) - τ x (cov_U Z x (Y x)))) := by
    let s₁ : Cₛ^∞⟮I; F, V⟯ := ⟨fun x => cov_V τZ x (Y x), h_first⟩
    let s₂ : Cₛ^∞⟮I; F, V⟯ := ⟨fun x => τ x (cov_U Z x (Y x)), h_second⟩
    have : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
        (fun x => TotalSpace.mk' F (E := V) x ((s₁ - s₂) x)) := (s₁ - s₂).contMDiff
    convert this using 1
  intro x₀
  rw [contMDiffAt_section]
  have h_diff_at := h_diff x₀
  rw [contMDiffAt_section] at h_diff_at
  refine h_diff_at.congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [h_eq]

/-- The generic Hom-bundle covariant derivative on `Hom(U, V)` is `C^∞`, provided both
`cov_U` and `cov_V` are `C^∞`. -/
noncomputable instance homBundleCovariantDerivativeGen_contMDiff
    (cov_U : CovariantDerivative I E_U U)
    [ContMDiffCovariantDerivative cov_U ∞]
    (cov_V : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov_V ∞] :
    ContMDiffCovariantDerivative
      (homBundleCovariantDerivativeGen I M E_U U F V cov_U cov_V) ∞ where
  contMDiff := {
    contMDiff := by
      intro τ hτ
      have hτ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E_U →L[ℝ] F)) ∞
          (fun x => TotalSpace.mk' (E_U →L[ℝ] F)
            (E := fun x : M => (U x →L[ℝ] V x)) x (τ x)) := by
        rw [show (∞ : WithTop ℕ∞) = ∞ + 1 from by simp] at hτ
        rwa [← contMDiffOn_univ]
      let τ_section : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x => U x →L[ℝ] V x)⟯ :=
        ⟨τ, hτ_smooth⟩
      rw [contMDiffOn_univ]
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (V₁ := TangentSpace I)
        (V₂ := fun x => U x →L[ℝ] V x)
        (φ := fun x => homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x)
      intro Y
      exact homBundleCovGen_section_smooth I M E_U U F V cov_U cov_V τ_section Y
  }

/-- Pointwise characterization: when `τ` is a smooth Hom-bundle section and `Y` a smooth
`U`-section, the generic Hom-bundle covariant derivative applied bilinearly to
`v ∈ T_xM` and `Y x ∈ U x` has the value
`cov_V (fun y => τ y (Y y)) x v − τ x (cov_U Y x v)`,
i.e. the standard product-rule formula `(∇^Hom_v τ)(Y x) = ∇^V_v(τ(Y)) − τ(∇^U_v Y)`. -/
theorem homBundleCovariantDerivativeGen_apply
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x => U x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E_U, U⟯) (x : M) (v : TangentSpace I x) :
    (homBundleCovariantDerivativeGen I M E_U U F V cov_U cov_V τ x v) (Y x) =
      cov_V (fun y => τ y (Y y)) x v - τ x (cov_U Y x v) := by
  change homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x v (Y x) = _
  obtain ⟨V_field, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hτ_diff := hom_section_mdiff I M E_U U F V τ x
  have hV_diff := vec_section_mdiff I M V_field x
  have hY_diff := u_section_mdiff I M E_U U Y x
  rw [show v = (V_field : Π x : M, TangentSpace I x) x from hVx.symm]
  rw [homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V τ
    hτ_diff hV_diff hY_diff]
  rfl

end HomConnectionGen

end
