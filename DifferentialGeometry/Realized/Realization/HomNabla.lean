import DifferentialGeometry.Realized.Realization.TensorNabla
import DifferentialGeometry.Realized.Realization.SmoothSections
import DifferentialGeometry.Realized.Realization.Connection
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

/-!
# Hom-bundle covariant derivative on `Hom(TM, V)`

Given a `CovariantDerivative cov_TM` on `TM` and a `CovariantDerivative cov_V` on a second
smooth vector bundle `V`, this file constructs the induced covariant derivative on the
Hom-bundle `Hom(TM, V) = fun x => TangentSpace I x →L[ℝ] V x`.

This is the generalization of `dualCovariantDerivative` (file `TensorNabla.lean`) to an
arbitrary target bundle `V` (in place of the trivial bundle `Bundle.Trivial M ℝ`).

## Main definition

* `homBundleCovariantDerivative` : the induced `CovariantDerivative` on
  `fun x => TangentSpace I x →L[ℝ] V x`.

## Strategy

For a Hom-bundle section `τ : Π x, TangentSpace I x →L[ℝ] V x` and vector fields `V_field`,
`Y` differentiable at `x`, the value (a vector in the fiber `V x`)
```
Ψ(τ, V_field, Y)(x) := cov_V (fun y => τ y (Y y)) x (V_field x) − τ x (cov_TM Y x (V_field x))
```
is *tensorial* in BOTH `V_field` and `Y` at `x`. The `V_field`-tensoriality is automatic
because both `cov_V (...) x` and `τ x ∘L cov_TM Y x` are continuous linear maps from
`T_xM` into `V x`. The `Y`-tensoriality is the standard product-rule cancellation,
this time using `cov_V`'s Leibniz rule with values in `V x`.

By `TensorialAt.mkHom₂`, this gives a continuous bilinear map
`T_xM →L[ℝ] T_xM →L[ℝ] V x` representing `(∇^Hom_v τ)(w)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative

namespace HomConnection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  -- The target bundle V with model fiber F (both explicit so typeclass resolution can match
  -- F to V uniquely throughout the file).
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [ContMDiffVectorBundle ∞ F V I]

/-! ### Abbreviations for differentiability of Hom-bundle and vector fields. -/

/-- "τ is differentiable at x" for a Hom-bundle section `τ`, in total-space form. -/
private abbrev MDiffAtHom
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x)) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] F))
    (fun y => TotalSpace.mk' (E →L[ℝ] F)
      (E := fun x : M => (TangentSpace I x →L[ℝ] V x)) y (τ y)) x

/-- "Y is differentiable at x" for a vector field Y, in total-space form. -/
private abbrev MDiffAtVec
    (Y : Π x : M, TangentSpace I x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E))
    (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x

/-- "σ is differentiable at x" for a section of `V`, in total-space form. -/
private abbrev MDiffAtV (σ : Π x : M, V x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, F))
    (fun y => TotalSpace.mk' F (E := V) y (σ y)) x

/-- Pairing `τ(Y)` is a differentiable section of `V` when `τ` and `Y` are differentiable.
This is the V-valued generalization of `mdiffAt_pairing`. -/
private theorem mdiffAt_apply
    {τ : Π x : M, (TangentSpace I x →L[ℝ] V x)}
    {Y : Π x : M, TangentSpace I x} {x : M}
    (hτ : MDiffAtHom I M F V τ x) (hY : MDiffAtVec I M Y x) :
    MDiffAtV I M F V (fun y => τ y (Y y)) x := by
  exact MDifferentiableAt.clm_bundle_apply (b := id) hτ hY

/-! ### The raw V-valued operator -/

/-- The raw V-valued operator
`Ψ(τ, V_field, Y)(x) := cov_V (τ·Y) x (V_field x) − τ x (cov_TM Y x (V_field x))`. -/
private def Psi
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    (V_field Y : Π x : M, TangentSpace I x) (x : M) : V x :=
  cov_V (fun y => τ y (Y y)) x (V_field x) - τ x (cov_TM Y x (V_field x))

/-! ### Tensoriality in V_field (the differentiation direction): automatic from CLM linearity. -/

private theorem Psi_add_left
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {V_field V_field' Y : Π x : M, TangentSpace I x} {x : M} :
    Psi I M F V cov_TM cov_V τ (V_field + V_field') Y x =
      Psi I M F V cov_TM cov_V τ V_field Y x + Psi I M F V cov_TM cov_V τ V_field' Y x := by
  have h_add : (V_field + V_field' : Π x : M, TangentSpace I x) x = V_field x + V_field' x := rfl
  simp only [Psi, h_add, ContinuousLinearMap.map_add]
  abel

private theorem Psi_smul_left
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {f : M → ℝ} {V_field Y : Π x : M, TangentSpace I x} {x : M} :
    Psi I M F V cov_TM cov_V τ (f • V_field) Y x = f x • Psi I M F V cov_TM cov_V τ V_field Y x := by
  have h_smul : (f • V_field : Π x : M, TangentSpace I x) x = f x • V_field x := rfl
  simp only [Psi, h_smul, ContinuousLinearMap.map_smul]
  rw [smul_sub]

/-! ### Tensoriality in Y (the input to the resulting Hom): the product-rule cancellation. -/

private theorem Psi_add_right
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {V_field Y Y' : Π x : M, TangentSpace I x} {x : M}
    (hτ : MDiffAtHom I M F V τ x)
    (hY : MDiffAtVec I M Y x) (hY' : MDiffAtVec I M Y' x) :
    Psi I M F V cov_TM cov_V τ V_field (Y + Y') x =
      Psi I M F V cov_TM cov_V τ V_field Y x + Psi I M F V cov_TM cov_V τ V_field Y' x := by
  -- Show V-valued differentiability of the pairings τ·Y and τ·Y'.
  have hτY : MDiffAtV I M F V (fun y => τ y (Y y)) x := mdiffAt_apply I M F V hτ hY
  have hτY' : MDiffAtV I M F V (fun y => τ y (Y' y)) x := mdiffAt_apply I M F V hτ hY'
  have h_add_fun : (fun y => τ y ((Y + Y') y)) =
      (fun y => τ y (Y y)) + (fun y => τ y (Y' y)) := by
    funext y
    simp [Pi.add_apply, ContinuousLinearMap.map_add]
  have hY_T : MDiffAt (T% fun y => Y y) x := hY
  have hY'_T : MDiffAt (T% fun y => Y' y) x := hY'
  simp only [Psi]
  -- cov_V is additive in the section argument; use `IsCovariantDerivativeOn.add`.
  rw [h_add_fun, cov_V.isCovariantDerivativeOn.add hτY hτY']
  rw [show (Y + Y' : Π x : M, TangentSpace I x) = (fun x => Y x) + (fun x => Y' x) from rfl,
      cov_TM.isCovariantDerivativeOn.add hY_T hY'_T]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
  abel

private theorem Psi_smul_right
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {V_field Y : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M}
    (hτ : MDiffAtHom I M F V τ x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hY : MDiffAtVec I M Y x) :
    Psi I M F V cov_TM cov_V τ V_field (f • Y) x = f x • Psi I M F V cov_TM cov_V τ V_field Y x := by
  have hτY : MDiffAtV I M F V (fun y => τ y (Y y)) x := mdiffAt_apply I M F V hτ hY
  -- Recall (f • Y) y = f y • Y y, so τ y ((f • Y) y) = f y • τ y (Y y) by CLM-linearity.
  have h_fun : (fun y => τ y ((f • Y) y)) = f • (fun y => τ y (Y y)) := by
    funext y
    exact ContinuousLinearMap.map_smul (τ y) (f y) (Y y)
  have hY_T : MDiffAt (T% fun y => Y y) x := hY
  simp only [Psi]
  rw [h_fun]
  -- Apply cov_V's Leibniz rule for V-valued sections: cov_V (f • s) x = f x • cov_V s x +
  --                                                  (extDerivFun f x).smulRight (s x).
  rw [cov_V.isCovariantDerivativeOn.leibniz hτY hf]
  -- Apply cov_TM's Leibniz rule for the TM section.
  rw [show (f • Y : Π x : M, TangentSpace I x) = f • (fun x => Y x) from rfl,
      cov_TM.isCovariantDerivativeOn.leibniz hY_T hf]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
    ContinuousLinearMap.map_smul]
  -- Goal: f x • cov_V (τY) x V_field + extDerivFun f x V_field • τ x (Y x) -
  --       (f x • τ x (cov_TM Y x V_field) + extDerivFun f x V_field • τ x (Y x)) =
  --       f x • (cov_V (τY) x V_field - τ x (cov_TM Y x V_field))
  -- The mixed terms cancel.
  rw [smul_sub]
  -- Now: a + b - (c + d) = (a - c) where a, b are first/second smulRight, etc.
  -- (a + b) - (c + d) where b = d. We need to rearrange.
  abel

/-! ### Bilinear tensoriality of `Psi cov_TM cov_V τ V_field Y x` -/

/-- Tensoriality in V_field (left argument) at x — for any Y. -/
private theorem Psi_tensorialAt_left
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {x : M} (Y : Π x : M, TangentSpace I x) :
    TensorialAt I E (fun V_field => Psi I M F V cov_TM cov_V τ V_field Y x) x where
  smul := fun _ _ => Psi_smul_left I M F V cov_TM cov_V τ
  add := fun _ _ => Psi_add_left I M F V cov_TM cov_V τ

/-- Tensoriality in Y (right argument) at x — when τ is differentiable at x. -/
private theorem Psi_tensorialAt_right
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {x : M} (hτ : MDiffAtHom I M F V τ x) (V_field : Π x : M, TangentSpace I x) :
    TensorialAt I E (fun Y => Psi I M F V cov_TM cov_V τ V_field Y x) x where
  smul := fun hf hY => Psi_smul_right I M F V cov_TM cov_V τ hτ hf hY
  add := fun hY hY' => Psi_add_right I M F V cov_TM cov_V τ hτ hY hY'

/-! ### The Hom-bundle covariant derivative -/

private theorem hom_section_mdiff
    (τ : Cₛ^∞⟮I; E →L[ℝ] F, (fun x => TangentSpace I x →L[ℝ] V x)⟯)
    (x : M) : MDiffAtHom I M F V (τ : Π x : M, (TangentSpace I x →L[ℝ] V x)) x :=
  τ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

private theorem vec_section_mdiff
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
  Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

/-- The Hom-bundle covariant derivative pointwise function. For each Hom-bundle section
`τ : Π x, TangentSpace I x →L[ℝ] V x` and point `x`, returns a CLM
`T_xM →L[ℝ] (T_xM →L[ℝ] V x)`.

If `τ` is differentiable at `x`, the value is the bilinear map built via `TensorialAt.mkHom₂`.
For non-differentiable τ, returns the junk value `0`. -/
noncomputable def homBundleCovariantDerivativeFun
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] V x) := by
  classical
  by_cases hτ : MDiffAtHom I M F V τ x
  · exact TensorialAt.mkHom₂ (F := E) (F' := E)
      (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
      (A := V x)
      (fun V_field Y => Psi I M F V cov_TM cov_V τ V_field Y x) x
      (fun Y _ => Psi_tensorialAt_left I M F V cov_TM cov_V τ Y)
      (fun V_field _ => Psi_tensorialAt_right I M F V cov_TM cov_V τ hτ V_field)
  · exact 0

/-- Specification: when `τ`, `V_field`, `Y` are all differentiable at `x`, the Hom-bundle
covariant derivative applied bilinearly to `V_field x` and `Y x` returns
`Psi cov_TM cov_V τ V_field Y x`. -/
theorem homBundleCovariantDerivativeFun_apply
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {x : M} (hτ : MDiffAtHom I M F V τ x)
    {V_field Y : Π x : M, TangentSpace I x}
    (hV : MDiffAtVec I M V_field x) (hY : MDiffAtVec I M Y x) :
    homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x (V_field x) (Y x) =
      Psi I M F V cov_TM cov_V τ V_field Y x := by
  unfold homBundleCovariantDerivativeFun
  rw [dif_pos hτ]
  exact TensorialAt.mkHom₂_apply
    (Φ := fun V_field Y => Psi I M F V cov_TM cov_V τ V_field Y x)
    (fun Y _ => Psi_tensorialAt_left I M F V cov_TM cov_V τ Y)
    (fun V_field _ => Psi_tensorialAt_right I M F V cov_TM cov_V τ hτ V_field) hV hY

/-- Unfolded specification: when `τ`, `V_field`, `Y` are all differentiable at `x`, the
Hom-bundle covariant derivative applied bilinearly to `V_field x` and `Y x` equals the
explicit product-rule difference
`cov_V (τ·Y) x (V_field x) − τ x (cov_TM Y x (V_field x))`. -/
theorem homBundleCovariantDerivativeFun_apply_eq
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {x : M} (hτ : MDiffAtHom I M F V τ x)
    {V_field Y : Π x : M, TangentSpace I x}
    (hV : MDiffAtVec I M V_field x) (hY : MDiffAtVec I M Y x) :
    homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x (V_field x) (Y x) =
      cov_V (fun y => τ y (Y y)) x (V_field x) - τ x (cov_TM Y x (V_field x)) := by
  rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V τ hτ hV hY]
  rfl

/-- Junk: when τ is not differentiable at x, the Hom-bundle covariant derivative is zero. -/
private theorem homBundleCovariantDerivativeFun_of_not_mdiff
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {x : M} (hτ : ¬ MDiffAtHom I M F V τ x) :
    homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x = 0 := by
  unfold homBundleCovariantDerivativeFun
  rw [dif_neg hτ]

/-! ### IsCovariantDerivativeOn -/

/-- The Hom-bundle covariant derivative satisfies `IsCovariantDerivativeOn` on `Set.univ`. -/
private theorem homBundleCovariantDerivativeFun_isCovOn
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V) :
    IsCovariantDerivativeOn (E →L[ℝ] F)
      (homBundleCovariantDerivativeFun I M F V cov_TM cov_V) Set.univ where
  add := by
    intro τ₁ τ₂ x hτ₁ hτ₂ _hx
    have hτ₁' : MDiffAtHom I M F V τ₁ x := hτ₁
    have hτ₂' : MDiffAtHom I M F V τ₂ x := hτ₂
    have hτ_sum : MDiffAtHom I M F V (τ₁ + τ₂) x :=
      mdifferentiableAt_add_section (F := E →L[ℝ] F) hτ₁ hτ₂
    ext v w
    obtain ⟨V_field, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
    have hV_diff : MDiffAtVec I M (V_field : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M V_field x
    have hY_diff : MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M Y x
    rw [show (v : TangentSpace I x) = (V_field : Π x : M, TangentSpace I x) x from hVx.symm]
    rw [show (w : TangentSpace I x) = (Y : Π x : M, TangentSpace I x) x from hYx.symm]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V (τ₁ + τ₂) hτ_sum hV_diff hY_diff]
    rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V τ₁ hτ₁' hV_diff hY_diff]
    rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V τ₂ hτ₂' hV_diff hY_diff]
    -- Goal: Psi (τ₁+τ₂) V_field Y x = Psi τ₁ V_field Y x + Psi τ₂ V_field Y x
    have h_funeq : (fun y => (τ₁ + τ₂) y (Y y)) =
        (fun y => τ₁ y (Y y)) + (fun y => τ₂ y (Y y)) := by
      funext y
      simp [Pi.add_apply, ContinuousLinearMap.add_apply]
    have hτ₁Y : MDiffAtV I M F V (fun y => τ₁ y (Y y)) x :=
      mdiffAt_apply I M F V hτ₁' hY_diff
    have hτ₂Y : MDiffAtV I M F V (fun y => τ₂ y (Y y)) x :=
      mdiffAt_apply I M F V hτ₂' hY_diff
    simp only [Psi]
    rw [h_funeq, cov_V.isCovariantDerivativeOn.add hτ₁Y hτ₂Y]
    simp only [ContinuousLinearMap.add_apply, Pi.add_apply]
    abel
  leibniz := by
    intro τ g x hτ hg _hx
    have hτ' : MDiffAtHom I M F V τ x := hτ
    have hgτ : MDiffAtHom I M F V (g • τ) x :=
      hg.smul_section (F := E →L[ℝ] F) hτ
    ext v w
    obtain ⟨V_field, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
    have hV_diff : MDiffAtVec I M (V_field : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M V_field x
    have hY_diff : MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M Y x
    rw [show (v : TangentSpace I x) = (V_field : Π x : M, TangentSpace I x) x from hVx.symm]
    rw [show (w : TangentSpace I x) = (Y : Π x : M, TangentSpace I x) x from hYx.symm]
    rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V (g • τ) hgτ hV_diff hY_diff]
    -- After distributing CLM-application on the RHS.
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V τ hτ' hV_diff hY_diff]
    -- Goal:
    --   Psi (g • τ) V_field Y x =
    --   g x • Psi τ V_field Y x + (extDerivFun g x V_field) • τ x (Y x)
    have h_funeq : (fun y => (g • τ) y (Y y)) = g • (fun y => τ y (Y y)) := by
      funext y
      rfl
    have hτY : MDiffAtV I M F V (fun y => τ y (Y y)) x :=
      mdiffAt_apply I M F V hτ' hY_diff
    simp only [Psi]
    rw [h_funeq]
    rw [cov_V.isCovariantDerivativeOn.leibniz hτY hg]
    have hgτ_apply : (g • τ) x = g x • τ x := rfl
    rw [hgτ_apply]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [smul_sub]
    abel

/-! ### The bundled `CovariantDerivative` -/

/-- The Hom-bundle covariant derivative on `Hom(TM, V)`, packaged as a `CovariantDerivative`. -/
noncomputable def homBundleCovariantDerivative
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V) :
    CovariantDerivative I (E →L[ℝ] F)
      (fun x => TangentSpace I x →L[ℝ] V x) where
  toFun := homBundleCovariantDerivativeFun I M F V cov_TM cov_V
  isCovariantDerivativeOnUniv := homBundleCovariantDerivativeFun_isCovOn I M F V cov_TM cov_V

/-! ### ContMDiffCovariantDerivative instance (smoothness) -/

/-- For a smooth Hom-bundle section τ and a smooth vector field Y, the V-valued section
`y ↦ ⟨y, τ y (Y y)⟩` is smooth. This is the V-valued analog of `contMDiff_dual_apply_section`.
-/
private theorem contMDiff_hom_apply_section
    (τ : Cₛ^∞⟮I; E →L[ℝ] F, (fun x => TangentSpace I x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun y => TotalSpace.mk' F (E := V) y (τ y (Y y))) := by
  exact ContMDiff.clm_bundle_apply (b := id) τ.contMDiff Y.contMDiff

/-- For smooth τ and smooth Y, the section `x ↦ ⟨x, (homBundleCovFun cov_TM cov_V τ x)(Y x)⟩`
of V is smooth. This is the V-valued generalization of `dualCov_section_smooth`. -/
private theorem homBundleCov_section_smooth
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov_TM ∞]
    (cov_V : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov_V ∞]
    (τ : Cₛ^∞⟮I; E →L[ℝ] F, (fun x => TangentSpace I x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] F)
        (E := fun x : M => (TangentSpace I x →L[ℝ] V x))
        x ((homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x) (Y x))) := by
  -- Apply the bridge: the section is smooth iff for every smooth Z of TM,
  -- the V-valued section x ↦ ⟨x, (homBundleCov ... τ x)(Y x)(Z x)⟩ is smooth.
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I) (V₂ := V)
    (φ := fun x => (homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x) (Y x))
  intro Z
  -- For each smooth Z, the value `(homBundleCov ... τ x)(Y x)(Z x)` equals
  -- `cov_V (τ·Z) x (Y x) − τ x (cov_TM Z x (Y x))`.
  -- 1. cov_V (τ·Z) is a smooth Hom(TM, V) section, applied at smooth Y gives smooth V section.
  -- 2. cov_TM Z is a smooth Hom(TM, TM) section, applied at smooth Y gives smooth TM section,
  --    then τ applied gives smooth V section.
  -- The smooth V-valued section τ·Z = fun y => τ y (Z y).
  have hτZ_section : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun y => TotalSpace.mk' F (E := V) y (τ y (Z y))) :=
    contMDiff_hom_apply_section I M F V τ Z
  let τZ : Cₛ^∞⟮I; F, V⟯ := ⟨fun y => τ y (Z y), hτZ_section⟩
  -- cov_V applied to a smooth section is smooth.
  have hcov_V_τZ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] F)
        (E := fun x : M => (TangentSpace I x →L[ℝ] V x)) x (cov_V τZ x)) := by
    have hτZ_plus : ContMDiff I (I.prod 𝓘(ℝ, F)) (∞ + 1) (T% fun x => τZ x) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]
      exact τZ.contMDiff
    have hcov_V_smooth :=
      (‹ContMDiffCovariantDerivative cov_V ∞›).contMDiff.contMDiff hτZ_plus.contMDiffOn
    rwa [← contMDiffOn_univ]
  -- Then evaluated at smooth Y, gives a smooth V section.
  have h_first : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F (E := V) x (cov_V τZ x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id) hcov_V_τZ Y.contMDiff
  -- Second term: cov_TM Z x (Y x) is smooth — this is the concreteConn pattern. We can
  -- reuse `concreteConn cov_TM Y Z` whose value at x is `cov_TM Z x (Y x)`.
  have h_concrete : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E (E := TangentSpace I) x
        ((concreteConn I M cov_TM Y Z) x)) :=
    (concreteConn I M cov_TM Y Z).contMDiff
  -- τ applied to the smooth TM-section gives smooth V-section.
  have h_second : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F (E := V) x (τ x ((concreteConn I M cov_TM Y Z) x))) :=
    ContMDiff.clm_bundle_apply (b := id) τ.contMDiff h_concrete
  -- Reduce: (homBundleCovFun cov_TM cov_V τ x (Y x))(Z x) =
  --   cov_V (τZ) x (Y x) − τ x (cov_TM Z x (Y x))
  have h_eq : ∀ x, (homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x) (Y x) (Z x) =
      cov_V τZ x (Y x) - τ x ((concreteConn I M cov_TM Y Z) x) := by
    intro x
    have hτ_diff := hom_section_mdiff I M F V τ x
    have hY_diff := vec_section_mdiff I M Y x
    have hZ_diff := vec_section_mdiff I M Z x
    rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V τ hτ_diff hY_diff hZ_diff]
    rfl
  -- Combine: the V-valued section x ↦ ⟨x, h_first - h_second⟩ is smooth.
  -- Use mdifferentiable_sub_section / contMDiff_sub_section style, but for ContMDiff we use
  -- mathlib's lemmas at the section level.
  -- Show that the desired section is pointwise equal to (V-section h_first) - (V-section h_second).
  have h_diff : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F (E := V) x
        (cov_V τZ x (Y x) - τ x ((concreteConn I M cov_TM Y Z) x))) := by
    -- Express as a difference of smooth sections via section subtraction.
    -- Build smooth sections s₁, s₂ and use ContMDiff sub_section.
    let s₁ : Cₛ^∞⟮I; F, V⟯ := ⟨fun x => cov_V τZ x (Y x), h_first⟩
    let s₂ : Cₛ^∞⟮I; F, V⟯ :=
      ⟨fun x => τ x ((concreteConn I M cov_TM Y Z) x), h_second⟩
    have : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
        (fun x => TotalSpace.mk' F (E := V) x ((s₁ - s₂) x)) := (s₁ - s₂).contMDiff
    convert this using 1
  -- Final: bridge to the section value via h_eq.
  intro x₀
  rw [contMDiffAt_section]
  have h_diff_at := h_diff x₀
  rw [contMDiffAt_section] at h_diff_at
  refine h_diff_at.congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [h_eq]

/-- The Hom-bundle covariant derivative on `Hom(TM, V)` is `C^∞`. -/
noncomputable instance homBundleCovariantDerivative_contMDiff
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov_TM ∞]
    (cov_V : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov_V ∞] :
    ContMDiffCovariantDerivative (homBundleCovariantDerivative I M F V cov_TM cov_V) ∞ where
  contMDiff := {
    contMDiff := by
      intro τ hτ
      have hτ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
          (fun x => TotalSpace.mk' (E →L[ℝ] F)
            (E := fun x : M => (TangentSpace I x →L[ℝ] V x)) x (τ x)) := by
        rw [show (∞ : WithTop ℕ∞) = ∞ + 1 from by simp] at hτ
        rwa [← contMDiffOn_univ]
      let τ_section : Cₛ^∞⟮I; E →L[ℝ] F, (fun x => TangentSpace I x →L[ℝ] V x)⟯ :=
        ⟨τ, hτ_smooth⟩
      rw [contMDiffOn_univ]
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (V₁ := TangentSpace I)
        (V₂ := fun x => TangentSpace I x →L[ℝ] V x)
        (φ := fun x => homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x)
      intro Y
      exact homBundleCov_section_smooth I M F V cov_TM cov_V τ_section Y
  }

/-! ### Pointwise computation lemma -/

/-- Pointwise characterization: when `τ` is a smooth Hom-bundle section and `Y` a smooth vector
field, the Hom-bundle covariant derivative applied bilinearly to `v ∈ T_xM` and `Y x` has the
value
`cov_V (fun y => τ y (Y y)) x v − τ x (cov_TM Y x v)`,
i.e. the standard product-rule formula `(∇^Hom_v τ)(Y x) = ∇^V_v(τ(Y)) − τ(∇^TM_v Y)`. -/
theorem homBundleCovariantDerivative_apply
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Cₛ^∞⟮I; E →L[ℝ] F, (fun x => TangentSpace I x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    (homBundleCovariantDerivative I M F V cov_TM cov_V τ x v) (Y x) =
      cov_V (fun y => τ y (Y y)) x v - τ x (cov_TM Y x v) := by
  change homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x v (Y x) = _
  obtain ⟨V_field, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hτ_diff := hom_section_mdiff I M F V τ x
  have hV_diff := vec_section_mdiff I M V_field x
  have hY_diff := vec_section_mdiff I M Y x
  rw [show v = (V_field : Π x : M, TangentSpace I x) x from hVx.symm]
  rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V τ hτ_diff hV_diff hY_diff]
  rfl

end HomConnection

end

