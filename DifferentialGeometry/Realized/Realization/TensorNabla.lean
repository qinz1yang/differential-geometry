import DifferentialGeometry.Realized.Realization.SmoothSections
import DifferentialGeometry.Realized.Realization.Connection
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

/-!
# Dual covariant derivative on T*M

Given a `CovariantDerivative` on `TM`, this file constructs the induced dual covariant
derivative on the cotangent bundle `T*M = Bundle.dual ℝ (TangentSpace I)`.

## Main definition

* `dualCovariantDerivative` : the dual `CovariantDerivative` on `Bundle.dual ℝ (TangentSpace I)`.

## Strategy

For a 1-form `α` and vector fields `V`, `Y` differentiable at `x`, the scalar
```
Ψ_α(V, Y)(x) := extDerivFun(α·Y) x (V x) - α x (cov Y x (V x))
```
is *tensorial* in BOTH `V` and `Y` at `x`. The `V`-tensoriality is automatic because
`extDerivFun(α·Y) x` and `α x ∘L cov Y x` are continuous linear maps. The `Y`-tensoriality
is the standard product-rule cancellation.

By `TensorialAt.mkHom₂`, this gives a continuous bilinear map
`T_xM →L[ℝ] T_xM →L[ℝ] ℝ` representing `(∇* α)(x)`. The first argument is the differentiation
direction `v`; the second is the input to the resulting 1-form `(∇*_v α)`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative

section DualConnection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Abbreviations for differentiability of 1-forms and vector fields. -/

/-- "α is differentiable at x" for a 1-form α, in total-space form. -/
private abbrev MDiffAtDual
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
    (fun y => TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x)) y (α y)) x

/-- "Y is differentiable at x" for a vector field Y, in total-space form. -/
private abbrev MDiffAtVec
    (Y : Π x : M, TangentSpace I x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E))
    (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x

/-- Pairing α(Y) is differentiable when α and Y are. Goes from total-space form
to "scalar function M → ℝ" form via Trivial bundle trivialization. -/
private theorem mdiffAt_pairing
    {α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x}
    {Y : Π x : M, TangentSpace I x} {x : M}
    (hα : MDiffAtDual I M α x) (hY : MDiffAtVec I M Y x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y y)) x := by
  -- Apply MDifferentiableAt.clm_bundle_apply: gives Trivial M ℝ section smoothness
  have h := MDifferentiableAt.clm_bundle_apply (b := id) hα hY
  -- h : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ)) (fun m ↦ ⟨id m, α m (Y m)⟩) x
  -- Convert to scalar smoothness via mdifferentiableAt_section for Trivial bundle.
  -- Convert h (which has `id m` for the base) into the standard section form.
  have h' : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun m => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) m (α m (Y m))) x := h
  -- Now use mdifferentiableAt_section to extract scalar smoothness.
  rw [mdifferentiableAt_section (F := ℝ) (E := Bundle.Trivial M ℝ)] at h'
  -- For the trivial bundle, the trivialization fiber projection is the identity.
  exact h'

/-! ### The raw scalar operator -/

/-- The raw scalar operator
`Ψ_α(V, Y)(x) := extDerivFun(α·Y) x (V x) - α x (cov Y x (V x))`. -/
private def Psi
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    (V Y : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  extDerivFun (fun y => α y (Y y)) x (V x) - (α x) (cov Y x (V x))

/-! ### Tensoriality in V (the differentiation direction): automatic from CLM linearity. -/

private theorem Psi_add_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {V V' Y : Π x : M, TangentSpace I x} {x : M} :
    Psi I M cov α (V + V') Y x = Psi I M cov α V Y x + Psi I M cov α V' Y x := by
  have h_add : (V + V' : Π x : M, TangentSpace I x) x = V x + V' x := rfl
  simp only [Psi, h_add, ContinuousLinearMap.map_add]
  ring

private theorem Psi_smul_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {f : M → ℝ} {V Y : Π x : M, TangentSpace I x} {x : M} :
    Psi I M cov α (f • V) Y x = f x • Psi I M cov α V Y x := by
  have h_smul : (f • V : Π x : M, TangentSpace I x) x = f x • V x := rfl
  simp only [Psi, h_smul, ContinuousLinearMap.map_smul, smul_eq_mul]
  ring

/-! ### Tensoriality in Y (the input to the resulting 1-form): the product-rule cancellation. -/

private theorem Psi_add_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {V Y Y' : Π x : M, TangentSpace I x} {x : M}
    (hα : MDiffAtDual I M α x)
    (hY : MDiffAtVec I M Y x) (hY' : MDiffAtVec I M Y' x) :
    Psi I M cov α V (Y + Y') x = Psi I M cov α V Y x + Psi I M cov α V Y' x := by
  -- Show smoothness of the scalar pairings α·Y, α·Y'
  have hαY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y y)) x :=
    mdiffAt_pairing I M hα hY
  have hαY' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y' y)) x :=
    mdiffAt_pairing I M hα hY'
  have h_add_fun : (fun y => α y ((Y + Y') y)) =
      (fun y => α y (Y y)) + (fun y => α y (Y' y)) := by
    funext y
    simp [Pi.add_apply, ContinuousLinearMap.map_add]
  -- Convert MDiffAtVec to MDiffAt (T% Y) — they should be equal
  have hY_T : MDiffAt (T% fun y => Y y) x := hY
  have hY'_T : MDiffAt (T% fun y => Y' y) x := hY'
  simp only [Psi]
  rw [h_add_fun, extDerivFun_add hαY hαY']
  rw [show (Y + Y' : Π x : M, TangentSpace I x) = (fun x => Y x) + (fun x => Y' x) from rfl,
    cov.isCovariantDerivativeOn.add hY_T hY'_T]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
  ring

private theorem Psi_smul_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {V Y : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M}
    (hα : MDiffAtDual I M α x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hY : MDiffAtVec I M Y x) :
    Psi I M cov α V (f • Y) x = f x • Psi I M cov α V Y x := by
  have hαY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y y)) x :=
    mdiffAt_pairing I M hα hY
  have h_fun : (fun y => α y ((f • Y) y)) = f • (fun y => α y (Y y)) := by
    funext y
    simp [smul_eq_mul]
  have hY_T : MDiffAt (T% fun y => Y y) x := hY
  simp only [Psi]
  rw [h_fun]
  have h_extDeriv_eq : ∀ (h : M → ℝ) (y : M) (w : TangentSpace I y),
      extDerivFun (I := I) h y w =
      NormedSpace.fromTangentSpace (h y) ((mfderiv I 𝓘(ℝ, ℝ) h y) w) := by
    intro h y w
    simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  have h_prod := fromTangentSpace_mfderiv_smul_apply (I := I) hf hαY (V x)
  rw [h_extDeriv_eq _ _ (V x), h_prod]
  -- Now use cov.isCovariantDerivativeOn.leibniz to expand cov (f • Y) x.
  rw [show (f • Y : Π x : M, TangentSpace I x) = f • (fun x => Y x) from rfl,
    cov.isCovariantDerivativeOn.leibniz hY_T hf]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
    ContinuousLinearMap.map_smul, smul_eq_mul]
  -- The remaining goal is an arithmetic identity. We have a `fromTangentSpace`-form
  -- expression on the LHS that equals `extDerivFun (α·Y) x (V x)` by `h_extDeriv_eq`.
  have h_eq2 : (NormedSpace.fromTangentSpace ((α x) (Y x)))
      (((mfderiv I 𝓘(ℝ, ℝ) (fun y => α y (Y y))) x) (V x)) =
      (extDerivFun (fun y => α y (Y y)) x) (V x) :=
    (h_extDeriv_eq (fun y => α y (Y y)) x (V x)).symm
  have h_eq3 : (NormedSpace.fromTangentSpace (f x))
      (((mfderiv I 𝓘(ℝ, ℝ) f) x) (V x)) =
      (extDerivFun f x) (V x) :=
    (h_extDeriv_eq f x (V x)).symm
  rw [h_eq2, h_eq3]
  ring

/-! ### Bilinear tensoriality of `Psi α V Y x` -/

/-- Tensoriality in V (left argument) at x — for any Y. -/
private theorem Psi_tensorialAt_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {x : M} (Y : Π x : M, TangentSpace I x) :
    TensorialAt I E (fun V => Psi I M cov α V Y x) x where
  smul := fun _ _ => Psi_smul_left I M cov α
  add := fun _ _ => Psi_add_left I M cov α

/-- Tensoriality in Y (right argument) at x — when α is differentiable at x. -/
private theorem Psi_tensorialAt_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {x : M} (hα : MDiffAtDual I M α x) (V : Π x : M, TangentSpace I x) :
    TensorialAt I E (fun Y => Psi I M cov α V Y x) x where
  smul := fun hf hY => Psi_smul_right I M cov α hα hf hY
  add := fun hY hY' => Psi_add_right I M cov α hα hY hY'

/-! ### The dual covariant derivative on T*M -/

private theorem dual_section_mdiff
    (α : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯)
    (x : M) : MDiffAtDual I M (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x) x :=
  α.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

private theorem vec_section_mdiff
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
  Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

/-- The dual covariant derivative pointwise function. For each section
`α : Π x, (Bundle.dual ℝ (TangentSpace I)) x` and point `x`, returns a CLM
`T_xM →L[ℝ] T*M_x`.

If `α` is differentiable at `x`, the value is the bilinear map built via
`TensorialAt.mkHom₂`. For non-differentiable α, returns the junk value `0`. -/
noncomputable def dualCovariantDerivativeFun
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    (x : M) :
    TangentSpace I x →L[ℝ] (Bundle.dual ℝ (TangentSpace I : M → Type _)) x := by
  classical
  by_cases hα : MDiffAtDual I M α x
  · exact TensorialAt.mkHom₂ (F := E) (F' := E)
      (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
      (fun V Y => Psi I M cov α V Y x) x
      (fun Y _ => Psi_tensorialAt_left I M cov α Y)
      (fun V _ => Psi_tensorialAt_right I M cov α hα V)
  · exact 0

/-- Specification: when `α`, `V`, `Y` are all differentiable at `x`, the dual covariant
derivative applied bilinearly to `V x` and `Y x` returns `Psi α V Y x`. -/
private theorem dualCovariantDerivativeFun_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {x : M} (hα : MDiffAtDual I M α x)
    {V Y : Π x : M, TangentSpace I x}
    (hV : MDiffAtVec I M V x) (hY : MDiffAtVec I M Y x) :
    dualCovariantDerivativeFun I M cov α x (V x) (Y x) = Psi I M cov α V Y x := by
  unfold dualCovariantDerivativeFun
  rw [dif_pos hα]
  exact TensorialAt.mkHom₂_apply
    (Φ := fun V Y => Psi I M cov α V Y x)
    (fun Y _ => Psi_tensorialAt_left I M cov α Y)
    (fun V _ => Psi_tensorialAt_right I M cov α hα V) hV hY

/-- The junk value: when α is not differentiable at x, the dual connection is zero. -/
private theorem dualCovariantDerivativeFun_of_not_mdiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {x : M} (hα : ¬ MDiffAtDual I M α x) :
    dualCovariantDerivativeFun I M cov α x = 0 := by
  unfold dualCovariantDerivativeFun
  rw [dif_neg hα]

/-! ### IsCovariantDerivativeOn -/

/-- The dual covariant derivative satisfies `IsCovariantDerivativeOn` on `Set.univ`. -/
private theorem dualCovariantDerivativeFun_isCovOn
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    IsCovariantDerivativeOn (E →L[ℝ] ℝ)
      (dualCovariantDerivativeFun I M cov) Set.univ where
  add := by
    intro α₁ α₂ x hα₁ hα₂ _hx
    -- IsCovariantDerivativeOn.add hypothesis: hα₁ : MDiffAt (T% α₁) x.
    -- Convert to MDiffAtDual form (they should be definitionally equal).
    have hα₁' : MDiffAtDual I M α₁ x := hα₁
    have hα₂' : MDiffAtDual I M α₂ x := hα₂
    have hα_sum : MDiffAtDual I M (α₁ + α₂) x :=
      mdifferentiableAt_add_section (F := E →L[ℝ] ℝ) hα₁ hα₂
    ext v w
    obtain ⟨V, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
    have hV_diff : MDiffAtVec I M (V : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M V x
    have hY_diff : MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M Y x
    rw [show (v : TangentSpace I x) = (V : Π x : M, TangentSpace I x) x from hVx.symm]
    rw [show (w : TangentSpace I x) = (Y : Π x : M, TangentSpace I x) x from hYx.symm]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    rw [dualCovariantDerivativeFun_apply I M cov (α₁ + α₂) hα_sum hV_diff hY_diff]
    rw [dualCovariantDerivativeFun_apply I M cov α₁ hα₁' hV_diff hY_diff]
    rw [dualCovariantDerivativeFun_apply I M cov α₂ hα₂' hV_diff hY_diff]
    -- Goal: Psi (α₁+α₂) V Y x = Psi α₁ V Y x + Psi α₂ V Y x
    have h_funeq : (fun y => (α₁ + α₂) y (Y y)) =
        (fun y => α₁ y (Y y)) + (fun y => α₂ y (Y y)) := by
      funext y
      simp [Pi.add_apply, ContinuousLinearMap.add_apply]
    have hα₁Y : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α₁ y (Y y)) x :=
      mdiffAt_pairing I M hα₁' hY_diff
    have hα₂Y : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α₂ y (Y y)) x :=
      mdiffAt_pairing I M hα₂' hY_diff
    simp only [Psi]
    rw [h_funeq, extDerivFun_add hα₁Y hα₂Y]
    simp only [ContinuousLinearMap.add_apply, Pi.add_apply]
    ring
  leibniz := by
    intro α g x hα hg _hx
    have hα' : MDiffAtDual I M α x := hα
    have hgα : MDiffAtDual I M (g • α) x :=
      hg.smul_section (F := E →L[ℝ] ℝ) hα
    ext v w
    obtain ⟨V, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
    have hV_diff : MDiffAtVec I M (V : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M V x
    have hY_diff : MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M Y x
    rw [show (v : TangentSpace I x) = (V : Π x : M, TangentSpace I x) x from hVx.symm]
    rw [show (w : TangentSpace I x) = (Y : Π x : M, TangentSpace I x) x from hYx.symm]
    -- LHS: dualCov(g•α) x (V x) (Y x)
    -- RHS evaluated at Y x: g x • dualCov α x (V x) (Y x) + extDerivFun g x V x • α x (Y x)
    -- The RHS is `(g x • A + B.smulRight v) (Y x)` where A and v are covectors.
    -- Distribute the (Y x) application using ContinuousLinearMap.add_apply and smul_apply.
    rw [dualCovariantDerivativeFun_apply I M cov (g • α) hgα hV_diff hY_diff]
    change Psi I M cov (g • α) V Y x =
      g x • (dualCovariantDerivativeFun I M cov α x (V x)) (Y x) +
      ((extDerivFun g x) (V x)) * (α x) (Y x)
    rw [dualCovariantDerivativeFun_apply I M cov α hα' hV_diff hY_diff]
    have h_funeq : (fun y => (g • α) y (Y y)) = g • (fun y => α y (Y y)) := by
      funext y
      simp [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hαY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y y)) x :=
      mdiffAt_pairing I M hα' hY_diff
    simp only [Psi]
    rw [h_funeq]
    have h_extDeriv_eq : ∀ (h : M → ℝ) (y : M) (u : TangentSpace I y),
        extDerivFun (I := I) h y u =
        NormedSpace.fromTangentSpace (h y) ((mfderiv I 𝓘(ℝ, ℝ) h y) u) := by
      intro h y u
      simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    have h_prod := fromTangentSpace_mfderiv_smul_apply (I := I) hg hαY (V x)
    rw [h_extDeriv_eq _ _ (V x), h_prod]
    have hgα_apply : (g • α) x = g x • α x := rfl
    rw [hgα_apply]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    -- Convert remaining fromTangentSpace expressions back to extDerivFun.
    have h_eq2 : (NormedSpace.fromTangentSpace ((α x) (Y x)))
        (((mfderiv I 𝓘(ℝ, ℝ) (fun y => α y (Y y))) x) (V x)) =
        (extDerivFun (fun y => α y (Y y)) x) (V x) :=
      (h_extDeriv_eq (fun y => α y (Y y)) x (V x)).symm
    have h_eq3 : (NormedSpace.fromTangentSpace (g x))
        (((mfderiv I 𝓘(ℝ, ℝ) g) x) (V x)) =
        (extDerivFun g x) (V x) :=
      (h_extDeriv_eq g x (V x)).symm
    rw [h_eq2, h_eq3]
    ring

/-! ### The bundled `CovariantDerivative` -/

/-- The dual covariant derivative on `T*M`, packaged as a `CovariantDerivative`. -/
noncomputable def dualCovariantDerivative
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    CovariantDerivative I (E →L[ℝ] ℝ)
      (Bundle.dual ℝ (TangentSpace I : M → Type _)) where
  toFun := dualCovariantDerivativeFun I M cov
  isCovariantDerivativeOnUniv := dualCovariantDerivativeFun_isCovOn I M cov

/-! ### ContMDiffCovariantDerivative instance (smoothness)

For a `C^∞` covariant derivative `cov` on `TM` and a smooth 1-form `α`, the dual covariant
derivative `dualCov α` is a smooth section of `Hom(TM, T*M)`. This is established in two
steps:

1. **Section helper** `dualCov_section_smooth`: for smooth α and smooth vector field Y,
   the section `x ↦ ⟨x, (dualCov α x)(Y x)⟩` is a smooth section of T*M. The proof uses
   the `dualCovariantDerivativeFun_apply` lemma to rewrite the value as
   `extDerivFun(α·Y) x - α x ∘L cov Y x`, then composes the smoothness lemmas from
   `SmoothSections.lean` and the connection.
2. **Bridge**: `contMDiff_clm_section_of_pointwise` lifts pointwise smoothness in step 1
   to total-space smoothness of the Hom-bundle section `x ↦ ⟨x, dualCov α x⟩`. -/

/-- For smooth α and smooth Y, the section `x ↦ ⟨x, (dualCov α x)(Y x)⟩` of `T*M` is smooth.

The proof uses the bridge `contMDiff_clm_section_of_pointwise` with
`V₁ = TangentSpace I, V₂ = Trivial M ℝ`: for each smooth section `Z` of TM, the scalar
`x ↦ (dualCov α x)(Y x)(Z x) = extDerivFun(α·Z) x (Y x) - α x (cov Z x (Y x))` is smooth,
which lifts to total-space smoothness as a section of `dual ℝ TangentSpace I = Hom(TM, ℝ)`. -/
private theorem dualCov_section_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (α : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x))
        x ((dualCovariantDerivativeFun I M cov α x) (Y x))) := by
  -- Apply the bridge: the section `x ↦ ⟨x, (dualCov α x)(Y x)⟩` is smooth iff for every
  -- smooth Z, the scalar `x ↦ (dualCov α x)(Y x)(Z x)` is smooth.
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I) (V₂ := Bundle.Trivial M ℝ)
    (φ := fun x => (dualCovariantDerivativeFun I M cov α x) (Y x))
  intro Z
  -- For each smooth Z, the value `(dualCov α x)(Y x)(Z x)` equals
  -- `extDerivFun(α·Z) x (Y x) - α x (cov Z x (Y x))` by `dualCovariantDerivative_apply`
  -- (with V = Y, Y_in_apply = Z).
  -- 1. `extDerivFun(α·Z) x (Y x)` smooth: `α·Z` is a smooth scalar function, its extDeriv
  --    is a smooth covector field, evaluated on smooth Y is smooth.
  -- 2. `α x (cov Z x (Y x))` smooth: `cov Z` is smooth Hom-bundle section, applied to
  --    smooth Y gives smooth TM section (= concreteConn cov Y Z), then α applied gives
  --    smooth scalar.
  have hαZ : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => α y (Z y)) :=
    contMDiff_dual_apply_section I M α Z
  let fαZ : C^∞⟮I, M; ℝ⟯ := ⟨_, hαZ⟩
  have h_extDeriv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x))
        x (extDerivFun (fun y => α y (Z y)) x)) := by
    have := contMDiff_extDerivFun_section I M fαZ
    simpa [fαZ] using this
  -- extDerivFun(α·Z) is a smooth section of T*M, evaluated at Y gives smooth scalar.
  have h_extDeriv_at_Y : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (fun y => α y (Z y)) x (Y x)) := by
    let dα : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯ :=
      ⟨fun x => extDerivFun (fun y => α y (Z y)) x, h_extDeriv⟩
    have := contMDiff_dual_apply_section I M dα Y
    simpa [dα] using this
  -- α x (cov Z x (Y x)) = α x ((concreteConn cov Y Z) x): apply contMDiff_dual_apply_section.
  have h_concreteConn : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => α x ((concreteConn I M cov Y Z) x)) :=
    contMDiff_dual_apply_section I M α (concreteConn I M cov Y Z)
  have h_α_cov : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => α x (cov Z x (Y x))) := h_concreteConn
  -- Combine: pointwise difference is smooth.
  have h_diff : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (fun y => α y (Z y)) x (Y x) - α x (cov Z x (Y x))) :=
    h_extDeriv_at_Y.sub h_α_cov
  -- Now show this equals `(dualCov α x)(Y x)(Z x)` and lift to total-space smoothness.
  have h_eq : ∀ x, (dualCovariantDerivativeFun I M cov α x) (Y x) (Z x) =
      extDerivFun (fun y => α y (Z y)) x (Y x) - α x (cov Z x (Y x)) := by
    intro x
    -- Use private dualCovariantDerivativeFun_apply with V = Y, Y_in_apply = Z.
    have hα := dual_section_mdiff I M α x
    have hY := vec_section_mdiff I M Y x
    have hZ := vec_section_mdiff I M Z x
    rw [dualCovariantDerivativeFun_apply I M cov α hα hY hZ]
    rfl
  -- Final: convert the scalar smoothness to total-space smoothness via Bundle.Trivial.
  -- The target is smoothness as a section of `Bundle.Trivial M ℝ`.
  intro x₀
  rw [contMDiffAt_section]
  -- After unfolding, the section value is the scalar (dualCov α x)(Y x)(Z x); on
  -- Bundle.Trivial, the trivialization fiber projection is the identity.
  have h_diff_at := h_diff x₀
  -- Convert h_diff to the form needed.
  refine h_diff_at.congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [h_eq]
  -- Need: `(trivializationAt ℝ (Trivial M ℝ) x₀ ⟨x, ...⟩).2 = (extDeriv... - α(cov Z Y))`
  -- For Bundle.Trivial, the trivialization fiber projection is the identity.
  simp [Bundle.Trivial.fiberBundle_trivializationAt']

/-! ### ContMDiffCovariantDerivative instance -/

/-- The dual covariant derivative on T*M is `C^∞`. -/
noncomputable instance dualCovariantDerivative_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative (dualCovariantDerivative I M cov) ∞ where
  contMDiff := {
    contMDiff := by
      -- Goal: for each section α with CMDiff (∞+1) (T% α), the function
      -- `x ↦ ⟨x, dualCov.toFun α x⟩` is ContMDiffOn ∞ on Set.univ.
      intro α hα
      -- α is C^(∞+1) = C^∞, so wrap as a smooth section.
      have hα_smooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
          (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
            (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x)) x (α x)) := by
        rw [show (∞ : WithTop ℕ∞) = ∞ + 1 from by simp] at hα
        rwa [← contMDiffOn_univ]
      let α_section : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯ :=
        ⟨α, hα_smooth⟩
      -- Apply the bridge: for each smooth Y, the section x ↦ ⟨x, (dualCov α x)(Y x)⟩
      -- is smooth (by `dualCov_section_smooth`).
      rw [contMDiffOn_univ]
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (V₁ := TangentSpace I)
        (V₂ := Bundle.dual ℝ (TangentSpace I : M → Type _))
        (φ := fun x => dualCovariantDerivativeFun I M cov α x)
      intro Y
      exact dualCov_section_smooth I M cov α_section Y
  }

/-! ### Pointwise computation lemma -/

/-- Pointwise characterization: when α is a smooth 1-form and Y a smooth vector field,
the dual covariant derivative applied bilinearly to `v ∈ T_xM` and `Y x` has the value
`extDerivFun(α·Y) x v - α x (cov Y x v)` (the standard product-rule formula
`(∇*_v α)(Y x) = v(α(Y)) - α(∇_v Y)`). -/
theorem dualCovariantDerivative_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    (dualCovariantDerivative I M cov α x v) (Y x) =
      extDerivFun (fun y => α y (Y y)) x v - (α x) (cov Y x v) := by
  change dualCovariantDerivativeFun I M cov α x v (Y x) = _
  obtain ⟨V, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hα_diff := dual_section_mdiff I M α x
  have hV_diff := vec_section_mdiff I M V x
  have hY_diff := vec_section_mdiff I M Y x
  rw [show v = (V : Π x : M, TangentSpace I x) x from hVx.symm]
  rw [dualCovariantDerivativeFun_apply I M cov α hα_diff hV_diff hY_diff]
  rfl

end DualConnection

end
