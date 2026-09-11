import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
noncomputable section
open Module

namespace DifferentialGeometry.ContinuousAlternatingMap

variable {m : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (hm : finrank ℝ E = m)
  (ω : E [⋀^Fin m]→L[ℝ] ℝ) (Ω : F [⋀^Fin (m + 1)]→L[ℝ] ℝ)
  (L : E →L[ℝ] F)

def normalCovector : F →L[ℝ] ℝ :=
  let b := Module.finBasisOfFinrankEq ℝ E hm
  (ω b)⁻¹ • ((_root_.ContinuousAlternatingMap.apply ℝ E ℝ b).comp
    ((_root_.ContinuousAlternatingMap.compContinuousLinearMapCLM L).comp Ω.curryLeft))


theorem normalCovector_spec (hω : ω ≠ 0) (v : F) (u : Fin m → E) :
    Ω (Matrix.vecCons v (L ∘ u)) = normalCovector hm ω Ω L v * ω u := by
  let b := Module.finBasisOfFinrankEq ℝ E hm
  have hb : ω b ≠ 0 := ω.toAlternatingMap.map_basis_ne_zero_iff b |>.mpr
    (fun h => hω (_root_.ContinuousAlternatingMap.toAlternatingMap_injective h))
  have h₁ := congrArg (fun f : E [⋀^Fin m]→ₗ[ℝ] ℝ => f u)
    (((Ω.curryLeft v).compContinuousLinearMap L).toAlternatingMap.eq_smul_basis_det b)
  have h₂ := congrArg (fun f : E [⋀^Fin m]→ₗ[ℝ] ℝ => f u)
    (ω.toAlternatingMap.eq_smul_basis_det b)
  change Ω (Matrix.vecCons v (L ∘ u)) =
    Ω (Matrix.vecCons v (L ∘ b)) * b.det u at h₁
  change ω u = ω b * b.det u at h₂
  change Ω (Matrix.vecCons v (L ∘ u)) =
    ((ω b)⁻¹ * Ω (Matrix.vecCons v (L ∘ b))) * ω u
  rw [h₁, h₂]
  field_simp


theorem normalCovector_unique (hω : ω ≠ 0) (ν : F →L[ℝ] ℝ)
    (hν : ∀ v u, Ω (Matrix.vecCons v (L ∘ u)) = ν v * ω u) :
    ν = normalCovector hm ω Ω L := by
  let b := Module.finBasisOfFinrankEq ℝ E hm
  have hb : ω b ≠ 0 := ω.toAlternatingMap.map_basis_ne_zero_iff b |>.mpr
    (fun h => hω (_root_.ContinuousAlternatingMap.toAlternatingMap_injective h))
  ext v
  exact mul_right_cancel₀ hb ((hν v b).symm.trans (normalCovector_spec hm ω Ω L hω v b))


theorem normalCovector_apply_basis (hω : ω ≠ 0) (b : Basis (Fin m) ℝ E) (v : F) :
    normalCovector hm ω Ω L v = Ω (Matrix.vecCons v (L ∘ b)) / ω b := by
  have hb : ω b ≠ 0 := ω.toAlternatingMap.map_basis_ne_zero_iff b |>.mpr
    (fun h => hω (_root_.ContinuousAlternatingMap.toAlternatingMap_injective h))
  exact (eq_div_iff hb).mpr (normalCovector_spec hm ω Ω L hω v b).symm

private theorem topForm_apply_ne_zero_iff
    (hF : finrank ℝ F = m + 1) (hΩ : Ω ≠ 0) (u : Fin (m + 1) → F) :
    Ω u ≠ 0 ↔ LinearIndependent ℝ u := by
  constructor
  · intro hu
    by_contra hdep
    exact hu (Ω.toAlternatingMap.map_linearDependent u hdep)
  · intro hu
    let b := basisOfLinearIndependentOfCardEqFinrank hu (by simp [hF])
    have hh := Ω.toAlternatingMap.map_basis_ne_zero_iff b |>.mpr
      (fun h => hΩ (_root_.ContinuousAlternatingMap.toAlternatingMap_injective h))
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank] at hh
    exact hh

theorem normalCovector_apply_eq_zero_iff (hω : ω ≠ 0)
    (hF : finrank ℝ F = m + 1) (hΩ : Ω ≠ 0) (hL : Function.Injective L) (v : F) :
    normalCovector hm ω Ω L v = 0 ↔ v ∈ L.range := by
  let b := Module.finBasisOfFinrankEq ℝ E hm
  have hb : ω b ≠ 0 := ω.toAlternatingMap.map_basis_ne_zero_iff b |>.mpr
    (fun h => hω (_root_.ContinuousAlternatingMap.toAlternatingMap_injective h))
  have hi : LinearIndependent ℝ (L ∘ b) := b.linearIndependent.map' L.toLinearMap
    (LinearMap.ker_eq_bot.mpr hL)
  have hs : Submodule.span ℝ (Set.range (L ∘ b)) = L.range := by
    rw [Set.range_comp]
    change Submodule.span ℝ (L.toLinearMap '' Set.range b) = L.range
    rw [← Submodule.map_span, b.span_eq, Submodule.map_top]
  apply not_iff_not.mp
  rw [normalCovector_apply_basis hm ω Ω L hω b, div_eq_zero_iff, or_iff_left hb]
  apply (topForm_apply_ne_zero_iff Ω hF hΩ _).trans
  change LinearIndependent ℝ (Fin.cons v (L ∘ b)) ↔ v ∉ L.range
  rw [linearIndependent_finCons, hs, and_iff_right hi]


theorem ker_normalCovector (hω : ω ≠ 0)
    (hF : finrank ℝ F = m + 1) (hΩ : Ω ≠ 0) (hL : Function.Injective L) :
    (normalCovector hm ω Ω L).ker = L.range := by
  ext v
  exact normalCovector_apply_eq_zero_iff hm ω Ω L hω hF hΩ hL v


theorem normalCovector_ne_zero (hω : ω ≠ 0)
    (hF : finrank ℝ F = m + 1) (hΩ : Ω ≠ 0) (hL : Function.Injective L) :
    normalCovector hm ω Ω L ≠ 0 := by
  intro hz
  have hk := ker_normalCovector hm ω Ω L hω hF hΩ hL
  have htop : L.range = ⊤ := by simpa only [hz, ContinuousLinearMap.toLinearMap_zero, LinearMap.ker_zero] using hk.symm
  have hr := LinearMap.finrank_range_of_inj (f := L.toLinearMap) hL
  rw [htop, finrank_top, hm, hF] at hr
  omega

theorem normalCovector_smul (hω : ω ≠ 0) (a b : ℝ) (ha : a ≠ 0) :
    normalCovector hm (a • ω) (b • Ω) L = (b / a) • normalCovector hm ω Ω L := by
  symm
  apply normalCovector_unique hm (a • ω) (b • Ω) L (smul_ne_zero ha hω)
  intro v u
  simp only [_root_.ContinuousAlternatingMap.smul_apply, smul_apply,
    smul_eq_mul, normalCovector_spec hm ω Ω L hω v u]
  field_simp

theorem normalCovector_smul_pos_iff (hω : ω ≠ 0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (v : F) :
    0 < normalCovector hm (a • ω) (b • Ω) L v ↔ 0 < normalCovector hm ω Ω L v := by
  rw [normalCovector_smul hm ω Ω L hω a b ha.ne', smul_apply,
    smul_eq_mul, mul_pos_iff_of_pos_left (div_pos hb ha)]


theorem normalCovector_surjective (hω : ω ≠ 0)
    (hF : finrank ℝ F = m + 1) (hΩ : Ω ≠ 0) (hL : Function.Injective L) :
    Function.Surjective (normalCovector hm ω Ω L) := by
  apply LinearMap.surjective (f := (normalCovector hm ω Ω L).toLinearMap)
  intro h
  exact normalCovector_ne_zero hm ω Ω L hω hF hΩ hL
    (by ext v; exact congrArg (fun f : F →ₗ[ℝ] ℝ => f v) h)

theorem normalCovector_compContinuousLinearEquiv (hω : ω ≠ 0)
    {E' F' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] (A : E' ≃L[ℝ] E) (B : F' ≃L[ℝ] F) :
    normalCovector (A.toLinearEquiv.finrank_eq.trans hm)
      (ω.compContinuousLinearMap A.toContinuousLinearMap) (Ω.compContinuousLinearMap B.toContinuousLinearMap)
      (B.symm.toContinuousLinearMap.comp (L.comp A.toContinuousLinearMap)) =
        (normalCovector hm ω Ω L).comp B.toContinuousLinearMap := by
  have hω' : ω.compContinuousLinearMap A.toContinuousLinearMap ≠ 0 := by
    intro h
    apply hω
    ext u
    have hh := congrArg (fun f : E' [⋀^Fin m]→L[ℝ] ℝ => f (A.symm ∘ u)) h
    change ω (fun i => A (A.symm (u i))) = 0 at hh
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hh
    exact hh
  symm
  apply normalCovector_unique _ _ _ _ hω'
  intro v u
  have ht : (B ∘ Matrix.vecCons v
      ((B.symm.toContinuousLinearMap.comp (L.comp A.toContinuousLinearMap)) ∘ u)) =
      Matrix.vecCons (B v) (L ∘ (A ∘ u)) := by
    funext i
    cases i using Fin.cases <;> simp [Function.comp_def]
  change Ω (B ∘ Matrix.vecCons v
    ((B.symm.toContinuousLinearMap.comp (L.comp A.toContinuousLinearMap)) ∘ u)) =
      normalCovector hm ω Ω L (B v) * ω (A ∘ u)
  rw [ht]
  exact normalCovector_spec hm ω Ω L hω (B v) (A ∘ u)

theorem continuousAt_normalCovector {X : Type*} [TopologicalSpace X] {x : X}
    {ω : X → E [⋀^Fin m]→L[ℝ] ℝ} {Ω : X → F [⋀^Fin (m + 1)]→L[ℝ] ℝ}
    {L : X → E →L[ℝ] F}
    (hω : ContinuousAt ω x) (hΩ : ContinuousAt Ω x) (hL : ContinuousAt L x)
    (hωx : ω x ≠ 0) :
    ContinuousAt (fun y => normalCovector hm (ω y) (Ω y) (L y)) x := by
  let b := Module.finBasisOfFinrankEq ℝ E hm
  have hb : ω x b ≠ 0 := (ω x).toAlternatingMap.map_basis_ne_zero_iff b |>.mpr
    (fun h => hωx (_root_.ContinuousAlternatingMap.toAlternatingMap_injective h))
  have h₁ : ContinuousAt (fun y => Ω y |>.curryLeft) x :=
    _root_.ContinuousAlternatingMap.curryLeftLI.continuous.continuousAt.comp hΩ
  have h₂ : ContinuousAt (fun y =>
      (_root_.ContinuousAlternatingMap.compContinuousLinearMapCLM (L y) :
        (F [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin m]→L[ℝ] ℝ))) x :=
    _root_.ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.continuousAt.comp hL
  exact ((hω.eval continuousAt_const).inv₀ hb).smul
    (continuousAt_const.clm_comp (h₂.clm_comp h₁))

end DifferentialGeometry.ContinuousAlternatingMap
