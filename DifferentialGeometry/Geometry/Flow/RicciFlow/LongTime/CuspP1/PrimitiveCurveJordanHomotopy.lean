import DifferentialGeometry.Topology.LoopSpace.PrimitiveCircleLift
import DifferentialGeometry.Topology.LoopSpace.HomeomorphismOrientation
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting

/-!
# Degree is a homotopy invariant (lane CP1-P2, group G1a)

Real lifts with integer shift of a circle-valued family `G : [0,1] × ℝ → Circle`, 1-periodic in the
second variable, have the same shift at both ends of the family.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Topology
namespace GC.LongTime.CuspP1

/-- The covering `ℝ → loopCircle` and its homeomorphism with `Circle`. -/
theorem coe_mk_eq_exp_CPP2 (x : ℝ) :
    AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0) (x : loopCircle) =
      Circle.exp (2 * Real.pi * x) := by
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  simp

private theorem intCast_coe_zero (n : ℤ) : (((n : ℝ)) : loopCircle) = 0 :=
  (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨n, by simp⟩

private theorem real_eq_add_int_of_coe_eq {x y : ℝ} (h : (x : loopCircle) = (y : loopCircle)) :
    ∃ k : ℤ, x = y + k := by
  have hz : ((x - y : ℝ) : loopCircle) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hz
  refine ⟨k, ?_⟩
  simp only [zsmul_eq_mul, mul_one] at hk
  linarith

/-- Two real lifts (through the covering `ℝ → loopCircle`) of the same map from `ℝ` differ by an
integer constant once they differ by an integer at one point. -/
private theorem lift_eq_add_int {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ t, (f t : loopCircle) = (g t : loopCircle)) :
    ∃ k : ℤ, ∀ t, f t = g t + k := by
  obtain ⟨k, hk⟩ := real_eq_add_int_of_coe_eq (hfg 0)
  refine ⟨k, fun t => ?_⟩
  have hcov : IsCoveringMap (fun x : ℝ => (x : loopCircle)) := AddCircle.isCoveringMap_coe (1 : ℝ)
  have := hcov.eq_of_comp_eq (A := ℝ) (g₁ := f) (g₂ := fun t => g t + k) hf
    (hg.add continuous_const) (by
      funext t
      change (f t : loopCircle) = ((g t + k : ℝ) : loopCircle)
      rw [AddCircle.coe_add, hfg t, intCast_coe_zero, add_zero]) 0 hk
  exact congrFun this t

theorem degree_eq_of_homotopy_CPP2 (G : unitInterval × ℝ → Circle) (hG : Continuous G)
    (hper : ∀ s t, G (s, t + 1) = G (s, t))
    (F₀ F₁ : ℝ → ℝ) (hF₀c : Continuous F₀) (hF₁c : Continuous F₁) (n₀ n₁ : ℤ)
    (hl₀ : ∀ t, G (0, t) = Circle.exp (2 * Real.pi * F₀ t))
    (hl₁ : ∀ t, G (1, t) = Circle.exp (2 * Real.pi * F₁ t))
    (hs₀ : ∀ t, F₀ (t + 1) = F₀ t + n₀) (hs₁ : ∀ t, F₁ (t + 1) = F₁ t + n₁) :
    n₀ = n₁ := by
  let φ : loopCircle ≃ₜ Circle := AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)
  have hcov : IsCoveringMap (fun x : ℝ => (x : loopCircle)) := AddCircle.isCoveringMap_coe (1 : ℝ)
  -- extend the family to `ℝ × ℝ` by clamping
  let Ĝ : C(ℝ × ℝ, loopCircle) :=
    ⟨fun st => φ.symm (G (Set.projIcc (0 : ℝ) 1 zero_le_one st.1, st.2)), by
      refine φ.symm.continuous.comp (hG.comp ?_)
      exact (continuous_projIcc.prodMap continuous_id)⟩
  have hĜ0 : ∀ t, Ĝ (0, t) = ((F₀ t : ℝ) : loopCircle) := by
    intro t
    change φ.symm (G (Set.projIcc (0 : ℝ) 1 zero_le_one 0, t)) = _
    have : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : unitInterval) := by
      apply Subtype.ext; simp [Set.projIcc]
    rw [this, hl₀, ← coe_mk_eq_exp_CPP2]
    exact φ.symm_apply_apply _
  have hĜ1 : ∀ t, Ĝ (1, t) = ((F₁ t : ℝ) : loopCircle) := by
    intro t
    change φ.symm (G (Set.projIcc (0 : ℝ) 1 zero_le_one 1, t)) = _
    have : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : unitInterval) := by
      apply Subtype.ext; simp [Set.projIcc]
    rw [this, hl₁, ← coe_mk_eq_exp_CPP2]
    exact φ.symm_apply_apply _
  have hĜper : ∀ s t, Ĝ (s, t + 1) = Ĝ (s, t) := by
    intro s t
    change φ.symm (G (_, t + 1)) = φ.symm (G (_, t))
    rw [hper]
  obtain ⟨L, ⟨hL0, hLlift⟩, -⟩ := hcov.existsUnique_continuousMap_lifts Ĝ (0, 0) (F₀ 0) (by
    rw [hĜ0])
  have hLp : ∀ s t, ((L (s, t) : ℝ) : loopCircle) = Ĝ (s, t) := fun s t => congrFun hLlift (s, t)
  -- `L (0, ·) = F₀`
  have hL0F : ∀ t, L (0, t) = F₀ t := by
    intro t
    have := hcov.eq_of_comp_eq (A := ℝ) (g₁ := fun t => L (0, t)) (g₂ := F₀)
      (L.continuous.comp (continuous_const.prodMk continuous_id)) hF₀c (by
        funext t
        change ((L (0, t) : ℝ) : loopCircle) = ((F₀ t : ℝ) : loopCircle)
        rw [hLp, hĜ0]) 0 hL0
    exact congrFun this t
  -- shift of `L`
  have hLshift : ∀ s t, L (s, t + 1) = L (s, t) + n₀ := by
    have := hcov.eq_of_comp_eq (A := ℝ × ℝ) (g₁ := fun st => L (st.1, st.2 + 1))
      (g₂ := fun st => L st + n₀)
      (L.continuous.comp (continuous_fst.prodMk (continuous_snd.add continuous_const)))
      (L.continuous.add continuous_const) (by
        funext st
        change ((L (st.1, st.2 + 1) : ℝ) : loopCircle) = ((L st + n₀ : ℝ) : loopCircle)
        rw [hLp, hĜper, AddCircle.coe_add, hLp, intCast_coe_zero, add_zero]) (0, 0) (by
        change L (0, 0 + 1) = L (0, 0) + n₀
        have h := hs₀ 0
        rw [zero_add] at h
        rw [zero_add, hL0F, hL0F, h])
    intro s t
    exact congrFun this (s, t)
  -- `L (1, ·)` and `F₁` are lifts of the same map
  obtain ⟨k, hk⟩ := lift_eq_add_int (f := F₁) (g := fun t => L (1, t)) hF₁c
    (L.continuous.comp (continuous_const.prodMk continuous_id)) (by
      intro t
      rw [← hĜ1, hLp])
  have h1 := hk 1
  have h0 := hk 0
  have e1 := hLshift 1 0
  rw [zero_add] at e1
  have : (n₁ : ℝ) = n₀ := by
    have := hs₁ 0
    rw [zero_add] at this
    linarith
  exact_mod_cast this.symm

end GC.LongTime.CuspP1
