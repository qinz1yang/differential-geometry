import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Module

noncomputable section

namespace DifferentialGeometry.Geometry.Affine

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem exists_affineEquiv_of_injective_of_two_directions
    (hW : Module.finrank K W = 2)
    (h : V → W) (hh : Function.Injective h) (u v : V)
    (huv : LinearIndependent K ![u, v])
    (hu : ∀ (x : V) (t : K), h (x + t • u) = h x + t • (h (x + u) - h x))
    (hv : ∀ (x : V) (t : K), h (x + t • v) = h x + t • (h (x + v) - h x)) :
    ∃ e : V ≃ᵃ[K] W, ∀ x, e x = h x := by
  let D := h 0
  let B := h u - D
  let C := h v - D
  let A := h (u + v) - h u - h v + D
  have haxis_u (s : K) : h (s • u) = D + s • B := by
    simpa only [zero_add] using hu 0 s
  have haxis_v (t : K) : h (t • v) = D + t • C := by
    simpa only [zero_add] using hv 0 t
  have hexp (s t : K) : h (s • u + t • v) = D + s • B + t • C + (s * t) • A := by
    calc
      h (s • u + t • v) = h (t • v) + s • (h (u + t • v) - h (t • v)) := by
        simpa only [add_comm] using hu (t • v) s
      _ = D + s • B + t • C + (s * t) • A := by
        rw [haxis_v, hv]
        dsimp only [D, B, C, A]
        module
  have huv' : v ≠ 0 ∧ ∀ a : K, a • v ≠ u := by
    simpa using linearIndependent_fin2.mp huv
  have hBC : LinearIndependent K ![B, C] := by
    apply linearIndependent_fin2.mpr
    change C ≠ 0 ∧ ∀ a : K, a • C ≠ B
    constructor
    · intro hC
      apply huv'.1
      apply hh
      exact sub_eq_zero.mp hC
    · intro a ha
      apply huv'.2 a
      apply hh
      rw [haxis_v, ha]
      dsimp only [D, B]
      abel
  let c : Module.Basis (Fin 2) K W := basisOfLinearIndependentOfCardEqFinrank hBC (by simp [hW])
  have hc0 : c 0 = B := by simp [c]
  have hc1 : c 1 = C := by simp [c]
  let a := c.repr A 0
  let b := c.repr A 1
  have hA : A = a • B + b • C := by
    simpa only [Fin.sum_univ_two, hc0, hc1] using (c.sum_repr A).symm
  have ha : a = 0 := by
    by_contra ha
    have hmul : (-a⁻¹) * a = -1 := by simp [ha]
    have heq : h (u + (-a⁻¹) • v) = h (((-a⁻¹) + (-a⁻¹) * b) • v) := by
      calc
        h (u + (-a⁻¹) • v) = D + B + (-a⁻¹) • C + (-a⁻¹) • A := by
          simpa using hexp 1 (-a⁻¹)
        _ = D + ((-a⁻¹) + (-a⁻¹) * b) • C := by
          rw [hA, smul_add, smul_smul, smul_smul, hmul]
          module
        _ = _ := (haxis_v _).symm
    have heq' := hh heq
    apply huv'.2 ((-a⁻¹) * b)
    calc
      ((-a⁻¹) * b) • v = ((-a⁻¹) + (-a⁻¹) * b) • v - (-a⁻¹) • v := by module
      _ = u := by rw [← heq']; abel
  have hb : b = 0 := by
    by_contra hb
    have hmul : (-b⁻¹) * b = -1 := by simp [hb]
    have hA' : A = b • C := by simpa only [ha, zero_smul, zero_add] using hA
    have heq : h ((-b⁻¹) • u + v) = h ((-b⁻¹) • u) := by
      calc
        h ((-b⁻¹) • u + v) = D + (-b⁻¹) • B + C + (-b⁻¹) • A := by
          simpa using hexp (-b⁻¹) 1
        _ = D + (-b⁻¹) • B := by
          rw [hA', smul_smul, hmul]
          module
        _ = _ := (haxis_u _).symm
    exact huv'.1 (add_eq_left.mp (hh heq))
  have hA0 : A = 0 := by simpa only [ha, hb, zero_smul, add_zero] using hA
  have hspan : ⊤ ≤ Submodule.span K (Set.range ![u, v]) := by
    intro x _
    let s := c.repr (h x - D) 0
    let t := c.repr (h x - D) 1
    have hcoord : s • B + t • C = h x - D := by
      simpa only [Fin.sum_univ_two, hc0, hc1] using c.sum_repr (h x - D)
    have heq : h (s • u + t • v) = h x := by
      rw [hexp, hA0, smul_zero, add_zero]
      calc
        D + s • B + t • C = D + (s • B + t • C) := by abel
        _ = D + (h x - D) := by rw [hcoord]
        _ = h x := by abel
    rw [← hh heq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ s (Submodule.subset_span ⟨0, by simp⟩))
      (Submodule.smul_mem _ t (Submodule.subset_span ⟨1, by simp⟩))
  let d : Module.Basis (Fin 2) K V := Module.Basis.mk huv hspan
  have hd0 : d 0 = u := by simp [d]
  have hd1 : d 1 = v := by simp [d]
  let L : V ≃ₗ[K] W := d.equiv c (Equiv.refl (Fin 2))
  have hLu : L u = B := by
    simpa only [hd0, hc0, Equiv.refl_apply] using d.equiv_apply 0 c (Equiv.refl (Fin 2))
  have hLv : L v = C := by
    simpa only [hd1, hc1, Equiv.refl_apply] using d.equiv_apply 1 c (Equiv.refl (Fin 2))
  have hform (x : V) : h x = L x + h 0 := by
    have hx : d.repr x 0 • u + d.repr x 1 • v = x := by
      simpa only [Fin.sum_univ_two, hd0, hd1] using d.sum_repr x
    rw [← hx, hexp, map_add, map_smul, map_smul, hLu, hLv, hA0, smul_zero, add_zero]
    dsimp only [D]
    abel
  refine ⟨AffineEquiv.mk' h L 0 ?_, fun _ => rfl⟩
  intro x
  simpa only [vsub_eq_sub, sub_zero, vadd_eq_add] using hform x

end DifferentialGeometry.Geometry.Affine
