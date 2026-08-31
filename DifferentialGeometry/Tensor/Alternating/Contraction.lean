import DifferentialGeometry.Tensor.Alternating.Curry
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Tactic

noncomputable section

open scoped BigOperators

namespace AlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private lemma skew_two (ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ) (u v : E) : ω ![v, u] = -ω ![u, v] := by
  simpa using ω.map_swap (v := ![u, v]) (i := (0 : Fin 2)) (j := 1) (by decide)

private lemma diag_two (ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ) (u : E) : ω ![u, u] = 0 := by
  exact ω.map_eq_zero_of_eq ![u, u] rfl (i := (0 : Fin 2)) (j := 1) (by decide)

private lemma basis_zero_of_coeff (ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ) (B : Module.Basis (Fin 3) ℝ E)
    (h : ∀ i j : Fin 3, ω ![B i, B j] = 0) : ω = 0 := by
  apply Module.Basis.ext_alternating B
  intro v hv
  have h' := h (v 0) (v 1)
  have hv' : (fun i => B (v i)) = ![B (v 0), B (v 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv']
  exact h'

private lemma kernel_vec (ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ) (B : Module.Basis (Fin 3) ℝ E) :
    ω.curryLeft (ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2) = 0 := by
  have h00 := diag_two ω (B 0)
  have h11 := diag_two ω (B 1)
  have h22 := diag_two ω (B 2)
  have h10 := skew_two ω (B 0) (B 1)
  have h20 := skew_two ω (B 0) (B 2)
  have h21 := skew_two ω (B 1) (B 2)
  apply Module.Basis.ext_alternating B
  intro v hv
  have hv' : v = ![v 0] := by
    funext i
    fin_cases i
    rfl
  rw [hv']
  have hv0 : v 0 = 0 ∨ v 0 = 1 ∨ v 0 = 2 := by omega
  rcases hv0 with hv0 | hv0 | hv0 <;> rw [hv0] at hv' <;> rw [hv']
  all_goals simp only [AlternatingMap.curryLeft_apply_apply, AlternatingMap.zero_apply]
  · have hargs : Matrix.vecCons
        (ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2)
        (fun i => B (![![0] 0] i)) =
        ![ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2,
          B 0] := by
      funext i
      fin_cases i <;> rfl
    rw [hargs]
    change ω (Matrix.vecCons
      (ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2) ![B 0]) = 0
    rw [ω.map_vecCons_add, ω.map_vecCons_add, ω.map_vecCons_smul,
      ω.map_vecCons_smul, ω.map_vecCons_smul]
    simp only [h00, h10, h20, smul_eq_mul]
    ring
  · have hargs : Matrix.vecCons
        (ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2)
        (fun i => B (![![1] 0] i)) =
        ![ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2,
          B 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hargs]
    change ω (Matrix.vecCons
      (ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2) ![B 1]) = 0
    rw [ω.map_vecCons_add, ω.map_vecCons_add, ω.map_vecCons_smul,
      ω.map_vecCons_smul, ω.map_vecCons_smul]
    simp only [h11, h21, smul_eq_mul]
    ring
  · have hargs : Matrix.vecCons
        (ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2)
        (fun i => B (![![2] 0] i)) =
        ![ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2,
          B 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hargs]
    change ω (Matrix.vecCons
      (ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2) ![B 2]) = 0
    rw [ω.map_vecCons_add, ω.map_vecCons_add, ω.map_vecCons_smul,
      ω.map_vecCons_smul, ω.map_vecCons_smul]
    simp only [h22, h20, smul_eq_mul]
    ring

theorem finrank_ker_curryLeft_eq_one [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 3)
    {ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ} (hω : ω ≠ 0) :
    Module.finrank ℝ ω.curryLeft.ker = 1 := by
  let B := Module.finBasisOfFinrankEq ℝ E hE
  have hω' : ¬ ∀ z : Fin 2 → E, ω z = 0 := by
    intro hz
    apply hω
    ext z
    exact hz z
  obtain ⟨z, hz⟩ := Classical.not_forall.mp hω'
  let u := z 0
  let v := z 1
  have hz' : z = ![u, v] := by
    funext i
    fin_cases i <;> rfl
  have huv : ω ![u, v] ≠ 0 := by simpa [hz'] using hz
  have hlin : LinearIndependent ℝ (fun i : Fin 2 => ω.curryLeft (![u, v] i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    fin_cases i
    · have hc' := congrArg (fun α : E [⋀^Fin 1]→ₗ[ℝ] ℝ => α ![v]) hc
      simp only [Fin.sum_univ_two, AlternatingMap.add_apply, AlternatingMap.smul_apply,
        AlternatingMap.zero_apply, AlternatingMap.curryLeft_apply_apply] at hc'
      have hvv := diag_two ω v
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hvv, smul_eq_mul, mul_zero,
        add_zero] at hc'
      exact (mul_eq_zero.mp hc').resolve_right huv
    · have hc' := congrArg (fun α : E [⋀^Fin 1]→ₗ[ℝ] ℝ => α ![u]) hc
      simp only [Fin.sum_univ_two, AlternatingMap.add_apply, AlternatingMap.smul_apply,
        AlternatingMap.zero_apply, AlternatingMap.curryLeft_apply_apply] at hc'
      have huu := diag_two ω u
      have hvu := skew_two ω u v
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, huu, hvu, smul_eq_mul, mul_zero,
        zero_add] at hc'
      exact (mul_eq_zero.mp hc').resolve_right (neg_ne_zero.mpr huv)
  let g : Fin 2 → ω.curryLeft.range :=
    fun i => ⟨ω.curryLeft (![u, v] i), ⟨![u, v] i, rfl⟩⟩
  have hg : LinearIndependent ℝ g := by
    apply LinearIndependent.of_comp (ω.curryLeft.range.subtype)
    simpa [g, Function.comp_def] using hlin
  have hspan : Module.finrank ℝ (Submodule.span ℝ (Set.range g)) = 2 := by
    simpa using finrank_span_eq_card hg
  have hmono : Module.finrank ℝ (Submodule.span ℝ (Set.range g)) ≤
      Module.finrank ℝ (ω.curryLeft.range : Type _) :=
    (Submodule.span ℝ (Set.range g)).finrank_le
  have hrange : 2 ≤ Module.finrank ℝ ω.curryLeft.range := by omega
  have hker : ω.curryLeft.ker ≠ ⊥ := by
    intro hbot
    let w := ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2
    have hwker : w ∈ ω.curryLeft.ker := by
      rw [LinearMap.mem_ker]
      exact kernel_vec ω B
    have hwzero : w = 0 := by
      have : w ∈ (⊥ : Submodule ℝ E) := hbot ▸ hwker
      simpa using this
    have hc0 := congrArg (fun x : E => B.repr x 0) hwzero
    have hc1 := congrArg (fun x : E => B.repr x 1) hwzero
    have hc2 := congrArg (fun x : E => B.repr x 2) hwzero
    have h12 : ω ![B 1, B 2] = 0 := by
      simpa [w, B.repr_self_apply] using hc0
    have h20 : ω ![B 2, B 0] = 0 := by
      simpa [w, B.repr_self_apply] using hc1
    have h01 : ω ![B 0, B 1] = 0 := by
      simpa [w, B.repr_self_apply] using hc2
    apply hω
    apply basis_zero_of_coeff ω B
    intro i j
    fin_cases i <;> fin_cases j
    all_goals simp [diag_two, skew_two, h12, h20, h01]
  have hsum := ω.curryLeft.finrank_range_add_finrank_ker
  have hker_pos : 1 ≤ Module.finrank ℝ (ω.curryLeft.ker : Type _) :=
    (Submodule.one_le_finrank_iff).2 hker
  rw [hE] at hsum
  omega

end AlternatingMap
