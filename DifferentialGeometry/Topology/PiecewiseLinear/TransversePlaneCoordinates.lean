import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

open Module

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem exists_ker_eq_of_finrank_succ_eq {N : Submodule ℝ E}
    (hN : Module.finrank ℝ N + 1 = Module.finrank ℝ E) :
    ∃ f : E →ₗ[ℝ] ℝ, LinearMap.ker f = N := by
  have hlt : N < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => ?_
    rw [h, finrank_top] at hN
    omega
  obtain ⟨f, hf0, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hle : N ≤ LinearMap.ker f := by
    intro y hy
    have hmem : f y ∈ Submodule.map f N := ⟨y, hy, rfl⟩
    rw [hfmap] at hmem
    simpa using hmem
  have hker : LinearMap.ker f ≠ ⊤ := fun h => hf0 (LinearMap.ker_eq_top.mp h)
  have h1 : Module.finrank ℝ (LinearMap.ker f) < Module.finrank ℝ E := Submodule.finrank_lt hker
  have h2 : Module.finrank ℝ N ≤ Module.finrank ℝ (LinearMap.ker f) := Submodule.finrank_mono hle
  exact ⟨f, (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm⟩

theorem exists_linearEquiv_of_transverse_planes {P Q : Submodule ℝ E}
    (hP : Module.finrank ℝ P = 2) (hQ : Module.finrank ℝ Q = 2)
    (hPQ : Module.finrank ℝ (P ⊓ Q : Submodule ℝ E) = 1) (hsup : P ⊔ Q = ⊤) :
    ∃ L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ,
      (∀ y : E, y ∈ P ↔ (L y).2.2 = 0) ∧ (∀ y : E, y ∈ Q ↔ (L y).2.1 = 0) := by
  have hdim : Module.finrank ℝ E = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
    rw [hsup, finrank_top, hP, hQ, hPQ] at h
    omega
  obtain ⟨β, hβ⟩ := exists_ker_eq_of_finrank_succ_eq (N := P) (by omega)
  obtain ⟨γ, hγ⟩ := exists_ker_eq_of_finrank_succ_eq (N := Q) (by omega)
  have hne : (P ⊓ Q : Submodule ℝ E) ≠ ⊥ := by
    intro h
    rw [h] at hPQ
    simp at hPQ
  obtain ⟨u, huPQ, hu0⟩ := (P ⊓ Q : Submodule ℝ E).ne_bot_iff.mp hne
  obtain ⟨α, hα⟩ := Module.Projective.exists_dual_ne_zero ℝ hu0
  have hspan : Submodule.span ℝ {u} = (P ⊓ Q : Submodule ℝ E) := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rwa [Submodule.span_singleton_le_iff_mem]
    · rw [hPQ, finrank_span_singleton hu0]
  have hinj : Function.Injective (α.prod (γ.prod β)) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    have hy' : (α.prod (γ.prod β)) y = 0 := hy
    have hαy : α y = 0 := congrArg Prod.fst hy'
    have hγy : γ y = 0 := congrArg (fun z : ℝ × ℝ × ℝ => z.2.1) hy'
    have hβy : β y = 0 := congrArg (fun z : ℝ × ℝ × ℝ => z.2.2) hy'
    have hmem : y ∈ Submodule.span ℝ {u} := by
      rw [hspan]
      exact ⟨hβ ▸ hβy, hγ ▸ hγy⟩
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    rw [← ht, map_smul, smul_eq_mul] at hαy
    rcases mul_eq_zero.mp hαy with h | h
    · rw [← ht, h, zero_smul]
    · exact absurd h hα
  have hdim3 : Module.finrank ℝ (ℝ × ℝ × ℝ) = 3 := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self]
  have hbij : Function.Bijective (α.prod (γ.prod β)) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hdim, hdim3])).mp hinj⟩
  refine ⟨LinearEquiv.ofBijective (α.prod (γ.prod β)) hbij, fun y => ?_, fun y => ?_⟩
  · change y ∈ P ↔ β y = 0
    rw [← hβ]
    exact LinearMap.mem_ker
  · change y ∈ Q ↔ γ y = 0
    rw [← hγ]
    exact LinearMap.mem_ker

omit [FiniteDimensional ℝ E] in
theorem mem_inf_iff_of_linearEquiv_of_transverse_planes {P Q : Submodule ℝ E}
    {L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ} (hPL : ∀ y : E, y ∈ P ↔ (L y).2.2 = 0)
    (hQL : ∀ y : E, y ∈ Q ↔ (L y).2.1 = 0) (y : E) :
    y ∈ (P ⊓ Q : Submodule ℝ E) ↔ (L y).2 = 0 := by
  rw [Submodule.mem_inf, hPL y, hQL y]
  constructor
  · rintro ⟨h1, h2⟩
    exact Prod.ext h2 h1
  · intro h
    exact ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩

end DifferentialGeometry.Topology.PiecewiseLinear
