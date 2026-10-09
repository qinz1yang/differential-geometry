/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.VertexBranchChartPair
import DifferentialGeometry.Topology.PiecewiseLinear.BranchSignChain

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_arcChartChain_of_imageContract
    (M N : Geometry.SimplicialComplex ℝ E) {n : ℕ} (v : Fin (n + 1) → E)
    (hvertex : ∀ i : Fin (n + 1), ∃ (N₁ : Geometry.SimplicialComplex ℝ (ℝ × ℝ × ℝ))
      (φ : E → ℝ × ℝ × ℝ) (a₁ b₁ : ℝ × ℝ × ℝ) (U₀ : Set E) (V₀ : Set (ℝ × ℝ × ℝ))
      (Ψ : E → ℝ × ℝ × ℝ),
      a₁ ≠ b₁ ∧
      (SimplicialComplex.geometricLink N₁ {φ (v i)}).space ∩
          {x : ℝ × ℝ × ℝ | x.2.2 = (φ (v i)).2.2} = {a₁, b₁} ∧
      (∃ x ∈ (SimplicialComplex.geometricLink N₁ {φ (v i)}).space, (φ (v i)).2.2 < x.2.2) ∧
      (∃ x ∈ (SimplicialComplex.geometricLink N₁ {φ (v i)}).space, x.2.2 < (φ (v i)).2.2) ∧
      IsOpen U₀ ∧ v i ∈ U₀ ∧ IsPLHomeomorphOn Ψ U₀ V₀ ∧ Ψ (v i) = 0 ∧
      ∀ᶠ y in 𝓝 (v i), (y ∈ M.space → (Ψ y).2.1 = 0) ∧ (y ∈ N.space → (Ψ y).2.2 = 0))
    (τ : Fin n → ZMod 2) :
    ∃ (N₁ : Fin (n + 1) → Geometry.SimplicialComplex ℝ (ℝ × ℝ × ℝ))
      (φ : Fin (n + 1) → E → ℝ × ℝ × ℝ) (a₁ b₁ side : Fin (n + 1) → ℝ × ℝ × ℝ)
      (U : Fin (n + 1) → Set E) (V : Fin (n + 1) → Set (ℝ × ℝ × ℝ))
      (Ψ : Fin (n + 1) → E → ℝ × ℝ × ℝ) (ε : Fin (n + 1) → ZMod 2),
      (∀ i, a₁ i ≠ b₁ i) ∧
      (∀ i, (SimplicialComplex.geometricLink (N₁ i) {φ i (v i)}).space ∩
          {x : ℝ × ℝ × ℝ | x.2.2 = (φ i (v i)).2.2} = {a₁ i, b₁ i}) ∧
      (∀ i, side i = if ε i = 0 then a₁ i else b₁ i) ∧
      (∀ i, side i ∈ (SimplicialComplex.geometricLink (N₁ i) {φ i (v i)}).space ∩
          {x : ℝ × ℝ × ℝ | x.2.2 = (φ i (v i)).2.2}) ∧
      (∀ i, IsOpen (U i)) ∧ (∀ i, v i ∈ U i) ∧ (∀ i, IsPLHomeomorphOn (Ψ i) (U i) (V i)) ∧
      (∀ i, Ψ i (v i) = 0) ∧
      (∀ i, ∀ᶠ y in 𝓝 (v i), (y ∈ M.space → (Ψ i y).2.1 = 0) ∧
        (y ∈ N.space → (Ψ i y).2.2 = 0)) ∧
      (∀ i : Fin n, ε i.succ = ε i.castSucc + τ i) := by
  choose N₁ φ a₁ b₁ U V Ψ hne hlevel _hpos _hneg hUopen hvU hPL hΨ0 hnear using hvertex
  obtain ⟨ε, hε⟩ := exists_sideChoice_of_chain τ
  refine ⟨N₁, φ, a₁, b₁, fun i => if ε i = 0 then a₁ i else b₁ i, U, V, Ψ, ε, hne, hlevel,
    fun i => rfl, fun i => ?_, hUopen, hvU, hPL, hΨ0, hnear, hε⟩
  rw [hlevel i]
  by_cases hεi : ε i = 0 <;> simp [hεi]

end DifferentialGeometry.Topology.PiecewiseLinear
