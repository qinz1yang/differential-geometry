/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.VertexBranchInput
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChartTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_transcription_of_transverse_vertex [DecidableEq E]
    (hn : Module.finrank ℝ E = 3)
    (K M N : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hM : M.faces ⊆ K.faces) (hN : N.faces ⊆ K.faces) {p : E}
    (hpM : {p} ∈ M.faces) (hpN : {p} ∈ N.faces) (hK : K.space ∈ 𝓝 p)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hlinkM : IsPLSphere 1 (SimplicialComplex.geometricLink M {p}).space)
    (hlinkN : IsPLSphere 1 (SimplicialComplex.geometricLink N {p}).space)
    {a b : E} (hab : a ≠ b)
    (hlevel : (SimplicialComplex.geometricLink M {p}).space ∩ {x | ℓ x = ℓ p} = {a, b})
    (hposM : ∃ x ∈ (SimplicialComplex.geometricLink M {p}).space, ℓ p < ℓ x)
    (hnegM : ∃ x ∈ (SimplicialComplex.geometricLink M {p}).space, ℓ x < ℓ p) :
    ∃ (K₁ N₁ : Geometry.SimplicialComplex ℝ (ℝ × ℝ × ℝ)) (φ : E → ℝ × ℝ × ℝ)
      (U : Set E) (W : Set (ℝ × ℝ × ℝ)),
      K₁.faces.Finite ∧ N₁.faces.Finite ∧ N₁.faces ⊆ K₁.faces ∧ φ p = 0 ∧
        ({φ p} : Finset (ℝ × ℝ × ℝ)) ∈ N₁.faces ∧ K₁.space ∈ 𝓝 (φ p) ∧
          IsPLSphere 1 (SimplicialComplex.geometricLink N₁ {φ p}).space ∧
            IsOpen U ∧ p ∈ U ∧ IsOpen W ∧ IsPLHomeomorphOn φ U W ∧
              (∀ᶠ y in 𝓝 p, y ∈ M.space → (φ y).2.2 = 0) ∧
                ∀ᶠ y in 𝓝 p, y ∈ N.space → φ y ∈ N₁.space := by
  classical
  obtain ⟨U, V, h₁, L₁, hU, hV, hpU, hPL₁, hh₁p, hnear₁⟩ :=
    exists_linearEquiv_normalForm_of_geometricLink_pair hn K M hM hpM hK ℓ hℓ hlinkM hab hlevel
      hposM hnegM
  have hWopen : IsOpen ((fun y => L₁ y) '' V) := by
    simpa using L₁.toContinuousLinearEquiv.toHomeomorph.isOpenMap V hV
  have hφhom : IsPLHomeomorphOn (fun y => L₁ (h₁ y)) U ((fun y => L₁ y) '' V) :=
    hPL₁.trans (isPLHomeomorphOn_linearEquiv L₁ hV)
  obtain ⟨hφpl, hφinj⟩ := isPiecewiseAffineOn_injOn_linearEquiv_comp hPL₁ L₁
  have hφp : L₁ (h₁ p) = 0 := by rw [hh₁p, map_zero]
  obtain ⟨R, K₁, M₁, N₁, hRK, hRfin, hpR, hstarU, hK₁fin, hM₁fin, hN₁fin, hMK₁, hNK₁, hpM₁,
    hpN₁, hK₁space, hM₁space, hN₁space, hlinkMmap, hlinkNmap⟩ :=
    exists_simplicialComplex_triple_image_closedStar_of_isPiecewiseAffineOn K M N hM hN hpM hpN
      (hU.mem_nhds hpU) hφpl hφinj
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite (restrict R N.space).faces := (restrict_faces_finite R N.space).to_subtype
  obtain ⟨gN, hgN⟩ := hlinkNmap
  have hlinkN₁ : IsPLSphere 1
      (SimplicialComplex.geometricLink N₁ {L₁ (h₁ p)}).space :=
    hlinkN.of_isPLHomeomorphOn hgN
  have hK₁nhds : K₁.space ∈ 𝓝 (L₁ (h₁ p)) := by
    rw [hK₁space]
    exact image_closedStar_mem_nhds_of_isPLHomeomorphOn R (by rw [hRK.space_eq]; exact hK)
      hWopen hφhom hpU
  have hB : ∀ᶠ y in 𝓝 p, y ∈ N.space → L₁ (h₁ y) ∈ N₁.space := by
    have hNspace : (restrict R N.space).space = N.space := (hRK.restrict N hN).space_eq
    have h := eventually_mem_image_closedStar_of_mem_space (restrict R N.space) p
      (fun y => L₁ (h₁ y))
    rw [hNspace] at h
    rw [hN₁space]
    exact h
  exact ⟨K₁, N₁, fun y => L₁ (h₁ y), U, (fun y => L₁ y) '' V, hK₁fin, hN₁fin, hNK₁, hφp, hpN₁,
    hK₁nhds, hlinkN₁, hU, hpU, hWopen, hφhom, hnear₁.mono fun y hy => hy.1, hB⟩

theorem exists_chart_two_sheets_of_transverse_vertex
    (K₁ N₁ : Geometry.SimplicialComplex ℝ (ℝ × ℝ × ℝ))
    (hK₁fin : K₁.faces.Finite) (hN₁fin : N₁.faces.Finite) (hNK₁ : N₁.faces ⊆ K₁.faces)
    {φ : E → ℝ × ℝ × ℝ} {p : E} (hφp : φ p = 0)
    (hpN₁ : ({φ p} : Finset (ℝ × ℝ × ℝ)) ∈ N₁.faces) (hK₁ : K₁.space ∈ 𝓝 (φ p))
    (hlinkN₁ : IsPLSphere 1 (SimplicialComplex.geometricLink N₁ {φ p}).space)
    {U : Set E} {W : Set (ℝ × ℝ × ℝ)} (hU : IsOpen U) (hpU : p ∈ U) (hW : IsOpen W)
    (hφ : IsPLHomeomorphOn φ U W) {A B : Set E}
    (hA : ∀ᶠ y in 𝓝 p, y ∈ A → (φ y).2.2 = 0)
    (hB : ∀ᶠ y in 𝓝 p, y ∈ B → φ y ∈ N₁.space)
    {a₁ b₁ : ℝ × ℝ × ℝ} (hab₁ : a₁ ≠ b₁)
    (hlevel₁ : (SimplicialComplex.geometricLink N₁ {φ p}).space ∩
      {x : ℝ × ℝ × ℝ | x.2.2 = (φ p).2.2} = {a₁, b₁})
    (hpos₁ : ∃ x ∈ (SimplicialComplex.geometricLink N₁ {φ p}).space, (φ p).2.2 < x.2.2)
    (hneg₁ : ∃ x ∈ (SimplicialComplex.geometricLink N₁ {φ p}).space, x.2.2 < (φ p).2.2) :
    ∃ (U₀ : Set E) (V₀ : Set (ℝ × ℝ × ℝ)) (Ψ : E → ℝ × ℝ × ℝ),
      IsOpen U₀ ∧ p ∈ U₀ ∧ IsPLHomeomorphOn Ψ U₀ V₀ ∧ Ψ p = 0 ∧
        ∀ᶠ y in 𝓝 p, (y ∈ A → (Ψ y).2.1 = 0) ∧ (y ∈ B → (Ψ y).2.2 = 0) := by
  let _ : Finite K₁.faces := hK₁fin.to_subtype
  let _ : Finite N₁.faces := hN₁fin.to_subtype
  obtain ⟨U₂, V₂, h₂, L₂, hU₂, hV₂, hqU₂, hPL₂, hh₂q, hnear₂⟩ :=
    exists_linearEquiv_normalForm_two_sheets K₁ N₁ hNK₁ hpN₁ hK₁ hlinkN₁ hab₁ hlevel₁ hpos₁ hneg₁
  rw [hφp] at hqU₂ hh₂q hnear₂
  obtain ⟨U₀, V₀, hU₀, hpU₀, hPLΨ, hΨp, hnearΨ⟩ :=
    exists_isPLHomeomorphOn_comp_two_sheets hU hpU hW hφ hφp hU₂ hV₂ hqU₂ hPL₂ hh₂q L₂ hA hB
      hnear₂
  exact ⟨U₀, V₀, _, hU₀, hpU₀, hPLΨ, hΨp, hnearΨ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
