import DifferentialGeometry.Topology.Cobordism.HCobordism
import DifferentialGeometry.Topology.Morse.Strip.ModelTransport
import DifferentialGeometry.Topology.Cobordism.HomotopySphere
import DifferentialGeometry.Topology.HighDimensional.TwistedSphere
import DifferentialGeometry.Topology.HighDimensional.PoincareHighDim

namespace DifferentialGeometry.Topology

open scoped _root_.Manifold ContDiff ContinuousMap
open Metric Set _root_.Topology

theorem poincare_smooth_ge6 {n : ℕ} (h6 : 6 ≤ n) {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin (m + 1 + 1))) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  have : Nonempty M := nonempty_of_homotopyEquiv e
  obtain ⟨e₀, e₁, f, h₀, h₁, hdisj, hf, hIic, hIci, hIio, hIoi, hm, hp, hreg⟩ :=
    exists_chartDisks_and_strip (M := M) (n := m + 1) (by omega : 1 ≤ m + 1)
  obtain ⟨hW, hH⟩ :=
    hcobordism_input_of_homotopy_sphere (by omega : 3 ≤ m + 1) e h₀ h₁ hdisj
  have hS₀ := h₀.simplyConnectedSpace_image_diskSphere (by omega : 3 ≤ m + 1)
  have hS₁ := h₁.simplyConnectedSpace_image_diskSphere (by omega : 3 ≤ m + 1)
  have hstrip : (e₀ '' diskInterior (m + 1) ∪ e₁ '' diskInterior (m + 1))ᶜ =
      f ⁻¹' Icc (-1/2) (1/2) := by
    rw [← hIio, ← hIoi]
    ext x
    simp only [mem_compl_iff, mem_union, mem_preimage, mem_Iio, mem_Ioi, mem_Icc, not_or,
      not_lt]
  rw [hstrip] at hW hH
  rw [← hm] at hS₀ hH
  rw [← hp] at hS₁
  have hf' : ContMDiff (morseModelI (m + 1)) 𝓘(ℝ, ℝ) ∞ f :=
    contMDiff_morseModelI_iff.mpr hf
  have hcompact : IsCompact (f ⁻¹' Icc (-1/2) (1/2)) :=
    (isClosed_Icc.preimage hf.continuous).isCompact
  have hreg' : ∀ x, f x = -1/2 ∨ f x = 1/2 → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt (morseModelI (m + 1)) f x := by
    intro x hx
    rw [isCriticalPointAt_morseModelI_iff hf]
    exact hreg x hx
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ := hcobordism_strip (morseModelI (m + 1)) (by omega : 6 ≤ m + 1)
    f hf' (by norm_num : (-1/2 : ℝ) < 1/2) hcompact hreg' hW hS₀ hS₁ hH
  let e₀' : Disk (m + 1) → M := Φ ∘ e₀
  have h₀' : IsClosedEmbedding e₀' :=
    Φ.toHomeomorph.isClosedEmbedding.comp h₀.isClosedEmbedding
  have hrange₀ : range e₀' = f ⁻¹' Iic (1/2) := by
    change range (Φ ∘ e₀) = _
    rw [range_comp, ← hIic, hΦ₁]
  have hsph₀ : e₀' '' diskSphere (m + 1) = f ⁻¹' {1/2} := by
    change (Φ ∘ e₀) '' diskSphere (m + 1) = _
    rw [image_comp, ← hm, hΦ₂]
  have hcover : range e₀' ∪ range e₁ = univ := by
    rw [hrange₀, ← hIci]
    ext x
    simp only [mem_union, mem_preimage, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total _ _
  have hinter : range e₀' ∩ range e₁ = e₀' '' diskSphere (m + 1) := by
    rw [hrange₀, ← hIci, hsph₀]
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ici, mem_singleton_iff]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
  have hbdry : e₀' '' diskSphere (m + 1) = e₁ '' diskSphere (m + 1) := by
    rw [hsph₀, hp]
  exact twisted_sphere_homeomorph h₀' h₁.isClosedEmbedding hcover hinter hbdry

theorem poincare_smooth {n : ℕ} (h5 : 5 ≤ n) {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  exact poincare_high_dim_topological h5 e

end DifferentialGeometry.Topology
