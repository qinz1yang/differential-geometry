import DifferentialGeometry.Analysis.InnerProductSpace.BufferedSectionGraphJets


set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis
universe u v

theorem exists_uniform_buffered_section_graph_family
    (C : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (ι : Type v) (L : ι → Submodule ℝ H) [∀ i, CompleteSpace (L i)]
        (b : ℝ) (r : ι → ℝ) (o : ι → H) (U : Set H)
        (η : H → H) (Q : H → Submodule ℝ H)
        [∀ z, (Q z).HasOrthogonalProjection] (δ : ℝ),
        1 ≤ b → (∀ i, 0 < r i) → 0 < δ → δ ≤ δ₀ →
        (∀ i, ball (o i) (8 * b * r i) ⊆ U) →
        (∀ i, ContDiffOn ℝ ∞ η (ball (o i) (8 * b * r i))) →
        (∀ i, ∀ z ∈ ball (o i) (8 * b * r i), η z ∈ Q z) →
        (∀ i, ∀ z ∈ ball (o i) (8 * b * r i),
          ‖(Q z).starProjection - (L i)ᗮ.starProjection‖ < 1) →
        (∀ i m j, j ≤ m → ∀ z ∈ ball (o i) (8 * b * r i),
          ‖iteratedFDeriv ℝ j (fun y => η y - (L i)ᗮ.starProjection (y - o i)) z‖ ≤
            C m * δ * r i * ((r i)⁻¹) ^ j) →
        ∃ g : ∀ i, L i → (L i)ᗮ, ∀ i,
          ContDiffOn ℝ ∞ (g i) (ball 0 (4 * b * r i)) ∧
          (∀ t ∈ ball (0 : L i) (4 * b * r i), ‖g i t‖ ≤ r i / 4 ∧
            o i + orthogonalCoordinateSum (L i) (t, g i t) ∈
              {z : H | z ∈ U ∧ η z = 0}) ∧
          (∀ t ∈ ball (0 : L i) (4 * b * r i), ∀ n ∈ closedBall (0 : (L i)ᗮ) (r i),
            η (o i + orthogonalCoordinateSum (L i) (t, n)) = 0 ↔ n = g i t) ∧
          (∀ m t, t ∈ ball (0 : L i) (4 * b * r i) → ∀ j, j ≤ m →
            ‖iteratedFDeriv ℝ j (g i) t‖ ≤ F m * δ * r i * ((r i)⁻¹) ^ j) ∧
          {z : H | z ∈ U ∧ η z = 0} ∩ ball (o i) (3 * b * r i) =
            {z : H | ∃ t ∈ ball (0 : L i) (4 * b * r i),
              z = o i + orthogonalCoordinateSum (L i) (t, g i t)} ∩
                ball (o i) (3 * b * r i) := by
  obtain ⟨δ₀, hδ₀, F, hF, hengine⟩ :=
    exists_uniform_buffered_section_graph_jets.{u} C hC
  refine ⟨δ₀, hδ₀, F, hF, ?_⟩
  intro H _ _ _ ι L _ b r o U η Q _ δ hb hr hδ hδsmall hU hη hmem hgap hjets
  have hexists (i : ι) := hengine H (L i) b (r i) (o i) η Q δ hb (hr i)
    hδ hδsmall (hη i) (hmem i) (hgap i) (hjets i)
  let g : ∀ i, L i → (L i)ᗮ := fun i => Classical.choose (hexists i)
  refine ⟨g, ?_⟩
  intro i
  have hgi := Classical.choose_spec (hexists i)
  have hgraphU (t : L i) (ht : t ∈ ball (0 : L i) (4 * b * r i)) :
      o i + orthogonalCoordinateSum (L i) (t, g i t) ∈ U := by
    apply hU i
    have htbound : ‖t‖ < 4 * b * r i := by
      simpa only [mem_ball, dist_zero_right] using ht
    have hgbound : ‖g i t‖ ≤ r i / 4 := (hgi.2.1 t ht).1
    have hbr : r i ≤ b * r i := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (hr i).le
    change dist (o i + ((t : H) + (g i t : H))) (o i) < 8 * b * r i
    rw [dist_eq_norm]
    have hsub : o i + ((t : H) + (g i t : H)) - o i = (t : H) + (g i t : H) := by
      abel
    rw [hsub]
    have hsum := norm_add_le (t : H) (g i t : H)
    change ‖(t : H) + (g i t : H)‖ ≤ ‖t‖ + ‖g i t‖ at hsum
    nlinarith [hr i]
  refine ⟨hgi.1, ?_, hgi.2.2.1, hgi.2.2.2.1, ?_⟩
  · intro t ht
    exact ⟨(hgi.2.1 t ht).1, hgraphU t ht, (hgi.2.1 t ht).2⟩
  · ext z
    constructor
    · rintro ⟨⟨_, hz⟩, hball⟩
      exact (Set.ext_iff.mp hgi.2.2.2.2 z).mp ⟨hz, hball⟩
    · intro hz
      have hzero : η z = 0 := ((Set.ext_iff.mp hgi.2.2.2.2 z).mpr hz).1
      obtain ⟨⟨t, ht, heq⟩, hball⟩ := hz
      refine ⟨⟨?_, hzero⟩, hball⟩
      rw [heq]
      exact hgraphU t ht

end DifferentialGeometry.Analysis
