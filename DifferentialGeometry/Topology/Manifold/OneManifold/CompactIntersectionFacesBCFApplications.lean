import DifferentialGeometry.Topology.Manifold.OneManifold.CompactIntersectionFacesBCF

/-!
# Consumer of the shared `K₃` kernel K1 (lane B-BCF134)

On the one-chart atlas of the real line, with `Kset = [0, 1]` and `C = [1/2, ∞)` (relative frontier
`{1/2}`, a half chart of `C` at `1/2` from `GraphAtlas1_BCF.halfChart_BCF`), K1 gives `K₃` and
`D₃ = K₃ ∩ C` with `[1/2, 1] ⊆ D₃`, and the new face `1/2 ∈ int K₃ ∩ ∂C` is a frontier point of `D₃`
(the second part of the face identity is non-empty).
-/

set_option autoImplicit false

open Set Function Filter Topology

namespace DifferentialGeometry.Topology

/-- The relative frontier of `[1/2, ∞)` in the line is `{1/2}`. -/
theorem relFrontier_Ici_half_BCF :
    Ici (1 / 2 : ℝ) \ Subtype.val '' interior (Subtype.val ⁻¹' Ici (1 / 2 : ℝ) : Set (univ : Set ℝ)) =
      {1 / 2} := by
  ext x
  constructor
  · rintro ⟨hx, hxI⟩
    rcases (mem_Ici.mp hx).lt_or_eq with h | h
    · exact absurd (mem_image_interior_preimage_val_iff.mpr
        ⟨mem_univ x, Ioi (1 / 2), isOpen_Ioi, h, fun z hz => mem_Ici.mpr hz.1.le⟩) hxI
    · exact h.symm
  · rintro rfl
    refine ⟨mem_Ici.mpr le_rfl, fun hI => ?_⟩
    obtain ⟨-, O, hO, hxO, hOC⟩ := mem_image_interior_preimage_val_iff.mp hI
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO _ hxO
    have hz : (1 / 2 - ε / 2 : ℝ) ∈ O := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith)
    have := mem_Ici.mp (hOC ⟨hz, mem_univ _⟩)
    linarith

/-- The half chart of `[1/2, ∞)` at `1/2` on the line atlas. -/
theorem exists_halfChart_Ici_half_BCF :
    ∃ d : HalfChart_BCF (univ : Set ℝ) (Ici (1 / 2 : ℝ)), (1 / 2 : ℝ) ∈ d.O := by
  have hTO : Ici (1 / 2 : ℝ) ∩ Ioo (-1 / 2) (3 / 2) =
      (fun t => lineGraphAtlas_BCF.param () (1 / 2 + 1 * t)) '' (Ioo (-1) 1 ∩ Ici 0) := by
    ext z
    constructor
    · rintro ⟨hz, hzO⟩
      refine ⟨z - 1 / 2, ⟨⟨by linarith [hzO.1], by linarith [hzO.2]⟩, ?_⟩, ?_⟩
      · exact mem_Ici.mpr (by linarith [mem_Ici.mp hz])
      · change 1 / 2 + 1 * (z - 1 / 2) = z
        ring
    · rintro ⟨t, ⟨ht, ht0⟩, rfl⟩
      change 1 / 2 + 1 * t ∈ Ici (1 / 2 : ℝ) ∩ Ioo (-1 / 2) (3 / 2)
      have := mem_Ici.mp ht0
      exact ⟨mem_Ici.mpr (by linarith), by linarith [ht.1], by linarith [ht.2]⟩
  exact ⟨lineGraphAtlas_BCF.halfChart_BCF () 1 (1 / 2) (one_mul 1) (Ioo (-1) 1) (Ioo (-1 / 2) (3 / 2))
    isOpen_Ioo (fun _ _ => mem_univ _) isOpen_Ioo hTO, by
      change (1 / 2 : ℝ) ∈ Ioo (-1 / 2) (3 / 2)
      constructor <;> norm_num⟩

/-- **Consumer of K1** on the line: `D₃ = K₃ ∩ [1/2, ∞)` contains `[1/2, 1]` and has the new face
`1/2` (an interior point of `K₃` on `∂C`) in its relative frontier. -/
theorem exists_compact_intersection_line_BCF :
    ∃ K D : SmoothCompactOneDomain_BCF (univ : Set ℝ), D.carrier = K.carrier ∩ Ici (1 / 2) ∧
      Icc (1 / 2 : ℝ) 1 ⊆ D.carrier ∧
      (1 / 2 : ℝ) ∈ D.carrier \ Subtype.val '' interior (Subtype.val ⁻¹' D.carrier : Set (univ : Set ℝ)) := by
  have hfr := relFrontier_Ici_half_BCF
  obtain ⟨K, D, hD, hcov, -, hface, -, -⟩ := lineGraphAtlas_BCF.exists_compact_intersection_faces_BCF
    (Kset := Icc 0 1) (C := Ici (1 / 2)) isCompact_Icc (subset_univ _)
    ⟨Ici (1 / 2), isClosed_Ici, (inter_univ _).symm⟩ (by rw [hfr]; exact finite_singleton _)
    (by
      rw [hfr]
      rintro y rfl
      exact exists_halfChart_Ici_half_BCF)
    (by rw [hfr]; rintro y rfl; constructor <;> norm_num)
  have hKsub : Icc (0 : ℝ) 1 ⊆ K.carrier := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hcov hx
    exact (interior_subset hy : y ∈ Subtype.val ⁻¹' K.carrier)
  refine ⟨K, D, hD, fun x hx => hD ▸ ⟨hKsub ⟨by linarith [hx.1], hx.2⟩, mem_Ici.mpr hx.1⟩, ?_⟩
  rw [hface, hfr]
  exact Or.inr ⟨hcov ⟨by norm_num, by norm_num⟩, rfl⟩

end DifferentialGeometry.Topology
