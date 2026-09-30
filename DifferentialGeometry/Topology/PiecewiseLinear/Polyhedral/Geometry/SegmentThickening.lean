import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.FinitePolyhedra

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry
open scoped Pointwise

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem segment_thickening_subset_affineSpan {s : Finset E} {a : E} (ha : a ∈ s)
    (v : E) (R : ℝ) :
    convexHull ℝ (s : Set E) + segment ℝ (-R • v) (R • v) ⊆
      affineSpan ℝ ((insert (a + v) s : Finset E) : Set E) := by
  let P := affineSpan ℝ ((insert (a + v) s : Finset E) : Set E)
  have hsP : (s : Set E) ⊆ P := fun x hx => subset_affineSpan ℝ _ (Finset.mem_insert_of_mem hx)
  have haP : a ∈ P := hsP ha
  have havP : a + v ∈ P := subset_affineSpan ℝ _ (Finset.mem_insert_self _ _)
  have hv : v ∈ P.direction := by
    have h := P.vsub_mem_direction havP haP
    simpa only [vsub_eq_sub, add_sub_cancel_left] using h
  have hline : segment ℝ (-R • v) (R • v) ⊆ P.direction :=
    (Submodule.convex P.direction).segment_subset (P.direction.smul_mem (-R) hv)
      (P.direction.smul_mem R hv)
  rintro x ⟨y, hy, z, hz, rfl⟩
  have hyP : y ∈ P := convexHull_min hsP P.convex hy
  change y + z ∈ P
  simpa only [vadd_eq_add, add_comm] using P.vadd_mem_of_mem_direction (hline hz) hyP

omit [DecidableEq E] in
theorem exists_complex_segment_thickening (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) (v : E) (R : ℝ) :
    ∃ T : SimplicialComplex ℝ E, T.faces.Finite ∧
      T.space = K.space + segment ℝ (-R • v) (R • v) ∧
      (∀ s ∈ T.faces, s.card ≤ d + 2) ∧
      ∀ s ∈ T.faces, ∃ t ∈ K.faces,
        convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) + segment ℝ (-R • v) (R • v) := by
  classical
  let : Fintype K.faces := hK.fintype
  let V : K.faces → Finset E := fun s =>
    (s.1.finite_toSet.add ((finite_singleton (R • v)).insert (-R • v))).toFinset
  have hV (s : K.faces) : convexHull ℝ (V s : Set E) =
      convexHull ℝ (s.1 : Set E) + segment ℝ (-R • v) (R • v) := by
    rw [show (V s : Set E) = (s.1 : Set E) + {-R • v, R • v} from Set.Finite.coe_toFinset _]
    rw [convexHull_add, convexHull_pair]
  obtain ⟨T, hT, hspace, hfaces⟩ := exists_complex_finite_convexHulls V
  have href : ∀ s ∈ T.faces, ∃ t ∈ K.faces,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) + segment ℝ (-R • v) (R • v) := by
    intro s hs
    obtain ⟨t, ht⟩ := hfaces s hs
    exact ⟨t.1, t.2, (hV t) ▸ ht⟩
  refine ⟨T, hT, ?_, ?_, href⟩
  · rw [hspace]
    simp_rw [hV]
    ext x
    constructor
    · intro hx
      obtain ⟨s, y, hy, z, hz, heq⟩ := mem_iUnion.mp hx
      exact ⟨y, K.convexHull_subset_space s.2 hy, z, hz, heq⟩
    · rintro ⟨y, hy, z, hz, heq⟩
      obtain ⟨s, hs, hys⟩ := SimplicialComplex.mem_space_iff.mp hy
      exact mem_iUnion.mpr ⟨⟨s, hs⟩, y, hys, z, hz, heq⟩
  · intro s hs
    obtain ⟨t, ht, hst⟩ := href s hs
    obtain ⟨a, ha⟩ := K.nonempty_of_mem_faces ht
    have hspan := (subset_convexHull ℝ (s : Set E)).trans
      (hst.trans (segment_thickening_subset_affineSpan ha v R))
    have hcard := (T.indep hs).card_le_card_of_subset_affineSpan hspan
    exact hcard.trans ((Finset.card_insert_le _ _).trans (by have := hd t ht; omega))

end DifferentialGeometry.Topology.Engulfing
