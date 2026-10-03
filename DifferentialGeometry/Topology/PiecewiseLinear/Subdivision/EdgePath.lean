import DifferentialGeometry.Topology.PiecewiseLinear.Piece.LocalFiniteness
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexComplex
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionEdgePath

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

open Classical in
theorem LocallyFinitePLPieceIn.exists_path_of_edge
    (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U) (hsub : IsSubdivision 𝒦'.complex 𝒦.complex)
    {x y : Ea} (hxy : x ≠ y) (hxyK : ({x, y} : Finset Ea) ∈ 𝒦.complex.faces) :
    ∃ (n : ℕ) (c : ℕ → ℝ), 0 < n ∧ c 0 = 0 ∧ c n = 1 ∧ StrictMonoOn c (Iic n) ∧
      (∀ i ≤ n, ({AffineMap.lineMap x y (c i)} : Finset Ea) ∈ 𝒦'.complex.faces) ∧
      (∀ i < n, ({AffineMap.lineMap x y (c i), AffineMap.lineMap x y (c (i + 1))} : Finset Ea) ∈
        𝒦'.complex.faces) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ({AffineMap.lineMap x y t} : Finset Ea) ∈ 𝒦'.complex.faces →
        ∃ i ≤ n, c i = t) ∧
      ∀ σ ∈ 𝒦'.complex.faces, convexHull ℝ (σ : Set Ea) ⊆ segment ℝ x y → σ.card = 2 →
        ∃ i < n, σ = {AffineMap.lineMap x y (c i), AffineMap.lineMap x y (c (i + 1))} := by
  classical
  let L := simplexComplex ({x, y} : Finset Ea) (𝒦.complex.indep hxyK)
  have hLsub : L.faces ⊆ 𝒦.complex.faces :=
    fun σ hσ => 𝒦.complex.down_closed hxyK hσ.2 hσ.1
  have hLspace : L.space = segment ℝ x y := by
    rw [simplexComplex_space _ _ (Finset.insert_nonempty _ _), Finset.coe_pair, convexHull_pair]
  let J := restrict 𝒦'.complex L.space
  have hJsub : IsSubdivision J L := hsub.restrict L hLsub
  have hsegK : segment ℝ x y ⊆ 𝒦'.complex.space := by
    rw [hsub.space_eq, ← hLspace]
    exact space_mono_of_faces_subset hLsub
  have hsegC : IsCompact (segment ℝ x y) := by
    rw [← convexHull_pair, ← Finset.coe_pair]
    exact ({x, y} : Finset Ea).finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hJfin : J.faces.Finite := by
    refine (𝒦'.finite_faces_inter_of_isCompact hsegC hsegK).subset ?_
    rintro σ ⟨hσ, hσL⟩
    obtain ⟨q, hq⟩ := 𝒦'.complex.nonempty_of_mem_faces hσ
    refine ⟨hσ, q, subset_convexHull ℝ _ (Finset.mem_coe.mpr hq), ?_⟩
    rw [← hLspace]
    exact hσL (subset_convexHull ℝ _ (Finset.mem_coe.mpr hq))
  have hxyL : ({x, y} : Finset Ea) ∈ L.faces := ⟨Finset.insert_nonempty _ _, le_rfl⟩
  obtain ⟨n, c, hn, hc0, hcn, hmono, hvert, hedge, hsurj, hσedge⟩ :=
    hJsub.exists_path_of_edge hJfin hxy hxyL
  refine ⟨n, c, hn, hc0, hcn, hmono, fun i hi => (hvert i hi).1,
    fun i hi => (hedge i hi).1, ?_, ?_⟩
  · intro t ht htv
    apply hsurj t ht
    refine ⟨htv, ?_⟩
    rw [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff, hLspace]
    exact (segment_eq_image_lineMap ℝ x y).symm ▸ ⟨t, ht, rfl⟩
  · intro σ hσ hσseg hσcard
    exact hσedge σ ⟨hσ, hLspace.symm ▸ hσseg⟩ hσseg hσcard

end DifferentialGeometry.Topology.PiecewiseLinear
