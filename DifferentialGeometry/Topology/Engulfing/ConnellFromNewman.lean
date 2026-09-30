import DifferentialGeometry.Topology.Engulfing.CellEngulfing
import DifferentialGeometry.Topology.Engulfing.ConnellCover
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.EnclosingSimplex
import DifferentialGeometry.Topology.Sphere.TwoOpenCells

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {M : Type*} [MetricSpace M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem exists_two_cells_cover_three_cores_of_relativeNewman (hn : 5 ≤ n)
    (eM : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hnewman : ∀ C : Set M, relativeNewmanAt (Cᶜ : Set M) n (n - 3) (n - 3 + 1))
    (A B C : Set M) (u v w : EuclideanSpace ℝ (Fin n) → M)
    (hA : IsCompact A) (hB : IsCompact B) (hC : IsCompact C)
    (hu : IsOpenEmbedding u) (hv : IsOpenEmbedding v) (hw : IsOpenEmbedding w)
    (hAu : A ⊆ range u) (hBv : B ⊆ range v) (hCw : C ⊆ range w) :
    ∃ u' v' : EuclideanSpace ℝ (Fin n) → M,
      IsOpenEmbedding u' ∧ IsOpenEmbedding v' ∧ A ∪ B ∪ C ⊆ range u' ∪ range v' := by
  classical
  let R := w ⁻¹' C
  have hR : IsCompact R := hw.isEmbedding.isInducing.isCompact_preimage' hC hCw
  obtain ⟨b, hb⟩ := exists_bounded_subset_interior_simplex hR.isBounded
  let K := barycentricComplex b b.ind
  have hK : K.faces.Finite := barycentricComplex_finite_faces b b.ind
  have hKspace : K.space = convexHull ℝ (range b) := barycentricComplex_space_eq b b.ind
  have hKconv : Convex ℝ K.space := hKspace.symm ▸ convex_convexHull ℝ _
  have hRK : R ⊆ interior K.space := by rw [hKspace]; exact hb
  obtain ⟨D, hD, hDspace, _, hinterior, hPA, hPB, hPAu, hPBv⟩ :=
    exists_connell_chart_preparation hw K hK hR hRK hA hB
      hu.isOpen_range hv.isOpen_range hAu hBv
  have hDdim : ∀ s ∈ D.faces, s.card ≤ n + 1 := by
    intro s hs
    simpa only [Fintype.card_coe, finrank_euclideanSpace_fin] using
      (D.indep hs).card_le_finrank_succ.trans
        (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  have hlowFinite : (skeleton D (n - 3)).faces.Finite := hD.subset (fun _ hs => hs.1)
  have hlowDim : ∀ s ∈ (skeleton D (n - 3)).faces, s.card ≤ n - 3 + 1 :=
    fun _ hs => hs.2
  have hhighFinite :
      (vertexRestriction (barycentricSubdivision D) (lowCentroids D (n - 3))ᶜ).faces.Finite :=
    (barycentricSubdivision_finite_faces D hD).subset (fun _ hs => hs.1)
  have hhighDim : ∀ s ∈
      (vertexRestriction (barycentricSubdivision D) (lowCentroids D (n - 3))ᶜ).faces,
      s.card ≤ n - 3 + 1 := by
    intro s hs
    have hcard := vertexRestriction_dual_face_card_le D (n - 3) hDdim s hs
    omega
  obtain ⟨u₁, hu₁, hAu₁, hlow⟩ := exists_cell_engulfing_retaining_compact
    (by omega : n - 3 + 3 ≤ n) eM hnewman hu hw hPA hPAu
    (skeleton D (n - 3)) hlowFinite hlowDim
  obtain ⟨v₁, hv₁, hBv₁, hhigh⟩ := exists_cell_engulfing_retaining_compact
    (by omega : n - 3 + 3 ≤ n) eM hnewman hv hw hPB hPBv
    (vertexRestriction (barycentricSubdivision D) (lowCentroids D (n - 3))ᶜ)
    hhighFinite hhighDim
  have hRinside : R ⊆ D.space := by rw [hDspace]; exact hRK.trans interior_subset
  have hDconv : Convex ℝ D.space := hDspace.symm ▸ hKconv
  obtain ⟨u', v', hu', hv', _, _, hcover⟩ := exists_two_open_cells_cover_three_cores_of_skeleta
    hw D hD hDconv (n - 3) hR hRinside hinterior
    ⟨u₁, v₁, hu₁, hv₁, hAu₁, hBv₁, hlow, hhigh⟩
  have heq : w '' R = C := image_preimage_eq_of_subset hCw
  exact ⟨u', v', hu', hv', by simpa only [heq] using hcover⟩

theorem exists_two_open_cells_of_relativeNewman [CompactSpace M] [Nonempty M]
    (hn : 5 ≤ n) (eM : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hnewman : ∀ C : Set M, relativeNewmanAt (Cᶜ : Set M) n (n - 3) (n - 3 + 1)) :
    ∃ u v : EuclideanSpace ℝ (Fin n) → M,
      IsOpenEmbedding u ∧ IsOpenEmbedding v ∧ range u ∪ range v = univ :=
  exists_two_open_cells_of_compact_three_core_reduction
    (exists_two_cells_cover_three_cores_of_relativeNewman hn eM hnewman)

theorem nonempty_homeomorph_sphere_of_relativeNewman [CompactSpace M] [Nonempty M]
    (hn : 5 ≤ n) (eM : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hnewman : ∀ C : Set M, relativeNewmanAt (Cᶜ : Set M) n (n - 3) (n - 3 + 1)) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  obtain ⟨u, v, hu, hv, hcover⟩ := exists_two_open_cells_of_relativeNewman hn eM hnewman
  exact nonempty_homeomorph_sphere_of_two_open_cells (by omega) hu hv hcover

end DifferentialGeometry.Topology.Engulfing
