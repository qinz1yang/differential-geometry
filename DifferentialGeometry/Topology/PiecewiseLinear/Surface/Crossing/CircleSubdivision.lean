import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCircleCharts
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCover
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCrossingArcs

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_subdivision_isolated_crossing_circle_disks
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {A B J N : Set E}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) A]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) B]
    (hJ : IsPLSphere 1 J) (hJA : J ⊆ A ∩ B) (hJK : J ⊆ interior K.space)
    (hcross : ∀ x ∈ J, HasPLCrossingAt A B x)
    (hN : IsOpen N) (hJN : J ⊆ N) (htrace : (A ∩ B) ∩ N ⊆ J) :
    ∃ (t : Finset J) (R : Geometry.SimplicialComplex ℝ E)
      (ψ : t → (ℝ × ℝ) × ℝ → E) (V : t → Set ((ℝ × ℝ) × ℝ))
      (Ω W : t → Set E) (P : t → Fin 4 → Set E)
      (q : t → Fin 4 → (Fin 3 → ℝ) → E),
      IsSubdivision R K ∧ R.faces.Finite ∧
      (PiecewiseLinear.restrict R J).space = J ∧
      (∀ j, IsOpen (V j) ∧ IsOpen (Ω j) ∧ IsOpen (W j) ∧ W j ⊆ Ω j ∧
        Ω j ⊆ N ∩ interior K.space ∧
        IsPLHomeomorphOn (ψ j) (V j) (R.space ∩ Ω j) ∧
        (∀ p ∈ V j, (ψ j p ∈ A ↔ p.1.2 = 0) ∧ (ψ j p ∈ B ↔ p.1.1 = 0)) ∧
        (∀ p ∈ V j, ψ j p ∈ A ∪ B ↔ p ∈ crossPlanes) ∧
        (∀ p ∈ V j, ψ j p ∈ J ↔ p.1 = 0) ∧
        ∀ i, IsPLHomeomorphOn (q j i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P j i) ∧
          P j i ⊆ K.space ∩ (A ∪ B) ∧
          (PiecewiseLinear.restrict R (P j i)).space = P j i ∧
          ∀ x ∈ R.space ∩ W j,
            (x ∈ P j i ↔ Function.invFunOn (ψ j) (V j) x ∈ crossHalfPlane i) ∧
            (x ∈ q j i '' stdSimplexBoundary 2 ↔ x ∈ J)) ∧
      ∀ s ∈ (PiecewiseLinear.restrict R J).faces,
        ∃ j, (⋃ v ∈ s, closedStar R v) ⊆ W j ∧
          (derivedNeighborhoodCell R s).space ⊆ W j := by
  choose ψ V Ω W P q hV hΩ hW hxW hWΩ hΩN hψ hAB hF hΓ hq hP hread hbd using
    (fun x : J => (hcross x x.2).exists_isolated_circle_disks x.2 hJA
      (hN.inter isOpen_interior) ⟨hJN x.2, hJK x.2⟩
      (fun _ h => htrace ⟨h.1, h.2.1⟩))
  have hcover : J ⊆ ⋃ x : J, W x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hJ.isPolyhedron.isCompact.elim_finite_subcover W hW hcover
  have hcoverE : ∀ x ∈ J, ∃ j : t, x ∈ W j.1 := by
    intro x hx
    obtain ⟨j, hjt, hxj⟩ := mem_iUnion₂.mp (ht hx)
    exact ⟨⟨j, hjt⟩, hxj⟩
  have hPpoly : ∀ j : t × Fin 4, IsPolyhedron (P j.1.1 j.2) := fun j =>
    (show IsPLBall 2 (P j.1.1 j.2) from ⟨q j.1.1 j.2, hq j.1.1 j.2⟩).isPolyhedron
  have hPK : ∀ j : t × Fin 4, P j.1.1 j.2 ⊆ K.space := by
    intro j x hx
    exact interior_subset (hP j.1.1 j.2 hx).1.2
  obtain ⟨R, hRK, hRfin, hJR, hPR, hcells⟩ :=
    exists_isSubdivision_derivedCells_subset_cover K hJ.isPolyhedron
      (hJK.trans interior_subset) (fun j : t × Fin 4 => P j.1.1 j.2) hPpoly hPK
      (fun j : t => W j.1) (fun j => hW j.1) hcoverE
  refine ⟨t, R, fun j => ψ j.1, fun j => V j.1, fun j => Ω j.1, fun j => W j.1,
    fun j => P j.1, fun j => q j.1, hRK, hRfin, hJR, ?_, hcells⟩
  intro j
  have hΩR : Ω j.1 ⊆ R.space := by
    rw [hRK.space_eq]
    exact fun _ hx => interior_subset (hΩN j.1 hx).2
  refine ⟨hV j.1, hΩ j.1, hW j.1, hWΩ j.1, hΩN j.1, ?_,
    hAB j.1, hF j.1, hΓ j.1, fun i => ?_⟩
  · simpa only [inter_eq_right.mpr hΩR] using hψ j.1
  · exact ⟨hq j.1 i, fun _ hx => ⟨hPK (j, i) hx, (hP j.1 i hx).2⟩,
      hPR (j, i), fun x hx => ⟨hread j.1 x hx.2 i, hbd j.1 x hx.2 i⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
