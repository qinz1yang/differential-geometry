import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualFillingRegions

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.filling_regions_of_cell_contacts
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P R : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) {A As B Bs D F J : Set M}
    (hcellA : IsPLCellOn 3 A As) (hcellB : IsPLCellOn 3 B Bs)
    (hRint : R ⊆ interior P) (hclosed : IsClosed R)
    (hreg : closure (interior R) = R) (hconn : IsConnected (interior R))
    (hfront : u '' frontier R = D ∪ F)
    (hcontactA : As ∩ u '' R = F) (hcontactB : Bs ∩ u '' R = D)
    (hJDF : J ⊆ D ∩ F) :
    let X := closure (interior (P ∩ u ⁻¹' A))
    let Y := closure (interior (P ∩ u ⁻¹' B))
    let τ := Function.invFunOn u P
    R ⊆ interior P ∧ IsClosed X ∧ IsClosed Y ∧
      closure (interior X) = X ∧ closure (interior Y) = Y ∧
      (∀ x ∈ interior P,
        (x ∈ frontier X ↔ u x ∈ As) ∧
        (x ∈ frontier Y ↔ u x ∈ Bs)) ∧
      IsClosed R ∧ closure (interior R) = R ∧
      IsConnected (interior R) ∧
      R ∩ frontier X = τ '' F ∧ R ∩ frontier Y = τ '' D ∧
      R ∩ frontier X ⊆ frontier R ∧
      R ∩ frontier Y ⊆ frontier R ∧
      frontier R ⊆ frontier X ∪ frontier Y ∧ τ '' J ⊆ R := by
  let X := closure (interior (P ∩ u ⁻¹' A))
  let Y := closure (interior (P ∩ u ⁻¹' B))
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hRP : R ⊆ P := hRint.trans interior_subset
  have hregA : closure (interior A) =
      A := by
    rw [← hcellA.sdiff_boundary_eq_interior]
    exact hcellA.closure_sdiff_boundary
  have hregB : closure (interior B) =
      B := by
    rw [← hcellB.sdiff_boundary_eq_interior]
    exact hcellB.closure_sdiff_boundary
  have hread (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ interior P) :
      (x ∈ frontier X ↔ u x ∈ As) ∧
      (x ∈ frontier Y ↔ u x ∈ Bs) := by
    constructor
    · rw [hu.regularized_clipped_region_frontier hregA hx |>.1,
        ← hcellA.boundary_eq_frontier]
    · rw [hu.regularized_clipped_region_frontier hregB hx |>.1,
        ← hcellB.boundary_eq_frontier]
  have hfrontR : frontier R ⊆ R := hclosed.frontier_subset
  have hcontact (S : Set M) (Z : Set (EuclideanSpace ℝ (Fin 3))) (E : Set M)
      (hSZ : ∀ x ∈ R, x ∈ Z ↔ u x ∈ S)
      (hSE : S ∩ u '' R = E) : R ∩ Z = τ '' E := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨u x, hSE.subset ⟨(hSZ x hx.1).mp hx.2, x, hx.1, rfl⟩,
        hleft (hRP hx.1)⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hyS, x, hx, rfl⟩ := hSE.symm.subset hy
      rw [hleft (hRP hx)]
      exact ⟨hx, (hSZ x hx).mpr hyS⟩
  have hfirst : R ∩ frontier X = τ '' F :=
    hcontact _ _ _ (fun x hx => (hread x (hRint hx)).1) hcontactA
  have hsecond : R ∩ frontier Y = τ '' D :=
    hcontact _ _ _ (fun x hx => (hread x (hRint hx)).2) hcontactB
  have hbackfront : τ '' (D ∪ F) ⊆ frontier R := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hfront.symm.subset hy
    rw [hleft (hRP (hfrontR hx))]
    exact hx
  refine ⟨hRint, isClosed_closure, isClosed_closure, closure_interior_idem,
    closure_interior_idem, hread, hclosed, hreg, hconn, hfirst, hsecond, ?_, ?_, ?_, ?_⟩
  · rw [hfirst]
    exact (image_mono subset_union_right).trans hbackfront
  · rw [hsecond]
    exact (image_mono subset_union_left).trans hbackfront
  · intro x hx
    rcases hfront.subset ⟨x, hx, rfl⟩ with hxD | hxF
    · exact Or.inr ((hread x (hRint (hfrontR hx))).2.mpr
        (hcontactB.symm.subset hxD).1)
    · exact Or.inl ((hread x (hRint (hfrontR hx))).1.mpr
        (hcontactA.symm.subset hxF).1)
  · exact ((image_mono (hJDF.trans inter_subset_left)).trans
      (image_mono subset_union_left)).trans (hbackfront.trans hfrontR)

end DifferentialGeometry.Topology.PiecewiseLinear
