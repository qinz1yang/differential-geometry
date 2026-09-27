/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDiskOfDoubleCell
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.PieceMap
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPLSphere_one_val_image_branchCarrier (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ (D : SingularTwoCell L.space) (BdM : Set L.space)
      (T : NormalSingularSetTriangulation D BdM) (c : T.Branch), ¬T.IsBoundaryBranch c →
      IsPLSphere 1 (Subtype.val '' T.branchCarrier c) := by
  classical
  let _ := combinatorialChartedSpace L hL
  intro D BdM T c hc
  let _ : Finite (T.branchComplex c).faces := (T.branchComplex_faces_finite c).to_subtype
  have hid : IsPiecewiseAffineOn
      (id : EuclideanSpace ℝ (Fin T.piece.ambientDim) →
        EuclideanSpace ℝ (Fin T.piece.ambientDim)) (T.branchComplex c).space :=
    (isPolyhedron_space (T.branchComplex c)).isPLHomeomorphOn_id.isPiecewiseAffineOn
  have hPL : IsPLOn T.piece.ambientDim 3 (T.branchPieceIn c).map (T.branchComplex c).space :=
    (T.branchPieceIn c).isPLOn_comp hid (mapsTo_id _)
  have hval : IsPiecewiseAffineOn
      (fun x => (((T.branchPieceIn c).map x : L.space) : E)) (T.branchComplex c).space :=
    isPiecewiseAffineOn_val_comp_of_isPLOn L hL (T.branchComplex c).space _ hPL
  have hinj : InjOn (fun x => (((T.branchPieceIn c).map x : L.space) : E))
      (T.branchComplex c).space := fun x hx y hy hxy =>
    (T.branchPieceIn c).bijOn.injOn hx hy (Subtype.ext hxy)
  obtain ⟨G, -, hGspace, hGpl⟩ := exists_isPLHomeomorphOn_image (T.branchComplex c) hval hinj
  have hcarrier : Subtype.val '' T.branchCarrier c =
      (fun x => (((T.branchPieceIn c).map x : L.space) : E)) '' (T.branchComplex c).space := by
    change Subtype.val '' (T.piece.piece.map '' (T.branchComplex c).space) = _
    exact image_image _ _ _
  rw [hcarrier, ← hGspace]
  exact (T.branchComplex_isPLSphere hc).of_isPLHomeomorphOn hGpl

theorem SingularTwoCell.isPolyhedron_val_image (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ D : SingularTwoCell L.space, IsPolyhedron (Subtype.val '' (⇑D '' D.domain)) := by
  classical
  let _ := combinatorialChartedSpace L hL
  intro D
  have hval : IsPiecewiseAffineOn (fun x => ((D x : L.space) : E)) D.domain :=
    isPiecewiseAffineOn_val_comp_of_isPLOn L hL D.domain D.toFun D.isPLOn
  rw [image_image]
  exact hval.isPolyhedron_image D.isPLBall_domain.isPolyhedron

theorem exists_circle_subcomplex_branchCarrier (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ (D : SingularTwoCell L.space) (BdM : Set L.space)
      (T : NormalSingularSetTriangulation D BdM) (c : T.Branch), ¬T.IsBoundaryBranch c →
      ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R L ∧ R.faces.Finite ∧
        (PiecewiseLinear.restrict R (Subtype.val '' T.branchCarrier c)).space =
            Subtype.val '' T.branchCarrier c ∧
          IsCombinatorialManifold 1
            (PiecewiseLinear.restrict R (Subtype.val '' T.branchCarrier c)) ∧
          IsConnected
            (PiecewiseLinear.restrict R (Subtype.val '' T.branchCarrier c)).space ∧
          (PiecewiseLinear.restrict R (Subtype.val '' (⇑D '' D.domain))).space =
            Subtype.val '' (⇑D '' D.domain) := by
  classical
  let _ := combinatorialChartedSpace L hL
  intro D BdM T c hc
  have hsphere := isPLSphere_one_val_image_branchCarrier L hL D BdM T c hc
  have hZpoly := SingularTwoCell.isPolyhedron_val_image L hL D
  have hsubval : ∀ S : Set L.space, Subtype.val '' S ⊆ L.space := by
    rintro S _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨R, hRL, hRfin, hQ⟩ :=
    exists_isSubdivision_subcomplexes L
      (fun b : Bool => cond b (Subtype.val '' T.branchCarrier c)
        (Subtype.val '' (⇑D '' D.domain)))
      (fun b => by cases b; exacts [hZpoly, hsphere.isPolyhedron])
      (fun b => by cases b; exacts [hsubval _, hsubval _])
  have hΓspace : (PiecewiseLinear.restrict R (Subtype.val '' T.branchCarrier c)).space =
      Subtype.val '' T.branchCarrier c := restrict_space_of_eq_biUnion R _ (hQ true)
  have hZspace : (PiecewiseLinear.restrict R (Subtype.val '' (⇑D '' D.domain))).space =
      Subtype.val '' (⇑D '' D.domain) := restrict_space_of_eq_biUnion R _ (hQ false)
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite (PiecewiseLinear.restrict R (Subtype.val '' T.branchCarrier c)).faces :=
    (restrict_faces_finite R (Subtype.val '' T.branchCarrier c)).to_subtype
  have hΓsphere :
      IsPLSphere 1 (PiecewiseLinear.restrict R (Subtype.val '' T.branchCarrier c)).space := by
    rw [hΓspace]
    exact hsphere
  exact ⟨R, hRL, hRfin, hΓspace, IsPLSphere.isCombinatorialManifold (n := 0) hΓsphere,
    hΓsphere.isConnected, hZspace⟩

open Classical in
theorem isOrientable_derivedNeighborhood_of_isSubdivision
    {L R : Geometry.SimplicialComplex ℝ E} [Finite L.faces] [Finite R.faces]
    (hL : IsCombinatorialManifold 3 L) (hor : IsOrientable 3 L) (hRL : IsSubdivision R L)
    (Lc : Geometry.SimplicialComplex ℝ E) :
    letI : Finite (derivedNeighborhood R Lc).faces :=
      (derivedNeighborhood_faces_finite R Lc).to_subtype
    letI : Finite (boundaryComplex 3 (derivedNeighborhood R Lc)).faces :=
      (boundaryComplex_faces_finite 3 (derivedNeighborhood R Lc)).to_subtype
    IsOrientable 3 (derivedNeighborhood R Lc) ∧
      IsOrientable 2 (boundaryComplex 3 (derivedNeighborhood R Lc)) := by
  classical
  let _ : Finite (derivedNeighborhood R Lc).faces :=
    (derivedNeighborhood_faces_finite R Lc).to_subtype
  let _ : Finite (boundaryComplex 3 (derivedNeighborhood R Lc)).faces :=
    (boundaryComplex_faces_finite 3 (derivedNeighborhood R Lc)).to_subtype
  have hRb : IsCombinatorialManifoldWithBoundary 3 R :=
    (hL.of_isSubdivision hRL).isCombinatorialManifoldWithBoundary
  have horR : IsOrientable 3 R := hor.subdivision hL.isCombinatorialManifoldWithBoundary hRL
  have hN : IsOrientable 3 (derivedNeighborhood R Lc) :=
    IsOrientable.of_le (secondDerived R) (derivedNeighborhood R Lc)
      (derivedNeighborhood_faces_subset R Lc) hRb.secondDerived (hRb.derivedNeighborhood Lc)
      ((horR.barycentricSubdivision hRb).barycentricSubdivision hRb.barycentricSubdivision)
  exact ⟨hN, IsOrientable.boundary (derivedNeighborhood R Lc) (hRb.derivedNeighborhood Lc) hN⟩

omit [FiniteDimensional ℝ E] in
open Classical in
theorem derivedNeighborhoodCell_inter_eq_coneSet_upperLink_restrict
    (R : Geometry.SimplicialComplex ℝ E) {Γ Z : Set E} (hΓZ : Γ ⊆ Z)
    (hZ : (PiecewiseLinear.restrict R Z).space = Z) {s : Finset E}
    (hs : s ∈ (PiecewiseLinear.restrict R Γ).faces) :
    (derivedNeighborhoodCell R s).space ∩ Z =
      coneSet (s.centroid ℝ id)
        (upperLink (barycentricSubdivision (PiecewiseLinear.restrict R Z))
          {s.centroid ℝ id}).space := by
  have hsR := (mem_restrict_faces_iff R Γ).mp hs
  have hsZ : s ∈ (PiecewiseLinear.restrict R Z).faces :=
    (mem_restrict_faces_iff R Z).mpr ⟨hsR.1, hsR.2.trans hΓZ⟩
  calc (derivedNeighborhoodCell R s).space ∩ Z
      = (derivedNeighborhoodCell R s).space ∩ (PiecewiseLinear.restrict R Z).space := by
        rw [hZ]
    _ = (derivedNeighborhoodCell (PiecewiseLinear.restrict R Z) s).space :=
        derivedNeighborhoodCell_inter_subcomplex R _ (restrict_faces_subset R Z) hsZ
    _ = _ := derivedNeighborhoodCell_space_eq_coneSet (PiecewiseLinear.restrict R Z) hsZ

end DifferentialGeometry.Topology.PiecewiseLinear
