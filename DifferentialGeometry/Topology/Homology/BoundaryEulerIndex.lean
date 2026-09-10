import DifferentialGeometry.Topology.VectorField.BoundaryEulerFromIndex
import DifferentialGeometry.Topology.VectorField.PrescribedOutwardBoundary
import DifferentialGeometry.Topology.VectorField.BoundaryCollarPullback

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold
open scoped ContDiff Topology
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open Poincare.VectorField
namespace Poincare.Homology

theorem eulerChar_intrinsicBoundary_eq_of_dimension_ge_two
    {d : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 2)) M]
    [IsManifold (𝓡∂ (d + 2)) ∞ M] [T2Space M] [CompactSpace M]
    (K : Type) [Field K] :
    eulerChar K (TopCat.of ((𝓡∂ (d + 2)).boundary M)) =
      (1 - (-1 : ℤ) ^ (d + 2)) * eulerChar K (TopCat.of M) := by
  let I := 𝓡∂ (d + 2)
  let B := BoundaryManifold I M
  let J := HasSmoothBoundary.boundaryModel I
  let _ : J.Boundaryless := HasSmoothBoundary.boundaryIBoundaryless
  let _ : IsManifold J ∞ B := BoundaryManifold.isManifold (I := I)
  let _ : BoundarylessManifold J B := inferInstance
  have hK : IsCompact (I.boundary M) := (I.isClosed_boundary (n := ∞) (by simp)).isCompact
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp hK
  obtain ⟨V, hV, hout, hVf, hVi, hVI, _⟩ :=
    exists_outward_vectorField_interiorIndexSum_eq_eulerChar (n := d + 1) (M := M)
  have hn (p : B) : V p.val ≠ 0 := by
    intro hz
    have hh := hout p.val p.property
    rw [hz] at hh
    exact (lt_irrefl 0) hh
  obtain ⟨ε, hε, c, _, _, hc0, hci, δ, hδ, hδε, Y, hY, _, e, he, _, hWn⟩ :=
    exists_nonvanishing_boundary_collar_pullback hK V hV hn
  let _ : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  have hi (q : _) (hq : 0 < q.val.2.val) : I.IsInteriorPoint (e q).val := by
    rw [he q]
    exact hci q.val hq
  have hz (q : _) (hq : q.val.2.val = 0) : I.IsBoundaryPoint (e q).val := by
    rw [he q]
    have hqeq : q.val.2 = ⟨0, ⟨le_rfl, hε.le⟩⟩ := Subtype.ext hq
    change I.IsBoundaryPoint (c (q.val.1, q.val.2))
    rw [hqeq, hc0]
    exact q.val.1.property
  obtain ⟨T, hT, hTf, hTi, _, _⟩ :=
    exists_closed_vectorField_interiorIndexSum_eq_eulerChar J (M := B)
  obtain ⟨G, hG, hGout, hzero, hgerm, hcomp⟩ :=
    exists_outward_with_prescribed_tangential_component hδ Y hY e hi hz V hV hout T hT
  have hGf : {x | G x = 0}.Finite := hzero.symm ▸ hVf
  have hGV (x : M) (hx : G x = 0) : V x = 0 :=
    (congrArg (fun s : Set M => x ∈ s) hzero).mp hx
  have hGi (x : M) (hx : G x = 0) : HasContinuousIsolatedZero I G x :=
    (hVi x (hGV x hx)).congr (hgerm x (hGV x hx)).symm
  have hGI (x : M) (hx : G x = 0) : I.IsInteriorPoint x := hVI x (hGV x hx)
  have hGn (q : _) :
      _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => G y.val) q ≠ 0 := by
    intro hq
    have hv := hGV (e q).val
      ((mpullback_diffeomorph_eq_zero_iff e (by simp) (fun y : Y => G y.val) q).mp hq)
    exact hWn q ((mpullback_diffeomorph_eq_zero_iff e (by simp) (fun y : Y => V y.val) q).mpr hv)
  exact eulerChar_collar_base_of_outward_components J hδ hδε Y hY e hi G hG hGout
    hGf hGi hGI hGn T hT hcomp hTf hTi K

end Poincare.Homology
