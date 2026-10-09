import DifferentialGeometry.Topology.PiecewiseLinear.Section34SurfaceCutDescent
import DifferentialGeometry.Topology.PiecewiseLinear.Section34DiskMotionPullback
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TorusInessentialDisk

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_essential_disk_of_interior_torus_carrier
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (D : Geometry.SimplicialComplex ℝ E)
    (S : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite D.faces] [Finite S.faces] (hD : IsPLBall 2 D.space)
    (hS : IsCombinatorialManifoldWithBoundary 3 S)
    {f : E × ℝ → EuclideanSpace ℝ (Fin 3)} (hf : IsCylindricalDiagram f D.space S.space)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1))
    {T : Set (EuclideanSpace ℝ (Fin 3))} (hT : IsPLTorus T)
    (hTS : T ⊆ interior S.space) (hgen : CarriesFundamentalGroupOnto T S.space) :
    ∃ (Q : Set (EuclideanSpace ℝ (Fin 3))) (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q ∧ Q ⊆ interior S.space ∧
      Q ∩ T = q '' stdSimplexBoundary 2 ∧
      ∃ hb : q '' stdSimplexBoundary 2 ⊆ T,
        ¬ (⟨inclusion hb, continuous_inclusion hb⟩ :
          C(q '' stdSimplexBoundary 2, T)).Nullhomotopic := by
  classical
  obtain ⟨K, hKfin, hK, hconn, hKT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite K.faces := hKfin.to_subtype
  have hKS : K.space ⊆ interior S.space := hKT ▸ hTS
  have hKgen : CarriesFundamentalGroupOnto K.space S.space := hKT ▸ hgen
  obtain ⟨A, B, hAfin, -, hA, -, hAsp, -⟩ :=
    hf.exists_ball_pair_with_boundary hD (a := 1 / 2) (by norm_num)
  let _ : Finite A.faces := hAfin.to_subtype
  let L := boundaryComplex 3 A
  let _ : Finite L.faces := (boundaryComplex_faces_finite 3 A).to_subtype
  have hLspace : L.space = frontier A.space :=
    (frontier_space_eq_boundaryComplex_space_of_finrank (by simp) A
      hA.isCombinatorialManifoldWithBoundary).symm
  have hL : IsCombinatorialManifold 2 L :=
    (show IsPLSphere 2 L.space from hLspace.symm ▸ hA.isPLSphere_frontier).isCombinatorialManifold
  obtain ⟨Φ, Q, q, hΦ, hfix, hq, hQS, hmeet, hnot⟩ :=
    hf.exists_supported_surface_nonbounding_disk D S K L hD hS hK hL hconn hKS hKgen
      hends (hLspace.trans (congrArg frontier hAsp))
  obtain ⟨N, -, -, -, -, -, -, -, -, hΦint⟩ :=
    hK.exists_supported_image_preserving_carrier S K hconn hKS hKgen hΦ hfix
  obtain ⟨Q', q', hq', hQ'S, hmeet', hnot', -, -⟩ :=
    hΦ.exists_pullback_disk_of_not_bounding hq (hΦint.symm ▸ hQS) hmeet hnot
  rw [hKT] at hmeet' hnot'
  have hb : q' '' stdSimplexBoundary 2 ⊆ T := hmeet'.symm.subset.trans inter_subset_right
  refine ⟨Q', q', hq', hQ'S, hmeet', hb, ?_⟩
  intro hnull
  obtain ⟨C, c, hc, hCT, hend⟩ := hT.exists_isPLHomeomorphOn_disk_of_nullhomotopic_inclusion
    hq'.isPLSphere_image_stdSimplexBoundary hb hnull
  exact hnot' ⟨C, c, hc, hCT, hend.symm⟩

end DifferentialGeometry.Topology.PiecewiseLinear
