import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CapCylinder
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.BallComplementCylinder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [T2Space M]

theorem CapCore.nonempty_union_cylinder
    {X : Set M} (cap : CapCore X) (T : PartialDiffeomorph IC I3 Cylinder M ∞)
    (hT : univ ×ˢ Icc (0 : ℝ) 1 ⊆ T.source)
    (hfront : frontier X = range (fun q : Sphere 2 => T (q, 0)))
    (hside : ∀ q : Sphere 2, ∀ a ∈ Icc (0 : ℝ) 1, T (q, a) ∈ X → a = 0) :
    Nonempty (CapCore (X ∪ T '' (univ ×ˢ Icc (0 : ℝ) 1))) := by
  cases cap with
  | ball C hC hX =>
    have hboundary : C '' sphere (0 : ThreeSpace) 1 = range (fun q : Sphere 2 => T (q, 0)) := by
      rw [← hX] at hfront
      rw [← C.image_frontier_of_isCompact (isCompact_closedBall _ _) hC,
        frontier_closedBall _ one_ne_zero] at hfront
      exact hfront
    obtain ⟨B, hB, hBi, _⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_ball_and_cylinder_eqOn_neighborhoods
        C T hC hT hboundary (fun q a ha h => hside q a ha (hX ▸ h))
    exact ⟨CapCore.ball B hB (hX ▸ hBi)⟩
  | projective Z pr b hb P hP hX =>
    have hb1 : closedBall (0 : ThreeSpace) 1 ⊆ b.source :=
      (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)).trans hb
    have hK : IsCompact (b '' Metric.ball (0 : ThreeSpace) 1)ᶜ :=
      (b.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
        (ball_subset_closedBall.trans hb1)).isClosed_compl.isCompact
    have hboundary : P '' (b '' sphere (0 : ThreeSpace) 1) = range (fun q : Sphere 2 => T (q, 0)) := by
      rw [DifferentialGeometry.Topology.Manifold.image_sphere_eq_frontier_of_ball_complement
        b P hb1 hK hP, hX, hfront]
    obtain ⟨B, F, hF, hBs, hBi, _, _, _⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_ball_complement_chart_of_ball_complement_and_cylinder
        b P T hb1 hP hT hboundary (fun q a ha h => hside q a ha (hX ▸ h))
    let D : ThreeSpace ≃ₘ[ℝ] ThreeSpace :=
      (LinearEquiv.smulOfNeZero ℝ ThreeSpace (1 / 2 : ℝ) (by norm_num)).toContinuousLinearEquiv.toDiffeomorph
    let b' := (D.toPartialDiffeomorph.trans F.toPartialDiffeomorph).trans b
    have hb' : closedBall (0 : ThreeSpace) 2 ⊆ b'.source := by
      intro z hz
      refine ⟨⟨mem_univ _, mem_univ _⟩, hb1 ?_⟩
      apply hF.subset
      refine ⟨(1 / 2 : ℝ) • z, ?_, rfl⟩
      rw [mem_closedBall_zero_iff, norm_smul]
      have hn := mem_closedBall_zero_iff.mp hz
      norm_num
      linarith
    have hball : b' '' Metric.ball (0 : ThreeSpace) 1 =
        (b ∘ F) '' Metric.ball (0 : ThreeSpace) (1 / 2) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨(1 / 2 : ℝ) • z, ?_, rfl⟩
        rw [mem_ball_zero_iff, norm_smul]
        have hn := mem_ball_zero_iff.mp hz
        norm_num
        linarith
      · rintro ⟨z, hz, rfl⟩
        refine ⟨(2 : ℝ) • z, ?_, ?_⟩
        · rw [mem_ball_zero_iff, norm_smul]
          have hn := mem_ball_zero_iff.mp hz
          norm_num
          linarith
        · change b (F ((1 / 2 : ℝ) • ((2 : ℝ) • z))) = b (F z)
          rw [smul_smul]
          norm_num
    exact ⟨CapCore.projective Z pr b' hb' B (hball.symm ▸ hBs) (hball.symm ▸ hX ▸ hBi)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
