import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SmoothStructure
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientation
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.LocalDiffeomorphism
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.PuncturedImageBall

open scoped Manifold ContDiff Topology
open Bundle Manifold Set Topology

noncomputable section
universe u v

namespace OrientationAssembly

abbrev csModel : Type := EuclideanSpace ℝ (Fin 3)
abbrev csSphere : Type := Metric.sphere (0 : csModel) 1

open DifferentialGeometry.Topology ConnectedSumQuotient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace csModel M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
  {N : Type v} [TopologicalSpace N] [ChartedSpace csModel N] [IsManifold (𝓡 3) ∞ N] [T2Space N]

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem mem_atlas_leftChart (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (a : csSphere ≃ₜ csSphere) (f : OpenPartialHomeomorph M csModel) (hf : f ∈ atlas csModel M) :
    letI := csChartedSpace c d a
    (leftChart c d a hn3 f).symm ∈ atlas csModel (ConnectedSumQuotient c d a) :=
  ⟨Sum.inl ⟨f, hf⟩, rfl⟩

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem mem_atlas_rightChart (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (a : csSphere ≃ₜ csSphere) (g : OpenPartialHomeomorph N csModel) (hg : g ∈ atlas csModel N) :
    letI := csChartedSpace c d a
    (rightChart c d a hn3 g).symm ∈ atlas csModel (ConnectedSumQuotient c d a) :=
  ⟨Sum.inr (Sum.inl ⟨g, hg⟩), rfl⟩

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem mem_atlas_seamChartX (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (a : csSphere ≃ₜ csSphere) :
    letI := csChartedSpace c d a
    seamChartX c d a ∈ atlas csModel (ConnectedSumQuotient c d a) :=
  ⟨Sum.inr (Sum.inr ()), rfl⟩

theorem interiorLeft_isLocalDiffeomorph' (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere) :
    letI := csChartedSpace c d aD.toHomeomorph
    letI := csIsManifold c d aD.toHomeomorph (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (interiorLeft c d aD) := by
  let _ := csChartedSpace c d aD.toHomeomorph
  let _ := csIsManifold c d aD.toHomeomorph (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
  exact interiorLeft_isLocalDiffeomorph c d aD (fun f hf => mem_atlas_leftChart c d aD.toHomeomorph f hf)

theorem interiorRight_isLocalDiffeomorph' (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere) :
    letI := csChartedSpace c d aD.toHomeomorph
    letI := csIsManifold c d aD.toHomeomorph (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (interiorRight c d aD) := by
  let _ := csChartedSpace c d aD.toHomeomorph
  let _ := csIsManifold c d aD.toHomeomorph (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
  exact interiorRight_isLocalDiffeomorph c d aD (fun g hg => mem_atlas_rightChart c d aD.toHomeomorph g hg)

theorem collarMap_isLocalDiffeomorph' (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere) :
    letI := csChartedSpace c d aD.toHomeomorph
    letI := csIsManifold c d aD.toHomeomorph (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (collarMap c d aD) := by
  let _ := csChartedSpace c d aD.toHomeomorph
  let _ := csIsManifold c d aD.toHomeomorph (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
  exact collarMap_isLocalDiffeomorph c d aD (mem_atlas_seamChartX c d aD.toHomeomorph)

end OrientationAssembly

namespace AssemblyReduction
open OrientationAssembly
abbrev csModel : Type := EuclideanSpace ℝ (Fin 3)
abbrev csSphere : Type := Metric.sphere (0 : csModel) 1
open DifferentialGeometry.Topology ConnectedSumQuotient

theorem exists_smooth_connected_sum_of_orientation
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold) (d : OrientedBallChart N.toClosedOrientedManifold)
    (a : BoundaryAttachment)
    (hO :
      letI := csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
      letI := csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
        (contDiffOn_reflectMap a.1) (contDiffOn_reflectMapInv a.1)
      ∃ O : DifferentialGeometry.ManifoldOrientation (𝓡 3)
          (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) 3,
        (∀ x : c.toBallChart.interior, Orientation.map (Fin 3)
            ((interiorLeft_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1).mfderivToContinuousLinearEquiv
              (by simp) x).toLinearEquiv (M.orientation.orientation x)
          = O.orientation (ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 x)) ∧
        (∀ x : d.toBallChart.interior, Orientation.map (Fin 3)
            ((interiorRight_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1).mfderivToContinuousLinearEquiv
              (by simp) x).toLinearEquiv (N.orientation.orientation x)
          = O.orientation (ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 x))) :
    Nonempty (SmoothConnectedSum c d a) := by
  let _ := csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
  let _ := csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
    (contDiffOn_reflectMap a.1) (contDiffOn_reflectMapInv a.1)
  have : Nonempty (Metric.sphere (0 : csModel) 1) := nonempty_sphere_of_neZero
  obtain ⟨O, hL, hR⟩ := hO
  exact ⟨O, interiorLeft_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1,
    interiorRight_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1,
    collarMap_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1, hL, hR⟩

end AssemblyReduction
