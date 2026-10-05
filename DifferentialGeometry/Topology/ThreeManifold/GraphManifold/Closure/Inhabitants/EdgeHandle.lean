import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts
import DifferentialGeometry.Topology.Manifold.ClosedCellOrientation
import DifferentialGeometry.Topology.Manifold.StereographicChart
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpaceProd
import DifferentialGeometry.Topology.Manifold.AddCircle
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere

/-!
The standard disk times interval embeds through the whole stereographic chart into the closed
three-sphere. Its actual inclusion derivative is bijective, including all corner points.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold.Assembly

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold
attribute [local instance] uliftChartedSpace isManifold_ulift

local instance edgeDiskCharts : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  Handle.closedCellChartedSpaceSucc 1
local instance edgeDiskSmooth : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  Handle.closedCellIsManifold 1

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S3 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

private def edgeHandleCoordinates : (E2 × ℝ) ≃L[ℝ] E3 :=
  (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ E2)
    AddCircle.euclideanSpaceFinOneContinuousLinearEquivReal.symm).trans
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates

private def edgeHandleNorth : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩

private def edgeHandleInclusion : ClosedCell 2 × Icc (0 : ℝ) 1 → E2 × ℝ :=
  Prod.map Subtype.val Subtype.val

private theorem edgeHandleInclusion_smooth :
    ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, E2 × ℝ) ∞ edgeHandleInclusion := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact
    (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 1).contMDiff
      |>.prodMap (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞))

private theorem edgeHandleInclusion_bijective (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, E2 × ℝ)
      edgeHandleInclusion p) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  have hi :=
    (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 1).prodMap
      (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1))
  exact DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt
    ((𝓡∂ 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) edgeHandleInclusion p
    (hi.isImmersion.isImmersionAt p) (by simp)

private def edgeHandleEuclidean : ClosedCell 2 × Icc (0 : ℝ) 1 → E3 :=
  edgeHandleCoordinates ∘ edgeHandleInclusion

private theorem edgeHandleEuclidean_smooth :
    ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓡 3) ∞ edgeHandleEuclidean :=
  edgeHandleCoordinates.contDiff.contMDiff.comp edgeHandleInclusion_smooth

private theorem edgeHandleEuclidean_bijective (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓡 3) edgeHandleEuclidean p) := by
  unfold edgeHandleEuclidean
  rw [mfderiv_comp p (edgeHandleCoordinates.contDiff.contMDiff.mdifferentiableAt
    (show (∞ : ℕ∞ω) ≠ 0 by simp))
    (edgeHandleInclusion_smooth.mdifferentiableAt (by simp))]
  exact (edgeHandleCoordinates.toDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) (edgeHandleInclusion p)).bijective.comp (edgeHandleInclusion_bijective p)

private def edgeHandleSphere : ClosedCell 2 × Icc (0 : ℝ) 1 → S3 :=
  (stereographic' 3 edgeHandleNorth).symm ∘ edgeHandleEuclidean

private theorem edgeHandleSphere_smooth :
    ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓡 3) ∞ edgeHandleSphere :=
  (DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph
    (n := 3) edgeHandleNorth).contMDiff.comp edgeHandleEuclidean_smooth

private theorem edgeHandleSphere_bijective (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓡 3) edgeHandleSphere p) := by
  have hs := DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph
    (n := 3) edgeHandleNorth
  unfold edgeHandleSphere
  rw [mfderiv_comp p (hs.contMDiff.mdifferentiableAt (by simp))
    (edgeHandleEuclidean_smooth.mdifferentiableAt (by simp))]
  exact ((hs (edgeHandleEuclidean p)).mfderivToContinuousLinearEquiv (by simp)).bijective.comp
    (edgeHandleEuclidean_bijective p)

private theorem edgeHandleSphere_injective : Injective edgeHandleSphere := by
  apply ((stereographic' 3 edgeHandleNorth).symm.isOpenEmbedding (by simp)).injective.comp
  apply edgeHandleCoordinates.injective.comp
  intro p q h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

def standardEdgeHandle : EdgeHandle (NoCuts.carrier standardThreeSphereLift.{u}) where
  map := standardThreeSphereLiftDiffeomorph.{u} ∘ edgeHandleSphere
  smooth := standardThreeSphereLiftDiffeomorph.{u}.contMDiff.comp edgeHandleSphere_smooth
  mfderiv_bijective p := by
    rw [mfderiv_comp p
      (standardThreeSphereLiftDiffeomorph.{u}.contMDiff.mdifferentiableAt (by simp))
      (edgeHandleSphere_smooth.mdifferentiableAt (by simp))]
    change Bijective ((mfderiv (𝓡 3) (𝓡 3)
      (ULift.up : S3 → ULift.{u} S3) (edgeHandleSphere p)).comp
        (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓡 3) edgeHandleSphere p))
    rw [mfderiv_ulift_up]
    exact edgeHandleSphere_bijective p
  injective := standardThreeSphereLiftDiffeomorph.{u}.injective.comp edgeHandleSphere_injective
  interior := by
    intro x hx
    exact BoundarylessManifold.isInteriorPoint

theorem standardEdgeHandle_endDisks_disjoint :
    Disjoint (standardEdgeHandle.{u}.endDisk false) (standardEdgeHandle.{u}.endDisk true) := by
  rw [disjoint_iff_inter_eq_empty]
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨a, ha⟩ := hy.1
  obtain ⟨b, hb⟩ := hy.2
  have heq := standardEdgeHandle.{u}.injective (ha.trans hb.symm)
  have hend := congrArg (fun z : ClosedCell 2 × Icc (0 : ℝ) 1 => z.2.val) heq
  norm_num [iccEnd] at hend

end GC.GraphManifold.Assembly
