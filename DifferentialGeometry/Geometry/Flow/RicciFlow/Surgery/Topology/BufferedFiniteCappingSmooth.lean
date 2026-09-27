import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedFiniteCapping
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCoreHalfSpaceModel
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreSmoothEmbedding
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapBallSmooth
import DifferentialGeometry.Topology.Manifold.ScaledClosedBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalTransitionBridge

section

set_option autoImplicit false
noncomputable section

open Set Function Manifold
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.Handle
open DifferentialGeometry.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] {ι : Type} [Fintype ι] {δ : ι → ℝ} {L : ℝ}
  (hL : 0 < L) (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1)
  (f : ∀ i : ι, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))

local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

@[instance_reducible]
def bufferedCutCoreChartedSpace : ChartedSpace (EuclideanHalfSpace 3) (T).core := by
  letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
    cutCoreBoundaryChartedSpace ThreeModel (by simp) hδ f hf hdisj
  letI := euclideanHalfSpaceProdChartedSpace (cutCore f)
  exact chartedSpaceOfHomeomorph (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj)

include hs in
theorem bufferedCutCore_isManifold :
    letI := bufferedCutCoreChartedSpace hδ hδ1 f hf hdisj
    IsManifold (𝓡∂ 3) ∞ (T).core := by
  let : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
    cutCoreBoundaryChartedSpace ThreeModel (by simp) hδ f hf hdisj
  let : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
    cutCore_isManifold ThreeModel (by simp) hδ f hf hdisj hs
  let : ChartedSpace (EuclideanHalfSpace 3) (cutCore f) := euclideanHalfSpaceProdChartedSpace (cutCore f)
  let : IsManifold (𝓡∂ 3) ∞ (cutCore f) := euclideanHalfSpaceProd_isManifold (cutCore f)
  exact isManifoldOfHomeomorph (𝓡∂ 3) (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj)

def bufferedCutCoreDiffeomorph :
    letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
      cutCoreBoundaryChartedSpace ThreeModel (by simp) hδ f hf hdisj
    letI := euclideanHalfSpaceProdChartedSpace (cutCore f)
    letI := bufferedCutCoreChartedSpace hδ hδ1 f hf hdisj
    (T).core ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ cutCore f := by
  letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
    cutCoreBoundaryChartedSpace ThreeModel (by simp) hδ f hf hdisj
  letI : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
    cutCore_isManifold ThreeModel (by simp) hδ f hf hdisj hs
  letI := euclideanHalfSpaceProdChartedSpace (cutCore f)
  letI : IsManifold (𝓡∂ 3) ∞ (cutCore f) := euclideanHalfSpaceProd_isManifold (cutCore f)
  letI := bufferedCutCoreChartedSpace hδ hδ1 f hf hdisj
  exact
    { toEquiv := (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj).toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
        (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj) (𝓡∂ 3) ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
        (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj) (𝓡∂ 3) ∞ }

include hs in
theorem bufferedCutCore_isSmoothEmbedding :
    letI := bufferedCutCoreChartedSpace hδ hδ1 f hf hdisj
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (Subtype.val : (T).core → M) := by
  let : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
    cutCoreBoundaryChartedSpace ThreeModel (by simp) hδ f hf hdisj
  let : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
    cutCore_isManifold ThreeModel (by simp) hδ f hf hdisj hs
  let := euclideanHalfSpaceProdChartedSpace (cutCore f)
  let := bufferedCutCoreChartedSpace hδ hδ1 f hf hdisj
  let : IsManifold (𝓡∂ 3) ∞ (T).core := bufferedCutCore_isManifold hδ hδ1 f hf hdisj hs
  exact isSmoothEmbedding_diffeomorph_precomp (Subtype.val : cutCore f → M)
    (DifferentialGeometry.Manifold.isSmoothEmbedding_coreSubtype_of_euclideanHalfSpaceProd
      (cutCore_ambientInclusion_isSmoothEmbedding ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj hs))
    (bufferedCutCoreDiffeomorph hδ hδ1 f hf hdisj hs)

include hs in
theorem bufferedCutCore_boundary :
    letI := bufferedCutCoreChartedSpace hδ hδ1 f hf hdisj
    (𝓡∂ 3).boundary (T).core = ⋃ b : (T).Boundary, range ((T).coreBoundarySphere b) := by
  let : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
    cutCoreBoundaryChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj
  let : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
    cutCore_isManifold ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj hs
  let := euclideanHalfSpaceProdChartedSpace (cutCore f)
  let := bufferedCutCoreChartedSpace hδ hδ1 f hf hdisj
  let D := bufferedCutCoreDiffeomorph hδ hδ1 f hf hdisj hs
  have hb : (𝓡∂ 3).boundary (cutCore f) =
      range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) :=
    (euclideanHalfSpaceProd_boundary (cutCore f)).trans
      (cutCore_boundary_eq_cuttingSpheres ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj hs)
  rw [← D.preimage_boundary (by simp), hb]
  ext x
  simp only [mem_preimage, mem_range, mem_iUnion]
  constructor
  · rintro ⟨⟨b, y⟩, hy⟩
    refine ⟨b, y, D.injective ?_⟩
    exact (bufferedCutCoreHomeomorph_boundary hδ hδ1 f hf hdisj b y).trans hy
  · rintro ⟨b, y, rfl⟩
    exact ⟨⟨b, y⟩, (bufferedCutCoreHomeomorph_boundary hδ hδ1 f hf hdisj b y).symm⟩

include hs in
theorem Capping.ofBufferedFiniteCaps_coreInclusion_isSmoothEmbedding :
    letI : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
    letI := bufferedCutCoreChartedSpace hδ hδ1 f hf hdisj
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (Capping.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj).coreInclusion := by
  let : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
    cutCoreBoundaryChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj
  let : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
    cutCore_isManifold ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj hs
  let := euclideanHalfSpaceProdChartedSpace (cutCore f)
  let := bufferedCutCoreChartedSpace hδ hδ1 f hf hdisj
  let : IsManifold (𝓡∂ 3) ∞ (T).core := bufferedCutCore_isManifold hδ hδ1 f hf hdisj hs
  let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
  exact isSmoothEmbedding_diffeomorph_precomp
    (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
    (DifferentialGeometry.Manifold.isSmoothEmbedding_coreInclusion_of_euclideanHalfSpaceProd _
      (finiteCoreInclusion_isSmoothEmbedding ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs))
    (bufferedCutCoreDiffeomorph hδ hδ1 f hf hdisj hs)

include hs in
theorem Capping.ofBufferedFiniteCaps_cap_isSmoothEmbedding (b : ι × Bool) :
    letI : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
    letI := threeBallChartedSpace
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      ((Capping.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj).cap b) := by
  let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
  let := threeBallChartedSpace
  let : IsManifold (𝓡∂ 3) ∞ ThreeBall := threeBall_isManifold
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let := closedCellChartedSpaceSucc 2
  let D := threeBallDiffeomorph.symm.trans (closedBallUnitDiffeomorph hL).symm
  have h := isSmoothEmbedding_diffeomorph_precomp
    (fun x : {x : ThreeSpace // ‖x‖ ≤ L} =>
      finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩)
    (finiteCapInclusion_ball_isSmoothEmbedding ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs b) D
  convert h using 1
  funext x
  rw [Capping.ofBufferedFiniteCaps_cap]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end

section

set_option autoImplicit false
noncomputable section

open Manifold
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.Handle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

attribute [local instance] threeBallChartedSpace threeBall_isManifold
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

def threeBallScaleDiffeomorph {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ {x : ThreeSpace // ‖x‖ ≤ L} := by
  letI := closedBallChartedSpace hL
  exact threeBallDiffeomorph.symm.trans (closedBallUnitDiffeomorph hL).symm

@[simp] theorem threeBallScaleDiffeomorph_apply {L : ℝ} (hL : 0 < L) (x : ThreeBall) :
    letI := closedBallChartedSpace hL
    (threeBallScaleDiffeomorph hL x).val = L • (x : ThreeSpace) := rfl

@[simp] theorem threeBallScaleDiffeomorph_symm_apply {L : ℝ} (hL : 0 < L)
    (x : {x : ThreeSpace // ‖x‖ ≤ L}) :
    letI := closedBallChartedSpace hL
    ((threeBallScaleDiffeomorph hL).symm x : ThreeSpace) = L⁻¹ • x.val := rfl

theorem mfderiv_threeBallScaleDiffeomorph_coe {L : ℝ} (hL : 0 < L) (x : ThreeBall) :
    letI := closedBallChartedSpace hL
    mfderiv (𝓡∂ 3) ThreeModel (Subtype.val : {x : ThreeSpace // ‖x‖ ≤ L} → ThreeSpace)
        (threeBallScaleDiffeomorph hL x) ∘L
      mfderiv (𝓡∂ 3) (𝓡∂ 3) (threeBallScaleDiffeomorph hL) x =
        L • mfderiv (𝓡∂ 3) ThreeModel (Subtype.val : ThreeBall → ThreeSpace) x := by
  let := closedBallChartedSpace hL
  rw [← mfderiv_comp x
    ((isSmoothEmbedding_closedBall_inclusion hL).contMDiff.mdifferentiableAt (by simp))
    ((threeBallScaleDiffeomorph hL).contMDiff.mdifferentiableAt (by simp))]
  change mfderiv (𝓡∂ 3) ThreeModel (fun y : ThreeBall => L • (y : ThreeSpace)) x = _
  let A : ThreeSpace →L[ℝ] ThreeSpace := L • ContinuousLinearMap.id ℝ ThreeSpace
  change mfderiv (𝓡∂ 3) ThreeModel (A ∘ (Subtype.val : ThreeBall → ThreeSpace)) x = _
  rw [mfderiv_comp x A.mdifferentiableAt
    (isSmoothEmbedding_threeBall_inclusion.contMDiff.mdifferentiableAt (by simp)),
    ContinuousLinearMap.mfderiv_eq]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end
