import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedTubeSystem
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapExhaustiveness
import DifferentialGeometry.Topology.Manifold.ScaledClosedBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalTransitionBridge

set_option autoImplicit false
noncomputable section

open Set Function
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  {ι : Type} [Fintype ι] {δ : ι → ℝ} {L : ℝ}
  (hL : 0 < L) (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1)
  (f : ∀ i : ι, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))

local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

omit [T2Space M] in
def bufferedCutCoreHomeomorph : (T).core ≃ₜ cutCore f :=
  Homeomorph.setCongr (TubeSystem.ofBufferedCharts_core hδ hδ1 f hf hdisj)

omit [T2Space M] in
theorem bufferedCutCoreHomeomorph_boundary (b : ι × Bool) (y : Sphere 2) :
    bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj ((T).coreBoundarySphere b y) =
      cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩ := by
  apply Subtype.ext
  rcases b with ⟨i, side⟩
  cases side <;> rfl

private def scaledThreeBallHomeomorph : ThreeBall ≃ₜ {x : ThreeSpace // ‖x‖ ≤ L} :=
  (DifferentialGeometry.Topology.Handle.closedCellBallHomeo 3).symm.trans (closedBallUnitHomeomorph hL).symm

private theorem scaledThreeBallHomeomorph_boundary (y : Sphere 2) :
    scaledThreeBallHomeomorph hL (sphereToThreeBall y) =
      DifferentialGeometry.Topology.Manifold.Attachment.radialCapBoundary hL y := by
  apply Subtype.ext
  rfl

private def bufferedFiniteCoreMap : C((T).core, Q) :=
  ⟨fun x => finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
      (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj x),
    (isClosedEmbedding_finiteCoreInclusion hL hδ f hf hdisj).continuous.comp
      (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj).continuous⟩

private def bufferedFiniteCapMap (b : ι × Bool) : C(ThreeBall, Q) :=
  ⟨fun x => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj
      ⟨b, scaledThreeBallHomeomorph hL x⟩,
    (isClosedEmbedding_finiteCapInclusion hL hδ f hf hdisj).continuous.comp
      (continuous_sigmaMk.comp (scaledThreeBallHomeomorph hL).continuous)⟩

private theorem range_bufferedFiniteCoreMap :
    range (bufferedFiniteCoreMap hL hδ hδ1 f hf hdisj) =
      range (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj) :=
  (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj).surjective.range_comp
    (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)

private theorem range_bufferedFiniteCapMap (b : ι × Bool) :
    range (bufferedFiniteCapMap hL hδ f hf hdisj b) =
      range (fun x : {x : ThreeSpace // ‖x‖ ≤ L} =>
        finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩) :=
  (scaledThreeBallHomeomorph hL).surjective.range_comp
    (fun x => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩)

def Capping.ofBufferedFiniteCaps : Capping T Q where
  coreInclusion := bufferedFiniteCoreMap hL hδ hδ1 f hf hdisj
  coreEmbedding := (isClosedEmbedding_finiteCoreInclusion hL hδ f hf hdisj).isEmbedding.comp
    (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj).isEmbedding
  cap := bufferedFiniteCapMap hL hδ f hf hdisj
  capEmbedding b :=
    (isClosedEmbedding_finiteCapInclusion hL hδ f hf hdisj).isEmbedding.comp
      (_root_.Topology.IsEmbedding.sigmaMk.comp (scaledThreeBallHomeomorph hL).isEmbedding)
  attaching := fun _ => Homeomorph.refl _
  boundary_eq b y := by
    change ι × Bool at b
    change finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj
        ⟨b, scaledThreeBallHomeomorph hL (sphereToThreeBall y)⟩ =
      finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj ((T).coreBoundarySphere b y))
    rw [scaledThreeBallHomeomorph_boundary, bufferedCutCoreHomeomorph_boundary hδ hδ1 f hf hdisj b y]
    exact finiteCapQuotient_coherence hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩
  exhaustive := by
    change range (bufferedFiniteCoreMap hL hδ hδ1 f hf hdisj) ∪
      (⋃ b : ι × Bool, range (bufferedFiniteCapMap hL hδ f hf hdisj b)) = univ
    rw [range_bufferedFiniteCoreMap]
    simp_rw [range_bufferedFiniteCapMap]
    have h := finiteCapQuotient_cover hL hδ f (fun i => (hf i).injective) hdisj
    rw [union_comm] at h
    convert h using 2
    ext q
    simp only [mem_iUnion, mem_range]
    constructor
    · rintro ⟨b, x, rfl⟩
      exact ⟨⟨b, x⟩, rfl⟩
    · rintro ⟨⟨b, x⟩, rfl⟩
      exact ⟨b, x, rfl⟩
  core_cap_intersection b := by
    rw [range_bufferedFiniteCoreMap hL hδ hδ1 f hf hdisj, range_bufferedFiniteCapMap hL hδ f hf hdisj b,
      finiteCap_core_inter_ball hL hδ f hf hdisj b]
    congr 1
    funext y
    exact congrArg (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
      (bufferedCutCoreHomeomorph_boundary hδ hδ1 f hf hdisj b y).symm
  cap_disjoint := by
    intro b c hbc
    change ι × Bool at b c
    rw [range_bufferedFiniteCapMap hL hδ f hf hdisj b, range_bufferedFiniteCapMap hL hδ f hf hdisj c]
    exact finiteCap_ball_images_disjoint hL hδ f hf hdisj hbc

theorem Capping.ofBufferedFiniteCaps_coreInclusion (x : (T).core) :
    (Capping.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj).coreInclusion x =
      finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj x) := rfl

theorem Capping.ofBufferedFiniteCaps_cap (b : ι × Bool) (x : ThreeBall) :
    (Capping.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj).cap b x =
      finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj
        ⟨b, ⟨L • (x : ThreeSpace), by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
          have hx : ‖(x : ThreeSpace)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
          nlinarith⟩⟩ := rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
