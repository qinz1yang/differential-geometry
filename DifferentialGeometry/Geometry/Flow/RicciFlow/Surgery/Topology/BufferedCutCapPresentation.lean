import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedFiniteCapping
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapDecomposition

set_option autoImplicit false
noncomputable section

open Set Function
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  {ι : Type} [Fintype ι] {δ : ι → ℝ} {L : ℝ}
  (hL : 0 < L) (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1)
  (f : ∀ i : ι, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (R : Set (ConnectedComponents (cutCore f)))

local notation "Q" => FiniteCapQuotient hL hδ f
  (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
private local instance : LocallyPathConnectedSpace M := originalModel_locallyPathConnected ThreeModel (by simp)
local notation "Ret" => finiteCapRetained hL hδ f hf hdisj R
local notation "Disc" => finiteCapDiscarded hL hδ f hf hdisj R
local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj

noncomputable def CutCapTopology.ofBufferedFiniteCaps
    (hnontrivial : Nonempty ι ∨ Nonempty (DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f Rᶜ)) :
    CutCapTopology M Ret Disc Q where
  tubes := T
  capping := Capping.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj
  presentation := by
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q := finiteCapChartedSpace ThreeModel (by simp) hL hδ f hf hdisj
    exact (finiteCapSelectedDiffeomorph ThreeModel (by simp) hL hδ f hf hdisj R).symm.toHomeomorph
  nontrivial := hnontrivial.imp id ((finiteCapRetained_nonempty_iff_core hL hδ f hf hdisj Rᶜ).mpr)

theorem CutCapTopology.ofBufferedFiniteCaps_tubes
    (hnontrivial : Nonempty ι ∨ Nonempty (DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f Rᶜ)) :
    (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).tubes = T := rfl

theorem CutCapTopology.ofBufferedFiniteCaps_presentation
    (hnontrivial : Nonempty ι ∨ Nonempty (DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f Rᶜ)) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q := finiteCapChartedSpace ThreeModel (by simp) hL hδ f hf hdisj
    (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).presentation =
      (finiteCapSelectedDiffeomorph ThreeModel (by simp) hL hδ f hf hdisj R).symm.toHomeomorph := rfl

theorem CutCapTopology.ofBufferedFiniteCaps_retainedCore
    (hnontrivial : Nonempty ι ∨ Nonempty (DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f Rᶜ)) :
    (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).retainedCore =
      (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj) ⁻¹' DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f R := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q := finiteCapChartedSpace ThreeModel (by simp) hL hδ f hf hdisj
  ext x
  change (∃ q : Ret,
      (finiteCapSelectedDiffeomorph ThreeModel (by simp) hL hδ f hf hdisj R).symm
        (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
          (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj x)) = Sum.inl q) ↔
    bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj x ∈ DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f R
  constructor
  · rintro ⟨q, hq⟩
    have hh := congrArg (finiteCapSelectedDiffeomorph ThreeModel (by simp) hL hδ f hf hdisj R) hq
    rw [Diffeomorph.apply_symm_apply, finiteCapSelectedDiffeomorph_inl] at hh
    have hm : finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj x) ∈ Ret := hh ▸ q.property
    exact hm
  · intro hx
    exact ⟨⟨_, hx⟩, finiteCapSelectedDiffeomorph_symm_retained ThreeModel (by simp)
      hL hδ f hf hdisj R
      (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj x)) hx⟩


theorem CutCapTopology.ofBufferedFiniteCaps_retainedBoundary_iff
    (hnontrivial : Nonempty ι ∨ Nonempty (DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f Rᶜ))
    (b : ι × Bool) :
    (∀ y : Sphere 2, (TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj).coreBoundarySphere b y ∈
      (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).retainedCore) ↔
      cuttingSphereComponent hδ f hf hdisj b ∈ R := by
  constructor
  · intro hb
    have hh := hb spherePoint
    rw [CutCapTopology.ofBufferedFiniteCaps_retainedCore] at hh
    change bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj
      ((TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj).coreBoundarySphere b spherePoint) ∈
      DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f R at hh
    erw [bufferedCutCoreHomeomorph_boundary hδ hδ1 f hf hdisj b spherePoint] at hh
    exact (cuttingSphere_mem_retainedCore_iff hδ f hf hdisj R b spherePoint).mp hh
  · intro hb y
    rw [CutCapTopology.ofBufferedFiniteCaps_retainedCore]
    change bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj
      ((TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj).coreBoundarySphere b y) ∈
      DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f R
    erw [bufferedCutCoreHomeomorph_boundary hδ hδ1 f hf hdisj b y]
    exact (cuttingSphere_mem_retainedCore_iff hδ f hf hdisj R b y).mpr hb

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
