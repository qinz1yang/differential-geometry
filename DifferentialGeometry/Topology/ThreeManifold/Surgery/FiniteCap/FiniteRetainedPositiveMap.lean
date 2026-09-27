import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapPositiveOverlap
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapPatchSelection
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteRetainedInterior

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev RetPosE3 := EuclideanSpace ℝ (Fin 3)
private abbrev RetPosIC := (𝓡 2).prod 𝓘(ℝ)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph RetPosIC I ∞ (f i))
variable (R : Set (ConnectedComponents (cutCore f))) (b : ι × Bool)
variable (hb : cuttingSphereComponent hδ f hf hdisj b ∈ R)
variable (r : ℝ) (hfit : r ≤ cuttingCollarWidth (precision b.1))
local notation "RetPosQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "RetPosPatch" => finiteCapRestrictedNeighborhood hL hδ f hf hdisj b r
local notation "RetPosOld" => finiteRetainedInteriorOpens hL hδ f hf hdisj R

def finiteRetainedPositiveMap :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace RetPosE3 RetPosQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    positiveCuttingCylinder r → RetPosOld := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace RetPosE3 RetPosQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  dsimp only
  intro q
  let p := finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit q
  exact ⟨p.val, finiteCapRestrictedNeighborhood_subset_retained hL hδ f hf hdisj R b hb r p.property,
    finiteCapPositiveMap_mem_old I hdim hL hδ f hf hdisj hs b r hfit q⟩

theorem finiteRetainedPositiveMap_val (q : positiveCuttingCylinder r) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace RetPosE3 RetPosQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    (finiteRetainedPositiveMap I hdim hL hδ f hf hdisj hs R b hb r hfit q).val =
      (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit q).val := rfl

theorem contMDiff_finiteRetainedPositiveMap :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace RetPosE3 RetPosQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ContMDiff RetPosIC (𝓡 3) ∞ (finiteRetainedPositiveMap I hdim hL hδ f hf hdisj hs R b hb r hfit) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace RetPosE3 RetPosQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  apply (ContMDiff.subtypeVal_comp_iff RetPosOld (finiteRetainedPositiveMap I hdim hL hδ f hf hdisj hs R b hb r hfit)).mp
  exact (contMDiff_subtype_val (U := RetPosPatch)).comp
    (contMDiff_finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit)

theorem finiteRetainedPositiveMap_mfderiv (q : positiveCuttingCylinder r) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace RetPosE3 RetPosQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    mfderiv RetPosIC (𝓡 3) (finiteRetainedPositiveMap I hdim hL hδ f hf hdisj hs R b hb r hfit) q =
      mfderiv RetPosIC (𝓡 3) (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit) q := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace RetPosE3 RetPosQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let alpha := finiteRetainedPositiveMap I hdim hL hδ f hf hdisj hs R b hb r hfit
  let beta := finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit
  have ha := contMDiff_finiteRetainedPositiveMap I hdim hL hδ f hf hdisj hs R b hb r hfit
  have hb' := contMDiff_finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit
  have he : (Subtype.val : RetPosOld → RetPosQ) ∘ alpha = (Subtype.val : RetPosPatch → RetPosQ) ∘ beta := rfl
  have hleft : mfderiv RetPosIC (𝓡 3) ((Subtype.val : RetPosOld → RetPosQ) ∘ alpha) q =
      mfderiv RetPosIC (𝓡 3) alpha q := by
    rw [mfderiv_comp q ((contMDiff_subtype_val (U := RetPosOld) (n := ∞)).mdifferentiable (by simp) (alpha q))
      (ha.mdifferentiable (by simp) q), mfderiv_subtype_val]
    rfl
  have hright : mfderiv RetPosIC (𝓡 3) ((Subtype.val : RetPosPatch → RetPosQ) ∘ beta) q =
      mfderiv RetPosIC (𝓡 3) beta q := by
    rw [mfderiv_comp q ((contMDiff_subtype_val (U := RetPosPatch) (n := ∞)).mdifferentiable (by simp) (beta q))
      (hb'.mdifferentiable (by simp) q), mfderiv_subtype_val]
    rfl
  exact hleft.symm.trans ((mfderiv_congr he).trans hright)

theorem finiteRetainedPositiveMap_original_point (U : Opens M)
    (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
    (q : positiveCuttingCylinder r) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace RetPosE3 RetPosQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet
      (finiteRetainedPositiveMap I hdim hL hδ f hf hdisj hs R b hb r hfit q)).val =
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b
          (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.trans_le hfit⟩)).val := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace RetPosE3 RetPosQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let alpha := finiteRetainedPositiveMap I hdim hL hδ f hf hdisj hs R b hb r hfit
  let x := (finiteCoreInteriorHomeomorph hL hδ f hf hdisj).symm (Opens.inclusion inf_le_right (alpha q))
  have hh := finiteRetainedInterior_original_point hL hδ f hf hdisj R (alpha q)
  have he := hh.trans (finiteCapPositiveMap_original I hdim hL hδ f hf hdisj hs b r hfit q)
  change finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
      (⟨x.val, interior_subset x.property⟩ : cutCore f) = _ at he
  have hcore := injective_finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj he
  exact congrArg (fun p : cutCore f => p.val) hcore
end DifferentialGeometry.Topology.ThreeManifold.Surgery
