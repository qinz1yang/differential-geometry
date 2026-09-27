import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.PositiveCuttingCoordinates
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapRestrictedSmooth
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev OverlapE3 := EuclideanSpace ℝ (Fin 3)
private abbrev OverlapIC := (𝓡 2).prod 𝓘(ℝ)
private theorem annulus_subset_ball (L r : ℝ) : positiveCuttingAnnulus L r ≤ finiteCapRestrictedBall L r :=
  fun _ hx => hx.2
private def annulusInclusion (L r : ℝ) : positiveCuttingAnnulus L r → finiteCapRestrictedBall L r :=
  Opens.inclusion (annulus_subset_ball L r)
private theorem annulusInclusion_local (L r : ℝ) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (annulusInclusion L r) := by
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (contMDiff_inclusion (annulus_subset_ball L r)) _ rfl
  intro x
  rw [mfderiv_opens_incl]
  exact fun _ _ he => he
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph OverlapIC I ∞ (f i))
variable (b : ι × Bool) (r : ℝ) (hfit : r ≤ cuttingCollarWidth (precision b.1))
local notation "OverlapQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "OverlapPatch" => finiteCapRestrictedNeighborhood hL hδ f hf hdisj b r

def finiteCapPositiveMap :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    positiveCuttingCylinder r → OverlapPatch := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact (finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit).symm ∘
    annulusInclusion L r ∘ positiveCuttingDiffeomorph hL r

theorem contMDiff_finiteCapPositiveMap :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ContMDiff OverlapIC (𝓡 3) ∞ (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit) := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact (finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit).symm.contMDiff.comp
    ((contMDiff_inclusion (annulus_subset_ball L r)).comp (positiveCuttingDiffeomorph hL r).contMDiff)

theorem injective_finiteCapPositiveMap :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Injective (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit) := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  have hj : Injective (annulusInclusion L r) := fun _ _ he =>
    Subtype.ext (congrArg (fun x : finiteCapRestrictedBall L r => x.val) he)
  exact (finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit).symm.injective.comp
    (hj.comp (positiveCuttingDiffeomorph hL r).injective)

theorem isLocalDiffeomorph_finiteCapPositiveMap :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsLocalDiffeomorph OverlapIC (𝓡 3) ∞ (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit) := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let P := finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit
  let D := positiveCuttingDiffeomorph hL r
  dsimp only
  intro q
  exact ((D.isLocalDiffeomorph q).comp (𝓡 3) (finiteCapRestrictedBall L r)
    (annulusInclusion_local L r (D q))).comp (𝓡 3) OverlapPatch
      (P.symm.isLocalDiffeomorph (annulusInclusion L r (D q)))

theorem finiteCapPositiveMap_mfderiv_surjective (q : positiveCuttingCylinder r) :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Surjective (mfderiv OverlapIC (𝓡 3) (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit) q) := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact ((isLocalDiffeomorph_finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit).mfderivToContinuousLinearEquiv (by simp) q).surjective

theorem finiteCapPositiveMap_original (q : positiveCuttingCylinder r) :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit q).val =
      finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b
          (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.trans_le hfit⟩)) := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact finiteCapOpenChart_symm_collar hL hδ f hf hdisj b
    (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.trans_le hfit⟩)

theorem finiteCapPositiveMap_mem_old (q : positiveCuttingCylinder r) :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit q).val ∈
      finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  rw [finiteCapPositiveMap_original]
  exact (finiteCoreInterior_collar_iff hL hδ f hf hdisj b _).mpr q.property.1

theorem range_finiteCapPositiveMap :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    range (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit) =
      {q : OverlapPatch | q.val ∈ finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj} := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let P := finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit
  let D := positiveCuttingDiffeomorph hL r
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact finiteCapPositiveMap_mem_old I hdim hL hδ f hf hdisj hs b r hfit p
  · intro hq
    have hh : finiteCapOpenChart hL hδ f hf hdisj b q.val ∈
        finiteCapOpenChart hL hδ f hf hdisj b ''
          ((finiteCapOpenChart hL hδ f hf hdisj b).source ∩
            finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj) :=
      ⟨q.val, ⟨q.property.1, hq⟩, rfl⟩
    rw [finiteCapOpenChart_interior_overlap_image] at hh
    let x : positiveCuttingAnnulus L r := ⟨(P q).val, hh.1, (P q).property⟩
    refine ⟨D.symm x, ?_⟩
    apply P.injective
    change P (P.symm (annulusInclusion L r (D (D.symm x)))) = P q
    exact (P.apply_symm_apply _).trans
      (Subtype.ext (congrArg (fun y : positiveCuttingAnnulus L r => y.val) (D.apply_symm_apply x)))
end DifferentialGeometry.Topology.ThreeManifold.Surgery
