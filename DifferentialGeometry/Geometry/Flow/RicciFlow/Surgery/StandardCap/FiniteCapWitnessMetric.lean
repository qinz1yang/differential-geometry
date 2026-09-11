import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapLocalInsertion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev WitnessE3 := EuclideanSpace ℝ (Fin 3)
private abbrev WitnessIC := (𝓡 2).prod 𝓘(ℝ)
private local instance staticChartedSpace {B : ℝ} {hB : 0 < B} : ChartedSpace WitnessE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance staticIsManifold {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance staticT2Space {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph WitnessIC I ∞ (f i))
variable {F K N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [Fact (Module.finrank ℝ F = 3)] [TopologicalSpace K] {J : ModelWithCorners ℝ F K} [J.Boundaryless]
variable [TopologicalSpace N] [ChartedSpace K N] [T2Space N] [IsManifold J ∞ N]
variable {g : SmoothRiemannianMetric J N} {x₀ : N} {δ : ℝ} {k : ℕ}
variable (d : normalizedDatum g x₀ δ k) {A D ε : ℝ} {hA : 0 < A} {m : ℕ}
variable (w : CanonicalStaticInsertionWitness d A hA D m ε)
variable (b : ι × Bool) (r : ℝ) (hfit : r ≤ cuttingCollarWidth (precision b.1)) (hstatic : r ≤ δ⁻¹)
local notation "WitnessQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "WitnessPatch" => finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj b r

def finiteCapWitnessMetric :
    let : ChartedSpace WitnessE3 WitnessQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ WitnessQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
    SmoothRiemannianMetric (𝓡 3) WitnessPatch := by
  let : ChartedSpace WitnessE3 WitnessQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ WitnessQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
  let : T2Space WitnessQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  exact pullbackMetricOfInjectiveLocalDiffeomorph w.data.outMetric
    (finiteCapInsertionMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit (inv_pos.mpr d.precision_pos) hstatic)
    (isLocalDiffeomorph_finiteCapInsertionMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit (inv_pos.mpr d.precision_pos) hstatic)
    (injective_finiteCapInsertionMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit (inv_pos.mpr d.precision_pos) hstatic)

theorem finiteCapWitnessMetric_inner :
    let : ChartedSpace WitnessE3 WitnessQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ WitnessQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
    ∀ (q : WitnessPatch) (v z : TangentSpace (𝓡 3) q),
      (finiteCapWitnessMetric I hdim hδ f hf hdisj hs d w b r hfit hstatic).inner q v z =
        w.data.outMetric.inner
          (finiteCapInsertionMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit (inv_pos.mpr d.precision_pos) hstatic q)
          (mfderiv (𝓡 3) (𝓡 3)
            (finiteCapInsertionMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit (inv_pos.mpr d.precision_pos) hstatic) q v)
          (mfderiv (𝓡 3) (𝓡 3)
            (finiteCapInsertionMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit (inv_pos.mpr d.precision_pos) hstatic) q z) := by
  let : ChartedSpace WitnessE3 WitnessQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ WitnessQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
  let : T2Space WitnessQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q v z
  exact pullbackMetricOfInjectiveLocalDiffeomorph_inner w.data.outMetric _ _ _ q v z

theorem finiteCapWitnessMap_cap (hr : 0 < r) (x : {v : WitnessE3 // ‖v‖ ≤ transitionEnd}) :
    let : ChartedSpace WitnessE3 WitnessQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
    finiteCapInsertionMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit (inv_pos.mpr d.precision_pos) hstatic
      ⟨finiteCapInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩,
        finiteCapInclusion_mem_restrictedNeighborhood transitionEnd_pos hδ f hf hdisj b hr x⟩ =
          w.data.capInclusion x := by
  let : ChartedSpace WitnessE3 WitnessQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
  exact (finiteCapInsertionMap_cap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit
    (inv_pos.mpr d.precision_pos) hstatic hr x).trans (congrFun w.properties.capInclusion_eq x).symm

theorem finiteCapWitnessMap_collar
    (q : Metric.sphere (0 : WitnessE3) 1 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) (hq : q.2.val < r) :
    let : ChartedSpace WitnessE3 WitnessQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
    finiteCapInsertionMap I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit (inv_pos.mpr d.precision_pos) hstatic
      ⟨finiteCoreInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q),
        (finiteCapRestrictedNeighborhood_collar_iff transitionEnd_pos hδ f hf hdisj b r q).mpr hq⟩ =
          w.data.retainedInclusion (q.1, ⟨q.2.val, q.2.property.1, hq.trans_le hstatic⟩) := by
  let : ChartedSpace WitnessE3 WitnessQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
  exact (finiteCapInsertionMap_collar I hdim transitionEnd_pos hδ f hf hdisj hs b r hfit
    (inv_pos.mpr d.precision_pos) hstatic q hq).trans (congrFun w.properties.retainedInclusion_eq _).symm
end DifferentialGeometry.PDE.RicciFlow.StandardCap
