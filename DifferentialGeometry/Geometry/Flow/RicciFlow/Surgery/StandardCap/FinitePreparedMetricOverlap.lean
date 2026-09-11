import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FiniteMetricOverlap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.PreparedCollarCorrespondence
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeckManifold

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev PreparedOverlapE3 := EuclideanSpace ℝ (Fin 3)
private abbrev PreparedOverlapIC := (𝓡 2).prod 𝓘(ℝ)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph PreparedOverlapIC I ∞ (f i))
local notation "PreparedOverlapQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (b : ι × Bool) (hb : cuttingSphereComponent hδ f hf hdisj b ∈ R)
variable (r : ℝ) (hfit : r ≤ cuttingCollarWidth (precision b.1))

variable {x₀ : U} {k₀ k : ℕ} {δ : ℝ}
variable (d₀ : normalizedDatum g x₀ (precision b.1) k₀)
variable (hOriginal : f b.1 = neckAmbientMap U d₀)
variable (hrec : δ⁻¹ + 1 ≤ (precision b.1)⁻¹)
variable (d : normalizedDatum g (d₀.offsetPoint (cuttingSign_sq b.2)) δ k)
variable (hmap : d.map = d₀.recenteringMap (cuttingSign_sq b.2) hrec) (hside : d.retainedSide = true)
variable {A D ε : ℝ} {hA : 0 < A} {m : ℕ} (w : CanonicalStaticInsertionWitness d A hA D m ε)
variable (hstatic : r ≤ δ⁻¹)
local notation "PreparedOverlapPatch" => finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj b r

include hOriginal hmap hside in
theorem finitePreparedMetricOverlap_inner :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace PreparedOverlapE3 PreparedOverlapQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ PreparedOverlapQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
    ∀ (q : PreparedOverlapPatch)
      (hq : q.val ∈ finiteCoreInterior transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj)
      (v z : TangentSpace (𝓡 3) q),
      (finiteOldMetric I hdim transitionEnd_pos hδ f hf hdisj hs U g R hRet).inner
        ⟨q.val, finiteCapRestrictedNeighborhood_subset_retained transitionEnd_pos hδ f hf hdisj R b hb r q.property, hq⟩ v z =
          (finiteCapWitnessMetric I hdim hδ f hf hdisj hs d w b r hfit hstatic).inner q v z := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace PreparedOverlapE3 PreparedOverlapQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ PreparedOverlapQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
  apply finiteMetricOverlap_inner I hdim hδ f hf hdisj hs U g R hRet b hb r hfit d w hstatic
  intro p
  have h := preparedDatum_positive_collar d₀ b.2 hrec d hmap hside hfit hstatic p
  have hv := congrArg (fun x : U => x.val) h
  refine hv.trans ?_
  change (neckAmbientMap U d₀) (cuttingCollarCylinderMap (hδ b.1) b.2
    (p.val.1, ⟨p.val.2, p.property.1.le, p.property.2.trans_le hfit⟩)) =
      f b.1 (cuttingCollarCylinderMap (hδ b.1) b.2
        (p.val.1, ⟨p.val.2, p.property.1.le, p.property.2.trans_le hfit⟩))
  rw [hOriginal]
end DifferentialGeometry.PDE.RicciFlow.StandardCap
