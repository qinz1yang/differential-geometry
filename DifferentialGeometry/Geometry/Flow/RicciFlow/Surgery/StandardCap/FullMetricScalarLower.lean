import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricSeam
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ScalarLowerBound
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapExhaustiveness

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
  DifferentialGeometry.Topology.ThreeManifold.Surgery
  DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
local notation "Q" => FiniteCapQuotient transitionEnd_pos hδ f (fun i =>
  _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i)))
  hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (c : ℝ) (hc : 4 ≤ c)
local notation "Ret" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "Old" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
local notation "Boundary" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
variable (x₀ : ι → U) (order : ι → ℕ)
variable (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
variable (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
variable {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ}
variable (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision
  b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
variable (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
  ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
variable (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map =
  (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
variable (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d
  b).retainedSide = true)
variable {A D ε : ℝ} {hA : 0 < A} {m : ℕ}
variable (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
  CanonicalStaticInsertionWitness (d b) A hA D m ε)

omit [SigmaCompactSpace M] in
theorem finiteFullPreparedMetric_cap_scalar_lower_bound_of_local
    (Qmin : ℝ)
    (hlower : ∀ b : Boundary, ∀ x ∈ range (w b).data.capMap,
      metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) / 2 ≤
        metricScalarAt (w b).data.outMetric x)
    (hscale : ∀ b : Boundary,
      Qmin ≤ metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    ∀ q : Ret, q.val ∈ range (finiteCapInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) →
      Qmin / 2 ≤ metricScalarAt gRet q := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q hcap
  obtain ⟨⟨b, x⟩, hx⟩ := hcap
  have hb : cuttingSphereComponent hδ f hf hdisj b ∈ R := by
    have hq := q.property
    rw [← hx] at hq
    exact hq
  let b' : Boundary := ⟨b, hb⟩
  have hplaced : finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b'
      ((w b').data.capMap x) = q := by
    rw [(w b').properties.capMap_eq, (w b').properties.capInclusion_eq]
    apply Subtype.ext
    exact (congrArg (fun p : finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj
        b ((c * precision b.1)⁻¹) => p.val)
      (finiteCapFullInsertionDiffeomorph_symm_cap I Fact.out transitionEnd_pos hδ f hf hdisj
        hs b (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).2.le
        (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1 x)).trans hx
  have hscalar := (finiteFullPreparedMetric_witness_curvature I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b' ((w b').data.capMap x)).1
  rw [hplaced] at hscalar
  rw [hscalar]
  exact (div_le_div_of_nonneg_right (hscale b') (by norm_num)).trans (hlower b' _ ⟨x, rfl⟩)


end DifferentialGeometry.PDE.RicciFlow.StandardCap
