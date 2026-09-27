import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FinitePreparedMetricOverlap
import DifferentialGeometry.Geometry.Metric.FamilyGluing

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev GluedE3 := EuclideanSpace ℝ (Fin 3)
private abbrev GluedIC := (𝓡 2).prod 𝓘(ℝ)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph GluedIC I ∞ (f i))
local notation "GluedQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (r : ι × Bool → ℝ) (hr : ∀ b, 0 < r b)
local notation "GluedRet" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "GluedOld" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
local notation "GluedB" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
local notation "GluedPatch" b => finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj b (r b)

private def gluingDomain (i : Option GluedB) : Opens GluedQ := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  exact match i with
  | none => GluedOld
  | some b => GluedPatch b.val

omit [IsManifold I ∞ M] in
private theorem gluingDomain_subset_retained (i : Option GluedB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    gluingDomain I hδ f hf hdisj R r i ≤ GluedRet := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  cases i with
  | none => exact inf_le_left
  | some b => exact finiteCapRestrictedNeighborhood_subset_retained transitionEnd_pos hδ f hf hdisj R b.val b.property (r b.val)

include hr in
omit [IsManifold I ∞ M] in
private theorem gluingDomain_cover :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    ∀ x : GluedRet, ∃ i : Option GluedB, x.val ∈ gluingDomain I hδ f hf hdisj R r i := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  dsimp only
  intro x
  have he := Set.ext_iff.mp (finiteCapRetained_restricted_cover transitionEnd_pos hδ f hf hdisj R r hr) x.val
  rcases he.mpr x.property with ho | hc
  · exact ⟨none, ho⟩
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hc
    exact ⟨some b, hb⟩

variable (x₀ : ι → U) (order : ι → ℕ)
variable (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
variable (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
variable {δ' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℝ} {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ}
variable (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (δ' b)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
variable (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
  ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (δ' b) (k' b))
variable (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
variable (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true)
variable {A D ε : ℝ} {hA : 0 < A} {m : ℕ}
variable (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε)
variable (hfit : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, r b.val ≤ cuttingCollarWidth (precision b.val.1))
variable (hstatic : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, r b.val ≤ (δ' b)⁻¹)

private def localMetrics :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    ∀ i : Option GluedB, SmoothRiemannianMetric (𝓡 3) (gluingDomain I hδ f hf hdisj R r i) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  dsimp only
  intro i
  cases i with
  | none => exact finiteOldMetric I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet
  | some b => exact finiteCapWitnessMetric I Fact.out hδ f hf hdisj hs (d b) (w b) b.val (r b.val) (hfit b) (hstatic b)

include hOriginal hmap hside in
private theorem localMetrics_compatible :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    ∀ (i j : Option GluedB) (x : GluedQ)
      (hi : x ∈ gluingDomain I hδ f hf hdisj R r i)
      (hj : x ∈ gluingDomain I hδ f hf hdisj R r j) (v z : TangentSpace (𝓡 3) x),
      (localMetrics I hδ f hf hdisj hs U g R hRet r x₀ order d₀ d w hfit hstatic i).inner ⟨x, hi⟩ v z =
        (localMetrics I hδ f hf hdisj hs U g R hRet r x₀ order d₀ d w hfit hstatic j).inner ⟨x, hj⟩ v z := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  dsimp only
  intro i j x hi hj v z
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some b =>
      exact finitePreparedMetricOverlap_inner I Fact.out hδ f hf hdisj hs U g R hRet
        b.val b.property (r b.val) (hfit b) (d₀ b.val.1) (hOriginal b.val.1)
        (hrec b) (d b) (hmap b) (hside b) (w b) (hstatic b) ⟨x, hj⟩ hi.2 v z
  | some b =>
    cases j with
    | none =>
      exact (finitePreparedMetricOverlap_inner I Fact.out hδ f hf hdisj hs U g R hRet
        b.val b.property (r b.val) (hfit b) (d₀ b.val.1) (hOriginal b.val.1)
        (hrec b) (d b) (hmap b) (hside b) (w b) (hstatic b) ⟨x, hi⟩ hj.2 v z).symm
    | some c =>
      by_cases he : b = c
      · subst c
        rfl
      · have hbc : b.val ≠ c.val := fun he' => he (Subtype.ext he')
        exact (Set.disjoint_left.mp (pairwise_disjoint_finiteCapRestrictedNeighborhoods
          transitionEnd_pos hδ f hf hdisj r hbc) hi hj).elim

def finiteGluedMetric :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    SmoothRiemannianMetric (𝓡 3) GluedRet := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space GluedQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  exact glueMetricFamilyOn (gluingDomain I hδ f hf hdisj R r)
    (localMetrics I hδ f hf hdisj hs U g R hRet r x₀ order d₀ d w hfit hstatic)
    GluedRet (gluingDomain_subset_retained I hδ f hf hdisj R r)
    (gluingDomain_cover I hδ f hf hdisj R r hr)
    (localMetrics_compatible I hδ f hf hdisj hs U g R hRet r x₀ order d₀ hOriginal hrec d hmap hside w hfit hstatic)

theorem finiteGluedMetric_inner_old :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    ∀ (q : GluedOld) (v z : TangentSpace (𝓡 3) q),
      (finiteGluedMetric I hδ f hf hdisj hs U g R hRet r hr x₀ order d₀ hOriginal hrec d hmap hside w hfit hstatic).inner
        (Opens.inclusion inf_le_left q) v z =
          (finiteOldMetric I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet).inner q v z := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space GluedQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q v z
  exact glueMetricFamilyOn_inner (gluingDomain I hδ f hf hdisj R r)
    (localMetrics I hδ f hf hdisj hs U g R hRet r x₀ order d₀ d w hfit hstatic)
    GluedRet (gluingDomain_subset_retained I hδ f hf hdisj R r)
    (gluingDomain_cover I hδ f hf hdisj R r hr)
    (localMetrics_compatible I hδ f hf hdisj hs U g R hRet r x₀ order d₀ hOriginal hrec d hmap hside w hfit hstatic) none q v z

theorem finiteGluedMetric_inner_cap (b : GluedB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    ∀ (q : GluedPatch b.val) (v z : TangentSpace (𝓡 3) q),
      (finiteGluedMetric I hδ f hf hdisj hs U g R hRet r hr x₀ order d₀ hOriginal hrec d hmap hside w hfit hstatic).inner
        (Opens.inclusion (finiteCapRestrictedNeighborhood_subset_retained transitionEnd_pos
          hδ f hf hdisj R b.val b.property (r b.val)) q) v z =
            (finiteCapWitnessMetric I Fact.out hδ f hf hdisj hs (d b) (w b) b.val (r b.val) (hfit b) (hstatic b)).inner q v z := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space GluedQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q v z
  exact glueMetricFamilyOn_inner (gluingDomain I hδ f hf hdisj R r)
    (localMetrics I hδ f hf hdisj hs U g R hRet r x₀ order d₀ d w hfit hstatic)
    GluedRet (gluingDomain_subset_retained I hδ f hf hdisj R r)
    (gluingDomain_cover I hδ f hf hdisj R r hr)
    (localMetrics_compatible I hδ f hf hdisj hs U g R hRet r x₀ order d₀ hOriginal hrec d hmap hside w hfit hstatic) (some b) q v z

theorem finiteGluedMetric_original_inner (p : coreInteriorDomain f)
    (hp : (⟨p.val, interior_subset p.property⟩ : cutCore f) ∈ retainedCore f R)
    (v z : TangentSpace I p) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    (finiteGluedMetric I hδ f hf hdisj hs U g R hRet r hr x₀ order d₀ hOriginal hrec d hmap hside w hfit hstatic).inner
      (Opens.inclusion inf_le_left (finiteRetainedInteriorImage transitionEnd_pos hδ f hf hdisj R p hp))
      (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) p v)
      (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) p z) =
        g.inner ⟨p.val, hRet hp⟩ v z := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  exact (finiteGluedMetric_inner_old I hδ f hf hdisj hs U g R hRet r hr x₀ order d₀ hOriginal hrec d hmap hside w hfit hstatic
    (finiteRetainedInteriorImage transitionEnd_pos hδ f hf hdisj R p hp)
    (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) p v)
    (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) p z)).trans
      (finiteOldMetric_original_inner I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet p hp v z)

end DifferentialGeometry.PDE.RicciFlow.StandardCap
