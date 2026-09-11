import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricRetainedCollar
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreInteriorDifferential

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev FullCoreTensorGE3 := EuclideanSpace ℝ (Fin 3)
private abbrev FullCoreTensorGIC := (𝓡 2).prod 𝓘(ℝ)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace FullCoreTensorGE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance : NeZero (Module.finrank ℝ FullCoreTensorGE3) := ⟨by simp⟩
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
private abbrev FullCoreTensorIH := ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)
private abbrev FullCoreTensorIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev FullCoreTensorS2 := Metric.sphere (0 : FullCoreTensorGE3) 1
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph FullCoreTensorGIC I ∞ (f i))
local notation "FullCoreTensorGQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (c : ℝ) (hc : 4 ≤ c)
local notation "FullCoreTensorGRet" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "FullCoreTensorGOld" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
local notation "FullCoreTensorGB" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
variable (x₀ : ι → U) (order : ι → ℕ)
variable (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
variable (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
variable {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ}
variable (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
variable (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
  ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
variable (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
variable (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true)
variable {A D ε : ℝ} {hA : 0 < A} {m : ℕ}
variable (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε)

theorem finiteFullPreparedMetric_retainedCore_interior (p : retainedCore f R)
    (hp : p.val.val ∈ interior (cutCore f)) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace FullCoreTensorIH (retainedCore f R) := retainedCoreChartedSpace I Fact.out hδ f hf hdisj R
    let : ChartedSpace FullCoreTensorGE3 FullCoreTensorGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullCoreTensorGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let Φ := finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
    let Ψ := retainedCoreDomainMap f R U hRet
    ∀ (v z : TangentSpace FullCoreTensorIR p),
      gRet.inner (Φ p) (mfderiv FullCoreTensorIR (𝓡 3) Φ p v) (mfderiv FullCoreTensorIR (𝓡 3) Φ p z) =
        g.inner (Ψ p) (mfderiv FullCoreTensorIR I Ψ p v) (mfderiv FullCoreTensorIR I Ψ p z) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullCoreTensorIH (retainedCore f R) := retainedCoreChartedSpace I Fact.out hδ f hf hdisj R
  let : ChartedSpace FullCoreTensorGE3 FullCoreTensorGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullCoreTensorGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let Φ := finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
  let Ψ := retainedCoreDomainMap f R U hRet
  dsimp only
  intro v z
  have hd : mfderiv FullCoreTensorIR (𝓡 3) Φ p =
      (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj)
        (⟨p.val.val, hp⟩ : coreInteriorDomain f)).comp (mfderiv FullCoreTensorIR I Ψ p) :=
    finiteRetainedCoreInclusion_mfderiv_interior I Fact.out transitionEnd_pos hδ f hf hdisj hs R U hRet p hp
  change gRet.inner (Φ p) (mfderiv FullCoreTensorIR (𝓡 3) Φ p v) (mfderiv FullCoreTensorIR (𝓡 3) Φ p z) =
    g.inner (Ψ p) (mfderiv FullCoreTensorIR I Ψ p v) (mfderiv FullCoreTensorIR I Ψ p z)
  rw [hd]
  exact finiteFullPreparedMetric_original_inner I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    ⟨p.val.val, hp⟩ p.property (mfderiv FullCoreTensorIR I Ψ p v) (mfderiv FullCoreTensorIR I Ψ p z)

theorem finiteFullPreparedMetric_retainedCore_inner :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace FullCoreTensorIH (retainedCore f R) := retainedCoreChartedSpace I Fact.out hδ f hf hdisj R
    let : ChartedSpace FullCoreTensorGE3 FullCoreTensorGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullCoreTensorGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let Φ := finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
    let Ψ := retainedCoreDomainMap f R U hRet
    ∀ (p : retainedCore f R) (v z : TangentSpace FullCoreTensorIR p),
      gRet.inner (Φ p) (mfderiv FullCoreTensorIR (𝓡 3) Φ p v) (mfderiv FullCoreTensorIR (𝓡 3) Φ p z) =
        g.inner (Ψ p) (mfderiv FullCoreTensorIR I Ψ p v) (mfderiv FullCoreTensorIR I Ψ p z) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullCoreTensorIH (retainedCore f R) := retainedCoreChartedSpace I Fact.out hδ f hf hdisj R
  let : ChartedSpace FullCoreTensorGE3 FullCoreTensorGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullCoreTensorGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let Φ := finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
  let Ψ := retainedCoreDomainMap f R U hRet
  dsimp only
  intro p v z
  by_cases hp : p.val.val ∈ interior (cutCore f)
  · exact finiteFullPreparedMetric_retainedCore_interior I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w p hp v z
  · have hfront : p.val ∈ range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
      rw [range_cuttingSphereAttachment hδ f hf hdisj]
      exact ⟨subset_closure p.val.property, hp⟩
    obtain ⟨⟨b, y⟩, he⟩ := hfront
    have hb : cuttingSphereComponent hδ f hf hdisj b ∈ R :=
      (cuttingSphere_mem_retainedCore_iff hδ f hf hdisj R b y).mp (he.symm ▸ p.property)
    let b' : FullCoreTensorGB := ⟨b, hb⟩
    let hB := (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1
    let q : FullCoreTensorS2 × Ico (0 : ℝ) (c * precision b.1)⁻¹ := (y, ⟨0, le_rfl, hB⟩)
    let κ := finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b' (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).2.le
    have hq : κ q = p := Subtype.ext
      ((finiteRetainedCollarCoreMap_zero transitionEnd_pos hδ f hf hdisj R b'
        (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).2.le hB y).trans he)
    have h : ∀ (v' z' : TangentSpace FullCoreTensorIR (κ q)),
        gRet.inner (Φ (κ q)) (mfderiv FullCoreTensorIR (𝓡 3) Φ (κ q) v') (mfderiv FullCoreTensorIR (𝓡 3) Φ (κ q) z') =
          g.inner (Ψ (κ q)) (mfderiv FullCoreTensorIR I Ψ (κ q) v') (mfderiv FullCoreTensorIR I Ψ (κ q) z') :=
      finiteFullPreparedMetric_retainedCore_collar I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b' q
    rw [hq] at h
    exact h v z
end DifferentialGeometry.PDE.RicciFlow.StandardCap
