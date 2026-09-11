import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricBoundaryCollar
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreCollarDifferential
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreSmoothEmbedding
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreDomainSmooth

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
private abbrev RetTensorGE3 := EuclideanSpace ℝ (Fin 3)
private abbrev RetTensorGIC := (𝓡 2).prod 𝓘(ℝ)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace RetTensorGE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance : NeZero (Module.finrank ℝ RetTensorGE3) := ⟨by simp⟩
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
private abbrev RetTensorIH := ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)
private abbrev RetTensorIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev RetTensorS2 := Metric.sphere (0 : RetTensorGE3) 1
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph RetTensorGIC I ∞ (f i))
local notation "RetTensorGQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (c : ℝ) (hc : 4 ≤ c)
local notation "RetTensorGRet" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "RetTensorGOld" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
local notation "RetTensorGB" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
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

theorem finiteFullPreparedMetric_retainedCore_collar (b : RetTensorGB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace RetTensorIH (retainedCore f R) := retainedCoreChartedSpace I Fact.out hδ f hf hdisj R
    let : ChartedSpace RetTensorGE3 RetTensorGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ RetTensorGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let κ := finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le
    let Φ := finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
    let Ψ := retainedCoreDomainMap f R U hRet
    ∀ (q : RetTensorS2 × Ico (0 : ℝ) (c * precision b.val.1)⁻¹)
      (v z : TangentSpace RetTensorIR (κ q)),
      gRet.inner (Φ (κ q)) (mfderiv RetTensorIR (𝓡 3) Φ (κ q) v) (mfderiv RetTensorIR (𝓡 3) Φ (κ q) z) =
        g.inner (Ψ (κ q)) (mfderiv RetTensorIR I Ψ (κ q) v) (mfderiv RetTensorIR I Ψ (κ q) z) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace RetTensorIH (retainedCore f R) := retainedCoreChartedSpace I Fact.out hδ f hf hdisj R
  let : ChartedSpace RetTensorGE3 RetTensorGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ RetTensorGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let hB := (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (c * precision b.val.1)⁻¹) := halfClosedIntervalChartedSpace hB
  let κ := finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le
  let Φ := finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
  let Ψ := retainedCoreDomainMap f R U hRet
  have hκ : ContMDiff RetTensorIR RetTensorIR ∞ κ := finiteRetainedCollarCoreMap_contMDiff I Fact.out transitionEnd_pos hδ f hf hdisj hs R b hB (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le
  have hΦ : ContMDiff RetTensorIR (𝓡 3) ∞ Φ := (finiteRetainedCoreInclusion_isSmoothEmbedding I Fact.out transitionEnd_pos hδ f hf hdisj hs R).contMDiff
  have hΨ : ContMDiff RetTensorIR I ∞ Ψ := (retainedCoreDomainMap_isSmoothEmbedding I Fact.out hδ f hf hdisj hs R U hRet).contMDiff
  dsimp only
  intro q v z
  have hb : Surjective (mfderiv RetTensorIR RetTensorIR κ q) :=
    (finiteRetainedCollarCoreMap_mfderiv_bijective I Fact.out transitionEnd_pos hδ f hf hdisj hs R b hB
      (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le q).2
  obtain ⟨v₀, rfl⟩ := hb v
  obtain ⟨z₀, rfl⟩ := hb z
  have hΦd (u : TangentSpace RetTensorIR q) :
      mfderiv RetTensorIR (𝓡 3) (Φ ∘ κ) q u =
        mfderiv RetTensorIR (𝓡 3) Φ (κ q) (mfderiv RetTensorIR RetTensorIR κ q u) :=
    congrArg (fun A : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] RetTensorGE3 => A u)
      (mfderiv_comp q (hΦ.mdifferentiableAt (by simp)) (hκ.mdifferentiableAt (by simp)))
  have hΨd (u : TangentSpace RetTensorIR q) :
      mfderiv RetTensorIR I (Ψ ∘ κ) q u =
        mfderiv RetTensorIR I Ψ (κ q) (mfderiv RetTensorIR RetTensorIR κ q u) :=
    congrArg (fun A : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] E => A u)
      (mfderiv_comp q (hΨ.mdifferentiableAt (by simp)) (hκ.mdifferentiableAt (by simp)))
  have h := finiteFullPreparedMetric_closed_collar I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b q v₀ z₀
  rw [hΦd, hΦd, hΨd, hΨd] at h
  exact h
end DifferentialGeometry.PDE.RicciFlow.StandardCap
