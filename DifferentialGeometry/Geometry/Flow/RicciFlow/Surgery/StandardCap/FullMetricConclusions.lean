import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricRetainedCore

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
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : SigmaCompactSpace (InsertionQuotient hB) := by
  let : SecondCountableTopology (InsertionQuotient hB) := radialCapAttachment_secondCountableTopology transitionEnd_pos hB
  let : LocallyCompactSpace (InsertionQuotient hB) := ChartedSpace.locallyCompactSpace E3 (InsertionQuotient hB)
  infer_instance
private abbrev Cap := {x : E3 // ‖x‖ ≤ transitionEnd}
private local instance : ChartedSpace (EuclideanHalfSpace 3) Cap := closedBallChartedSpace transitionEnd_pos
private local instance : IsManifold (𝓡∂ 3) ∞ Cap := closedBall_isManifold transitionEnd_pos
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
local notation "Q" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (c : ℝ) (hc : 4 ≤ c)
local notation "Ret" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "Old" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
local notation "B" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
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

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)

private theorem oldCurvature :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    ∀ q : Old,
      metricScalarAt gRet (Opens.inclusion inf_le_left q) = metricScalarAt g (finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet q) ∧
        leastCurvatureOperatorEigenvalueAt gRet (Opens.inclusion inf_le_left q)
          (metricAlgebraicCurvatureTensorAt gRet (Opens.inclusion inf_le_left q)) =
            leastCurvatureOperatorEigenvalueAt g (finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet q)
              (metricAlgebraicCurvatureTensorAt g (finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet q)) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let F := finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet
  have hlocal := isLocalDiffeomorph_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj I Fact.out hs U R hRet
  have hi : _root_.Topology.IsOpenEmbedding F :=
    .of_continuous_injective_isOpenMap hlocal.contMDiff.continuous
      (injective_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet) hlocal.isOpenMap
  let : SecondCountableTopology Old := hi.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace Old := ChartedSpace.locallyCompactSpace E3 Old
  let : SigmaCompactSpace Old := inferInstance
  let old := finiteOldMetric I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let inc : Old → Ret := Opens.inclusion inf_le_left
  have hi : Injective inc := fun _ _ he => Subtype.ext (congrArg (fun q : Ret => q.val) he)
  have hl : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ inc := by
    apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      (contMDiff_inclusion (n := ∞) (show Old ≤ Ret from inf_le_left)) _ rfl
    intro q
    rw [mfderiv_opens_incl]
    exact fun _ _ he => he
  have hm : ∀ (q : Old) (v z : TangentSpace (𝓡 3) q),
      old.inner q v z = gRet.inner (inc q) (mfderiv (𝓡 3) (𝓡 3) inc q v) (mfderiv (𝓡 3) (𝓡 3) inc q z) := by
    intro q v z
    dsimp only [inc]
    rw [mfderiv_opens_incl]
    exact (finiteGluedMetric_inner_old I hδ f hf hdisj hs U g R hRet
      (fun b => (c * precision b.1)⁻¹) (fun b => (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1)
      x₀ order d₀ hOriginal hrec d hmap hside w
      (fun b => (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le) (fun _ => le_rfl) q v z).symm
  dsimp only
  intro q
  have hglobal := curvature_of_injective_local_isometry old gRet inc hl hi hm q
  have horiginal := curvature_of_injective_local_isometry old g (finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet)
    (isLocalDiffeomorph_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj I Fact.out hs U R hRet)
    (injective_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet)
    (finiteOldMetric_inner I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet) q
  exact ⟨hglobal.1.symm.trans horiginal.1, hglobal.2.symm.trans horiginal.2⟩

private theorem globalHamiltonIvey {C : ℕ → ℝ}
    (hw : ∀ b : B, StaticInsertionAdditionalProperties C (w b))
    (a : ℝ) (ha : 0 < a)
    (hin : ∀ p : U, (metricScalarAt g p,
      2 * leastCurvatureOperatorEigenvalueAt g p (metricAlgebraicCurvatureTensorAt g p)) ∈ fixedHamiltonIveyRegion a) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    ∀ q : Ret, (metricScalarAt gRet q,
      2 * leastCurvatureOperatorEigenvalueAt gRet q (metricAlgebraicCurvatureTensorAt gRet q)) ∈ fixedHamiltonIveyRegion a := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q
  have hcover := Set.ext_iff.mp (finiteCapRetained_restricted_cover transitionEnd_pos hδ f hf hdisj R
    (fun b => (c * precision b.1)⁻¹) (fun b => (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1)) q.val
  rcases hcover.mpr q.property with hold | hcap
  · let p : Old := ⟨q.val, hold⟩
    have hq : Opens.inclusion (show Old ≤ Ret from inf_le_left) p = q := rfl
    obtain ⟨hR, hν⟩ := oldCurvature I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w p
    rw [hq] at hR hν
    rw [hR, hν]
    exact hin _
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hcap
    have hrange := range_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    have hq : q ∈ range (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) := hrange.symm ▸ hb
    obtain ⟨p, rfl⟩ := hq
    obtain ⟨hR, hν⟩ := finiteFullPreparedMetric_witness_curvature I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b p
    rw [hR, hν]
    exact (hw b).hamiltonIvey a ha (fun x => hin ((d b).controlledMap x)) p

private theorem globalScalarFloor {C : ℕ → ℝ}
    (hw : ∀ b : B, StaticInsertionAdditionalProperties C (w b))
    (L₀ : ℝ) (hL₀ : L₀ ≤ 0) (hin : ∀ p : U, L₀ ≤ metricScalarAt g p) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    ∀ q : Ret, L₀ ≤ metricScalarAt gRet q := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q
  have hcover := Set.ext_iff.mp (finiteCapRetained_restricted_cover transitionEnd_pos hδ f hf hdisj R
    (fun b => (c * precision b.1)⁻¹) (fun b => (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1)) q.val
  rcases hcover.mpr q.property with hold | hcap
  · let p : Old := ⟨q.val, hold⟩
    have hq : Opens.inclusion (show Old ≤ Ret from inf_le_left) p = q := rfl
    have hR := (oldCurvature I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w p).1
    rw [hq] at hR
    rw [hR]
    exact hin _
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hcap
    have hrange := range_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    have hq : q ∈ range (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) := hrange.symm ▸ hb
    obtain ⟨p, rfl⟩ := hq
    exact hL₀.trans ((finiteFullPreparedMetric_witness_scalar I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w hw b).1 p).le

def FullMetricConclusions (C : ℕ → ℝ) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I Fact.out hδ f hf hdisj R
    let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    SmoothRiemannianMetric (𝓡 3) Ret → Prop :=
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I Fact.out hδ f hf hdisj R
    let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    fun gRet =>
      (let Φ := finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
    let Ψ := retainedCoreDomainMap f R U hRet
    ∀ (p : retainedCore f R) (v z : TangentSpace IR p),
      gRet.inner (Φ p) (mfderiv IR (𝓡 3) Φ p v) (mfderiv IR (𝓡 3) Φ p z) =
        g.inner (Ψ p) (mfderiv IR I Ψ p v) (mfderiv IR I Ψ p z)) ∧
      (∀ (a : ℝ), 0 < a →
      (∀ p : U, (metricScalarAt g p, 2 * leastCurvatureOperatorEigenvalueAt g p (metricAlgebraicCurvatureTensorAt g p)) ∈ fixedHamiltonIveyRegion a) →
      ∀ q : Ret, (metricScalarAt gRet q,
      2 * leastCurvatureOperatorEigenvalueAt gRet q (metricAlgebraicCurvatureTensorAt gRet q)) ∈ fixedHamiltonIveyRegion a) ∧
      (∀ (L₀ : ℝ), L₀ ≤ 0 → (∀ p : U, L₀ ≤ metricScalarAt g p) →
      ∀ q : Ret, L₀ ≤ metricScalarAt gRet q) ∧
      (∀ b : B,
      let cap := (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) ∘ (w b).data.capMap
    ∀ (x : Cap), x.val ∈ deepRegion A → ∀ v z : TangentSpace (𝓡∂ 3) x,
      (scaleMetric (metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) (d b).scalar_pos gRet).inner
        (cap x) (mfderiv (𝓡∂ 3) (𝓡 3) cap x v) (mfderiv (𝓡∂ 3) (𝓡 3) cap x z) =
          (1 - Real.sqrt (c * precision b.val.1)) * metric.inner x.val
            (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x v)
            (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x z)) ∧
      (∀ b : B,
      let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    let Φ := F ∘ (w b).data.windowMap
    let hF := isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    let hiF := injective_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    let hΦ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ Φ :=
      fun q => ((w b).properties.window_local q).comp (𝓡 3) Ret (hF ((w b).data.windowMap q))
    let hiΦ := hiF.comp (w b).properties.window_embedding.isEmbedding.injective
    metricDerivENormSupOn
      {x : modelWindow (D + 1) | (riemannianEDistOf metric 0 x.val).toReal < D} m
      (pullbackMetricOfInjectiveLocalDiffeomorph
        (scaleMetric (metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) (d b).scalar_pos gRet) Φ hΦ hiΦ)
      (metric.restrictOpen (modelWindow (D + 1))) (metric.restrictOpen (modelWindow (D + 1))) < ENNReal.ofReal ε) ∧
      (∀ b : B,
      let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    ∀ (x : Cap), x.val ∈ positiveRegion A → ∀ u v : TangentSpace (𝓡 3) (F ((w b).data.capMap x)),
      gRet.inner (F ((w b).data.capMap x)) u u * gRet.inner (F ((w b).data.capMap x)) v v -
        gRet.inner (F ((w b).data.capMap x)) u v ^ 2 ≠ 0 →
      0 < sectionalCurvature gRet (F ((w b).data.capMap x)) u v) ∧
      (∀ b : B,
      ∀ q ∈ range (w b).data.capMap, ∀ j ≤ m,
      Real.sqrt (normSq0S gRet (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b q) (4 + j)
        (iterCov gRet 4 (metricRm04 gRet) j (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b q))) ≤
          C j * (metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) ^ (1 + (j : ℝ) / 2))

theorem fullMetricConclusions {C : ℕ → ℝ}
    (hw : ∀ b : B, StaticInsertionAdditionalProperties C (w b)) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I Fact.out hδ f hf hdisj R
    let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    FullMetricConclusions I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ d w C
      (finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I Fact.out hδ f hf hdisj R
  let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  exact ⟨finiteFullPreparedMetric_retainedCore_inner I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w,
    fun a ha hin => globalHamiltonIvey I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w hw a ha hin,
    fun L₀ hL₀ hin => globalScalarFloor I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w hw L₀ hL₀ hin,
    fun b => finiteFullPreparedMetric_deep_inner I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w hw b,
    fun b => finiteFullPreparedMetric_window_close I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b,
    fun b => finiteFullPreparedMetric_positive_sectional I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w hw b,
    fun b => finiteFullPreparedMetric_cap_derivatives I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w hw b⟩
end DifferentialGeometry.PDE.RicciFlow.StandardCap
