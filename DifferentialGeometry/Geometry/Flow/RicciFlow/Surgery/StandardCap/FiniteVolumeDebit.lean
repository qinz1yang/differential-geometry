import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.VolumeMargin
import DifferentialGeometry.Geometry.Neck.RetainedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitnessVolume

noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private def retainedIndexEquiv {ι : Type*} (P : ι × Bool → Prop)
    (hside : ∀ i, P (i, true) ∧ ¬ P (i, false)) : {b : ι × Bool // P b} ≃ ι where
  toFun b := b.val.1
  invFun i := ⟨(i, true), (hside i).1⟩
  left_inv := by
    rintro ⟨⟨i, side⟩, hi⟩
    cases side with
    | false => exact ((hside i).2 hi).elim
    | true => rfl
  right_inv _ := rfl

private abbrev CurvGE3 := EuclideanSpace ℝ (Fin 3)
private abbrev CurvCap := {x : EuclideanSpace ℝ (Fin 3) // ‖x‖ ≤ transitionEnd}
private local instance : CompactSpace CurvCap :=
  (closedBallUnitHomeomorph transitionEnd_pos).symm.compactSpace
private local instance : ChartedSpace (EuclideanHalfSpace 3) CurvCap := closedBallChartedSpace transitionEnd_pos
private local instance : IsManifold (𝓡∂ 3) ∞ CurvCap := closedBall_isManifold transitionEnd_pos
private abbrev CurvGIC := (𝓡 2).prod 𝓘(ℝ)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace CurvGE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance : NeZero (Module.finrank ℝ CurvGE3) := ⟨by simp⟩
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : SigmaCompactSpace (InsertionQuotient hB) := by
  let : SecondCountableTopology (InsertionQuotient hB) := radialCapAttachment_secondCountableTopology transitionEnd_pos hB
  let : LocallyCompactSpace (InsertionQuotient hB) := ChartedSpace.locallyCompactSpace CurvGE3 (InsertionQuotient hB)
  infer_instance
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph CurvGIC I ∞ (f i))
local notation "CurvGQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (c : ℝ) (hc : 4 ≤ c)
local notation "CurvGRet" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "CurvGOld" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
local notation "CurvGB" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
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

private local instance {B : ℝ} {hB : 0 < B} :
    MeasurableSpace (InsertionQuotient hB) := borel (InsertionQuotient hB)
private local instance {B : ℝ} {hB : 0 < B} : BorelSpace (InsertionQuotient hB) := ⟨rfl⟩

theorem finiteFullPreparedMetric_volume_add_negative_bands_le [CompactSpace M]
    (hδquarter : ∀ i, precision i ≤ 1 / 4)
    (hneg : ∀ i, cuttingSphereComponent hδ f hf hdisj (i, false) ∉ R) :
    let : SecondCountableTopology H := I.secondCountableTopology
    let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let : CompactSpace CurvGQ := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
    let : CompactSpace CurvGRet :=
      (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    riemannianVolumeMeasure (𝓡 3) CurvGRet gRet univ +
      ∑' i : ι, ENNReal.ofReal (2 * Real.pi / precision i) *
        ENNReal.ofReal ((metricScalarAt g (x₀ i)) ^ (-3 / 2 : ℝ)) ≤
      riemannianVolumeMeasure I U g
        (range (retainedCoreDomainMap f R U hRet) ∪
          ⋃ i : ι, (d₀ i).map '' {q | q.val.2 ∈ Icc (-(precision i)⁻¹) (-1 : ℝ)}) +
      ∑' b : CurvGB, riemannianVolumeMeasure (𝓡 3)
        (InsertionQuotient (inv_pos.mpr (d b).precision_pos))
        (w b).data.outMetric (range (w b).data.capMap) := by
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace CurvGQ := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : CompactSpace CurvGRet :=
    (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
  dsimp only
  have hout := finiteFullPreparedMetric_volume_le I hδ f hf hdisj hs U g R hRet c hc
    x₀ order d₀ hOriginal hrec d hmap hside w
  have hin := retained_core_add_negative_bands_volume_le U g x₀ order d₀ f hf hdisj hOriginal R hRet
    hδquarter hneg
  have h₁ := add_le_add_left hout
    (∑' i : ι, ENNReal.ofReal (2 * Real.pi / precision i) *
      ENNReal.ofReal ((metricScalarAt g (x₀ i)) ^ (-3 / 2 : ℝ)))
  have h₂ := add_le_add_left hin
    (∑' b : CurvGB, riemannianVolumeMeasure (𝓡 3)
      (InsertionQuotient (inv_pos.mpr (d b).precision_pos)) (w b).data.outMetric (range (w b).data.capMap))
  rw [add_right_comm] at h₁
  exact h₁.trans h₂


theorem exists_finiteFullPreparedMetric_volume_debit_threshold (A : ℝ) (hA : 0 < A) :
    ∃ δV : ℝ, 0 < δV ∧ δV < 1 / 2 ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
        [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [CompactSpace M]
        {ι : Type*} [Finite ι] {precision : ι → ℝ}
        (hδ : ∀ i, 0 < precision i) (f : ∀ i, bufferedCylinder (precision i) → M)
        (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
        (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
        (hs : ∀ i, IsLocalDiffeomorph CurvGIC I ∞ (f i))
        (U : Opens M) (g : SmoothRiemannianMetric I U)
        (R : Set (ConnectedComponents (cutCore f)))
        (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → U) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
        (k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ)
        (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          normalizedDatum g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
            (c * precision b.val.1) (k' b))
        (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          (d b).retainedSide = true)
        (D : ℝ) (m : ℕ) (ε : ℝ)
        (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          CanonicalStaticInsertionWitness (d b) A hA D m ε),
      ((∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, c * precision b.val.1 ≤ δV) →
      (∀ i, precision i ≤ 1 / 4) →
      (∀ i, cuttingSphereComponent hδ f hf hdisj (i, true) ∈ R ∧
        cuttingSphereComponent hδ f hf hdisj (i, false) ∉ R) →
      ∀ (Q : ℝ), 0 < Q → (∀ i, metricScalarAt g (x₀ i) = Q) →
      (∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, Q / 2 ≤ metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) →
      ∀ η : ℝ≥0∞,
      (∀ i, ENNReal.ofReal (8 * Q ^ (-3 / 2 : ℝ)) *
          riemannianVolumeMeasure (𝓡 3) CurvGE3 metric {x | ‖x‖ ≤ transitionEnd} + η ≤
        ENNReal.ofReal (2 * Real.pi / precision i) * ENNReal.ofReal (Q ^ (-3 / 2 : ℝ))) →
    let : SecondCountableTopology H := I.secondCountableTopology
    let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let : CompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
    let : CompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) :=
      (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    riemannianVolumeMeasure (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) gRet univ + (Nat.card ι : ℝ≥0∞) * η ≤
      riemannianVolumeMeasure I U g
        (range (retainedCoreDomainMap f R U hRet) ∪
          ⋃ i : ι, (d₀ i).map '' {q | q.val.2 ∈ Icc (-(precision i)⁻¹) (-1 : ℝ)})) := by
  obtain ⟨δV, hδV, hhalf, hfactory⟩ := exists_canonicalStaticInsertionWitness_cap_volume_bound_of_scalar_lower A hA
  refine ⟨δV, hδV, hhalf, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ _ ι _ precision hδ f hf hdisj hs U g R hRet c hc
    x₀ order d₀ hOriginal k' hrec d hmap hside D m ε w
    hsmall hquarter hone Q hQ hscale hlocal η hmargin
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : CompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) :=
    (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
  dsimp only
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} := Fintype.ofFinite {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
  let e : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} ≃ ι := retainedIndexEquiv
    (fun b : ι × Bool => cuttingSphereComponent hδ f hf hdisj b ∈ R) hone
  let capConst := ENNReal.ofReal (8 * Q ^ (-3 / 2 : ℝ)) *
    riemannianVolumeMeasure (𝓡 3) CurvGE3 metric {x | ‖x‖ ≤ transitionEnd}
  have hcaps : (∑' b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, riemannianVolumeMeasure (𝓡 3)
      (InsertionQuotient (inv_pos.mpr (d b).precision_pos))
      (w b).data.outMetric (range (w b).data.capMap)) ≤ ∑' i : ι, capConst := by
    calc
      _ ≤ ∑' b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, capConst := by
        apply ENNReal.tsum_le_tsum
        intro b
        exact hfactory (c * precision b.val.1) (d b).precision_pos (hsmall b) (k' b)
          g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (d b) D m ε (w b) Q hQ (hlocal b)
      _ = _ := e.tsum_eq (fun _ => capConst)
  have houtput := finiteFullPreparedMetric_volume_le I hδ f hf hdisj hs U g R hRet c hc
    x₀ order d₀ hOriginal hrec d hmap hside w
  have hbase := houtput.trans (add_le_add_right hcaps _)
  have hsource := retained_core_add_negative_bands_volume_le U g x₀ order d₀ f hf hdisj hOriginal R hRet
    hquarter (fun i => (hone i).2)
  simp_rw [hscale] at hsource
  have hm : (∑' i : ι, capConst) + (Nat.card ι : ℝ≥0∞) * η ≤
      ∑' i : ι, ENNReal.ofReal (2 * Real.pi / precision i) * ENNReal.ofReal (Q ^ (-3 / 2 : ℝ)) := by
    rw [Nat.card_eq_fintype_card]
    have he : (Fintype.card ι : ℝ≥0∞) * η = ∑' _ : ι, η := by
      simp [tsum_fintype, nsmul_eq_mul]
    rw [he, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum hmargin
  apply (add_le_add_left hbase _).trans
  rw [add_assoc]
  exact (add_le_add_right hm _).trans hsource


theorem exists_finiteFullPreparedMetric_volume_debit (A : ℝ) (hA : 0 < A) :
    ∃ δV : ℝ, 0 < δV ∧ δV < 1 / 2 ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
        [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [CompactSpace M]
        {ι : Type*} [Finite ι] {precision : ι → ℝ}
        (hδ : ∀ i, 0 < precision i) (f : ∀ i, bufferedCylinder (precision i) → M)
        (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
        (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
        (hs : ∀ i, IsLocalDiffeomorph CurvGIC I ∞ (f i))
        (U : Opens M) (g : SmoothRiemannianMetric I U)
        (R : Set (ConnectedComponents (cutCore f)))
        (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → U) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
        (k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ)
        (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          normalizedDatum g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
            (c * precision b.val.1) (k' b))
        (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          (d b).retainedSide = true)
        (D : ℝ) (m : ℕ) (ε : ℝ)
        (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          CanonicalStaticInsertionWitness (d b) A hA D m ε),
      ((∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, c * precision b.val.1 ≤ δV) →
      (∀ i, precision i ≤ 1 / 4) →
      (∀ i, cuttingSphereComponent hδ f hf hdisj (i, true) ∈ R ∧
        cuttingSphereComponent hδ f hf hdisj (i, false) ∉ R) →
      ∀ (Q : ℝ), 0 < Q → (∀ i, metricScalarAt g (x₀ i) = Q) →
      (∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, Q / 2 ≤ metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) →
      (∀ i, precision i ≤ Real.pi /
        (8 * (riemannianVolumeMeasure (𝓡 3) CurvGE3 metric {x | ‖x‖ ≤ transitionEnd}).toReal + 1)) →
    let : SecondCountableTopology H := I.secondCountableTopology
    let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let : CompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
    let : CompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) :=
      (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    riemannianVolumeMeasure (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) gRet univ + (Nat.card ι : ℝ≥0∞) * ENNReal.ofReal (Q ^ (-3 / 2 : ℝ)) ≤
      riemannianVolumeMeasure I U g
        (range (retainedCoreDomainMap f R U hRet) ∪
          ⋃ i : ι, (d₀ i).map '' {q | q.val.2 ∈ Icc (-(precision i)⁻¹) (-1 : ℝ)})) := by
  obtain ⟨δV, hδV, hhalf, hfactory⟩ := exists_finiteFullPreparedMetric_volume_debit_threshold A hA
  refine ⟨δV, hδV, hhalf, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ _ ι _ precision hδ f hf hdisj hs U g R hRet c hc
    x₀ order d₀ hOriginal k' hrec d hmap hside D m ε w
    hsmall hquarter hone Q hQ hscale hlocal hprecision
  exact hfactory I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside D m ε w
    hsmall hquarter hone Q hQ hscale hlocal (ENNReal.ofReal (Q ^ (-3 / 2 : ℝ)))
    (fun i => cap_volume_margin_of_precision_le (precision i) Q (hδ i) hQ (hprecision i))

end DifferentialGeometry.PDE.RicciFlow.StandardCap
