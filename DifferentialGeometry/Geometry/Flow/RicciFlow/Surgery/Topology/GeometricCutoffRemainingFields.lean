import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffGeometryReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.EndNeckFields
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem neckBuffer_le_of_le {δ δ' : ℝ} (hδ : 0 < δ) (h : δ ≤ δ') :
    neckBuffer δ' ≤ neckBuffer δ := by
  intro x hx
  have hinv : δ'⁻¹ ≤ δ⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hδ h
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem isSmoothEmbedding_opens_inclusion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {V U : TopologicalSpace.Opens M} (hVU : V ≤ U) :
    IsSmoothEmbedding I I ∞ (TopologicalSpace.Opens.inclusion hVU) := by
  refine DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen I I U
    (TopologicalSpace.Opens.inclusion hVU) ?_
  exact IsSmoothEmbedding.of_opens (I := I) V

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem metricDerivNormSupOn_restrictOpenOfSubset {U V : TopologicalSpace.Opens M}
    (hVU : V ≤ U) [SigmaCompactSpace U] [T2Space U] [T2Space V]
    (gk gInf gRef : SmoothRiemannianMetric I U) (K : Set V) (p : ℕ) :
    metricDerivNormSupOn K p (gk.restrictOpenOfSubset hVU)
        (gInf.restrictOpenOfSubset hVU) (gRef.restrictOpenOfSubset hVU) =
      metricDerivNormSupOn (TopologicalSpace.Opens.inclusion hVU '' K) p gk gInf gRef := by
  unfold metricDerivNormSupOn
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨a, ha, x, hxK, hr⟩
    exact ⟨a, ha, TopologicalSpace.Opens.inclusion hVU x, ⟨x, hxK, rfl⟩,
      (metricDerivNorm_flat hVU gk gInf gRef a x) ▸ hr⟩
  · rintro ⟨a, ha, y, ⟨x, hxK, rfl⟩, hr⟩
    exact ⟨a, ha, x, hxK,
      (metricDerivNorm_flat hVU gk gInf gRef a x).trans hr⟩

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

def NormalizedNeck.monoDelta {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric ThreeModel M} {δ δ' : ℝ} {k : ℕ}
    (N : NormalizedNeck g δ k) (h : δ ≤ δ') (h' : δ' < 1) :
    NormalizedNeck g δ' k := by
  have hle : neckBuffer δ' ≤ neckBuffer δ := neckBuffer_le_of_le N.delta_pos h
  have hincl : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞
      (TopologicalSpace.Opens.inclusion hle) := isSmoothEmbedding_opens_inclusion hle
  have hchart : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞
      (fun x : neckBuffer δ' => N.chart (TopologicalSpace.Opens.inclusion hle x)) :=
    IsSmoothEmbedding.comp N.chart_smooth hincl (by decide)
  have hcont : Continuous
      (fun x : neckBuffer δ' => N.chart (TopologicalSpace.Opens.inclusion hle x)) :=
    N.chart.continuous.comp (contMDiff_inclusion (I := NeckCylinderModel) (n := ∞) hle).continuous
  have hsub : TopologicalSpace.Opens.inclusion hle '' neckClosedTest δ' ⊆ neckClosedTest δ := by
    rintro y ⟨x, hx, rfl⟩
    have hinv : δ'⁻¹ ≤ δ⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le N.delta_pos h
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  refine
    { delta_pos := lt_of_lt_of_le N.delta_pos h
      delta_lt_one := h'
      sphereMark := N.sphereMark
      center := N.center
      chart := ⟨fun x : neckBuffer δ' =>
        N.chart (TopologicalSpace.Opens.inclusion hle x), hcont⟩
      chart_smooth := hchart
      marked := ?_
      scale := N.scale
      scale_pos := N.scale_pos
      scale_scalar := N.scale_scalar
      normalizedMetric := N.normalizedMetric.restrictOpenOfSubset hle
      normalized_inner := ?_
      closeness := ?_ }
  · have hmem' : (N.sphereMark, (0 : ℝ)) ∈ neckBuffer δ' := by
      have h1 : 1 < δ'⁻¹ := (one_lt_inv₀ (lt_of_lt_of_le N.delta_pos h)).mpr h'
      change -δ'⁻¹ - 1 < (0 : ℝ) ∧ (0 : ℝ) < δ'⁻¹ + 1
      constructor <;> linarith
    change N.chart (TopologicalSpace.Opens.inclusion hle ⟨(N.sphereMark, 0), hmem'⟩) = N.center
    convert N.marked using 2
  · intro x V W
    change (N.normalizedMetric.restrictOpenOfSubset hle).inner x V W =
      N.scale * (g.inner (N.chart (TopologicalSpace.Opens.inclusion hle x))
        (mfderiv NeckCylinderModel ThreeModel
          ((N.chart : neckBuffer δ → M) ∘ TopologicalSpace.Opens.inclusion hle) x V)
        (mfderiv NeckCylinderModel ThreeModel
          ((N.chart : neckBuffer δ → M) ∘ TopologicalSpace.Opens.inclusion hle) x W))
    rw [SmoothRiemannianMetric.restrictSubset_inner]
    rw [N.normalized_inner (TopologicalSpace.Opens.inclusion hle x) V W]
    have hmd : MDifferentiableAt NeckCylinderModel ThreeModel
        (N.chart : neckBuffer δ → M) (TopologicalSpace.Opens.inclusion hle x) :=
      N.chart_smooth.contMDiff.mdifferentiableAt (by simp)
    have hmd' : MDifferentiableAt NeckCylinderModel NeckCylinderModel
        (TopologicalSpace.Opens.inclusion hle) x :=
      (contMDiff_inclusion (I := NeckCylinderModel) (n := ∞) hle).contMDiffAt.mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    rw [mfderiv_comp_apply x (f := TopologicalSpace.Opens.inclusion hle)
        (g := (N.chart : neckBuffer δ → M)) hmd hmd' V,
      mfderiv_comp_apply x (f := TopologicalSpace.Opens.inclusion hle)
        (g := (N.chart : neckBuffer δ → M)) hmd hmd' W]
    rw [mfderiv_opens_incl (I := NeckCylinderModel) hle x]
    rfl
  · have hsc : SigmaCompactSpace ↥(neckBuffer δ) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer δ).isOpen)
    rw [← SmoothRiemannianMetric.restrictOpen_flat roundCylinderMetric hle]
    rw [CheegerGromovCompactness.metricDerivNormSupOn_restrictOpenOfSubset hle N.normalizedMetric
      (roundCylinderMetric.restrictOpen (neckBuffer δ))
      (roundCylinderMetric.restrictOpen (neckBuffer δ)) (neckClosedTest δ') k]
    refine lt_of_le_of_lt ?_ (lt_of_lt_of_le N.closeness h)
    refine CheegerGromovCompactness.metricDerivNormSupOn_le_of_forall
      (TopologicalSpace.Opens.inclusion hle '' neckClosedTest δ') k
      N.normalizedMetric (roundCylinderMetric.restrictOpen (neckBuffer δ))
      (roundCylinderMetric.restrictOpen (neckBuffer δ))
      (CheegerGromovCompactness.metricDerivNormSupOn (neckClosedTest δ) k N.normalizedMetric
        (roundCylinderMetric.restrictOpen (neckBuffer δ))
        (roundCylinderMetric.restrictOpen (neckBuffer δ)))
      (metricDerivNormSupOn_nonneg _ _ _ _ _) ?_
    intro a ha x hx
    exact CheegerGromovCompactness.derivNorm_le_sup (isCompact_neckClosedTest δ) ha _ _ _
      (hsub hx)


theorem NormalizedNeck.nonempty_monoDelta {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric ThreeModel M} {δ δ' : ℝ} {k : ℕ}
    (h : δ ≤ δ') (h' : δ' < 1) (hn : Nonempty (NormalizedNeck g δ k)) :
    Nonempty (NormalizedNeck g δ' k) :=
  hn.map fun N => N.monoDelta h h'

theorem exists_normalizedNeck_iff_of_le {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {L : ℕ} :
    (∃ k : ℕ, L ≤ k ∧ Nonempty (NormalizedNeck g δ k)) ↔
      Nonempty (NormalizedNeck g δ L) := by
  constructor
  · rintro ⟨k, hLk, ⟨N⟩⟩
    exact ⟨N.lowerOrder hLk⟩
  · intro h
    exact ⟨L, le_rfl, h⟩

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

theorem nominal_time_of_incomingBackwardNeck
    {nominalRadius : Nonempty (H.event i).transition.trace.tubes.Index → ℝ}
    {delta : (H.event i).transition.trace.tubes.Index → ℝ}
    {order : (H.event i).transition.trace.tubes.Index → ℕ}
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (delta α) (order α))
    (backward : ∀ α, IncomingBackwardNeck H i (neck α) (nominalRadius ⟨α⟩)) :
    ∀ h, (nominalRadius h) ^ 2 ≤ H.time i.succ := by
  intro h
  cases h with
  | intro α =>
    have hle := (backward α).left_nonneg
    linarith

theorem exists_pos_mul_sq_gt {r δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ r < δ ^ 2 * ρ := by
  refine ⟨max (r / δ ^ 2) 0 + 1, by positivity, ?_⟩
  have hmax : r / δ ^ 2 ≤ max (r / δ ^ 2) 0 := le_max_left _ _
  have hsq : (0 : ℝ) < δ ^ 2 := pow_pos hδ 2
  have hne : δ ^ 2 ≠ 0 := ne_of_gt hsq
  calc r = δ ^ 2 * (r / δ ^ 2) := (mul_div_cancel₀ r hne).symm
    _ ≤ δ ^ 2 * max (r / δ ^ 2) 0 := mul_le_mul_of_nonneg_left hmax hsq.le
    _ < δ ^ 2 * (max (r / δ ^ 2) 0 + 1) := by nlinarith

theorem exists_neckRadius_nominalSmall (q : CutoffParameters) (htime : 0 ≤ H.time i.succ)
    (s : (H.event i).transition.trace.tubes.Index → ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ h : Nonempty (H.event i).transition.trace.tubes.Index,
      canonicalNominalRadius s h < (q.delta (H.time i.succ)) ^ 2 * ρ := by
  by_cases hne : Nonempty (H.event i).transition.trace.tubes.Index
  · obtain ⟨ρ, hρ, hlt⟩ := exists_pos_mul_sq_gt (r := canonicalNominalRadius s hne)
      (δ := q.delta (H.time i.succ)) (q.delta_pos _ htime)
    exact ⟨ρ, hρ, fun h => by rw [Subsingleton.elim h hne]; exact hlt⟩
  · exact ⟨1, one_pos, fun h => absurd h hne⟩

def CutoffParameters.withNeckRadius (q : CutoffParameters) (ρ : ℝ → ℝ)
    (hρ : ∀ t, 0 ≤ t → 0 < ρ t) : CutoffParameters where
  delta := q.delta
  neckRadius := ρ
  protectedRadius := q.protectedRadius
  delta_pos := q.delta_pos
  delta_lt_one := q.delta_lt_one
  neckRadius_pos := hρ
  protectedRadius_pos := q.protectedRadius_pos
  fixed := q.fixed
  modelRadius := q.modelRadius
  modelRadius_pos := q.modelRadius_pos
  modelOrder := q.modelOrder
  modelAccuracy := q.modelAccuracy
  modelAccuracy_pos := q.modelAccuracy_pos
  recenterConstant := q.recenterConstant
  recenterConstant_ge_four := q.recenterConstant_ge_four

theorem HasRecenterConstants.withNeckRadius {q : CutoffParameters}
    (h : HasRecenterConstants.{u} q) {ρ : ℝ → ℝ} (hρ : ∀ t, 0 ≤ t → 0 < ρ t) :
    HasRecenterConstants.{u} (q.withNeckRadius ρ hρ) := by
  obtain ⟨c, δ₀, hc, hδ₀, hconst, huniv, hsmall⟩ := h
  exact ⟨c, δ₀, hc, hδ₀, hconst, huniv, hsmall⟩

theorem exists_cutoffParameters_nominal_small (q : CutoffParameters) (htime : 0 ≤ H.time i.succ)
    (s : (H.event i).transition.trace.tubes.Index → ℝ) :
    ∃ q' : CutoffParameters,
      q'.delta = q.delta ∧ q'.protectedRadius = q.protectedRadius ∧ q'.fixed = q.fixed ∧
      q'.modelRadius = q.modelRadius ∧ q'.modelOrder = q.modelOrder ∧
      q'.modelAccuracy = q.modelAccuracy ∧ q'.recenterConstant = q.recenterConstant ∧
      (HasRecenterConstants.{u} q → HasRecenterConstants.{u} q') ∧
      ∀ h, canonicalNominalRadius s h <
        (q'.delta (H.time i.succ)) ^ 2 * q'.neckRadius (H.time i.succ) := by
  obtain ⟨ρ, hρ, hlt⟩ := exists_neckRadius_nominalSmall (H := H) (i := i) q htime s
  exact ⟨q.withNeckRadius (fun _ => ρ) (fun _ _ => hρ), rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun hq => hq.withNeckRadius _, hlt⟩

theorem singularEndpoint_iff_not_bounded {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) :
    G.SingularEndpoint ↔ ∀ d ∈ Ico a s, ¬ ∃ K : ℝ,
      ∀ t ∈ Ioo d s, ∀ x : P.Carrier, G.riemannNorm t x ≤ K := by
  constructor
  · intro h d hd hb
    obtain ⟨K, hK⟩ := hb
    obtain ⟨t, ht, x, hx⟩ := h (max K 0 + 1) (by positivity) d hd
    have hle := hK t ht x
    have hmax := le_max_left K (0 : ℝ)
    linarith
  · intro h L hL d hd
    by_contra hc
    have hb : ∀ t ∈ Ioo d s, ∀ x : P.Carrier, G.riemannNorm t x ≤ L := by
      intro t ht x
      by_contra hlt
      exact hc ⟨t, ht, x, lt_of_not_ge hlt⟩
    exact h d hd ⟨L, hb⟩

theorem protected_interior_mono_protectedRadius {ρ₁ ρ₂ : ℝ} (h₁ : 0 < ρ₁)
    (h : ρ₁ ≤ ρ₂) :
    (∀ x : (H.event i).incoming.terminalRegularOpen,
      metricScalarAt (H.event i).terminal.metric x ≤ ((ρ₁) ^ 2)⁻¹ →
      x.1 ∈ interior (Subtype.val '' (H.event i).transition.trace.retainedCore)) →
    (∀ x : (H.event i).incoming.terminalRegularOpen,
      metricScalarAt (H.event i).terminal.metric x ≤ ((ρ₂) ^ 2)⁻¹ →
      x.1 ∈ interior (Subtype.val '' (H.event i).transition.trace.retainedCore)) := by
  intro hf x hx
  refine hf x ?_
  have hsq : ρ₁ ^ 2 ≤ ρ₂ ^ 2 := by nlinarith
  have hinv : ((ρ₂) ^ 2)⁻¹ ≤ ((ρ₁) ^ 2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos h₁ 2) hsq
  linarith

theorem retained_meets_protected_anti_protectedRadius {ρ₁ ρ₂ : ℝ} (h₁ : 0 < ρ₁)
    (h : ρ₁ ≤ ρ₂) :
    (∀ c : ConnectedComponents (H.event i).transition.trace.tubes.core,
      (∃ x : (H.event i).transition.trace.tubes.core,
        ConnectedComponents.mk x = c ∧ x ∈ (H.event i).transition.trace.retainedCore) →
      ∃ x : (H.event i).incoming.terminalRegularOpen,
        ∃ hx : x.1 ∈ (H.event i).transition.trace.tubes.core,
          ConnectedComponents.mk ⟨x.1, hx⟩ = c ∧
            metricScalarAt (H.event i).terminal.metric x ≤ ((ρ₂) ^ 2)⁻¹) →
    (∀ c : ConnectedComponents (H.event i).transition.trace.tubes.core,
      (∃ x : (H.event i).transition.trace.tubes.core,
        ConnectedComponents.mk x = c ∧ x ∈ (H.event i).transition.trace.retainedCore) →
      ∃ x : (H.event i).incoming.terminalRegularOpen,
        ∃ hx : x.1 ∈ (H.event i).transition.trace.tubes.core,
          ConnectedComponents.mk ⟨x.1, hx⟩ = c ∧
            metricScalarAt (H.event i).terminal.metric x ≤ ((ρ₁) ^ 2)⁻¹) := by
  intro hf c hc
  obtain ⟨x, hx, hmk, hsc⟩ := hf c hc
  have hsq : ρ₁ ^ 2 ≤ ρ₂ ^ 2 := by nlinarith
  have hinv : ((ρ₂) ^ 2)⁻¹ ≤ ((ρ₁) ^ 2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos h₁ 2) hsq
  exact ⟨x, hx, hmk, hsc.trans hinv⟩


theorem sumEmpty_symm_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [IsEmpty Y]
    (x : X) : (Homeomorph.sumEmpty X Y).symm x = Sum.inl x := rfl

def twoBallRetainedCutCap :
    CutCapTopology TubeDomain (ThreeBall ⊕ ThreeBall) PEmpty (ThreeBall ⊕ ThreeBall) where
  tubes := cylinderTubeSystem
  capping := twoBallCapping
  presentation := (Homeomorph.sumEmpty (ThreeBall ⊕ ThreeBall) PEmpty).symm
  nontrivial := Or.inl ⟨PUnit.unit⟩

theorem twoBallRetainedCutCap_retainedCore_eq_univ :
    twoBallRetainedCutCap.retainedCore = Set.univ := by
  ext x
  exact ⟨fun _ => Set.mem_univ x,
    fun _ => ⟨twoBallRetainedCutCap.capping.coreInclusion x, rfl⟩⟩

theorem twoBallRetainedCutCap_retainedBoundary_true (z : Sphere 2) :
    twoBallRetainedCutCap.tubes.coreBoundarySphere (PUnit.unit, true) z ∈
      twoBallRetainedCutCap.retainedCore := by
  rw [twoBallRetainedCutCap_retainedCore_eq_univ]
  exact Set.mem_univ _

theorem twoBallRetainedCutCap_retainedBoundary_false (z : Sphere 2) :
    twoBallRetainedCutCap.tubes.coreBoundarySphere (PUnit.unit, false) z ∈
      twoBallRetainedCutCap.retainedCore := by
  rw [twoBallRetainedCutCap_retainedCore_eq_univ]
  exact Set.mem_univ _

theorem twoBallCutCap_retainedBoundary_true (z : Sphere 2) :
    twoBallCutCap.tubes.coreBoundarySphere (PUnit.unit, true) z ∉ twoBallCutCap.retainedCore :=
  twoBallCutCap.capDiscarded_coreBoundarySphere_not_mem_retainedCore (PUnit.unit, true)
    twoBallCutCap_capDiscarded z

theorem twoBallCutCap_retainedBoundary_false (z : Sphere 2) :
    twoBallCutCap.tubes.coreBoundarySphere (PUnit.unit, false) z ∈ twoBallCutCap.retainedCore :=
  twoBallCutCap.capRetained_coreBoundarySphere_mem_retainedCore (PUnit.unit, false)
    twoBallCutCap_capRetained z

theorem twoBallCutCap_one_retained_side :
    (∀ z : Sphere 2, twoBallCutCap.tubes.coreBoundarySphere (PUnit.unit, true) z ∈
        twoBallCutCap.retainedCore) ↔
      ¬ (∀ z : Sphere 2, twoBallCutCap.tubes.coreBoundarySphere (PUnit.unit, false) z ∈
        twoBallCutCap.retainedCore) :=
  ⟨fun h => absurd h (fun h' => twoBallCutCap_retainedBoundary_true sphereNorth (h' sphereNorth)),
    fun h => absurd (fun z => twoBallCutCap_retainedBoundary_false z) h⟩

theorem not_twoBallRetainedCutCap_one_retained_side :
    ¬ ((∀ z : Sphere 2, twoBallRetainedCutCap.tubes.coreBoundarySphere (PUnit.unit, true) z ∈
          twoBallRetainedCutCap.retainedCore) ↔
        ¬ (∀ z : Sphere 2,
          twoBallRetainedCutCap.tubes.coreBoundarySphere (PUnit.unit, false) z ∈
            twoBallRetainedCutCap.retainedCore)) :=
  fun h => (h.mp twoBallRetainedCutCap_retainedBoundary_true)
    twoBallRetainedCutCap_retainedBoundary_false


structure GeometricCutoffScaleFrontier (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (parameters : CutoffParameters) where
  neck : (H.event i).transition.trace.tubes.Index →
    NormalizedNeck (H.event i).terminal.metric (parameters.delta (H.time i.succ))
      (max (parameters.modelOrder + 6)
        (2 * ⌊(parameters.delta (H.time i.succ))⁻¹⌋₊ + 4))
  scale_const : ∀ α β, (neck α).scale = (neck β).scale
  nominal_small : ∀ h, canonicalNominalRadius (fun α => (neck α).scale) h <
    (parameters.delta (H.time i.succ)) ^ 2 * parameters.neckRadius (H.time i.succ)
  backward : ∀ α, IncomingBackwardNeck H i (neck α)
    (canonicalNominalRadius (fun α => (neck α).scale) ⟨α⟩)
  singular : (H.event i).incoming.SingularEndpoint
  buffer_disjoint : Pairwise fun α β =>
    Disjoint (Set.range (neck α).chart) (Set.range (neck β).chart)
  tube_eq : ∀ α, ∀ x : TubeDomain,
    ∀ hx : (x.1, x.2.1) ∈ neckBuffer (parameters.delta (H.time i.succ)),
    (H.event i).transition.trace.tubes.tube α x = ((neck α).chart ⟨(x.1, x.2.1), hx⟩).1
  protected_interior : ∀ x : (H.event i).incoming.terminalRegularOpen,
    metricScalarAt (H.event i).terminal.metric x ≤
      ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
    x.1 ∈ interior (Subtype.val '' (H.event i).transition.trace.retainedCore)
  retained_meets_protected : ∀ c : ConnectedComponents (H.event i).transition.trace.tubes.core,
    (∃ x : (H.event i).transition.trace.tubes.core,
      ConnectedComponents.mk x = c ∧ x ∈ (H.event i).transition.trace.retainedCore) →
    ∃ x : (H.event i).incoming.terminalRegularOpen,
      ∃ hx : x.1 ∈ (H.event i).transition.trace.tubes.core,
        ConnectedComponents.mk ⟨x.1, hx⟩ = c ∧
          metricScalarAt (H.event i).terminal.metric x ≤
            ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹
  one_retained_side : ∀ α,
    (H.event i).RetainedBoundary (α, true) ↔ ¬ (H.event i).RetainedBoundary (α, false)
  old_tube_band : ∀ x ∈ (H.event i).transition.trace.retainedCore,
    MetricCutCapEvent.TubeBandHit (H.event i) x → x ∈ (H.event i).old
  curvature_preserving : ∀ a : ℝ, 0 < a →
    (∀ x : (H.event i).incoming.terminalRegularOpen,
      InFixedHamiltonIveyRegion (H.event i).terminal.metric a x) →
    ∀ x : (H.stage i.succ).Carrier, InFixedHamiltonIveyRegion (H.event i).outputMetric a x
  scalar_preserving : ∀ L : ℝ, L ≤ 0 →
    (∀ x : (H.event i).incoming.terminalRegularOpen,
      L ≤ metricScalarAt (H.event i).terminal.metric x) →
    ∀ x : (H.stage i.succ).Carrier, L ≤ metricScalarAt (H.event i).outputMetric x
  recenter : HasRecenterConstants.{u} parameters
  staticFrontier : ∀ b : (H.event i).RetainedBoundaryIndex,
    PresentedStaticCapFrontier H i parameters.fixed parameters.modelRadius parameters.modelOrder
      parameters.modelAccuracy
      (recenterNeck (H := H) (i := i) (parameters := parameters) recenter neck
        (fun _ => le_rfl) (fun _ => le_rfl) b) b


namespace GeometricCutoffScaleFrontier

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

def toGeometryFrontier (F : GeometricCutoffScaleFrontier H i parameters) :
    GeometricCutoffGeometryFrontier H i parameters where
  delta := fun _ => parameters.delta (H.time i.succ)
  delta_le := fun _ => le_rfl
  order := fun _ => max (parameters.modelOrder + 6)
    (2 * ⌊(parameters.delta (H.time i.succ))⁻¹⌋₊ + 4)
  order_lower := fun _ => le_rfl
  neck := F.neck
  scale_const := F.scale_const
  nominal_small := F.nominal_small
  nominal_time := nominal_time_of_incomingBackwardNeck F.neck F.backward
  backward := F.backward
  singular := F.singular
  buffer_disjoint := F.buffer_disjoint
  tube_eq := F.tube_eq
  protected_interior := F.protected_interior
  retained_meets_protected := F.retained_meets_protected
  one_retained_side := F.one_retained_side
  old_tube_band := F.old_tube_band
  curvature_preserving := F.curvature_preserving
  scalar_preserving := F.scalar_preserving
  recenter := F.recenter
  staticFrontier := F.staticFrontier

def toFrontier (F : GeometricCutoffScaleFrontier H i parameters) :
    GeometricCutoffFrontier H i parameters :=
  F.toGeometryFrontier.toFrontier

theorem nonempty_geometricCutoffGeometryFrontier
    (h : Nonempty (GeometricCutoffScaleFrontier H i parameters)) :
    Nonempty (GeometricCutoffGeometryFrontier H i parameters) :=
  h.map toGeometryFrontier

theorem nonempty_geometricCutoffRecord
    (h : Nonempty (GeometricCutoffScaleFrontier H i parameters)) :
    Nonempty (GeometricCutoffRecord H i parameters) :=
  h.map fun F => GeometricCutoffRecord.ofFrontier F.toFrontier

end GeometricCutoffScaleFrontier

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
