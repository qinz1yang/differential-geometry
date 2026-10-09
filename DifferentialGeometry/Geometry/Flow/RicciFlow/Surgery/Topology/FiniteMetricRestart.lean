import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricJetBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteMetricCutCapJetBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledRestart

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
  DifferentialGeometry.Topology.ThreeManifold.Surgery
  DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.StandardCap DifferentialGeometry.Manifold
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

theorem MetricCutCapEvent.exists_controlled_restart_of_finiteFullPreparedMetric
    {C : ℕ → ℝ} (hw : ∀ b : Boundary, StaticInsertionAdditionalProperties C (w b))
    (hC : ∀ j ≤ m, 0 ≤ C j)
    (hratio : ∀ b : Boundary,
      |metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
        metricScalarAt g (x₀ b.val.1) - 1| ≤ c * precision b.val.1)
    (K : ℕ → ℝ) (Qmax : ℝ) (hQmax : 0 ≤ Qmax)
    (hin : ∀ p : retainedCore f R, ∀ j ≤ m,
      Real.sqrt (normSq0S g (retainedCoreDomainMap f R U hRet p) (4 + j)
        (iterCov g 4 (metricRm04 g) j (retainedCoreDomainMap f R U hRet p))) ≤ K j)
    (hscale : ∀ b : Boundary, metricScalarAt g (x₀ b.val.1) ≤ Qmax) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace E3 Q :=
      finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q :=
      finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    ∀ [CompactSpace Ret] (oRet : SmoothOrientation (𝓡 3) Ret)
      {P : OrientedThreeStage} {a s : ℝ}
      (event : MetricCutCapEvent P
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) a s),
      event.outputMetric = finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc
        x₀ order d₀ hOriginal hrec d hmap hside w →
      ∃ G : (OrientedThreeStage.ofSmoothOrientation Ret oRet).ClosedSlab s (s + compactCurvatureControlTime 3 (max (K 0) (2 * C 0 * Qmax))),
        G.flow.base.metric s = event.outputMetric ∧
        ∀ t ∈ Set.Icc s (s + compactCurvatureControlTime 3 (max (K 0) (2 * C 0 * Qmax))), ∀ q : Ret,
          Real.sqrt (normSq0S (G.flow.base.metric t) q 4 (metricRm04 (G.flow.base.metric t) q)) ≤
            Real.sqrt (2 * (max (K 0) (2 * C 0 * Qmax)) ^ 2 + 1) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace E3 Q :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro hcompact oRet P a s event hout
  apply MetricCutCapEvent.exists_closedSlab_restart_of_curvature_bound event (max (K 0) (2 * C 0 * Qmax))
  intro q
  have h := MetricCutCapEvent.curvature_jets_le_of_finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet
    c hc x₀ order d₀ hOriginal hrec d hmap hside w hw hC hratio K Qmax hQmax hin hscale oRet event hout q 0 (Nat.zero_le m)
  simpa only [Nat.add_zero, Nat.cast_zero, zero_div, add_zero, Real.rpow_one,
    iterCov, Nat.rec_zero, mul_left_comm (C 0) 2 Qmax, mul_assoc] using h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.StandardCap

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] threeBallChartedSpace threeBall_isManifold
private instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

theorem exists_uniform_metricCutCapEvent_controlled_restart :
    ∃ (c : ℝ) (hc : 4 ≤ c), ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧
      ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [CompactSpace M],
      ∀ (o : SmoothOrientation ThreeModel M) {t₀ t₁ : ℝ}
        (G : (OrientedThreeStage.ofSmoothOrientation M o).IncomingSlab t₀ t₁)
        (L : G.TerminalLimitMetric)
        {ι : Type} [Fintype ι] (precision : ι → ℝ) (hδ : ∀ i, 0 < precision i),
      (∀ i, precision i ≤ δ₀) → ∀ (x₀ : ι → G.terminalRegularOpen)
        (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (m + 6))
        (f : ∀ i : ι, bufferedCylinder (precision i) → M)
        (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
        (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
        (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
        (hOriginal : ∀ i, f i = neckAmbientMap G.terminalRegularOpen (d₀ i))
        (R : Set (ConnectedComponents (cutCore f)))
        (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          (fun x : M => G.terminalRegularRegion x))
        (_ : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ)),
      let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
      let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      letI : LocallyPathConnectedSpace M :=
        originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
      let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
      let Disc := finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
      letI : ChartedSpace ThreeSpace Q :=
        finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
      letI : IsManifold ThreeModel ∞ Q :=
        finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj hs
      letI : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
      letI : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
      letI : CompactSpace Ret :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
      letI : CompactSpace Disc :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).2
      ∃ hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹,
      ∃ d : ∀ b : Bidx, normalizedDatum L.metric
        ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (m + 4),
      ∃ hmap : ∀ b : Bidx, (d b).map =
        (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b),
      ∃ hside : ∀ b : Bidx, (d b).retainedSide = true,
      ∃ w : ∀ b : Bidx, CanonicalStaticInsertionWitness (d b) A hA D m ε,
        (∀ b : Bidx, |metricScalarAt L.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
          metricScalarAt L.metric (x₀ b.val.1) - 1| ≤ c * precision b.val.1) ∧
        (∀ b : Bidx, StaticInsertionAdditionalProperties C (w b)) ∧
      let gRet := finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
        G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6) d₀
        hOriginal hrec d hmap hside w
      ∃ (oRet : SmoothOrientation ThreeModel Ret),
      let QRet := OrientedThreeStage.ofSmoothOrientation Ret oRet
      ∃ E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        QRet t₀ t₁,
        E.incoming = G ∧ HEq E.terminal L ∧
        E.outputMetric = gRet ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
        (∀ a : ℝ, 0 < a →
          (∀ x : E.incoming.terminalRegularOpen, InFixedHamiltonIveyRegion E.terminal.metric a x) →
          ∀ x : Ret, InFixedHamiltonIveyRegion E.outputMetric a x) ∧
        (∀ L₀ : ℝ, L₀ ≤ 0 →
          (∀ x : E.incoming.terminalRegularOpen, L₀ ≤ metricScalarAt E.terminal.metric x) →
          ∀ x : Ret, L₀ ≤ metricScalarAt E.outputMetric x) ∧
        (∀ (K : ℕ → ℝ) (Qmax : ℝ), 0 ≤ Qmax →
          (∀ p : retainedCore f R, ∀ j ≤ m,
            Real.sqrt (normSq0S L.metric (retainedCoreDomainMap f R G.terminalRegularOpen hRet p) (4 + j)
              (iterCov L.metric 4 (metricRm04 L.metric) j (retainedCoreDomainMap f R G.terminalRegularOpen hRet p))) ≤ K j) →
          (∀ b : Bidx, metricScalarAt L.metric (x₀ b.val.1) ≤ Qmax) →
          ∃ S : QRet.ClosedSlab t₁
              (t₁ + compactCurvatureControlTime 3 (max (K 0) (2 * C 0 * Qmax))),
            S.flow.base.metric t₁ = gRet ∧
            ∀ t ∈ Icc t₁ (t₁ + compactCurvatureControlTime 3 (max (K 0) (2 * C 0 * Qmax))), ∀ x : Ret,
              Real.sqrt (normSq0S (S.flow.base.metric t) x 4 (metricRm04 (S.flow.base.metric t) x)) ≤
                Real.sqrt (2 * (max (K 0) (2 * C 0 * Qmax)) ^ 2 + 1)) := by
  obtain ⟨c, hc, C, hC, A, hA, hsmall, hfactory⟩ := exists_uniform_metricCutCapEvent_curvature_preserving.{u}
  refine ⟨c, hc, C, hC, A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δ₀, hδ₀, hquarter, hmake⟩ := hfactory D hD m ε hε
  refine ⟨δ₀, hδ₀, hquarter, ?_⟩
  intro M _ _ _ _ _ o t₀ t₁ G L ι _ precision hδ hle x₀ d₀ f hf hdisj hs hOriginal R hRet hnontrivial
  let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
  let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
  let Disc := finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
  let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).2
  dsimp only
  obtain ⟨hrec, d, hmap, hside, w, hratio, hw, oQ, oRet, oDisc, F, B, a, hboundary,
    hchoice, hB, event, hDisc, hCap, htrace, hG, hL, hout, hOld, hBoundary, hpin, hscalar⟩ :=
      hmake o G L precision hδ hle x₀ d₀ f hf hdisj hs hOriginal R hRet hnontrivial
  refine ⟨hrec, d, hmap, hside, w, hratio, hw, oRet,
    event, hG, hL, hout, hOld, hBoundary, hpin, hscalar, ?_⟩
  intro K Qmax hQmax hin hscale
  obtain ⟨S, hS, hbound⟩ := MetricCutCapEvent.exists_controlled_restart_of_finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
    G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6) d₀
    hOriginal hrec d hmap hside w hw (fun j _ => (hC j).le) hratio K Qmax hQmax hin hscale oRet event hout
  exact ⟨S, hS.trans hout, hbound⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
