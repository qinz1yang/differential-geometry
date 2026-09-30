import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowPersistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncoming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Basic

noncomputable section
open Set Function Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem exists_common_flow_of_normalized_incoming_window
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hG : ∀ t ∈ Ico (H.time last) s, G.flow.base.metric t = H.stageMetric last t)
    {D q : ℝ} (hq : 0 < q)
    (J : standardCapWindow D → (H.stage first).Carrier)
    (Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G)
    (hΞs : IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
    (hbirth : ∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = J y)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast : ∀ t ∈ Icc (H.time last) s,
      gflow t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (F : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
      (RealTimeInterval.closed 0 (q * (s - H.time first))
        (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity)))
    (hFmetric : ∀ t, F.base.metric t =
      localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) :
    ∃ f : (j : H.StageInterval first last) → standardCapWindow D → (H.stage j.val).Carrier,
      ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
        (∀ j, Function.Injective (f j)) ∧
        f ⟨first, le_rfl, hle⟩ = J ∧
        (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∀ y : standardCapWindow D,
            (H.event i).RegularCrossing
              (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ y)
              (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ y)) ∧
        ∃ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
            (RealTimeInterval.closed (H.time first) s
              ((H.time_strictMono.monotone hle).trans G.lt.le)),
          IsSolutionOn S ∧
          (∀ j : H.StageInterval first last, ∀ t ∈ H.stageDomain j.val,
            t < s → S.base.metric t = localPullMetric (H.stageMetric j.val t) (f j) (hf j)) ∧
          (∀ t ∈ Icc 0 (q * (s - H.time first)),
            scaleMetric q hq (S.base.metric (H.time first + t / q)) = F.base.metric t) ∧
          ∃ (Φ : standardCapWindow D → G.terminalRegularOpen)
            (hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ),
            Subtype.val ∘ Φ = f ⟨last, hle, le_rfl⟩ ∧
            Φ = H.backwardSurvivorIncomingMap first last hle G ∘ Ξ ∧
            S.base.metric s = localPullMetric L.metric Φ hΦ := by
  have hinit : G.flow.base.metric (H.time last) = H.initialMetric last :=
    (hG (H.time last) ⟨le_rfl, G.lt⟩).trans (H.stageMetric_initial last)
  obtain ⟨g₀, hslabs₀, hlast₀, _, hsol⟩ :=
    H.exists_backwardSurvivorIncoming_isSolutionOn first last hle G L hinit
  let S₀ : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingDomain first last hle G)
      (RealTimeInterval.closed (H.time first) s
        ((H.time_strictMono.monotone hle).trans G.lt.le)) := { base := { metric := g₀ } }
  have heq (t : ℝ) (ht : t ∈ Icc (H.time first) s) : g₀ t = gflow t :=
    H.backwardSurvivorIncomingMetric_eq_of_common_piecewise_flow first last hle G L g₀ gflow
      hslabs₀ hslabs hlast₀ hlast ht
  let f (j : H.StageInterval first last) : standardCapWindow D → (H.stage j.val).Carrier :=
    (H.backwardSurvivorMap first last hle j.val j.property.1 j.property.2 ∘ Subtype.val) ∘ Ξ
  have hf (j : H.StageInterval first last) :
      IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j) :=
    isLocalDiffeomorph_comp
      (isLocalDiffeomorph_comp
        (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j.val j.property.1 j.property.2)
        (isLocalDiffeomorph_subtype_val (H.backwardSurvivorIncomingDomain first last hle G))) hΞ
  refine ⟨f, hf, ?_, funext hbirth, ?_, ?_⟩
  · intro j
    exact (H.backwardSurvivorMap_injective first last hle j.val j.property.1 j.property.2).comp
      (Subtype.val_injective.comp hΞs.isEmbedding.injective)
  · intro i hi hl y
    exact H.backwardSurvivorMap_crossing first last hle i hi hl (Ξ y).val
  let : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first last hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  let S := S₀.localPullback Ξ hΞ
  refine ⟨S, hsol.localPullback Ξ hΞ, ?_, ?_, ?_⟩
  · intro j t ht hts
    change localPullMetric (g₀ t) Ξ hΞ = _
    rw [H.metric_eq_stage_pullback_of_backwardSurvivorIncoming first last hle s G L g₀
      (fun i hi hl t ht => hslabs₀ i hi hl t (Ico_subset_Icc_self ht))
      (fun t ht => hlast₀ t (Ico_subset_Icc_self ht)) hG
      j.val j.property.1 j.property.2 ht hts]
    exact localPullMetric_comp (H.stageMetric j.val t)
      (H.backwardSurvivorMap first last hle j.val j.property.1 j.property.2 ∘ Subtype.val) Ξ
      (isLocalDiffeomorph_comp
        (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j.val j.property.1 j.property.2)
        (isLocalDiffeomorph_subtype_val (H.backwardSurvivorIncomingDomain first last hle G))) hΞ (hf j)
  · intro t ht
    have hclock : H.time first + t / q ∈ Icc (H.time first) s := by
      refine ⟨le_add_of_nonneg_right (div_nonneg ht.1 hq.le), ?_⟩
      have hh : t / q ≤ s - H.time first :=
        (div_le_iff₀ hq).mpr (by nlinarith [ht.2])
      linarith
    change scaleMetric q hq (localPullMetric (g₀ _) Ξ hΞ) = _
    rw [← localPullMetric_scaleMetric, heq _ hclock, hFmetric]
  · let Φ := H.backwardSurvivorIncomingMap first last hle G ∘ Ξ
    have hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ :=
      isLocalDiffeomorph_comp (H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G) hΞ
    refine ⟨Φ, hΦ, ?_, rfl, ?_⟩
    · funext y
      exact (H.backwardSurvivorMap_last first last hle (Ξ y).val).symm
    · change localPullMetric (g₀ s) Ξ hΞ = _
      rw [hlast₀ s ⟨G.lt.le, le_rfl⟩, H.backwardSurvivorIncomingMetric_terminal]
      exact localPullMetric_comp L.metric (H.backwardSurvivorIncomingMap first last hle G) Ξ
        (H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G) hΞ hΦ


universe uE uH uM

theorem exists_uniform_prepared_cap_common_flow_of_backward_trace
    (Θ : ℝ) (C : ℝ≥0) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ P Creset Cbirth : ℝ, 0 < P ∧ 0 < Creset ∧ 0 < Cbirth ∧
      ∀ {E : Type uE} {H₀ : Type uH} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless],
      ∀ (D ε η : ℝ) (hD : 0 < D), 0 < ε → 0 < η → ∀ N : ℕ,
      ∃ R : ℝ, ∃ hDR : D + 1 < R, ∃ m₀ : ℕ, 4 ≤ m₀ ∧
      ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {M : Type uM} [TopologicalSpace M] [ChartedSpace H₀ M]
        [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A}
        {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ)
        (hR : R ≤ Dbig), m₀ ≤ m → ζ ≤ ζ₀ →
      let hDD : D ≤ Dbig := by linarith;
      let inc : standardCapWindow D → standardCapWindow Dbig :=
        TopologicalSpace.Opens.inclusion (fun _ hx => hx.trans_le (add_le_add hDD (le_refl 1)));
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      (∀ t ∈ Ico (H.time last) s, G.flow.base.metric t = H.stageMetric last t) →
      ∀ (Jbig : standardCapWindow Dbig → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      ∀ (q q₀ a₀ : ℝ) (hq : 0 < q), 0 < q₀ → q₀ ≤ Cbirth * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      (∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s,
        q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      q * (s - H.time first) ≤ Θ →
      ∀ (z : standardCapWindow D) (x : (H.stage last).Carrier)
        (Atrace : BackwardPointTrace H first last hle x),
        Atrace.point first le_rfl hle = Jbig (inc z) →
    ∃ f : (j : H.StageInterval first last) → standardCapWindow D → (H.stage j.val).Carrier,
      ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
        (∀ j, Function.Injective (f j)) ∧
        f ⟨first, le_rfl, hle⟩ = Jbig ∘ inc ∧
        (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∀ y : standardCapWindow D,
            (H.event i).RegularCrossing
              (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ y)
              (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ y)) ∧
        ∃ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
            (RealTimeInterval.closed (H.time first) s
              ((H.time_strictMono.monotone hle).trans G.lt.le)),
          IsSolutionOn S ∧
          (∀ j : H.StageInterval first last, ∀ t ∈ H.stageDomain j.val,
            t < s → S.base.metric t = localPullMetric (H.stageMetric j.val t) (f j) (hf j)) ∧
          (∀ t ∈ Icc 0 (q * (s - H.time first)), ∀ y : standardCapWindow D,
            normSq0S (scaleMetric q hq (S.base.metric (H.time first + t / q))) y 4
              (metricRm04At (scaleMetric q hq (S.base.metric (H.time first + t / q))) y) ≤ P ^ 2 ∧
            |metricScalarAt (scaleMetric q hq (S.base.metric (H.time first + t / q))) y| ≤ Creset) ∧
          ∃ (Φ : standardCapWindow D → G.terminalRegularOpen)
            (hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ),
            Subtype.val ∘ Φ = f ⟨last, hle, le_rfl⟩ ∧
            (Φ z).val = x ∧
            S.base.metric s = localPullMetric L.metric Φ hΦ ∧
          ∃ Q : StandardSolution,
            ENNReal.ofReal (q * (s - H.time first)) < Q.val.lifetime ∧
            ∀ t ∈ Icc 0 (q * (s - H.time first)),
              (∀ j ≤ N, ∀ y : standardCapWindow D,
                metricDerivNorm j (scaleMetric q hq (S.base.metric (H.time first + t / q)))
                  ((Q.val.metric t).restrictOpen (standardCapWindow D))
                  (StandardCap.metric.restrictOpen (standardCapWindow D)) y < ε) ∧
              ∀ j ≤ 2, ∀ y : standardCapWindow D,
                metricDerivNorm j (scaleMetric q hq (S.base.metric (H.time first + t / q)))
                  ((Q.val.metric t).restrictOpen (standardCapWindow D))
                  (StandardCap.metric.restrictOpen (standardCapWindow D)) y < η := by
  obtain ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, hwindow⟩ :=
    exists_uniform_prepared_incoming_cap_window_flow_of_backward_trace.{u, uE, uH, uM}
      Θ C hΘ hΘ1
  refine ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, ?_⟩
  intro E H₀ _ _ _ _ _ I _ D ε η hD hε hη N
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hwindow⟩ :=
    hwindow (I := I) D ε η hD hε hη N
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hR hm hζ hDD inc
    H first last hle s G L hG Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv hfinal htime z x Atrace hanchor
  have hinit : G.flow.base.metric (H.time last) = H.initialMetric last :=
    (hG (H.time last) ⟨le_rfl, G.lt⟩).trans (H.stageMetric_initial last)
  obtain ⟨hx, Ξ, hΞs, hbirth, hmarked, hΞ, gflow, F, hslabs, hlast, _, _, hFmetric,
    _, hcurv, Q, hQ, hclose⟩ := hwindow w hR hm hζ H first last hle s G L hinit
      Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero parameters records hfixed hlower
      hdelta hderiv hfinal htime z x Atrace hanchor
  obtain ⟨f, hf, hinj, hbirth', hcross, S, hS, hstage, hnormalized, Φ, hΦ, hΦval,
    hΦeq, hterminal⟩ := exists_common_flow_of_normalized_incoming_window
      H first last hle s G L hG hq (Jbig ∘ inc) Ξ hΞs hΞ hbirth gflow hslabs hlast F hFmetric
  refine ⟨f, hf, hinj, hbirth', hcross, S, hS, hstage, ?_, Φ, hΦ, hΦval, ?_,
    hterminal, Q, hQ, ?_⟩
  · intro t ht y
    rw [hnormalized t ht]
    exact hcurv t ht y
  · rw [hΦeq]
    exact congrArg Subtype.val hmarked
  · intro t ht
    rw [hnormalized t ht]
    exact hclose t ht

theorem exists_uniform_prepared_cap_common_flow_until_normalized_time
    (Θ : ℝ) (C : ℝ≥0) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ P Creset Cbirth : ℝ, 0 < P ∧ 0 < Creset ∧ 0 < Cbirth ∧
      ∀ {E : Type uE} {H₀ : Type uH} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless],
      ∀ (D ε η : ℝ) (hD : 0 < D), 0 < ε → 0 < η → ∀ N : ℕ,
      ∃ R : ℝ, ∃ hDR : D + 1 < R, ∃ m₀ : ℕ, 4 ≤ m₀ ∧
      ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {M : Type uM} [TopologicalSpace M] [ChartedSpace H₀ M]
        [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A}
        {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ)
        (hR : R ≤ Dbig), m₀ ≤ m → ζ ≤ ζ₀ →
      let hDD : D ≤ Dbig := by linarith;
      let inc : standardCapWindow D → standardCapWindow Dbig :=
        TopologicalSpace.Opens.inclusion (fun _ hx => hx.trans_le (add_le_add hDD (le_refl 1)));
      ∀ (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
        (t : Icc (0 : ℝ) H.horizon) (hbirth : H.time first < t.val),
      ∀ (Jbig : standardCapWindow Dbig → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      ∀ (q q₀ a₀ : ℝ) (hq : 0 < q), 0 < q₀ → q₀ ≤ Cbirth * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ H.activeStage t → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin (H.eventCount + 1), first ≤ j → j ≤ H.activeStage t →
        ∀ x : (H.stage j).Carrier, ∀ v ∈ Ioo (H.time j) (H.stageEndTime j), v ≤ t.val →
          q₀ < metricScalarAt (H.stageMetric j v) x →
          |derivWithin (fun a => metricScalarAt (H.stageMetric j a) x) (Iic v) v| ≤
            C * metricScalarAt (H.stageMetric j v) x ^ 2) →
      let s := min t.val (H.time first + Θ / q);
      let hs : H.time first < s := by
        exact lt_min hbirth (lt_add_of_pos_right _ (div_pos hΘ hq));
      let stop : Icc (0 : ℝ) H.horizon :=
        ⟨s, (H.time_nonneg first).trans hs.le, (min_le_left _ _).trans t.property.2⟩;
      let hfs : first ≤ H.activeStage stop := H.le_activeStage stop first hs.le;
      ∀ z : standardCapWindow D,
        Jbig (inc z) ∈ range (H.backwardSurvivorMap first (H.activeStage stop) hfs first le_rfl hfs) →
      q * (s - H.time first) ≤ Θ ∧
      (q * (s - H.time first) = Θ ∨ s = t.val) ∧
      ∃ (y : H.backwardSurvivorDomain first (H.activeStage stop) hfs),
        H.backwardSurvivorMap first (H.activeStage stop) hfs first le_rfl hfs y = Jbig (inc z) ∧
      ∃ (last : Fin (H.eventCount + 1)) (hle : first ≤ last) (hla : last ≤ H.activeStage stop)
        (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
        s ≤ H.stageEndTime last ∧
        (∀ v : ℝ, G.flow.base.metric v = H.stageMetric last v) ∧
    ∃ f : (j : H.StageInterval first last) → standardCapWindow D → (H.stage j.val).Carrier,
      ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
        (∀ j, Function.Injective (f j)) ∧
        f ⟨first, le_rfl, hle⟩ = Jbig ∘ inc ∧
        (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∀ y : standardCapWindow D,
            (H.event i).RegularCrossing
              (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ y)
              (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ y)) ∧
        ∃ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
            (RealTimeInterval.closed (H.time first) s
              ((H.time_strictMono.monotone hle).trans G.lt.le)),
          IsSolutionOn S ∧
          (∀ j : H.StageInterval first last, ∀ t ∈ H.stageDomain j.val,
            t < s → S.base.metric t = localPullMetric (H.stageMetric j.val t) (f j) (hf j)) ∧
          (∀ t ∈ Icc 0 (q * (s - H.time first)), ∀ y : standardCapWindow D,
            normSq0S (scaleMetric q hq (S.base.metric (H.time first + t / q))) y 4
              (metricRm04At (scaleMetric q hq (S.base.metric (H.time first + t / q))) y) ≤ P ^ 2 ∧
            |metricScalarAt (scaleMetric q hq (S.base.metric (H.time first + t / q))) y| ≤ Creset) ∧
          ∃ (Φ : standardCapWindow D → G.terminalRegularOpen)
            (hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ),
            Subtype.val ∘ Φ = f ⟨last, hle, le_rfl⟩ ∧
            (Φ z).val = H.backwardSurvivorMap first (H.activeStage stop) hfs last hle hla y ∧
            S.base.metric s = localPullMetric L.metric Φ hΦ ∧
          ∃ Q : StandardSolution,
            ENNReal.ofReal (q * (s - H.time first)) < Q.val.lifetime ∧
            ∀ t ∈ Icc 0 (q * (s - H.time first)),
              (∀ j ≤ N, ∀ y : standardCapWindow D,
                metricDerivNorm j (scaleMetric q hq (S.base.metric (H.time first + t / q)))
                  ((Q.val.metric t).restrictOpen (standardCapWindow D))
                  (StandardCap.metric.restrictOpen (standardCapWindow D)) y < ε) ∧
              ∀ j ≤ 2, ∀ y : standardCapWindow D,
                metricDerivNorm j (scaleMetric q hq (S.base.metric (H.time first + t / q)))
                  ((Q.val.metric t).restrictOpen (standardCapWindow D))
                  (StandardCap.metric.restrictOpen (standardCapWindow D)) y < η := by
  obtain ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, hflow⟩ :=
    exists_uniform_prepared_cap_common_flow_of_backward_trace.{u, uE, uH, uM}
      Θ C hΘ hΘ1
  refine ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, ?_⟩
  intro E H₀ _ _ _ _ _ I _ D ε η hD hε hη N
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hflow⟩ :=
    hflow (I := I) D ε η hD hε hη N
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hR hm hζ hDD inc
    H first t hbirth Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv s hs stop hfs z hmarker
  have hsTarget : s ≤ t.val := min_le_left _ _
  have hsAge : s ≤ H.time first + Θ / q := min_le_right _ _
  have htime : q * (s - H.time first) ≤ Θ := by
    have hdiv : s - H.time first ≤ Θ / q := by linarith
    have hh := (le_div_iff₀ hq).mp hdiv
    nlinarith
  have hstop : q * (s - H.time first) = Θ ∨ s = t.val := by
    rcases le_total t.val (H.time first + Θ / q) with ht | ht
    · exact Or.inr (min_eq_left ht)
    · left
      have he : s = H.time first + Θ / q := min_eq_right ht
      rw [he]
      field_simp
      ring
  obtain ⟨y, hy⟩ := hmarker
  obtain ⟨last, hle, hla, G, ⟨L⟩, hsend, hG, hregular⟩ :=
    H.exists_incoming_prefix first stop hs
  have hlt : last ≤ H.activeStage t := hla.trans (H.activeStage_mono hsTarget)
  let Atr : BackwardPointTrace H first (H.activeStage stop) hfs y.val :=
    Classical.choice y.property
  let Atrace := Atr.restrictLast hle hla
  have hanchor : Atrace.point first le_rfl hle = Jbig (inc z) := by
    exact (H.backwardSurvivorMap_eq_point first (H.activeStage stop) hfs
      first le_rfl hfs y Atr).symm.trans hy
  have hfinal : ∀ x : (H.stage last).Carrier, ∀ v ∈ Ioo (H.time last) s,
      q₀ < G.flow.scalar v x →
      |derivWithin (fun a => G.flow.scalar a x) (Iic v) v| ≤ C * G.flow.scalar v x ^ 2 := by
    intro x v hv hhigh
    have hsc : ∀ a, G.flow.scalar a x = metricScalarAt (H.stageMetric last a) x := by
      intro a
      change metricScalarAt (G.flow.base.metric a) x = _
      rw [hG a]
    simpa only [hsc] using hderiv last hle hlt x v
      ⟨hv.1, hv.2.trans_le hsend⟩ (hv.2.le.trans hsTarget) (by simpa only [hsc] using hhigh)
  have hevents : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q₀ < (H.event j).incoming.flow.scalar v x →
      |derivWithin (fun a => (H.event j).incoming.flow.scalar a x) (Iic v) v| ≤
        C * (H.event j).incoming.flow.scalar v x ^ 2 := by
    intro j hj hjl x v hv hhigh
    have hvTarget : v ≤ t.val :=
      hv.2.le.trans ((H.time_strictMono.monotone (hjl.trans hlt)).trans (H.activeStage_time_le t))
    have hvEnd : v ∈ Ioo (H.time j.castSucc) (H.stageEndTime j.castSucc) := by
      simpa only [H.stageEndTime_castSucc] using hv
    have hsc : ∀ a, metricScalarAt (H.stageMetric j.castSucc a) x =
        (H.event j).incoming.flow.scalar a x := by
      intro a
      simp only [stageMetric, Fin.lastCases_castSucc]
      rfl
    simpa only [hsc] using
      hderiv j.castSucc hj ((j.castSucc_lt_succ.le.trans hjl).trans hlt) x v hvEnd hvTarget
        (by simpa only [hsc] using hhigh)
  obtain ⟨f, hf, hinj, hfBirth, hcross, S, hS, hstage, hcurv, Φ, hΦ, hΦval,
    hmarked, hterminal, Q, hQ, hclose⟩ :=
    hflow w hR hm hζ H first last hle s G L (fun v _ => hG v)
      Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero parameters records hfixed hlower
      (fun j hj hjl => hdelta j hj (hjl.trans hlt)) hevents hfinal htime
      z (Atr.point last hle hla) Atrace hanchor
  refine ⟨htime, hstop, y, hy, last, hle, hla, G, L, hsend, hG, f, hf, hinj,
    hfBirth, hcross, S, hS, hstage, hcurv, Φ, hΦ, hΦval, ?_, hterminal, Q, hQ, hclose⟩
  exact hmarked.trans (H.backwardSurvivorMap_eq_point first (H.activeStage stop) hfs
    last hle hla y Atr).symm


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
