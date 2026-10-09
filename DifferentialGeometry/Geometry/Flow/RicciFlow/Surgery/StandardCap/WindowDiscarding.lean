import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowCommonFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFirstLoss
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowPersistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowCrossing
import DifferentialGeometry.Geometry.Metric.PullbackScaling

set_option autoImplicit false
noncomputable section
open Set Function Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u uE uH uM
private local instance (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

theorem exists_uniform_first_cap_discarding_event_of_not_surviving
    (Θ : ℝ) (C : ℝ≥0) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ P Creset Cbirth : ℝ, 0 < P ∧ 0 < Creset ∧ 0 < Cbirth ∧
      ∀ {E : Type uE} {H₀ : Type uH} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless],
      ∀ (a Rtarget ε : ℝ), 0 < a → 0 < ε → ∀ N : ℕ,
      ∃ (D : ℝ) (hD : 0 < D), a + 1 < D ∧ Rtarget < D ∧
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
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last),
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
      q * (H.time last - H.time first) ≤ Θ →
      (¬ Jbig '' {x : standardCapWindow Dbig | ‖x.val‖ ≤ a} ⊆
        range (H.backwardSurvivorMap first last hle first le_rfl hle)) →
      ∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc), i.succ ≤ last ∧
        (∀ (j : Fin (H.eventCount + 1)) (hj : first ≤ j), j ≤ i.castSucc →
          Jbig '' {x : standardCapWindow Dbig | ‖x.val‖ ≤ a} ⊆
            range (H.backwardSurvivorMap first j hj first le_rfl hj)) ∧
      ∃ Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first i.castSucc hf (H.event i).incoming,
          IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
          (∀ y, H.backwardSurvivorMap first i.castSucc hf first le_rfl hf (Ξ y).val = (Jbig ∘ inc) y) ∧
          ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
            (gflow : ℝ → SmoothRiemannianMetric ThreeModel
              (H.backwardSurvivorIncomingDomain first i.castSucc hf (H.event i).incoming))
            (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
              (RealTimeInterval.closed 0 (q * (H.time i.succ - H.time first))
                (by have ht := H.time_strictMono (hf.trans_lt i.castSucc_lt_succ); positivity))),
            (∀ (j : Fin H.eventCount) (hj : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
              ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
                gflow t = (H.backwardSurvivorSlabMetric first i.castSucc hf j hj hl t).restrictOpen
                  (H.backwardSurvivorIncomingDomain first i.castSucc hf (H.event i).incoming)) ∧
            (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
              gflow t = H.backwardSurvivorIncomingMetric first i.castSucc hf (H.event i).incoming (H.event i).terminal t) ∧
            IsSolutionOn S ∧ S.base.metric 0 = (w.restrictWindow hD hDD).windowMetric ∧
            (∀ t, S.base.metric t =
              localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) ∧
            (∀ (y : standardCapWindow D) (j k : Fin (Module.finrank ℝ ThreeSpace)),
              ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
                (fun z : ℝ × standardCapWindow D => chartGramMatrix (S.base.metric z.1) y z.2 j k)
                (Icc 0 (q * (H.time i.succ - H.time first)) ×ˢ
                  (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
            (∀ t ∈ Icc 0 (q * (H.time i.succ - H.time first)), ∀ y : standardCapWindow D,
              normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ P ^ 2 ∧ |S.scalar t y| ≤ Creset) ∧
            (∀ y : standardCapWindow D, ‖y.val‖ ≤ a →
              ∃ z : (H.event i).transition.trace.tubes.core,
                z.val = (H.backwardSurvivorIncomingMap first i.castSucc hf (H.event i).incoming (Ξ y)).val ∧
                ∃ d : (H.event i).discarded.Carrier,
                  (H.event i).transition.trace.presentation
                    ((H.event i).transition.trace.capping.coreInclusion z) = Sum.inr d) ∧
            ∃ Q : StandardSolution, ENNReal.ofReal (q * (H.time i.succ - H.time first)) < Q.val.lifetime ∧
              ∀ t ∈ Icc 0 (q * (H.time i.succ - H.time first)),
                (∀ j ≤ N, ∀ y : standardCapWindow D,
                  metricDerivNorm j (S.base.metric t)
                    ((Q.val.metric t).restrictOpen (standardCapWindow D))
                    (StandardCap.metric.restrictOpen (standardCapWindow D)) y < ε) ∧
                ∀ j ≤ 2, ∀ y : standardCapWindow D,
                  metricDerivNorm j (S.base.metric t)
                    ((Q.val.metric t).restrictOpen (standardCapWindow D))
                    (StandardCap.metric.restrictOpen (standardCapWindow D)) y < ε := by
  obtain ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, hwindow⟩ :=
    exists_uniform_prepared_incoming_cap_window_flow_of_backward_trace Θ C hΘ hΘ1
  obtain ⟨Rtip, εtip, hRtip, hεtip, hcross⟩ :=
    exists_cutoff_cap_survivor_partialDiffeomorph_or_discarded_of_standard_metric_close Θ hΘ.le hΘ1
  refine ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, ?_⟩
  intro E H₀ _ _ _ _ _ I _ a Rtarget ε ha hε N
  let b := max a Rtip
  let D := max (b + 2) (Rtarget + 1)
  have hb : 0 < b := ha.trans_le (le_max_left _ _)
  have hD : 0 < D := lt_of_lt_of_le (by linarith : 0 < b + 2) (le_max_left _ _)
  have haD : a + 1 < D := by
    have haB : a ≤ b := le_max_left _ _
    have hBD : b + 2 ≤ D := le_max_left _ _
    linarith
  have htarget : Rtarget < D := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨ηcut, hηcut, hcross⟩ := hcross b (le_max_right _ _)
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δwindow, hζ₀, hζhalf, hδwindow, hwindow⟩ :=
    hwindow (I := I) D ε (min ε εtip) hD hε (lt_min hε hεtip) N
  refine ⟨D, hD, haD, htarget, R, hDR, m₀, hm₀, ζ₀, min δwindow ηcut,
    hζ₀, hζhalf, lt_min hδwindow hηcut, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hR hm hζ hDD inc
    H first last hle Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv htime hnot
  let X := {x : standardCapWindow Dbig // ‖x.val‖ ≤ a}
  let J : X → (H.stage first).Carrier := fun x => Jbig x.val
  have hrange : range J = Jbig '' {x : standardCapWindow Dbig | ‖x.val‖ ≤ a} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  obtain ⟨i, hf, hil, hpast, zbad, p, Atrace, hbirthTrace, hbad⟩ :=
    H.exists_first_event_trace_without_regularCrossing first last hle J (by rwa [hrange])
  let z : standardCapWindow D := ⟨zbad.val.val, by
    change ‖zbad.val.val‖ < D + 1
    have hz := zbad.property
    change ‖zbad.val.val‖ ≤ a at hz
    linarith⟩
  have hincz : inc z = zbad.val := Subtype.ext rfl
  have hanchor : Atrace.point first le_rfl hf = Jbig (inc z) := by
    rw [hincz]
    exact hbirthTrace
  have hδprior : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      ∀ c, (records j).delta c ≤ δwindow := by
    intro j hj hji c
    exact (hdelta j hj (hji.trans (i.castSucc_lt_succ.le.trans hil)) c).trans (min_le_left _ _)
  have hderivPrior : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2 :=
    fun j hj hji => hderiv j hj (hji.trans (i.castSucc_lt_succ.le.trans hil))
  have htimei : q * (H.time i.succ - H.time first) ≤ Θ :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_right (H.time_strictMono.monotone hil) _) hq.le).trans htime
  obtain ⟨hp, Ξ, hΞs, hbirth, hmarked, hΞ, gflow, S, hslabs, hlast, hS, hSzero,
    hmetric, hgram, hcurv, Q, hQ, hclose⟩ :=
    hwindow w hR hm hζ H first i.castSucc hf (H.time i.succ) (H.event i).incoming
      (H.event i).terminal (H.event_initial i) Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
      parameters records hfixed hlower hδprior hderivPrior (hderiv i hf hil) htimei z p Atrace hanchor
  let age := q * (H.time i.succ - H.time first)
  have hage : 0 < age := mul_pos hq (sub_pos.mpr (H.time_strictMono (hf.trans_lt i.castSucc_lt_succ)))
  let Φ := H.backwardSurvivorIncomingMap first i.castSucc hf (H.event i).incoming ∘ Ξ
  have hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ :=
    isLocalDiffeomorph_comp (H.backwardSurvivorIncomingMap_isLocalDiffeomorph _ _ _ _) hΞ
  have hΦinj : Injective Φ :=
    (H.backwardSurvivorIncomingMap_injective _ _ _ _).comp hΞs.isEmbedding.injective
  have hmet : S.base.metric age = localPullMetric (scaleMetric q hq (H.event i).terminal.metric) Φ hΦ := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v z
    have hc : H.time first + age / q = H.time i.succ := by
      dsimp only [age]
      rw [mul_div_cancel_left₀ _ hq.ne']
      ring
    rw [hmetric, hc, hlast _ ⟨(H.event i).incoming.lt.le, le_rfl⟩,
      H.backwardSurvivorIncomingMetric_terminal]
    rw [localPullMetric_inner, scaleMetric_inner, localPullMetric_inner, localPullMetric_inner, scaleMetric_inner]
    rw [mfderiv_comp x
      ((H.backwardSurvivorIncomingMap_isLocalDiffeomorph _ _ _ _).contMDiff.mdifferentiableAt (by simp))
      (hΞ.contMDiff.mdifferentiableAt (by simp))]
    rfl
  have hcp : ∀ x : standardCapWindow D, ‖x.val‖ < D → ∀ j ≤ 2,
      metricDerivNorm j (localPullMetric (scaleMetric q hq (H.event i).terminal.metric) Φ hΦ)
        ((Q.val.metric age).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) x ≤ εtip := by
    intro x _ j hj
    rw [← hmet]
    exact ((hclose age ⟨hage.le, le_rfl⟩).2 j hj x).le.trans (min_le_right _ _)
  have hcut := hcross H i parameters (records i) (records i).old_eq_retained
    (fun c => (hdelta i hf hil c).trans (min_le_right _ _)) Rtip D le_rfl (le_max_right _ _)
    (by have := le_max_left (b + 2) (Rtarget + 1); dsimp only [D] at *; linarith)
    Q age ⟨hage.le, htimei⟩ Φ hΦ hΦinj q hq hcp
  have hdiscard : ∀ x ∈ Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ b},
      ∃ z : (H.event i).transition.trace.tubes.core, z.val = x.val ∧
        ∃ d : (H.event i).discarded.Carrier,
          (H.event i).transition.trace.presentation ((H.event i).transition.trace.capping.coreInclusion z) = Sum.inr d := by
    rcases hcut with ⟨F, hFsource, hFcross, _, _⟩ | hdiscard
    · have hz : ‖z.val‖ ≤ b := zbad.property.trans (le_max_left _ _)
      have hc := hFcross (Φ z) (hFsource (mem_image_of_mem Φ hz))
      have hpz : (Φ z).val = p := congrArg Subtype.val hmarked
      rw [hpz] at hc
      exact (hbad (F (Φ z)) hc).elim
    · exact hdiscard
  refine ⟨i, hf, hil, ?_, Ξ, hΞs, hbirth, hΞ, gflow, S, hslabs, hlast, hS, hSzero,
    hmetric, hgram, hcurv, ?_, Q, hQ, ?_⟩
  · intro j hj hji
    rw [← hrange]
    exact hpast j hj hji
  · intro y hy
    exact hdiscard (Φ y) (mem_image_of_mem Φ (hy.trans (le_max_left _ _)))
  · intro t ht
    exact ⟨(hclose t ht).1, fun j hj y => ((hclose t ht).2 j hj y).trans_le (min_le_left _ _)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u uE uH uM

theorem exists_uniform_first_cap_discarding_common_flow_of_not_surviving
    (Θ : ℝ) (C : ℝ≥0) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ P Creset Cbirth : ℝ, 0 < P ∧ 0 < Creset ∧ 0 < Cbirth ∧
      ∀ {E : Type uE} {H₀ : Type uH} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless],
      ∀ (a Rtarget ε : ℝ), 0 < a → 0 < ε → ∀ N : ℕ,
      ∃ (D : ℝ) (hD : 0 < D), a + 1 < D ∧ Rtarget < D ∧
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
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last),
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
      q * (H.time last - H.time first) ≤ Θ →
      (¬ Jbig '' {x : standardCapWindow Dbig | ‖x.val‖ ≤ a} ⊆
        range (H.backwardSurvivorMap first last hle first le_rfl hle)) →
      ∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc), i.succ ≤ last ∧
        (∀ (j : Fin (H.eventCount + 1)) (hj : first ≤ j), j ≤ i.castSucc →
          Jbig '' {x : standardCapWindow Dbig | ‖x.val‖ ≤ a} ⊆
            range (H.backwardSurvivorMap first j hj first le_rfl hj)) ∧
      ∃ f : (j : H.StageInterval first i.castSucc) → standardCapWindow D → (H.stage j.val).Carrier,
        ∃ hfmap : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
          (∀ j, Function.Injective (f j)) ∧
          f ⟨first, le_rfl, hf⟩ = Jbig ∘ inc ∧
          (∀ (j : Fin H.eventCount) (hj : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
            ∀ y : standardCapWindow D,
              (H.event j).RegularCrossing
                (f ⟨j.castSucc, hj, j.castSucc_lt_succ.le.trans hl⟩ y)
                (f ⟨j.succ, hj.trans j.castSucc_lt_succ.le, hl⟩ y)) ∧
          ∃ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
              (RealTimeInterval.closed (H.time first) (H.time i.succ)
                (H.time_strictMono.monotone (hf.trans i.castSucc_lt_succ.le))),
            IsSolutionOn S ∧
            scaleMetric q hq (S.base.metric (H.time first)) =
              (w.restrictWindow hD hDD).windowMetric ∧
            (∀ j : H.StageInterval first i.castSucc, ∀ t ∈ H.stageDomain j.val,
              t < H.time i.succ →
                S.base.metric t = localPullMetric (H.stageMetric j.val t) (f j) (hfmap j)) ∧
            (∀ t ∈ Icc 0 (q * (H.time i.succ - H.time first)), ∀ y : standardCapWindow D,
              normSq0S (scaleMetric q hq (S.base.metric (H.time first + t / q))) y 4
                (metricRm04At (scaleMetric q hq (S.base.metric (H.time first + t / q))) y) ≤ P ^ 2 ∧
              |metricScalarAt (scaleMetric q hq (S.base.metric (H.time first + t / q))) y| ≤ Creset) ∧
            ∃ (Φ : standardCapWindow D → (H.event i).incoming.terminalRegularOpen)
              (hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ),
              Subtype.val ∘ Φ = f ⟨i.castSucc, hf, le_rfl⟩ ∧
              S.base.metric (H.time i.succ) = localPullMetric (H.event i).terminal.metric Φ hΦ ∧
              (∀ y : standardCapWindow D, ‖y.val‖ ≤ a →
                ∃ z : (H.event i).transition.trace.tubes.core,
                  z.val = (Φ y).val ∧ ∃ d : (H.event i).discarded.Carrier,
                    (H.event i).transition.trace.presentation
                      ((H.event i).transition.trace.capping.coreInclusion z) = Sum.inr d) ∧
              ∃ Q : StandardSolution,
                ENNReal.ofReal (q * (H.time i.succ - H.time first)) < Q.val.lifetime ∧
                ∀ t ∈ Icc 0 (q * (H.time i.succ - H.time first)),
                  (∀ j ≤ N, ∀ y : standardCapWindow D,
                    metricDerivNorm j (scaleMetric q hq (S.base.metric (H.time first + t / q)))
                      ((Q.val.metric t).restrictOpen (standardCapWindow D))
                      (StandardCap.metric.restrictOpen (standardCapWindow D)) y < ε) ∧
                  ∀ j ≤ 2, ∀ y : standardCapWindow D,
                    metricDerivNorm j (scaleMetric q hq (S.base.metric (H.time first + t / q)))
                      ((Q.val.metric t).restrictOpen (standardCapWindow D))
                      (StandardCap.metric.restrictOpen (standardCapWindow D)) y < ε := by
  obtain ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, hdiscard⟩ :=
    exists_uniform_first_cap_discarding_event_of_not_surviving.{u, uE, uH, uM} Θ C hΘ hΘ1
  refine ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, ?_⟩
  intro E H₀ _ _ _ _ _ I _ a Rtarget ε ha hε N
  obtain ⟨D, hD, haD, htarget, R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hdiscard⟩ :=
    hdiscard (I := I) a Rtarget ε ha hε N
  refine ⟨D, hD, haD, htarget, R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hR hm hζ hDD inc
    H first last hle Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv htime hnot
  obtain ⟨i, hf, hil, hpast, Ξ, hΞs, hbirth, hΞ, gflow, F, hslabs, hlast,
    _, hFzero, hFmetric, _, hcurv, hdiscarded, Q, hQ, hclose⟩ :=
    hdiscard w hR hm hζ H first last hle Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq
      hzero parameters records hfixed hlower hdelta hderiv htime hnot
  have hG : ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ),
      (H.event i).incoming.flow.base.metric t = H.stageMetric i.castSucc t := by
    intro t _
    simp only [stageMetric, Fin.lastCases_castSucc]
  obtain ⟨f, hfmap, hinj, hbirth', hcross, S, hS, hstage, hnormalized, Φ, hΦ,
      hΦval, hΦeq, hterminal⟩ :=
    exists_common_flow_of_normalized_incoming_window H first i.castSucc hf
      (H.time i.succ) (H.event i).incoming (H.event i).terminal hG hq (Jbig ∘ inc)
      Ξ hΞs hΞ hbirth gflow hslabs hlast F hFmetric
  refine ⟨i, hf, hil, hpast, f, hfmap, hinj, hbirth', hcross, S, hS, ?_,
    hstage, ?_, Φ, hΦ, hΦval, hterminal, ?_, Q, hQ, ?_⟩
  · have hzeroage : (0 : ℝ) ∈ Icc 0 (q * (H.time i.succ - H.time first)) :=
      ⟨le_rfl, mul_nonneg hq.le
        (sub_nonneg.mpr (H.time_strictMono.monotone (hf.trans i.castSucc_lt_succ.le)))⟩
    simpa only [zero_div, add_zero] using (hnormalized 0 hzeroage).trans hFzero
  · intro t ht y
    rw [hnormalized t ht]
    exact hcurv t ht y
  · intro y hy
    rw [hΦeq]
    exact hdiscarded y hy
  · intro t ht
    rw [hnormalized t ht]
    exact hclose t ht

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
