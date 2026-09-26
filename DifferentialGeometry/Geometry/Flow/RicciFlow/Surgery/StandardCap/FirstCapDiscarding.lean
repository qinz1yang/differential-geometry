import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowDiscarding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowCommonFlow
set_option autoImplicit false
noncomputable section
open Set Function Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology NNReal ENNReal
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
