import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowCommonFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowDiscarding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FirstCapDiscarding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.PreparedCapCommonFlow

set_option autoImplicit false
noncomputable section
open Set Function Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u uE uH uM

theorem exists_uniform_prepared_cap_evolution
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
      (∃ (s : ℝ), H.time first < s ∧ s ≤ t.val ∧ q * (s - H.time first) ≤ Θ ∧
        (q * (s - H.time first) = Θ ∨ s = t.val) ∧
        ∃ (last : Fin (H.eventCount + 1)) (hle : first ≤ last), last ≤ H.activeStage t ∧
        ∃ (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
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
                  (StandardCap.metric.restrictOpen (standardCapWindow D)) y < ε) ∨
      (∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc), i.succ ≤ H.activeStage t ∧
        H.time i.succ ≤ t.val ∧ q * (H.time i.succ - H.time first) ≤ Θ ∧
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
                      (StandardCap.metric.restrictOpen (standardCapWindow D)) y < ε) := by
  classical
  obtain ⟨Pd, Cd, Cbd, hPd, hCd, hCbd, hdiscard⟩ :=
    exists_uniform_first_cap_discarding_common_flow_of_not_surviving.{u, uE, uH, uM}
      Θ C hΘ hΘ1
  obtain ⟨Ps, Cs, Cbs, hPs, hCs, hCbs, hsurvive⟩ :=
    exists_uniform_prepared_cap_common_flow_until_normalized_time.{u, uE, uH, uM}
      Θ C hΘ hΘ1
  refine ⟨max Pd Ps, max Cd Cs, min Cbd Cbs,
    hPd.trans_le (le_max_left _ _), hCd.trans_le (le_max_left _ _), lt_min hCbd hCbs, ?_⟩
  intro E H₀ _ _ _ _ _ I _ a Rtarget ε ha hε N
  obtain ⟨D, hD, haD, htarget, Rd, hDRd, md, hmd, ζd, δd, hζd, hζdh, hδd, hdiscard⟩ :=
    hdiscard (I := I) a Rtarget ε ha hε N
  obtain ⟨Rs, hDRs, ms, hms, ζs, δs, hζs, hζsh, hδs, hsurvive⟩ :=
    hsurvive (I := I) D ε ε hD hε hε N
  refine ⟨D, hD, haD, htarget, max Rd Rs, hDRd.trans_le (le_max_left _ _),
    max md ms, hmd.trans (le_max_left _ _), min ζd ζs, min δd δs,
    lt_min hζd hζs, (min_le_left _ _).trans hζdh, lt_min hδd hδs, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hR hm hζ hDD inc
    H first t hbirth Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv
  have hRd : Rd ≤ Dbig := (le_max_left _ _).trans hR
  have hRs : Rs ≤ Dbig := (le_max_right _ _).trans hR
  have hmdm : md ≤ m := (le_max_left _ _).trans hm
  have hmsm : ms ≤ m := (le_max_right _ _).trans hm
  have hζd' : ζ ≤ ζd := hζ.trans (min_le_left _ _)
  have hζs' : ζ ≤ ζs := hζ.trans (min_le_right _ _)
  have hq₀d : q₀ ≤ Cbd * q := hq₀Q.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le)
  have hq₀s : q₀ ≤ Cbs * q := hq₀Q.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hq.le)
  let s := min t.val (H.time first + Θ / q)
  have hs : H.time first < s := lt_min hbirth (lt_add_of_pos_right _ (div_pos hΘ hq))
  have hsTarget : s ≤ t.val := min_le_left _ _
  let stop : Icc (0 : ℝ) H.horizon :=
    ⟨s, (H.time_nonneg first).trans hs.le, hsTarget.trans t.property.2⟩
  have hfs : first ≤ H.activeStage stop := H.le_activeStage stop first hs.le
  have hstopTarget : H.activeStage stop ≤ H.activeStage t := H.activeStage_mono hsTarget
  let z : standardCapWindow D := ⟨0, by change ‖(0 : ThreeSpace)‖ < D + 1; simp only [norm_zero]; linarith⟩
  have htime : q * (s - H.time first) ≤ Θ := by
    have hh := (le_div_iff₀ hq).mp
      (show s - H.time first ≤ Θ / q from by have := min_le_right t.val (H.time first + Θ / q); dsimp only [s]; linarith)
    nlinarith
  by_cases hmarker : Jbig (inc z) ∈
      range (H.backwardSurvivorMap first (H.activeStage stop) hfs first le_rfl hfs)
  · obtain ⟨hage, hstop, y, hy, last, hle, hla, G, L, hsend, hG,
      f, hfmap, hinj, hfbirth, hcross, S, hS, hstage, hcurv, Φ, hΦ,
      hΦval, hmarked, hterminal, Q, hQ, hclose⟩ :=
      hsurvive w hRs hmsm hζs' H first t hbirth Jbig hJbig q q₀ a₀ hq hq₀ hq₀s haq
        hzero parameters records hfixed hlower
        (fun j hj hjt b => (hdelta j hj hjt b).trans (min_le_right _ _)) hderiv z hmarker
    left
    refine ⟨s, hs, hsTarget, hage, hstop, last, hle, hla.trans hstopTarget, G, L, hsend, hG,
      f, hfmap, hinj, hfbirth, hcross, S, hS, hstage, ?_, Φ, hΦ, hΦval,
      hterminal, Q, hQ, hclose⟩
    intro v hv x
    have hc := hcurv v hv x
    exact ⟨hc.1.trans (pow_le_pow_left₀ hPs.le (le_max_right Pd Ps) 2),
      hc.2.trans (le_max_right _ _)⟩
  · have hnot : ¬ Jbig '' {x : standardCapWindow Dbig | ‖x.val‖ ≤ a} ⊆
        range (H.backwardSurvivorMap first (H.activeStage stop) hfs first le_rfl hfs) := by
      intro hall
      apply hmarker
      exact hall ⟨inc z, by change ‖(0 : ThreeSpace)‖ ≤ a; simpa only [norm_zero] using ha.le, rfl⟩
    have htimeStage : q * (H.time (H.activeStage stop) - H.time first) ≤ Θ :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right (H.activeStage_time_le stop) _) hq.le).trans htime
    have hevents : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ H.activeStage stop →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.event j).incoming.flow.scalar v x →
        |derivWithin (fun a => (H.event j).incoming.flow.scalar a x) (Iic v) v| ≤
          C * (H.event j).incoming.flow.scalar v x ^ 2 := by
      intro j hj hjl x v hv hhigh
      have hvTarget : v ≤ t.val := hv.2.le.trans
        ((H.time_strictMono.monotone (hjl.trans hstopTarget)).trans (H.activeStage_time_le t))
      have hvEnd : v ∈ Ioo (H.time j.castSucc) (H.stageEndTime j.castSucc) := by
        simpa only [H.stageEndTime_castSucc] using hv
      have hsc : ∀ r, metricScalarAt (H.stageMetric j.castSucc r) x =
          (H.event j).incoming.flow.scalar r x := by
        intro r
        simp only [stageMetric, Fin.lastCases_castSucc]
        rfl
      simpa only [hsc] using
        hderiv j.castSucc hj ((j.castSucc_lt_succ.le.trans hjl).trans hstopTarget) x v
          hvEnd hvTarget (by simpa only [hsc] using hhigh)
    obtain ⟨i, hf, hil, hpast, f, hfmap, hinj, hfbirth, hcross, S, hS, hSzero,
      hstage, hcurv, Φ, hΦ, hΦval, hterminal, hdiscarded, Q, hQ, hclose⟩ :=
      hdiscard w hRd hmdm hζd' H first (H.activeStage stop) hfs Jbig hJbig q q₀ a₀ hq hq₀ hq₀d haq
        hzero parameters records hfixed hlower
        (fun j hj hjl b => (hdelta j hj (hjl.trans hstopTarget) b).trans (min_le_left _ _))
        hevents htimeStage hnot
    have heventStop : H.time i.succ ≤ s :=
      (H.time_strictMono.monotone hil).trans (H.activeStage_time_le stop)
    have hage : q * (H.time i.succ - H.time first) ≤ Θ :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right heventStop _) hq.le).trans htime
    right
    refine ⟨i, hf, hil.trans hstopTarget, heventStop.trans hsTarget, hage,
      f, hfmap, hinj, hfbirth, hcross, S, hS, hSzero, hstage, ?_, Φ, hΦ,
      hΦval, hterminal, hdiscarded, Q, hQ, hclose⟩
    intro v hv x
    have hc := hcurv v hv x
    exact ⟨hc.1.trans (pow_le_pow_left₀ hPd.le (le_max_left Pd Ps) 2),
      hc.2.trans (le_max_left _ _)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
