import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFirstLossFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowCrossing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowRicciBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowSurvival

set_option autoImplicit false
noncomputable section
open Set Function Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
private local instance (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

theorem exists_uniform_cap_window_survival_step_of_standard_tip_metric_close
    (Θ Kpast C₀ : ℝ) (C : ℝ≥0) (hΘ : 0 ≤ Θ) (hΘ1 : Θ < 1) (hC₀ : 0 < C₀) :
    ∃ ε δstep : ℝ, 0 < ε ∧ 0 < δstep ∧ ∀ D : ℝ, 32 < D →
      ∃ η : ℝ, 0 < η ∧
      ∀ {E H₀ M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H₀ M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      4 ≤ m → ζ ≤ 1 / 2 →
      (∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
        w.windowMetric.inner x v v ≤ (3 / 2 : ℝ) * StandardCap.metric.inner x.val v v) →
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (next : Fin H.eventCount) (hnext : first ≤ next.castSucc)
    (J : standardCapWindow D → (H.stage first).Carrier) (_ : IsSmoothEmbedding ThreeModel ThreeModel ∞ J)
    {τ : ℝ} (G : (H.stage next.castSucc).IncomingSlab (H.time next.castSucc) τ)
    (L : G.TerminalLimitMetric)
    (_ : ∀ t, G.flow.base.metric t = (H.event next).incoming.flow.base.metric t)
    (_ : L.metric =
      ((H.event next).incoming.flow.base.metric τ).restrictOpen G.terminalRegularOpen)
    (_ : τ ∈ Ico (H.time next.castSucc) (H.time next.succ))
    (Ψ : standardCapWindow D → H.backwardSurvivorIncomingDomain first next.castSucc hnext G)
    (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ)
    (_ : ∀ x, H.backwardSurvivorMap first next.castSucc hnext first le_rfl hnext
      (Ψ x).val = J x)
    (gflow₀ : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first next.castSucc hnext G))
    (_ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ next.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow₀ t = (H.backwardSurvivorSlabMetric first next.castSucc hnext j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first next.castSucc hnext G))
    (_ : ∀ t ∈ Icc (H.time next.castSucc) τ,
      gflow₀ t = H.backwardSurvivorIncomingMetric first next.castSucc hnext G L t)
    {r q a₀ : ℝ}
    (hq : 0 < q) (_ : r ≤ C₀ * q) (_ : 1 ≤ a₀ * q)
    (_ : ∀ x (v z : TangentSpace ThreeModel x),
      w.windowMetric.inner x v z = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x z))
    {D₀ : RealTimeInterval} (S₀ : SolutionOn (I := ThreeModel) (M := standardCapWindow D) D₀)
    (_ : ∀ t ∈ Icc 0 (q * (τ - H.time first)), S₀.base.metric t =
      localPullMetric (scaleMetric q hq (gflow₀ (H.time first + t / q))) Ψ hΨ)
    (_ : ∀ t ∈ Icc 0 (q * (τ - H.time first)), ∀ x : standardCapWindow D,
      normSq0S (S₀.base.metric t) x 4 (S₀.base.rm04 t x) ≤ Kpast)
    (_ : ∀ x, (H.event next).incoming.flow.scalar τ (Ψ x).val.val ≤ C₀ * q)
    (_ : ∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        r < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    (_ : ∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last →
      ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ), τ ≤ t →
        ∀ x : (H.stage j.castSucc).Carrier,
          InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀ x),
      q * (H.time last - H.time first) ≤ Θ → q * (H.time last - τ) ≤ δstep →
      ∀ (Q : StandardSolution) (s₀ : ℝ), s₀ ∈ Icc 0 Θ →
      ∀ (tip : standardCapWindow D), tip.val = 0 →
      (∀ j ≤ 2, metricDerivNorm j (S₀.base.metric (q * (τ - H.time first)))
        ((Q.val.metric s₀).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) tip ≤ ε) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ η) →
      ∀ (z : standardCapWindow D) (endpoint : (H.stage last).Carrier)
        (Atrace : BackwardPointTrace H first last hle endpoint), Atrace.point first le_rfl hle = J z →
      ∃ Υ : standardCapWindow D → H.backwardSurvivorDomain first last hle,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Υ ∧
        ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Υ x) = J x := by
  let K := max Kpast ((2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2)
  obtain ⟨ε, σ, c, hε, hσ, hc, htip⟩ :=
    StandardCap.exists_uniform_window_tip_ricci_lower_bound_of_standard_metric_close Θ Θ K hΘ hΘ1
  let δstep := min σ (2 * ((C : ℝ) + 1) * C₀)⁻¹
  have hδstep : 0 < δstep := lt_min hσ (by positivity)
  have hprotect :=
    exists_cutoff_cap_survivor_partialDiffeomorph_of_window_flow_tip_ricci_lower_bound Θ K c hc
  refine ⟨ε, δstep, hε, hδstep, ?_⟩
  intro D hD
  obtain ⟨η, hη, hprotect⟩ := hprotect D (by linarith)
  refine ⟨η, hη, ?_⟩
  intro E H₀ M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle next hnext J hJ τ G L hsource hterminal hτ Ψ hΨ hΨbirth
    gflow₀ hslabs₀ hlast₀ r q a₀ hq hrQ haq hzero D₀ S₀ hmetric₀ hpast hscalar
    hderiv hpinch hfulltime hremaining Q s₀ hs₀ tip htipzero hclose parameters records hdelta
    z endpoint Atrace hanchor
  have hbudget : 2 * C * C₀ * (q * (H.time last - τ)) ≤ 1 := by
    have hd := hremaining.trans (min_le_right _ _)
    have hp : 0 < 2 * ((C : ℝ) + 1) * C₀ := by positivity
    have hh := (le_div_iff₀ hp).mp (show q * (H.time last - τ) ≤ 1 / (2 * ((C : ℝ) + 1) * C₀) from by simpa only [one_div] using hd)
    by_cases ht : 0 ≤ q * (H.time last - τ)
    · nlinarith [mul_nonneg (show 0 ≤ 2 * C₀ by positivity) ht]
    · have htneg : q * (H.time last - τ) ≤ 0 := (lt_of_not_ge ht).le
      exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) htneg).trans (by norm_num)
  have hsurvive : range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle) := by
    by_contra hnot
    obtain ⟨i, hf, hni, hil, hpastStages, Ξ, hΞs, hbirth, hfailed, hΞ, gflow,
      hslabs, hlast, S, hS, hSzero, hmetric, hgram, hoverlap, hRm⟩ :=
      H.exists_first_event_normalized_chart_solution_of_scalar_bound_at_later_time
        first last hle next hnext J hJ G L hsource hterminal hτ Ψ hΨ hΨbirth
        gflow₀ hslabs₀ hlast₀ hC₀ hq hrQ haq w.windowMetric hzero S₀ hmetric₀ hpast
        hscalar hderiv hpinch hbudget hnot
    let θ := q * (H.time i.succ - H.time first)
    let uτ := q * (τ - H.time first)
    have hθ : 0 < θ := mul_pos hq (sub_pos.mpr (H.time_strictMono (hf.trans_lt i.castSucc_lt_succ)))
    have hθΘ : θ ≤ Θ := (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (H.time_strictMono.monotone hil) _) hq.le).trans hfulltime
    have hτphys : τ < H.time i.succ := hτ.2.trans_le
      (H.time_strictMono.monotone (Fin.succ_le_succ_iff.mpr (Fin.castSucc_le_castSucc_iff.mp hni)))
    have huτ : uτ ∈ Icc 0 θ := by
      constructor
      · dsimp only [uτ]
        exact mul_nonneg hq.le (sub_nonneg.mpr ((H.time_strictMono.monotone hnext).trans hτ.1))
      · dsimp only [uτ, θ]
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right hτphys.le _) hq.le
    have hθstep : θ ≤ uτ + σ := by
      have hh := (mul_le_mul_of_nonneg_left (sub_le_sub_right (H.time_strictMono.monotone hil) τ) hq.le).trans hremaining
      have hh' := hh.trans (min_le_left _ _)
      dsimp only [θ, uτ]
      linarith
    have hcurv : ∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D,
        nablaKRm04NormSqIntrinsic S 0 t x ≤ K := by
      simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hRm
    have htipclose : ∀ j ≤ 2, metricDerivNorm j (S.base.metric uτ)
        ((Q.val.metric s₀).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) tip ≤ ε := by
      intro j hj
      rw [hoverlap uτ ⟨huτ.1, le_rfl⟩]
      exact hclose j hj
    have hRic := htip w hD hm hζ _ θ hθ hθΘ (fun _ h => h) (fun _ h => h)
      S hS hSzero hgram (fun t ht x _ => hcurv t ht x) uτ huτ Q s₀ hs₀ tip htipzero htipclose
      θ ⟨huτ.2, le_min hθstep le_rfl⟩
    let Φ := H.backwardSurvivorTerminalFaceMap first i hf ∘ Ξ
    have hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ :=
      isLocalDiffeomorph_comp (H.backwardSurvivorTerminalFaceMap_isLocalDiffeomorph first i hf) hΞ
    have hmet : S.base.metric θ = localPullMetric (scaleMetric q hq (H.event i).terminal.metric) Φ hΦ := by
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      rw [hmetric, show H.time first + θ / q = H.time i.succ by dsimp only [θ]; field_simp; ring,
        hlast _ ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩,
        H.backwardSurvivorTerminalFaceMetric_terminal]
      rw [localPullMetric_inner, scaleMetric_inner, localPullMetric_inner, localPullMetric_inner, scaleMetric_inner]
      rw [mfderiv_comp x
        ((H.backwardSurvivorTerminalFaceMap_isLocalDiffeomorph first i hf).contMDiff.mdifferentiableAt (by simp))
        (hΞ.contMDiff.mdifferentiableAt (by simp))]
      rfl
    have hcross := H.exists_regularCrossing_of_backwardSurvivor_initial_eq first last hle J i hf hil
      Ξ hbirth z endpoint Atrace hanchor
    obtain ⟨F, hFsource, hFcross, _, _, _⟩ := hprotect _ θ hθΘ (fun _ h => h) (fun _ h => h)
      S hS (by intro x v; rw [hSzero]; exact hupper x v) hcurv θ ⟨hθ.le, le_rfl⟩
      H i parameters (records i) (records i).old_eq_retained (hdelta i hni hil)
      Φ hΦ q hq hmet tip hRic z _ hcross
    obtain ⟨xbad, hbad⟩ := hfailed
    exact hbad (F (Φ xbad)) (hFcross (Φ xbad) (hFsource (mem_range_self xbad)))
  have hF := H.backwardSurvivorMap_isSmoothEmbedding first last hle first le_rfl hle
  exact ⟨hF.lift J hsurvive, hF.isSmoothEmbedding_lift hJ (by simp) hsurvive,
    hF.comp_lift hsurvive⟩


theorem exists_uniform_incoming_cap_window_step_of_standard_tip_metric_close
    (Θ Kpast C₀ : ℝ) (C : ℝ≥0) (hΘ : 0 ≤ Θ) (hΘ1 : Θ < 1) (hC₀ : 0 < C₀) :
    ∃ ε δstep : ℝ, 0 < ε ∧ 0 < δstep ∧ ∀ D : ℝ, 32 < D →
      ∃ η : ℝ, 0 < η ∧
      ∀ {E H₀ M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H₀ M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      4 ≤ m → ζ ≤ 1 / 2 →
      (∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
        w.windowMetric.inner x v v ≤ (3 / 2 : ℝ) * StandardCap.metric.inner x.val v v) →
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (next : Fin H.eventCount) (hnext : first ≤ next.castSucc) (hnextlast : next.succ ≤ last)
    (J : standardCapWindow D → (H.stage first).Carrier) (_ : IsSmoothEmbedding ThreeModel ThreeModel ∞ J)
    {τ : ℝ} (G : (H.stage next.castSucc).IncomingSlab (H.time next.castSucc) τ)
    (L : G.TerminalLimitMetric)
    (_ : ∀ t, G.flow.base.metric t = (H.event next).incoming.flow.base.metric t)
    (_ : L.metric =
      ((H.event next).incoming.flow.base.metric τ).restrictOpen G.terminalRegularOpen)
    (_ : τ ∈ Ico (H.time next.castSucc) (H.time next.succ))
    (Ψ : standardCapWindow D → H.backwardSurvivorIncomingDomain first next.castSucc hnext G)
    (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ)
    (_ : ∀ x, H.backwardSurvivorMap first next.castSucc hnext first le_rfl hnext
      (Ψ x).val = J x)
    (gflow₀ : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first next.castSucc hnext G))
    (_ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ next.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow₀ t = (H.backwardSurvivorSlabMetric first next.castSucc hnext j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first next.castSucc hnext G))
    (_ : ∀ t ∈ Icc (H.time next.castSucc) τ,
      gflow₀ t = H.backwardSurvivorIncomingMetric first next.castSucc hnext G L t)
    {r q a₀ : ℝ}
    (hq : 0 < q) (_ : r ≤ C₀ * q) (_ : 1 ≤ a₀ * q)
    (_ : ∀ x (v z : TangentSpace ThreeModel x),
      w.windowMetric.inner x v z = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x z))
    {D₀ : RealTimeInterval} (S₀ : SolutionOn (I := ThreeModel) (M := standardCapWindow D) D₀)
    (_ : ∀ t ∈ Icc 0 (q * (τ - H.time first)), S₀.base.metric t =
      localPullMetric (scaleMetric q hq (gflow₀ (H.time first + t / q))) Ψ hΨ)
    (_ : ∀ t ∈ Icc 0 (q * (τ - H.time first)), ∀ x : standardCapWindow D,
      normSq0S (S₀.base.metric t) x 4 (S₀.base.rm04 t x) ≤ Kpast)
    (_ : ∀ x, (H.event next).incoming.flow.scalar τ (Ψ x).val.val ≤ C₀ * q)
    (_ : ∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        r < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    {s : ℝ} (Gfinal : (H.stage last).IncomingSlab (H.time last) s)
    (Lfinal : Gfinal.TerminalLimitMetric)
    (_ : Gfinal.flow.base.metric (H.time last) = H.initialMetric last)
    (_ : ∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s,
      r < Gfinal.flow.scalar t x →
      |derivWithin (fun v => Gfinal.flow.scalar v x) (Iic t) t| ≤ C * Gfinal.flow.scalar t x ^ 2),
      q * (s - H.time first) ≤ Θ → q * (s - τ) ≤ δstep →
      ∀ (Q : StandardSolution) (s₀ : ℝ), s₀ ∈ Icc 0 Θ →
      ∀ (tip : standardCapWindow D), tip.val = 0 →
      (∀ j ≤ 2, metricDerivNorm j (S₀.base.metric (q * (τ - H.time first)))
        ((Q.val.metric s₀).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) tip ≤ ε) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ η) →
      ∀ (z : standardCapWindow D) (endpoint : Gfinal.terminalRegularOpen)
        (Atrace : BackwardPointTrace H first last hle endpoint.val), Atrace.point first le_rfl hle = J z →
      ∃ (Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle Gfinal),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
        (∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ x).val = J x) ∧
        H.backwardSurvivorIncomingMap first last hle Gfinal (Ξ z) = endpoint ∧
        ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
          (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle Gfinal)),
          (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
            ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
              gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
                (H.backwardSurvivorIncomingDomain first last hle Gfinal)) ∧
          (∀ t ∈ Icc (H.time last) s,
            gflow t = H.backwardSurvivorIncomingMetric first last hle Gfinal Lfinal t) ∧
          ∃ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
              (RealTimeInterval.closed 0 (q * (s - H.time first))
                (by have ht := (H.time_strictMono.monotone hle).trans_lt Gfinal.lt; positivity)),
            IsSolutionOn S ∧ S.base.metric 0 = w.windowMetric ∧
            (∀ t, S.base.metric t =
              localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) ∧
            (∀ (x : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
              ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
                (fun z : ℝ × standardCapWindow D => chartGramMatrix (S.base.metric z.1) x z.2 i j)
                (Icc 0 (q * (s - H.time first)) ×ˢ
                  (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet)) ∧
            (∀ t ∈ Icc 0 (q * (τ - H.time first)), S.base.metric t = S₀.base.metric t) ∧
            ∀ t ∈ Icc 0 (q * (s - H.time first)), ∀ x : standardCapWindow D,
              normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤
                max Kpast ((2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2) := by
  obtain ⟨ε, δsurvive, hε, hδsurvive, hsurvive⟩ :=
    exists_uniform_cap_window_survival_step_of_standard_tip_metric_close Θ Kpast C₀ C hΘ hΘ1 hC₀
  let δstep := min δsurvive (2 * ((C : ℝ) + 1) * C₀)⁻¹
  have hδstep : 0 < δstep := lt_min hδsurvive (by positivity)
  refine ⟨ε, δstep, hε, hδstep, ?_⟩
  intro D hD
  obtain ⟨η, hη, hsurvive⟩ := hsurvive D hD
  refine ⟨η, hη, ?_⟩
  intro E H₀ M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle next hnext hnextlast J hJ τ G L hsource hterminal hτ Ψ hΨ hΨbirth
    gflow₀ hslabs₀ hlast₀ r q a₀ hq hrQ haq hzero D₀ S₀ hmetric₀ hpast hscalar hderiv
    s Gfinal Lfinal hinit hfinal hfulltime hremaining Q s₀ hs₀ tip htipzero hclose
    parameters records hfixed hlower hdelta z endpoint Atrace hanchor
  have hbudget : 2 * C * C₀ * (q * (s - τ)) ≤ 1 := by
    have hd := hremaining.trans (min_le_right _ _)
    have hp : 0 < 2 * ((C : ℝ) + 1) * C₀ := by positivity
    have hh := (le_div_iff₀ hp).mp
      (show q * (s - τ) ≤ 1 / (2 * ((C : ℝ) + 1) * C₀) from by
        simpa only [one_div] using hd)
    have hτs : τ < s := hτ.2.trans_le (H.time_strictMono.monotone hnextlast) |>.trans Gfinal.lt
    have ht : 0 ≤ q * (s - τ) := mul_nonneg hq.le (sub_nonneg.mpr hτs.le)
    nlinarith [mul_nonneg (show 0 ≤ 2 * C₀ by positivity) ht]
  have ha₀ : 0 < a₀ := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h hq.le
    linarith
  have hp := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hlower
  have hpinch (j : Fin H.eventCount) (_ : next.castSucc ≤ j.castSucc) (_ : j.succ ≤ last)
      (t : ℝ) (ht : t ∈ Ico (H.time j.castSucc) (H.time j.succ)) (_ : τ ≤ t)
      (x : (H.stage j.castSucc).Carrier) :
      InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀ x := by
    have ht0 : 0 ≤ t := (H.time_nonneg j.castSucc).trans ht.1
    have hstage : t ∈ H.stageDomain j.castSucc := by
      simpa only [stageDomain, Fin.lastCases_castSucc] using ht
    have hregion : InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) (a₀ + t) x := by
      simpa only [stageMetric, Fin.lastCases_castSucc] using (hp.1 j.castSucc t hstage x).1
    apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ a₀ x).mpr
    exact fixedHamiltonIveyRegion_antitoneOn ha₀ (by linarith : 0 < a₀ + t) (by linarith)
      ((inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ (a₀ + t) x).mp hregion)
  have hfull : q * (H.time last - H.time first) ≤ Θ :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_right Gfinal.lt.le _) hq.le).trans hfulltime
  have hremain : q * (H.time last - τ) ≤ δsurvive :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_right Gfinal.lt.le _) hq.le).trans
      (hremaining.trans (min_le_left _ _))
  obtain ⟨Υ, hΥs, hΥbirth⟩ := hsurvive w hm hζ hupper H first last hle next hnext J hJ
    G L hsource hterminal hτ Ψ hΨ hΨbirth gflow₀ hslabs₀ hlast₀ hq hrQ haq hzero
    S₀ hmetric₀ hpast hscalar hderiv hpinch hfull hremain Q s₀ hs₀ tip htipzero hclose
    parameters records hdelta z endpoint.val Atrace hanchor
  have hΥ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Υ := fun x =>
    Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq rfl
      (hΥs.isImmersion.isImmersionAt x)
  have hscalarΥ (x : standardCapWindow D) :
      (H.event next).incoming.flow.scalar τ
        (H.backwardSurvivorMap first last hle next.castSucc hnext
          (next.castSucc_lt_succ.le.trans hnextlast) (Υ x)) ≤ C₀ * q := by
    have he := H.backwardSurvivorMap_eq_of_initial_eq first next.castSucc last hnext hle
      (Ψ x).val (Υ x) ((hΨbirth x).trans (hΥbirth x).symm) next.castSucc hnext le_rfl
      (next.castSucc_lt_succ.le.trans hnextlast)
    have hp : (Ψ x).val.val = H.backwardSurvivorMap first last hle next.castSucc hnext
        (next.castSucc_lt_succ.le.trans hnextlast) (Υ x) := by
      simpa only [H.backwardSurvivorMap_last] using he
    rw [← hp]
    exact hscalar x
  obtain ⟨Ξ, hΞ, hprojection, hbirth, gflow, hslabs, hlast, S, hS, hSzero,
    hmetric, hgram, hoverlap, hRm⟩ :=
    exists_normalized_backwardSurvivorIncoming_chart_solution_curvature_bound_of_earlier_scalar_bound_at_time
      Gfinal Lfinal hinit Υ hΥ next hnext hnextlast hC₀ hq hrQ haq hτ
      (fun _ j hj hl => hderiv j hj hl _) (fun x => hfinal (Υ x).val) hscalarΥ hbudget
      J hΥbirth w.windowMetric hzero records hfixed hlower G L hsource hterminal
      Ψ hΨ hΨbirth gflow₀ hslabs₀ hlast₀ S₀ hmetric₀ hpast
  have hΞs : IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen ThreeModel ThreeModel
      (H.backwardSurvivorIncomingDomain first last hle Gfinal) Ξ
      (by
        have he : Subtype.val ∘ Ξ = Υ := funext hprojection
        rw [he]
        exact hΥs)
  have hpoint : H.backwardSurvivorIncomingMap first last hle Gfinal (Ξ z) = endpoint :=
    H.backwardSurvivorIncomingMap_eq_of_initial_point_eq first last hle Gfinal J Ξ hbirth
      endpoint Atrace z hanchor.symm
  exact ⟨Ξ, hΞs, hbirth, hpoint, hΞ, gflow, hslabs, hlast, S, hS, hSzero,
    hmetric, hgram, hoverlap, hRm⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
