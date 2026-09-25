import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalBackwardFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarBall

noncomputable section
open Set Function DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
universe u

theorem exists_uniform_backward_flow_of_canonicalCutoffRecords
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Dbig c ρ Qbar : ℝ) (hDbig : StandardCap.transitionEnd < Dbig)
    (hc : 0 < c) (hρ : 0 < ρ) (hQbar : 0 < Qbar) :
    ∃ (Phi : ℝ → ℝ) (ε₀ δ₀ : ℝ), Perelman.AdmissiblePinchingFunction Phi ∧
      0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ p₀ : CutoffParameters, p₀.modelRadius = Dbig → p₀.recenterConstant ≤ c →
        2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ε₀ →
      ∀ H₀ : RetainedCoreHistory P, InitialIdentification P g H₀.toHistory →
      H₀.hasCanonicalCutoffRecords p₀ δ₀ ρ →
      let H := H₀.toHistory;
      ∀ (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (K : Set G.terminalRegularOpen) (q Q θ : ℝ) (C : ℝ≥0),
      0 < q → q ≤ Q → Q ≤ Qbar → 0 < θ → θ ≤ 1 / 4 → 6 * C * θ ≤ 1 →
      H.time first ≤ s - θ / Q →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        s - θ / Q < H.time j.succ) →
      (∀ x ∈ K, metricScalarAt L.metric x ≤ (3 / 2 : ℝ) * Q) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q < (H.event j).incoming.flow.scalar t y →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t y ^ 2) →
      (∀ x ∈ K, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t x.val →
        |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤ C * G.flow.scalar t x.val ^ 2) →
      range (H.backwardSurvivorIncomingFootprintMap first last hle G K) = interior K ∧
      ∃ (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.backwardSurvivorIncomingFootprint first last hle G K))
        (hcs : s - θ / Q ≤ s),
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
          ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
            gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
              (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
                (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
        (∀ t ∈ Icc (H.time last) s,
          gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
        gflow s = localPullMetric L.metric
          (H.backwardSurvivorIncomingFootprintMap first last hle G K)
          (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
        IsSolutionOn ({ base := { metric := gflow } } :
          SolutionOn (I := ThreeModel) (M := H.backwardSurvivorIncomingFootprint first last hle G K)
            (RealTimeInterval.closed (s - θ / Q) s hcs)) ∧
        ∀ t ∈ Icc (s - θ / Q) s, ∀ z : H.backwardSurvivorIncomingFootprint first last hle G K,
          normSq0S (gflow t) z 4 (metricRm04At (gflow t) z) ≤
            (4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0)) ^ 2 := by
  obtain ⟨δ₀, hδ₀, hflow⟩ := ObservedHistory.exists_uniform_backward_flow_of_terminal_scalar_upper_bound
    c ρ Qbar hc hρ hQbar
  obtain ⟨ε₀, hε₀, hcap⟩ := exists_presented_cap_scalar_lower_bound_of_canonical_window Dbig hDbig
  obtain ⟨Phi, hPhi, hpinch⟩ := Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P g
  refine ⟨Phi, ε₀, δ₀, hPhi, hε₀, hδ₀, ?_⟩
  intro p₀ hpD hpc hpm hpε H₀ hident hInv
  obtain ⟨p, _, hpmodel, hporder, hpaccuracy, hprecenter, records, hcanonical, hδ, hrad⟩ := hInv
  intro H first last hle s G L hinit K q Q θ C hq hqQ hQQbar hθpos hθ hbudget hroom
    hcrossTime hscalar hderiv hfinal
  apply hflow H first last hle s G L hinit K q Q θ C hq hqQ hQQbar hθ hbudget
    hcrossTime hscalar hderiv hfinal p records (hprecenter.trans_le hpc)
    (fun j _ _ => hδ j) (fun j _ _ => hrad j)
  · intro j _ _ b z
    have hh := hcap (H.event j) (fixed := p.fixed) (m := p.modelOrder) (ε := p.modelAccuracy)
    rw [← hpD, ← hpmodel] at hh
    exact hh (hpaccuracy.trans_le hpε) (by omega) ((records j).static b) (hcanonical j b) z
  · exact hroom
  · exact hθpos
  · exact hPhi
  · intro j _ _
    exact hpinch H hident p records j.castSucc (H.time j.succ) (H.event j).incoming (H.event_initial j)
  · exact hpinch H hident p records last s G hinit

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end

noncomputable section
open Set Function DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
universe u

theorem exists_uniform_backward_ball_flow_of_canonicalCutoffRecords
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Dbig c ρ Qbar : ℝ) (hDbig : StandardCap.transitionEnd < Dbig)
    (hc : 0 < c) (hρ : 0 < ρ) (hQbar : 0 < Qbar) :
    ∃ (Phi : ℝ → ℝ) (ε₀ δ₀ : ℝ), Perelman.AdmissiblePinchingFunction Phi ∧
      0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ p₀ : CutoffParameters, p₀.modelRadius = Dbig → p₀.recenterConstant ≤ c →
        2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ε₀ →
      ∀ H₀ : RetainedCoreHistory P, InitialIdentification P g H₀.toHistory →
      H₀.hasCanonicalCutoffRecords p₀ δ₀ ρ →
      let H := H₀.toHistory;
      ∀ (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (x : G.terminalRegularOpen) (q Q θ : ℝ) (C Cgrad : ℝ≥0),
      0 < q → q ≤ Q → Q ≤ Qbar → 0 < θ → θ ≤ 1 / 4 → 6 * C * θ ≤ 1 →
      H.time first ≤ s - θ / (4 * Q) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        s - θ / (4 * Q) < H.time j.succ) →
      metricScalarAt L.metric x ≤ Q →
      (∀ y : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y →
        ∀ v : TangentSpace ThreeModel y,
          |scalarDifferential G.flow t y v| ≤ Cgrad * G.flow.scalar t y *
            Real.sqrt (G.flow.scalar t y) * Real.sqrt ((G.flow.base.metric t).inner y v v)) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q < (H.event j).incoming.flow.scalar t y →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t y ^ 2) →
      (∀ y : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y →
        |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2) →
      let K := riemannianClosedBallOf L.metric x
        (Perelman.CanonicalNeighborhood.localPropagationRadius Cgrad / (2 * Real.sqrt (2 * Q)));
      IsCompact K ∧
      range (H.backwardSurvivorIncomingFootprintMap first last hle G K) = interior K ∧
      ∃ (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.backwardSurvivorIncomingFootprint first last hle G K))
        (hcs : s - θ / (4 * Q) ≤ s),
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
          ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
            gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
              (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
                (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
        (∀ t ∈ Icc (H.time last) s,
          gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
        gflow s = localPullMetric L.metric
          (H.backwardSurvivorIncomingFootprintMap first last hle G K)
          (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
        IsSolutionOn ({ base := { metric := gflow } } :
          SolutionOn (I := ThreeModel) (M := H.backwardSurvivorIncomingFootprint first last hle G K)
            (RealTimeInterval.closed (s - θ / (4 * Q)) s hcs)) ∧
        ∀ t ∈ Icc (s - θ / (4 * Q)) s, ∀ z : H.backwardSurvivorIncomingFootprint first last hle G K,
          normSq0S (gflow t) z 4 (metricRm04At (gflow t) z) ≤
            (4 * Real.sqrt 3 * (4 * Q + Phi (16 * Q) + Phi 0)) ^ 2 := by
  obtain ⟨Phi, ε₀, δ₀, hPhi, hε₀, hδ₀, hflow⟩ :=
    exists_uniform_backward_flow_of_canonicalCutoffRecords P g Dbig c ρ (4 * Qbar)
      hDbig hc hρ (by positivity)
  refine ⟨Phi, ε₀, δ₀, hPhi, hε₀, hδ₀, ?_⟩
  intro p₀ hpD hpc hpm hpε H₀ hident hInv H first last hle s G L hinit
    x q Q θ C Cgrad hq hqQ hQQbar hθpos hθ hbudget hroom hcrossTime hx hgradient hderiv hfinal K
  have hQ : 0 < Q := hq.trans_le hqQ
  have hcompact : IsCompact K :=
    L.isCompact_small_ball_of_scalar_derivative_bounds Cgrad C hQ hqQ hgradient hfinal x hx
  refine ⟨hcompact, ?_⟩
  have hscalar : ∀ y ∈ K, metricScalarAt L.metric y ≤ (3 / 2 : ℝ) * (4 * Q) := by
    intro y hy
    have hh := L.scalar_le_on_small_ball_of_gradient_bound Cgrad hQ hqQ hgradient x hx y hy
    linarith
  have hh := hflow p₀ hpD hpc hpm hpε H₀ hident hInv first last hle s G L hinit K
    q (4 * Q) θ C hq (by linarith) (by linarith) hθpos hθ hbudget hroom hcrossTime
    hscalar hderiv (fun y _ => hfinal y.val)
  simpa only [show (4 : ℝ) * (4 * Q) = 16 * Q by ring] using hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end

noncomputable section
open Set Function DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
universe u

private theorem exists_stage_covering_time_before
    (H : ObservedHistory.{u}) (last : Fin (H.eventCount + 1)) {t : ℝ} (ht : 0 ≤ t) :
    ∃ first : Fin (H.eventCount + 1), first ≤ last ∧ H.time first ≤ t ∧
      ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → t < H.time j.succ := by
  by_cases hlast : H.time last ≤ t
  · refine ⟨last,le_rfl,hlast,?_⟩
    intro j hj hnext
    exact False.elim ((not_le_of_gt j.castSucc_lt_succ) (hnext.trans hj))
  · let tH : Icc (0 : ℝ) H.horizon := ⟨t,ht,(not_le.mp hlast).le.trans (H.time_le_horizon_at last)⟩
    have hle : H.activeStage tH ≤ last := by
      apply H.time_strictMono.le_iff_le.mp
      exact (H.activeStage_time_le tH).trans (not_le.mp hlast).le
    refine ⟨H.activeStage tH,hle,H.activeStage_time_le tH,?_⟩
    intro j hj hnext
    have hn : (H.activeStage tH).val < H.eventCount := lt_of_le_of_lt hj j.isLt
    exact (H.activeStage_before_next tH hn).trans_le
      (H.time_strictMono.monotone (show (⟨(H.activeStage tH).val + 1,by omega⟩ : Fin (H.eventCount+1)) ≤ j.succ from
        Nat.succ_le_succ hj))


theorem exists_uniform_backward_ball_flow_of_bounded_terminal_scalar
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Dbig c ρ q Qbar tau : ℝ) (C Cgrad : ℝ≥0)
    (hDbig : StandardCap.transitionEnd < Dbig)
    (hc : 0 < c) (hρ : 0 < ρ) (hq : 0 < q) (hqQ : q ≤ Qbar) (htau : 0 < tau) :
    ∃ (Phi : ℝ → ℝ) (ε₀ δ₀ Δ r : ℝ), Perelman.AdmissiblePinchingFunction Phi ∧
      0 < ε₀ ∧ 0 < δ₀ ∧ 0 < Δ ∧ Δ ≤ tau ∧ 0 < r ∧
      ∀ p₀ : CutoffParameters, p₀.modelRadius = Dbig → p₀.recenterConstant ≤ c →
        2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ε₀ →
      ∀ H₀ : RetainedCoreHistory P, InitialIdentification P g H₀.toHistory →
      H₀.hasCanonicalCutoffRecords p₀ δ₀ ρ →
      let H := H₀.toHistory;
      ∀ (last : Fin (H.eventCount + 1))
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last → tau ≤ s →
      ∀ x : G.terminalRegularOpen, metricScalarAt L.metric x ≤ Qbar →
      (∀ y : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y →
        ∀ v : TangentSpace ThreeModel y,
          |scalarDifferential G.flow t y v| ≤ Cgrad * G.flow.scalar t y *
            Real.sqrt (G.flow.scalar t y) * Real.sqrt ((G.flow.base.metric t).inner y v v)) →
      (∀ j : Fin H.eventCount, j.succ ≤ last →
        ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q < (H.event j).incoming.flow.scalar t y →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t y ^ 2) →
      (∀ y : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y →
        |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2) →
      ∃ (first : Fin (H.eventCount + 1)) (hle : first ≤ last),
      let K := riemannianClosedBallOf L.metric x r;
      IsCompact K ∧
      range (H.backwardSurvivorIncomingFootprintMap first last hle G K) = interior K ∧
      ∃ (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.backwardSurvivorIncomingFootprint first last hle G K))
        (hcs : s - Δ ≤ s),
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
          ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
            gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
              (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
                (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
        (∀ t ∈ Icc (H.time last) s,
          gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
        gflow s = localPullMetric L.metric
          (H.backwardSurvivorIncomingFootprintMap first last hle G K)
          (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
        IsSolutionOn ({ base := { metric := gflow } } :
          SolutionOn (I := ThreeModel) (M := H.backwardSurvivorIncomingFootprint first last hle G K)
            (RealTimeInterval.closed (s - Δ) s hcs)) ∧
        ∀ t ∈ Icc (s - Δ) s, ∀ z : H.backwardSurvivorIncomingFootprint first last hle G K,
          normSq0S (gflow t) z 4 (metricRm04At (gflow t) z) ≤
            (4 * Real.sqrt 3 * (4 * Qbar + Phi (16 * Qbar) + Phi 0)) ^ 2 := by
  have hQbar : 0 < Qbar := hq.trans_le hqQ
  obtain ⟨Phi, ε₀, δ₀, hPhi, hε₀, hδ₀, hflow⟩ :=
    exists_uniform_backward_ball_flow_of_canonicalCutoffRecords P g Dbig c ρ Qbar
      hDbig hc hρ hQbar
  let θ := min (1 / 4 : ℝ) (min (1 / (6 * ((C : ℝ) + 1))) (4 * Qbar * tau))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθquarter : θ ≤ 1 / 4 := min_le_left _ _
  have hθC : θ ≤ 1 / (6 * ((C : ℝ) + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hθtau : θ ≤ 4 * Qbar * tau := (min_le_right _ _).trans (min_le_right _ _)
  have hbudget : 6 * (C : ℝ) * θ ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 6 * ((C : ℝ) + 1))).mp hθC
    nlinarith [C.coe_nonneg]
  let Δ := θ / (4 * Qbar)
  have hΔ : 0 < Δ := div_pos hθ (by positivity)
  have hΔtau : Δ ≤ tau := (div_le_iff₀ (by positivity : 0 < 4 * Qbar)).mpr (by nlinarith)
  let r := localPropagationRadius Cgrad / (2 * Real.sqrt (2 * Qbar))
  have hr : 0 < r := div_pos (localPropagationRadius_pos Cgrad.coe_nonneg) (by positivity)
  refine ⟨Phi, ε₀, δ₀, Δ, r, hPhi, hε₀, hδ₀, hΔ, hΔtau, hr, ?_⟩
  intro p₀ hpD hpc hpm hpε H₀ hident hInv H last s G L hinit hs x hx hgradient hderiv hfinal
  obtain ⟨first, hle, hroom, hcross⟩ := exists_stage_covering_time_before H last
    (show 0 ≤ s - Δ by linarith)
  refine ⟨first, hle, ?_⟩
  exact hflow p₀ hpD hpc hpm hpε H₀ hident hInv first last hle s G L hinit x
    q Qbar θ C Cgrad hq hqQ le_rfl hθ hθquarter hbudget hroom hcross hx hgradient
    (fun j _ hl => hderiv j hl) hfinal

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end
