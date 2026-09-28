import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.FineCutNeckSupplyStrong
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalHornSliceSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalHornBlowupSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPinchingOfCutoffRecords

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem fineCutNeckSupplyStrong_holds (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    FineCutNeckSupplyStrong P₀ g₀ := by
  obtain ⟨eta, etaC, heta, hetaC, hC1⟩ :=
    RetainedCoreHistory.exists_slices_of_deep_horn_presentation_sequence.{u}
  obtain ⟨epsW, hepsW, hC2⟩ := RetainedCoreHistory.exists_tolerance_false_of_deep_horn_slices.{u}
  obtain ⟨phi, hphi, hpinchOf⟩ :=
    exists_admissiblePinchingFunction_of_hasCanonicalCutoffRecords P₀ g₀
  obtain ⟨a, ha, hsingTime⟩ :=
    exists_pos_le_terminal_time_of_hasCanonicalCutoffRecords P₀ g₀
  refine ⟨1 / 30000, by norm_num, by norm_num, eta,
    min etaC (min epsW crossingNeckAccuracy.{u}), heta,
    lt_min hetaC (lt_min hepsW crossingNeckAccuracy_pos), ?_⟩
  intro κ C1s C2s qcan a₀ Ctime Cgrad ε hκ _ _ hq _ hε hεcone εc hεc hεc12
  by_contra hcon
  have hbad : ∀ n : ℕ, ∃ (p₀ : CutoffParameters) (δb ρb : ℝ) (H : RetainedCoreHistory.{u}),
      ∃ (_ : InitialIdentification P₀ g₀ H.toHistory)
        (hend : H.time (Fin.last H.eventCount) = H.horizon),
        H.hasCanonicalCutoffRecords p₀ δb ρb ∧
        H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) ∧
        H.EventSlabsStronglyCanonical ε (1 / 30000) C1s C2s qcan (Fin.last H.eventCount) ∧
        H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) ∧
        ∃ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
            (H.time (Fin.last H.eventCount)) s) (L : G.TerminalLimitMetric)
          (hsing : G.SingularEndpoint) (parameters : CutoffParameters)
          (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          G.DerivativeBoundBefore Ctime qcan s ∧ G.GradientBoundBefore Cgrad qcan s ∧
          H.StronglyCanonicalBefore (Fin.last H.eventCount) G ε (1 / 30000) C1s C2s qcan s ∧
          (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
            H.TerminalNoncollapsedBefore hend G hG κ ε t₀) ∧
          ∃ (εP Λ : ℝ) (P : TerminalCorePresentation
              { stage := H.stage (Fin.last H.eventCount)
                startTime := H.time (Fin.last H.eventCount)
                endTime := s
                startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
                startTime_lt_endTime := G.lt
                slab := G
                terminal := L
                singular := hsing
                parameters := parameters } εP Λ),
            εP ≤ eta ∧
            ∃ (c : ConnectedComponents G.terminalRegularOpen) (e : P.hornIndex c)
              (x : G.terminalRegularOpen),
              x ∈ interior (range fun p : HalfNeckCylinder => P.horn c e p.1) ∧
              ((n : ℝ) + 1) * max (Λ * (P.coreRadius ^ 2)⁻¹) (max qcan 1) ≤
                metricScalarAt L.metric x ∧
              ¬ ∃ N : NormalizedNeck L.metric εc (⌊εc⁻¹⌋₊ + 1), N.center = x := by
    intro n
    by_contra hn
    apply hcon
    refine ⟨(n : ℝ) + 1, by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)], ?_⟩
    intro p₀ δb ρb H hinit hend hrec _ hderiv _ hclass hnc s G L hsing parameters hG hderG hgradG
      hcanG hncG εP Λ P hεP Qc hQc c e x hx hQx
    by_contra hnoN
    exact hn ⟨p₀, δb, ρb, H, hinit, hend, hrec, hderiv, hclass, hnc, s, G, L, hsing, parameters,
      hG, hderG, hgradG, hcanG, hncG, εP, Λ, P, hεP, c, e, x, hx, hQc.trans hQx,
      fun ⟨N, hN⟩ => hnoN ⟨εc, ⌊εc⁻¹⌋₊ + 1, N, hN, le_rfl, le_rfl⟩⟩
  choose p₀ δb ρb H hinit hend hrec hderiv hclass hnc s G L hsing parameters hG hderG hgradG hcanG
    hncG εP Λ P hεP c e x hxint hRl hnoN using hbad
  have hpinch : ∀ n, (H n).EventSlabsPinched phi := fun n =>
    (hpinchOf (H n) (hinit n) (hrec n)).1
  have hpinchG : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi := fun n =>
    (hpinchOf (H n) (hinit n) (hrec n)).2 _ (G n) (hG n)
  have hs : ∀ n, a ≤ s n := fun n => hsingTime (H n) (hinit n) (hrec n) _ (G n) (hG n) (hsing n)
  have hεC : ε ≤ etaC := hεcone.trans (min_le_left _ _)
  have hεW : ε ≤ epsW := hεcone.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεcross : ε ≤ crossingNeckAccuracy.{u} :=
    hεcone.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨τ, Q, S, V, W, hτmem, hQ1, hno, hcl, hgap, hV, hW, hVW, hS, hpts, hup, hwit⟩ :=
    hC1 hκ hq hε hεC hεc hεc12 ha hphi H hend hderiv hpinch G L hsing parameters hG hs hderG
      hgradG hcanG hpinchG hncG P hεP c e x hxint hRl hnoN
  have heps : 0 < min (εc / (1 + εc)) (1 / 12) := lt_min (div_pos hεc (by linarith)) (by norm_num)
  have heps11 : min (εc / (1 + εc)) (1 / 12) < 1 / 11 :=
    (min_le_right _ _).trans_lt (by norm_num)
  have hRl1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ metricScalarAt (L n).metric (x n) := fun n =>
    (le_mul_of_one_le_right (by positivity)
      ((le_max_right _ _).trans (le_max_right _ _))).trans (hRl n)
  exact hC2 hκ hq hε hεW hεcross le_rfl ha hphi H hend hderiv hpinch hclass hnc G L hG hs hderG
    hgradG hcanG hpinchG hncG x heps heps11 hRl1 τ Q S V W hτmem hQ1 hno hcl hgap hV hW hVW hS
    hpts hup hwit

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
