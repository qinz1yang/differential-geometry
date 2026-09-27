import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalBackwardBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Metric.Restriction.Ball
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.BackwardPatch

noncomputable section
open Set Function DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
universe u

private theorem test_radius_bounds {r Δ B : ℝ} (hr : 0 < r) (hΔ : 0 < Δ) (hB : 0 ≤ B) :
    let rt := min (r / 8) (min (Real.sqrt Δ / 4) ((Real.sqrt (B + 1))⁻¹ / 4))
    0 < rt ∧ rt < r ∧ rt ^ 2 ≤ Δ ∧ rt ^ 4 * B ^ 2 ≤ 1 := by
  dsimp only
  let rt := min (r / 8) (min (Real.sqrt Δ / 4) ((Real.sqrt (B + 1))⁻¹ / 4))
  have hrt : 0 < rt := by dsimp [rt]; positivity
  have hrr : rt ≤ r / 8 := min_le_left _ _
  have htΔ : rt ≤ Real.sqrt Δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have htB : rt ≤ (Real.sqrt (B + 1))⁻¹ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hsqΔ : rt ^ 2 ≤ Δ := by
    have hsq := Real.sq_sqrt hΔ.le
    nlinarith [Real.sqrt_nonneg Δ]
  have hroot : 0 < Real.sqrt (B + 1) := Real.sqrt_pos.mpr (by linarith)
  have hprod : rt * Real.sqrt (B + 1) ≤ 1 / 4 := by
    have hm := mul_le_mul_of_nonneg_right htB hroot.le
    have heq : ((Real.sqrt (B + 1))⁻¹ / 4) * Real.sqrt (B + 1) = (1 / 4 : ℝ) := by
      field_simp
    rwa [heq] at hm
  have hsq : rt ^ 2 * B ≤ 1 := by
    have hb := Real.sq_sqrt (by linarith : 0 ≤ B + 1)
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ rt * Real.sqrt (B + 1)) hprod 2
    nlinarith [sq_nonneg rt]
  have hsq2 := pow_le_pow_left₀ (by positivity : 0 ≤ rt ^ 2 * B) hsq 2
  exact ⟨hrt,by linarith,hsqΔ,by nlinarith only [hsq2]⟩

theorem exists_uniform_ordinary_backward_ball_flow
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Dbig c ρ q Qbar tau : ℝ) (C Cgrad : ℝ≥0)
    (hDbig : StandardCap.transitionEnd < Dbig)
    (hc : 0 < c) (hρ : 0 < ρ) (hq : 0 < q) (hqQ : q ≤ Qbar) (htau : 0 < tau) :
    ∃ (Phi : ℝ → ℝ) (ε₀ δ₀ Δ r rtest : ℝ), Perelman.AdmissiblePinchingFunction Phi ∧
      0 < ε₀ ∧ 0 < δ₀ ∧ 0 < Δ ∧ Δ ≤ tau ∧ 0 < r ∧ 0 < rtest ∧ rtest < r ∧
      rtest ^ 2 ≤ Δ ∧
      rtest ^ 4 * (4 * Real.sqrt 3 * (4 * Qbar + Phi (16 * Qbar) + Phi 0)) ^ 2 ≤ 1 ∧
      ∀ p₀ : CutoffParameters, p₀.modelRadius = Dbig → p₀.recenterConstant ≤ c →
        2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ε₀ →
      ∀ H₀ : RetainedCoreHistory P, InitialIdentification P g H₀.toHistory →
      H₀.hasCanonicalCutoffRecords p₀ δ₀ ρ →
      let H := H₀.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (ht : H.time (H.activeStage t) < (t : ℝ)), tau ≤ t →
      ∀ x : (H.stageAt t).Carrier, metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ Qbar →
      (∀ y : (H.stageAt t).Carrier, ∀ v ∈ Ioo (H.time (H.activeStage t)) t,
        (t : ℝ) - Δ ≤ v → q < (H.closedPrefixAt t ht).flow.scalar v y →
        ∀ w : TangentSpace ThreeModel y,
          |scalarDifferential (H.closedPrefixAt t ht).flow v y w| ≤
            Cgrad * (H.closedPrefixAt t ht).flow.scalar v y *
              Real.sqrt ((H.closedPrefixAt t ht).flow.scalar v y) *
                Real.sqrt (((H.closedPrefixAt t ht).flow.base.metric v).inner y w w)) →
      (∀ j : Fin H.eventCount, j.succ ≤ H.activeStage t →
        ∀ y : (H.stage j.castSucc).Carrier, ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          (t : ℝ) - Δ ≤ v → q < (H.event j).incoming.flow.scalar v y →
          |derivWithin (fun w => (H.event j).incoming.flow.scalar w y) (Iic v) v| ≤
            C * (H.event j).incoming.flow.scalar v y ^ 2) →
      (∀ y : (H.stageAt t).Carrier, ∀ v ∈ Ioo (H.time (H.activeStage t)) t,
        (t : ℝ) - Δ ≤ v → q < metricScalarAt (H.stageMetric (H.activeStage t) v) y →
        |derivWithin (fun w => metricScalarAt (H.stageMetric (H.activeStage t) w) y) (Iic v) v| ≤
          C * metricScalarAt (H.stageMetric (H.activeStage t) v) y ^ 2) →
      let S := H.closedPrefixAt t ht;
      let G := S.restrictIncoming le_rfl S.lt le_rfl;
      let L := S.endpointTerminalLimitMetric (H.stageAt t);
      ∃ (xL : G.terminalRegularOpen), xL.val = x ∧
      ∃ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t),
      H.time first ≤ (t : ℝ) - Δ ∧
      let K := riemannianClosedBallOf L.metric xL r;
      IsCompact K ∧
      range (H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K) = interior K ∧
      ∃ (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K))
        (hcs : (t : ℝ) - Δ ≤ t),
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
          ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
            gflow v = ((H.backwardSurvivorSlabMetric first (H.activeStage t) hle j hf hl v).restrictOpen
              (H.backwardSurvivorIncomingDomain first (H.activeStage t) hle G)).restrictOpen
                (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K)) ∧
        (∀ v ∈ Icc (H.time (H.activeStage t)) t,
          gflow v = (H.backwardSurvivorIncomingMetric first (H.activeStage t) hle G L v).restrictOpen
            (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K)) ∧
        gflow t = localPullMetric L.metric
          (H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K)
          (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first (H.activeStage t) hle G K) ∧
        IsSolutionOn ({ base := { metric := gflow } } :
          SolutionOn (I := ThreeModel) (M := H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K)
            (RealTimeInterval.closed ((t : ℝ) - Δ) t hcs)) ∧
        (∀ v ∈ Icc ((t : ℝ) - Δ) t, ∀ z : H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K,
          normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤
            (4 * Real.sqrt 3 * (4 * Qbar + Phi (16 * Qbar) + Phi 0)) ^ 2) ∧
        let f : H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K →
            (H.stageAt t).Carrier := fun z =>
          (H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K z).val;
        ∃ hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f,
          Function.Injective f ∧ gflow t = localPullMetric (H.stageMetric (H.activeStage t) t) f hf ∧
          riemannianBallOf (H.stageMetric (H.activeStage t) t) x rtest ⊆ range f ∧
          H.isParabolicallyRmControlledBall t x rtest := by
  obtain ⟨Phi, ε₀, δ₀, Δ, r, hPhi, hε₀, hδ₀, hΔ, hΔtau, hr, hflow⟩ :=
    exists_uniform_backward_ball_flow_with_stage_bounds P g Dbig c ρ q Qbar tau C Cgrad
      hDbig hc hρ hq hqQ htau
  let B := 4 * Real.sqrt 3 * (4 * Qbar + Phi (16 * Qbar) + Phi 0)
  have hB : 0 ≤ B := by have := hq.trans_le hqQ; have := hPhi.pos (16 * Qbar); have := hPhi.pos 0; dsimp [B]; positivity
  let rtest := min (r / 8) (min (Real.sqrt Δ / 4) ((Real.sqrt (B + 1))⁻¹ / 4))
  obtain ⟨hrt,hrr,htΔ,htB⟩ := test_radius_bounds hr hΔ hB
  refine ⟨Phi,ε₀,δ₀,Δ,r,rtest,hPhi,hε₀,hδ₀,hΔ,hΔtau,hr,hrt,hrr,htΔ,htB,?_⟩
  intro p₀ hpD hpc hpm hpε H₀ hident hInv H t ht htau x hx hgrad hderiv hfinal S G L
  have hregular : G.terminalRegularRegion = univ := S.terminalRegularRegion_eq_univ (H.stageAt t)
  have hclosed : IsClosed (G.terminalRegularOpen : Set (H.stageAt t).Carrier) := by
    change IsClosed G.terminalRegularRegion
    rw [hregular]
    exact isClosed_univ
  let xL : G.terminalRegularOpen := ⟨x, by change x ∈ G.terminalRegularRegion; rw [hregular]; trivial⟩
  have hGmetric (v : ℝ) : G.flow.base.metric v = H.stageMetric (H.activeStage t) v :=
    H.closedPrefixAt_metric t ht v
  have hGscalar (v : ℝ) (y : (H.stageAt t).Carrier) : G.flow.scalar v y = metricScalarAt (H.stageMetric (H.activeStage t) v) y := by
    change metricScalarAt (G.flow.base.metric v) y = _
    rw [hGmetric]
  have hLmetric : L.metric = (H.stageMetric (H.activeStage t) t).restrictOpen G.terminalRegularOpen := by
    change (S.flow.base.metric t).restrictOpen _ = _
    rw [H.closedPrefixAt_metric]
  have hxL : metricScalarAt L.metric xL ≤ Qbar := by
    rw [hLmetric, metricScalarAt_restrictOpen]
    exact hx
  have hgradG : ∀ y : (H.stageAt t).Carrier, ∀ v ∈ Ioo (H.time (H.activeStage t)) t,
      (t : ℝ) - Δ ≤ v → q < G.flow.scalar v y → ∀ w : TangentSpace ThreeModel y,
      |scalarDifferential G.flow v y w| ≤ Cgrad * G.flow.scalar v y * Real.sqrt (G.flow.scalar v y) *
        Real.sqrt ((G.flow.base.metric v).inner y w w) := hgrad
  have hfinalG : ∀ y : (H.stageAt t).Carrier, ∀ v ∈ Ioo (H.time (H.activeStage t)) t,
      (t : ℝ) - Δ ≤ v → q < G.flow.scalar v y →
      |derivWithin (fun w => G.flow.scalar w y) (Iic v) v| ≤ C * G.flow.scalar v y ^ 2 := by
    intro y v hv hvΔ hy
    simpa only [hGscalar] using hfinal y v hv hvΔ (by rwa [hGscalar] at hy)
  obtain ⟨first,hle,hroom,hcross,hK,hrange,gflow,hcs,hslabs,hlast,hterminal,hsol,hcurv⟩ :=
    hflow p₀ hpD hpc hpm hpε H₀ hident hInv (H.activeStage t) t G L
      (H.closedPrefixAt_initial t ht) htau xL hxL hgradG hderiv hfinalG
  let K := riemannianClosedBallOf L.metric xL r
  have hball : riemannianBallOf (H.stageMetric (H.activeStage t) t) x rtest ⊆
      range (fun z : H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K =>
        (H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K z).val) := by
    intro y hy
    have heq := riemannianBallOf_eq_image_restrictOpen_of_isClosed
      (H.stageMetric (H.activeStage t) t) G.terminalRegularOpen hclosed xL rtest
    change y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) xL.val rtest at hy
    rw [heq, ← hLmetric] at hy
    obtain ⟨yL,hyL,rfl⟩ := hy
    have hyint : yL ∈ interior K := by
      apply Geometry.Metric.riemannianBallOf_subset_interior_riemannianClosedBallOf L.metric xL r
      exact (show riemannianEDistOf L.metric xL yL < ENNReal.ofReal rtest from hyL).trans_le
        (ENNReal.ofReal_le_ofReal hrr.le)
    obtain ⟨z,hz⟩ := (hrange ▸ hyint : yL ∈ range (H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K))
    exact ⟨z,congrArg Subtype.val hz⟩
  let F := H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K
  have hF := H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first (H.activeStage t) hle G K
  let f : H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K → (H.stageAt t).Carrier :=
    Subtype.val ∘ F
  have hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val (I := ThreeModel) G.terminalRegularOpen) hF
  have hinj : Function.Injective f :=
    Subtype.val_injective.comp (H.backwardSurvivorIncomingFootprintMap_injective first (H.activeStage t) hle G K)
  have hstageTerminal : gflow t = localPullMetric (H.stageMetric (H.activeStage t) t) f hf := by
    calc
      gflow t = localPullMetric L.metric F hF := hterminal
      _ = localPullMetric ((H.stageMetric (H.activeStage t) t).restrictOpen G.terminalRegularOpen) F hF :=
        congrArg (fun h => localPullMetric h F hF) hLmetric
      _ = _ := by
        rw [← localPullMetric_subtype_val]
        exact localPullMetric_comp _ Subtype.val F _ hF hf
  refine ⟨xL,rfl,first,hle,hroom,hK,hrange,gflow,hcs,hslabs,hlast,hterminal,hsol,hcurv,hf,hinj,hstageTerminal,hball,?_⟩
  exact H.isParabolicallyRmControlledBall_of_closedPrefixAt_incomingFootprint t ht first hle K gflow
    hslabs hlast x rtest Δ (B^2) hrt htΔ hroom hball hcurv htB

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end

noncomputable section
open Set Function DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
universe u

private theorem incoming_footprint_sigmaCompact (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
    (hle : first ≤ last) {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s)
    (K : Set G.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorIncomingFootprint first last hle G K) := by
  let : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorDomain first last hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorIncomingFootprint first last hle G K).isOpen)

theorem exists_uniform_ordinary_backward_patch_volume_and_action
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Dbig c ρ q Qbar tau κ epsTest : ℝ) (C Cgrad : ℝ≥0)
    (hDbig : StandardCap.transitionEnd < Dbig)
    (hc : 0 < c) (hρ : 0 < ρ) (hq : 0 < q) (hqQ : q ≤ Qbar) (htau : 0 < tau) (hκ : 0 < κ) (hepsTest : 0 < epsTest) :
    ∃ (Phi : ℝ → ℝ) (ε₀ δ₀ Δ r rtest rpatch : ℝ), Perelman.AdmissiblePinchingFunction Phi ∧
      0 < ε₀ ∧ 0 < δ₀ ∧ 0 < Δ ∧ Δ ≤ tau ∧ 0 < r ∧ 0 < rtest ∧ rtest < r ∧
      0 < rpatch ∧ rpatch < rtest ∧ rpatch ≤ epsTest ∧ rpatch ^ 2 ≤ Δ ∧
      rtest ^ 2 ≤ Δ ∧
      rtest ^ 4 * (4 * Real.sqrt 3 * (4 * Qbar + Phi (16 * Qbar) + Phi 0)) ^ 2 ≤ 1 ∧
      ∀ p₀ : CutoffParameters, p₀.modelRadius = Dbig → p₀.recenterConstant ≤ c →
        2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ε₀ →
      ∀ H₀ : RetainedCoreHistory P, InitialIdentification P g H₀.toHistory →
      H₀.hasCanonicalCutoffRecords p₀ δ₀ ρ →
      let H := H₀.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (ht : H.time (H.activeStage t) < (t : ℝ)), tau ≤ t →
      ∀ x : (H.stageAt t).Carrier, metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ Qbar →
      (∀ y : (H.stageAt t).Carrier, ∀ v ∈ Ioo (H.time (H.activeStage t)) t,
        (t : ℝ) - Δ ≤ v → q < (H.closedPrefixAt t ht).flow.scalar v y →
        ∀ w : TangentSpace ThreeModel y,
          |scalarDifferential (H.closedPrefixAt t ht).flow v y w| ≤
            Cgrad * (H.closedPrefixAt t ht).flow.scalar v y *
              Real.sqrt ((H.closedPrefixAt t ht).flow.scalar v y) *
                Real.sqrt (((H.closedPrefixAt t ht).flow.base.metric v).inner y w w)) →
      (∀ j : Fin H.eventCount, j.succ ≤ H.activeStage t →
        ∀ y : (H.stage j.castSucc).Carrier, ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          (t : ℝ) - Δ ≤ v → q < (H.event j).incoming.flow.scalar v y →
          |derivWithin (fun w => (H.event j).incoming.flow.scalar w y) (Iic v) v| ≤
            C * (H.event j).incoming.flow.scalar v y ^ 2) →
      (∀ y : (H.stageAt t).Carrier, ∀ v ∈ Ioo (H.time (H.activeStage t)) t,
        (t : ℝ) - Δ ≤ v → q < metricScalarAt (H.stageMetric (H.activeStage t) v) y →
        |derivWithin (fun w => metricScalarAt (H.stageMetric (H.activeStage t) w) y) (Iic v) v| ≤
          C * metricScalarAt (H.stageMetric (H.activeStage t) v) y ^ 2) →
      (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ epsTest → H.isParabolicallyRmControlledBall t x ρ' →
        ENNReal.ofReal κ * ENNReal.ofReal ρ' ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier (H.stageMetric (H.activeStage t) t)
            (riemannianBallOf (H.stageMetric (H.activeStage t) t) x ρ')) →
      let S := H.closedPrefixAt t ht;
      let G := S.restrictIncoming le_rfl S.lt le_rfl;
      let L := S.endpointTerminalLimitMetric (H.stageAt t);
      ∃ (xL : G.terminalRegularOpen), xL.val = x ∧
      ∃ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t),
      H.time first ≤ (t : ℝ) - Δ ∧
      let K := riemannianClosedBallOf L.metric xL r;
      IsCompact K ∧
      range (H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K) = interior K ∧
      ∃ (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K))
        (hcs : (t : ℝ) - Δ ≤ t),
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
          ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
            gflow v = ((H.backwardSurvivorSlabMetric first (H.activeStage t) hle j hf hl v).restrictOpen
              (H.backwardSurvivorIncomingDomain first (H.activeStage t) hle G)).restrictOpen
                (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K)) ∧
        (∀ v ∈ Icc (H.time (H.activeStage t)) t,
          gflow v = (H.backwardSurvivorIncomingMetric first (H.activeStage t) hle G L v).restrictOpen
            (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K)) ∧
        gflow t = localPullMetric L.metric
          (H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K)
          (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first (H.activeStage t) hle G K) ∧
        IsSolutionOn ({ base := { metric := gflow } } :
          SolutionOn (I := ThreeModel) (M := H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K)
            (RealTimeInterval.closed ((t : ℝ) - Δ) t hcs)) ∧
        (∀ v ∈ Icc ((t : ℝ) - Δ) t, ∀ z : H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K,
          normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤
            (4 * Real.sqrt 3 * (4 * Qbar + Phi (16 * Qbar) + Phi 0)) ^ 2) ∧
        let f : H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K →
            (H.stageAt t).Carrier := fun z =>
          (H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K z).val;
        ∃ hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f,
          Function.Injective f ∧ gflow t = localPullMetric (H.stageMetric (H.activeStage t) t) f hf ∧
          riemannianBallOf (H.stageMetric (H.activeStage t) t) x rtest ⊆ range f ∧
          H.isParabolicallyRmControlledBall t x rtest ∧
          let _ : SigmaCompactSpace (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K) :=
            incoming_footprint_sigmaCompact H first (H.activeStage t) hle G K;
          let Sflow : SolutionOn (I := ThreeModel)
              (M := H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K)
              (RealTimeInterval.closed ((t : ℝ) - Δ) t hcs) := { base := { metric := gflow } };
          let B := 4 * Real.sqrt 3 * (4 * Qbar + Phi (16 * Qbar) + Phi 0);
          ∃ p : H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K,
            f p = x ∧
            let V := riemannianBallOf (gflow t) p rpatch;
            IsOpen V ∧ f '' V = riemannianBallOf (H.stageMetric (H.activeStage t) t) x rpatch ∧
            0 < Real.exp (-27 * B * rpatch ^ 2) * κ ∧
            ENNReal.ofReal (Real.exp (-27 * B * rpatch ^ 2) * κ) * ENNReal.ofReal rpatch ^ 3 ≤
              riemannianVolumeMeasure ThreeModel
                (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K)
                (gflow ((t : ℝ) - rpatch ^ 2)) V ∧
            ∀ T Emax : ℝ, (t : ℝ) ≤ T → T - t + rpatch ^ 2 ≤ Emax → ∀ q' ∈ V,
              ∃ α : ℝ → H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K,
                ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ α ∧
                α (Real.sqrt (T - t)) = p ∧ α (Real.sqrt (T - t + rpatch ^ 2)) = q' ∧
                MapsTo α (Icc (Real.sqrt (T - t)) (Real.sqrt (T - t + rpatch ^ 2)))
                  (riemannianClosedBallOf (gflow t) p rpatch) ∧
                Perelman.lRegularizedAction Sflow T α (Real.sqrt (T - t))
                  (Real.sqrt (T - t + rpatch ^ 2)) ≤
                    (Real.exp (18 * B * Δ) + 18 * B * rpatch ^ 2) * Real.sqrt Emax := by
  obtain ⟨Phi,ε₀,δ₀,Δ,r,rtest,hPhi,hε₀,hδ₀,hΔ,hΔtau,hr,hrt,hrr,htΔ,htB,hflow⟩ :=
    exists_uniform_ordinary_backward_ball_flow P g Dbig c ρ q Qbar tau C Cgrad
      hDbig hc hρ hq hqQ htau
  let rpatch := min (rtest / 2) epsTest
  have hrpatch : 0 < rpatch := lt_min (half_pos hrt) hepsTest
  have hrpt : rpatch < rtest := (min_le_left _ _).trans_lt (half_lt_self hrt)
  have hrpeps : rpatch ≤ epsTest := min_le_right _ _
  have hrpΔ : rpatch ^ 2 ≤ Δ := (pow_le_pow_left₀ hrpatch.le hrpt.le 2).trans htΔ
  refine ⟨Phi,ε₀,δ₀,Δ,r,rtest,rpatch,hPhi,hε₀,hδ₀,hΔ,hΔtau,hr,hrt,hrr,
    hrpatch,hrpt,hrpeps,hrpΔ,htΔ,htB,?_⟩
  intro p₀ hpD hpc hpm hpε H₀ hident hInv H t ht htau x hx hgrad hderiv hfinal hNC S G L
  obtain ⟨xL,hxL,first,hle,hroom,hK,hrange,gflow,hcs,hslabs,hlast,hterminal,hsol,hcurv,
    hf,hinj,hstageTerminal,hball,htest⟩ :=
    hflow p₀ hpD hpc hpm hpε H₀ hident hInv t ht htau x hx hgrad hderiv hfinal
  let K := riemannianClosedBallOf L.metric xL r
  let F := H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K
  let f : H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K → (H.stageAt t).Carrier :=
    fun z => (F z).val
  let Sflow : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K)
      (RealTimeInterval.closed ((t : ℝ) - Δ) t hcs) := { base := { metric := gflow } }
  let B := 4 * Real.sqrt 3 * (4 * Qbar + Phi (16 * Qbar) + Phi 0)
  have hB : 0 ≤ B := by
    have := hq.trans_le hqQ
    have := hPhi.pos (16 * Qbar)
    have := hPhi.pos 0
    dsimp [B]
    positivity
  let _ : SigmaCompactSpace (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K) :=
    incoming_footprint_sigmaCompact H first (H.activeStage t) hle G K
  have hcompact : IsCompact (riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) x rtest) :=
    (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _).isCompact
  have htestpatch : H.isParabolicallyRmControlledBall t x rpatch :=
    htest.mono_radius H hrpatch hrpt.le
  have hvolume : ENNReal.ofReal κ * ENNReal.ofReal rpatch ^ Module.finrank ℝ ThreeSpace ≤
      riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier (H.stageMetric (H.activeStage t) t)
        (riemannianBallOf (H.stageMetric (H.activeStage t) t) x rpatch) := by
    simpa only [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace]] using hNC rpatch hrpatch hrpeps htestpatch
  obtain ⟨p,hp,hV,himage,hvol,hconnect⟩ := Perelman.exists_volume_and_connector_action_bound_of_terminal_map
    Sflow hsol (H.stageMetric (H.activeStage t) t) f hf hinj hB hcs Subset.rfl Subset.rfl hcurv
    hstageTerminal x hrpatch hrpt hcompact hball (by linarith only [hrpΔ]) hvolume
  refine ⟨xL,hxL,first,hle,hroom,hK,hrange,gflow,hcs,hslabs,hlast,hterminal,hsol,hcurv,
    hf,hinj,hstageTerminal,hball,htest,p,hp,hV,himage,by positivity,?_,?_⟩
  · simpa only [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace], Nat.cast_ofNat,
      show (3 : ℝ) ^ 3 = 27 by norm_num, neg_mul] using hvol
  · intro T Emax hT hE q' hq'
    obtain ⟨α,hα,hαa,hαb,hαstay,hact⟩ := hconnect T Emax hT hE q' hq'
    refine ⟨α,hα,hαa,hαb,hαstay,?_⟩
    simpa only [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace], Nat.cast_ofNat,
      show (3 : ℝ) ^ 2 = 9 by norm_num, show 2 * (9 : ℝ) = 18 by norm_num,
      sub_sub_cancel] using hact

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end
