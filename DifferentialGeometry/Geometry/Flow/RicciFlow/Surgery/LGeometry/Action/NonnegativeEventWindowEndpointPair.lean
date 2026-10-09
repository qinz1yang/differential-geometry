import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EventWindowEndpointPair

set_option autoImplicit false
noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

open private exceptional_mem_inner_window from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapNoShortcut

/-- The actual endpoint-pair construction also permits the zero-clock event.
The selected seed trace, supplied curve and common cap family stay fixed. -/
theorem exists_old_seed_and_endpoint_outside_retained_cap_windows_of_nonneg_clock
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
    (r k Aact rTerm : ℝ) (hr : 0 < r) (hk : 0 ≤ k)
    (hhalf : k ^ 2 ≤ r ^ 2 / 2)
    (hseed : H.isParabolicallyRmControlledBall t p r)
    (hrTerm : 0 < rTerm) (hrTermLe : rTerm ≤ r)
    (htest : H.isParabolicallyRmControlledBall t x rTerm)
    (hseedBudget : 3 * r ≤ Aact)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (htrace : seedTrace.isRmControlled (hat := hSeedTime) r)
    (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t)
    (hevent : t.val - k ^ 2 = H.time i.succ)
    {D ε : ℝ} {m : ℕ}
    (S : ∀ c : (H.event i).RetainedBoundaryIndex,
      (H.event i).PresentedStaticCap parameters.fixed D m ε c)
    (hcanonical : ∀ c, (S c).hasCanonicalWindow)
    (hEndpoint : ∀ (pole : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t pole rTerm →
      ∀ (L : ℝ) (q : (H.stage i.succ).Carrier),
        L ∈ H.regularizedC1ActionValues i.succ (H.activeStage t) hl t.val 0 k pole q →
        L ≤ Aact →
        ∀ c : (H.event i).RetainedBoundaryIndex,
          q ∉ (S c).window ''
            {z : standardCapWindow D | ‖z.val‖ ≤ StandardCap.transitionEnd + 10})
    (gamma : (j : H.StageInterval i.succ (H.activeStage t)) → ℝ → (H.stage j.val).Carrier)
    (hC1 : ∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j))
    (hInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
      (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val))
    (hterminal : gamma ⟨H.activeStage t, hl, le_rfl⟩ 0 = x)
    (hnodes : ∀ (j : Fin H.eventCount) (hf : i.succ ≤ j.castSucc)
      (hj : j.succ ≤ H.activeStage t),
      ∃ z : (H.event j).old,
        z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hj⟩
          (Real.sqrt (t.val - H.time j.succ)) ∧
        (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hj⟩
          (Real.sqrt (t.val - H.time j.succ)))
    (hsmall : (∑ j : H.StageInterval i.succ (H.activeStage t),
      H.stageRegularizedAction j.val t.val (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ≤ Aact) :
    ∃ hfSeed : H.activeStage aSeed ≤ i.castSucc,
    ∃ O z : (H.event i).old,
      O.val.val = seedTrace.point i.castSucc hfSeed (i.castSucc_le_succ.trans hl) ∧
      (H.event i).oldOutput O =
        seedTrace.point i.succ (hfSeed.trans i.castSucc_le_succ) hl ∧
      (H.event i).oldOutput z = gamma ⟨i.succ, le_rfl, hl⟩ k ∧
      (∀ c : (H.event i).RetainedBoundaryIndex,
        (H.event i).oldOutput O ∉ (S c).window ''
          {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
      (∀ c : (H.event i).RetainedBoundaryIndex,
        (H.event i).oldOutput z ∉ (S c).window ''
          {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) := by
  classical
  have hseedBefore : (aSeed : ℝ) < H.time i.succ := by
    rw [hSeedClock, ← hevent]
    nlinarith [sq_pos_of_pos hr]
  have hfSeed : H.activeStage aSeed ≤ i.castSucc := by
    by_contra hnot
    have hsucc : i.succ ≤ H.activeStage aSeed := by
      have hh : i.castSucc < H.activeStage aSeed := lt_of_not_ge hnot
      change i.val < (H.activeStage aSeed).val at hh
      change i.val + 1 ≤ (H.activeStage aSeed).val
      omega
    exact (not_le_of_gt hseedBefore)
      ((H.time_strictMono.monotone hsucc).trans (H.activeStage_time_le aSeed))
  obtain ⟨O, _, hOin, hOout⟩ := seedTrace.crossing i hfSeed hl
  let aBirth := H.stageTime i.succ
  have hSeedBirth : aSeed ≤ aBirth := hseedBefore.le
  have hBirthLe : aBirth ≤ t :=
    (H.time_strictMono.monotone hl).trans (H.activeStage_time_le t)
  have hSeedActionAt (j : Fin (H.eventCount + 1)) (hj : j = H.activeStage aBirth)
      (hfirst : H.activeStage aSeed ≤ j) (hlast : j ≤ H.activeStage t) :
      ∃ L : ℝ,
        L ∈ H.regularizedC1ActionValues j (H.activeStage t) hlast t.val 0 k p
          (seedTrace.point j hfirst hlast) ∧ L ≤ 6 * k ^ 3 / r ^ 2 := by
    subst j
    let tail := seedTrace.restrictFirst hfirst hlast
    have htail : tail.isRmControlled (hat := hBirthLe) r :=
      htrace.restrictFirst seedTrace hr.le le_rfl hSeedBirth hBirthLe
    exact tail.exists_regularizedC1ActionValues_le_of_isRmControlled hr hk hevent htail
  obtain ⟨Lseed, hLseed, hLseedBound⟩ := hSeedActionAt i.succ
    (H.activeStage_stageTime i.succ).symm (hfSeed.trans i.castSucc_le_succ) hl
  have hkr : k ≤ r :=
    (sq_le_sq₀ hk hr.le).mp (by nlinarith [sq_nonneg r])
  have hseedSmall : Lseed ≤ Aact := by
    have hmul := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 6 * k)
    calc
      Lseed ≤ 6 * k ^ 3 / r ^ 2 := hLseedBound
      _ ≤ 3 * k := (div_le_iff₀ (sq_pos_of_pos hr)).mpr (by nlinarith only [hmul])
      _ ≤ 3 * r := by linarith
      _ ≤ Aact := hseedBudget
  have hOoutside : ∀ c : (H.event i).RetainedBoundaryIndex,
      (H.event i).oldOutput O ∉ (S c).window ''
        {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd + 10} := by
    refine hEndpoint p (hseed.mono_radius H hrTerm hrTermLe) Lseed _ ?_ hseedSmall
    rw [hOout]
    exact hLseed
  let q := gamma ⟨i.succ, le_rfl, hl⟩ k
  let Lgamma := ∑ j : H.StageInterval i.succ (H.activeStage t),
    H.stageRegularizedAction j.val t.val (gamma j)
      (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)
  have hupper : t.val - (0 : ℝ) ^ 2 ∈
      Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using
      (show t.val ∈ Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) from
        ⟨H.activeStage_time_le t, H.le_stageEndTime_of_mem_stageDomain (H.activeStage_mem t)⟩)
  have hlower : t.val - k ^ 2 ∈ H.stageDomain i.succ := by
    rw [hevent]
    exact (H.mem_stageDomain_iff (H.stageTime i.succ) i.succ).mpr
      (H.activeStage_stageTime i.succ)
  have hgammaAction : Lgamma ∈ H.regularizedC1ActionValues
      i.succ (H.activeStage t) hl t.val 0 k x q :=
    ⟨le_rfl, hk, hupper, hlower, gamma, hC1, hInt, hterminal, rfl, hnodes, rfl⟩
  have hqoutside := hEndpoint x htest Lgamma q hgammaAction hsmall
  have hqInterior : q ∈ interior (range (H.event i).oldOutput) := by
    by_contra hnot
    obtain ⟨c, y, hy, hyq⟩ := exceptional_mem_inner_window
      (H.event i) S (records i).old_eq_retained hcanonical hnot
    exact hqoutside c ⟨y, by change ‖y.val‖ ≤ StandardCap.transitionEnd + 10; linarith, hyq⟩
  obtain ⟨z, hz⟩ := interior_subset hqInterior
  refine ⟨hfSeed, O, z, hOin, hOout, hz, hOoutside, ?_⟩
  intro c
  rw [hz]
  exact hqoutside c

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
