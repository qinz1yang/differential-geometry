import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterSeed_CX8
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterLocal_O7
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitData

set_option autoImplicit false

/-!
# CH12-CX8: normalized survivor flows with actual-history realizations

Each time of the local flow is the pullback of the active stage of the observed history.
The scalar bound and the deficit identity are transported from that same stage; no separate
time-slice convergence or unlinked family of pointed limits is used.
-/

noncomputable section
open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12
universe u

private local instance {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

open private ObservedHistory.isScaledSurvivorData
  ObservedHistory.exists_isScaledSurvivorData_of_isTracedRegion
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitData

open private ObservedHistory.mem_Icc_of_mem_window
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

/-- The survivor flow is linked to the actual history at every normalized time.
The stage index is generalized so this applies directly at `Fin.last` for a regular slice. -/
theorem survivor_realizations_of_traced_CX8 {P : OrientedThreeStage.{u}} {g₀ : P.Metric}
    {F : GC.Interface.RawSurgery P g₀} {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (s : GC.LongTime.RegularSlice F.observation)
    (j : Fin (s.history.eventCount + 1)) (hj : s.history.activeStage (sliceTop_S8 s) = j)
    (p : (s.history.stage j).Carrier) {b θ K : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1)
    (htr : ∀ p' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq p' p →
      s.history.isTracedRegion (sliceTop_S8 s) p' (2 * (b * Real.sqrt s.time))
        (θ * s.time) (K / s.time)) :
    ∃ (W : Opens (s.history.stage j).Carrier)
      (g : ℝ → SmoothRiemannianMetric ThreeModel W),
      (W : Set (s.history.stage j).Carrier) =
        riemannianBallOf (scaleMetric s.time⁻¹ (inv_pos.mpr s.positive)
          (s.history.stageMetric j s.time)) p (2 * b) ∧
      IsSolutionOn (flowOn_O7 g θ hθ.le) ∧
      g 0 = (scaleMetric s.time⁻¹ (inv_pos.mpr s.positive)
        (s.history.stageMetric j s.time)).restrictOpen W ∧
      (∀ σ ∈ Icc (-θ) 0, ∀ x : W, curvDerivNormSq 0 (g σ) x ≤ K ^ 2) ∧
      ∀ σ ∈ Icc (-θ) 0, ∃ (X : OrientedThreeStage.{u}) (m : X.Metric)
        (f : W → X.Carrier) (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f),
        Function.Injective f ∧
        g σ = scaleMetric s.time⁻¹ (inv_pos.mpr s.positive) (localPullMetric m f hf) ∧
        (∀ x : X.Carrier, -3 / (2 * (s.time * (1 + σ) + Hp.scalarShift)) ≤
          metricScalarAt m x) ∧
        metricDeficit_O7 m Hp.scalarShift (s.time * (1 + σ)) =
          metricDeficit_O7 (GC.LongTime.postMetric F.observation (s.time * (1 + σ)))
            Hp.scalarShift (s.time * (1 + σ)) := by
  subst hj
  have ht := s.positive
  have htr' : s.history.isTracedRegion (sliceTop_S8 s) p (2 * (b * Real.sqrt s.time))
      (θ / s.time⁻¹) (K * s.time⁻¹) := by
    simpa only [div_inv_eq_mul, div_eq_mul_inv, inv_inv] using htr p HEq.rfl
  obtain ⟨W, g, hW, hsol, hzero, hcurv, -, a, hat, ha, f, hf, hinj, -, -, hpull⟩ :=
    ObservedHistory.exists_isScaledSurvivorData_of_isTracedRegion s.history (sliceTop_S8 s) p
      (inv_pos.mpr ht) hθ htr'
  refine ⟨W, g, ?_, hsol θ hθ.le le_rfl, hzero, hcurv, ?_⟩
  · rw [hW]
    have hsqrt : 0 < Real.sqrt s.time := Real.sqrt_pos.mpr ht
    have hscale : Real.sqrt s.time⁻¹ * (2 * (b * Real.sqrt s.time)) = 2 * b := by
      rw [Real.sqrt_inv]; field_simp
    exact (hscale ▸ riemannianBallOf_scaleMetric s.time⁻¹ (inv_pos.mpr ht)
      (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p
      (2 * (b * Real.sqrt s.time))).symm
  intro σ hσ
  have htime : s.time + σ / s.time⁻¹ = s.time * (1 + σ) := by
    rw [div_inv_eq_mul]; ring
  have hwin := ObservedHistory.mem_Icc_of_mem_window (inv_pos.mpr ht) ha hσ
  change (a : ℝ) ≤ s.time + σ / s.time⁻¹ ∧ s.time + σ / s.time⁻¹ ≤ s.time at hwin
  rw [htime] at hwin
  have hpos : 0 < s.time * (1 + σ) := mul_pos ht (by linarith [hσ.1])
  let u : Icc (0 : ℝ) s.history.horizon := ⟨s.time * (1 + σ), hpos.le, hwin.2⟩
  let i : s.history.StageInterval (s.history.activeStage a)
      (s.history.activeStage (sliceTop_S8 s)) :=
    ⟨s.history.activeStage u, s.history.activeStage_mono hwin.1,
      s.history.activeStage_mono hwin.2⟩
  have hdom : s.time + σ / s.time⁻¹ ∈ s.history.stageDomain i.val := by
    rw [htime]
    exact s.history.activeStage_mem u
  have hmetric := hpull σ hσ i hdom
  change g σ = scaleMetric s.time⁻¹ (inv_pos.mpr ht)
    (localPullMetric (s.history.stageMetric i.val (s.time + σ / s.time⁻¹)) (f i) (hf i)) at hmetric
  rw [htime] at hmetric
  refine ⟨s.history.stage i.val, s.history.stageMetric i.val u, f i, hf i,
    hinj i, hmetric, ?_, ?_⟩
  · exact postMetric_lower_on_observe_S10 F.observation
      (fun t => -3 / (2 * (t + Hp.scalarShift))) Hp.scalar_lower s.time ht.le u
  · exact (metricDeficit_postMetric_eq_O7 F.observation s.time ht.le
      (s.time * (1 + σ)) hpos hwin.2 Hp.scalarShift).symm

end GC.LongTime.Ch12
