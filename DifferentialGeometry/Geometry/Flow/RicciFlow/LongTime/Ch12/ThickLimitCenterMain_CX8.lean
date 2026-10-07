import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterSurvivor_CX8
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterExtraction_CX8

set_option autoImplicit false

/-!
# CH12-CX8: the parabolic centre theorem, in O5's exact C1 shape

The only extra analytic input is the unchanged W2 hypothesis from S8. A bad subsequence
retains its fixed seed constants and lies beyond the uniform traced-window threshold.
Its survivor flows have a linked local parabolic limit; O7's deficit argument and the
centre-defect transport contradict the lower bound on the bad subsequence.
-/

noncomputable section
open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12
universe u

/-- C1 (`hcenter`) with O5's seed constants, quantifiers and strict defect bound unchanged. -/
theorem hcenter_CX8 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hW2 : ∀ w : ℝ, 0 < w → ∃ T Λ b τ C : ℝ, 0 < T ∧ 1 ≤ Λ ∧ 0 < b ∧ 0 < τ ∧ 0 < C ∧
      τ * b ^ 2 < 1 / 2 ∧
      ∀ s : GC.LongTime.RegularSlice F.observation, T ≤ s.time →
      ∀ (p : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r : ℝ), 0 < r →
        r ≤ b * Real.sqrt s.time →
        (∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s))
            s.time) p r,
          SectionalBoundedBelowAt (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s))
            s.time) q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (s.history.stageMetric
          (s.history.activeStage (sliceTop_S8 s)) s.time) p r →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ r) →
        s.history.isTracedRegion (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (C / r ^ 2))
    : ∀ (S : LatePointSequence_S13 F) (a v : ℝ), 0 < a → 0 < v →
      (∀ j, HasNormalizedSeed_S13 (S.slices j) (S.point j) a v) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, NormalizedRicciDefect_S13 (S.slices j) (S.point j) < ε := by
  intro S a v ha hv hseed ε hε
  obtain ⟨b, θ, K, T, hb, hba, hθ, hθhalf, hK, -, hwin⟩ :=
    traced_window_of_seed_CX8 Hp hW2 ha hv
  have hθ1 : θ < 1 := by linarith
  by_contra hfail
  rw [Filter.not_eventually] at hfail
  have hlate : ∀ᶠ n in atTop, T ≤ (S.slices n).time :=
    S.times_tendsto.eventually (eventually_ge_atTop T)
  obtain ⟨φ, hφ, hφn⟩ := Filter.extraction_of_frequently_atTop (hfail.and_eventually hlate)
  let S' := S.subsequence φ hφ
  have hseed' (n : ℕ) : HasNormalizedSeed_S13 (S'.slices n) (S'.point n) a v := hseed (φ n)
  have hex (n : ℕ) := survivor_realizations_of_traced_CX8 Hp (S'.slices n)
    (Fin.last _) (S'.slices n).history.activeStage_at_horizon (S'.point n) hθ hθ1
    (hwin (S'.slices n) (hφn n).2 (S'.point n) (hseed' n))
  choose W h hW hsol hzero hcurv hreal using hex
  obtain ⟨n, hn⟩ := exists_center_defect_lt_of_survivors_CX8 Hp S' hv hb hba hθ hθ1 hK
    hseed' W h hW hsol hzero hcurv hreal hε
  exact (hφn n).1 hn

end GC.LongTime.Ch12
