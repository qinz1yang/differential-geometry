import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionShiWholeBallApplications

/-!
# CH12-S8, group 1: W3 (WBD01) — buffered traced region ⇒ whole-ball Shi bound ⇒ `MacroWholeBall_O2`

W2 (M01: KL83.1 seed, KL84.2 backward survival, first exit; D-WBD §4.1 `eventually_buffered_traces_of_volume_test`)
is an **explicit hypothesis** `hW2` of `macroWholeBall_O2_of_W2_S8`, written out in full (no new named Prop),
in the slice form `H := s.history`, `t := s.time`.  W3 is proved here from A11b
(`curvatureDerivativeNorm_le_whole_ball_of_isTracedRegion`: TerminalBall Shi on a traced region).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- The terminal time of the observed history of a regular slice, as a point of its time interval. -/
def sliceTop_S8 (s : GC.LongTime.RegularSlice F.observation) : Icc (0 : ℝ) s.history.horizon :=
  ⟨s.time, s.positive.le, le_rfl⟩

/-- Core of W3, with the stage index generalized (so that `activeStage_at_horizon` can be `subst`ed):
a traced region of radius `2r`, backward time `τ r²`, curvature `C r⁻²` gives the whole-ball bound. -/
theorem wholeBall_of_traced_S8 (s : GC.LongTime.RegularSlice F.observation)
    (j : Fin (s.history.eventCount + 1)) (hj : s.history.activeStage (sliceTop_S8 s) = j)
    (p : (s.history.stage j).Carrier) {τ r C : ℝ} (hτ : 0 < τ) (hr : 0 < r) (hC : 0 < C)
    (htr : ∀ p' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq p' p →
      s.history.isTracedRegion (sliceTop_S8 s) p' (2 * r) (τ * r ^ 2) (C / r ^ 2)) (m : ℕ) :
    ∀ q ∈ riemannianBallOf (s.history.stageMetric j s.time) p r,
      curvatureDerivativeNorm (s.history.stageMetric j s.time) m q ≤
        (shiLocalUniformBound 3 m (C * τ / 2)
            (Real.sqrt C / (8 * Real.exp ((3 : ℝ) ^ 2 * (C * τ / 2)))) *
          C / Real.sqrt (τ / 2) ^ m) * (r ^ (m + 2))⁻¹ := by
  subst hj
  have h := FILL910.curvatureDerivativeNorm_le_whole_ball_of_isTracedRegion s.history
    (sliceTop_S8 s) p hτ hr hC (htr p HEq.rfl) m
  intro q hq
  have := h q hq
  rw [div_eq_mul_inv] at this
  exact this


/-- **W2 ∘ W3 = `MacroWholeBall_O2`.**  `hW2` (explicit input, W2/M01; exact statement frozen in
DELIVERIES CH12-S8) produces the buffered traced region at every macroscopic test ball; the
conclusion is `MacroWholeBall_O2 Hp`, with `Λ, b, T` those of `hW2` and
`A k = shiLocalUniformBound 3 k (Cτ/2) (√C/(8 e^{9Cτ/2})) · C / √(τ/2)^k`. -/
theorem macroWholeBall_O2_of_W2_S8 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
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
        s.history.isTracedRegion (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (C / r ^ 2)) :
    MacroWholeBall_O2 Hp := by
  intro w hw
  obtain ⟨T, Λ, b, τ, C, hT, hΛ, hb, hτ, hC, -, hW⟩ := hW2 w hw
  refine ⟨Λ, b, T, fun k => shiLocalUniformBound 3 k (C * τ / 2)
    (Real.sqrt C / (8 * Real.exp ((3 : ℝ) ^ 2 * (C * τ / 2)))) * C / Real.sqrt (τ / 2) ^ k,
    hΛ, hb, ?_⟩
  intro s hs p ρ hρ hρb hrec _ hsec hvol k
  have hgen : ∀ (j : Fin (s.history.eventCount + 1))
      (hj : s.history.activeStage (sliceTop_S8 s) = j) (p : (s.history.stage j).Carrier),
      (∀ q ∈ riemannianBallOf (s.history.stageMetric j s.time) p ρ,
        SectionalBoundedBelowAt (s.history.stageMetric j s.time) q (-(ρ ^ 2)⁻¹)) →
      ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume (s.history.stageMetric j s.time) p ρ →
      ∀ q ∈ riemannianBallOf (s.history.stageMetric j s.time) p ρ,
        curvatureDerivativeNorm (s.history.stageMetric j s.time) k q ≤
          (shiLocalUniformBound 3 k (C * τ / 2)
            (Real.sqrt C / (8 * Real.exp ((3 : ℝ) ^ 2 * (C * τ / 2)))) * C /
              Real.sqrt (τ / 2) ^ k) * (ρ ^ (k + 2))⁻¹ := by
    intro j hj
    subst hj
    intro p hsec hvol
    have htr := hW s hs p ρ hρ hρb hsec hvol
      hrec
    exact wholeBall_of_traced_S8 s _ rfl p hτ hρ hC (fun p' hp' => by cases hp'; exact htr) k
  exact hgen (Fin.last _) s.history.activeStage_at_horizon p hsec hvol

end GC.LongTime.Ch12
