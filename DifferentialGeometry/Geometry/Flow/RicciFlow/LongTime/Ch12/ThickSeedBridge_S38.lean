import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickJetsFinal_S36
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickScaleQ1_S37
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LargeTriggerSeed_S21

set_option autoImplicit false

/-!
# CH12-S38 / G1: the Q1 bridge

`thick_scale_lower_bound_S37` (`a ≤ ρ` for a thick point of curvature radius `ρ`) gives the
seed form `hQ1` consumed by `thickSequenceHasHyperbolicSubsequence_S36`, through the
Bishop--Gromov scale-down `seed_scale_down_S21` at the scale `a ≤ ρ`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

/-- A point of curvature radius `r` whose `r`-ball has volume `≥ w r³` carries a seed
`(a, c w)` at every scale `a ≤ r`, with a numerical constant `c`. -/
theorem thick_seed_S38 : ∃ c : ℝ, 0 < c ∧
    ∀ (Q : OrientedThreeStage.{u}) (ĝ : Q.Metric) (p : Q.Carrier) (w r a : ℝ),
      0 < w → 0 < r → curvatureRadius ĝ p = ENNReal.ofReal r →
      ENNReal.ofReal (w * r ^ 3) ≤ ballVolume ĝ p r → 0 < a → a ≤ r →
      (∀ q ∈ riemannianBallOf ĝ p a, SectionalBoundedBelowAt ĝ q (-(a ^ 2)⁻¹)) ∧
        ENNReal.ofReal (c * w * a ^ 3) ≤ ballVolume ĝ p a := by
  obtain ⟨c, hc, hseed⟩ := seed_scale_down_S21.{u}
  refine ⟨c, hc, ?_⟩
  intro Q ĝ p w r a hw hr hcr hvol ha har
  exact hseed Q.Carrier ĝ p w r a hw ha har
    (sec_lower_on_ball_of_curvatureRadius_S37 Q ĝ p hr hcr) hvol

/-- The Q1 bridge: S37's `a ≤ ρ` form of Q1-scale implies the seed form `hQ1` of S36. -/
theorem hQ1_of_scale_S38 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g}
    (hscale : ∀ w : ℝ, 0 < w → ∃ a : ℝ, 0 < a ∧ ∃ T : ℝ,
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        curvatureRadius s.normalizedMetric p = ENNReal.ofReal ρ →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.normalizedMetric p ρ → a ≤ ρ) :
    ∀ w : ℝ, 0 < w → ∃ T a v : ℝ, 0 < a ∧ 0 < v ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ (p : s.stage.Carrier) (r : ℝ), 0 < r →
        curvatureRadius s.normalizedMetric p = ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r →
        HasNormalizedSeed_S13 s p a v := by
  obtain ⟨c, hc, hseed⟩ := thick_seed_S38.{u}
  intro w hw
  obtain ⟨a, ha, T, hT⟩ := hscale w hw
  refine ⟨T, a, c * w, ha, mul_pos hc hw, ?_⟩
  intro s hs p r hr hcr hvol
  exact hseed s.stage s.normalizedMetric p w r a hw hr hcr hvol ha (hT s hs p r hr hcr hvol)

/-- **LTF05a without `hQ1`.**  The extraction of a hyperbolic subsequence from a `w`-thick
sequence from LTF03, W2 and the zero-order part of W1 (Q1-scale of S37 inside). -/
theorem thickSequenceHasHyperbolicSubsequence_S38 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v R : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v R)
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
    (K : ℕ)
    (hW1 : ∃ (b T C : ℝ → ℝ), (∀ w : ℝ, 0 < w → 0 < b w) ∧ (∀ w, 0 < C w) ∧
      ∀ w : ℝ, 0 < w → ∀ s : RegularSlice F.observation, T w ≤ s.time →
      ∀ (p : s.stage.Carrier) (r : ℝ), 0 < r → r ≤ b w →
        (∃ z ∈ connectedComponent p,
          ¬ SectionalBoundedBelowAt s.normalizedMetric z 0) →
        (∀ q ∈ riemannianBallOf s.normalizedMetric p r,
          SectionalBoundedBelowAt s.normalizedMetric q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r →
        ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.normalizedMetric p r,
          curvatureDerivativeNorm s.normalizedMetric k q ≤ C w * (r ^ (k + 2))⁻¹)
    (w : ℝ) :
    ThickSequenceHasHyperbolicSubsequence_S13 Hp hdec hneg w :=
  thickSequenceHasHyperbolicSubsequence_S36 Hp hdec hneg hLTF03 hW2 w
    (hQ1_of_scale_S38 (thick_scale_lower_bound_S37 Hp K hW1))

end GC.LongTime.Ch12
