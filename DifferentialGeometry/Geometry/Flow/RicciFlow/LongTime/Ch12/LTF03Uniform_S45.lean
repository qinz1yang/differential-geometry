import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterfaceProps

set_option autoImplicit false

/-!
# CH12-S45 / G1: uniform-threshold form of LTF03

`SeedHyperbolicOnFixedBallsSeq_S13` is stated along late point sequences.  The forward-window
argument of `hLTF04` needs it as a threshold statement over all late regular slices: a
macroscopic seed `(a, v)` at `p` on a slice with `time ≥ T` forces the normalized Ricci defect
to be `< ε` on the whole normalized ball `B(p, L)`.  The proof is the usual contradiction with a
sequence of bad slices.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

/-- LTF03, threshold form: from the sequential statement for every late point sequence. -/
theorem ltf03_threshold_S45 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v L : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v L)
    (a v L ε : ℝ) (ha : 0 < a) (hv : 0 < v) (hL : 0 < L) (hε : 0 < ε) :
    ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ p : s.stage.Carrier, HasNormalizedSeed_S13 s p a v →
        ∀ q ∈ riemannianBallOf s.normalizedMetric p L, NormalizedRicciDefect_S13 s q < ε := by
  by_contra hcon
  simp only [not_exists, not_forall, not_lt] at hcon
  choose s hsT p hseed q hqL hq using hcon
  let S : LatePointSequence_S13 F :=
    { slices := fun j : ℕ => s (j : ℝ)
      times_tendsto := tendsto_atTop_mono (fun j : ℕ => hsT (j : ℝ)) tendsto_natCast_atTop_atTop
      point := fun j => p (j : ℝ) }
  have hev := hLTF03 S a v L ha hv hL (fun j => hseed (j : ℝ)) ε hε
  obtain ⟨j, hj⟩ := hev.exists
  exact absurd (hj (q (j : ℝ)) (hqL (j : ℝ))) (not_lt.mpr (hq (j : ℝ)))

end GC.LongTime.Ch12
