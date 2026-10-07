import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterface
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeamImage_CX4

set_option autoImplicit false

/-! CH12-O27 G3 (part b) — **HPI06 regular-time covering from `Done`** (R4 core, sequence step).
If no `w`-thick `LatePointSequence_S13` escapes (ESC, the [FROZEN] CH12-O21 G0 shape with
`old := count`) the family's core images, then at late regular times every `w`-thick point lies in the
image of a model ball of one fixed radius `N`.  Pure diagonal argument: a counterexample at times
`≥ n` outside the radius-`n` images is an escaping `w`-thick sequence. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

/-- **R4 core (regular times).**  `hdone` = "Done" of the H4 iteration for thickness `w`. -/
theorem cover_regular_of_done_O27 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (count : ℕ)
    (model : Fin count → FiniteVolumeHyperbolicModel.{u}) (start : Fin count → ℝ)
    (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier)
    (w : ℝ)
    (hdone : ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w →
      ¬ ∀ (i : Fin count) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : start i ≤ (S.slices j).time,
        S.point j ∉ sliceCast_CX4 (S.slices j) ''
          (map i _ hj '' riemannianBallOf (model i).metric (model i).basepoint R)) :
    ∃ N : ℕ, ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (r : ℝ), 0 < r →
        curvatureRadius s.normalizedMetric p = ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r →
        ∃ (i : Fin count) (hi : start i ≤ s.time),
          p ∈ sliceCast_CX4 s '' (map i s.time hi ''
            riemannianBallOf (model i).metric (model i).basepoint N) := by
  by_contra hcon
  push Not at hcon
  choose s hs p r hr hcr hth hno using fun n : ℕ => hcon n n
  let S : LatePointSequence_S13 F :=
    { slices := s
      times_tendsto := tendsto_atTop_mono (fun n => hs n) tendsto_natCast_atTop_atTop
      point := p }
  refine hdone S (fun j => ⟨r j, hr j, hcr j, hth j⟩) fun i R => ⟨⌈R⌉₊, fun j hj hij hmem => ?_⟩
  obtain ⟨x, ⟨y, hy, rfl⟩, hx⟩ := hmem
  refine hno j i hij ⟨map i _ hij y, ⟨y, riemannianBallOf_mono _ _ ?_ hy, rfl⟩, hx⟩
  exact (Nat.le_ceil R).trans (by exact_mod_cast hj)

end GC.LongTime.Ch12
