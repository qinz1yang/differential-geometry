import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84CapExclude_S74
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TrackedLift_S70
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype

set_option autoImplicit false

/-!
# CH12-S89 / G1: backward crossing at an event time (history-level core)

An `Ico` lift datum (`a ≤ t0`, stage range `[first, last]`) whose survivor points sit at the
START of stage `first = i.succ` with `time first = t0` cannot be an `Ioo` datum (`a' < t0`): the
stage range would have to start before the event.  If the lifted points `q_p` of the initial slice
of stage `i.succ` have scalar `≤ 0`, they are not cap points (cap exclusion
`exists_regularCrossing_of_scalar_lt_S74`), so each `φ p` extends to a backward trace over
`[i.castSucc, last]` (`BackwardPointTrace.prepend`).  The new lift `φ'` has the SAME underlying
points as `φ` (smoothness is `val ∘ φ' = val ∘ φ`), and the survivor maps at all later stages
agree, hence the HEq clause is unchanged.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem exists_nominal_bound_S89 {K : ObservedHistory.{u}} {i : Fin K.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord K i p) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ h, R.nominalRadius h ≤ r0 := by
  by_cases hne : Nonempty (K.event i).transition.trace.tubes.Index
  · exact ⟨R.nominalRadius hne, R.nominal_pos hne, fun _ => le_of_eq rfl⟩
  · exact ⟨1, one_pos, fun h => absurd h hne⟩

/-- A point of the initial slice of stage `i.succ` with scalar `≤ 0` is a regular-crossing image
(cap exclusion with `C₁ = 1` and `r0` any bound for the nominal radii). -/
theorem exists_regularCrossing_of_scalar_nonpos_S89 {K : ObservedHistory.{u}}
    {i : Fin K.eventCount} {p : CutoffParameters} (R : GeometricCutoffRecord K i p)
    (hscale : ∀ (b : (K.event i).RetainedBoundaryIndex) (z : ThreeBall),
      (R.static b).neck.scale / 2 ≤
        metricScalarAt (R.static b).witness.metric ((R.static b).witness.cap z))
    (hrc : p.recenterConstant * p.delta (K.time i.succ) ≤ 1 / 2)
    (q : (K.stage i.succ).Carrier) (hq : metricScalarAt (K.initialMetric i.succ) q ≤ 0) :
    ∃ z : (K.stage i.castSucc).Carrier, (K.event i).RegularCrossing z q := by
  obtain ⟨r0, hr0, hnom⟩ := exists_nominal_bound_S89 R
  refine exists_regularCrossing_of_scalar_lt_S74 R (C₁ := 1) (r0 := r0) one_pos hr0 hscale hrc
    (fun h => by rw [one_mul]; exact hnom h) q ?_
  rw [K.event_output i]
  exact lt_of_le_of_lt hq (by positivity)

/-- Extension of a survivor point of `[i.succ, last]` to `[i.castSucc, last]` across the event `i`,
given a regular-crossing preimage of its first point; the later survivor maps are unchanged. -/
theorem exists_extend_survivor_S89 {K : ObservedHistory.{u}} {i : Fin K.eventCount}
    {last : Fin (K.eventCount + 1)} (ordered : i.succ ≤ last)
    (x : K.backwardSurvivorDomain i.succ last ordered)
    (hz : ∃ z : (K.stage i.castSucc).Carrier, (K.event i).RegularCrossing z
      (K.backwardSurvivorMap i.succ last ordered i.succ le_rfl ordered x)) :
    ∃ y : K.backwardSurvivorDomain i.castSucc last (i.castSucc_lt_succ.le.trans ordered),
      y.val = x.val ∧ ∀ (ρ : Fin (K.eventCount + 1)) (hj : i.succ ≤ ρ) (hl : ρ ≤ last),
        K.backwardSurvivorMap i.castSucc last (i.castSucc_lt_succ.le.trans ordered) ρ
          ((i.castSucc_lt_succ.le).trans hj) hl y =
        K.backwardSurvivorMap i.succ last ordered ρ hj hl x := by
  obtain ⟨z, hz⟩ := hz
  let A : BackwardPointTrace K i.succ last ordered x.val := Classical.choice x.property
  have hq : K.backwardSurvivorMap i.succ last ordered i.succ le_rfl ordered x =
      A.point i.succ le_rfl ordered := rfl
  rw [hq] at hz
  let A' := A.prepend z hz
  let y : K.backwardSurvivorDomain i.castSucc last (i.castSucc_lt_succ.le.trans ordered) :=
    ⟨x.val, ⟨A'⟩⟩
  refine ⟨y, rfl, fun ρ hj hl => ?_⟩
  have h1 : K.backwardSurvivorMap i.castSucc last (i.castSucc_lt_succ.le.trans ordered) ρ
      ((i.castSucc_lt_succ.le).trans hj) hl y = A'.point ρ ((i.castSucc_lt_succ.le).trans hj) hl :=
    K.backwardSurvivorMap_eq_point _ _ _ ρ _ hl y A'
  have h2 : K.backwardSurvivorMap i.succ last ordered ρ hj hl x = A.point ρ hj hl :=
    K.backwardSurvivorMap_eq_point _ _ _ ρ hj hl x A
  rw [h1, h2]
  have hne : ρ ≠ i.castSucc := fun h => by
    have := i.castSucc_lt_succ
    rw [← h] at this
    exact absurd hj (not_le.mpr this)
  change (if hki : ρ = i.castSucc then hki ▸ z else A.point ρ _ hl) = A.point ρ hj hl
  simp only [dite_eq_right hne]

end GC.LongTime.Ch12
