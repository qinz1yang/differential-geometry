import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceSeeds_CX2

/-!
# CH12-O28 G2a: running the KL Lemma 86.2 induction inside one tower history

`[FROZEN] CH12-O28`, FINDING 2.  A restarted subball at an earlier time `u < s.time` lives in the
slice history `s.history`, which is *definitionally* the prefix of the tower history
`sliceTowerHistory_CX2 s` (`slice_history_restrict_CX2`).  Running the minimal-bad-ball argument
inside that single tower history avoids any transport across `ObservationTower.observe_restrict`
(`SamePresentation`), for which no trace API exists.  This file supplies the two directions of glue:

* `tracedFamily_to_restrict_O28` / `tracedFamily_slice_of_tower_O28`: a traced family along a
  backward trace in the tower history gives the conclusion of `hG2c` in the slice history;
* `sectional_slice_to_tower_O28`, `volume_slice_to_tower_O28`: the top-time hypotheses of
  `hG2c` (sectional lower bound, Euclidean subball volumes) pass from the slice to the tower.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse

namespace GC.LongTime.Ch12

universe u

section Restrict

variable (H : ObservedHistory.{u}) (cut : Icc (0 : ℝ) H.horizon)

/-- A traced family along a backward trace of the source history restricts to the prefix. -/
theorem tracedFamily_to_restrict_O28
    {a t : Icc (0 : ℝ) (H.restrict cut).horizon} (hat : a ≤ t)
    {x : ((H.restrict cut).stageAt t).Carrier} {ρ τ K : ℝ}
    (X' : BackwardPointTrace H (H.activeStage (restrictTime_CX2 H cut a))
      (H.activeStage (restrictTime_CX2 H cut t))
      (H.activeStage_mono (show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut t from hat))
      (restrictPoint_CX2 H cut t x))
    (hfam : ∀ (u : Icc (0 : ℝ) H.horizon) (hau : restrictTime_CX2 H cut a ≤ u)
      (hut : u ≤ restrictTime_CX2 H cut t),
      H.isTracedRegion u (X'.point (H.activeStage u) (H.activeStage_mono hau)
        (H.activeStage_mono hut)) ρ τ K) :
    ∃ X : BackwardPointTrace (H.restrict cut) ((H.restrict cut).activeStage a)
        ((H.restrict cut).activeStage t) ((H.restrict cut).activeStage_mono hat) x,
      ∀ (u : Icc (0 : ℝ) (H.restrict cut).horizon) (hau : a ≤ u) (hut : u ≤ t),
        (H.restrict cut).isTracedRegion u (X.point ((H.restrict cut).activeStage u)
          ((H.restrict cut).activeStage_mono hau) ((H.restrict cut).activeStage_mono hut))
          ρ τ K := by
  refine ⟨traceAtToRestriction_CX2 H cut (hat := hat) X', fun u hau hut => ?_⟩
  rw [isTracedRegion_restrict_iff_CX2]
  have hX : traceAtOfRestriction_CX2 H cut (hat := hat)
      (traceAtToRestriction_CX2 H cut (hat := hat) X') = X' := Subsingleton.elim _ _
  have h1 := traceAtOfRestriction_point_heq_CX2 H cut (hat := hat)
    (traceAtToRestriction_CX2 H cut (hat := hat) X') u hau hut
  rw [hX] at h1
  have h2 := eq_of_heq ((restrictPoint_heq_CX2 H cut u _).trans h1.symm)
  rw [h2]
  exact hfam (restrictTime_CX2 H cut u) hau hut

end Restrict

section Heq

theorem sectional_heq_O28 {P Q : OrientedThreeStage.{u}} {g : P.Metric} {h : Q.Metric}
    (hPQ : P = Q) (hgh : HEq g h) {p : P.Carrier} {q : Q.Carrier} (hpq : HEq p q) {c : ℝ} :
    SectionalBoundedBelowAt g p c ↔ SectionalBoundedBelowAt h q c := by
  subst Q
  cases hgh
  cases hpq
  rfl

end Heq

section Slice

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- The conclusion of `hG2c` at a slice, produced in the tower history of the slice. -/
theorem tracedFamily_slice_of_tower_O28 (s : RegularSlice F.observation)
    {x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier} {ρ τ K c : ℝ}
    (a : Icc (0 : ℝ) s.history.horizon) (hat : a ≤ sliceTop_S8 s) (ha : (a : ℝ) = c)
    (X' : BackwardPointTrace (sliceTowerHistory_CX2 s)
      ((sliceTowerHistory_CX2 s).activeStage
        (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) a))
      ((sliceTowerHistory_CX2 s).activeStage
        (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)))
      ((sliceTowerHistory_CX2 s).activeStage_mono
        (show restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) a ≤
          restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)
          from hat))
      (restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s) x0))
    (hfam : ∀ (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
      (hau : restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) a ≤ u)
      (hut : u ≤ restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s)
        (sliceTop_S8 s)),
      (sliceTowerHistory_CX2 s).isTracedRegion u
        (X'.point ((sliceTowerHistory_CX2 s).activeStage u)
          ((sliceTowerHistory_CX2 s).activeStage_mono hau)
          ((sliceTowerHistory_CX2 s).activeStage_mono hut)) ρ τ K) :
    ∃ (a : Icc (0 : ℝ) s.history.horizon) (hat : a ≤ sliceTop_S8 s)
      (X : BackwardPointTrace s.history (s.history.activeStage a)
        (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) x0),
      (a : ℝ) = c ∧ ∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a ≤ u)
        (hut : u ≤ sliceTop_S8 s),
        s.history.isTracedRegion u (X.point (s.history.activeStage u)
          (s.history.activeStage_mono hau) (s.history.activeStage_mono hut)) ρ τ K := by
  obtain ⟨X, hX⟩ := tracedFamily_to_restrict_O28 (sliceTowerHistory_CX2 s)
    (sliceTowerTime_CX2 s) hat X' hfam
  exact ⟨a, hat, X, ha, hX⟩

/-- The sectional hypothesis of `hG2c` at the slice top passes to the tower history. -/
theorem sectional_slice_to_tower_O28 (s : RegularSlice F.observation)
    (t : Icc (0 : ℝ) s.history.horizon) (x0 : (s.history.stageAt t).Carrier) (r c : ℝ)
    (hsec : ∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage t) t) x0 r,
      SectionalBoundedBelowAt (s.history.stageMetric (s.history.activeStage t) t) q c) :
    ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage
          (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) t))
        (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) t))
        (restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) t x0) r,
      SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage
          (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) t))
        (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) t)) q c := by
  intro q hq
  set H := sliceTowerHistory_CX2 s
  set cut := sliceTowerTime_CX2 s
  obtain ⟨q', rfl⟩ := restrictPoint_surjective_CX2 H cut t q
  have hq' := (metricBall_heq_CX2 (H.restrict_stageAt cut t) (H.restrict_sliceMetric cut t)
    (restrictPoint_heq_CX2 H cut t x0).symm (restrictPoint_heq_CX2 H cut t q').symm r).mpr hq
  exact (sectional_heq_O28 (H.restrict_stageAt cut t) (H.restrict_sliceMetric cut t)
    (restrictPoint_heq_CX2 H cut t q').symm).mp (hsec q' hq')

/-- The Euclidean-subball volume hypothesis of `hG2c` passes to the tower history. -/
theorem volume_slice_to_tower_O28 (s : RegularSlice F.observation)
    (t : Icc (0 : ℝ) s.history.horizon) (x0 : (s.history.stageAt t).Carrier) (r ε : ℝ)
    (hvol : ∀ z ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage t) t) x0 r,
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
        ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
          ballVolume (s.history.stageMetric (s.history.activeStage t) t) z ρ) :
    ∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage
          (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) t))
        (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) t))
        (restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) t x0) r,
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
        ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
          ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage
              (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) t))
            (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) t)) z ρ := by
  intro z hz ρ hρ hρr
  set H := sliceTowerHistory_CX2 s
  set cut := sliceTowerTime_CX2 s
  obtain ⟨z', rfl⟩ := restrictPoint_surjective_CX2 H cut t z
  have hz' := (metricBall_heq_CX2 (H.restrict_stageAt cut t) (H.restrict_sliceMetric cut t)
    (restrictPoint_heq_CX2 H cut t x0).symm (restrictPoint_heq_CX2 H cut t z').symm r).mpr hz
  exact (hvol z' hz' ρ hρ hρr).trans_eq (ballVolume_heq_CX2 (H.restrict_stageAt cut t)
    (H.restrict_sliceMetric cut t) (restrictPoint_heq_CX2 H cut t z').symm ρ)

end Slice

end GC.LongTime.Ch12
