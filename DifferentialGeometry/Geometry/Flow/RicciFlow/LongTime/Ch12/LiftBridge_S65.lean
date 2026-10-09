import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ForwardWindowDef_S45
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EventRightFamily_S38
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryKernelHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices

set_option autoImplicit false

/-!
# CH12-S65 / G1: lift data and the `HEq` bridge between tower histories and `postStage`

For `n : ℕ` and a time `r ∈ [0, n]`, the stage `postStage F.observation r` equals the active stage
`(F.tower.history n).stage (activeStage r)` (`postStage_eq_stage_active_CPD2`), and the metrics
agree up to `HEq` (`postMetric_heq_stageMetric_S65`, the `postMetric_regularSlice` analogue at
arbitrary, event or non-event, times).  `liftMap_S65` is the survivor map composed with the cast
`activeStage r ⟶ postStage r`; `ckErr` is invariant under this cast.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime GC.LongTime.Ch12 GC.LongTime.CuspP1
open scoped Manifold ContDiff ENNReal
universe u

namespace GC.LongTime.Ch12

section Generic

/-- `ckErr_S45` is invariant under transporting the target along an equality of stages. -/
theorem ckErr_cast_S65 (H : FiniteVolumeHyperbolicModel.{u}) {A B : OrientedThreeStage.{u}}
    (h : A = B) (gA : A.Metric) (gB : B.Metric) (hg : HEq gA gB) (c : ℝ)
    (f : H.Carrier → A.Carrier) (k : ℕ) (p : H.Carrier) :
    ckErr_S45 H gA c f k p =
      ckErr_S45 H gB c (fun q => cast (congrArg OrientedThreeStage.Carrier h) (f q)) k p := by
  subst h
  rw [eq_of_heq hg]
  rfl

theorem contMDiffOn_cast_S65 {A B : OrientedThreeStage.{u}} (h : A = B) {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] (f : X → A.Carrier)
    (s : Set X) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f s) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => cast (congrArg OrientedThreeStage.Carrier h) (f x)) s := by
  subst h
  exact hf

theorem cast_inj_S65 {A B : OrientedThreeStage.{u}} (h : A = B) {x y : A.Carrier}
    (hxy : cast (congrArg OrientedThreeStage.Carrier h) x =
      cast (congrArg OrientedThreeStage.Carrier h) y) : x = y := by
  subst h
  exact hxy

end Generic

section Bridge

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

private theorem stageMetric_index_heq_S65 (H : ObservedHistory.{u}) {j j' : Fin (H.eventCount + 1)}
    (hj : j = j') (τ : ℝ) : HEq (H.stageMetric j τ) (H.stageMetric j' τ) := by
  subst hj
  rfl

/-- The metric of `postStage r` is, up to `HEq`, the metric of the active stage of the history
`n` at time `r` (any `r ∈ [0, n]`, in particular event times). -/
theorem postMetric_heq_stageMetric_S65 (T : ObservationTower P g) (n : ℕ)
    (t : Icc (0 : ℝ) (T.history n).horizon) :
    HEq (postMetric T (t : ℝ)) ((T.history n).stageMetric ((T.history n).activeStage t) (t : ℝ)) := by
  have hb0 : 0 ≤ (t : ℝ) := t.2.1
  have hbn : (t : ℝ) ≤ (n : ℝ) := le_of_le_of_eq t.2.2 (T.horizon_eq n)
  have h1 := (postStage_eq_observe_S38 T (t : ℝ) hb0).2
  have R := T.observe_eq_atIndex n (t : ℝ) hb0 hbn
  have hdom : (t : ℝ) ∈ (T.observe (t : ℝ) hb0).stageDomain
      (Fin.last (T.observe (t : ℝ) hb0).eventCount) := by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, Set.mem_Icc]
    exact ⟨(T.observe (t : ℝ) hb0).time_le_horizon, le_rfl⟩
  have h2 := R.metric_heq _ _ hdom
  have hdom2 : (t : ℝ) ∈ (T.atIndex n (t : ℝ) hb0 hbn).stageDomain
      (Fin.cast (congrArg (· + 1) R.count_eq) (Fin.last (T.observe (t : ℝ) hb0).eventCount)) := by
    have hcast : Fin.cast (congrArg (· + 1) R.count_eq) (Fin.last (T.observe (t : ℝ) hb0).eventCount)
        = Fin.last (T.atIndex n (t : ℝ) hb0 hbn).eventCount := Fin.ext R.count_eq
    rw [hcast]
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, Set.mem_Icc]
    exact ⟨(T.atIndex n (t : ℝ) hb0 hbn).time_le_horizon, le_rfl⟩
  have h3 := ObservedHistory.restrict_stageMetric (T.history n) t
    (Fin.cast (congrArg (· + 1) R.count_eq) (Fin.last (T.observe (t : ℝ) hb0).eventCount)) (t : ℝ) hdom2
  have hfin : Fin.castLE (Nat.add_le_add_right
      (Nat.le_of_lt_succ ((T.history n).activeStage t).isLt) 1)
      (Fin.cast (congrArg (· + 1) R.count_eq) (Fin.last (T.observe (t : ℝ) hb0).eventCount)) =
      (T.history n).activeStage t := Fin.ext R.count_eq
  exact h1.trans (h2.trans (h3.trans (stageMetric_index_heq_S65 (T.history n) hfin (t : ℝ))))

end Bridge

section Lift

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- The survivor map of the active stage at `r`, transported to `postStage r`. -/
def liftMap_S65 (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
    (ordered : first ≤ last) (r : Icc (0 : ℝ) (F.tower.history n).horizon)
    (hf : first ≤ (F.tower.history n).toHistory.activeStage r)
    (hl : (F.tower.history n).toHistory.activeStage r ≤ last)
    (x : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered) :
    (postStage F.observation (r : ℝ)).Carrier :=
  cast (congrArg OrientedThreeStage.Carrier
    (postStage_eq_stage_active_CPD2 F.observation n r).symm)
    ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
      ((F.tower.history n).toHistory.activeStage r) hf hl x)

theorem liftMap_heq_S65 (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
    (ordered : first ≤ last) (r : Icc (0 : ℝ) (F.tower.history n).horizon)
    (hf : first ≤ (F.tower.history n).toHistory.activeStage r)
    (hl : (F.tower.history n).toHistory.activeStage r ≤ last)
    (x : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered) :
    HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
      ((F.tower.history n).toHistory.activeStage r) hf hl x)
      (liftMap_S65 (F := F) n first last ordered r hf hl x) :=
  (cast_heq _ _).symm

/-- `ckErr` of the transported lift equals `ckErr` of the survivor lift in the history stage. -/
theorem ckErr_liftMap_S65 (H : FiniteVolumeHyperbolicModel.{u}) (n : ℕ)
    (first last : Fin ((F.tower.history n).eventCount + 1))
    (ordered : first ≤ last) (r : Icc (0 : ℝ) (F.tower.history n).horizon)
    (hf : first ≤ (F.tower.history n).toHistory.activeStage r)
    (hl : (F.tower.history n).toHistory.activeStage r ≤ last)
    (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered)
    (c : ℝ) (j : ℕ) (p : H.Carrier) :
    ckErr_S45 H (postMetric F.observation (r : ℝ)) c
      (fun q => liftMap_S65 (F := F) n first last ordered r hf hl (φ q)) j p =
    ckErr_S45 H ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage r) (r : ℝ)) c
      (fun q => (F.tower.history n).toHistory.backwardSurvivorMap first last ordered
        ((F.tower.history n).toHistory.activeStage r) hf hl (φ q)) j p := by
  have h := postStage_eq_stage_active_CPD2 F.observation n r
  have := ckErr_cast_S65 H h.symm
    ((F.tower.history n).toHistory.stageMetric ((F.tower.history n).toHistory.activeStage r) (r : ℝ))
    (postMetric F.observation (r : ℝ)) (postMetric_heq_stageMetric_S65 F.observation n r).symm c
    (fun q => (F.tower.history n).toHistory.backwardSurvivorMap first last ordered
        ((F.tower.history n).toHistory.activeStage r) hf hl (φ q)) j p
  exact this.symm

end Lift

end GC.LongTime.Ch12
