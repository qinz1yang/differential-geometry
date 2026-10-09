import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.RegularSlice
import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskArea

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.MinimalSurface
open scoped Manifold ContDiff

namespace GC.LongTime

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

def postStage (O : ObservationTower P g) (t : ℝ) : OrientedThreeStage.{u} :=
  (O.observe (max t 0) (le_max_right t 0)).stage
    (Fin.last (O.observe (max t 0) (le_max_right t 0)).eventCount)

def postMetric (O : ObservationTower P g) (t : ℝ) : (postStage O t).Metric :=
  (O.observe (max t 0) (le_max_right t 0)).stageMetric
    (Fin.last (O.observe (max t 0) (le_max_right t 0)).eventCount) (max t 0)

theorem postStage_regularSlice (O : ObservationTower P g) (s : RegularSlice O) :
    postStage O s.time = s.stage := by
  have htime : max s.time 0 = s.time := max_eq_left s.positive.le
  have hobs : O.observe (max s.time 0) (le_max_right s.time 0) =
      O.observe s.time s.positive.le := by
    have hsub : (⟨max s.time 0, le_max_right s.time 0⟩ : {t : ℝ // 0 ≤ t}) =
        ⟨s.time, s.positive.le⟩ := Subtype.ext htime
    exact congrArg (fun t : {t : ℝ // 0 ≤ t} => O.observe t.val t.property)
      hsub
  exact congrArg (fun H : ObservedHistory => H.stage (Fin.last H.eventCount)) hobs

theorem postMetric_regularSlice (O : ObservationTower P g) (s : RegularSlice O) :
    HEq (postMetric O s.time) s.metric := by
  have htime : max s.time 0 = s.time := max_eq_left s.positive.le
  have hobs : O.observe (max s.time 0) (le_max_right s.time 0) =
      O.observe s.time s.positive.le := by
    have hsub : (⟨max s.time 0, le_max_right s.time 0⟩ : {t : ℝ // 0 ≤ t}) =
        ⟨s.time, s.positive.le⟩ := Subtype.ext htime
    exact congrArg (fun t : {t : ℝ // 0 ≤ t} => O.observe t.val t.property)
      hsub
  have hmetric : ∀ {H H' : ObservedHistory}, H = H' → ∀ t : ℝ,
      HEq (H.stageMetric (Fin.last H.eventCount) t)
        (H'.stageMetric (Fin.last H'.eventCount) t) := by
    intro H H' h t
    cases h
    rfl
  exact (heq_of_eq (congrArg
    (fun t => (O.observe (max s.time 0) (le_max_right s.time 0)).stageMetric
      (Fin.last (O.observe (max s.time 0) (le_max_right s.time 0)).eventCount) t)
    htime)).trans (hmetric hobs s.time)

def exteriorDiskArea (O : ObservationTower P g)
    (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) : ℝ → ℝ :=
  exteriorDiskAreaOn (fun t => (postStage O t).Carrier) (postMetric O) W T γ

theorem exteriorDiskArea_nonneg (O : ObservationTower P g)
    (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) (t : ℝ) :
    0 ≤ exteriorDiskArea O W T γ t :=
  exteriorDiskAreaOn_nonneg (fun t => (postStage O t).Carrier) (postMetric O) W T γ t

theorem exteriorDiskArea_eq (O : ObservationTower P g)
    (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier)
    (t : ℝ) (ht : T ≤ t) :
    exteriorDiskArea O W T γ t =
      leastExteriorDiskArea (postMetric O t) (W t) (γ t ht) := by
  simp only [exteriorDiskArea, exteriorDiskAreaOn, dif_pos ht]

def hasExteriorDiskMinimizersAfter (O : ObservationTower P g)
    (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) : Prop :=
  ∀ (t : ℝ) (ht : T ≤ t), ∃ u : C(closedDisk, (postStage O t).Carrier),
    isExteriorSpanningDisk (W t) (γ t ht) u ∧
    DifferentialGeometry.Geometry.riemannianDiskArea (postMetric O t) u =
      exteriorDiskArea O W T γ t

end GC.LongTime
