import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.MetricStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.StepInputFrontierAudit
import Mathlib.Topology.Covering.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry (SmoothRiemannianMetric)

universe u

structure UnboundedRoundCoveringDegreeWitness (N : ℕ) where
  Z : Type u
  [topology : TopologicalSpace Z]
  [charts : ChartedSpace ThreeSpace Z]
  [smooth : IsManifold ThreeModel ∞ Z]
  metric : SmoothRiemannianMetric ThreeModel Z
  covering : RoundCovering Z metric
  unbounded : ∀ C : RoundCovering Z metric, N < C.degree

attribute [instance] UnboundedRoundCoveringDegreeWitness.topology
  UnboundedRoundCoveringDegreeWitness.charts UnboundedRoundCoveringDegreeWitness.smooth

def HasRoundCoveringsOfUnboundedDegree : Prop :=
  ∀ N : ℕ, Nonempty (UnboundedRoundCoveringDegreeWitness.{u} N)

theorem not_hasBoundedRoundCoveringDegree_of_hasRoundCoveringsOfUnboundedDegree
    (hunb : HasRoundCoveringsOfUnboundedDegree.{u}) (Nold : ℕ) :
    ¬ HasBoundedRoundCoveringDegree.{u} Nold := by
  intro hb
  obtain ⟨W⟩ := hunb Nold
  obtain ⟨C, _h1, hle⟩ := hb W.Z W.metric ⟨W.covering⟩
  exact absurd (W.unbounded C) (not_lt.mpr hle)

theorem not_isRoundDegreeInput_of_hasRoundCoveringsOfUnboundedDegree
    (hne : ∃ H : ObservedHistory.{u}, Nonempty (EnlargementStrip H))
    (hunb : HasRoundCoveringsOfUnboundedDegree.{u}) : ¬ isRoundDegreeInput.{u} := by
  intro h
  obtain ⟨H, ⟨S⟩⟩ := hne
  obtain ⟨Nold, _hNold, hcover⟩ := h
    ({ horizon := 1, horizon_pos := one_pos, initialParameter := 1
       initialParameter_pos := one_pos, epsilon := 1, epsilon_pos := one_pos
       comparisonConstant := 1, comparisonConstant_pos := one_pos, volumeConstant := 1
       volumeConstant_pos := one_pos, scaleLower := 1, scaleLower_pos := one_pos
       noncollapsing := 1, noncollapsing_pos := one_pos, olderLength := 1
       olderLength_pos := one_pos, energyBound := 1, olderLength_le_energy := le_rfl } : OldData)
  obtain ⟨W⟩ := hunb Nold
  obtain ⟨C, _h1, hle⟩ := hcover H S W.Z W.metric ⟨W.covering⟩
  exact absurd (W.unbounded C) (not_lt.mpr hle)

structure SelectedRoundSource where
  Z : Type u
  [topology : TopologicalSpace Z]
  [charts : ChartedSpace ThreeSpace Z]
  [smooth : IsManifold ThreeModel ∞ Z]
  metric : SmoothRiemannianMetric ThreeModel Z
  covering : RoundCovering Z metric

attribute [instance] SelectedRoundSource.topology SelectedRoundSource.charts
  SelectedRoundSource.smooth

def SelectedRoundSource.degree (X : SelectedRoundSource.{u}) : ℕ :=
  @RoundCovering.degree X.Z X.topology X.charts X.smooth X.metric X.covering

def isRoundDegreeInputForChosenSource
    (sel : ∀ (H : ObservedHistory.{u}) (_S : EnlargementStrip H),
      SelectedRoundSource.{u}) : Prop :=
  ∃ Nold : ℕ, 1 ≤ Nold ∧ ∀ H S, 1 ≤ (sel H S).degree ∧ (sel H S).degree ≤ Nold

theorem degreeBound_of_isRoundDegreeInputForChosenSource
    {sel : ∀ (H : ObservedHistory.{u}) (_S : EnlargementStrip H), SelectedRoundSource.{u}}
    (h : isRoundDegreeInputForChosenSource.{u} sel) (H : ObservedHistory.{u})
    (S : EnlargementStrip H) :
    ∃ Nold : ℕ, 1 ≤ Nold ∧ 1 ≤ (sel H S).degree ∧ (sel H S).degree ≤ Nold := by
  obtain ⟨Nold, hNold, hbound⟩ := h
  exact ⟨Nold, hNold, hbound H S⟩

def UniformDegreeBoundForEverySelection : Prop :=
  ∃ Nold : ℕ, 1 ≤ Nold ∧
    ∀ sel : ∀ (H : ObservedHistory.{u}) (_S : EnlargementStrip H), SelectedRoundSource.{u},
      ∀ H S, 1 ≤ (sel H S).degree ∧ (sel H S).degree ≤ Nold

theorem isRoundDegreeInput_of_uniformDegreeBoundForEverySelection
    (h : UniformDegreeBoundForEverySelection.{u}) : isRoundDegreeInput.{u} := by
  obtain ⟨Nold, hNold, hbound⟩ := h
  intro _d
  refine ⟨Nold, hNold, fun H S Z => ?_⟩
  intro instT instC instM k hne
  let X : SelectedRoundSource.{u} :=
    { Z := Z
      topology := instT
      charts := instC
      smooth := instM
      metric := k
      covering := Classical.choice hne }
  have hb := hbound (fun _ _ => X) H S
  refine ⟨Classical.choice hne, ?_, ?_⟩
  · simpa [SelectedRoundSource.degree, X] using hb.1
  · simpa [SelectedRoundSource.degree, X] using hb.2

theorem not_uniformDegreeBoundForEverySelection_of_hasRoundCoveringsOfUnboundedDegree
    (hne : ∃ H : ObservedHistory.{u}, Nonempty (EnlargementStrip H))
    (hunb : HasRoundCoveringsOfUnboundedDegree.{u}) :
    ¬ UniformDegreeBoundForEverySelection.{u} := by
  rintro ⟨Nold, _hNold, hbound⟩
  obtain ⟨H, ⟨S⟩⟩ := hne
  obtain ⟨W⟩ := hunb Nold
  let X : SelectedRoundSource.{u} :=
    { Z := W.Z
      topology := W.topology
      charts := W.charts
      smooth := W.smooth
      metric := W.metric
      covering := W.covering }
  have hb := hbound (fun _ _ => X) H S
  have hdeg : X.degree = W.covering.degree := rfl
  exact absurd (W.unbounded W.covering) (not_lt.mpr (hdeg ▸ hb.2))

noncomputable def standardRoundCovering : RoundCovering (Sphere 3)
    (DifferentialGeometry.Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) where
  cover := ContinuousMap.id (Sphere 3)
  cover_isCoveringMap :=
    isLocalHomeomorph_iff_isCoveringMap.mp
      (Homeomorph.isLocalHomeomorph (Homeomorph.refl (Sphere 3)))
  isRound := by
    intro x
    refine ⟨PartialDiffeomorph.refl (I := ThreeModel) (Sphere 3), Set.mem_univ x, ?_⟩
    intro y _ V W
    simp only [PartialDiffeomorph.refl, PartialEquiv.refl_coe, mfderiv_id]
    rfl

theorem standardRoundCovering_degree : standardRoundCovering.degree = 1 := by
  rw [RoundCovering.degree]
  simp [standardRoundCovering]

noncomputable def standardSelectedRoundSource : SelectedRoundSource.{0} where
  Z := Sphere 3
  topology := inferInstance
  charts := inferInstance
  smooth := inferInstance
  metric := DifferentialGeometry.Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)
  covering := standardRoundCovering

theorem standardSelectedRoundSource_degree : standardSelectedRoundSource.degree = 1 := by
  rw [SelectedRoundSource.degree, standardSelectedRoundSource]
  exact standardRoundCovering_degree

theorem nonempty_selectedRoundSource_zero : Nonempty (SelectedRoundSource.{0}) :=
  ⟨standardSelectedRoundSource⟩

noncomputable def standardSelection :
    ∀ (H : ObservedHistory.{0}) (_S : EnlargementStrip H), SelectedRoundSource.{0} :=
  fun _ _ => standardSelectedRoundSource

theorem isRoundDegreeInputForChosenSource_standardSelection :
    isRoundDegreeInputForChosenSource.{0} standardSelection :=
  ⟨1, le_rfl, fun _ _ => by
    rw [standardSelection, standardSelectedRoundSource_degree]
    exact ⟨le_rfl, le_rfl⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
