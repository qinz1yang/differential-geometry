import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.MetricStep
import Mathlib.Topology.Covering.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry (SmoothRiemannianMetric)

universe u

def HasBoundedRoundCoveringDegree (Nold : ℕ) : Prop :=
  ∀ (Z : Type u) [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold ThreeModel ∞ Z]
    (k : SmoothRiemannianMetric ThreeModel Z),
    Nonempty (RoundCovering Z k) →
      ∃ C : RoundCovering Z k, 1 ≤ C.degree ∧ C.degree ≤ Nold

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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
