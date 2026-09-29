import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition
import Mathlib.Topology.Covering.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry (SmoothRiemannianMetric)

universe u

structure RoundCovering (Z : Type u) [TopologicalSpace Z] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Z]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ Z] (k : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) Z) where
  cover : C((Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1), Z)
  cover_isCoveringMap : IsCoveringMap (cover : (Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1) → Z)
  isRound : ∀ x : Z, ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) ((Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)) Z ∞,
    x ∈ e.target ∧ ∀ y ∈ e.source, ∀ (V W : TangentSpace (𝓡 3) y),
      k.inner (e y) (mfderiv (𝓡 3) (𝓡 3) e y V) (mfderiv (𝓡 3) (𝓡 3) e y W) =
        (DifferentialGeometry.Geometry.roundMetric
          (E := EuclideanSpace ℝ (Fin 4)) (n := 3)).inner y V W

def sphereThreeBasePoint : (Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1) :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

def RoundCovering.degree {Z : Type u} [TopologicalSpace Z] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Z]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ Z] {k : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) Z}
    (C : RoundCovering Z k) : ℕ :=
  (C.cover ⁻¹' {C.cover sphereThreeBasePoint}).ncard

theorem RoundCovering.degree_eq_one_of_injective {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Z] [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ Z]
    {k : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) Z} (C : RoundCovering Z k)
    (h : Function.Injective C.cover) : C.degree = 1 := by
  rw [RoundCovering.degree, Set.ncard_eq_one]
  refine ⟨sphereThreeBasePoint, ?_⟩
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨rfl, ?_⟩
  intro y hy
  exact h hy

def HasBoundedRoundCoveringDegree (Nold : ℕ) : Prop :=
  ∀ (Z : Type u) [TopologicalSpace Z] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Z] [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ Z]
    (k : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) Z),
    Nonempty (RoundCovering Z k) →
      ∃ C : RoundCovering Z k, 1 ≤ C.degree ∧ C.degree ≤ Nold

structure UnboundedRoundCoveringDegreeWitness (N : ℕ) where
  Z : Type u
  [topology : TopologicalSpace Z]
  [charts : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Z]
  [smooth : IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ Z]
  metric : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) Z
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

noncomputable def standardRoundCovering : RoundCovering ((Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1))
    (DifferentialGeometry.Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) where
  cover := ContinuousMap.id ((Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1))
  cover_isCoveringMap :=
    isLocalHomeomorph_iff_isCoveringMap.mp
      (Homeomorph.isLocalHomeomorph (Homeomorph.refl ((Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1))))
  isRound := by
    intro x
    refine ⟨PartialDiffeomorph.refl (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) ((Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)), Set.mem_univ x, ?_⟩
    intro y _ V W
    simp only [PartialDiffeomorph.refl, PartialEquiv.refl_coe, mfderiv_id]
    rfl

theorem standardRoundCovering_degree : standardRoundCovering.degree = 1 := by
  rw [RoundCovering.degree]
  simp [standardRoundCovering]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
