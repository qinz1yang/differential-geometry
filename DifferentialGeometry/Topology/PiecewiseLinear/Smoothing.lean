/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartGluing
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import Mathlib.Geometry.Manifold.Instances.Real

open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def PLSmoothing (n : ℕ) : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    (C : ChartedSpace (EuclideanSpace ℝ (Fin n)) X),
    (letI := C; HasGroupoid X (plGroupoid n)) →
    ∃ C' : ChartedSpace (EuclideanSpace ℝ (Fin n)) X,
      letI := C'
      IsManifold (𝓡 n) ∞ X

def PLSmoothingModel (n : ℕ) : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    (C : ChartedSpace (EuclideanSpace ℝ (Fin n)) X),
    (letI := C; HasGroupoid X (plGroupoid n)) →
    ∃ (N : Type u) (_ : TopologicalSpace N) (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N),
      IsManifold (𝓡 n) ∞ N ∧ Nonempty (X ≃ₜ N)

theorem plSmoothing_of_plSmoothingModel {n : ℕ} (h : PLSmoothingModel.{u} n) :
    PLSmoothing.{u} n := by
  intro X _ _ _ C hC
  obtain ⟨N, _, _, hN, ⟨e⟩⟩ := h C hC
  exact ⟨DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace e,
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 n) (n := ∞) e⟩

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem exists_isManifold_of_plApproximation_of_plSmoothing (hA : PLApproximation.{u} n)
    (hB : PLSmoothing.{u} n) :
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin n)) X,
      letI := C
      IsManifold (𝓡 n) ∞ X := by
  have hsc : SecondCountableTopology X :=
    ChartedSpace.secondCountable_of_sigmaCompact (H := EuclideanSpace ℝ (Fin n)) (M := X)
  obtain ⟨C, hC⟩ := exists_chartedSpace_hasGroupoid_plGroupoid_of_plApproximation (X := X) hA
  exact hB C hC

theorem plSmoothing_zero : PLSmoothing.{u} 0 := by
  intro Y _ _ _ C _
  refine ⟨C, ?_⟩
  let _ := C
  have hsub : Subsingleton (EuclideanSpace ℝ (Fin 0)) :=
    (WithLp.equiv 2 (Fin 0 → ℝ)).subsingleton
  exact { compatible := fun _ _ =>
    mem_groupoid_of_pregroupoid.mpr ⟨contDiffOn_of_subsingleton, contDiffOn_of_subsingleton⟩ }

theorem exists_isManifold_zero {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] :
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 0)) M,
      letI := C
      IsManifold (𝓡 0) ∞ M :=
  exists_isManifold_of_plApproximation_of_plSmoothing plApproximation_zero plSmoothing_zero

theorem exists_isManifold_three_of_plApproximation_of_plSmoothing {M : Type u}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (hA : PLApproximation.{u} 3)
    (hB : PLSmoothing.{u} 3) :
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := C
      IsManifold (𝓡 3) ∞ M :=
  exists_isManifold_of_plApproximation_of_plSmoothing hA hB

end DifferentialGeometry.Topology.PiecewiseLinear
