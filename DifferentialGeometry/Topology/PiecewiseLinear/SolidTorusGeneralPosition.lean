/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section RelativeGeneralPosition

def Fits (A U S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  IsCombinatorialSolidTorus S ∧ A ⊆ interior S ∧ S ⊆ U

def PairGP (R S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (∀ x ∈ frontier R ∩ frontier S, HasPLCrossingAt (frontier R) (frontier S) x) ∧
    ∃ (ι : Type) (_ : Finite ι) (G : ι → Set (EuclideanSpace ℝ (Fin 3))),
      (∀ i, IsPLSphere 1 (G i)) ∧ (Pairwise fun i i' => Disjoint (G i) (G i')) ∧
        frontier R ∩ frontier S = ⋃ i, G i

theorem PairGP.symm {R S : Set (EuclideanSpace ℝ (Fin 3))} (h : PairGP R S) : PairGP S R := by
  obtain ⟨hcross, ι, hι, G, hG, hdisj, heq⟩ := h
  refine ⟨fun x hx => ?_, ι, hι, G, hG, hdisj, ?_⟩
  · rw [inter_comm] at hx
    exact (hcross x hx).symm
  · rw [inter_comm]
    exact heq

end RelativeGeneralPosition

end DifferentialGeometry.Topology.PiecewiseLinear
