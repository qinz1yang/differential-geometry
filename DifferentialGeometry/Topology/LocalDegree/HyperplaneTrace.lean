/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.HalfSpaceOpen

open Set

noncomputable section

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))
local notation "E'" => EuclideanSpace ℝ (Fin ((d + 1) + 1))

def euclideanHyperplaneSource (U : Set E') : Set E :=
  (fun x => euclideanProductPoint d x 0) ⁻¹' U

def euclideanHyperplaneTrace (F : E' → E') (x : E) : E :=
  (euclideanProductChart d (F (euclideanProductPoint d x 0))).1

private theorem hyperplane_inclusion_coordinates (x : E) :
    euclideanProductChart d (euclideanProductPoint d x 0) = (x, 0) :=
  (euclideanProductChart d).apply_symm_apply (x, 0)

private theorem continuous_hyperplane_inclusion :
    Continuous (fun x : E => euclideanProductPoint d x 0) :=
  (euclideanProductChart d).symm.continuous.comp (continuous_id.prodMk continuous_const)

theorem isOpen_euclideanHyperplaneSource {U : Set E'} (hU : IsOpen U) :
    IsOpen (euclideanHyperplaneSource U) :=
  hU.preimage continuous_hyperplane_inclusion

theorem continuousOn_euclideanHyperplaneTrace {U : Set E'} {F : E' → E'}
    (hF : ContinuousOn F U) :
    ContinuousOn (euclideanHyperplaneTrace F) (euclideanHyperplaneSource U) :=
  continuous_fst.comp_continuousOn ((euclideanProductChart d).continuous.comp_continuousOn
    (hF.comp continuous_hyperplane_inclusion.continuousOn (fun _ hx => hx)))

theorem injOn_euclideanHyperplaneTrace {U : Set E'} {F : E' → E'} (hFi : InjOn F U)
    (hplane : ∀ y ∈ U, (euclideanProductChart d y).2 = 0 →
      (euclideanProductChart d (F y)).2 = 0) :
    InjOn (euclideanHyperplaneTrace F) (euclideanHyperplaneSource U) := by
  intro x hx y hy hxy
  have hx0 : (euclideanProductChart d (euclideanProductPoint d x 0)).2 = 0 := by
    rw [hyperplane_inclusion_coordinates]
  have hy0 : (euclideanProductChart d (euclideanProductPoint d y 0)).2 = 0 := by
    rw [hyperplane_inclusion_coordinates]
  have hFxy : F (euclideanProductPoint d x 0) = F (euclideanProductPoint d y 0) :=
    (euclideanProductChart d).injective
      (Prod.ext hxy ((hplane _ hx hx0).trans (hplane _ hy hy0).symm))
  have hxy' := congrArg (fun z => (euclideanProductChart d z).1) (hFi hx hy hFxy)
  simpa only [hyperplane_inclusion_coordinates] using hxy'

theorem euclideanHyperplaneTrace_spec {U : Set E'} {F : E' → E'}
    (hplane : ∀ y ∈ U, (euclideanProductChart d y).2 = 0 →
      (euclideanProductChart d (F y)).2 = 0)
    {y : E'} (hy : y ∈ U) (hy0 : (euclideanProductChart d y).2 = 0) :
    F y = euclideanProductPoint d
      (euclideanHyperplaneTrace F (euclideanProductChart d y).1) 0 := by
  have hlift : euclideanProductPoint d (euclideanProductChart d y).1 0 = y := by
    apply (euclideanProductChart d).injective
    rw [hyperplane_inclusion_coordinates]
    exact Prod.ext rfl hy0.symm
  unfold euclideanHyperplaneTrace
  rw [hlift]
  change F y = (euclideanProductChart d).symm ((euclideanProductChart d (F y)).1, 0)
  rw [← hplane y hy hy0]
  exact ((euclideanProductChart d).symm_apply_apply (F y)).symm

theorem zero_mem_euclideanHyperplaneSource {U : Set E'} (h0 : (0 : E') ∈ U) :
    (0 : E) ∈ euclideanHyperplaneSource U := by
  change euclideanProductPoint d 0 0 ∈ U
  simpa [euclideanProductPoint] using h0

theorem embeddingOrientationParity_hyperplaneTrace
    {U : Set E'} {F : E' → E'} (hU : IsOpen U)
    (hF : ContinuousOn F U) (hFi : InjOn F U) (hU0 : (0 : E') ∈ U) (hF0 : F 0 = 0)
    (hplane : ∀ y ∈ U, (euclideanProductChart d y).2 = 0 →
      (euclideanProductChart d (F y)).2 = 0)
    (hpos : ∀ y ∈ U, 0 < (euclideanProductChart d y).2 →
      0 < (euclideanProductChart d (F y)).2)
    (hneg : ∀ y ∈ U, (euclideanProductChart d y).2 < 0 →
      (euclideanProductChart d (F y)).2 < 0) :
    embeddingOrientationParity hU hF hFi ⟨0, hU0⟩ =
      embeddingOrientationParity (isOpen_euclideanHyperplaneSource hU)
        (continuousOn_euclideanHyperplaneTrace hF) (injOn_euclideanHyperplaneTrace hFi hplane)
        ⟨0, zero_mem_euclideanHyperplaneSource hU0⟩ := by
  have hzero : euclideanHyperplaneTrace F (0 : E) = 0 := by
    unfold euclideanHyperplaneTrace
    simp only [show euclideanProductPoint d 0 0 = 0 by simp [euclideanProductPoint], hF0, map_zero]
    rfl
  exact embeddingOrientationParity_eq_of_preserves_halfspaces
    (isOpen_euclideanHyperplaneSource hU) hU (continuousOn_euclideanHyperplaneTrace hF)
    (injOn_euclideanHyperplaneTrace hFi hplane) hF hFi
    (zero_mem_euclideanHyperplaneSource hU0) hU0 hzero hF0
    (fun _ hy hy0 => euclideanHyperplaneTrace_spec hplane hy hy0) hpos hneg

end DifferentialGeometry.LocalDegree
