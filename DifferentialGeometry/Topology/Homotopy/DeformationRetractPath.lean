/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homotopy.DeformationRetract
import Mathlib.Topology.Homotopy.Path

namespace DifferentialGeometry.Topology.Homotopy

universe u

open ContinuousMap
open unitInterval

namespace StrongDeformationRetract

variable {X : Type u} [TopologicalSpace X] {A : Set X}

noncomputable def retractLoop (r : StrongDeformationRetract A) {x : X} (hx : x ∈ A)
    (ℓ : Path x x) : Path x x where
  toFun s := ((r.retraction (ℓ s) : A) : X)
  continuous_toFun :=
    (continuous_subtype_val.comp (map_continuous r.retraction)).comp (map_continuous ℓ)
  source' := by
    have h0 : ℓ 0 = x := ℓ.source
    change ((r.retraction (ℓ 0) : A) : X) = x
    rw [h0]
    exact r.retraction_eq hx
  target' := by
    have h1 : ℓ 1 = x := ℓ.target
    change ((r.retraction (ℓ 1) : A) : X) = x
    rw [h1]
    exact r.retraction_eq hx

theorem retractLoop_apply (r : StrongDeformationRetract A) {x : X} (hx : x ∈ A)
    (ℓ : Path x x) (s : I) : r.retractLoop hx ℓ s = ((r.retraction (ℓ s) : A) : X) := rfl

noncomputable def retractLoopHomotopy (r : StrongDeformationRetract A) {x : X} (hx : x ∈ A)
    (ℓ : Path x x) : Path.Homotopy ℓ (r.retractLoop hx ℓ) where
  toFun z := r.homotopy (z.1, ℓ z.2)
  continuous_toFun :=
    (map_continuous r.homotopy).comp (continuous_fst.prodMk ((map_continuous ℓ).comp
        continuous_snd))
  map_zero_left s := r.homotopy.apply_zero (ℓ s)
  map_one_left s := r.homotopy.apply_one (ℓ s)
  prop' := by
    intro t s hs
    have hsx : ℓ s = x := by
      rcases hs with rfl | rfl
      · exact ℓ.source
      · exact ℓ.target
    change r.homotopy (t, ℓ s) = ℓ s
    rw [hsx]
    exact r.homotopy_fixed_on t hx

theorem homotopic_retractLoop (r : StrongDeformationRetract A) {x : X} (hx : x ∈ A)
    (ℓ : Path x x) : ℓ.Homotopic (r.retractLoop hx ℓ) :=
  ⟨r.retractLoopHomotopy hx ℓ⟩

theorem retractLoop_mem (r : StrongDeformationRetract A) {x : X} (hx : x ∈ A)
    (ℓ : Path x x) (s : I) : r.retractLoop hx ℓ s ∈ A :=
  (r.retraction (ℓ s)).2

end StrongDeformationRetract

end DifferentialGeometry.Topology.Homotopy
