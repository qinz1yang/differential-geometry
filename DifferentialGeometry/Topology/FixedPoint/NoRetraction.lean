/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereTopHomology
import Mathlib.Topology.Connected.TotallyDisconnected

open Metric Module

namespace DifferentialGeometry.Topology.FixedPoint

theorem not_exists_retraction_closedBall_sphere {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : 0 < finrank ℝ E) :
    ¬ ∃ r : closedBall (0 : E) 1 → sphere (0 : E) 1,
      Continuous r ∧ ∀ x : sphere (0 : E) 1,
        r ⟨x.1, sphere_subset_closedBall x.2⟩ = x := by
  rintro ⟨r, hr, hret⟩
  let : ContractibleSpace (closedBall (0 : E) 1) :=
    (convex_closedBall (0 : E) 1).contractibleSpace ⟨0, by simp⟩
  let i : C(sphere (0 : E) 1, closedBall (0 : E) 1) :=
    ⟨fun x ↦ ⟨x.1, sphere_subset_closedBall x.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  by_cases hdim : finrank ℝ E = 1
  · let v := unitSpherePointOfFinrankPos (E := E) hd
    let := oneDimUnitSphere_finite hdim v
    have h := TotallyDisconnectedSpace.eq_of_continuous r hr (i v) (i (-v))
    dsimp only [i, ContinuousMap.coe_mk] at h
    rw [hret v, hret (-v)] at h
    exact unitSphere_ne_antipode v h
  · let n := finrank ℝ E - 2
    have hn : finrank ℝ E = n + 2 := by omega
    let := integralSingularHomology_subsingleton_of_contractible (n + 1)
      (by omega) (closedBall (0 : E) 1)
    let p : C(closedBall (0 : E) 1, sphere (0 : E) 1) := ⟨r, hr⟩
    have hcomp : p.comp i = ContinuousMap.id (sphere (0 : E) 1) := by
      apply ContinuousMap.ext
      exact hret
    have hmap : (integralSingularHomologyMap (n + 1) p).comp
        (integralSingularHomologyMap (n + 1) i) = LinearMap.id := by
      rw [← integralSingularHomologyMap_comp, hcomp, integralSingularHomologyMap_id]
    have hleft : Function.LeftInverse (integralSingularHomologyMap (n + 1) p)
        (integralSingularHomologyMap (n + 1) i) :=
      fun a ↦ LinearMap.congr_fun hmap a
    let := hleft.injective.subsingleton
    let : Subsingleton ℤ := (integralSphereTopHomologyEquiv n E hn).symm.injective.subsingleton
    exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

end DifferentialGeometry.Topology.FixedPoint
