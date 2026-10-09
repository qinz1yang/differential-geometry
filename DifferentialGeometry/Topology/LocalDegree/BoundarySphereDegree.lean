/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.Euclidean

open Set Metric

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

def IsolatingRadius.boundarySphereMap {f : E → E} (h : IsolatingRadius f 0 1)
    (hm : MapsTo f (sphere 0 1) (sphere 0 1)) : C(EuclideanSphere d, EuclideanSphere d) :=
  ⟨fun z => ⟨f z, hm z.2⟩,
    ((h.continuousOn.mono sphere_subset_closedBall).domRestrict).subtype_mk _⟩

theorem euclideanLocalDegree_eq_boundarySphereDegree {f : E → E}
    (h : IsolatingRadius f 0 1) (hm : MapsTo f (sphere 0 1) (sphere 0 1)) :
    euclideanLocalDegree f 0 ⟨1, h⟩ = euclideanSphereDegree (h.boundarySphereMap hm) := by
  erw [euclideanLocalDegree_eq_sphereDegree _ h ⟨1, by norm_num, le_rfl⟩]
  congr 1
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  rw [sphereMap_apply, zero_add, one_smul]
  change ‖f z‖⁻¹ • f z = f z
  rw [mem_sphere_zero_iff_norm.mp (hm z.2), inv_one, one_smul]

end DifferentialGeometry.LocalDegree
