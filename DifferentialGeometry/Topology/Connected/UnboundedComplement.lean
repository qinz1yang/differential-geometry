/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.BallComplement

open Set Metric

namespace DifferentialGeometry.Topology

theorem IsCompact.exists_not_isBounded_connectedComponentIn_compl {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}
    (hK : IsCompact K) (hd : 1 < Module.rank ℝ E) :
    ∃ x ∉ K, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x) := by
  let _ : Nontrivial E := rank_pos_iff_nontrivial.mp (lt_trans zero_lt_one hd)
  obtain ⟨r, hKr⟩ := (isBounded_iff_subset_closedBall (0 : E)).mp hK.isBounded
  have hconn := (isPathConnected_compl_closedBall hd (0 : E) r).isConnected
  obtain ⟨x, hx⟩ := hconn.nonempty
  have hout : (closedBall (0 : E) r)ᶜ ⊆ Kᶜ := compl_subset_compl.mpr hKr
  have hcomponent : (closedBall (0 : E) r)ᶜ ⊆ connectedComponentIn Kᶜ x :=
    hconn.isPreconnected.subset_connectedComponentIn hx hout
  refine ⟨x, hout hx, ?_⟩
  intro hbounded
  have hbound : Bornology.IsBounded (closedBall (0 : E) r ∪ (closedBall (0 : E) r)ᶜ) :=
    isBounded_closedBall.union (hbounded.subset hcomponent)
  rw [union_compl_self] at hbound
  exact NormedSpace.unbounded_univ ℝ E hbound

end DifferentialGeometry.Topology
