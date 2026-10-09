/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

theorem exists_dist_lt_image_interior_stable_of_isPLCellOn {S B Kc : Set M₁} {F : M₁ → M₂}
    (hS : IsPLCellOn 3 S B) (hFc : ContinuousOn F S) (hFi : InjOn F S) (hK : IsCompact Kc)
    (hKS : Kc ⊆ S \ B) :
    ∃ δ > 0, ∀ G : M₁ → M₂, IsPLHomeomorphInto 3 G S → (∀ z ∈ S, dist (F z) (G z) < δ) →
      F '' Kc ⊆ interior (G '' S) := by
  classical
  have hloc : LocallyConnectedSpace M₂ :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M₂
  have hKsub : Kc ⊆ S := fun x hx => (hKS hx).1
  have hWopen : IsOpen (F '' (S \ B)) := by
    rw [hS.sdiff_boundary_eq_interior]
    exact isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) isOpen_interior
      (hFc.mono interior_subset) (hFi.mono interior_subset)
  have hsep : ∀ z ∈ B, F z ∉ F '' (S \ B) := by
    rintro z hz ⟨y, hy, hyz⟩
    have hyz' : y = z := hFi hy.1 (hS.boundary_subset hz) hyz
    subst hyz'
    exact hy.2 hz
  have key : ∀ x : M₁, ∃ (V : Set M₂) (d : ℝ), x ∈ Kc →
      IsOpen V ∧ IsPreconnected V ∧ Metric.ball (F x) d ⊆ V ∧ 0 < d ∧
        ∀ v ∈ V, ∀ z ∈ B, d ≤ dist v (F z) := by
    intro x
    by_cases hx : x ∈ Kc
    · obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hWopen (F x) ⟨x, hKS hx, rfl⟩
      have hVopen : IsOpen (connectedComponentIn (Metric.ball (F x) (r / 4)) (F x)) :=
        Metric.isOpen_ball.connectedComponentIn
      have hmem : F x ∈ connectedComponentIn (Metric.ball (F x) (r / 4)) (F x) :=
        mem_connectedComponentIn (Metric.mem_ball_self (by linarith))
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hVopen (F x) hmem
      refine ⟨connectedComponentIn (Metric.ball (F x) (r / 4)) (F x), min ρ (r / 4), fun _ =>
        ⟨hVopen, isPreconnected_connectedComponentIn,
          (Metric.ball_subset_ball (min_le_left _ _)).trans hρsub, lt_min hρ (by linarith), ?_⟩⟩
      intro v hv z hz
      have hvb : dist (F x) v < r / 4 := by
        rw [dist_comm]
        exact Metric.mem_ball.mp (connectedComponentIn_subset _ _ hv)
      have hfar : r ≤ dist (F z) (F x) := by
        by_contra hcon
        exact hsep z hz (hrsub (Metric.mem_ball.mpr (not_le.mp hcon)))
      have htri : dist (F z) (F x) ≤ dist (F z) v + dist v (F x) := dist_triangle _ _ _
      have hcomm : dist v (F x) = dist (F x) v := dist_comm _ _
      have hgoal : dist v (F z) = dist (F z) v := dist_comm _ _
      have hmin : min ρ (r / 4) ≤ r / 4 := min_le_right _ _
      rw [hgoal]
      linarith
    · exact ⟨∅, 0, fun hx' => absurd hx' hx⟩
  choose V d hVd using key
  have hcover : F '' Kc ⊆ ⋃ x ∈ Kc, V x := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_iUnion₂.mpr ⟨x, hx,
      (hVd x hx).2.2.1 (Metric.mem_ball_self (hVd x hx).2.2.2.1)⟩
  obtain ⟨b, hbK, hbfin, hbcover⟩ :=
    (hK.image_of_continuousOn (hFc.mono hKsub)).elim_finite_subcover_image
      (fun x hx => (hVd x hx).1) hcover
  have hδpos : 0 < (insert (1 : ℝ) (hbfin.toFinset.image d)).min'
      (Finset.insert_nonempty _ _) := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact one_pos
    · obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hy'
      exact (hVd x (hbK (hbfin.mem_toFinset.mp hxT))).2.2.2.1
  have hδle : ∀ x ∈ b, (insert (1 : ℝ) (hbfin.toFinset.image d)).min'
      (Finset.insert_nonempty _ _) ≤ d x := fun x hx =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem d (hbfin.mem_toFinset.mpr hx)))
  refine ⟨_, hδpos, fun G hG hclose => ?_⟩
  have hGI : G '' (S \ B) = interior (G '' S) := (hS.image_boundary_interior hG).2
  have hGclosed : IsClosed (G '' S) :=
    (hS.isCompact.image_of_continuousOn hG.continuousOn).isClosed
  have hkey : ∀ x ∈ b, V x ⊆ interior (G '' S) := by
    intro x hxb
    have hxK : x ∈ Kc := hbK hxb
    obtain ⟨hVopen, hVconn, hball, hdpos, hmargin⟩ := hVd x hxK
    refine hVconn.subset_left_of_subset_union isOpen_interior hGclosed.isOpen_compl
      (Disjoint.mono_left interior_subset disjoint_compl_right) (fun v hv => ?_) ?_
    · by_cases hvS : v ∈ G '' S
      · refine Or.inl ?_
        obtain ⟨z, hzS, rfl⟩ := hvS
        rw [← hGI]
        refine ⟨z, ⟨hzS, fun hzB => ?_⟩, rfl⟩
        have h2 : d x ≤ dist (G z) (F z) := hmargin _ hv z hzB
        rw [dist_comm] at h2
        linarith [hδle x hxb, hclose z hzS]
      · exact Or.inr hvS
    · refine ⟨G x, hball (Metric.mem_ball.mpr ?_), ?_⟩
      · rw [dist_comm]
        exact lt_of_lt_of_le (hclose x (hKsub hxK)) (hδle x hxb)
      · rw [← hGI]
        exact ⟨x, hKS hxK, rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨x₀, hx₀, hmem⟩ := mem_iUnion₂.mp (hbcover ⟨x, hx, rfl⟩)
  exact hkey x₀ hx₀ hmem

end DifferentialGeometry.Topology.PiecewiseLinear
