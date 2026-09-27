import DifferentialGeometry.Geometry.Metric.Distance.Basic
import DifferentialGeometry.Topology.FirstExit
import Mathlib.Geometry.Manifold.Riemannian.Basic

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianEDistOf_ball_subset_of_le_frontier_distance
    (g : SmoothRiemannianMetric I M) {A : Set M} {p : M}
    (hp : p ∈ interior A) {r : ℝ≥0∞}
    (hfront : ∀ q ∈ frontier A, r ≤ riemannianEDistOf g p q) :
    {y | riemannianEDistOf g p y < r} ⊆ interior A := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro y hy
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ := exists_lt_of_riemannianEDist_lt hy
  by_contra hyA
  obtain ⟨t, ht, _, hboundary⟩ :=
    exists_first_exit_frontier_of_not_mem_interior zero_lt_one hγ.continuousOn
      (hγ0 ▸ hp) (hγ1 ▸ hyA)
  have hprefix : riemannianEDistOf g p (γ t) ≤ pathELength I γ 0 t :=
    riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl ht.2))
      hγ0 rfl ht.1.le
  exact (not_lt_of_ge (hfront (γ t) hboundary))
    (hprefix.trans_lt ((pathELength_mono le_rfl ht.2).trans_lt hlength))

theorem riemannianEDistOf_closedBall_subset_of_le_frontier_distance [RegularSpace M]
    (g : SmoothRiemannianMetric I M) {A : Set M} (hA : IsClosed A) {p : M}
    (hp : p ∈ interior A) {r : ℝ≥0∞} (hr : r ≠ ⊤)
    (hfront : ∀ q ∈ frontier A, r ≤ riemannianEDistOf g p q) :
    {y | riemannianEDistOf g p y ≤ r} ⊆ A := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  intro y hy
  by_contra hyA
  obtain ⟨c, hc, hball⟩ :=
    setOfPred_riemannianEDist_lt_subset_nhds I (hA.isOpen_compl.mem_nhds hyA)
  have hshort : riemannianEDist I p y < r + c :=
    hy.trans_lt (ENNReal.lt_add_right hr (by exact_mod_cast hc.ne'))
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ := exists_lt_of_riemannianEDist_lt hshort
  obtain ⟨t, ht, _, hboundary⟩ :=
    exists_first_exit_frontier hA zero_lt_one hγ.continuousOn
      (hγ0 ▸ hp) (hγ1 ▸ hyA)
  have hleft : r ≤ pathELength I γ 0 t :=
    (hfront (γ t) hboundary).trans
      (riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl ht.2))
        hγ0 rfl ht.1.le)
  have hright : (c : ℝ≥0∞) ≤ pathELength I γ t 1 := by
    have hfar : (c : ℝ≥0∞) ≤ riemannianEDist I y (γ t) := by
      apply le_of_not_gt
      intro hlt
      exact hball hlt (hA.closure_eq ▸ frontier_subset_closure hboundary)
    rw [riemannianEDist_comm] at hfar
    exact hfar.trans
      (riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc ht.1.le le_rfl))
        rfl hγ1 ht.2)
  have htotal := add_le_add hleft hright
  rw [pathELength_add ht.1.le ht.2] at htotal
  exact (not_lt_of_ge htotal) hlength

end DifferentialGeometry.Geometry.Metric
