import DifferentialGeometry.Geometry.Comparison.Toponogov.AngleKernel
import DifferentialGeometry.Topology.MetricSpace.TotallyBounded

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace DifferentialGeometry.Toponogov

variable {ι : Type*}

theorem AngleKernel.totallyBounded_iff_finset_angle_net (K : AngleKernel ι) :
    let _ := K.metricSpace
    TotallyBounded (univ : Set (Quotient K.setoid)) ↔
      ∀ eps > 0, ∃ A : Finset ι, ∀ i, ∃ a ∈ A, K.angle a i < eps := by
  classical
  let _ := K.metricSpace
  change TotallyBounded (univ : Set (Quotient K.setoid)) ↔ _
  rw [Metric.totallyBounded_univ_iff_finset_net]
  choose rep hrep using K.classOf_surjective
  constructor
  · intro h eps heps
    obtain ⟨S, hS⟩ := h eps heps
    refine ⟨S.image rep, fun i => ?_⟩
    obtain ⟨q, hq, hd⟩ := hS (K.classOf i)
    refine ⟨rep q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, ?_⟩
    have heq : K.angle (rep q) i = Dist.dist q (K.classOf i) := by
      change K.dist (K.classOf (rep q)) (K.classOf i) = _
      rw [hrep]
      rfl
    rw [heq, _root_.dist_comm]
    exact hd
  · intro h eps heps
    obtain ⟨A, hA⟩ := h eps heps
    refine ⟨A.image K.classOf, fun q => ?_⟩
    obtain ⟨i, rfl⟩ := K.classOf_surjective q
    obtain ⟨a, ha, hd⟩ := hA i
    refine ⟨K.classOf a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    rw [_root_.dist_comm]
    exact hd

end DifferentialGeometry.Toponogov
