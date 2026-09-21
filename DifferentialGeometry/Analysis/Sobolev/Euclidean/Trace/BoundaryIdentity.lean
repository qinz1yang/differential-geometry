import DifferentialGeometry.Analysis.Sobolev.Euclidean.Trace.BoundaryApproach
import DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk

section

noncomputable section

open Filter MeasureTheory
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem disk_boundary_eq_of_lipschitz_sequence_energy_bound
    (f : ℕ → ℂ → E) (q : C(Topology.closedDisk, E)) (η : ℂ → E) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n))
    (hae : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      Tendsto (fun n => f n z) atTop (𝓝 (Geometry.diskExtension q z)))
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → Tendsto (fun n => f n z) atTop (𝓝 (η z)))
    (hη : ContinuousOn η (Metric.sphere (0 : ℂ) 1))
    {B : ℝ} (henergy : ∀ n,
      (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (f n) z‖ ^ 2) ≤ B) :
    ∀ p (hp : p ∈ Metric.sphere (0 : ℂ) 1),
      q ⟨p, Metric.sphere_subset_closedBall hp⟩ = η p := by
  have hq : Continuous (Geometry.diskExtension q) :=
    q.continuous.comp Geometry.diskRetraction_lipschitz.continuous
  intro p hp
  have heq : Geometry.diskExtension q p = η p := by
    apply eq_of_forall_dist_le
    intro ε hε
    obtain ⟨R, hR, hclose⟩ := Metric.continuousAt_iff.mp (hq.continuousAt (x := p))
      (ε / 2) (half_pos hε)
    obtain ⟨z, _, hzp, hzη⟩ :=
      exists_interior_boundary_approach_of_lipschitz_sequence_energy_bound
        f (Geometry.diskExtension q) η K hf hq.continuousOn hae hboundary hη henergy
        p hp (ε / 2) (half_pos hε) R hR
    have hqz : dist (Geometry.diskExtension q p) (Geometry.diskExtension q z) < ε / 2 := by
      rw [dist_comm]
      exact hclose hzp
    exact (dist_triangle (Geometry.diskExtension q p) (Geometry.diskExtension q z) (η p)).trans
      ((add_lt_add hqz hzη).trans_eq (add_halves ε)).le
  exact (Geometry.diskExtension_coe q
    (⟨p, Metric.sphere_subset_closedBall hp⟩ : Topology.closedDisk)).symm.trans heq

end DifferentialGeometry.Analysis

end

end
