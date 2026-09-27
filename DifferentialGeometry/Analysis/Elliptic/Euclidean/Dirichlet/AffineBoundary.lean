import DifferentialGeometry.Analysis.Elliptic.Euclidean.Barrier.AffineDirichlet
import DifferentialGeometry.Topology.Continuous.PiecewiseBoundary
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.SmoothRepresentative

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DeGiorgi
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem IsSolution.exists_continuous_closedBall_representative_of_coordinate_trace
    (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R)
    {A : EllipticCoeff d (Metric.ball (0 : V) R)} {u : V → ℝ} (hu : IsSolution A u)
    (B : SmoothEllipticBilinearForm d (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R)) (j : Fin d)
    (ht : MemH01 (fun x => u x - x j) (Metric.ball (0 : V) R)) :
    ∃ v : V → ℝ, ContDiffOn ℝ ∞ v (Metric.ball (0 : V) R) ∧
      ContinuousOn v (Metric.closedBall (0 : V) R) ∧
      u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v ∧
      ∀ x ∈ Metric.sphere (0 : V) R, v x = x j := by
  classical
  obtain ⟨v, hv, huv⟩ := hu.exists_contDiffOn_ae_eq Metric.isOpen_ball B hAB
  obtain ⟨k, C, hk, _, hbound⟩ :=
    hu.exists_affine_dirichlet_barrier_bound_of_continuousOn hd hR B hAB j ht hv.continuousOn huv
  let w := (Metric.ball (0 : V) R).piecewise v (fun x => x j)
  have heq : EqOn w v (Metric.ball (0 : V) R) := fun x hx => piecewise_eq_of_mem _ _ _ hx
  have hj : Continuous (fun x : V => x j) := (EuclideanSpace.proj j : V →L[ℝ] ℝ).continuous
  have hwc : ContinuousOn w (Metric.closedBall (0 : V) R) := by
    have hb : Continuous (fun x : V => C * exponentialBallBarrier R k x) :=
      continuous_const.mul (contDiff_exponentialBallBarrier R k).continuous
    have hh := continuousOn_piecewise_of_norm_sub_le_boundary_vanishing
      Metric.isOpen_ball hv.continuousOn hj.continuousOn hb.continuousOn
      (fun x hx => by
        have hs : x ∈ Metric.sphere (0 : V) R := by
          simpa only [frontier_ball (0 : V) (ne_of_gt hR)] using hx
        rw [exponentialBallBarrier_eq_zero hs, mul_zero])
      (fun x hx => by simpa only [Real.norm_eq_abs] using hbound x hx)
    simpa only [closure_ball (0 : V) (ne_of_gt hR)] using hh
  refine ⟨w, hv.congr heq, hwc, huv.trans ?_, ?_⟩
  · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact (heq hx).symm
  · intro x hx
    apply piecewise_eq_of_notMem
    exact Metric.sphere_disjoint_ball.notMem_of_mem_left hx

theorem IsSolution.exists_continuous_boundary_extension_of_representative
    (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R)
    {A : EllipticCoeff d (Metric.ball (0 : V) R)} {u : V → ℝ} (hu : IsSolution A u)
    (B : SmoothEllipticBilinearForm d (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R)) (j : Fin d)
    (ht : MemH01 (fun x => u x - x j) (Metric.ball (0 : V) R))
    {S : Set V} (hS : IsOpen S) (hSR : S ⊆ Metric.ball (0 : V) R)
    {v : V → ℝ} (hv : ContinuousOn v S) (huv : u =ᵐ[volume.restrict S] v) :
    ∃ w : V → ℝ, ContDiffOn ℝ ∞ w (Metric.ball (0 : V) R) ∧
      ContinuousOn w (Metric.closedBall (0 : V) R) ∧
      u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] w ∧ EqOn w v S ∧
      ∀ x ∈ Metric.sphere (0 : V) R, w x = x j := by
  obtain ⟨w, hws, hwc, huw, hwbd⟩ :=
    hu.exists_continuous_closedBall_representative_of_coordinate_trace hd hR B hAB j ht
  have huwS : u =ᵐ[volume.restrict S] w :=
    huw.filter_mono (MeasureTheory.ae_mono (Measure.restrict_mono hSR le_rfl))
  exact ⟨w, hws, hwc, huw,
    Measure.eqOn_open_of_ae_eq (huwS.symm.trans huv) hS (hws.continuousOn.mono hSR) hv, hwbd⟩

end DeGiorgi

end

end
