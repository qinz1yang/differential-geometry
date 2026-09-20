import DifferentialGeometry.Analysis.Elliptic.Euclidean.DivergenceOperator
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.SmoothRepresentative
import DifferentialGeometry.Analysis.Elliptic.Coefficients.Extension
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Barrier.Exponential
import DifferentialGeometry.Topology.MetricSpace.ClosedBallRelativeDomain
import DifferentialGeometry.External.DeGiorgi.Localization

section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis
open Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem le_of_divergence_matMulE_smoothGradField_pos_of_le_frontier
    {u : V → ℝ} {S : Set V} {a : ℝ} (hS : IsCompact (closure S))
    (hu : ContinuousOn u (closure S)) (hd : ∀ x ∈ interior S, ContDiffAt ℝ 2 u x)
    (A : V → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x ∈ interior S, ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hpos : ∀ x ∈ interior S, (A x).PosSemidef)
    (hdiv : ∀ x ∈ interior S, 0 < ∑ i, fderiv ℝ
      (fun y => DeGiorgi.matMulE (A y) (DeGiorgi.smoothGradField u y) i) x
        (EuclideanSpace.single i 1))
    (hbd : ∀ x ∈ frontier S, u x ≤ a) : ∀ x ∈ closure S, u x ≤ a := by
  intro x hx
  obtain ⟨y, hy, hm⟩ := hS.exists_isMaxOn ⟨x, hx⟩ hu
  have hny : y ∉ interior S := by
    intro hyi
    have hlocal := hm.isLocalMax (mem_of_superset (isOpen_interior.mem_nhds hyi)
      (interior_subset.trans subset_closure))
    exact (not_lt_of_ge (divergence_nonpos_of_localMax (hd y hyi) hlocal A (hA y hyi)
      (hpos y hyi))) (hdiv y hyi)
  exact (hm hx).trans (hbd y ⟨hy, hny⟩)

theorem le_of_divergence_matMulE_smoothGradField_nonneg_of_le_frontier
    (B : SmoothEllipticBilinearForm d (univ : Set V)) {R : ℝ} (hR : 0 ≤ R)
    {u : V → ℝ} {S : Set V} (hS : closure S ⊆ Metric.closedBall (0 : V) R)
    (hu : ContinuousOn u (closure S)) (hd : ∀ x ∈ interior S, ContDiffAt ℝ 2 u x)
    (hdiv : ∀ x ∈ interior S, 0 ≤ ∑ i, fderiv ℝ
      (fun y => DeGiorgi.matMulE (B.a y) (DeGiorgi.smoothGradField u y) i) x
        (EuclideanSpace.single i 1))
    {a : ℝ} (hbd : ∀ x ∈ frontier S, u x ≤ a) : ∀ x ∈ closure S, u x ≤ a := by
  have hSc : IsCompact (closure S) :=
    (isCompact_closedBall (0 : V) R).of_isClosed_subset isClosed_closure hS
  obtain ⟨k, hk, hb⟩ := exists_exponentialBallBarrier_divergence_le_neg_one B R
  let b := exponentialBallBarrier (d := d) R k
  have hbc : ContDiff ℝ ∞ b := contDiff_exponentialBallBarrier R k
  intro x hx
  have hbpos : 0 ≤ b x := exponentialBallBarrier_nonneg hR hk.le (hS hx)
  have hε : ∀ ε : ℝ, 0 < ε → u x + -ε * b x ≤ a := by
    intro ε hε
    apply le_of_divergence_matMulE_smoothGradField_pos_of_le_frontier
      (u := fun y => u y + -ε * b y) hSc
      (hu.add (continuousOn_const.mul hbc.continuous.continuousOn))
      (fun y hy => (hd y hy).add (contDiffAt_const.mul (hbc.contDiffAt.of_le (by norm_cast))))
      B.a (fun y _ i j => (B.smooth_a i j).differentiable (by simp) y)
      (fun y _ => (B.posDef (mem_univ y)).posSemidef) ?_ ?_ x hx
    · intro y hy
      rw [divergence_matMulE_smoothGradField_add_smul
        (fun i j => (B.smooth_a i j).differentiable (by simp) y) (hd y hy)
        (hbc.contDiffAt.of_le (by norm_cast))]
      have hp := hdiv y hy
      have hneg := hb y (hS (subset_closure (interior_subset hy)))
      have hh := mul_le_mul_of_nonneg_left hneg hε.le
      nlinarith
    · intro y hy
      have hby : 0 ≤ b y := exponentialBallBarrier_nonneg hR hk.le (hS hy.1)
      have hh := hbd y hy
      nlinarith
  by_contra hn
  have hgap : 0 < u x - a := sub_pos.mpr (lt_of_not_ge hn)
  have ht := hε ((u x - a) / (2 * (b x + 1))) (div_pos hgap (by positivity))
  have he : (u x - a) / (2 * (b x + 1)) * (2 * (b x + 1)) = u x - a :=
    div_mul_cancel₀ _ (by positivity)
  have hp : 0 < (u x - a) / (2 * (b x + 1)) := div_pos hgap (by positivity)
  nlinarith

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DeGiorgi
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem IsSolution.le_on_relatively_open_closedBall_of_le_frontier
    {R : ℝ} (hR : 0 < R) {A : EllipticCoeff d (Metric.ball (0 : V) R)} {u v : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm d (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R))
    (hv : ContDiffOn ℝ 2 v (Metric.ball (0 : V) R))
    (hc : ContinuousOn v (Metric.closedBall (0 : V) R))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v)
    {S : Set (Metric.closedBall (0 : V) R)} (hS : IsOpen S)
    (hsub : ∀ x ∈ S, (x : V) ∈ Metric.ball (0 : V) R)
    {a : ℝ} (hbd : ∀ x ∈ frontier S, v x ≤ a) : ∀ x ∈ S, v x ≤ a := by
  let T : Set V := Subtype.val '' S
  have hT : IsOpen T := isOpen_image_of_relatively_open_closedBall hS hsub
  have hTR : T ⊆ Metric.ball (0 : V) R := by rintro x ⟨y, hy, rfl⟩; exact hsub y hy
  have hcl : closure T ⊆ Metric.closedBall (0 : V) R :=
    closure_minimal (hTR.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall
  have hdiv := hu.divergence_smooth_representative_eq_zero Metric.isOpen_ball B hAB hv huv
  have hmax := le_of_divergence_matMulE_smoothGradField_nonneg_of_le_frontier B hR.le hcl
    (hc.mono hcl)
    (fun x hx => (hv x (hTR (interior_subset hx))).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hTR (interior_subset hx))))
    (fun x hx => le_of_eq (hdiv x (hTR (interior_subset hx))).symm)
    (fun x hx => by
      obtain ⟨hxR, hxf⟩ := mem_frontier_relative_of_mem_frontier_image_closedBall hS hsub hx
      exact hbd ⟨x, hxR⟩ hxf)
  intro x hx
  exact hmax x (subset_closure (mem_image_of_mem Subtype.val hx))

theorem IsSolution.le_on_relatively_open_closedBall_of_frontier_le
    {R : ℝ} (hR : 0 < R) {A : EllipticCoeff d (Metric.ball (0 : V) R)} {u v : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm d (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R))
    (hv : ContDiffOn ℝ 2 v (Metric.ball (0 : V) R))
    (hc : ContinuousOn v (Metric.closedBall (0 : V) R))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v)
    {S : Set (Metric.closedBall (0 : V) R)} (hS : IsOpen S)
    (hsub : ∀ x ∈ S, (x : V) ∈ Metric.ball (0 : V) R)
    {a : ℝ} (hbd : ∀ x ∈ frontier S, a ≤ v x) : ∀ x ∈ S, a ≤ v x := by
  have hh := (hu.neg_ball hR).le_on_relatively_open_closedBall_of_le_frontier hR B hAB
    hv.neg hc.neg (huv.fun_comp Neg.neg) hS hsub
    (a := -a) (fun x hx => neg_le_neg (hbd x hx))
  intro x hx
  exact neg_le_neg_iff.mp (hh x hx)

end DeGiorgi

end

end
