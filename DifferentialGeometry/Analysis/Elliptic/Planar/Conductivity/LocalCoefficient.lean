import DifferentialGeometry.Analysis.Elliptic.Coefficients
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis

open Laplacian.MetricExtension

local notation "V" => EuclideanSpace ℝ (Fin 2)

/-- Extend a locally continuous matrix coefficient by the identity outside the
closed unit ball. The ellipticity constants are the caller's prescribed values,
and agreement with the original coefficient includes the sphere. -/
theorem exists_ellipticCoeff_of_closedBall_continuous
    (K : V → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j, ContinuousOn (fun x => K x i j) (Metric.closedBall (0 : V) 1))
    (lam capLam : ℝ) (hlam : 0 < lam) (hcap : lam ≤ capLam)
    (hcoer : ∀ x ∈ Metric.closedBall (0 : V) 1, ∀ ξ : V,
      lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (K x) ξ⟫_ℝ)
    (hcoerInv : ∀ x ∈ Metric.closedBall (0 : V) 1, ∀ ξ : V,
      capLam⁻¹ * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE ((K x)⁻¹) ξ⟫_ℝ) :
    ∃ A : DeGiorgi.EllipticCoeff 2 (Metric.ball (0 : V) 1),
      A.lam = lam ∧ A.Λ = capLam ∧
      (∀ x ∈ Metric.closedBall (0 : V) 1, A.a x = K x) ∧
      (∀ x ∉ Metric.closedBall (0 : V) 1, A.a x = 1) := by
  classical
  let a : V → Matrix (Fin 2) (Fin 2) ℝ :=
    (Metric.closedBall (0 : V) 1).piecewise K (fun _ => 1)
  have ha (x : V) (hx : x ∈ Metric.closedBall (0 : V) 1) : a x = K x :=
    Set.piecewise_eq_of_mem _ _ _ hx
  have ha' (x : V) (hx : x ∉ Metric.closedBall (0 : V) 1) : a x = 1 :=
    Set.piecewise_eq_of_notMem _ _ _ hx
  have hcont : ContinuousOn K (Metric.closedBall (0 : V) 1) :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => hK i j
  have hmeas : Measurable a :=
    hcont.measurable_piecewise continuousOn_const Metric.isClosed_closedBall.measurableSet
  have hentry : ∀ i j, Measurable (fun x => a x i j) := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hmeas)
  let A := ellipticCoeffOfPointwiseBounds Metric.isOpen_ball.measurableSet
    a lam capLam hlam hcap hentry
    (by
      intro x hx ξ
      rw [ha x (Metric.ball_subset_closedBall hx)]
      exact hcoer x (Metric.ball_subset_closedBall hx) ξ)
    (by
      intro x hx ξ
      rw [ha x (Metric.ball_subset_closedBall hx)]
      exact hcoerInv x (Metric.ball_subset_closedBall hx) ξ)
  exact ⟨A, rfl, rfl, ha, ha'⟩

end DifferentialGeometry.Analysis
