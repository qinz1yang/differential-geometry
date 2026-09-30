import DifferentialGeometry.Geometry.Comparison.CompleteHingeComparison
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem fourPointComparison_of_complete_local_comparison
    {X : Type*} [MetricSpace X] [CompleteSpace X] {κ : ℝ} (hκ : 0 ≤ κ)
    (hsegments : ∀ x y : X, ∃ σ : Icc (0 : ℝ) (dist x y) → X,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (hlocal : ∀ z : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω) :
    fourPointComparison κ (univ : Set X) := by
  classical
  intro x hx u hu v hv w hw hux hvx hwx
  let P : Fin 3 → X := ![u, v, w]
  let L : Fin 3 → ℝ := fun i => dist x (P i)
  have hL : ∀ i, 0 < L i := by
    intro i
    fin_cases i
    · exact dist_pos.mpr hux.symm
    · exact dist_pos.mpr hvx.symm
    · exact dist_pos.mpr hwx.symm
  choose σ hσ hσ0 hσend using fun i : Fin 3 => hsegments x (P i)
  let γ : Fin 3 → ℝ → X := fun i => IccExtend dist_nonneg (σ i)
  have hrad : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), dist x (γ i s) = s := by
    intro i s hs
    have ht := (hσ i).IccExtend_forward_radial (h := 0) ⟨le_rfl, dist_nonneg⟩
      (s := s) (show s ∈ Icc (0 : ℝ) (dist x (P i) - 0) by
        simpa only [sub_zero] using (show s ∈ Icc (0 : ℝ) (dist x (P i)) from ⟨hs.1.le, hs.2⟩))
    simpa only [zero_add, hσ0 i, γ] using ht
  have hmin : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), ∀ t ∈ Ioc (0 : ℝ) (L i),
      dist (γ i s) (γ i t) = |s - t| := by
    intro i s hs t ht
    exact (hσ i).dist_IccExtend dist_nonneg ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩
  have hend (i : Fin 3) : γ i (L i) = P i := by
    change IccExtend dist_nonneg (σ i) (dist x (P i)) = P i
    rw [IccExtend_right, hσend]
  have hbound (i j : Fin 3) :
      comparisonAngleNegCurvature κ (L i) (L j) (dist (P i) (P j)) ≤
        germComparisonAngle κ (γ i) (γ j) := by
    have h := endpointHingeComparison_of_complete_local_comparison hκ hsegments hlocal
      (P i) (L i + L j + 1)
    have ht := h x (L i) (L j) (γ i) (γ j) (hL i) (hL j) (by linarith)
      (hend i) (hrad i) (hrad j) (hmin i) (hmin j)
    rwa [hend j] at ht
  obtain ⟨Ω, hΩ, hcomp, hxΩ⟩ := hlocal x
  have hthree := germComparisonAngle_sum_le_two_pi_of_local_fourPointComparison
    hκ hL hΩ hcomp hxΩ hrad hmin 0 1 2
  have h01 := hbound 0 1
  have h12 := hbound 1 2
  have h20 := hbound 2 0
  change comparisonAngleNegCurvature κ (dist x u) (dist x v) (dist u v) ≤
    germComparisonAngle κ (γ 0) (γ 1) at h01
  change comparisonAngleNegCurvature κ (dist x v) (dist x w) (dist v w) ≤
    germComparisonAngle κ (γ 1) (γ 2) at h12
  change comparisonAngleNegCurvature κ (dist x w) (dist x u) (dist w u) ≤
    germComparisonAngle κ (γ 2) (γ 0) at h20
  exact (add_le_add (add_le_add h01 h12) h20).trans hthree

end DifferentialGeometry.Geometry.Comparison.Toponogov
