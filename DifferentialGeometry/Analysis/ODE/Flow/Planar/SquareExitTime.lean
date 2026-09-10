import DifferentialGeometry.Analysis.ODE.Flow.Planar.SquareFlowExit
import DifferentialGeometry.Analysis.ODE.Flow.Planar.ConstantHalfSpaceExit

open Set
open scoped ContDiff

namespace Poincare.Analysis

theorem exists_smooth_square_exitTime
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {v : P × ℂ → ℂ} (hv : ContDiff ℝ ∞ v) (φ : P → _root_.Flow ℝ ℂ)
    (hφ : ContDiff ℝ ∞ (fun q : P × ℝ × ℂ ↦ φ q.1 q.2.1 q.2.2))
    {ζ : P → ℂ} (hζ : ContDiff ℝ ∞ ζ) {S : Set P}
    (hnz : ∀ p ∈ S, ∀ z, v (p, z) ≠ 0)
    (hderiv : ∀ p ∈ S, ∀ z t, HasDerivAt (fun s ↦ φ p s z) (v (p, φ p t z)) t)
    (hfixed : ∀ p ∈ S, ∀ z : ℂ,
      z.re ≤ 0 ∨ 1 ≤ z.re ∨ z.im ≤ 0 ∨ 1 ≤ z.im → v (p, z) = 1)
    (hinit : ∀ p ∈ S, (ζ p).re ∈ Ico 0 1 ∧ (ζ p).im ∈ Icc 0 1) :
    ∃ τ : P → ℝ, ContDiffOn ℝ ∞ τ S ∧
      (∀ p ∈ S, 0 < τ p) ∧
      (∀ p ∈ S, (φ p (τ p) (ζ p)).re = 1) ∧
      (∀ p ∈ S, ∀ t, (φ p t (ζ p)).re = 1 → t = τ p) ∧
      ∀ p ∈ S, ∀ s : ℝ, 0 ≤ s →
        φ p (τ p + s) (ζ p) = φ p (τ p) (ζ p) + s • (1 : ℂ) := by
  have hγ : ContDiff ℝ ∞ (fun q : P × ℝ ↦ φ q.1 q.2 (ζ q.1)) :=
    hφ.comp (contDiff_fst.prodMk (contDiff_snd.prodMk (hζ.comp contDiff_fst)))
  apply exists_smooth_exitTime_of_constant_halfSpace hv hγ Complex.reCLM (1 : ℂ)
    (b := 1) (by simp)
    (fun p hp z hz ↦ hfixed p hp z (Or.inr (Or.inl hz)))
    (fun p hp t ↦ hderiv p hp (ζ p) t)
    (fun p hp ↦ by simpa only [(φ p).map_zero_apply, Complex.reCLM_apply]
      using (hinit p hp).1.2)
  intro p hp
  obtain ⟨t, _, ht⟩ := exists_pos_rightEdge_crossing (φ p)
    (hv.comp (contDiff_const.prodMk contDiff_id)) (hnz p hp) (hderiv p hp)
    (hfixed p hp) (hinit p hp).1 (hinit p hp).2
  exact ⟨t, ht⟩

end Poincare.Analysis
