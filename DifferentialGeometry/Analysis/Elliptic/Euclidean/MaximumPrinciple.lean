import DifferentialGeometry.Analysis.Calculus.SecondDerivative.Minimum
import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic.Linarith

open Filter Set InnerProductSpace
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem laplacian_nonneg_of_localMin
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hmin : IsLocalMin f x) :
    0 ≤ Laplacian.laplacian f x := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_nonneg
  intro i _
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he (v : E) : fderiv ℝ (fun q => fderiv ℝ f q v) x v =
      fderiv ℝ (fderiv ℝ f) x v v := by
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  rw [← he]
  exact secondDirectional_nonneg_of_localMin hf hmin _

theorem laplacian_nonpos_of_localMax
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hmax : IsLocalMax f x) :
    Laplacian.laplacian f x ≤ 0 := by
  have hn := laplacian_nonneg_of_localMin hf.neg hmax.neg
  change 0 ≤ Laplacian.laplacian (-f) x at hn
  simpa only [laplacian_neg, Pi.neg_apply, neg_nonneg] using hn

theorem le_of_laplacian_pos_of_le_frontier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {s : Set E} {C : ℝ}
    (hs : IsCompact (closure s)) (hf : UpperSemicontinuousOn f (closure s))
    (hd : ∀ x ∈ interior s, ContDiffAt ℝ 2 f x)
    (hΔ : ∀ x ∈ interior s, 0 < Laplacian.laplacian f x)
    (hb : ∀ x ∈ frontier s, f x ≤ C) : ∀ x ∈ closure s, f x ≤ C := by
  intro x hx
  obtain ⟨y, hy, hmax⟩ := hf.exists_isMaxOn ⟨x, hx⟩ hs
  have hny : y ∉ interior s := by
    intro hyi
    have hm := hmax.isLocalMax (mem_of_superset (isOpen_interior.mem_nhds hyi)
      (interior_subset.trans subset_closure))
    exact (not_lt_of_ge (laplacian_nonpos_of_localMax (hd y hyi) hm)) (hΔ y hyi)
  exact (hmax hx).trans (hb y ⟨hy, hny⟩)

theorem le_of_laplacian_nonneg_of_le_frontier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] {f : E → ℝ} {s : Set E} {C : ℝ}
    (hs : IsCompact (closure s)) (hf : UpperSemicontinuousOn f (closure s))
    (hd : ∀ x ∈ interior s, ContDiffAt ℝ 2 f x)
    (hΔ : ∀ x ∈ interior s, 0 ≤ Laplacian.laplacian f x)
    (hb : ∀ x ∈ frontier s, f x ≤ C) : ∀ x ∈ closure s, f x ≤ C := by
  obtain ⟨R, hR, hbound⟩ := hs.isBounded.exists_pos_norm_le
  intro x hx
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (R ^ 2 + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hn (y : E) : ContDiffAt ℝ 2 (fun z : E => ‖z‖ ^ 2) y :=
    contDiffAt_id.norm_sq ℝ
  have hcmp := le_of_laplacian_pos_of_le_frontier (f := fun y => f y + δ * ‖y‖ ^ 2)
    (C := C + ε) hs (hf.add (continuousOn_const.mul (continuous_norm.pow 2).continuousOn).upperSemicontinuousOn)
    (fun y hy => (hd y hy).add (contDiffAt_const.mul (hn y))) ?_ ?_ x hx
  · have hnon : 0 ≤ δ * ‖x‖ ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
    linarith
  · intro y hy
    change 0 < Laplacian.laplacian (f + fun z : E => δ * ‖z‖ ^ 2) y
    rw [(hd y hy).laplacian_add (contDiffAt_const.mul (hn y))]
    have hscale : Laplacian.laplacian (fun z : E => δ * ‖z‖ ^ 2) y =
        δ * Laplacian.laplacian (fun z : E => ‖z‖ ^ 2) y :=
      laplacian_smul δ (hn y)
    rw [hscale, InnerProductSpace.laplacian_norm_sq]
    have hdim : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
    have hp : 0 < δ * (2 * (Module.finrank ℝ E : ℝ)) := by positivity
    linarith [hΔ y hy]
  · intro y hy
    have hys := hbound y hy.1
    have hsquare : ‖y‖ ^ 2 ≤ R ^ 2 := sq_le_sq₀ (norm_nonneg _) hR.le |>.2 hys
    have hmul : δ * ‖y‖ ^ 2 ≤ ε := by
      have hh : δ * (R ^ 2 + 1) = ε := div_mul_cancel₀ ε (by positivity)
      nlinarith
    linarith [hb y hy]

end DifferentialGeometry.Analysis
