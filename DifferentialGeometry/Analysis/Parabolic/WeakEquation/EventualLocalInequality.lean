import DifferentialGeometry.Analysis.Parabolic.WeakEquation.LocalInequality
import Mathlib.Order.Filter.Finite


noncomputable section

namespace DifferentialGeometry.Analysis

open Filter Set MeasureTheory
open scoped ContDiff Manifold Topology BigOperators

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X]
  {μ : Measure X} {Ω : Set X} {α ι : Type*} [Fintype ι] {l : Filter α}

theorem eventually_integrable_integral_mul_add_sum_mul_fderiv_nonneg_of_local
    (B : α → X → ℝ) (A : α → ι → X → ℝ) (v : ι → X)
    (hlocal : ∀ x ∈ Ω, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∀ᶠ k in l, ∀ ψ : X → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ V → (∀ y, 0 ≤ ψ y) →
        Integrable (fun y => B k y * ψ y + ∑ i, A k i y * fderiv ℝ ψ y (v i)) μ ∧
          0 ≤ ∫ y, B k y * ψ y + ∑ i, A k i y * fderiv ℝ ψ y (v i) ∂μ)
    {φ : X → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) (hφn : ∀ x, 0 ≤ φ x) :
    ∀ᶠ k in l,
      Integrable (fun x => B k x * φ x + ∑ i, A k i x * fderiv ℝ φ x (v i)) μ ∧
        0 ≤ ∫ x, B k x * φ x + ∑ i, A k i x * fderiv ℝ φ x (v i) ∂μ := by
  classical
  choose V hVo hxV _hVΩ hV using fun x : Ω => hlocal x x.property
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, X)
    (isClosed_tsupport φ) V hVo (fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hφΩ hx⟩, hxV ⟨x, hφΩ hx⟩⟩)
  obtain ⟨s, hsum⟩ := ρ.toPartitionOfUnity.exists_finset_sum_smul_eq hφc
    (subset_tsupport φ)
  let ψ : Ω → X → ℝ := fun i x => ρ i x * φ x
  have hψ (i : Ω) : ContDiff ℝ 2 (ψ i) := by
    have hi : ContDiff ℝ 2 (ρ i) :=
      contMDiff_iff_contDiff.mp ((ρ i).contMDiff.of_le (by decide))
    exact hi.mul hφ
  have hψc (i : Ω) : HasCompactSupport (ψ i) := hφc.mul_left
  have hψV (i : Ω) : tsupport (ψ i) ⊆ V i :=
    tsupport_mul_subset_left.trans (hρ i)
  have hψn (i : Ω) (x : X) : 0 ≤ ψ i x := mul_nonneg (ρ.nonneg i x) (hφn x)
  have heq : φ = ∑ i ∈ s, ψ i := by
    funext x
    have h := (hsum x).symm
    change φ x = ∑ i ∈ s, ρ i x * φ x at h
    simpa only [Finset.sum_apply, ψ] using h
  have hder (x w : X) : fderiv ℝ φ x w = ∑ i ∈ s, fderiv ℝ (ψ i) x w := by
    conv_lhs => rw [heq]
    rw [fderiv_sum (fun i _ => (hψ i).differentiable (by norm_num) x)]
    simp only [_root_.sum_apply]
  have hfun (k : α) :
      (fun x => B k x * φ x + ∑ j, A k j x * fderiv ℝ φ x (v j)) =
        fun x => ∑ i ∈ s,
          (B k x * ψ i x + ∑ j, A k j x * fderiv ℝ (ψ i) x (v j)) := by
    funext x
    have hval : φ x = ∑ i ∈ s, ψ i x := by
      simpa only [Finset.sum_apply] using congrFun heq x
    simp_rw [hval, hder, Finset.mul_sum]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
  have hfinite : ∀ᶠ k in l, ∀ i ∈ s,
      Integrable (fun x => B k x * ψ i x + ∑ j, A k j x * fderiv ℝ (ψ i) x (v j)) μ ∧
        0 ≤ ∫ x, B k x * ψ i x + ∑ j, A k j x * fderiv ℝ (ψ i) x (v j) ∂μ := by
    apply (eventually_all_finset s).2
    intro i _
    filter_upwards [hV i] with k hk
    exact hk (ψ i) (hψ i) (hψc i) (hψV i) (hψn i)
  filter_upwards [hfinite] with k hk
  rw [hfun k]
  refine ⟨integrable_finsetSum s (fun i hi => (hk i hi).1), ?_⟩
  rw [integral_finsetSum s (fun i hi => (hk i hi).1)]
  exact Finset.sum_nonneg fun i hi => (hk i hi).2

end DifferentialGeometry.Analysis

end
