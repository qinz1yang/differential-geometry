import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

noncomputable section

open Matrix Set
open scoped RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) [Fintype n] := EuclideanSpace Real n

theorem exists_uniform_matrix_quadratic_lower_bound
    {X n : Type*} [TopologicalSpace X]
    [Fintype n] [Nonempty n]
    {K : Set X} (hK : IsCompact K)
    (A : X → Matrix n n Real)
    (hAcont : ∀ i j, ContinuousOn (fun x ↦ A x i j) K)
    (hApos : ∀ x ∈ K, (A x).PosDef) :
    ∃ c : Real, 0 < c ∧ ∀ x ∈ K, ∀ v : Euc n,
      c * ‖v‖ ^ 2 ≤ star v ⬝ᵥ A x *ᵥ v := by
  classical
  let Q : X × Euc n → Real := fun p ↦
    ∑ i, ∑ j, A p.1 i j * p.2 i * p.2 j
  have hQcont : ContinuousOn Q (K ×ˢ (Set.univ : Set (Euc n))) := by
    refine continuousOn_finset_sum Finset.univ (fun i _ ↦ ?_)
    refine continuousOn_finset_sum Finset.univ (fun j _ ↦ ?_)
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact (hAcont i j).comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
    · have hval : Continuous (fun v : Euc n => (v : n → Real)) :=
        (PiLp.continuousLinearEquiv 2 Real (fun _ : n ↦ Real)).continuous
      exact ((continuous_apply i).comp (hval.comp continuous_snd)).continuousOn
    · have hval : Continuous (fun v : Euc n => (v : n → Real)) :=
        (PiLp.continuousLinearEquiv 2 Real (fun _ : n ↦ Real)).continuous
      exact ((continuous_apply j).comp (hval.comp continuous_snd)).continuousOn
  let S : Set (Euc n) := Metric.sphere 0 1
  have hScompact : IsCompact S := isCompact_sphere 0 1
  have hSnonempty : S.Nonempty := by
    let i : n := Classical.arbitrary n
    refine ⟨EuclideanSpace.basisFun n Real i, ?_⟩
    rw [Metric.mem_sphere, dist_zero_right,
      (EuclideanSpace.basisFun n Real).norm_eq_one]
  by_cases hKnonempty : K.Nonempty
  · have hKScompact : IsCompact (K ×ˢ S) := hK.prod hScompact
    have hQcontKS : ContinuousOn Q (K ×ˢ S) :=
      hQcont.mono (Set.prod_mono Subset.rfl (subset_univ S))
    obtain ⟨p₀, hp₀, hp₀min⟩ :=
      hKScompact.exists_isMinOn (hKnonempty.prod hSnonempty) hQcontKS
    have hp₀ne : p₀.2 ≠ 0 := by
      intro hp₀zero
      have := hp₀.2
      rw [hp₀zero, Metric.mem_sphere, dist_self] at this
      exact zero_ne_one this
    have hp₀pos : 0 < Q p₀ := by
      have hp₀coe : (p₀.2 : n → Real) ≠ 0 := by
        intro h
        apply hp₀ne
        exact PiLp.ext (fun i ↦ congrFun h i)
      have hpos := (hApos p₀.1 hp₀.1).dotProduct_mulVec_pos hp₀coe
      have hdotQ : star p₀.2 ⬝ᵥ A p₀.1 *ᵥ p₀.2 = Q p₀ := by
        simp only [Q, dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
          Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ ↦ ?_)
        refine Finset.sum_congr rfl (fun j _ ↦ ?_)
        ring
      rw [← hdotQ]
      exact hpos
    refine ⟨Q p₀, hp₀pos, ?_⟩
    intro x hx v
    by_cases hv : v = 0
    · subst hv
      simp [Q]
    · have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
      let u : Euc n := ‖v‖⁻¹ • v
      have huS : u ∈ S := by
        rw [Metric.mem_sphere, dist_zero_right]
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hvnorm]
        exact inv_mul_cancel₀ hvnorm.ne'
      have hmin : Q p₀ ≤ Q (x, u) := hp₀min ⟨hx, huS⟩
      have hscale : star v ⬝ᵥ A x *ᵥ v = ‖v‖ ^ 2 * Q (x, u) := by
        simp only [Q, dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
          Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ ↦ ?_)
        refine Finset.sum_congr rfl (fun j _ ↦ ?_)
        simp only [u, PiLp.smul_apply, smul_eq_mul]
        field_simp
      rw [hscale, mul_comm]
      exact mul_le_mul_of_nonneg_left hmin (sq_nonneg ‖v‖)
  · refine ⟨1, one_pos, ?_⟩
    intro x hx
    exact absurd ⟨x, hx⟩ hKnonempty

theorem exists_uniform_matrix_quadratic_lower_bound_of_finite
    {R X n : Type*} [Finite R] [TopologicalSpace X]
    [Fintype n] [Nonempty n]
    (K : R → Set X) (hK : ∀ r, IsCompact (K r))
    (A : R → X → Matrix n n Real)
    (hAcont : ∀ r i j, ContinuousOn (fun x ↦ A r x i j) (K r))
    (hApos : ∀ r x, x ∈ K r → (A r x).PosDef) :
    ∃ c : Real, 0 < c ∧ ∀ r x, x ∈ K r → ∀ v : Euc n,
      c * ‖v‖ ^ 2 ≤ star v ⬝ᵥ A r x *ᵥ v := by
  classical
  have hlocal : ∀ r : R, ∃ c : Real, 0 < c ∧ ∀ x ∈ K r, ∀ v : Euc n,
      c * ‖v‖ ^ 2 ≤ star v ⬝ᵥ A r x *ᵥ v := by
    intro r
    exact exists_uniform_matrix_quadratic_lower_bound
      (hK r) (A r) (hAcont r) (hApos r)
  choose c hcpos hcbound using hlocal
  cases isEmpty_or_nonempty R with
  | inl hR =>
      letI := hR
      refine ⟨1, one_pos, ?_⟩
      intro r
      exact isEmptyElim r
  | inr hR =>
      letI := hR
      letI := Fintype.ofFinite R
      have himage : (Finset.univ.image c).Nonempty := by simp
      let cmin : Real := (Finset.univ.image c).min' himage
      have hcminmem : cmin ∈ Finset.univ.image c :=
        Finset.min'_mem (Finset.univ.image c) himage
      have hcminpos : 0 < cmin := by
        rcases Finset.mem_image.mp hcminmem with ⟨r, hr, hrc⟩
        rw [← hrc]
        exact hcpos r
      refine ⟨cmin, hcminpos, ?_⟩
      intro r x hx v
      exact (mul_le_mul_of_nonneg_right
        (Finset.min'_le (Finset.univ.image c) (c r)
          (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩))
        (sq_nonneg ‖v‖)).trans (hcbound r x hx v)

end DifferentialGeometry.Analysis.Schauder
