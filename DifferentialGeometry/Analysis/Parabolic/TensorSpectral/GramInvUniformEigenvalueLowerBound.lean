import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerLowerBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.NormComparison
import DifferentialGeometry.Integral.L2.PointwiseInner.DualMetric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Uniform Rayleigh-quotient lower bound for the inverse chart-frame Gram matrix

For a closed Riemannian manifold `(M, g)` and a chart base point `α : M`, the
quadratic form
`(b, ξ) ↦ ∑_{i, j} (chartGramMatrix g α b)⁻¹_{ij} ξ_i ξ_j`
on the compact closed support of the chart-atlas partition-of-unity weight at
`α` admits a strictly positive uniform lower bound in `ξ`-norm.

Concretely:

* `exists_chartInvGramMatrix_quadForm_lower_bound_on_pouTsupport` — there
  exists `c > 0` such that for every `b` in the closed support and every
  coefficient vector `ξ : Fin n → ℝ`,
  `c * (∑ i, ξ i ^ 2) ≤ ∑ i j, (chartInvGramMatrix g α b)_{ij} * ξ i * ξ j`.

## Proof strategy

The chart-frame Gram matrix `chartGramMatrix g α b` is positive-definite at
every point of the chart base set (`chartGramMatrix_posDef`); its inverse
`chartInvGramMatrix g α b := (chartGramMatrix g α b)⁻¹` is therefore
positive-definite there. Its entries are continuous in `b` on the chart
base set (`chartInvGramMatrix_entry_contMDiffOn`), and the chart base set
contains the compact closed support of the chart-atlas
partition-of-unity weight at `α`. The Rayleigh-quotient bilinear form is
continuous on `baseSet × (Fin n → ℝ)`, strictly positive at every
`(b, ξ)` with `ξ ≠ 0`, and the extreme-value theorem on the compact
product `tsupport(POU_α) × unit sphere` gives a strictly positive
minimum, which is the required lower bound (with the squared `ξ`-norm
scaling for general `ξ`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Metric Function
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The unit sphere `{ξ | ∑ ξ_i^2 = 1}` in `Fin n → ℝ` is compact (closed and
bounded in a finite-dimensional space). -/
private lemma sphere_isCompact :
    IsCompact {ξ : Fin (Module.finrank ℝ E) → ℝ |
      ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 = 1} := by
  have hcont : Continuous
      (fun ξ : Fin (Module.finrank ℝ E) → ℝ =>
        ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) :=
    continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2)
  have hclosed : IsClosed {ξ : Fin (Module.finrank ℝ E) → ℝ |
      ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 = 1} :=
    isClosed_eq hcont continuous_const
  have hbdd : Bornology.IsBounded {ξ : Fin (Module.finrank ℝ E) → ℝ |
      ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 = 1} := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : _)).mpr ⟨1, ?_⟩
    intro ξ hξ
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr ?_
    intro i
    have hle : ξ i ^ 2 ≤ ∑ j : Fin (Module.finrank ℝ E), ξ j ^ 2 := by
      refine Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin (Module.finrank ℝ E) => ξ j ^ 2) ?_ (Finset.mem_univ i)
      intro j _
      exact sq_nonneg _
    rw [hξ] at hle
    have habs : |ξ i| ≤ 1 := by
      have h_abs_sq : |ξ i| ^ 2 ≤ 1 := by rw [sq_abs]; exact hle
      nlinarith [abs_nonneg (ξ i), sq_nonneg (|ξ i| - 1)]
    exact habs
  exact (isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩)

/-- **Uniform Rayleigh-quotient lower bound for the chart-frame inverse Gram
matrix on an arbitrary compact subset `Kα` of the chart base set.**

For a closed Riemannian manifold `(M, g)`, any chart base point `α`, and a
compact set `Kα` contained in the chart-`α` base set, there exists `c > 0`
such that for every `b ∈ Kα` and every coefficient vector
`ξ : Fin (Module.finrank ℝ E) → ℝ`,
`c * (∑ i, ξ i ^ 2) ≤ ∑ i j, (chartInvGramMatrix g α b)_{ij} * ξ i * ξ j`.

The Gram matrix is built from the chart-`α`-trivialised model basis at every
base-set point; on a compact subset of the chart base set the inverse is
positive-definite with continuous entries, and the extreme-value theorem
produces a strictly positive minimum. -/
theorem exists_chartInvGramMatrix_quadForm_lower_bound_on_compact
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {Kα : Set M} (hKα_compact : IsCompact Kα)
    (hKα_sub_baseSet :
      Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ c : ℝ, 0 < c ∧
      ∀ b : M, b ∈ Kα →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          c * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j := by
  classical
  set Q : M × (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun p =>
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α p.1 i j * p.2 i * p.2 j
    with hQ_def
  have hQ_pos_baseSet : ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      ∀ ξ : Fin (Module.finrank ℝ E) → ℝ, ξ ≠ 0 →
        0 < ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j := by
    intro b hb ξ hξ
    have hG_pd : (chartGramMatrix (I := I) g α b).PosDef :=
      chartGramMatrix_posDef (I := I) g α hb
    have hGinv_pd : (chartInvGramMatrix (I := I) g α b).PosDef := by
      unfold chartInvGramMatrix
      exact hG_pd.inv
    have hdot_pos :
        0 < star ξ ⬝ᵥ chartInvGramMatrix (I := I) g α b *ᵥ ξ :=
      hGinv_pd.dotProduct_mulVec_pos hξ
    have hexp :
        star ξ ⬝ᵥ chartInvGramMatrix (I := I) g α b *ᵥ ξ =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [← hexp]; exact hdot_pos
  have hQ_cont : ContinuousOn Q
      ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ
        (Set.univ : Set (Fin (Module.finrank ℝ E) → ℝ))) := by
    refine continuousOn_finset_sum _ (fun i _ => ?_)
    refine continuousOn_finset_sum _ (fun j _ => ?_)
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.mul ?_ ?_
      · have hentry := (chartInvGramMatrix_entry_contMDiffOn
          (I := I) g α i j).continuousOn
        exact hentry.comp continuous_fst.continuousOn (fun p hp => hp.1)
      · exact ((continuous_apply i).comp continuous_snd).continuousOn
    · exact ((continuous_apply j).comp continuous_snd).continuousOn
  set Sph : Set (Fin (Module.finrank ℝ E) → ℝ) :=
    {ξ | ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 = 1} with hSph_def
  have hSph_compact : IsCompact Sph := sphere_isCompact (E := E)
  set K : Set (M × (Fin (Module.finrank ℝ E) → ℝ)) := Kα ×ˢ Sph with hK_def
  have hK_compact : IsCompact K := hKα_compact.prod hSph_compact
  have hK_sub_baseSet :
      K ⊆ (trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ := by
    intro p hp
    exact ⟨hKα_sub_baseSet hp.1, mem_univ _⟩
  have hQ_cont_K : ContinuousOn Q K := hQ_cont.mono hK_sub_baseSet
  have hSph_ne_zero : ∀ ξ ∈ Sph, ξ ≠ 0 := by
    intro ξ hξ hξ0
    have : (1 : ℝ) = 0 := by
      rw [← hξ, hξ0]; simp
    exact one_ne_zero this
  by_cases hK_ne : K.Nonempty
  · obtain ⟨p₀, hp₀_mem, hp₀_min⟩ :=
      hK_compact.exists_isMinOn hK_ne hQ_cont_K
    have hp₀_M : p₀.1 ∈ Kα := hp₀_mem.1
    have hp₀_S : p₀.2 ∈ Sph := hp₀_mem.2
    have hp₀_ξne : p₀.2 ≠ 0 := hSph_ne_zero p₀.2 hp₀_S
    have hp₀_base : p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      hKα_sub_baseSet hp₀_M
    have hp₀_pos : 0 < Q p₀ :=
      hQ_pos_baseSet p₀.1 hp₀_base p₀.2 hp₀_ξne
    refine ⟨Q p₀, hp₀_pos, ?_⟩
    intro b hb ξ
    by_cases hξ_eq : (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) = 0
    · have hξzero : ∀ i, ξ i = 0 := by
        intro i
        have hle : ξ i ^ 2 ≤ ∑ j : Fin (Module.finrank ℝ E), ξ j ^ 2 := by
          refine Finset.single_le_sum (s := Finset.univ)
            (f := fun j : Fin (Module.finrank ℝ E) => ξ j ^ 2) ?_ (Finset.mem_univ i)
          intro j _; exact sq_nonneg _
        rw [hξ_eq] at hle
        have hsqz : ξ i ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsqz
      have hQzero :
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j) = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [hξzero i, mul_zero, zero_mul]
      rw [hξ_eq, mul_zero, hQzero]
    · have hξ_pos : 0 < ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 :=
        lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg _))
          (Ne.symm hξ_eq)
      set r : ℝ := Real.sqrt (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2)
        with hr_def
      have hr_pos : 0 < r := Real.sqrt_pos.mpr hξ_pos
      have hr_ne : r ≠ 0 := ne_of_gt hr_pos
      have hr_sq : r ^ 2 = ∑ i, ξ i ^ 2 := by
        rw [hr_def, sq]; rw [Real.mul_self_sqrt (le_of_lt hξ_pos)]
      set η : Fin (Module.finrank ℝ E) → ℝ := fun i => ξ i / r with hη_def
      have hη_sph : η ∈ Sph := by
        rw [hSph_def]
        change ∑ i : Fin (Module.finrank ℝ E), η i ^ 2 = 1
        have : ∑ i : Fin (Module.finrank ℝ E), η i ^ 2 =
            (∑ i, ξ i ^ 2) / r ^ 2 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hη_def, div_pow]
        rw [this, hr_sq]
        exact div_self (ne_of_gt hξ_pos)
      have hbη_mem : (b, η) ∈ K := ⟨hb, hη_sph⟩
      have hmin_le_bη : Q p₀ ≤ Q (b, η) := hp₀_min hbη_mem
      have hQscale :
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j) =
            r ^ 2 *
              (∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g α b i j * η i * η j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hη_def]
        change chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j =
          r ^ 2 * (chartInvGramMatrix (I := I) g α b i j * (ξ i / r) * (ξ j / r))
        field_simp
      rw [hQscale]
      have hQη : Q (b, η) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α b i j * η i * η j := rfl
      rw [← hQη]
      rw [← hr_sq, mul_comm]
      exact mul_le_mul_of_nonneg_left hmin_le_bη (sq_nonneg r)
  · refine ⟨1, one_pos, ?_⟩
    intro b hb ξ
    by_cases hKα_ne : Kα.Nonempty
    · by_cases hn : Nonempty (Fin (Module.finrank ℝ E))
      · haveI : Nonempty (Fin (Module.finrank ℝ E)) := hn
        set i₀ : Fin (Module.finrank ℝ E) := Classical.arbitrary _
        set e₀ : Fin (Module.finrank ℝ E) → ℝ :=
          (Pi.single i₀ (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ) with he₀_def
        have h0 : e₀ ∈ Sph := by
          rw [hSph_def]
          change ∑ i : Fin (Module.finrank ℝ E), (e₀ i) ^ 2 = 1
          rw [Finset.sum_eq_single i₀]
          · simp [he₀_def]
          · intro i _ hi
            rw [he₀_def, Pi.single_apply, if_neg hi]; ring
          · intro h
            exact absurd (Finset.mem_univ _) h
        obtain ⟨b₀, hb₀⟩ := hKα_ne
        exact absurd ⟨(b₀, e₀), ⟨hb₀, h0⟩⟩ hK_ne
      · have hempty : ¬ Nonempty (Fin (Module.finrank ℝ E)) := hn
        have hsum_empty : ∀ f : Fin (Module.finrank ℝ E) → ℝ,
            ∑ i : Fin (Module.finrank ℝ E), f i = 0 := by
          intro f
          apply Finset.sum_eq_zero
          intro i _
          exact absurd ⟨i⟩ hempty
        rw [hsum_empty]
        rw [mul_zero]
        exact le_of_eq (hsum_empty _).symm
    · exact absurd ⟨b, hb⟩ hKα_ne

/-- **Uniform Rayleigh-quotient lower bound for the chart-frame inverse Gram
matrix on the compact closed support of the chart-atlas partition-of-unity
weight at `α`.**

For a closed Riemannian manifold `(M, g)` and any chart base point `α`,
there exists `c > 0` such that for every `b` in the closed support of the
chart-atlas partition-of-unity weight at `α` and every coefficient vector
`ξ : Fin (Module.finrank ℝ E) → ℝ`,
`c * (∑ i, ξ i ^ 2) ≤ ∑ i j, (chartInvGramMatrix g α b)_{ij} * ξ i * ξ j`.

This is the specialisation of
`exists_chartInvGramMatrix_quadForm_lower_bound_on_compact` to the compact
closed support of the chart-atlas partition-of-unity weight. -/
theorem exists_chartInvGramMatrix_quadForm_lower_bound_on_pouTsupport
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ c : ℝ, 0 < c ∧
      ∀ b : M, b ∈ tsupport
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          c * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j :=
  exists_chartInvGramMatrix_quadForm_lower_bound_on_compact
    (I := I) (M := M) g α
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_subset_baseSet (I := I) (M := M) α)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
