import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartGramUniformContinuity

/-!
# Uniform upper bound for the chart-α Gram-matrix quadratic form on the
# closed support of the chart-atlas partition-of-unity weight at `α`

For a closed Riemannian manifold `(M, g)` and a chart base point `α : M`, the
quadratic form
`(b, ξ) ↦ ∑_{i, j} g.inner b (chartBasisVecFiber α i b) (chartBasisVecFiber α j b)
    · ξ i · ξ j`
on the compact closed support of the chart-atlas partition-of-unity weight at
`α` admits a uniform upper bound by a non-negative multiple of the squared
`ξ`-norm `∑_i ξ i ^ 2`.

This is the forward companion of
`exists_chartInvGramMatrix_quadForm_lower_bound_on_pouTsupport` (the same
statement with the inverse Gram matrix and `≥ c · ∑ ξ i ^ 2`). The forward
direction is more elementary: each entry of `chartGramMatrix g α b` is
continuous in `b` on the chart base set, the closed POU support is compact
and contained in the chart base set, so every entry is uniformly bounded
there; the bound on the quadratic form then follows from
`|G_{ij} · ξ_i · ξ_j| ≤ |G_{ij}| · ∑_k ξ_k ^ 2`.

## Main result

* `exists_chartGramMatrix_quadForm_upper_bound_on_pouTsupport` — there
  exists `C ≥ 0` such that for every `b` in the closed support and every
  coefficient vector `ξ : Fin n → ℝ`,
  `∑ i, ∑ j, g.inner b (chartBasisVecFiber α i b) (chartBasisVecFiber α j b)
        · ξ i · ξ j ≤ C · ∑ i, ξ i ^ 2`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private lemma abs_mul_le_sum_sq
    {N : ℕ} (ξ : Fin N → ℝ) (i j : Fin N) :
    |ξ i * ξ j| ≤ ∑ k : Fin N, ξ k ^ 2 := by
  classical
  have hAMGM : 2 * |ξ i * ξ j| ≤ ξ i ^ 2 + ξ j ^ 2 := by
    have h := sq_nonneg (|ξ i| - |ξ j|)
    have h_abs_sq_i : |ξ i| ^ 2 = ξ i ^ 2 := sq_abs (ξ i)
    have h_abs_sq_j : |ξ j| ^ 2 = ξ j ^ 2 := sq_abs (ξ j)
    have h_abs_mul : |ξ i * ξ j| = |ξ i| * |ξ j| := abs_mul _ _
    nlinarith [h_abs_sq_i, h_abs_sq_j, h_abs_mul,
      abs_nonneg (ξ i), abs_nonneg (ξ j)]
  have h_half_le : |ξ i * ξ j| ≤ (ξ i ^ 2 + ξ j ^ 2) / 2 := by linarith
  have h_i_le : ξ i ^ 2 ≤ ∑ k : Fin N, ξ k ^ 2 := by
    refine Finset.single_le_sum (s := Finset.univ)
      (f := fun k : Fin N => ξ k ^ 2) ?_ (Finset.mem_univ i)
    intro k _
    exact sq_nonneg _
  have h_j_le : ξ j ^ 2 ≤ ∑ k : Fin N, ξ k ^ 2 := by
    refine Finset.single_le_sum (s := Finset.univ)
      (f := fun k : Fin N => ξ k ^ 2) ?_ (Finset.mem_univ j)
    intro k _
    exact sq_nonneg _
  have h_half_total : (ξ i ^ 2 + ξ j ^ 2) / 2 ≤ ∑ k : Fin N, ξ k ^ 2 := by
    have h_sum_le : ξ i ^ 2 + ξ j ^ 2 ≤ 2 * ∑ k : Fin N, ξ k ^ 2 := by linarith
    linarith
  exact le_trans h_half_le h_half_total

private lemma chartGramMatrix_eq_inner
    (g : SmoothRiemannianMetric I M) (α b : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) g α b i j =
      g.inner b
        (chartBasisVecFiber (I := I) α i b)
        (chartBasisVecFiber (I := I) α j b) :=
  chartGramMatrix_apply g α b i j

private lemma chartGramMatrix_sum_entry_bound_on_pouTsupport
    [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ i j : Fin (Module.finrank ℝ E),
          |chartGramMatrix (I := I) g α b i j| ≤ C₀ := by
  classical
  set Kα : Set M := tsupport (fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hKα_def
  have hKα_compact : IsCompact Kα :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hKα_sub_base :
      Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α
  have hKα_sub_src : Kα ⊆ (chartAt H α).source := by
    have h_set_eq : ((trivializationAt E (TangentSpace I) α).baseSet : Set M)
        = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M) α
    rw [← h_set_eq]
    exact hKα_sub_base
  have hchoice : ∀ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      ∃ K : ℝ, 0 < K ∧
        ∀ b ∈ Kα, |chartGramMatrix (I := I) g α b ij.1 ij.2| ≤ K := by
    intro ij
    exact chartGramMatrix_entry_isBounded_on_compact (I := I) (M := M)
      g α ij.1 ij.2 hKα_compact hKα_sub_src
  choose K hK_pos hK_le using hchoice
  set V : Finset (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :=
    Finset.univ with hV_def
  set C₀ : ℝ := ∑ ij ∈ V, K ij with hC₀_def
  have hC₀_nonneg : 0 ≤ C₀ := by
    refine Finset.sum_nonneg ?_
    intro ij _
    exact le_of_lt (hK_pos ij)
  refine ⟨C₀, hC₀_nonneg, ?_⟩
  intro b hb i j
  have hK_ij_le_C₀ : K (i, j) ≤ C₀ := by
    refine Finset.single_le_sum (s := V) (f := fun ij => K ij) ?_
      (Finset.mem_univ (i, j))
    intro ij _
    exact le_of_lt (hK_pos ij)
  have h_entry : |chartGramMatrix (I := I) g α b i j| ≤ K (i, j) :=
    hK_le (i, j) b hb
  linarith

/-- **Uniform upper bound on the chart-`α` Gram-matrix quadratic form over
the closed support of the chart-atlas partition-of-unity weight at `α`.**

For a closed Riemannian manifold `(M, g)` and a chart base point `α : M`,
there exists `C ≥ 0` such that for every `b` in the closed support of the
chart-atlas partition-of-unity weight at `α` and every coefficient vector
`ξ : Fin (Module.finrank ℝ E) → ℝ`,
`∑ i, ∑ j, g.inner b (chartBasisVecFiber α i b) (chartBasisVecFiber α j b)
    · ξ i · ξ j ≤ C · ∑ i, ξ i ^ 2`.

The forward companion of
`exists_chartInvGramMatrix_quadForm_lower_bound_on_pouTsupport`. The
quadratic form is dominated by the entrywise bound on the Gram matrix
(continuous entries on a compact subset of the chart base set) combined
with the AM-GM-type inequality `|ξ i · ξ j| ≤ ∑_k ξ k ^ 2`. -/
theorem exists_chartGramMatrix_quadForm_upper_bound_on_pouTsupport
    [I.Boundaryless] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              g.inner b (chartBasisVecFiber (I := I) α i b)
                       (chartBasisVecFiber (I := I) α j b) * ξ i * ξ j) ≤
            C * (∑ i : Fin (Module.finrank ℝ E), (ξ i)^2) := by
  classical
  set N : ℕ := Module.finrank ℝ E with hN_def
  obtain ⟨C₀, hC₀_nonneg, hC₀_bound⟩ :=
    chartGramMatrix_sum_entry_bound_on_pouTsupport (I := I) (M := M) g α
  set C : ℝ := (N : ℝ) ^ 2 * C₀ with hC_def
  have hC_nonneg : 0 ≤ C := by
    have hN_sq_nn : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
    exact mul_nonneg hN_sq_nn hC₀_nonneg
  refine ⟨C, hC_nonneg, ?_⟩
  intro b hb ξ
  have h_per_pair : ∀ i j : Fin N,
      g.inner b (chartBasisVecFiber (I := I) α i b)
                (chartBasisVecFiber (I := I) α j b) * ξ i * ξ j ≤
        C₀ * ∑ k : Fin N, ξ k ^ 2 := by
    intro i j
    set G_ij : ℝ := g.inner b (chartBasisVecFiber (I := I) α i b)
        (chartBasisVecFiber (I := I) α j b) with hG_def
    have hG_eq_chart : G_ij = chartGramMatrix (I := I) g α b i j := by
      rw [hG_def]
      exact (chartGramMatrix_eq_inner (I := I) g α b i j).symm
    have h_abs_G : |G_ij| ≤ C₀ := by
      rw [hG_eq_chart]
      exact hC₀_bound b hb i j
    have h_le_abs : G_ij * ξ i * ξ j ≤ |G_ij * ξ i * ξ j| := le_abs_self _
    have h_abs_prod : |G_ij * ξ i * ξ j| = |G_ij| * |ξ i * ξ j| := by
      rw [mul_assoc, abs_mul, abs_mul]
    have h_abs_mul_bound : |ξ i * ξ j| ≤ ∑ k : Fin N, ξ k ^ 2 :=
      abs_mul_le_sum_sq (N := N) ξ i j
    have h_abs_nn : 0 ≤ |ξ i * ξ j| := abs_nonneg _
    calc G_ij * ξ i * ξ j
        ≤ |G_ij * ξ i * ξ j| := h_le_abs
      _ = |G_ij| * |ξ i * ξ j| := h_abs_prod
      _ ≤ C₀ * |ξ i * ξ j| := mul_le_mul_of_nonneg_right h_abs_G h_abs_nn
      _ ≤ C₀ * ∑ k : Fin N, ξ k ^ 2 :=
          mul_le_mul_of_nonneg_left h_abs_mul_bound hC₀_nonneg
  calc (∑ i : Fin N,
          ∑ j : Fin N,
            g.inner b (chartBasisVecFiber (I := I) α i b)
                     (chartBasisVecFiber (I := I) α j b) * ξ i * ξ j)
      ≤ ∑ i : Fin N, ∑ j : Fin N, C₀ * ∑ k : Fin N, ξ k ^ 2 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine Finset.sum_le_sum (fun j _ => ?_)
        exact h_per_pair i j
    _ = ((Finset.univ : Finset (Fin N)).card : ℝ) *
        ((Finset.univ : Finset (Fin N)).card : ℝ) *
          (C₀ * ∑ k : Fin N, ξ k ^ 2) := by
        rw [show (∑ i : Fin N, ∑ j : Fin N, C₀ * ∑ k : Fin N, ξ k ^ 2) =
            (∑ i : Fin N, ((Finset.univ : Finset (Fin N)).card : ℝ) *
              (C₀ * ∑ k : Fin N, ξ k ^ 2)) from ?_]
        · simp only [Finset.sum_const, nsmul_eq_mul]
          ring
        · refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (N : ℝ) ^ 2 * C₀ * ∑ k : Fin N, ξ k ^ 2 := by
        rw [Finset.card_univ, Fintype.card_fin]
        ring
    _ = C * ∑ k : Fin N, ξ k ^ 2 := by rw [hC_def]

end Connection
end Integral
end DifferentialGeometry

end
