import DifferentialGeometry.Geometry.HessianTrace

/-!
# Chart-level metric compatibility identity

This file proves the chart-level metric compatibility identity, derived purely
algebraically from the explicit definition of the chart Christoffel symbol of
the second kind:
$$\Gamma^l{}_{ij}(g, \alpha)(y) = \tfrac12 \sum_m G^{lm}(\alpha, x_y)\,
  \bigl(\partial_i G_{mj}(\alpha, y) + \partial_j G_{mi}(\alpha, y)
       - \partial_m G_{ij}(\alpha, y)\bigr),$$
where `x_y := (extChartAt I α).symm y` and `G^{lm}` is the inverse Gram matrix.

The headline identity states
$$\partial_k G_{ij}(\alpha, y) = \sum_l \Gamma^l{}_{ki}(\alpha, y)\, G_{lj}(\alpha, y)
  + \sum_l \Gamma^l{}_{kj}(\alpha, y)\, G_{li}(\alpha, y),$$
and follows by substituting the explicit formula and collapsing the inner
contraction `∑_l G^{lm} G_{lj}` to `δ^m_j` via the matrix-inverse pairing.

The hypothesis `y ∈ interior (extChartAt I α).target` ensures the chart map
inverse `(extChartAt I α).symm` is well-defined at `y` and the inverse Gram
matrix is the genuine inverse there.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- Symmetry of the chart inverse Gram matrix entries: `G^{ij}(α, y) = G^{ji}(α, y)`,
derived from the fact that the inverse of a Hermitian (here symmetric) matrix
is Hermitian. -/
private lemma chartInvGramOnE_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartInvGramOnE (I := I) g α i j y = chartInvGramOnE (I := I) g α j i y := by
  unfold chartInvGramOnE
  set z := (extChartAt I α).symm y
  have hG_hermit : (chartGramMatrix (I := I) g α z).IsHermitian :=
    chartGramMatrix_isHermitian (I := I) g α z
  have hGinv_hermit : (chartGramMatrix (I := I) g α z)⁻¹.IsHermitian := hG_hermit.inv
  have hentry := hGinv_hermit.apply i j
  unfold chartInvGramMatrix
  have hstar : star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
      (chartGramMatrix (I := I) g α z)⁻¹ i j := hentry
  rw [show star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
      (chartGramMatrix (I := I) g α z)⁻¹ j i from rfl] at hstar
  exact hstar.symm

/-- The Gram-inverse pairing identity at a chart-target point: for any
`y ∈ (extChartAt I α).target` and indices `m, j`,
`∑_l G^{ml}(α, y) * G_{lj}(α, y) = δ^m_j`. -/
private lemma sum_chartInvGramOnE_chartGramOnE_left
    (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target)
    (m j : Fin (Module.finrank ℝ E)) :
    ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α m l y *
          chartGramOnE (I := I) g α l j y =
      (if m = j then (1 : ℝ) else 0) := by
  classical
  set z : M := (extChartAt I α).symm y
  have hz_base : z ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    have hsource : z ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hprod_eq :
      ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α m l y *
            chartGramOnE (I := I) g α l j y =
        (chartInvGramMatrix (I := I) g α z *
          chartGramMatrix (I := I) g α z) m j := by
    simp only [Matrix.mul_apply]
    rfl
  rw [hprod_eq, chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hz_base]
  by_cases hmj : m = j
  · subst hmj; simp
  · rw [if_neg hmj]
    exact Matrix.one_apply_ne hmj

/-- Symmetric form of the Gram-inverse pairing: `∑_l G^{lm}(y) * G_{lj}(y) = δ^m_j`,
using symmetry of `G^{-1}` in its two indices. -/
private lemma sum_chartInvGramOnE_chartGramOnE_right
    (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target)
    (m j : Fin (Module.finrank ℝ E)) :
    ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α l m y *
          chartGramOnE (I := I) g α l j y =
      (if m = j then (1 : ℝ) else 0) := by
  classical
  rw [show (∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α l m y *
          chartGramOnE (I := I) g α l j y) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α m l y *
          chartGramOnE (I := I) g α l j y from
      Finset.sum_congr rfl (fun l _ => by
        rw [chartInvGramOnE_symm (I := I) g α l m y])]
  exact sum_chartInvGramOnE_chartGramOnE_left (I := I) g α hy m j

/-- Equality of `partialDeriv` on the symmetric pair of Gram entries:
`∂_k G_{ab} = ∂_k G_{ba}` (since `chartGramOnE g α a b = chartGramOnE g α b a`
as functions of `y`). -/
private lemma partialDeriv_chartGramOnE_swap_indices
    (g : SmoothRiemannianMetric I M) (α : M)
    (k a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y =
      partialDeriv (E := E) k (chartGramOnE (I := I) g α b a) y := by
  congr 1
  funext y'
  exact chartGramOnE_symm (I := I) g α a b y'

/-- Two-sum form of the chart metric identity: for
`y ∈ interior (extChartAt I α).target`,
$$\partial_k G_{ij}(\alpha, y) =
  \sum_l \Gamma^l{}_{ki}(\alpha, y)\, G_{lj}(\alpha, y) +
  \sum_l \Gamma^l{}_{kj}(\alpha, y)\, G_{li}(\alpha, y).$$

This is the metric-compatibility property of the Levi-Civita Christoffel symbol
of the second kind, derived from the explicit chart formula. -/
theorem chartGramOnE_partialDeriv_eq_christoffel_sum_split
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y =
      (∑ l : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α k i l y *
            chartGramOnE (I := I) g α l j y) +
      (∑ l : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α k j l y *
            chartGramOnE (I := I) g α l i y) := by
  classical
  have hytgt : y ∈ (extChartAt I α).target := interior_subset hy
  let S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          Fin (Module.finrank ℝ E) → ℝ :=
    fun a b c =>
      partialDeriv (E := E) a (chartGramOnE (I := I) g α c b) y +
        partialDeriv (E := E) b (chartGramOnE (I := I) g α c a) y -
        partialDeriv (E := E) c (chartGramOnE (I := I) g α a b) y
  have hS : ∀ a b c, S a b c =
      partialDeriv (E := E) a (chartGramOnE (I := I) g α c b) y +
        partialDeriv (E := E) b (chartGramOnE (I := I) g α c a) y -
        partialDeriv (E := E) c (chartGramOnE (I := I) g α a b) y := fun _ _ _ => rfl
  have hsubst :
      (∑ l : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α k i l y *
            chartGramOnE (I := I) g α l j y) +
        (∑ l : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k j l y *
              chartGramOnE (I := I) g α l i y) =
      (∑ l : Fin (Module.finrank ℝ E),
          ((1 / 2 : ℝ) * ∑ m : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α l m y * S k i m) *
              chartGramOnE (I := I) g α l j y) +
      (∑ l : Fin (Module.finrank ℝ E),
          ((1 / 2 : ℝ) * ∑ m : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α l m y * S k j m) *
              chartGramOnE (I := I) g α l i y) := rfl
  rw [hsubst]
  have hT1 :
      (∑ l : Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) * ∑ m : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α l m y * S k i m) *
            chartGramOnE (I := I) g α l j y) =
      (1 / 2 : ℝ) *
        ∑ m : Fin (Module.finrank ℝ E), S k i m *
          (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α l m y *
                chartGramOnE (I := I) g α l j y) := by
    have hreshape :
        (∑ l : Fin (Module.finrank ℝ E),
          ((1 / 2 : ℝ) * ∑ m : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α l m y * S k i m) *
              chartGramOnE (I := I) g α l j y) =
        ∑ l : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (1 / 2 : ℝ) *
            (chartInvGramOnE (I := I) g α l m y * S k i m *
              chartGramOnE (I := I) g α l j y) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hreshape, Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  have hT2 :
      (∑ l : Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) * ∑ m : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α l m y * S k j m) *
            chartGramOnE (I := I) g α l i y) =
      (1 / 2 : ℝ) *
        ∑ m : Fin (Module.finrank ℝ E), S k j m *
          (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α l m y *
                chartGramOnE (I := I) g α l i y) := by
    have hreshape :
        (∑ l : Fin (Module.finrank ℝ E),
          ((1 / 2 : ℝ) * ∑ m : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α l m y * S k j m) *
              chartGramOnE (I := I) g α l i y) =
        ∑ l : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (1 / 2 : ℝ) *
            (chartInvGramOnE (I := I) g α l m y * S k j m *
              chartGramOnE (I := I) g α l i y) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hreshape, Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hT1, hT2]
  have hcollapse1 : ∀ m : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α l m y *
            chartGramOnE (I := I) g α l j y) =
        (if m = j then (1 : ℝ) else 0) := by
    intro m
    exact sum_chartInvGramOnE_chartGramOnE_right (I := I) g α hytgt m j
  have hcollapse2 : ∀ m : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α l m y *
            chartGramOnE (I := I) g α l i y) =
        (if m = i then (1 : ℝ) else 0) := by
    intro m
    exact sum_chartInvGramOnE_chartGramOnE_right (I := I) g α hytgt m i
  rw [show
      ((1 / 2 : ℝ) *
        ∑ m : Fin (Module.finrank ℝ E), S k i m *
          (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α l m y *
                chartGramOnE (I := I) g α l j y)) +
      ((1 / 2 : ℝ) *
        ∑ m : Fin (Module.finrank ℝ E), S k j m *
          (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α l m y *
                chartGramOnE (I := I) g α l i y)) =
      ((1 / 2 : ℝ) *
        ∑ m : Fin (Module.finrank ℝ E),
          S k i m * (if m = j then (1 : ℝ) else 0)) +
      ((1 / 2 : ℝ) *
        ∑ m : Fin (Module.finrank ℝ E),
          S k j m * (if m = i then (1 : ℝ) else 0)) from by
    congr 2
    · refine Finset.sum_congr rfl (fun m _ => ?_); rw [hcollapse1 m]
    · refine Finset.sum_congr rfl (fun m _ => ?_); rw [hcollapse2 m]]
  rw [show
      (∑ m : Fin (Module.finrank ℝ E),
          S k i m * (if m = j then (1 : ℝ) else 0)) =
        S k i j from by
    rw [Finset.sum_eq_single j]
    · simp
    · intro m _ hmj
      simp [hmj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj]
  rw [show
      (∑ m : Fin (Module.finrank ℝ E),
          S k j m * (if m = i then (1 : ℝ) else 0)) =
        S k j i from by
    rw [Finset.sum_eq_single i]
    · simp
    · intro m _ hmi
      simp [hmi]
    · intro hi
      exact absurd (Finset.mem_univ i) hi]
  rw [hS k i j, hS k j i]
  rw [partialDeriv_chartGramOnE_swap_indices (I := I) g α k j i y,
      partialDeriv_chartGramOnE_swap_indices (I := I) g α i j k y,
      partialDeriv_chartGramOnE_swap_indices (I := I) g α j k i y,
      partialDeriv_chartGramOnE_swap_indices (I := I) g α j i k y,
      partialDeriv_chartGramOnE_swap_indices (I := I) g α i k j y]
  ring

/-- **Chart metric compatibility identity** (single-sum form): for
`y ∈ interior (extChartAt I α).target`,
$$\partial_k G_{ij}(\alpha, y) = \sum_l \bigl(\Gamma^l{}_{ki}(\alpha, y)\, G_{lj}(\alpha, y)
  + \Gamma^l{}_{kj}(\alpha, y)\, G_{li}(\alpha, y)\bigr).$$

This is the metric-compatibility property of the Levi-Civita Christoffel symbol
of the second kind in chart coordinates, in the combined single-sum form. -/
theorem chartGramOnE_partialDeriv_eq_christoffel_sum
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y =
      ∑ l : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α k i l y *
            chartGramOnE (I := I) g α l j y +
          chartChristoffel (I := I) g α k j l y *
            chartGramOnE (I := I) g α l i y) := by
  classical
  rw [chartGramOnE_partialDeriv_eq_christoffel_sum_split (I := I) g α i j k hy]
  rw [← Finset.sum_add_distrib]

end Geometry
end DifferentialGeometry
