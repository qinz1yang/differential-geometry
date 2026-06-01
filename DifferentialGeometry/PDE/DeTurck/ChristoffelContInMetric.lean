import DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ChartVectorField

/-!
# Continuity in the metric of the chart-coordinate DeTurck vector-field component

For a fixed background metric `g'` and a one-parameter family of metrics `g_DT t`
varying continuously in `t`, the `k`-th chart-coordinate component
$$W^k(g, g')(y) = \sum_{a,b} G(g)^{ab}(y)\,
    \bigl(\Gamma^k{}_{ab}(g)(y) - \Gamma^k{}_{ab}(g')(y)\bigr)$$
of the DeTurck vector field is continuous in `t`.

The chart formula expresses `W^k` rationally in:

* the chart-Gram entries `G_{ij}(g, α) y = g.inner _ (e_i) (e_j)`,
* and their model-space partial derivatives `∂_l G_{ij}(g, α)(y)`.

This file proves that under continuity-in-`t` of these chart-coordinate data, the
chart inverse Gram matrix, the chart Christoffel symbols, and ultimately
`chartDeTurckVFComp` are continuous in `t` at a fixed chart point `y`.

The matrix inverse is handled via Cramer's rule (`A⁻¹ = (det A)⁻¹ • adjugate A`),
which is valid because `g_DT t` is positive-definite at the chart point — its
Gram-matrix determinant is strictly positive, hence non-zero, hence the inverse
formula `det⁻¹ · adjugate` is continuous in `t` whenever the entries are.

## Main results

* `chartGramOnE_det_continuous_in_metric_at` — `t ↦ det(G(g_DT t, α)(y))` is
  continuous on `s` from continuity of the entries.
* `chartGramOnE_adjugate_continuous_in_metric_at` — `t ↦ adjugate(G(g_DT t, α)(y)) i j`
  is continuous on `s` from continuity of the entries.
* `chartInvGramOnE_continuous_in_metric_at` — `t ↦ G(g_DT t, α)⁻¹(y) i j` is
  continuous on `s` from continuity of the entries plus positive-definiteness.
* `chartChristoffel_continuous_in_metric_at` — `t ↦ chartChristoffel (g_DT t) α a b k y`
  is continuous on `s` from continuity of the entries and of their partial
  derivatives, plus positive-definiteness.
* `chartDeTurckVFComp_continuous_in_metric_at` — `t ↦ chartDeTurckVFComp (g_DT t) g' α k y`
  is continuous on `s` under the same hypotheses.

The hypotheses are minimal, separable chart-coordinate continuity statements;
they are NOT a repackaging of the conclusion. The substance is Cramer's rule
combined with the explicit chart formula for `chartChristoffel`.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Determinant of the chart Gram matrix is continuous in the metric.**

If at the chart point `y` each chart-Gram entry `t ↦ chartGramOnE (g_DT t) α i j y`
is continuous on `s`, then `t ↦ det(G(g_DT t, α)(y))` is continuous on `s`.  The
determinant is a polynomial (Leibniz formula) in the matrix entries. -/
theorem chartGramOnE_det_continuous_in_metric_at
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (y : E)
    (s : Set ℝ)
    (h_entry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α i j y) s) :
    ContinuousOn
      (fun t : ℝ => (Matrix.of fun i j => chartGramOnE (I := I) (g_DT t) α i j y).det)
      s := by
  classical
  have hrewrite :
      (fun t : ℝ => (Matrix.of fun i j => chartGramOnE (I := I) (g_DT t) α i j y).det)
        = fun t : ℝ =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ k : Fin (Module.finrank ℝ E),
                  (Matrix.of fun i j => chartGramOnE (I := I) (g_DT t) α i j y) (σ k) k := by
    funext t
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hrewrite]
  refine continuousOn_finset_sum _ (fun σ _ => ?_)
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finset_prod _ (fun k _ => ?_)
  have h := h_entry (σ k) k
  refine h.congr ?_
  intro t _
  rfl

/-- **Each adjugate entry of the chart Gram matrix is continuous in the metric.**

The `(i,j)` adjugate entry is the determinant of the matrix with the `j`-th row
replaced by the standard basis vector `e_i`.  This is a polynomial in the chart
Gram entries — every untouched row is a Gram entry (continuous in `t` by
hypothesis), and the replaced row is a constant. -/
theorem chartGramOnE_adjugate_continuous_in_metric_at
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (y : E)
    (s : Set ℝ)
    (h_entry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α i j y) s)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun t : ℝ =>
        (Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y).adjugate i j)
      s := by
  classical
  have hrewrite :
      (fun t : ℝ =>
          (Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y).adjugate i j)
        = fun t : ℝ =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ k : Fin (Module.finrank ℝ E),
                  ((Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y).updateRow j
                    (Pi.single i (1 : ℝ))) (σ k) k := by
    funext t
    rw [Matrix.adjugate_apply, Matrix.det_apply]
    simp [Units.smul_def]
  rw [hrewrite]
  refine continuousOn_finset_sum _ (fun σ _ => ?_)
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finset_prod _ (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq :
        (fun t : ℝ =>
            ((Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y).updateRow j
              (Pi.single i (1 : ℝ))) (σ k) k)
          = fun _ : ℝ =>
              (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) i (1 : ℝ)) k := by
      funext t
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact continuousOn_const
  · have heq :
        (fun t : ℝ =>
            ((Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y).updateRow j
              (Pi.single i (1 : ℝ))) (σ k) k)
          = fun t : ℝ =>
              (Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y) (σ k) k := by
      funext t
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    have h := h_entry (σ k) k
    refine h.congr ?_
    intro t _
    rfl

/-- **The chart inverse Gram entry is continuous in the metric.**

Assuming continuity-in-`t` of the chart Gram entries at the chart point `y`, and
that the corresponding manifold point `x` lies in the chart-`α` base set (so the
Gram matrix is positive-definite and the determinant is non-zero), the chart
inverse Gram entry `t ↦ chartInvGramOnE (g_DT t) α i j y` is continuous on `s`. -/
theorem chartInvGramOnE_continuous_in_metric_at
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (y : E)
    (s : Set ℝ)
    (h_entry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α i j y) s)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun t : ℝ => chartInvGramOnE (I := I) (g_DT t) α i j y) s := by
  classical
  set Gmat : ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun t => Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y with hGmat_def
  have hGmat_eq : ∀ t, Gmat t = chartGramMatrix (I := I) (g_DT t) α
      ((extChartAt I α).symm y) := by
    intro t
    ext a b
    rw [hGmat_def]
    simp only [Matrix.of_apply]
    rw [chartGramOnE_def]
  have hcongr : ∀ t ∈ s,
      chartInvGramOnE (I := I) (g_DT t) α i j y =
        ((Gmat t).det)⁻¹ * (Gmat t).adjugate i j := by
    intro t _
    rw [chartInvGramOnE_def]
    unfold chartInvGramMatrix
    have hpos := chartGramMatrix_det_pos (I := I) (g_DT t) α hx
    have hdet_ne : (chartGramMatrix (I := I) (g_DT t) α
        ((extChartAt I α).symm y)).det ≠ 0 := ne_of_gt hpos
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) (g_DT t) α
            ((extChartAt I α).symm y)).det •
          (chartGramMatrix (I := I) (g_DT t) α
            ((extChartAt I α).symm y)).adjugate) i j =
      ((Gmat t).det)⁻¹ * (Gmat t).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul]
    rw [hGmat_eq t]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContinuousOn.congr ?_ hcongr
  refine ContinuousOn.mul ?_ ?_
  · have hdet_cont : ContinuousOn (fun t : ℝ => (Gmat t).det) s := by
      have h := chartGramOnE_det_continuous_in_metric_at (I := I) g_DT α y s h_entry
      exact h
    refine hdet_cont.inv₀ ?_
    intro t _
    have hpos := chartGramMatrix_det_pos (I := I) (g_DT t) α hx
    have : (Gmat t).det = (chartGramMatrix (I := I) (g_DT t) α
        ((extChartAt I α).symm y)).det := by
      rw [hGmat_eq t]
    rw [this]
    exact ne_of_gt hpos
  · exact chartGramOnE_adjugate_continuous_in_metric_at (I := I) g_DT α y s h_entry i j

/-- **The chart Christoffel symbol is continuous in the metric.**

The chart Christoffel symbol of the second kind has the explicit chart formula
$$\Gamma^k{}_{ab}(g)(y) = \tfrac12 \sum_l G(g)^{kl}(y) \,
    \bigl(\partial_a G(g)_{lb}(y) + \partial_b G(g)_{la}(y) - \partial_l G(g)_{ab}(y)\bigr).$$

Under continuity-in-`t` of the chart Gram entries and of their model-direction
partial derivatives at `y`, and positive-definiteness at the corresponding
manifold point, the chart Christoffel symbol is continuous in `t` on `s`. -/
theorem chartChristoffel_continuous_in_metric_at
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (y : E)
    (s : Set ℝ)
    (h_entry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α i j y) s)
    (h_partial : ∀ l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun t : ℝ => partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α i j) y) s)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (a b k : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun t : ℝ => chartChristoffel (I := I) (g_DT t) α a b k y) s := by
  classical
  have hrewrite : (fun t : ℝ => chartChristoffel (I := I) (g_DT t) α a b k y) =
      fun t : ℝ =>
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) (g_DT t) α ((extChartAt I α).symm y) k l *
            (partialDeriv (E := E) a (chartGramOnE (I := I) (g_DT t) α l b) y +
             partialDeriv (E := E) b (chartGramOnE (I := I) (g_DT t) α l a) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α a b) y) := by
    funext t
    rw [chartChristoffel_def]
  rw [hrewrite]
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finset_sum _ (fun l _ => ?_)
  refine ContinuousOn.mul ?_ ?_
  · have hcongr : (fun t : ℝ => chartInvGramMatrix (I := I) (g_DT t) α
            ((extChartAt I α).symm y) k l)
        = fun t : ℝ => chartInvGramOnE (I := I) (g_DT t) α k l y := by
      funext t
      rfl
    rw [hcongr]
    exact chartInvGramOnE_continuous_in_metric_at (I := I) g_DT α y s h_entry hx k l
  · refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.add ?_ ?_
      · exact h_partial a l b
      · exact h_partial b l a
    · exact h_partial l a b

/-- **The chart-coordinate DeTurck-VF component is continuous in the evolving
metric.**

Under continuity-in-`t` of the chart Gram entries of `g_DT t` and of their
model-direction partial derivatives at `y`, and positive-definiteness of `g_DT t`
at the corresponding manifold point, the chart component
`chartDeTurckVFComp (g_DT t) g' α k y` is continuous in `t` on `s`. -/
theorem chartDeTurckVFComp_continuous_in_metric_at
    (g' : SmoothRiemannianMetric I M) (α : M) (y : E)
    (s : Set ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (h_entry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α i j y) s)
    (h_partial : ∀ l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun t : ℝ => partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α i j) y) s)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun t : ℝ =>
        DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT t) g' α k y) s := by
  classical
  have hrewrite :
      (fun t : ℝ => DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT t) g' α k y)
        = fun t : ℝ =>
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) (g_DT t) α a b y *
                (chartChristoffel (I := I) (g_DT t) α a b k y -
                  chartChristoffel (I := I) g' α a b k y) := by
    funext t
    rw [DeTurckLinearization.chartDeTurckVFComp_def]
  rw [hrewrite]
  refine continuousOn_finset_sum _ (fun a _ => ?_)
  refine continuousOn_finset_sum _ (fun b _ => ?_)
  refine ContinuousOn.mul ?_ ?_
  · exact chartInvGramOnE_continuous_in_metric_at (I := I) g_DT α y s h_entry hx a b
  · refine ContinuousOn.sub ?_ ?_
    · exact chartChristoffel_continuous_in_metric_at (I := I) g_DT α y s h_entry h_partial hx a b k
    · exact continuousOn_const

end DeTurck
end PDE
end DifferentialGeometry
