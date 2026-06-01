import DifferentialGeometry.Geometry.Hessian
import DifferentialGeometry.Geometry.HessianTrace
import DifferentialGeometry.Geometry.Curvature.Ricci

/-!
# Chart-level metric / Christoffel identities

This file collects a small set of additive identities relating the chart Gram
matrix `chartGramMatrix g α`, its pull-back `chartGramOnE g α`, the chart
Christoffel symbol `chartChristoffel g α`, and the underlying Riemannian inner
product `g.inner`.

Three groups of results:

* Chart pull-back of the inner product. The inner product `g.inner x` reads off
  in the chart-local frame as the chart Gram matrix; with `v, w` decomposed in
  the chart-basis frame, `g.inner x v w = ∑_{ij} v^i w^j G_{ij}(α, x)`.

* Chart metric identity. The defining metric-compatibility property of the
  Christoffel symbol of the second kind in chart coordinates,
  $$\partial_k G_{ij} = \sum_l \Gamma^l{}_{ki}\, G_{lj}
    + \sum_l \Gamma^l{}_{kj}\, G_{li},$$
  derived purely algebraically from the explicit definition
  `chartChristoffel = (1/2) G^{-1}(\partial G + \partial G - \partial G)` and
  the pairing `G^{-1} G = I`.

* Smoothness of the chart Christoffel symbol. The Christoffel symbol
  `chartChristoffel g α i j k` is `C^∞` on the interior of the chart target,
  derived from the smoothness of `chartGramOnE`, `chartInvGramOnE` and their
  partial derivatives.

These identities form the chart-level scaffolding for downstream covariant-
derivative formulas and curvature computations.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- Evaluation of `g.inner x` on two chart-basis frame vectors recovers the
chart Gram matrix entry. -/
lemma g_inner_eq_chartGramMatrix_basis
    (g : SmoothRiemannianMetric I M) (α : M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) =
      chartGramMatrix (I := I) g α x i j :=
  (chartGramMatrix_apply (I := I) g α x i j).symm

/-- Decomposition of a tangent vector in the chart-basis frame: at any point of
the trivialization base set, `v` is the sum over `i` of the trivialization
coordinates of `v` (with respect to the model-space basis) scaled by the
chart-basis frame vectors. -/
lemma chartBasisVecFiber_recompose
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : TangentSpace I x) :
    v = ∑ i : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
          ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v)) i •
        chartBasisVecFiber (I := I) α i x := by
  classical
  set T : Bundle.Trivialization E
      (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α
  have hsymm_apply :
      T.symmL ℝ x (T.continuousLinearMapAt ℝ x v) = v :=
    T.symmL_continuousLinearMapAt (R := ℝ) hx v
  set vE : E := T.continuousLinearMapAt ℝ x v with hvE_def
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E
  have hdecomp : vE = ∑ i, b.repr vE i • b i :=
    (Module.Basis.sum_repr b vE).symm
  have hsymm_sum := congrArg (T.symmL ℝ x) hdecomp
  rw [hsymm_apply] at hsymm_sum
  rw [map_sum] at hsymm_sum
  have hbasis : ∀ i, T.symmL ℝ x (b i) = chartBasisVecFiber (I := I) α i x := by
    intro i; rfl
  rw [hsymm_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, hbasis i]

/-- **Chart pull-back of `g.inner`.** For tangent vectors `v, w` at `x` in the
trivialization base set at `α`, the inner product `g.inner x v w` decomposes in
the chart-basis frame as the bilinear sum over the trivialization-extracted
components, weighted by `chartGramOnE g α i j (extChartAt I α x)` (i.e. the
chart Gram matrix at `x`). -/
theorem g_inner_eq_chart_sum
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hxsrc : x ∈ (extChartAt I α).source)
    (v w : TangentSpace I x) :
    g.inner x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr
              ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v)) i *
            ((chartModelBasis E).repr
              ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x w)) j *
            chartGramOnE (I := I) g α i j (extChartAt I α x) := by
  classical
  set T : Bundle.Trivialization E
      (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E
  set vE : E := T.continuousLinearMapAt ℝ x v
  set wE : E := T.continuousLinearMapAt ℝ x w
  have hv : v = ∑ i, b.repr vE i • chartBasisVecFiber (I := I) α i x :=
    chartBasisVecFiber_recompose (I := I) α hx v
  have hw : w = ∑ j, b.repr wE j • chartBasisVecFiber (I := I) α j x :=
    chartBasisVecFiber_recompose (I := I) α hx w
  have hchart : ∀ i j : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i j (extChartAt I α x) =
        chartGramMatrix (I := I) g α x i j := by
    intro i j
    unfold chartGramOnE
    rw [(extChartAt I α).left_inv hxsrc]
  rw [hv, hw]
  have hL :
      g.inner x (∑ i, b.repr vE i • chartBasisVecFiber (I := I) α i x)
        = ∑ i, b.repr vE i •
            g.inner x (chartBasisVecFiber (I := I) α i x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
  rw [hL]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [map_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul, smul_eq_mul]
  rw [hchart i j, g_inner_eq_chartGramMatrix_basis (I := I) g α x i j]
  ring

/-- The Gram-inverse pairing identity at a chart-target point: for any
`y ∈ (extChartAt I α).target` and indices `m, j`,
$\sum_l G^{ml}(α, y)\, G_{lj}(α, y) = \delta^m_j$. -/
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

/-- Symmetric form: `∑ l, G^{lm}(y) * G_{lj}(y) = δ^m_j` (using symmetry of
`G^{-1}` in its two indices). -/
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

/-- **Chart metric identity (∂g = Γ·g + g·Γ).**
The defining property of the Levi-Civita Christoffel symbol of the second kind
in chart coordinates: for `y ∈ interior (extChartAt I α).target`,
$$\partial_k G_{ij}(α, y) = \sum_l \Gamma^l{}_{ki}(α, y)\, G_{lj}(α, y)
  + \sum_l \Gamma^l{}_{kj}(α, y)\, G_{li}(α, y).$$ -/
theorem partialDeriv_chartGramOnE_eq_chartChristoffel_sum
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
  have hchristoffel : ∀ (a b c : Fin (Module.finrank ℝ E)),
      chartChristoffel (I := I) g α a b c y =
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α c l y * S a b l := by
    intro a b c
    rfl
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

end Connection
end Integral
end DifferentialGeometry
