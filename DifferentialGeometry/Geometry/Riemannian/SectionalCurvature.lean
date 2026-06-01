import DifferentialGeometry.Geometry.Curvature.Riemann

set_option linter.unusedSectionVars false

/-!
# Sectional curvature

For a smooth Riemannian metric `g` on a smooth manifold `M`, the **sectional
curvature** at `p : M` of the 2-plane spanned by `v, w ∈ T_p M` is the scalar
$$K_g(p; v, w) := \frac{g\bigl(R(v, w)\,w,\ v\bigr)}{g(v, v)\, g(w, w) - g(v, w)^2},$$
where `R` is the Riemann curvature tensor of the Levi-Civita connection.

The denominator is the squared `g`-area of the parallelogram spanned by `v` and
`w`; by Cauchy–Schwarz it vanishes precisely when `v, w` are linearly dependent.

We express the definition in chart coordinates: lowering the upper index of the
chart Riemann tensor `R^l{}_{ijk}` by the chart Gram matrix produces the (0,4)
tensor `R_{ijkl}`, and the numerator is the quartic
$\sum_{i,j,k,l} v^l w^i v^j w^k\, R_{ijkl}(p, \varphi_p(p))$
in the model-basis components.

## Main definitions

* `chartRiemannLower g p i j k l y` — the lowered chart Riemann tensor.
* `sectionalCurvatureNumerator g p v w` — the numerator `⟨R(v, w) w, v⟩_g`.
* `sectionalCurvatureDenominator g p v w` — the Gram determinant
  `g(v, v) g(w, w) - g(v, w)^2`.
* `sectionalCurvature g p v w` — the quotient. Junk value `0` on linearly
  dependent inputs.

## Main results

* `sectionalCurvatureDenominator_nonneg` — Cauchy–Schwarz: the denominator is
  non-negative.
* `sectionalCurvature_of_linearly_dependent_{left,right}`,
  `sectionalCurvature_self`, `sectionalCurvature_zero_{left,right}` — junk
  value identities.
* `sectionalCurvatureNumerator_smul_{left,right}` and the corresponding
  denominator and quotient lemmas — quadratic scaling in each argument and
  the resulting scaling invariance of `K`.
* `sectionalCurvature_symm_of_chartRiemannLower_second_pair_antisymm` —
  hypothesis-bearing symmetry `K(v, w) = K(w, v)`. The metric-compatibility
  antisymmetry of the second pair of `R_{ijkl}` is supplied externally, in
  the same style as `ricciFun_symm_of_chartRicciTensor_symm`.
-/

noncomputable section

open Bundle Manifold Set Finset
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- **The lowered chart-coordinate Riemann tensor**
`R_{ijkl}(α, y) := ∑_m g_{lm}(α, y) · R^m{}_{ijk}(α, y)`.
Inherits the project's convention: `(j, k)` is the antisymmetric pair,
`i` is the "vector" index, `l` is the new lowered index. -/
def chartRiemannLower (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ m : Fin (Module.finrank ℝ E),
    chartGramOnE (I := I) g α l m y *
      chartRiemannTensor (I := I) g α i j k m y

@[simp] lemma chartRiemannLower_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    chartRiemannLower (I := I) g α i j k l y =
      ∑ m : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α l m y *
          chartRiemannTensor (I := I) g α i j k m y := rfl

/-- Antisymmetry in the antisymmetric pair `(j, k)`; inherited. -/
theorem chartRiemannLower_antisymm_jk
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    chartRiemannLower (I := I) g α i j k l y =
      - chartRiemannLower (I := I) g α i k j l y := by
  classical
  rw [chartRiemannLower_def, chartRiemannLower_def, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [chartRiemannTensor_antisymm_jk]
  ring

/-- **The numerator `⟨R(v, w) w, v⟩_g` of the sectional curvature**,
expressed in chart coordinates as
`∑_{i,j,k,l} v^l w^i v^j w^k R_{ijkl}(p, ϕ_p(p))`.
Components are read off in `chartModelBasis E`: `i` is the Z-slot index of
the Riemann operator (contracted with `w^i`), `(j, k)` is the antisymmetric
pair (contracted with `(v^j, w^k)`), `l` is the lowered output index
(contracted with `v^l`). -/
def sectionalCurvatureNumerator (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) l *
            ((chartModelBasis E).repr w) i *
              ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w) k *
                  chartRiemannLower (I := I) g p i j k l (extChartAt I p p)

@[simp] lemma sectionalCurvatureNumerator_def
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvatureNumerator (I := I) g p v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr v) l *
                ((chartModelBasis E).repr w) i *
                  ((chartModelBasis E).repr v) j *
                    ((chartModelBasis E).repr w) k *
                      chartRiemannLower (I := I) g p i j k l
                        (extChartAt I p p) := rfl

/-- **The denominator of the sectional curvature**: the `g`-Gram
determinant `g(v, v) g(w, w) - g(v, w)^2`. By Cauchy–Schwarz this is
non-negative, and vanishes iff `v, w` are linearly dependent. -/
def sectionalCurvatureDenominator (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2

@[simp] lemma sectionalCurvatureDenominator_def
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p v w =
      g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2 := rfl

/-- **The sectional curvature of the 2-plane spanned by `v, w ∈ T_p M`**:
the quotient `sectionalCurvatureNumerator / sectionalCurvatureDenominator`.
Junk value `0` is returned when the denominator vanishes (i.e. `v, w`
linearly dependent). -/
def sectionalCurvature (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  sectionalCurvatureNumerator (I := I) g p v w /
    sectionalCurvatureDenominator (I := I) g p v w

@[simp] lemma sectionalCurvature_def
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v w =
      sectionalCurvatureNumerator (I := I) g p v w /
        sectionalCurvatureDenominator (I := I) g p v w := rfl

/-- **Cauchy–Schwarz for `g`**: `g(v, w)^2 ≤ g(v, v) * g(w, w)`. Discriminant
argument on the non-negative quadratic `t ↦ g(t • v + w, t • v + w)`. -/
private lemma chart_metric_cauchy_schwarz
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    (g.inner p v w) ^ 2 ≤ g.inner p v v * g.inner p w w := by
  have hq_nonneg : ∀ t : ℝ, 0 ≤ g.inner p (t • v + w) (t • v + w) := by
    intro t
    by_cases htv : t • v + w = 0
    · rw [htv]; simp
    · exact (g.pos p _ htv).le
  have hq_expand : ∀ t : ℝ,
      g.inner p (t • v + w) (t • v + w) =
        t ^ 2 * g.inner p v v + 2 * t * g.inner p v w + g.inner p w w := by
    intro t
    have h_first : g.inner p (t • v + w) =
        t • g.inner p v + g.inner p w := by
      rw [map_add, map_smul]
    rw [h_first, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, ContinuousLinearMap.map_add, ContinuousLinearMap.map_add,
        ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
        smul_eq_mul, smul_eq_mul, g.symm p w v]
    ring
  have hA_nonneg : 0 ≤ g.inner p v v := by
    by_cases hv : v = 0
    · rw [hv]; simp
    · exact (g.pos p v hv).le
  have hC_nonneg : 0 ≤ g.inner p w w := by
    by_cases hw : w = 0
    · rw [hw]; simp
    · exact (g.pos p w hw).le
  by_cases hA_zero : g.inner p v v = 0
  · have hv_zero : v = 0 := by
      by_contra hv_ne
      exact absurd hA_zero (ne_of_gt (g.pos p v hv_ne))
    have hB_zero : g.inner p v w = 0 := by
      rw [hv_zero]
      simp
    rw [hB_zero, hA_zero]
    simp
  · have hA_pos : 0 < g.inner p v v :=
      lt_of_le_of_ne hA_nonneg (Ne.symm hA_zero)
    have h_at_t := hq_nonneg (-g.inner p v w / g.inner p v v)
    rw [hq_expand] at h_at_t
    have h_simplify :
        (-g.inner p v w / g.inner p v v) ^ 2 * g.inner p v v +
            2 * (-g.inner p v w / g.inner p v v) * g.inner p v w +
            g.inner p w w =
          g.inner p w w - (g.inner p v w) ^ 2 / g.inner p v v := by
      field_simp; ring
    rw [h_simplify] at h_at_t
    have h_expand :
        g.inner p v v *
          (g.inner p w w - (g.inner p v w) ^ 2 / g.inner p v v) =
          g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2 := by
      field_simp
    have h_mul := mul_nonneg hA_pos.le h_at_t
    rw [h_expand] at h_mul
    linarith

/-- The sectional-curvature denominator is non-negative (Cauchy–Schwarz). -/
theorem sectionalCurvatureDenominator_nonneg
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    0 ≤ sectionalCurvatureDenominator (I := I) g p v w := by
  rw [sectionalCurvatureDenominator_def]
  linarith [chart_metric_cauchy_schwarz (I := I) g p v w]

/-- The pair `(c • v, v)` has zero `g`-Gram determinant: Cauchy–Schwarz is an
equality on collinear vectors. -/
theorem sectionalCurvatureDenominator_eq_zero_of_left_smul
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p (c • v) v = 0 := by
  rw [sectionalCurvatureDenominator_def]
  have h1 : g.inner p (c • v) = c • g.inner p v := map_smul _ _ _
  have hLL : g.inner p (c • v) (c • v) = c ^ 2 * g.inner p v v := by
    rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]; ring
  have hL : g.inner p (c • v) v = c * g.inner p v v := by
    rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hLL, hL]; ring

/-- The pair `(v, c • v)` has zero `g`-Gram determinant. -/
theorem sectionalCurvatureDenominator_eq_zero_of_right_smul
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p v (c • v) = 0 := by
  rw [sectionalCurvatureDenominator_def]
  have h1 : g.inner p (c • v) = c • g.inner p v := map_smul _ _ _
  have hRR : g.inner p (c • v) (c • v) = c ^ 2 * g.inner p v v := by
    rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]; ring
  have hR : g.inner p v (c • v) = c * g.inner p v v := by
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [hRR, hR]; ring

/-- Quadratic scaling of the numerator in `v`: `Num(c • v, w) = c^2 · Num(v, w)`. -/
theorem sectionalCurvatureNumerator_smul_left
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v w : TangentSpace I p) :
    sectionalCurvatureNumerator (I := I) g p (c • v) w =
      c ^ 2 * sectionalCurvatureNumerator (I := I) g p v w := by
  classical
  rw [sectionalCurvatureNumerator_def, sectionalCurvatureNumerator_def,
      Finset.mul_sum]
  refine Finset.sum_congr rfl ?_; intro i _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro j _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro k _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro l _
  have h_repr : (chartModelBasis E).repr (c • v) =
      c • (chartModelBasis E).repr v := map_smul _ _ _
  rw [h_repr]
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Quadratic scaling of the numerator in `w`: `Num(v, c • w) = c^2 · Num(v, w)`. -/
theorem sectionalCurvatureNumerator_smul_right
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v w : TangentSpace I p) :
    sectionalCurvatureNumerator (I := I) g p v (c • w) =
      c ^ 2 * sectionalCurvatureNumerator (I := I) g p v w := by
  classical
  rw [sectionalCurvatureNumerator_def, sectionalCurvatureNumerator_def,
      Finset.mul_sum]
  refine Finset.sum_congr rfl ?_; intro i _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro j _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro k _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro l _
  have h_repr : (chartModelBasis E).repr (c • w) =
      c • (chartModelBasis E).repr w := map_smul _ _ _
  rw [h_repr]
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Quadratic scaling of the denominator in `v`. -/
theorem sectionalCurvatureDenominator_smul_left
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v w : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p (c • v) w =
      c ^ 2 * sectionalCurvatureDenominator (I := I) g p v w := by
  rw [sectionalCurvatureDenominator_def, sectionalCurvatureDenominator_def]
  have h1 : g.inner p (c • v) = c • g.inner p v := map_smul _ _ _
  have hLL : g.inner p (c • v) (c • v) = c ^ 2 * g.inner p v v := by
    rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]; ring
  have hL : g.inner p (c • v) w = c * g.inner p v w := by
    rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hLL, hL]; ring

/-- Quadratic scaling of the denominator in `w`. -/
theorem sectionalCurvatureDenominator_smul_right
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v w : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p v (c • w) =
      c ^ 2 * sectionalCurvatureDenominator (I := I) g p v w := by
  rw [sectionalCurvatureDenominator_def, sectionalCurvatureDenominator_def]
  have h1 : g.inner p (c • w) = c • g.inner p w := map_smul _ _ _
  have hRR : g.inner p (c • w) (c • w) = c ^ 2 * g.inner p w w := by
    rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]; ring
  have hR : g.inner p v (c • w) = c * g.inner p v w := by
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [hRR, hR]; ring

/-- **Scaling invariance of `K` in the left argument**: `K(c • v, w) = K(v, w)`
for `c ≠ 0`. -/
theorem sectionalCurvature_smul_left
    (g : SmoothRiemannianMetric I M) (p : M) {c : ℝ} (hc : c ≠ 0)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (c • v) w =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_def, sectionalCurvature_def,
      sectionalCurvatureNumerator_smul_left,
      sectionalCurvatureDenominator_smul_left,
      mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-- **Scaling invariance of `K` in the right argument**: `K(v, c • w) = K(v, w)`
for `c ≠ 0`. -/
theorem sectionalCurvature_smul_right
    (g : SmoothRiemannianMetric I M) (p : M) {c : ℝ} (hc : c ≠ 0)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v (c • w) =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_def, sectionalCurvature_def,
      sectionalCurvatureNumerator_smul_right,
      sectionalCurvatureDenominator_smul_right,
      mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-- Junk value on `(c • v, v)`: `K(c • v, v) = 0`. -/
theorem sectionalCurvature_of_linearly_dependent_left
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v : TangentSpace I p) :
    sectionalCurvature (I := I) g p (c • v) v = 0 := by
  rw [sectionalCurvature_def,
      sectionalCurvatureDenominator_eq_zero_of_left_smul]
  exact div_zero _

/-- Junk value on `(v, c • v)`: `K(v, c • v) = 0`. -/
theorem sectionalCurvature_of_linearly_dependent_right
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v : TangentSpace I p) :
    sectionalCurvature (I := I) g p v (c • v) = 0 := by
  rw [sectionalCurvature_def,
      sectionalCurvatureDenominator_eq_zero_of_right_smul]
  exact div_zero _

/-- Junk value on the diagonal: `K(v, v) = 0`. -/
theorem sectionalCurvature_self
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    sectionalCurvature (I := I) g p v v = 0 := by
  have h := sectionalCurvature_of_linearly_dependent_left (I := I) g p 1 v
  rw [one_smul] at h; exact h

/-- Junk value when the left argument is zero. -/
theorem sectionalCurvature_zero_left
    (g : SmoothRiemannianMetric I M) (p : M)
    (w : TangentSpace I p) :
    sectionalCurvature (I := I) g p 0 w = 0 := by
  have h := sectionalCurvature_of_linearly_dependent_left (I := I) g p 0 w
  rw [zero_smul] at h; exact h

/-- Junk value when the right argument is zero. -/
theorem sectionalCurvature_zero_right
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    sectionalCurvature (I := I) g p v 0 = 0 := by
  have h := sectionalCurvature_of_linearly_dependent_right (I := I) g p 0 v
  rw [zero_smul] at h; exact h

/-- **Sign invariance of `K` in the left argument**: `K(-v, w) = K(v, w)`.
Follows from `sectionalCurvature_smul_left` applied with `c = -1`. -/
theorem sectionalCurvature_neg_left
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (-v) w =
      sectionalCurvature (I := I) g p v w := by
  have h := sectionalCurvature_smul_left (I := I) g p
    (c := (-1 : ℝ)) (by norm_num) v w
  rw [neg_one_smul] at h
  exact h

/-- **Sign invariance of `K` in the right argument**: `K(v, -w) = K(v, w)`.
Follows from `sectionalCurvature_smul_right` applied with `c = -1`. -/
theorem sectionalCurvature_neg_right
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v (-w) =
      sectionalCurvature (I := I) g p v w := by
  have h := sectionalCurvature_smul_right (I := I) g p
    (c := (-1 : ℝ)) (by norm_num) v w
  rw [neg_one_smul] at h
  exact h

/-- **Double-slot sign invariance of `K`**: `K(-v, -w) = K(v, w)`.
Follows by composing `sectionalCurvature_neg_left` and
`sectionalCurvature_neg_right`. -/
theorem sectionalCurvature_neg_neg
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (-v) (-w) =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_neg_left (I := I) g p v (-w),
      sectionalCurvature_neg_right (I := I) g p v w]

/-- **Joint scaling invariance of `K`**: `K(c • v, d • w) = K(v, w)` for
`c ≠ 0` and `d ≠ 0`. Follows by composing `sectionalCurvature_smul_left`
and `sectionalCurvature_smul_right`. -/
theorem sectionalCurvature_smul_smul
    (g : SmoothRiemannianMetric I M) (p : M) {c d : ℝ}
    (hc : c ≠ 0) (hd : d ≠ 0) (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (c • v) (d • w) =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_smul_left (I := I) g p hc v (d • w),
      sectionalCurvature_smul_right (I := I) g p hd v w]

/-- **Negated-scaling invariance of `K` in the left argument**:
`K(-(c • v), w) = K(v, w)` for `c ≠ 0`. Follows by composing
`sectionalCurvature_neg_left` and `sectionalCurvature_smul_left`. -/
theorem sectionalCurvature_neg_smul_left
    (g : SmoothRiemannianMetric I M) (p : M) {c : ℝ} (hc : c ≠ 0)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (-(c • v)) w =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_neg_left (I := I) g p (c • v) w,
      sectionalCurvature_smul_left (I := I) g p hc v w]

/-- **Negated-scaling invariance of `K` in the right argument**:
`K(v, -(c • w)) = K(v, w)` for `c ≠ 0`. Follows by composing
`sectionalCurvature_neg_right` and `sectionalCurvature_smul_right`. -/
theorem sectionalCurvature_neg_smul_right
    (g : SmoothRiemannianMetric I M) (p : M) {c : ℝ} (hc : c ≠ 0)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v (-(c • w)) =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_neg_right (I := I) g p v (c • w),
      sectionalCurvature_smul_right (I := I) g p hc v w]

/-- **Reindex helper.** Complete-reversal reindex of a 4-fold sum, obtained
by six adjacent-swap applications of `Finset.sum_comm`. -/
private lemma chartFourFold_reverse_sum
    {n : ℕ}
    (α β : Fin n → ℝ) (T : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        α l * β i * α j * β k * T i j k l) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        β l * α i * β j * α k * T l k j i) := by
  classical
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, l, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, l]; rw [Finset.sum_comm]
  conv_lhs => enter [2, l, 2, k]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_; intro l _
  refine Finset.sum_congr rfl ?_; intro k _
  refine Finset.sum_congr rfl ?_; intro j _
  refine Finset.sum_congr rfl ?_; intro i _
  ring

/-- Hypothesis-bearing symmetry of the numerator: given the second-pair
antisymmetry `R_{ijkl} = -R_{ljki}` (metric-compatibility identity), the
numerator is symmetric in `(v, w)`. -/
theorem sectionalCurvatureNumerator_symm_of_chartRiemannLower_second_pair_antisymm
    (g : SmoothRiemannianMetric I M) (p : M)
    (h_pair : ∀ i j k l : Fin (Module.finrank ℝ E),
        chartRiemannLower (I := I) g p i j k l (extChartAt I p p) =
          - chartRiemannLower (I := I) g p l j k i (extChartAt I p p))
    (v w : TangentSpace I p) :
    sectionalCurvatureNumerator (I := I) g p v w =
      sectionalCurvatureNumerator (I := I) g p w v := by
  classical
  have h_combined : ∀ i j k l : Fin (Module.finrank ℝ E),
      chartRiemannLower (I := I) g p i j k l (extChartAt I p p) =
        chartRiemannLower (I := I) g p l k j i (extChartAt I p p) := by
    intro i j k l
    rw [chartRiemannLower_antisymm_jk (I := I) g p i j k l, h_pair i k j l]
    ring
  rw [sectionalCurvatureNumerator_def, sectionalCurvatureNumerator_def]
  refine Eq.trans ?_ (chartFourFold_reverse_sum (n := Module.finrank ℝ E)
    (α := fun i => ((chartModelBasis E).repr v) i)
    (β := fun i => ((chartModelBasis E).repr w) i)
    (T := fun a b c d =>
      chartRiemannLower (I := I) g p d c b a (extChartAt I p p)))
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [h_combined i j k l]

/-- The denominator is symmetric in `(v, w)` (unconditional, by `g.symm`). -/
theorem sectionalCurvatureDenominator_symm
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p v w =
      sectionalCurvatureDenominator (I := I) g p w v := by
  rw [sectionalCurvatureDenominator_def, sectionalCurvatureDenominator_def]
  rw [g.symm p v w]
  ring

/-- Hypothesis-bearing symmetry `K(v, w) = K(w, v)`: given the second-pair
antisymmetry `R_{ijkl} = -R_{ljki}` (metric-compatibility identity). -/
theorem sectionalCurvature_symm_of_chartRiemannLower_second_pair_antisymm
    (g : SmoothRiemannianMetric I M) (p : M)
    (h_pair : ∀ i j k l : Fin (Module.finrank ℝ E),
        chartRiemannLower (I := I) g p i j k l (extChartAt I p p) =
          - chartRiemannLower (I := I) g p l j k i (extChartAt I p p))
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v w =
      sectionalCurvature (I := I) g p w v := by
  rw [sectionalCurvature_def, sectionalCurvature_def]
  rw [sectionalCurvatureNumerator_symm_of_chartRiemannLower_second_pair_antisymm
        (I := I) g p h_pair v w,
      sectionalCurvatureDenominator_symm (I := I) g p v w]

end Riemannian
end Geometry
end DifferentialGeometry
