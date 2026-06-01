import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.Connection.CurvatureBundling
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Geometry.Curvature.Riemann

/-!
# Bridge between the chart Riemann tensor and the abstract Riemann operator

The chart-coordinate Riemann tensor `chartRiemannTensor g α i j k l y` (defined in
`Integral.Geometry.Curvature.Riemann`) packages the (1, 3)-tensor
$$
  R^l{}_{ijk}(g, \alpha)(y) =
    \partial_j \Gamma^l{}_{ik}(g, \alpha)(y) -
    \partial_k \Gamma^l{}_{ij}(g, \alpha)(y) +
    \sum_m \bigl(\Gamma^l{}_{jm}(g, \alpha)(y)\,\Gamma^m{}_{ik}(g, \alpha)(y) -
                 \Gamma^l{}_{km}(g, \alpha)(y)\,\Gamma^m{}_{ij}(g, \alpha)(y)\bigr).
$$
The abstract Riemann operator `riemannOp (LeviCivita g) x` (defined in
`Integral.Connection.CurvatureBundling`) is the bundled continuous trilinear map
`T_x M →L T_x M →L T_x M →L T_x M` that on smooth global sections evaluates to
$$
  R^{LC}(X, Y) Z(x) = \nabla_X(\nabla_Y Z)(x) - \nabla_Y(\nabla_X Z)(x) - \nabla_{[X, Y]} Z(x).
$$

Both objects describe the Riemann curvature of the Levi-Civita connection. This file
constructs the bridge between them: a continuous trilinear CLM `chartRiemannCLM g x`
whose chart-basis components are exactly the entries of `chartRiemannTensor g x i j k l`
at `(extChartAt I x x)`. The bridge CLM is independent of the (deep) chart-Christoffel
expansion; it is built directly from the chart-Riemann tensor entries via the standard
basis-coordinate sum, mirroring the `ricciFun` construction in
`Integral.Geometry.Curvature.Riemann`.

## Main definitions

* `chartRiemannCLM g x` — the chart-Riemann tensor at `x` packaged as a continuous
  trilinear CLM `T_x M →L T_x M →L T_x M →L T_x M`. By construction,
  `chartRiemannCLM g x v w u` is the basis-coordinate triple sum
  $$
    \sum_{i, j, k, l} u^i \cdot v^j \cdot w^k \cdot R^l{}_{ijk}(g, x)(\varphi_x x) \cdot e_l,
  $$
  where `e_i := (chartModelBasis E) i` and `(u^i, v^j, w^k)` are the basis components
  of the input vectors.

## Main theorems

* `chartRiemannCLM_apply` — the defining triple-sum expansion.
* `chartRiemannCLM_basis_apply` — the chart-basis evaluation:
  `chartRiemannCLM g x (e_j) (e_k) (e_i) = ∑ l, R^l{}_{ijk}(g, x)(ϕ_x x) • e_l`.
* `chartRiemannCLM_repr_basis` — the basis-coordinate identification:
  the `l`-th coordinate of `chartRiemannCLM g x (e_j) (e_k) (e_i)` is
  `R^l{}_{ijk}(g, x)(ϕ_x x)`.
* `chartRiemannCLM_antisymm_jk` — antisymmetry in the first two CLM arguments
  (the differentiation indices), inherited from `chartRiemannTensor_antisymm_jk`.

## Connection with `riemannOp`

The deep identification `chartRiemannCLM g x = riemannOp (LeviCivita g) x` reduces, by
trilinearity in finite dimensions, to a basis identity expanding the right-hand side via
`riemannOp_apply_smooth` and iterating `LeviCivita_chart_apply` twice. The basis
identity is captured by `riemannOp_chartBasis_via_riemannSec`, which expresses the
right-hand-side basis values through the section-level formula `riemannSec` on smooth
global extensions of the chart-basis vectors. The trilinear identification of the two
CLMs is then determined by the per-basis equality.

The fully expanded chart-coordinate identification of the basis values via the
Christoffel formula is the deferred deep step (it iterates the chart-Levi-Civita formula
twice, each step requiring intermediate smoothness on chart-frame extensions). This file
delivers the structural bridge — the CLM definition, basis-evaluation lemmas, and the
section-level reduction of the right-hand side — leaving the iterated chart-Christoffel
identification as a clean down-stream deferred lemma.

## Sign convention

`riemannSec cov X Y Z = ∇_X(∇_Y Z) - ∇_Y(∇_X Z) - ∇_{[X, Y]} Z`. With Mathlib's argument
convention `cov.toFun σ x v ≅ (∇_v σ)(x)`, this matches the standard
`R(X, Y) Z` operator. The chart-Riemann tensor `chartRiemannTensor g α i j k l` adopts
the geometer's convention with differentiation indices `(j, k)` and "vector" index `i`,
so the basis pairing is `chartRiemannCLM g x (e_j) (e_k) (e_i) = ∑ l R^l{}_{ijk} e_l`.
-/

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- The trilinear LinearMap form of the chart-Riemann tensor at `x`. This is the
basis-coordinate sum encoding the chart entries `R^l{}_{ijk}` evaluated at the chart
basepoint. -/
def chartRiemannLin (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun v := {
    toFun := fun w => {
      toFun := fun u =>
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ((chartModelBasis E).repr u i *
                    (chartModelBasis E).repr v j *
                    (chartModelBasis E).repr w k *
                    chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                  ((chartModelBasis E) l : TangentSpace I x)
      map_add' := fun u₁ u₂ => by
        classical
        have hrepr : (chartModelBasis E).repr (u₁ + u₂) =
            (chartModelBasis E).repr u₁ + (chartModelBasis E).repr u₂ := map_add _ _ _
        simp only [hrepr]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        simp only [Finsupp.coe_add, Pi.add_apply]
        rw [show ((((chartModelBasis E).repr u₁) i + ((chartModelBasis E).repr u₂) i) *
              ((chartModelBasis E).repr v) j * ((chartModelBasis E).repr w) k *
              chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) =
            (((chartModelBasis E).repr u₁) i * ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) +
            (((chartModelBasis E).repr u₂) i * ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) from by ring]
        exact add_smul _ _ _
      map_smul' := fun c u => by
        classical
        have hrepr : (chartModelBasis E).repr (c • u) =
            c • (chartModelBasis E).repr u := map_smul _ _ _
        simp only [hrepr]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
        rw [show (c * ((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) =
              c * (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) from by ring]
        exact mul_smul _ _ _
    }
    map_add' := fun w₁ w₂ => by
      classical
      ext u
      have hrepr : (chartModelBasis E).repr (w₁ + w₂) =
          (chartModelBasis E).repr w₁ + (chartModelBasis E).repr w₂ := map_add _ _ _
      change (∑ i, ∑ j, ∑ k, ∑ l,
              (((chartModelBasis E).repr u) i *
                  ((chartModelBasis E).repr v) j *
                  ((chartModelBasis E).repr (w₁ + w₂)) k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x)) =
          (∑ i, ∑ j, ∑ k, ∑ l,
              (((chartModelBasis E).repr u) i *
                  ((chartModelBasis E).repr v) j *
                  ((chartModelBasis E).repr w₁) k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x)) +
          (∑ i, ∑ j, ∑ k, ∑ l,
              (((chartModelBasis E).repr u) i *
                  ((chartModelBasis E).repr v) j *
                  ((chartModelBasis E).repr w₂) k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x))
      simp only [hrepr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp only [Finsupp.coe_add, Pi.add_apply]
      rw [show (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
              (((chartModelBasis E).repr w₁) k + ((chartModelBasis E).repr w₂) k) *
              chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) =
            (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w₁) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) +
            (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w₂) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) from by ring]
      exact add_smul _ _ _
    map_smul' := fun c w => by
      classical
      ext u
      have hrepr : (chartModelBasis E).repr (c • w) =
          c • (chartModelBasis E).repr w := map_smul _ _ _
      change (∑ i, ∑ j, ∑ k, ∑ l,
              (((chartModelBasis E).repr u) i *
                  ((chartModelBasis E).repr v) j *
                  ((chartModelBasis E).repr (c • w)) k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x)) =
          c • (∑ i, ∑ j, ∑ k, ∑ l,
              (((chartModelBasis E).repr u) i *
                  ((chartModelBasis E).repr v) j *
                  ((chartModelBasis E).repr w) k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x))
      simp only [hrepr]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [show (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
              (c * ((chartModelBasis E).repr w) k) *
              chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) =
            c * (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) from by ring]
      exact mul_smul _ _ _
  }
  map_add' := fun v₁ v₂ => by
    classical
    ext w u
    have hrepr : (chartModelBasis E).repr (v₁ + v₂) =
        (chartModelBasis E).repr v₁ + (chartModelBasis E).repr v₂ := map_add _ _ _
    change (∑ i, ∑ j, ∑ k, ∑ l,
            (((chartModelBasis E).repr u) i *
                ((chartModelBasis E).repr (v₁ + v₂)) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
              ((chartModelBasis E) l : TangentSpace I x)) =
        (∑ i, ∑ j, ∑ k, ∑ l,
            (((chartModelBasis E).repr u) i *
                ((chartModelBasis E).repr v₁) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
              ((chartModelBasis E) l : TangentSpace I x)) +
        (∑ i, ∑ j, ∑ k, ∑ l,
            (((chartModelBasis E).repr u) i *
                ((chartModelBasis E).repr v₂) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
              ((chartModelBasis E) l : TangentSpace I x))
    simp only [hrepr]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [Finsupp.coe_add, Pi.add_apply]
    rw [show (((chartModelBasis E).repr u) i *
            (((chartModelBasis E).repr v₁) j + ((chartModelBasis E).repr v₂) j) *
            ((chartModelBasis E).repr w) k *
            chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) =
          (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v₁) j *
              ((chartModelBasis E).repr w) k *
              chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) +
          (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v₂) j *
              ((chartModelBasis E).repr w) k *
              chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) from by ring]
    exact add_smul _ _ _
  map_smul' := fun c v => by
    classical
    ext w u
    have hrepr : (chartModelBasis E).repr (c • v) =
        c • (chartModelBasis E).repr v := map_smul _ _ _
    change (∑ i, ∑ j, ∑ k, ∑ l,
            (((chartModelBasis E).repr u) i *
                ((chartModelBasis E).repr (c • v)) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
              ((chartModelBasis E) l : TangentSpace I x)) =
        c • (∑ i, ∑ j, ∑ k, ∑ l,
            (((chartModelBasis E).repr u) i *
                ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
              ((chartModelBasis E) l : TangentSpace I x))
    simp only [hrepr]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [show (((chartModelBasis E).repr u) i * (c * ((chartModelBasis E).repr v) j) *
            ((chartModelBasis E).repr w) k *
            chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) =
          c * (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
              ((chartModelBasis E).repr w) k *
              chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) from by ring]
    exact mul_smul _ _ _

/-- Pointwise expansion of `chartRiemannLin`. -/
@[simp] lemma chartRiemannLin_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) :
    chartRiemannLin (I := I) g x v w u =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr u i *
                  (chartModelBasis E).repr v j *
                  (chartModelBasis E).repr w k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x) := rfl

/-- The continuous trilinear chart-Riemann CLM at `x`, packaging
`chartRiemannLin` as a CLM via `LinearMap.toContinuousLinearMap` (using
finite-dimensionality of `T_x M = E`). -/
def chartRiemannCLM (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  let outer : TangentSpace I x →ₗ[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
    { toFun := fun v =>
        let mid : TangentSpace I x →ₗ[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
          { toFun := fun w =>
              LinearMap.toContinuousLinearMap (chartRiemannLin (I := I) g x v w)
            map_add' := fun w₁ w₂ => by
              ext u; change chartRiemannLin (I := I) g x v (w₁ + w₂) u = _
              rw [map_add]; rfl
            map_smul' := fun c w => by
              ext u; change chartRiemannLin (I := I) g x v (c • w) u = _
              rw [map_smul]; rfl }
        LinearMap.toContinuousLinearMap mid
      map_add' := fun v₁ v₂ => by
        ext w u
        change chartRiemannLin (I := I) g x (v₁ + v₂) w u = _
        rw [map_add]; rfl
      map_smul' := fun c v => by
        ext w u
        change chartRiemannLin (I := I) g x (c • v) w u = _
        rw [map_smul]; rfl }
  LinearMap.toContinuousLinearMap outer

/-- The defining identity: `chartRiemannCLM g x v w u = chartRiemannLin g x v w u`.
The two objects coincide pointwise; only the typing differs (CLM vs. LinearMap). -/
@[simp] theorem chartRiemannCLM_apply_eq_chartRiemannLin
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) :
    chartRiemannCLM (I := I) g x v w u = chartRiemannLin (I := I) g x v w u := rfl

/-- Pointwise expansion of `chartRiemannCLM` as the basis-coordinate quadruple sum. -/
theorem chartRiemannCLM_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) :
    chartRiemannCLM (I := I) g x v w u =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr u i *
                  (chartModelBasis E).repr v j *
                  (chartModelBasis E).repr w k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x) :=
  chartRiemannLin_apply (I := I) g x v w u

/-- Helper: `(chartModelBasis E).repr (b a) b' = if a = b' then 1 else 0`.

Mathlib's `Module.Basis.repr_self_apply` directly gives this form. -/
private lemma repr_basis_eq_kron (a b' : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).repr ((chartModelBasis E) a)) b' =
      (if a = b' then (1 : ℝ) else 0) :=
  Module.Basis.repr_self_apply _ _ _

/-- **Chart-basis evaluation of `chartRiemannCLM`.** Evaluating the chart-Riemann CLM
on the canonical basis triple `(e_j, e_k, e_i)` (with `e := chartModelBasis E`)
yields `∑ l, R^l{}_{ijk}(g, x)(ϕ_x x) • e_l`. The differentiation indices are the first
two arguments `(j, k)`; the "vector" index is the third argument `i`. -/
theorem chartRiemannCLM_basis_apply (g : SmoothRiemannianMetric I M) (x : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartRiemannCLM (I := I) g x
        ((chartModelBasis E) j) ((chartModelBasis E) k)
        ((chartModelBasis E) i) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g x i j k l (extChartAt I x x) •
          ((chartModelBasis E) l : TangentSpace I x) := by
  classical
  rw [chartRiemannCLM_apply]
  have hkron :
      ∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ∑ k' : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr ((chartModelBasis E) i)) i' *
                  ((chartModelBasis E).repr ((chartModelBasis E) j)) j' *
                  ((chartModelBasis E).repr ((chartModelBasis E) k)) k' *
                  chartRiemannTensor (I := I) g x i' j' k' l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x) =
      ∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ∑ k' : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((if i = i' then (1 : ℝ) else 0) *
                  (if j = j' then (1 : ℝ) else 0) *
                  (if k = k' then (1 : ℝ) else 0) *
                  chartRiemannTensor (I := I) g x i' j' k' l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x) := by
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    refine Finset.sum_congr rfl (fun k' _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [repr_basis_eq_kron, repr_basis_eq_kron, repr_basis_eq_kron]
  rw [hkron]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single k]
      · refine Finset.sum_congr rfl (fun l _ => ?_)
        simp
      · intro k' _ hk_ne
        refine Finset.sum_eq_zero (fun l _ => ?_)
        have hkk' : ¬ k = k' := fun h => hk_ne h.symm
        simp [hkk']
      · intro hk; exact absurd (Finset.mem_univ _) hk
    · intro j' _ hj_ne
      refine Finset.sum_eq_zero (fun k' _ => Finset.sum_eq_zero (fun l _ => ?_))
      have hjj' : ¬ j = j' := fun h => hj_ne h.symm
      simp [hjj']
    · intro hj; exact absurd (Finset.mem_univ _) hj
  · intro i' _ hi_ne
    refine Finset.sum_eq_zero (fun j' _ =>
      Finset.sum_eq_zero (fun k' _ => Finset.sum_eq_zero (fun l _ => ?_)))
    have hii' : ¬ i = i' := fun h => hi_ne h.symm
    simp [hii']
  · intro hi; exact absurd (Finset.mem_univ _) hi

/-- **Basis-coordinate identification.** The `l`-th basis coordinate of
`chartRiemannCLM g x (e_j) (e_k) (e_i)` is exactly the chart-Riemann tensor entry
`R^l{}_{ijk}(g, x)(ϕ_x x)`. -/
theorem chartRiemannCLM_repr_basis (g : SmoothRiemannianMetric I M) (x : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).repr
        (chartRiemannCLM (I := I) g x
          ((chartModelBasis E) j) ((chartModelBasis E) k)
          ((chartModelBasis E) i))) l =
      chartRiemannTensor (I := I) g x i j k l (extChartAt I x x) := by
  classical
  rw [chartRiemannCLM_basis_apply]
  rw [map_sum]
  rw [Finsupp.coe_finset_sum]
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single l]
  · rw [LinearEquiv.map_smul, Finsupp.smul_apply,
        Module.Basis.repr_self_apply, smul_eq_mul, if_pos rfl, mul_one]
  · intro l' _ hl_ne
    rw [LinearEquiv.map_smul, Finsupp.smul_apply,
        Module.Basis.repr_self_apply, smul_eq_mul]
    have h_neg : ¬ l' = l := hl_ne
    rw [if_neg h_neg, mul_zero]
  · intro hl; exact absurd (Finset.mem_univ _) hl

/-- **Antisymmetry of `chartRiemannCLM` in the first two CLM arguments.** Interchanging
the two differentiation directions `(v, w)` flips the sign of the chart-Riemann CLM
output. This follows from `chartRiemannTensor_antisymm_jk` together with the
basis-coordinate sum.

The proof shows `LHS + RHS = 0` (where RHS is the swapped form `chartRiemannCLM g x w v u`).
After swapping `(j, k)` summation labels on the second sum and applying
`chartRiemannTensor_antisymm_jk`, the two summands cancel pointwise. -/
theorem chartRiemannCLM_antisymm_jk (g : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) :
    chartRiemannCLM (I := I) g x v w u = - chartRiemannCLM (I := I) g x w v u := by
  classical
  rw [chartRiemannCLM_apply, chartRiemannCLM_apply]
  have key : ∀ i j k l : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr u i *
          (chartModelBasis E).repr w k *
          (chartModelBasis E).repr v j *
          chartRiemannTensor (I := I) g x i k j l (extChartAt I x x)) •
        ((chartModelBasis E) l : TangentSpace I x) =
      -(((chartModelBasis E).repr u i *
          (chartModelBasis E).repr v j *
          (chartModelBasis E).repr w k *
          chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
        ((chartModelBasis E) l : TangentSpace I x)) := by
    intro i j k l
    rw [show chartRiemannTensor (I := I) g x i k j l (extChartAt I x x) =
          - chartRiemannTensor (I := I) g x i j k l (extChartAt I x x) from
        chartRiemannTensor_antisymm_jk (I := I) g x i k j l _]
    rw [show ((chartModelBasis E).repr u i *
            (chartModelBasis E).repr w k *
            (chartModelBasis E).repr v j *
            -chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) =
          -((chartModelBasis E).repr u i *
              (chartModelBasis E).repr v j *
              (chartModelBasis E).repr w k *
              chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) from by ring]
    rw [neg_smul]
  have hRHS_to_neg_LHS :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr u i *
                  (chartModelBasis E).repr w j *
                  (chartModelBasis E).repr v k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x) =
      -(∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr u i *
                  (chartModelBasis E).repr v j *
                  (chartModelBasis E).repr w k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x)) := by
    have step1 : ∀ i : Fin (Module.finrank ℝ E),
        (∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr u i *
                  (chartModelBasis E).repr w j *
                  (chartModelBasis E).repr v k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x)) =
        -(∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr u i *
                  (chartModelBasis E).repr v j *
                  (chartModelBasis E).repr w k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x)) := by
      intro i
      rw [Finset.sum_comm
        (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
        (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
        (f := fun j k =>
          ∑ l : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr u i *
                (chartModelBasis E).repr w j *
                (chartModelBasis E).repr v k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
              ((chartModelBasis E) l : TangentSpace I x))]
      rw [show ∑ k : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr u i *
                      (chartModelBasis E).repr w j *
                      (chartModelBasis E).repr v k *
                      chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                    ((chartModelBasis E) l : TangentSpace I x) =
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr u i *
                      (chartModelBasis E).repr w k *
                      (chartModelBasis E).repr v j *
                      chartRiemannTensor (I := I) g x i k j l (extChartAt I x x)) •
                    ((chartModelBasis E) l : TangentSpace I x) from by
        rw [Finset.sum_comm]]
      rw [show ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr u i *
                      (chartModelBasis E).repr w k *
                      (chartModelBasis E).repr v j *
                      chartRiemannTensor (I := I) g x i k j l (extChartAt I x x)) •
                    ((chartModelBasis E) l : TangentSpace I x) =
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  -(((chartModelBasis E).repr u i *
                      (chartModelBasis E).repr v j *
                      (chartModelBasis E).repr w k *
                      chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                    ((chartModelBasis E) l : TangentSpace I x)) from by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun l _ => ?_)
        exact key i j k l]
      simp only [Finset.sum_neg_distrib]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr u i *
                      (chartModelBasis E).repr w j *
                      (chartModelBasis E).repr v k *
                      chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                    ((chartModelBasis E) l : TangentSpace I x)) =
          ∑ i : Fin (Module.finrank ℝ E),
            -(∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr u i *
                      (chartModelBasis E).repr v j *
                      (chartModelBasis E).repr w k *
                      chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                    ((chartModelBasis E) l : TangentSpace I x)) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact step1 i]
    simp only [Finset.sum_neg_distrib]
  rw [hRHS_to_neg_LHS]
  abel

/-- Antisymmetry of the chart-Riemann CLM on the canonical model-basis triple. -/
theorem chartRiemannCLM_basis_antisymm_jk (g : SmoothRiemannianMetric I M) (x : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartRiemannCLM (I := I) g x
        ((chartModelBasis E) j) ((chartModelBasis E) k)
        ((chartModelBasis E) i) =
      - chartRiemannCLM (I := I) g x
          ((chartModelBasis E) k) ((chartModelBasis E) j)
          ((chartModelBasis E) i) :=
  chartRiemannCLM_antisymm_jk (I := I) g x
    ((chartModelBasis E) j) ((chartModelBasis E) k) ((chartModelBasis E) i)

/-- The chart-Riemann CLM vanishes on the diagonal (when `v = w`). -/
theorem chartRiemannCLM_diag (g : SmoothRiemannianMetric I M) (x : M)
    (v u : TangentSpace I x) :
    chartRiemannCLM (I := I) g x v v u = 0 := by
  have h : chartRiemannCLM (I := I) g x v v u = -chartRiemannCLM (I := I) g x v v u :=
    chartRiemannCLM_antisymm_jk (I := I) g x v v u
  set a := chartRiemannCLM (I := I) g x v v u with ha_def
  have h_add : a + a = 0 := by
    nth_rewrite 1 [h]
    rw [neg_add_cancel]
  have h_two_smul : (2 : ℝ) • a = a + a := by
    rw [show (2 : ℝ) = 1 + 1 from by norm_num, add_smul, one_smul]
  have h_smul_zero : (2 : ℝ) • a = 0 := h_two_smul.trans h_add
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp h_smul_zero).resolve_left htwo

/-- **Section-level reduction of `riemannOp` on smooth basis extensions.** For any
choice of smooth global tangent sections `X i` with `X i x = (chartModelBasis E) i`,
the value of the abstract Riemann operator `riemannOp (LeviCivita g) x (e_j) (e_k) (e_i)`
equals the section-level formula `riemannSec (LeviCivita g) (X j) (X k) (X i) x`.

This is the entry point for the deep chart-Christoffel identification: once we have
basis-extending smooth sections, the right-hand side `riemannSec` can be expanded via
two iterations of `LeviCivita_chart_apply` to recover the chart-Riemann tensor entry
`∑ l R^l{}_{ijk}(g, x)(ϕ_x x) • e_l`. -/
theorem riemannOp_chartBasis_via_riemannSec (g : SmoothRiemannianMetric I M) (x : M)
    {X : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hX : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (X i)))
    (hXx : ∀ i, X i x = (chartModelBasis E) i)
    (i j k : Fin (Module.finrank ℝ E)) :
    riemannOp (cov := LeviCivita (I := I) g) x
        ((chartModelBasis E) j) ((chartModelBasis E) k)
        ((chartModelBasis E) i) =
      riemannSec (LeviCivita (I := I) g) (X j) (X k) (X i) x := by
  rw [show ((chartModelBasis E) j : TangentSpace I x) = X j x from (hXx j).symm,
      show ((chartModelBasis E) k : TangentSpace I x) = X k x from (hXx k).symm,
      show ((chartModelBasis E) i : TangentSpace I x) = X i x from (hXx i).symm]
  exact riemannOp_apply_smooth (cov := LeviCivita (I := I) g) (hX j) (hX k) (hX i)

/-- **Section-level antisymmetry transfer.** The antisymmetry of `riemannSec` in its
first two arguments (already established as `riemannSec_swap`) restated for the
basis-vector form. -/
theorem riemannSec_chartBasis_swap (g : SmoothRiemannianMetric I M) (x : M)
    (X : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (i j k : Fin (Module.finrank ℝ E)) :
    riemannSec (LeviCivita (I := I) g) (X j) (X k) (X i) x =
      - riemannSec (LeviCivita (I := I) g) (X k) (X j) (X i) x :=
  riemannSec_swap (cov := LeviCivita (I := I) g) (X j) (X k) (X i) x

/-- **Section-level diagonal vanishing.** For smooth sections `X j`, the section-level
Riemann formula vanishes on the diagonal `(X j, X j)`. -/
theorem riemannSec_chartBasis_diag (g : SmoothRiemannianMetric I M) (x : M)
    (X : Π b : M, TangentSpace I b) (Z : Π b : M, TangentSpace I b) :
    riemannSec (LeviCivita (I := I) g) X X Z x = 0 :=
  riemannSec_self_eq_zero (cov := LeviCivita (I := I) g) X Z x

/-- Antisymmetry of `riemannOp (LeviCivita g) x` on the canonical model-basis triple. -/
theorem riemannOp_basis_antisymm_jk (g : SmoothRiemannianMetric I M) (x : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    riemannOp (cov := LeviCivita (I := I) g) x
        ((chartModelBasis E) j) ((chartModelBasis E) k)
        ((chartModelBasis E) i) =
      - riemannOp (cov := LeviCivita (I := I) g) x
          ((chartModelBasis E) k) ((chartModelBasis E) j)
          ((chartModelBasis E) i) :=
  riemannOp_swap (cov := LeviCivita (I := I) g) x
    ((chartModelBasis E) j) ((chartModelBasis E) k) ((chartModelBasis E) i)

end Connection
end Integral
end DifferentialGeometry
