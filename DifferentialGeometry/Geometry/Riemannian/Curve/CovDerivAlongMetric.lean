import DifferentialGeometry.Geometry.Riemannian.Curve.CovDerivAlong
import DifferentialGeometry.Integral.Connection.ChartMetric

set_option linter.unusedSectionVars false

/-!
# Metric compatibility for the covariant derivative along a curve

For a smooth Riemannian metric `g` on a smooth (boundaryless) manifold `M`, a
`C¹` curve `γ : ℝ → M`, and `C¹` vector fields `V, W` along `γ`, the function
`s ↦ g.inner (γ s) (V s) (W s)` is real-valued and differentiable at every
time `t`, with

```
deriv (fun s => g.inner (γ s) (V s) (W s)) t =
  g.inner (γ t) (covDerivAlong g γ V _ _ t) (W t) +
    g.inner (γ t) (V t) (covDerivAlong g γ W _ _ t).
```

This is the metric-compatibility property of the chart-Christoffel covariant
derivative `covDerivAlong`. The proof is purely chart-local: in the canonical
chart at `γ t`, we identify the inner product as a sum over chart Gram entries
times chart-fibre coordinates of `V, W`, then differentiate using
`partialDeriv_chartGramOnE_eq_chartChristoffel_sum`.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Curve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic

/-! ## Eventual containment of `γ s` in the chart base / source -/

/-- For a continuous curve `γ`, the curve enters the trivialization base set
at `γ t` for `s` near `t`. -/
lemma eventually_γ_mem_trivBaseSet (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (t : ℝ) :
    ∀ᶠ s in nhds t, γ s ∈
      (trivializationAt E (TangentSpace I) (γ t)).baseSet := by
  have hcont : Continuous γ := hγ.continuous
  have hop : IsOpen (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    (trivializationAt E (TangentSpace I) (γ t)).open_baseSet
  have hmem : γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H (γ t)
  exact (hcont.continuousAt).preimage_mem_nhds (hop.mem_nhds hmem)

/-- The curve enters the extended chart source at `γ t` for `s` near `t`. -/
lemma eventually_γ_mem_extChartAt_source (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (t : ℝ) :
    ∀ᶠ s in nhds t, γ s ∈ (extChartAt I (γ t)).source := by
  have hcont : Continuous γ := hγ.continuous
  have hop : IsOpen (extChartAt I (γ t)).source := isOpen_extChartAt_source (I := I) (γ t)
  have hmem : γ t ∈ (extChartAt I (γ t)).source := mem_extChartAt_source (I := I) (γ t)
  exact (hcont.continuousAt).preimage_mem_nhds (hop.mem_nhds hmem)

/-! ## Chart-coordinate scalar projections of a chart-fibre vector field
along a curve -/

/-- The `i`-th chart coordinate of the chart-fibre vector along `γ` at base
time `t`. -/
def chartFiberCoordAlong (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (t : ℝ) (i : Fin (Module.finrank ℝ E)) : ℝ → ℝ :=
  fun s => chartCoord (E := E) i (chartFiberAlong (I := I) γ V t s)

@[simp] lemma chartFiberCoordAlong_def (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (i : Fin (Module.finrank ℝ E)) (s : ℝ) :
    chartFiberCoordAlong (I := I) γ V t i s =
      chartCoord (E := E) i (chartFiberAlong (I := I) γ V t s) := rfl

/-- The `i`-th chart-coordinate is `C¹`-differentiable in `s` at `s = t`,
inherited from the chart-fibre representation. The differentiable structure
arises from composition with the continuous linear basis-coordinate map. -/
lemma chartFiberCoordAlong_differentiableAt (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t))
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (t : ℝ) (i : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (chartFiberCoordAlong (I := I) γ V t i) t := by
  classical
  have hfiber : DifferentiableAt ℝ (chartFiberAlong (I := I) γ V t) t :=
    chartFiberAlong_differentiableAt (I := I) γ V hV t
  -- `chartCoord i` factors through `(chartModelBasis E).coord i`, a CLM via `toContinuousLinearMap`.
  set L : E →L[ℝ] ℝ := ((chartModelBasis E).coord i).toContinuousLinearMap with hL_def
  have hCLM : DifferentiableAt ℝ L (chartFiberAlong (I := I) γ V t t) :=
    L.differentiableAt
  -- Compose: `L ∘ chartFiberAlong γ V t` is differentiable at `t`.
  have hcomp : DifferentiableAt ℝ (fun s => L (chartFiberAlong (I := I) γ V t s)) t :=
    hCLM.comp t hfiber
  -- The composition equals `chartFiberCoordAlong γ V t i` pointwise (definitional).
  change DifferentiableAt ℝ (fun s => (chartModelBasis E).repr
      (chartFiberAlong (I := I) γ V t s) i) t
  -- We will use Funext to identify the goal with `hcomp`.
  have hfun_eq : (fun s => L (chartFiberAlong (I := I) γ V t s)) =
      (fun s => (chartModelBasis E).repr (chartFiberAlong (I := I) γ V t s) i) := by
    funext s
    change ((chartModelBasis E).coord i) (chartFiberAlong (I := I) γ V t s) =
      (chartModelBasis E).repr (chartFiberAlong (I := I) γ V t s) i
    rfl
  rw [hfun_eq] at hcomp
  exact hcomp

/-- At base time `s = t`, the chart-coordinate-along equals the chart coordinate
of `V t`. -/
@[simp] lemma chartFiberCoordAlong_self (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    chartFiberCoordAlong (I := I) γ V t i t = chartCoord (E := E) i (V t) := by
  unfold chartFiberCoordAlong
  rw [chartFiberAlong_self]

/-! ## Chart-Gram-matrix entry along the curve -/

/-- The `(i,j)`-entry of the chart Gram matrix, evaluated along the curve `γ` at
base time `t`: `s ↦ G_ij(α, φ(γ s))` for `α := γ t`, `φ := extChartAt I α`. -/
def chartGramAlong (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (t : ℝ) (i j : Fin (Module.finrank ℝ E)) : ℝ → ℝ :=
  fun s => chartGramOnE (I := I) g (γ t) i j (extChartAt I (γ t) (γ s))

@[simp] lemma chartGramAlong_def (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (t : ℝ) (i j : Fin (Module.finrank ℝ E)) (s : ℝ) :
    chartGramAlong (I := I) g γ t i j s =
      chartGramOnE (I := I) g (γ t) i j (extChartAt I (γ t) (γ s)) := rfl

/-- Differentiability of `chartGramAlong` at `t`, via the chain rule applied to
the smooth chart-Gram pull-back and the differentiable chart-base curve. -/
lemma chartGramAlong_differentiableAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (t : ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (chartGramAlong (I := I) g γ t i j) t := by
  classical
  -- (1) The chart-base curve `chartCurveAt γ t` is differentiable at `t`.
  have hchart_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
      (chartCurveAt (I := I) γ t) t := by
    have hγ_at : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t := hγ.contMDiffAt
    have hchart : ContMDiffAt I 𝓘(ℝ, E) 1 (extChartAt I (γ t)) (γ t) := by
      have h : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I (γ t)) (γ t) :=
        contMDiffAt_extChartAt (I := I) (x := γ t) (n := (∞ : WithTop ℕ∞))
      exact h.of_le (by norm_num)
    exact hchart.comp t hγ_at
  have hchart_diff : DifferentiableAt ℝ (chartCurveAt (I := I) γ t) t :=
    hchart_at.contDiffAt.differentiableAt_one
  -- (2) `chartGramOnE g (γt) i j` is differentiable at `φ(γt)` since
  -- `φ(γt) ∈ interior (extChartAt (γt)).target` (under `[I.Boundaryless]`).
  have hsrc : γ t ∈ (extChartAt I (γ t)).source :=
    mem_extChartAt_source (I := I) (γ t)
  have htgt : extChartAt I (γ t) (γ t) ∈ (extChartAt I (γ t)).target :=
    (extChartAt I (γ t)).map_source hsrc
  have hint : extChartAt I (γ t) (γ t) ∈ interior (extChartAt I (γ t)).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) (γ t) htgt
  have hG_cdo : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g (γ t) i j)
      (interior (extChartAt I (γ t)).target) :=
    (chartGramOnE_contDiffOn (I := I) g (γ t) i j).mono interior_subset
  have hG_at : DifferentiableAt ℝ (chartGramOnE (I := I) g (γ t) i j)
      (extChartAt I (γ t) (γ t)) := by
    have hG_cda : ContDiffAt ℝ ∞ (chartGramOnE (I := I) g (γ t) i j)
        (extChartAt I (γ t) (γ t)) :=
      hG_cdo.contDiffAt (isOpen_interior.mem_nhds hint)
    exact hG_cda.differentiableAt (by simp)
  -- (3) Chain rule: `(G_ij ∘ chartCurveAt γ t)` differentiable at `t`.
  have hcomp := hG_at.comp t hchart_diff
  -- The composition equals `chartGramAlong g γ t i j`.
  have hfun : (chartGramOnE (I := I) g (γ t) i j) ∘
        (chartCurveAt (I := I) γ t) = chartGramAlong (I := I) g γ t i j := by
    funext s; rfl
  rw [hfun] at hcomp
  exact hcomp

/-- The chain-rule computation of `deriv (chartGramAlong) t` as a sum of
chart-coordinate-weighted partial derivatives of `chartGramOnE`. Uses the
basis expansion of `deriv(chartCurveAt γ t) t`. -/
lemma deriv_chartGramAlong_eq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (t : ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deriv (chartGramAlong (I := I) g γ t i j) t =
      ∑ k : Fin (Module.finrank ℝ E),
        chartCoord (E := E) k (deriv (chartCurveAt (I := I) γ t) t) *
          partialDeriv (E := E) k
            (chartGramOnE (I := I) g (γ t) i j)
            (extChartAt I (γ t) (γ t)) := by
  classical
  -- (1) The chart-base curve `chartCurveAt γ t` is differentiable at `t`.
  have hchart_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
      (chartCurveAt (I := I) γ t) t := by
    have hγ_at : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t := hγ.contMDiffAt
    have hchart : ContMDiffAt I 𝓘(ℝ, E) 1 (extChartAt I (γ t)) (γ t) := by
      have h : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I (γ t)) (γ t) :=
        contMDiffAt_extChartAt (I := I) (x := γ t) (n := (∞ : WithTop ℕ∞))
      exact h.of_le (by norm_num)
    exact hchart.comp t hγ_at
  have hchart_da : HasDerivAt (chartCurveAt (I := I) γ t)
      (deriv (chartCurveAt (I := I) γ t) t) t :=
    hchart_at.contDiffAt.differentiableAt_one.hasDerivAt
  -- (2) Differentiability of `chartGramOnE g (γt) i j` at `φ(γt)`.
  have hsrc : γ t ∈ (extChartAt I (γ t)).source :=
    mem_extChartAt_source (I := I) (γ t)
  have htgt : extChartAt I (γ t) (γ t) ∈ (extChartAt I (γ t)).target :=
    (extChartAt I (γ t)).map_source hsrc
  have hint : extChartAt I (γ t) (γ t) ∈ interior (extChartAt I (γ t)).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) (γ t) htgt
  have hG_cdo : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g (γ t) i j)
      (interior (extChartAt I (γ t)).target) :=
    (chartGramOnE_contDiffOn (I := I) g (γ t) i j).mono interior_subset
  have hG_cda : ContDiffAt ℝ ∞ (chartGramOnE (I := I) g (γ t) i j)
      (extChartAt I (γ t) (γ t)) :=
    hG_cdo.contDiffAt (isOpen_interior.mem_nhds hint)
  have hG_fd : HasFDerivAt (chartGramOnE (I := I) g (γ t) i j)
      (fderiv ℝ (chartGramOnE (I := I) g (γ t) i j)
        (extChartAt I (γ t) (γ t))) (extChartAt I (γ t) (γ t)) :=
    (hG_cda.differentiableAt (by simp)).hasFDerivAt
  -- (3) Chain rule: HasDerivAt for `chartGramAlong g γ t i j` at `t`.
  have hcomp_fd : HasDerivAt
      (chartGramOnE (I := I) g (γ t) i j ∘ chartCurveAt (I := I) γ t)
      ((fderiv ℝ (chartGramOnE (I := I) g (γ t) i j)
          (extChartAt I (γ t) (γ t)))
        (deriv (chartCurveAt (I := I) γ t) t)) t :=
    hG_fd.comp_hasDerivAt t hchart_da
  -- Rewrite the composition.
  have hfun : (chartGramOnE (I := I) g (γ t) i j) ∘
        (chartCurveAt (I := I) γ t) = chartGramAlong (I := I) g γ t i j := by
    funext s; rfl
  rw [hfun] at hcomp_fd
  -- (4) Convert the derivative.
  have hderiv_eq :
      deriv (chartGramAlong (I := I) g γ t i j) t =
      (fderiv ℝ (chartGramOnE (I := I) g (γ t) i j)
        (extChartAt I (γ t) (γ t)))
          (deriv (chartCurveAt (I := I) γ t) t) := hcomp_fd.deriv
  rw [hderiv_eq]
  -- (5) Expand the fderiv-application using the basis of `E`.
  -- `(fderiv u y) v = ∑ k, chartCoord k v * (fderiv u y) (e_k) = ∑ k, chartCoord k v * partialDeriv k u y`.
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E with hb
  set v : E := deriv (chartCurveAt (I := I) γ t) t with hv_def
  have hv_decomp : v = ∑ k, b.repr v k • b k := (Module.Basis.sum_repr b v).symm
  -- Apply the linear map to the sum.
  set L : E →L[ℝ] ℝ := fderiv ℝ (chartGramOnE (I := I) g (γ t) i j)
    (extChartAt I (γ t) (γ t)) with hL_def
  have hLv : L v = L (∑ k, b.repr v k • b k) := by rw [← hv_decomp]
  rw [hLv]
  -- Distribute via map_sum, map_smul.
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul, smul_eq_mul]
  -- `L (b k) = (fderiv chartGramOnE _ _) (chartModelBasis E k) = partialDeriv k _ _`.
  rfl

/-! ## Eventual chart-sum representation of `g.inner` along the curve -/

/-- Locally near `t`, the inner product `g.inner (γ s) (V s) (W s)` decomposes as
a sum of chart-Gram-entry-weighted chart-fibre-coordinate products. -/
lemma g_inner_eq_chart_sum_along_eventually
    (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (V W : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    (fun s => g.inner (γ s) (V s) (W s)) =ᶠ[nhds t]
      (fun s => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartFiberCoordAlong (I := I) γ V t i s *
            chartFiberCoordAlong (I := I) γ W t j s *
            chartGramAlong (I := I) g γ t i j s) := by
  filter_upwards [eventually_γ_mem_trivBaseSet (I := I) γ hγ t,
    eventually_γ_mem_extChartAt_source (I := I) γ hγ t] with s hs_triv hs_ext
  -- Apply `g_inner_eq_chart_sum` at chart α := γ t, x := γ s.
  have hsum := g_inner_eq_chart_sum (I := I) g (γ t) (x := γ s) hs_triv hs_ext
    (V s) (W s)
  rw [hsum]
  -- Convert the trivialization-linear-map expressions to `chartFiberCoord`.
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  -- Rewrite the two `(chartModelBasis E).repr (continuousLinearMapAt ...)`.
  have hVi :
      ((chartModelBasis E).repr
          ((trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt ℝ (γ s) (V s))) i =
      chartFiberCoordAlong (I := I) γ V t i s := by
    -- chartFiberAlong γ V t s = chartFiberCoord (γt) ⟨γs, Vs⟩ = clmAt (γs) (Vs).
    have hch := chartFiberCoord_eq_clmAt_of_mem (I := I) (γ t) (V s)
      (by rw [TangentBundle.trivializationAt_baseSet] at hs_triv; exact hs_triv)
    rw [← hch]
    rfl
  have hWj :
      ((chartModelBasis E).repr
          ((trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt ℝ (γ s) (W s))) j =
      chartFiberCoordAlong (I := I) γ W t j s := by
    have hch := chartFiberCoord_eq_clmAt_of_mem (I := I) (γ t) (W s)
      (by rw [TangentBundle.trivializationAt_baseSet] at hs_triv; exact hs_triv)
    rw [← hch]
    rfl
  rw [hVi, hWj]
  rfl

/-! ## Derivative of the sum at `s = t` -/

/-- Local helper: the derivative of a product of three differentiable real-valued
functions at a point, via two applications of the product rule. -/
private lemma deriv_triple_product
    (f g h : ℝ → ℝ) {t : ℝ}
    (hf : DifferentiableAt ℝ f t)
    (hg : DifferentiableAt ℝ g t)
    (hh : DifferentiableAt ℝ h t) :
    deriv (fun s => f s * g s * h s) t =
      deriv f t * g t * h t + f t * deriv g t * h t + f t * g t * deriv h t := by
  classical
  have hfg : DifferentiableAt ℝ (fun s => f s * g s) t := hf.mul hg
  -- (1) `deriv (s ↦ (f * g) s * h s) t = deriv (f * g) t · h t + (f * g) t · deriv h t`.
  have hstep1 : deriv (fun s => f s * g s * h s) t =
      deriv (fun s => f s * g s) t * h t + (f t * g t) * deriv h t :=
    deriv_fun_mul hfg hh
  rw [hstep1]
  rw [deriv_fun_mul hf hg]
  ring

/-- The pointwise derivative of the chart-sum expression at `s = t`. We compute
this by differentiating each `v^i * w^j * G_ij` triple-product and summing,
using `deriv_sum` and the product rule. -/
lemma deriv_chart_sum_at [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} (V W : ∀ t, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M)))
    (t : ℝ) :
    deriv (fun s => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartFiberCoordAlong (I := I) γ V t i s *
            chartFiberCoordAlong (I := I) γ W t j s *
            chartGramAlong (I := I) g γ t i j s) t =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (deriv (chartFiberCoordAlong (I := I) γ V t i) t *
              chartFiberCoordAlong (I := I) γ W t j t *
              chartGramAlong (I := I) g γ t i j t +
            chartFiberCoordAlong (I := I) γ V t i t *
              deriv (chartFiberCoordAlong (I := I) γ W t j) t *
              chartGramAlong (I := I) g γ t i j t +
            chartFiberCoordAlong (I := I) γ V t i t *
              chartFiberCoordAlong (I := I) γ W t j t *
              deriv (chartGramAlong (I := I) g γ t i j) t) := by
  classical
  -- Differentiability of each triple-product factor.
  have hvi : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartFiberCoordAlong (I := I) γ V t i) t := fun i =>
    chartFiberCoordAlong_differentiableAt (I := I) γ V hV t i
  have hwj : ∀ j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartFiberCoordAlong (I := I) γ W t j) t := fun j =>
    chartFiberCoordAlong_differentiableAt (I := I) γ W hW t j
  have hGij : ∀ i j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartGramAlong (I := I) g γ t i j) t := fun i j =>
    chartGramAlong_differentiableAt (I := I) g γ hγ t i j
  -- Differentiability of each summand `(λ s, v^i w^j G_ij s)`.
  have hijsum : ∀ i j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun s => chartFiberCoordAlong (I := I) γ V t i s *
          chartFiberCoordAlong (I := I) γ W t j s *
          chartGramAlong (I := I) g γ t i j s) t := fun i j =>
    ((hvi i).mul (hwj j)).mul (hGij i j)
  -- Differentiability of the inner sum over j.
  have hjsum : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun s => ∑ j : Fin (Module.finrank ℝ E),
          chartFiberCoordAlong (I := I) γ V t i s *
            chartFiberCoordAlong (I := I) γ W t j s *
            chartGramAlong (I := I) g γ t i j s) t := fun i =>
    DifferentiableAt.fun_sum (fun j _ => hijsum i j)
  -- Differentiate the outer sum.
  rw [deriv_fun_sum (fun i _ => hjsum i)]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [deriv_fun_sum (fun j _ => hijsum i j)]
  refine Finset.sum_congr rfl ?_
  intro j _
  -- Apply the triple-product derivative formula.
  exact deriv_triple_product
    (chartFiberCoordAlong (I := I) γ V t i)
    (chartFiberCoordAlong (I := I) γ W t j)
    (chartGramAlong (I := I) g γ t i j) (hvi i) (hwj j) (hGij i j)

/-! ## Algebraic reassembly via the chart-metric identity -/

/-- The sum-of-three-terms expression, with `Ġij` expanded via the chain rule
identity, equals the metric-compatibility right-hand side. This is the pure
algebraic step. -/
lemma chart_sum_deriv_eq_inner_covDeriv [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} (V W : ∀ t, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M)))
    (t : ℝ) :
    (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (deriv (chartFiberCoordAlong (I := I) γ V t i) t *
              chartFiberCoordAlong (I := I) γ W t j t *
              chartGramAlong (I := I) g γ t i j t +
            chartFiberCoordAlong (I := I) γ V t i t *
              deriv (chartFiberCoordAlong (I := I) γ W t j) t *
              chartGramAlong (I := I) g γ t i j t +
            chartFiberCoordAlong (I := I) γ V t i t *
              chartFiberCoordAlong (I := I) γ W t j t *
              deriv (chartGramAlong (I := I) g γ t i j) t)) =
      g.inner (γ t) (covDerivAlong (I := I) g γ V hγ hV t) (W t) +
        g.inner (γ t) (V t) (covDerivAlong (I := I) g γ W hγ hW t) := by
  classical
  -- Notation: shorten the variables.
  set n := Module.finrank ℝ E
  set α : M := γ t with hα_def
  set y : E := extChartAt I α α with hy_def
  have hsrc : α ∈ (extChartAt I α).source := mem_extChartAt_source (I := I) α
  have htgt : y ∈ (extChartAt I α).target := (extChartAt I α).map_source hsrc
  have hint : y ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α htgt
  -- chartCurveAt α t = φ(α) = y at s = t.
  have hcurve_t : chartCurveAt (I := I) γ t t = y := rfl
  -- Step 1: rewrite `deriv (chartGramAlong g γ t i j) t` via the chain-rule lemma.
  have hG_deriv : ∀ i j : Fin n,
      deriv (chartGramAlong (I := I) g γ t i j) t =
        ∑ k : Fin n,
          chartCoord (E := E) k (deriv (chartCurveAt (I := I) γ t) t) *
            partialDeriv (E := E) k
              (chartGramOnE (I := I) g α i j) y := by
    intro i j
    exact deriv_chartGramAlong_eq (I := I) g γ hγ t i j
  -- Step 2: rewrite `partialDeriv k (chartGramOnE g α i j) y` via the chart-metric identity.
  have hpd : ∀ i j k : Fin n,
      partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y =
        (∑ l : Fin n,
            chartChristoffel (I := I) g α k i l y *
              chartGramOnE (I := I) g α l j y) +
        (∑ l : Fin n,
            chartChristoffel (I := I) g α k j l y *
              chartGramOnE (I := I) g α l i y) :=
    fun i j k => partialDeriv_chartGramOnE_eq_chartChristoffel_sum (I := I) g α i j k hint
  -- Step 3: shorthand names for the chart-coord fields at `s = t`.
  set vt : Fin n → ℝ := fun i => chartFiberCoordAlong (I := I) γ V t i t with hvt_def
  set wt : Fin n → ℝ := fun j => chartFiberCoordAlong (I := I) γ W t j t with hwt_def
  set dv : Fin n → ℝ := fun i => deriv (chartFiberCoordAlong (I := I) γ V t i) t
    with hdv_def
  set dw : Fin n → ℝ := fun j => deriv (chartFiberCoordAlong (I := I) γ W t j) t
    with hdw_def
  set udot : Fin n → ℝ := fun k => chartCoord (E := E) k
    (deriv (chartCurveAt (I := I) γ t) t) with hudot_def
  set Gij : Fin n → Fin n → ℝ := fun i j => chartGramOnE (I := I) g α i j y with hGij_def
  set Γkil : Fin n → Fin n → Fin n → ℝ := fun k i l =>
    chartChristoffel (I := I) g α k i l y with hΓ_def
  -- `chartGramAlong g γ t i j t = G_ij`.
  have hGa_t : ∀ i j : Fin n, chartGramAlong (I := I) g γ t i j t = Gij i j := by
    intro i j; rfl
  -- Rewrite the LHS using the helper expansion.
  have hLHS_step1 :
      (∑ i : Fin n, ∑ j : Fin n,
          (dv i * wt j * Gij i j +
            vt i * dw j * Gij i j +
            vt i * wt j *
              (∑ k : Fin n, udot k *
                ((∑ l : Fin n, Γkil k i l * Gij l j) +
                 (∑ l : Fin n, Γkil k j l * Gij l i))))) =
      (∑ i : Fin n, ∑ j : Fin n,
          (deriv (chartFiberCoordAlong (I := I) γ V t i) t *
              chartFiberCoordAlong (I := I) γ W t j t *
              chartGramAlong (I := I) g γ t i j t +
            chartFiberCoordAlong (I := I) γ V t i t *
              deriv (chartFiberCoordAlong (I := I) γ W t j) t *
              chartGramAlong (I := I) g γ t i j t +
            chartFiberCoordAlong (I := I) γ V t i t *
              chartFiberCoordAlong (I := I) γ W t j t *
              deriv (chartGramAlong (I := I) g γ t i j) t)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    change dv i * wt j * Gij i j + vt i * dw j * Gij i j +
        vt i * wt j *
          (∑ k : Fin n, udot k *
            ((∑ l : Fin n, Γkil k i l * Gij l j) +
             (∑ l : Fin n, Γkil k j l * Gij l i))) =
      deriv (chartFiberCoordAlong (I := I) γ V t i) t *
          chartFiberCoordAlong (I := I) γ W t j t *
          chartGramAlong (I := I) g γ t i j t +
      chartFiberCoordAlong (I := I) γ V t i t *
          deriv (chartFiberCoordAlong (I := I) γ W t j) t *
          chartGramAlong (I := I) g γ t i j t +
      chartFiberCoordAlong (I := I) γ V t i t *
          chartFiberCoordAlong (I := I) γ W t j t *
          deriv (chartGramAlong (I := I) g γ t i j) t
    rw [hG_deriv i j, hGa_t i j]
    -- Substitute the partial-deriv identity into the sum.
    have hsum_eq :
        (∑ k : Fin n, udot k *
            partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y) =
        (∑ k : Fin n, udot k *
          ((∑ l : Fin n, Γkil k i l * Gij l j) +
           (∑ l : Fin n, Γkil k j l * Gij l i))) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [hpd i j k]
    rw [hsum_eq]
  rw [← hLHS_step1]
  -- Now expand the inner `vt i * wt j * (∑ k, ...)` term and split.
  -- Two large pieces:
  --   A = ∑ i j, dv i * wt j * Gij i j + vt i * wt j * (∑ k, udot k * ∑ l, Γ^l_{ki} G_lj)
  --   B = ∑ i j, vt i * dw j * Gij i j + vt i * wt j * (∑ k, udot k * ∑ l, Γ^l_{kj} G_li)
  -- and the original LHS = A + B.
  have hsplit :
      (∑ i : Fin n, ∑ j : Fin n,
          (dv i * wt j * Gij i j +
            vt i * dw j * Gij i j +
            vt i * wt j *
              (∑ k : Fin n, udot k *
                ((∑ l : Fin n, Γkil k i l * Gij l j) +
                 (∑ l : Fin n, Γkil k j l * Gij l i))))) =
      (∑ i : Fin n, ∑ j : Fin n,
          (dv i * wt j * Gij i j +
            vt i * wt j * (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k i l * Gij l j))) +
      (∑ i : Fin n, ∑ j : Fin n,
          (vt i * dw j * Gij i j +
            vt i * wt j * (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k j l * Gij l i))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    have hmul_distrib : vt i * wt j *
            ((∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k i l * Gij l j) +
             (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k j l * Gij l i)) =
        vt i * wt j * (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k i l * Gij l j) +
        vt i * wt j * (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k j l * Gij l i) := by
      rw [mul_add]
    have hsum_distrib :
        (∑ k : Fin n, udot k *
          ((∑ l : Fin n, Γkil k i l * Gij l j) +
           (∑ l : Fin n, Γkil k j l * Gij l i))) =
        (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k i l * Gij l j) +
        (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k j l * Gij l i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [mul_add]
    rw [hsum_distrib, hmul_distrib]
    ring
  rw [hsplit]
  -- Compute the chart-fibre of `covDerivAlong g γ V t` in `chartCoord l`-form.
  -- `chartCoord l (covDerivAlong g γ V t) = chartCoord l (deriv (chartFiberAlong γ V t) t) +
  --   chartCoord l (chartChristoffelContraction g α (deriv (chartCurveAt γ t) t) (V t) y)`
  -- and unfolding `chartChristoffelContraction`'s chart-l coord gives
  -- `∑ k i, Γ_{k i}^l y * udot k * (chartCoord i (V t))`.
  -- Note: `chartCoord i (V t) = vt i` via `chartFiberCoordAlong_self`.
  -- Note: `chartCoord l (deriv (chartFiberAlong γ V t) t) = dv l` since
  -- chartCoord and deriv-of-CLM-composition commute up to differentiation linearity.
  -- These reassembly identities are then plugged into the chart-sum form of
  -- `g.inner α (∇V) W` via `g_inner_eq_chart_sum`.
  -- For clarity we develop the chart-coord identification first.
  -- Step A: chartCoord l (deriv(chartFiberAlong γ V t) t) = dv l.
  have hdv_chartCoord : ∀ l : Fin n,
      chartCoord (E := E) l (deriv (chartFiberAlong (I := I) γ V t) t) = dv l := by
    intro l
    -- `chartCoord l = (chartModelBasis E).coord l`, a CLM via `toContinuousLinearMap`.
    -- Apply `HasFDerivAt.comp_hasDerivAt`: `L (deriv f t) = deriv (L ∘ f) t`.
    have hf_diff : DifferentiableAt ℝ (chartFiberAlong (I := I) γ V t) t :=
      chartFiberAlong_differentiableAt (I := I) γ V hV t
    set L : E →L[ℝ] ℝ := ((chartModelBasis E).coord l).toContinuousLinearMap with hL_def
    have hL_HD : HasDerivAt (fun s => L (chartFiberAlong (I := I) γ V t s))
        (L (deriv (chartFiberAlong (I := I) γ V t) t)) t :=
      (L.hasFDerivAt).comp_hasDerivAt t hf_diff.hasDerivAt
    have hL_eq : L (deriv (chartFiberAlong (I := I) γ V t) t) =
        deriv (fun s => L (chartFiberAlong (I := I) γ V t s)) t := hL_HD.deriv.symm
    have hfun : (fun s => L (chartFiberAlong (I := I) γ V t s)) =
        chartFiberCoordAlong (I := I) γ V t l := by
      funext s
      change ((chartModelBasis E).coord l) (chartFiberAlong (I := I) γ V t s) =
        chartFiberCoordAlong (I := I) γ V t l s
      rfl
    change ((chartModelBasis E).coord l) (deriv (chartFiberAlong (I := I) γ V t) t) = dv l
    change L (deriv (chartFiberAlong (I := I) γ V t) t) = dv l
    rw [hL_eq, hfun]
  have hdw_chartCoord : ∀ l : Fin n,
      chartCoord (E := E) l (deriv (chartFiberAlong (I := I) γ W t) t) = dw l := by
    intro l
    have hf_diff : DifferentiableAt ℝ (chartFiberAlong (I := I) γ W t) t :=
      chartFiberAlong_differentiableAt (I := I) γ W hW t
    set L : E →L[ℝ] ℝ := ((chartModelBasis E).coord l).toContinuousLinearMap with hL_def
    have hL_HD : HasDerivAt (fun s => L (chartFiberAlong (I := I) γ W t s))
        (L (deriv (chartFiberAlong (I := I) γ W t) t)) t :=
      (L.hasFDerivAt).comp_hasDerivAt t hf_diff.hasDerivAt
    have hL_eq : L (deriv (chartFiberAlong (I := I) γ W t) t) =
        deriv (fun s => L (chartFiberAlong (I := I) γ W t s)) t := hL_HD.deriv.symm
    have hfun : (fun s => L (chartFiberAlong (I := I) γ W t s)) =
        chartFiberCoordAlong (I := I) γ W t l := by
      funext s
      change ((chartModelBasis E).coord l) (chartFiberAlong (I := I) γ W t s) =
        chartFiberCoordAlong (I := I) γ W t l s
      rfl
    change ((chartModelBasis E).coord l) (deriv (chartFiberAlong (I := I) γ W t) t) = dw l
    change L (deriv (chartFiberAlong (I := I) γ W t) t) = dw l
    rw [hL_eq, hfun]
  -- Step B: chartCoord_l of `chartChristoffelContraction g α u̇ (V t) y`.
  -- General helper: chartCoord_l of `∑ k, c k • chartModelBasis E k = c l`.
  have hcoord_basis_sum : ∀ (c : Fin n → ℝ) (l : Fin n),
      chartCoord (E := E) l (∑ k : Fin n, c k • (chartModelBasis E k)) = c l := by
    intro c l
    classical
    -- chartCoord l = (chartModelBasis E).coord l, a linear map.
    change ((chartModelBasis E).repr (∑ k : Fin n, c k • (chartModelBasis E k))) l = c l
    -- Use `Basis.repr` linearity: `repr (∑ c k • basis k) = ∑ c k • (repr (basis k)) = ∑ c k • single k 1`.
    have hL : ((chartModelBasis E).repr (∑ k : Fin n, c k • (chartModelBasis E k))) =
        ∑ k : Fin n, c k • ((chartModelBasis E).repr (chartModelBasis E k)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul]
    rw [hL]
    -- Evaluate at `l`: `∑ k, c k • repr(basis k) l = ∑ k, c k * if k = l then 1 else 0 = c l`.
    rw [Finsupp.finset_sum_apply]
    have hsum_eq : ∑ k : Fin n,
        (c k • (chartModelBasis E).repr (chartModelBasis E k)) l =
      ∑ k : Fin n, if k = l then c k else 0 := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [(chartModelBasis E).repr_self]
      rw [Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply]
      by_cases hk : k = l
      · subst hk; simp
      · simp [hk]
    rw [hsum_eq]
    rw [Finset.sum_ite_eq' Finset.univ l (fun k => c k)]
    simp
  have hcontract_V : ∀ l : Fin n,
      chartCoord (E := E) l
        (chartChristoffelContraction (I := I) g α
          (deriv (chartCurveAt (I := I) γ t) t) (V t) y) =
        ∑ k : Fin n, udot k * ∑ i : Fin n, Γkil k i l * vt i := by
    intro l
    -- Apply the helper with `c k = ∑ i j, Γ_{ij}^k y · u̇^i · v^j`.
    set c : Fin n → ℝ := fun k =>
      ∑ i : Fin n, ∑ j : Fin n,
        chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i (deriv (chartCurveAt (I := I) γ t) t) *
          chartCoord (E := E) j (V t) with hc_def
    have hunfold : chartChristoffelContraction (I := I) g α
        (deriv (chartCurveAt (I := I) γ t) t) (V t) y =
      ∑ k_idx : Fin n, c k_idx • (chartModelBasis E k_idx) := rfl
    rw [hunfold, hcoord_basis_sum c l]
    -- Now show c l = ∑ k, udot k * ∑ i, Γkil k i l * vt i.
    -- c l = ∑ i j, Γ_{ij}^l · chartCoord_i u̇ · chartCoord_j (V t)
    -- target: ∑ k, udot_k · ∑ i, Γ_{ki}^l · vt_i
    --       = ∑ k, ∑ i, udot_k · Γ_{ki}^l · vt_i
    -- where udot_k = chartCoord_k u̇ and vt_i = chartCoord_i (V t).
    -- Rename: in c l, change `i, j` → `k, i`. Then both are 2-fold sums.
    rw [hc_def]
    -- Show the 2-fold sums match.
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    -- LHS summand: Γ_{ki}^l · chartCoord_k u̇ · chartCoord_i (V t)
    -- RHS summand: udot_k · (Γ_{ki}^l · vt_i)
    --            = chartCoord_k u̇ · (chartChristoffel g α k i l y · chartFiberCoordAlong γ V t i t)
    -- Apply `chartFiberCoordAlong_self` to identify vt_i = chartCoord_i (V t).
    change chartChristoffel (I := I) g α k i l y *
        chartCoord (E := E) k (deriv (chartCurveAt (I := I) γ t) t) *
        chartCoord (E := E) i (V t) =
      udot k * (Γkil k i l * vt i)
    change _ = udot k * (chartChristoffel (I := I) g α k i l y *
      chartFiberCoordAlong (I := I) γ V t i t)
    rw [chartFiberCoordAlong_self]
    change chartChristoffel (I := I) g α k i l y *
        chartCoord (E := E) k (deriv (chartCurveAt (I := I) γ t) t) *
        chartCoord (E := E) i (V t) =
      chartCoord (E := E) k (deriv (chartCurveAt (I := I) γ t) t) *
        (chartChristoffel (I := I) g α k i l y *
          chartCoord (E := E) i (V t))
    ring
  have hcontract_W : ∀ l : Fin n,
      chartCoord (E := E) l
        (chartChristoffelContraction (I := I) g α
          (deriv (chartCurveAt (I := I) γ t) t) (W t) y) =
        ∑ k : Fin n, udot k * ∑ j : Fin n, Γkil k j l * wt j := by
    intro l
    set c : Fin n → ℝ := fun k =>
      ∑ i : Fin n, ∑ j : Fin n,
        chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i (deriv (chartCurveAt (I := I) γ t) t) *
          chartCoord (E := E) j (W t) with hc_def
    have hunfold : chartChristoffelContraction (I := I) g α
        (deriv (chartCurveAt (I := I) γ t) t) (W t) y =
      ∑ k_idx : Fin n, c k_idx • (chartModelBasis E k_idx) := rfl
    rw [hunfold, hcoord_basis_sum c l]
    rw [hc_def]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    change chartChristoffel (I := I) g α k j l y *
        chartCoord (E := E) k (deriv (chartCurveAt (I := I) γ t) t) *
        chartCoord (E := E) j (W t) =
      udot k * (Γkil k j l * wt j)
    change _ = udot k * (chartChristoffel (I := I) g α k j l y *
      chartFiberCoordAlong (I := I) γ W t j t)
    rw [chartFiberCoordAlong_self]
    change chartChristoffel (I := I) g α k j l y *
        chartCoord (E := E) k (deriv (chartCurveAt (I := I) γ t) t) *
        chartCoord (E := E) j (W t) =
      chartCoord (E := E) k (deriv (chartCurveAt (I := I) γ t) t) *
        (chartChristoffel (I := I) g α k j l y *
          chartCoord (E := E) j (W t))
    ring
  -- Step C: chartCoord_l of `covDerivAlong g γ V t` = dv l + (Christoffel V-contraction)_l.
  have hcovV_chartCoord : ∀ l : Fin n,
      chartCoord (E := E) l (covDerivAlong (I := I) g γ V hγ hV t) =
        dv l + ∑ k : Fin n, udot k * ∑ i : Fin n, Γkil k i l * vt i := by
    intro l
    -- Unfold covDerivAlong and use the additivity of chartCoord (which is linear).
    rw [covDerivAlong_def]
    have hsum_eq : chartCoord (E := E) l
        (deriv (chartFiberAlong (I := I) γ V t) t +
          chartChristoffelContraction (I := I) g α
            (deriv (chartCurveAt (I := I) γ t) t) (V t)
            (chartCurveAt (I := I) γ t t)) =
        chartCoord (E := E) l (deriv (chartFiberAlong (I := I) γ V t) t) +
          chartCoord (E := E) l
            (chartChristoffelContraction (I := I) g α
              (deriv (chartCurveAt (I := I) γ t) t) (V t)
              (chartCurveAt (I := I) γ t t)) := by
      -- `chartCoord l = ((chartModelBasis E).repr · l)` is a linear functional, so additive.
      change ((chartModelBasis E).repr _) l = _ + _
      rw [map_add]
      rfl
    rw [hsum_eq, hdv_chartCoord l]
    -- `chartCurveAt γ t t = y` (definitionally `extChartAt I α (γ t) = y`).
    rw [hcurve_t]
    rw [hcontract_V l]
  have hcovW_chartCoord : ∀ l : Fin n,
      chartCoord (E := E) l (covDerivAlong (I := I) g γ W hγ hW t) =
        dw l + ∑ k : Fin n, udot k * ∑ j : Fin n, Γkil k j l * wt j := by
    intro l
    rw [covDerivAlong_def]
    have hsum_eq : chartCoord (E := E) l
        (deriv (chartFiberAlong (I := I) γ W t) t +
          chartChristoffelContraction (I := I) g α
            (deriv (chartCurveAt (I := I) γ t) t) (W t)
            (chartCurveAt (I := I) γ t t)) =
        chartCoord (E := E) l (deriv (chartFiberAlong (I := I) γ W t) t) +
          chartCoord (E := E) l
            (chartChristoffelContraction (I := I) g α
              (deriv (chartCurveAt (I := I) γ t) t) (W t)
              (chartCurveAt (I := I) γ t t)) := by
      change ((chartModelBasis E).repr _) l = _ + _
      rw [map_add]
      rfl
    rw [hsum_eq, hdw_chartCoord l]
    rw [hcurve_t]
    rw [hcontract_W l]
  -- Step D: express `g.inner α (∇V) (W t)` as a chart sum.
  have hαbase : α ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H α
  -- The sum form: g.inner α (∇V) (W t) = ∑ l j, (∇V)^l · w^j · G_lj
  have hinner_covV :
      g.inner α (covDerivAlong (I := I) g γ V hγ hV t) (W t) =
        ∑ l : Fin n, ∑ j : Fin n,
          chartCoord (E := E) l (covDerivAlong (I := I) g γ V hγ hV t) *
            chartCoord (E := E) j (W t) *
            chartGramOnE (I := I) g α l j y := by
    have hsum := g_inner_eq_chart_sum (I := I) g α (x := α) hαbase hsrc
      (covDerivAlong (I := I) g γ V hγ hV t) (W t)
    rw [hsum]
    refine Finset.sum_congr rfl ?_
    intro l _
    refine Finset.sum_congr rfl ?_
    intro j _
    -- The expression matches: `(repr l) (clmAt α α v) = chartCoord l v` for v at α.
    have hclmV := chartFiberCoord_eq_clmAt_of_mem (I := I) α
      (covDerivAlong (I := I) g γ V hγ hV t) (mem_chart_source H α)
    have hclmW := chartFiberCoord_eq_clmAt_of_mem (I := I) α (W t) (mem_chart_source H α)
    have hV_self := chartFiberCoord_self (I := I) α (covDerivAlong (I := I) g γ V hγ hV t)
    have hW_self := chartFiberCoord_self (I := I) α (W t)
    -- chartFiberCoord α ⟨α, X⟩ = X for X ∈ TangentSpace I α.
    -- combined with `chartFiberCoord_eq_clmAt_of_mem`:
    -- `clmAt α ℝ α X = X`, so `repr l (clmAt α ℝ α X) = repr l X = chartCoord l X`.
    have hVrepr : ((chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α
          (covDerivAlong (I := I) g γ V hγ hV t))) l =
        chartCoord (E := E) l (covDerivAlong (I := I) g γ V hγ hV t) := by
      rw [← hclmV, hV_self]; rfl
    have hWrepr : ((chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α (W t))) j =
        chartCoord (E := E) j (W t) := by
      rw [← hclmW, hW_self]; rfl
    rw [hVrepr, hWrepr]
  have hinner_covW :
      g.inner α (V t) (covDerivAlong (I := I) g γ W hγ hW t) =
        ∑ i : Fin n, ∑ l : Fin n,
          chartCoord (E := E) i (V t) *
            chartCoord (E := E) l (covDerivAlong (I := I) g γ W hγ hW t) *
            chartGramOnE (I := I) g α i l y := by
    have hsum := g_inner_eq_chart_sum (I := I) g α (x := α) hαbase hsrc
      (V t) (covDerivAlong (I := I) g γ W hγ hW t)
    rw [hsum]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro l _
    have hclmV := chartFiberCoord_eq_clmAt_of_mem (I := I) α (V t) (mem_chart_source H α)
    have hclmW := chartFiberCoord_eq_clmAt_of_mem (I := I) α
      (covDerivAlong (I := I) g γ W hγ hW t) (mem_chart_source H α)
    have hV_self := chartFiberCoord_self (I := I) α (V t)
    have hW_self := chartFiberCoord_self (I := I) α (covDerivAlong (I := I) g γ W hγ hW t)
    have hVrepr : ((chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α (V t))) i =
        chartCoord (E := E) i (V t) := by
      rw [← hclmV, hV_self]; rfl
    have hWrepr : ((chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α
          (covDerivAlong (I := I) g γ W hγ hW t))) l =
        chartCoord (E := E) l (covDerivAlong (I := I) g γ W hγ hW t) := by
      rw [← hclmW, hW_self]; rfl
    rw [hVrepr, hWrepr]
  -- Now combine: rewrite the chart-coord values via the basic identities.
  rw [hα_def] at hinner_covV hinner_covW
  have hvt_eq : ∀ i : Fin n, chartCoord (E := E) i (V t) = vt i := by
    intro i
    change chartCoord (E := E) i (V t) = chartFiberCoordAlong (I := I) γ V t i t
    rw [chartFiberCoordAlong_self]
  have hwt_eq : ∀ j : Fin n, chartCoord (E := E) j (W t) = wt j := by
    intro j
    change chartCoord (E := E) j (W t) = chartFiberCoordAlong (I := I) γ W t j t
    rw [chartFiberCoordAlong_self]
  have hG_eq : ∀ i j : Fin n, chartGramOnE (I := I) g α i j y = Gij i j := by
    intros; rfl
  -- RHS (using chart-sum of inner):
  --   g.inner α (cov V) (W t) + g.inner α (V t) (cov W)
  rw [hinner_covV, hinner_covW]
  -- Replace inner-applied chart coords by their `dv, vt, dw, wt`-counterparts.
  have hRHS_covV :
      (∑ l : Fin n, ∑ j : Fin n,
          chartCoord (E := E) l (covDerivAlong (I := I) g γ V hγ hV t) *
            chartCoord (E := E) j (W t) * chartGramOnE (I := I) g α l j y) =
      (∑ l : Fin n, ∑ j : Fin n,
          (dv l + ∑ k : Fin n, udot k * ∑ i : Fin n, Γkil k i l * vt i) *
            wt j * Gij l j) := by
    refine Finset.sum_congr rfl ?_
    intro l _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hcovV_chartCoord l, hwt_eq j]
  have hRHS_covW :
      (∑ i : Fin n, ∑ l : Fin n,
          chartCoord (E := E) i (V t) *
            chartCoord (E := E) l (covDerivAlong (I := I) g γ W hγ hW t) *
            chartGramOnE (I := I) g α i l y) =
      (∑ i : Fin n, ∑ l : Fin n,
          vt i * (dw l + ∑ k : Fin n, udot k * ∑ j : Fin n, Γkil k j l * wt j) *
            Gij i l) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [hvt_eq i, hcovW_chartCoord l]
  rw [hRHS_covV, hRHS_covW]
  -- LHS = A + B; RHS = C + D. We show A = C and B = D below.
  -- After dummy index renaming and `Finset.sum_comm`, these match.
  have hC :
      (∑ l : Fin n, ∑ j : Fin n,
          (dv l + ∑ k : Fin n, udot k * ∑ i : Fin n, Γkil k i l * vt i) *
            wt j * Gij l j) =
      (∑ i : Fin n, ∑ j : Fin n,
          (dv i * wt j * Gij i j +
            vt i * wt j *
              (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k i l * Gij l j))) := by
    classical
    -- Split LHS = LHS_a + LHS_b and RHS = RHS_a + RHS_b, then match each.
    have hLHS_split :
        (∑ l : Fin n, ∑ j : Fin n,
            (dv l + ∑ k : Fin n, udot k * ∑ i : Fin n, Γkil k i l * vt i) *
              wt j * Gij l j) =
        (∑ l : Fin n, ∑ j : Fin n, dv l * wt j * Gij l j) +
        (∑ l : Fin n, ∑ j : Fin n,
          (∑ k : Fin n, udot k * ∑ i : Fin n, Γkil k i l * vt i) *
            wt j * Gij l j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [add_mul, add_mul]
    have hRHS_split :
        (∑ i : Fin n, ∑ j : Fin n,
            (dv i * wt j * Gij i j +
              vt i * wt j *
                (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k i l * Gij l j))) =
        (∑ i : Fin n, ∑ j : Fin n, dv i * wt j * Gij i j) +
        (∑ i : Fin n, ∑ j : Fin n,
          vt i * wt j *
            (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k i l * Gij l j)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
    rw [hLHS_split, hRHS_split]
    -- First-piece equality (rename l → i).
    have hpart_a : (∑ l : Fin n, ∑ j : Fin n, dv l * wt j * Gij l j) =
        (∑ i : Fin n, ∑ j : Fin n, dv i * wt j * Gij i j) := rfl
    rw [hpart_a]
    congr 1
    -- Second-piece equality: convert both sides to a 4-fold sum.
    -- LHS:  ∑ l j, (∑ k, udot_k * ∑ i, Γ_{ki}^l * vt_i) * wt_j * Gij_{lj}
    --     = ∑ l j k i, udot_k * Γ_{ki}^l * vt_i * wt_j * Gij_{lj}
    -- RHS:  ∑ i j, vt_i * wt_j * (∑ k, udot_k * ∑ l, Γ_{ki}^l * Gij_{lj})
    --     = ∑ i j k l, udot_k * Γ_{ki}^l * vt_i * wt_j * Gij_{lj}
    -- These are sums of the same scalar function over Fin n^4; reorder via sum_comm.
    have hLHS_4 :
        (∑ l : Fin n, ∑ j : Fin n,
            (∑ k : Fin n, udot k * ∑ i : Fin n, Γkil k i l * vt i) *
              wt j * Gij l j) =
        (∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n,
            udot k * Γkil k i l * vt i * wt j * Gij l j) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    have hRHS_4 :
        (∑ i : Fin n, ∑ j : Fin n,
            vt i * wt j *
              (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k i l * Gij l j)) =
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            udot k * Γkil k i l * vt i * wt j * Gij l j) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    rw [hLHS_4, hRHS_4]
    -- Both sides are 4-fold sums of the same scalar `udot k * Γkil k i l * vt i * wt j * Gij l j`.
    -- LHS: ∑_l ∑_j ∑_k ∑_i. RHS: ∑_i ∑_j ∑_k ∑_l.
    -- The reordering is achieved by repeated `Finset.sum_comm`.
    -- LHS = ∑_l ∑_j ∑_k ∑_i F
    --     = ∑_j ∑_l ∑_k ∑_i F  (swap outer l ↔ j)
    --     = ∑_j ∑_k ∑_l ∑_i F  (swap l ↔ k at second level)
    --     = ∑_j ∑_k ∑_i ∑_l F  (swap inner l ↔ i)
    --     = ∑_k ∑_j ∑_i ∑_l F  (swap outer j ↔ k)
    --     ... and so on. This is messy; let's do bulk commutations to get to ∑_i ∑_j ∑_k ∑_l.
    -- Simpler: swap (l, i) — i.e., commute the outermost ∑_l with the innermost ∑_i.
    -- A swap of (l, _, _, i) → (i, _, _, l): keep j, k in place; swap l ↔ i.
    -- Use Finset.sum_comm twice:
    -- ∑_l ∑_j ∑_k ∑_i F = ∑_l ∑_j (∑_i ∑_k F) -- by sum_comm of (k, i)
    --                   = ∑_j ∑_l ∑_i ∑_k F  -- by sum_comm of (l, j)
    --                   ... still messy.
    -- Cleanest: convert to product sum, then reindex.
    -- LHS = ∑ p ∈ univ ×ˢ univ ×ˢ univ ×ˢ univ, F (p.1) p.2.1 p.2.2.1 p.2.2.2 (l, j, k, i)
    -- RHS = ∑ p ∈ univ ×ˢ univ ×ˢ univ ×ˢ univ, F (p.2.2.2) p.2.1 p.2.2.1 p.1 (i, j, k, l)
    -- and reindex.
    have hbij : ∀ (F : Fin n → Fin n → Fin n → Fin n → ℝ),
        (∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n, F l j k i) =
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n, F l j k i) := by
      intro F
      -- Step 1: inner swap (k, i) on LHS (within each (l, j)-pair).
      have hstep1 :
          (∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n, F l j k i) =
          (∑ l : Fin n, ∑ j : Fin n, ∑ i : Fin n, ∑ k : Fin n, F l j k i) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        exact Finset.sum_comm
      -- Step 2: swap (j, i) in middle positions (within each l).
      have hstep2 :
          (∑ l : Fin n, ∑ j : Fin n, ∑ i : Fin n, ∑ k : Fin n, F l j k i) =
          (∑ l : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, F l j k i) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        exact Finset.sum_comm
      -- Step 3: swap (l, i) outer.
      have hstep3 :
          (∑ l : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, F l j k i) =
          (∑ i : Fin n, ∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n, F l j k i) :=
        Finset.sum_comm
      -- Step 4: swap (l, j) inside each i.
      have hstep4 :
          (∑ i : Fin n, ∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n, F l j k i) =
          (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, ∑ k : Fin n, F l j k i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact Finset.sum_comm
      -- Step 5: swap (l, k) inside each (i, j).
      have hstep5 :
          (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, ∑ k : Fin n, F l j k i) =
          (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n, F l j k i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        exact Finset.sum_comm
      rw [hstep1, hstep2, hstep3, hstep4, hstep5]
    exact hbij (fun l j k i => udot k * Γkil k i l * vt i * wt j * Gij l j)
  -- Symmetric analog for the second piece.
  have hD :
      (∑ i : Fin n, ∑ l : Fin n,
          vt i * (dw l + ∑ k : Fin n, udot k * ∑ j : Fin n, Γkil k j l * wt j) *
            Gij i l) =
      (∑ i : Fin n, ∑ j : Fin n,
          (vt i * dw j * Gij i j +
            vt i * wt j *
              (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k j l * Gij l i))) := by
    classical
    have hLHS_split :
        (∑ i : Fin n, ∑ l : Fin n,
            vt i * (dw l + ∑ k : Fin n, udot k * ∑ j : Fin n, Γkil k j l * wt j) *
              Gij i l) =
        (∑ i : Fin n, ∑ l : Fin n, vt i * dw l * Gij i l) +
        (∑ i : Fin n, ∑ l : Fin n, vt i *
          (∑ k : Fin n, udot k * ∑ j : Fin n, Γkil k j l * wt j) * Gij i l) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [mul_add, add_mul]
    have hRHS_split :
        (∑ i : Fin n, ∑ j : Fin n,
            (vt i * dw j * Gij i j +
              vt i * wt j *
                (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k j l * Gij l i))) =
        (∑ i : Fin n, ∑ j : Fin n, vt i * dw j * Gij i j) +
        (∑ i : Fin n, ∑ j : Fin n,
          vt i * wt j *
            (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k j l * Gij l i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
    rw [hLHS_split, hRHS_split]
    have hpart_a : (∑ i : Fin n, ∑ l : Fin n, vt i * dw l * Gij i l) =
        (∑ i : Fin n, ∑ j : Fin n, vt i * dw j * Gij i j) := rfl
    rw [hpart_a]
    congr 1
    -- 4-fold sums.
    have hLHS_4 :
        (∑ i : Fin n, ∑ l : Fin n, vt i *
            (∑ k : Fin n, udot k * ∑ j : Fin n, Γkil k j l * wt j) * Gij i l) =
        (∑ i : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ j : Fin n,
            vt i * udot k * Γkil k j l * wt j * Gij i l) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have hRHS_4 :
        (∑ i : Fin n, ∑ j : Fin n, vt i * wt j *
            (∑ k : Fin n, udot k * ∑ l : Fin n, Γkil k j l * Gij l i)) =
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            vt i * udot k * Γkil k j l * wt j * Gij l i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    rw [hLHS_4, hRHS_4]
    -- Reorder: ∑_i ∑_l ∑_k ∑_j to match ∑_i ∑_j ∑_k ∑_l.
    -- We need to express both as ∑(i,j,k,l) of the same scalar.
    -- The scalar is vt_i * udot_k * Γ_{kj}^l * wt_j * Gij_{l i} on RHS, but
    -- Gij_{li} is for `Gij i l` symmetric in `(i, l)`? Actually `Gij i j` was defined as
    -- `chartGramOnE g α i j y`, which IS symmetric in `(i, j)` via `chartGramOnE_symm`.
    -- We use that to identify Gij_{li} = Gij_{il}.
    have hsymm : ∀ a b : Fin n, Gij a b = Gij b a := by
      intros a b
      change chartGramOnE (I := I) g α a b y = chartGramOnE (I := I) g α b a y
      exact chartGramOnE_symm (I := I) g α a b y
    -- Replace Gij_{l i} by Gij_{i l} in RHS_4.
    have hRHS_4_symm :
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            vt i * udot k * Γkil k j l * wt j * Gij l i) =
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            vt i * udot k * Γkil k j l * wt j * Gij i l) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      refine Finset.sum_congr rfl ?_
      intro k _
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [hsymm l i]
    rw [hRHS_4_symm]
    -- Now both sides are sums over Fin n × Fin n × Fin n × Fin n of
    -- `vt i * udot k * Γkil k j l * wt j * Gij i l`, indexed (i, l, k, j) on LHS
    -- and (i, j, k, l) on RHS. Reorder.
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- LHS: ∑ l ∑ k ∑ j G; RHS: ∑ j ∑ k ∑ l G. Use 3-step commute.
    have hbij3 : ∀ (G : Fin n → Fin n → Fin n → ℝ),
        (∑ l : Fin n, ∑ k : Fin n, ∑ j : Fin n, G l k j) =
        (∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n, G l k j) := by
      intro G
      -- Step 1: swap outer (l, k): ∑ l ∑ k = ∑ k ∑ l.
      rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun l k => ∑ j : Fin n, G l k j)]
      -- Now: ∑ k ∑ l ∑ j G = ∑ j ∑ k ∑ l G.
      -- Step 2: swap inner (l, j) for each k: ∑ l ∑ j = ∑ j ∑ l.
      have h2 : (∑ k : Fin n, ∑ l : Fin n, ∑ j : Fin n, G l k j) =
          (∑ k : Fin n, ∑ j : Fin n, ∑ l : Fin n, G l k j) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact Finset.sum_comm
      rw [h2]
      -- Now: ∑ k ∑ j ∑ l G = ∑ j ∑ k ∑ l G.
      -- Step 3: swap outer (k, j): ∑ k ∑ j = ∑ j ∑ k.
      exact Finset.sum_comm
    exact hbij3 (fun l k j => vt i * udot k * Γkil k j l * wt j * Gij i l)
  -- A = C and B = D conclude.
  rw [← hC, ← hD]

/-! ## Metric compatibility headline -/

/-- **Metric compatibility for the chart-Christoffel covariant derivative along a curve.**
For a smooth Riemannian metric `g` on a smooth boundaryless manifold `M`, a `C¹` curve
`γ : ℝ → M`, and `C¹` vector fields `V, W` along `γ`, the inner product
`s ↦ g.inner (γ s) (V s) (W s)` is differentiable at every time `t` with
`d/dt g(V, W) = g(∇_γ̇ V, W) + g(V, ∇_γ̇ W)`. -/
theorem covDerivAlong_metric_compatibility
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M)))
    (t : ℝ) :
    deriv (fun s => g.inner (γ s) (V s) (W s)) t =
      g.inner (γ t) (covDerivAlong (I := I) g γ V hγ hV t) (W t) +
        g.inner (γ t) (V t) (covDerivAlong (I := I) g γ W hγ hW t) := by
  classical
  -- (1) Locally, `g.inner (γ s) (V s) (W s) = ∑ ij, v^i(s) w^j(s) G_ij(s)`.
  have hev := g_inner_eq_chart_sum_along_eventually (I := I) g γ hγ V W t
  -- (2) Both functions have the same derivative at `t`.
  have hderiv_eq : deriv (fun s => g.inner (γ s) (V s) (W s)) t =
      deriv (fun s => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartFiberCoordAlong (I := I) γ V t i s *
            chartFiberCoordAlong (I := I) γ W t j s *
            chartGramAlong (I := I) g γ t i j s) t :=
    Filter.EventuallyEq.deriv_eq hev
  rw [hderiv_eq]
  -- (3) Compute the derivative of the chart-sum via the triple-product rule.
  rw [deriv_chart_sum_at (I := I) g V W hγ hV hW t]
  -- (4) The resulting sum equals the metric-compatibility right-hand side via the chart-metric
  -- identity (`partialDeriv_chartGramOnE_eq_chartChristoffel_sum`).
  exact chart_sum_deriv_eq_inner_covDeriv (I := I) g V W hγ hV hW t

end Curve
end Riemannian
end Geometry
end DifferentialGeometry

end
