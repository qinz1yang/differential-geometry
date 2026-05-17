import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Basic

set_option linter.unusedSectionVars false

/-!
# Covariant derivative of a vector field along a curve

For a smooth Riemannian metric `g` on a smooth manifold `M`, a curve
`γ : ℝ → M`, and a "vector field along γ" `V : ∀ t, TangentSpace I (γ t)`,
this file defines `covDerivAlong g γ V hγ hV t`, the covariant derivative
of `V` along `γ` at time `t`, valued in `TangentSpace I (γ t)`.

The definition uses the chart at `γ t` itself: in this chart, the curve
becomes `s ↦ extChartAt I (γ t) (γ s) : ℝ → E` and the lifted curve
becomes a chart-fibre representation `s ↦ chartFiberCoord (γ t) ⟨γ s, V s⟩`.
The covariant derivative at `t` is then the scalar derivative of the
chart-fibre representation, corrected by the Christoffel contraction:
$$
(\nabla_{\dot\gamma} V)^i(t) =
  \frac{d}{ds}\bigg|_{s=t} \big(\mathrm{chartFiber}_{\gamma t}(V s)\big)^i
  + \sum_{j,k} \Gamma^{i}{}_{jk}(\gamma t)\,
      \dot\gamma^j(t)\, V^k(t),
$$
where all chart-coordinate quantities are taken in `extChartAt I (γ t)`
and `Γ` is `chartChristoffel g (γ t)` (see
`DifferentialGeometry/Geometry/Hessian.lean` and
`DifferentialGeometry/Geometry/Riemannian/Geodesic/Equation.lean`).

Because the definition uses a single canonically determined chart (the
one at `γ t`), chart-independence is built into the definition.

## Algebraic properties (main public API)

* `covDerivAlong_add`: additivity in `V`.
* `covDerivAlong_smul_const`: ℝ-linearity in `V` for constant scalars.
* `covDerivAlong_smul_function`: Leibniz rule over scalar functions
  `f : ℝ → ℝ`.

The smoothness hypothesis on `V` is the `C¹` condition
`ContMDiff 𝓘(ℝ, ℝ) I.tangent 1 (fun t => (⟨γ t, V t⟩ : TangentBundle I M))`.

## What this file does **not** provide

`covDerivAlong_metric_compatibility` (the identity
`d/dt g(V,W) = g(∇V, W) + g(V, ∇W)`) is intentionally not delivered here:
its proof reduces to the chart-coordinate metric-compatibility identity
$$\partial_k G_{ij}(y) = \sum_\ell \big(\Gamma^\ell{}_{ki}(y)\,G_{\ell j}(y)
   + \Gamma^\ell{}_{kj}(y)\,G_{\ell i}(y)\big),$$
which expresses the symmetry of the Levi-Civita Christoffel symbols
relative to the Gram matrix and is a self-contained chart-level
identity. It is recorded as a pending mathematical prerequisite.
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
open DifferentialGeometry.Geometry.Riemannian.Geodesic

/-! ## Chart-fibre representation of a vector field along a curve -/

/-- The chart-fibre representation of a vector field along a curve `γ`
at base time `t`, evaluated at time `s`: the chart-α fibre coordinate
of `⟨γ s, V s⟩` in the trivialisation at `α := γ t`. -/
def chartFiberAlong (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (t : ℝ) : ℝ → E :=
  fun s => chartFiberCoord (I := I) (γ t) (⟨γ s, V s⟩ : TangentBundle I M)

@[simp] lemma chartFiberAlong_def (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t s : ℝ) :
    chartFiberAlong (I := I) γ V t s =
      chartFiberCoord (I := I) (γ t) (⟨γ s, V s⟩ : TangentBundle I M) := rfl

/-! ## Fibre-linearity of `chartFiberCoord` on the base set -/

/-- On the base set, the chart-fibre coordinate is given by the
trivialisation's `continuousLinearMapAt`, hence is `ℝ`-linear in the
fibre argument. -/
lemma chartFiberCoord_eq_clmAt_of_mem (α : M) {b : M} (v : TangentSpace I b)
    (hb : b ∈ (chartAt H α).source) :
    chartFiberCoord (I := I) α (⟨b, v⟩ : TangentBundle I M) =
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b) v := by
  classical
  have hb' : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hb
  have hcoe :=
    (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem
      (R := ℝ) hb'
  have hclmAt_eq_lm :
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b) v =
        ((trivializationAt E (TangentSpace I) α).linearMapAt ℝ b) v := rfl
  rw [hclmAt_eq_lm, hcoe]
  rfl

/-- Additivity of `chartFiberCoord` in the fibre argument, on the base set. -/
lemma chartFiberCoord_add_of_mem (α : M) {b : M} (v w : TangentSpace I b)
    (hb : b ∈ (chartAt H α).source) :
    chartFiberCoord (I := I) α (⟨b, v + w⟩ : TangentBundle I M) =
      chartFiberCoord (I := I) α (⟨b, v⟩ : TangentBundle I M) +
        chartFiberCoord (I := I) α (⟨b, w⟩ : TangentBundle I M) := by
  rw [chartFiberCoord_eq_clmAt_of_mem (I := I) α v hb,
    chartFiberCoord_eq_clmAt_of_mem (I := I) α w hb,
    chartFiberCoord_eq_clmAt_of_mem (I := I) α (v + w) hb,
    ContinuousLinearMap.map_add]

/-- ℝ-scalar multiplication compatibility of `chartFiberCoord` in the
fibre argument, on the base set. -/
lemma chartFiberCoord_smul_of_mem (α : M) {b : M} (c : ℝ)
    (v : TangentSpace I b) (hb : b ∈ (chartAt H α).source) :
    chartFiberCoord (I := I) α (⟨b, c • v⟩ : TangentBundle I M) =
      c • chartFiberCoord (I := I) α (⟨b, v⟩ : TangentBundle I M) := by
  rw [chartFiberCoord_eq_clmAt_of_mem (I := I) α v hb,
    chartFiberCoord_eq_clmAt_of_mem (I := I) α (c • v) hb,
    ContinuousLinearMap.map_smul]

/-- At the base point itself, the chart-fibre coordinate is the identity. -/
lemma chartFiberCoord_self (α : M) (v : TangentSpace I α) :
    chartFiberCoord (I := I) α (⟨α, v⟩ : TangentBundle I M) = v := by
  classical
  have hself : α ∈ (chartAt H α).source := mem_chart_source H α
  rw [chartFiberCoord_eq_clmAt_of_mem (I := I) α v hself]
  -- `(trivAt α).continuousLinearMapAt ℝ α = coordChange α α α`, and that's the identity.
  have hcore :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (I := I) (M := M) (b₀ := α) (b := α) hself
  rw [hcore]
  apply (tangentBundleCore I M).coordChange_self
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hself

/-- At base time `s = t`, the chart-fibre representation equals `V t`. -/
@[simp] lemma chartFiberAlong_self (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    chartFiberAlong (I := I) γ V t t = V t := by
  unfold chartFiberAlong
  exact chartFiberCoord_self (I := I) (γ t) (V t)

/-! ## `chartFiberAlong` is `C¹` from a `C¹` lift

We extract scalar `C¹`/differentiability of `chartFiberAlong γ V t` at
`t` from the manifold `C¹` smoothness of the total-space lift, using
`Trivialization.contMDiffAt_iff` for the trivialisation at `γ t`. -/

/-- The chart-fibre-along function is `C¹` in `s` at `s = t`, given the
`C¹` smoothness hypothesis on the total-space lift. -/
lemma chartFiberAlong_contMDiffAt (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t))
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (t : ℝ) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (chartFiberAlong (I := I) γ V t) t := by
  classical
  -- We apply `Trivialization.contMDiffAt_iff` for the trivialisation at `α = γ t`.
  -- The hypothesis gives us `ContMDiffAt 𝓘(ℝ) (I.prod 𝓘(ℝ, E)) 1 (fun s => ⟨γ s, V s⟩) t`,
  -- which by the trivialisation `iff`-lemma decomposes into smoothness of the
  -- projection (` γ`) and smoothness of the trivialised fibre map.
  set α := γ t with hα
  -- The lift sends `t` to a point in the source of the trivialisation at α.
  have hin_src : (fun s => (⟨γ s, V s⟩ : TangentBundle I M)) t ∈
      (trivializationAt E (TangentSpace I) α).source := by
    rw [Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (γ t)
  have hVat : ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) 1
      (fun s => (⟨γ s, V s⟩ : TangentBundle I M)) t := hV.contMDiffAt
  -- Apply `e.contMDiffAt_iff`.
  have hiff :=
    (trivializationAt E (TangentSpace I) α).contMDiffAt_iff
      (IM := 𝓘(ℝ, ℝ)) (IB := I) (n := (1 : WithTop ℕ∞))
      (f := fun s => (⟨γ s, V s⟩ : TangentBundle I M)) hin_src
  -- `(hiff.mp hVat).2 : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) 1 (s ↦ (trivAt α ⟨γ s, V s⟩).2) t`.
  exact (hiff.mp hVat).2

/-- Scalar differentiability of `chartFiberAlong γ V t` at `t`. -/
lemma chartFiberAlong_differentiableAt (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t))
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (t : ℝ) :
    DifferentiableAt ℝ (chartFiberAlong (I := I) γ V t) t := by
  classical
  have h := chartFiberAlong_contMDiffAt (I := I) γ V hV t
  -- `ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) 1 f t → ContDiffAt ℝ 1 f t`.
  have hcd : ContDiffAt ℝ 1 (chartFiberAlong (I := I) γ V t) t := h.contDiffAt
  exact hcd.differentiableAt_one

/-! ## Eventual equalities of `chartFiberAlong`

The chart-fibre representation is fibrewise linear *only on the chart
base set*, but the curve `γ` enters the chart base set on a
neighbourhood of `t` (by continuity of `γ` plus `γ t ∈ chart source`).
Hence the additivity / scalar / Leibniz identities hold *eventually*
near `t`, which is sufficient to conclude `deriv`-equality at `t`. -/

/-- `γ s ∈ (chartAt H (γ t)).source` for `s` near `t`. -/
lemma eventually_γ_mem_chartAt (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (t : ℝ) :
    ∀ᶠ s in nhds t, γ s ∈ (chartAt H (γ t)).source := by
  have hcont : Continuous γ := hγ.continuous
  have hop : IsOpen ((chartAt H (γ t)).source) := (chartAt H (γ t)).open_source
  have hmem : γ t ∈ (chartAt H (γ t)).source := mem_chart_source H (γ t)
  exact (hcont.continuousAt).preimage_mem_nhds (hop.mem_nhds hmem)

/-- For `V`, `W`, `V + W` (the latter packaged as `λ t, V t + W t`), the
chart-fibre representations satisfy additivity *eventually* near `t`. -/
lemma chartFiberAlong_add_eventually (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (V W : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    (fun s => chartFiberAlong (I := I) γ (fun u => V u + W u) t s) =ᶠ[nhds t]
      (fun s => chartFiberAlong (I := I) γ V t s +
        chartFiberAlong (I := I) γ W t s) := by
  filter_upwards [eventually_γ_mem_chartAt (I := I) γ hγ t] with s hs
  unfold chartFiberAlong
  exact chartFiberCoord_add_of_mem (I := I) (γ t) (V s) (W s) hs

/-- Eventual scalar-multiplication compatibility of `chartFiberAlong`. -/
lemma chartFiberAlong_smul_const_eventually (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (c : ℝ) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    (fun s => chartFiberAlong (I := I) γ (fun u => c • V u) t s) =ᶠ[nhds t]
      (fun s => c • chartFiberAlong (I := I) γ V t s) := by
  filter_upwards [eventually_γ_mem_chartAt (I := I) γ hγ t] with s hs
  unfold chartFiberAlong
  exact chartFiberCoord_smul_of_mem (I := I) (γ t) c (V s) hs

/-- Eventual Leibniz-rule compatibility of `chartFiberAlong` over scalar
functions. -/
lemma chartFiberAlong_smul_function_eventually (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (f : ℝ → ℝ) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    (fun s => chartFiberAlong (I := I) γ (fun u => f u • V u) t s) =ᶠ[nhds t]
      (fun s => f s • chartFiberAlong (I := I) γ V t s) := by
  filter_upwards [eventually_γ_mem_chartAt (I := I) γ hγ t] with s hs
  unfold chartFiberAlong
  exact chartFiberCoord_smul_of_mem (I := I) (γ t) (f s) (V s) hs

/-! ## Chart-coordinate curve in the chart at `γ t` -/

/-- The chart-coordinate curve `s ↦ φ_{γ t}(γ s)` in the chart at `γ t`. -/
def chartCurveAt (γ : ℝ → M) (t : ℝ) : ℝ → E :=
  fun s => extChartAt I (γ t) (γ s)

@[simp] lemma chartCurveAt_def (γ : ℝ → M) (t s : ℝ) :
    chartCurveAt (I := I) γ t s = extChartAt I (γ t) (γ s) := rfl

/-! ## The covariant derivative along a curve -/

/-- The covariant derivative of a vector field `V` along a curve `γ` at
time `t`, for a smooth Riemannian metric `g`.

The formula in the chart at `γ t` reads
```
(∇_γ̇ V)(t) = (d/ds V^chart(s))|_{s=t}
           + Γ_{γ t}(γ̇^chart(t), V^chart(t))(φ_{γ t}(γ t)),
```
where:
* `V^chart(s) := chartFiberCoord (γ t) ⟨γ s, V s⟩` is the chart-α
  fibre coordinate at time `s`,
* `γ̇^chart(t) := deriv (s ↦ φ_{γ t}(γ s)) t` is the chart velocity,
* the Christoffel contraction `Γ_{γ t}(·, ·)(y)` is the chart-coordinate
  expression of the Levi-Civita connection at `γ t`.

The hypotheses `hγ` (a `C¹` curve) and `hV` (a `C¹` total-space lift of
the vector field along `γ`) ensure the underlying derivatives exist;
they do not enter the formula directly. Since the chart at `γ t` is
canonically determined by the basepoint `γ t`, this definition is
chart-independent by construction. -/
def covDerivAlong
    (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (_hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (_hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (t : ℝ) : TangentSpace I (γ t) :=
  deriv (chartFiberAlong (I := I) γ V t) t +
    chartChristoffelContraction (I := I) g (γ t)
      (deriv (chartCurveAt (I := I) γ t) t)
      (V t)
      (chartCurveAt (I := I) γ t t)

@[simp] lemma covDerivAlong_def
    (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (t : ℝ) :
    covDerivAlong (I := I) g γ V hγ hV t =
      deriv (chartFiberAlong (I := I) γ V t) t +
        chartChristoffelContraction (I := I) g (γ t)
          (deriv (chartCurveAt (I := I) γ t) t)
          (V t)
          (chartCurveAt (I := I) γ t t) := rfl

/-! ## Right-linearity of the Christoffel contraction in the second slot -/

/-- Additivity of the Christoffel contraction in the second vector slot. -/
lemma chartChristoffelContraction_add_right
    (g : SmoothRiemannianMetric I M) (α : M)
    (v w₁ w₂ : E) (y : E) :
    chartChristoffelContraction (I := I) g α v (w₁ + w₂) y =
      chartChristoffelContraction (I := I) g α v w₁ y +
        chartChristoffelContraction (I := I) g α v w₂ y := by
  classical
  unfold chartChristoffelContraction
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [← add_smul]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hadd : chartCoord (E := E) j (w₁ + w₂) =
      chartCoord (E := E) j w₁ + chartCoord (E := E) j w₂ := by
    simp [chartCoord, map_add]
  rw [hadd]
  ring

/-- Scalar-multiplication compatibility of the Christoffel contraction in
the second vector slot. -/
lemma chartChristoffelContraction_smul_right
    (g : SmoothRiemannianMetric I M) (α : M)
    (c : ℝ) (v w : E) (y : E) :
    chartChristoffelContraction (I := I) g α v (c • w) y =
      c • chartChristoffelContraction (I := I) g α v w y := by
  classical
  unfold chartChristoffelContraction
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [smul_smul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [chartCoord_smul]
  ring

/-! ## Algebraic properties of `covDerivAlong`

The proofs proceed by:
1. unfolding `covDerivAlong` to its chart formula,
2. using `Filter.EventuallyEq.deriv_eq` to transfer the eventual
   additivity / scalar / Leibniz identity of `chartFiberAlong` to a
   pointwise identity of derivatives at `t`,
3. using additivity / scalar / Leibniz for `deriv` on the chart-fibre part,
4. using right-linearity of `chartChristoffelContraction` on the
   Christoffel-correction part,
5. assembling.
-/

section AlgebraicProperties

variable {g : SmoothRiemannianMetric I M} {γ : ℝ → M}

/-- **Additivity in `V`.** -/
theorem covDerivAlong_add
    (V W : ∀ t, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M)))
    (hVW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t + W t⟩ : TangentBundle I M)))
    (t : ℝ) :
    covDerivAlong (I := I) g γ (fun t => V t + W t) hγ hVW t =
      covDerivAlong (I := I) g γ V hγ hV t +
        covDerivAlong (I := I) g γ W hγ hW t := by
  classical
  -- (1) Transfer eventual additivity of chartFiberAlong to a deriv-equality.
  have hev := chartFiberAlong_add_eventually (I := I) γ hγ V W t
  -- The deriv of the LHS at `t` equals the deriv of the RHS at `t`.
  have hderiv_eq : deriv (chartFiberAlong (I := I) γ (fun u => V u + W u) t) t =
      deriv (fun s => chartFiberAlong (I := I) γ V t s +
        chartFiberAlong (I := I) γ W t s) t :=
    Filter.EventuallyEq.deriv_eq hev
  -- (2) Additivity of `deriv` for the sum on the RHS, using differentiability.
  have hV_d : DifferentiableAt ℝ (chartFiberAlong (I := I) γ V t) t :=
    chartFiberAlong_differentiableAt (I := I) γ V hV t
  have hW_d : DifferentiableAt ℝ (chartFiberAlong (I := I) γ W t) t :=
    chartFiberAlong_differentiableAt (I := I) γ W hW t
  have hderiv_sum :
      deriv (fun s => chartFiberAlong (I := I) γ V t s +
        chartFiberAlong (I := I) γ W t s) t =
      deriv (chartFiberAlong (I := I) γ V t) t +
        deriv (chartFiberAlong (I := I) γ W t) t :=
    deriv_add hV_d hW_d
  -- (3) Combine: deriv of (V+W) chart-fibre = deriv V + deriv W.
  have hderiv_add :
      deriv (chartFiberAlong (I := I) γ (fun u => V u + W u) t) t =
        deriv (chartFiberAlong (I := I) γ V t) t +
          deriv (chartFiberAlong (I := I) γ W t) t :=
    hderiv_eq.trans hderiv_sum
  -- (4) Unfold both sides.
  rw [covDerivAlong_def, covDerivAlong_def, covDerivAlong_def, hderiv_add]
  -- Rewrite Γ's second slot via additivity. We invoke the lemma with explicit
  -- second-slot vectors to avoid `TangentSpace` vs `E` `Add`-instance friction.
  have hΓ_add := chartChristoffelContraction_add_right (I := I) g (γ t)
    (deriv (chartCurveAt (I := I) γ t) t) (V t) (W t)
    (chartCurveAt (I := I) γ t t)
  rw [show
      chartChristoffelContraction (I := I) g (γ t)
        (deriv (chartCurveAt (I := I) γ t) t) (V t + W t)
        (chartCurveAt (I := I) γ t t) =
      chartChristoffelContraction (I := I) g (γ t)
        (deriv (chartCurveAt (I := I) γ t) t) (V t)
        (chartCurveAt (I := I) γ t t) +
      chartChristoffelContraction (I := I) g (γ t)
        (deriv (chartCurveAt (I := I) γ t) t) (W t)
        (chartCurveAt (I := I) γ t t) from hΓ_add]
  abel

/-- **Scalar multiplication by a constant.** -/
theorem covDerivAlong_smul_const
    (c : ℝ) (V : ∀ t, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (hcV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, c • V t⟩ : TangentBundle I M)))
    (t : ℝ) :
    covDerivAlong (I := I) g γ (fun t => c • V t) hγ hcV t =
      c • covDerivAlong (I := I) g γ V hγ hV t := by
  classical
  have hev := chartFiberAlong_smul_const_eventually (I := I) γ hγ c V t
  have hderiv_eq : deriv (chartFiberAlong (I := I) γ (fun u => c • V u) t) t =
      deriv (fun s => c • chartFiberAlong (I := I) γ V t s) t :=
    Filter.EventuallyEq.deriv_eq hev
  have hV_d : DifferentiableAt ℝ (chartFiberAlong (I := I) γ V t) t :=
    chartFiberAlong_differentiableAt (I := I) γ V hV t
  have hderiv_smul_RHS :
      deriv (fun s => c • chartFiberAlong (I := I) γ V t s) t =
      c • deriv (chartFiberAlong (I := I) γ V t) t :=
    deriv_fun_const_smul c hV_d
  have hderiv_smul :
      deriv (chartFiberAlong (I := I) γ (fun u => c • V u) t) t =
        c • deriv (chartFiberAlong (I := I) γ V t) t :=
    hderiv_eq.trans hderiv_smul_RHS
  rw [covDerivAlong_def, covDerivAlong_def, hderiv_smul]
  -- Goal: c • deriv V_α + Γ(γ̇, c • V t) = c • (deriv V_α + Γ(γ̇, V t))
  -- Rewrite the Christoffel-contraction's second slot via smul-right.
  have hΓ_smul := chartChristoffelContraction_smul_right (I := I) g (γ t)
    c (deriv (chartCurveAt (I := I) γ t) t) (V t)
    (chartCurveAt (I := I) γ t t)
  rw [show
      chartChristoffelContraction (I := I) g (γ t)
        (deriv (chartCurveAt (I := I) γ t) t) (c • V t)
        (chartCurveAt (I := I) γ t t) =
      c • chartChristoffelContraction (I := I) g (γ t)
        (deriv (chartCurveAt (I := I) γ t) t) (V t)
        (chartCurveAt (I := I) γ t t) from hΓ_smul]
  -- Goal: c • dV + c • Γ = c • (dV + Γ).
  -- Compute as `E`-valued equation via the definitional `TangentSpace I _ = E`.
  let dV : E := deriv (chartFiberAlong (I := I) γ V t) t
  let Γv : E := chartChristoffelContraction (I := I) g (γ t)
    (deriv (chartCurveAt (I := I) γ t) t) (V t)
    (chartCurveAt (I := I) γ t t)
  change c • dV + c • Γv = c • (dV + Γv)
  rw [smul_add]

/-- **Leibniz rule over scalar functions.** -/
theorem covDerivAlong_smul_function
    (f : ℝ → ℝ) {t : ℝ} (V : ∀ t, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hf : DifferentiableAt ℝ f t)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (hfV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, f t • V t⟩ : TangentBundle I M))) :
    covDerivAlong (I := I) g γ (fun t => f t • V t) hγ hfV t =
      deriv f t • V t + f t • covDerivAlong (I := I) g γ V hγ hV t := by
  classical
  have hev := chartFiberAlong_smul_function_eventually (I := I) γ hγ f V t
  -- deriv of LHS at t = deriv of `s ↦ f s • V_α s` at t.
  have hderiv_eq : deriv (chartFiberAlong (I := I) γ (fun u => f u • V u) t) t =
      deriv (fun s => f s • chartFiberAlong (I := I) γ V t s) t :=
    Filter.EventuallyEq.deriv_eq hev
  have hV_d : DifferentiableAt ℝ (chartFiberAlong (I := I) γ V t) t :=
    chartFiberAlong_differentiableAt (I := I) γ V hV t
  -- Product rule: `deriv (s ↦ f s • V_α s) t = f t • V_α' t + f' t • V_α t`.
  have hderiv_smul_RHS :
      deriv (fun s => f s • chartFiberAlong (I := I) γ V t s) t =
      f t • deriv (chartFiberAlong (I := I) γ V t) t +
        deriv f t • chartFiberAlong (I := I) γ V t t :=
    deriv_fun_smul hf hV_d
  have hderiv_smul :
      deriv (chartFiberAlong (I := I) γ (fun u => f u • V u) t) t =
      f t • deriv (chartFiberAlong (I := I) γ V t) t +
        deriv f t • chartFiberAlong (I := I) γ V t t :=
    hderiv_eq.trans hderiv_smul_RHS
  rw [covDerivAlong_def, covDerivAlong_def]
  -- Simplify chart-fibre self-value: `chartFiberAlong γ V t t = V t`.
  have hself_V : chartFiberAlong (I := I) γ V t t = V t :=
    chartFiberAlong_self (I := I) γ V t
  rw [hderiv_smul, hself_V]
  -- Rewrite Γ's second slot via smul-right.
  have hΓ_smul := chartChristoffelContraction_smul_right (I := I) g (γ t)
    (f t) (deriv (chartCurveAt (I := I) γ t) t) (V t)
    (chartCurveAt (I := I) γ t t)
  rw [show
      chartChristoffelContraction (I := I) g (γ t)
        (deriv (chartCurveAt (I := I) γ t) t) (f t • V t)
        (chartCurveAt (I := I) γ t t) =
      f t • chartChristoffelContraction (I := I) g (γ t)
        (deriv (chartCurveAt (I := I) γ t) t) (V t)
        (chartCurveAt (I := I) γ t t) from hΓ_smul]
  -- Goal: f t • dV + df • V + f t • Γ = df • V + f t • (dV + Γ).
  -- Compute as `E`-valued equation via the definitional `TangentSpace I _ = E`.
  let dV : E := deriv (chartFiberAlong (I := I) γ V t) t
  let Vv : E := V t
  let Γv : E := chartChristoffelContraction (I := I) g (γ t)
    (deriv (chartCurveAt (I := I) γ t) t) (V t)
    (chartCurveAt (I := I) γ t t)
  change f t • dV + deriv f t • Vv + f t • Γv =
    deriv f t • Vv + f t • (dV + Γv)
  rw [smul_add]
  abel

end AlgebraicProperties

end Curve
end Riemannian
end Geometry
end DifferentialGeometry

end
