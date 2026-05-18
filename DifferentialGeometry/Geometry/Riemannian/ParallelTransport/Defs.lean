import DifferentialGeometry.Geometry.Riemannian.Curve.CovDerivAlongMetric

set_option linter.unusedSectionVars false

/-!
# Parallel vector fields along a curve

For a smooth Riemannian metric `g` on a smooth boundaryless manifold `M` and a
`C¹` curve `γ : ℝ → M`, a `C¹` vector field `V` along `γ` is **parallel** if its
covariant derivative along `γ` vanishes identically:
`covDerivAlong g γ V _ _ t = 0` for every `t`.

The main result of this file is the **inner-product preservation** property:
if `V` and `W` are both parallel along `γ`, then `g.inner (γ s) (V s) (W s)` is
constant in `s`. As a special case, the `g`-norm of a parallel field is
constant. Both statements are unconditional consequences of the metric
compatibility identity `covDerivAlong_metric_compatibility`.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry DifferentialGeometry.Integral.Measure
  DifferentialGeometry.Geometry.Riemannian.Curve

namespace Geometry
namespace Riemannian
namespace ParallelTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Parallel vector field along a curve -/

/-- A vector field `V` along a `C¹` curve `γ` is **parallel** if its covariant
derivative along `γ` vanishes at every time. -/
def IsParallelAlong (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))) : Prop :=
  ∀ t, covDerivAlong (I := I) g γ V hγ hV t = 0

/-! ## Differentiability of the inner product along the curve

The function `s ↦ g.inner (γ s) (V s) (W s)` is differentiable at every time
`t`. Locally near `t`, it coincides with the chart-sum representation, whose
differentiability is established in `Curve.CovDerivAlongMetric`. -/

/-- Differentiability of the inner product along the curve at a single time. -/
private lemma g_inner_along_differentiableAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (V W : ∀ t, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M)))
    (t : ℝ) :
    DifferentiableAt ℝ (fun s => g.inner (γ s) (V s) (W s)) t := by
  classical
  -- (1) Eventual equality with the chart-sum at base time `t`.
  have hev := g_inner_eq_chart_sum_along_eventually (I := I) g γ hγ V W t
  -- (2) Differentiability of each chart-sum factor at `t`.
  have hvi : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartFiberCoordAlong (I := I) γ V t i) t := fun i =>
    chartFiberCoordAlong_differentiableAt (I := I) γ V hV t i
  have hwj : ∀ j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartFiberCoordAlong (I := I) γ W t j) t := fun j =>
    chartFiberCoordAlong_differentiableAt (I := I) γ W hW t j
  have hGij : ∀ i j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartGramAlong (I := I) g γ t i j) t := fun i j =>
    chartGramAlong_differentiableAt (I := I) g γ hγ t i j
  -- (3) Differentiability of each triple-product summand.
  have hijsum : ∀ i j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun s => chartFiberCoordAlong (I := I) γ V t i s *
          chartFiberCoordAlong (I := I) γ W t j s *
          chartGramAlong (I := I) g γ t i j s) t := fun i j =>
    ((hvi i).mul (hwj j)).mul (hGij i j)
  -- (4) Differentiability of the inner sum over j.
  have hjsum : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun s => ∑ j : Fin (Module.finrank ℝ E),
          chartFiberCoordAlong (I := I) γ V t i s *
            chartFiberCoordAlong (I := I) γ W t j s *
            chartGramAlong (I := I) g γ t i j s) t := fun i =>
    DifferentiableAt.fun_sum (fun j _ => hijsum i j)
  -- (5) Differentiability of the outer sum over i.
  have hsum : DifferentiableAt ℝ
      (fun s => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartFiberCoordAlong (I := I) γ V t i s *
            chartFiberCoordAlong (I := I) γ W t j s *
            chartGramAlong (I := I) g γ t i j s) t :=
    DifferentiableAt.fun_sum (fun i _ => hjsum i)
  -- (6) Transfer differentiability across the eventual equality.
  exact (hev.differentiableAt_iff).mpr hsum

/-! ## Inner-product preservation along a parallel pair -/

/-- **Inner-product preservation.** If `V` and `W` are parallel along `γ`, then
`g.inner (γ s) (V s) (W s)` is independent of `s`. -/
theorem isParallelAlong_inner_const
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)}
    {hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ}
    {hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))}
    {hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M))}
    (hVp : IsParallelAlong (I := I) g γ V hγ hV)
    (hWp : IsParallelAlong (I := I) g γ W hγ hW) (t₀ t₁ : ℝ) :
    g.inner (γ t₀) (V t₀) (W t₀) = g.inner (γ t₁) (V t₁) (W t₁) := by
  classical
  -- (1) Globally differentiable inner-product function.
  have hdiff : Differentiable ℝ (fun s => g.inner (γ s) (V s) (W s)) := by
    intro t
    exact g_inner_along_differentiableAt (I := I) g V W hγ hV hW t
  -- (2) Derivative vanishes pointwise via metric compatibility.
  have hderiv_zero : ∀ t, deriv (fun s => g.inner (γ s) (V s) (W s)) t = 0 := by
    intro t
    have hmc := covDerivAlong_metric_compatibility (I := I) g hγ hV hW t
    rw [hmc, hVp t, hWp t]
    -- Goal: `g.inner (γ t) 0 (W t) + g.inner (γ t) (V t) 0 = 0`.
    simp
  -- (3) Apply Mathlib's constancy theorem on ℝ.
  exact is_const_of_deriv_eq_zero hdiff hderiv_zero t₀ t₁

/-- **Norm preservation.** If `V` is parallel along `γ`, then
`g.inner (γ s) (V s) (V s)` is independent of `s`. -/
theorem IsParallelAlong.norm_const
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {V : ∀ t, TangentSpace I (γ t)}
    {hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ}
    {hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))}
    (hVp : IsParallelAlong (I := I) g γ V hγ hV) (t₀ t₁ : ℝ) :
    g.inner (γ t₀) (V t₀) (V t₀) = g.inner (γ t₁) (V t₁) (V t₁) :=
  isParallelAlong_inner_const (I := I) hVp hVp t₀ t₁

/-! ## Linear-combination closure of parallel fields

The covariant derivative `covDerivAlong` is additive in the vector-field
slot and ℝ-linear under multiplication by a constant scalar. The third
hypothesis that `covDerivAlong_add` and `covDerivAlong_smul_const`
require — smoothness of the combined lift `fun t => ⟨γ t, …⟩` into the
tangent bundle — is constructed locally via the trivialisation at
`γ t₀`. -/

/-- Smoothness of the tangent-bundle lift of the pointwise sum
`fun t => V t + W t` along `γ`, given smoothness of each summand's
lift and `C¹` smoothness of the base curve. -/
lemma contMDiff_tangentBundle_along_add
    (γ : ℝ → M) (V W : ∀ t, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
      (fun t => (⟨γ t, V t + W t⟩ : TangentBundle I M)) := by
  classical
  intro t
  -- We apply the trivialisation `iff` at `α := γ t`. The lift hits
  -- the trivialisation source at `t` since `γ t ∈ chart source`.
  set α := γ t with hα
  have hin_src : (fun s => (⟨γ s, V s + W s⟩ : TangentBundle I M)) t ∈
      (trivializationAt E (TangentSpace I) α).source := by
    rw [Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (γ t)
  have hiff :=
    (trivializationAt E (TangentSpace I) α).contMDiffAt_iff
      (IM := 𝓘(ℝ, ℝ)) (IB := I) (n := (1 : WithTop ℕ∞))
      (f := fun s => (⟨γ s, V s + W s⟩ : TangentBundle I M)) hin_src
  refine hiff.mpr ⟨?_, ?_⟩
  · -- Projection: smoothness of `γ` at `t`.
    exact hγ.contMDiffAt
  · -- Snd: smoothness of the chart-fibre sum at `t`.
    -- (s ↦ snd_trivAt α ⟨γ s, V s + W s⟩) = chartFiberAlong γ (V+W) t.
    have hV_chart : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
        (chartFiberAlong (I := I) γ V t) t :=
      chartFiberAlong_contMDiffAt (I := I) γ V hV t
    have hW_chart : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
        (chartFiberAlong (I := I) γ W t) t :=
      chartFiberAlong_contMDiffAt (I := I) γ W hW t
    have hsum : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
        (fun s => chartFiberAlong (I := I) γ V t s +
          chartFiberAlong (I := I) γ W t s) t :=
      hV_chart.add hW_chart
    -- Transfer along the eventual equality of `chartFiberAlong`.
    -- `hev : chartFiberAlong γ (V+W) t =ᶠ[𝓝 t] (V_α + W_α)`. The trivialisation's
    -- snd component on `⟨γ s, V s + W s⟩` is definitionally `chartFiberAlong γ (V+W) t s`.
    have hev := chartFiberAlong_add_eventually (I := I) γ hγ V W t
    exact hsum.congr_of_eventuallyEq hev

/-- Smoothness of the tangent-bundle lift of the constant-scalar multiple
`fun t => c • V t` along `γ`, given smoothness of the original lift
and `C¹` smoothness of the base curve. -/
lemma contMDiff_tangentBundle_along_smul
    (γ : ℝ → M) (c : ℝ) (V : ∀ t, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
      (fun t => (⟨γ t, c • V t⟩ : TangentBundle I M)) := by
  classical
  intro t
  set α := γ t with hα
  have hin_src : (fun s => (⟨γ s, c • V s⟩ : TangentBundle I M)) t ∈
      (trivializationAt E (TangentSpace I) α).source := by
    rw [Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (γ t)
  have hiff :=
    (trivializationAt E (TangentSpace I) α).contMDiffAt_iff
      (IM := 𝓘(ℝ, ℝ)) (IB := I) (n := (1 : WithTop ℕ∞))
      (f := fun s => (⟨γ s, c • V s⟩ : TangentBundle I M)) hin_src
  refine hiff.mpr ⟨?_, ?_⟩
  · exact hγ.contMDiffAt
  · have hV_chart : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
        (chartFiberAlong (I := I) γ V t) t :=
      chartFiberAlong_contMDiffAt (I := I) γ V hV t
    -- Constant-scalar multiplication preserves manifold smoothness.
    have hsmul : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
        (fun s => c • chartFiberAlong (I := I) γ V t s) t :=
      contMDiffAt_const.smul hV_chart
    have hev := chartFiberAlong_smul_const_eventually (I := I) γ hγ c V t
    exact hsmul.congr_of_eventuallyEq hev

/-! ## Sum and scalar-multiple of parallel fields -/

/-- **Sum of parallel fields is parallel.** -/
theorem IsParallelAlong.add
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)}
    {hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ}
    {hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))}
    {hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M))}
    (hVp : IsParallelAlong (I := I) g γ V hγ hV)
    (hWp : IsParallelAlong (I := I) g γ W hγ hW) :
    IsParallelAlong (I := I) g γ (fun t => V t + W t) hγ
      (contMDiff_tangentBundle_along_add (I := I) γ V W hγ hV hW) := by
  intro t
  -- Additivity of `covDerivAlong` in `V`; both summands are zero by
  -- hypothesis, hence the sum is zero.
  rw [covDerivAlong_add (I := I) V W hγ hV hW
    (contMDiff_tangentBundle_along_add (I := I) γ V W hγ hV hW) t,
    hVp t, hWp t, add_zero]

/-- **Scalar multiple of a parallel field is parallel.** -/
theorem IsParallelAlong.smul
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {V : ∀ t, TangentSpace I (γ t)}
    {hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ}
    {hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))}
    (c : ℝ) (hVp : IsParallelAlong (I := I) g γ V hγ hV) :
    IsParallelAlong (I := I) g γ (fun t => c • V t) hγ
      (contMDiff_tangentBundle_along_smul (I := I) γ c V hγ hV) := by
  intro t
  -- ℝ-linearity of `covDerivAlong` in `V`; the inner term is zero by
  -- hypothesis, so the scalar multiple is `c • 0 = 0`.
  rw [covDerivAlong_smul_const (I := I) c V hγ hV
    (contMDiff_tangentBundle_along_smul (I := I) γ c V hγ hV) t,
    hVp t, smul_zero]

/-- Smoothness of the tangent-bundle lift of the pointwise negation
`fun t => -V t` along `γ`, given smoothness of the original lift and
`C¹` smoothness of the base curve. Reduced to `_smul` with scalar `-1`. -/
lemma contMDiff_tangentBundle_along_neg
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
      (fun t => (⟨γ t, -V t⟩ : TangentBundle I M)) := by
  have h := contMDiff_tangentBundle_along_smul (I := I) γ (-1 : ℝ) V hγ hV
  have hfun : (fun t => (⟨γ t, (-1 : ℝ) • V t⟩ : TangentBundle I M)) =
      (fun t => (⟨γ t, -V t⟩ : TangentBundle I M)) := by
    funext s; congr 1; exact neg_one_smul ℝ (V s)
  exact hfun ▸ h

/-- Smoothness of the tangent-bundle lift of the pointwise difference
`fun t => V t - W t` along `γ`, given smoothness of each operand's lift
and `C¹` smoothness of the base curve. Reduced to `_add` + `_neg`. -/
lemma contMDiff_tangentBundle_along_sub
    (γ : ℝ → M) (V W : ∀ t, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
      (fun t => (⟨γ t, V t - W t⟩ : TangentBundle I M)) := by
  have hnegW := contMDiff_tangentBundle_along_neg (I := I) γ W hγ hW
  have h := contMDiff_tangentBundle_along_add (I := I) γ V (fun t => -W t) hγ hV hnegW
  have hfun : (fun t => (⟨γ t, V t + -W t⟩ : TangentBundle I M)) =
      (fun t => (⟨γ t, V t - W t⟩ : TangentBundle I M)) := by
    funext s; congr 1; exact (sub_eq_add_neg (V s) (W s)).symm
  exact hfun ▸ h

/-- **Negation of a parallel field is parallel.** Thin wrapper over
`IsParallelAlong.smul` with scalar `-1`. -/
theorem IsParallelAlong.neg
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {V : ∀ t, TangentSpace I (γ t)}
    {hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ}
    {hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))}
    (hVp : IsParallelAlong (I := I) g γ V hγ hV) :
    IsParallelAlong (I := I) g γ (fun t => -V t) hγ
      (contMDiff_tangentBundle_along_neg (I := I) γ V hγ hV) := by
  -- Reduce `fun t => -V t` to `fun t => (-1 : ℝ) • V t` via `funext` + `neg_one_smul`,
  -- then transport `IsParallelAlong … ((-1) • V) …` across this equality.
  -- The smoothness witness's type depends on the vector field, so we transport
  -- the entire predicate as a single dependent expression.
  have hsmul : IsParallelAlong (I := I) g γ (fun t => (-1 : ℝ) • V t) hγ
      (contMDiff_tangentBundle_along_smul (I := I) γ (-1 : ℝ) V hγ hV) :=
    hVp.smul (-1 : ℝ)
  -- Functional equality of the two vector-field shapes.
  have hfield : (fun t => (-1 : ℝ) • V t) = (fun t => -V t) := by
    funext s; exact neg_one_smul ℝ (V s)
  -- Transport `hsmul` across `hfield`. Since `IsParallelAlong` takes the field
  -- and its smoothness witness as separate arguments (with the witness type
  -- depending on the field), we use `subst`/`Eq.mpr` after generalizing the
  -- witness as a free parameter.
  -- Establish the generalized form first.
  have generalized : ∀ {W : ∀ t, TangentSpace I (γ t)}
      (hWsmooth : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M))),
      W = (fun t => (-1 : ℝ) • V t) →
      IsParallelAlong (I := I) g γ W hγ hWsmooth := by
    rintro W hWsmooth rfl
    -- Now `hWsmooth : ContMDiff ... (fun t => ⟨γ t, (-1) • V t⟩)`. Use `hsmul`
    -- with proof-irrelevance on the witness.
    exact hsmul
  exact generalized (contMDiff_tangentBundle_along_neg (I := I) γ V hγ hV) hfield.symm

/-- **Difference of parallel fields is parallel.** Thin wrapper over
`IsParallelAlong.add` and `IsParallelAlong.neg`. -/
theorem IsParallelAlong.sub
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)}
    {hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ}
    {hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))}
    {hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M))}
    (hVp : IsParallelAlong (I := I) g γ V hγ hV)
    (hWp : IsParallelAlong (I := I) g γ W hγ hW) :
    IsParallelAlong (I := I) g γ (fun t => V t - W t) hγ
      (contMDiff_tangentBundle_along_sub (I := I) γ V W hγ hV hW) := by
  -- Reduce `fun t => V t - W t` to `fun t => V t + -W t` via `sub_eq_add_neg`,
  -- then transport `IsParallelAlong … (V + -W) …` across this equality.
  have hadd : IsParallelAlong (I := I) g γ (fun t => V t + -W t) hγ
      (contMDiff_tangentBundle_along_add (I := I) γ V (fun t => -W t) hγ hV
        (contMDiff_tangentBundle_along_neg (I := I) γ W hγ hW)) :=
    hVp.add hWp.neg
  have hfield : (fun t => V t + -W t) = (fun t => V t - W t) := by
    funext s; exact (sub_eq_add_neg (V s) (W s)).symm
  have generalized : ∀ {F : ∀ t, TangentSpace I (γ t)}
      (hFsmooth : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, F t⟩ : TangentBundle I M))),
      F = (fun t => V t + -W t) →
      IsParallelAlong (I := I) g γ F hγ hFsmooth := by
    rintro F hFsmooth rfl
    exact hadd
  exact generalized (contMDiff_tangentBundle_along_sub (I := I) γ V W hγ hV hW)
    hfield.symm

/-! ## Inner product with an arbitrary smooth vector field along `γ`

If `V` is parallel along `γ`, then for any smooth (possibly non-parallel)
field `Z` along `γ`, the inner product `g(V s, Z s)` has derivative
`g(V s, ∇Z s)` — purely the `Z`-side covariant derivative. Hence if
moreover `Z` is parallel, the inner product is constant. -/

/-- Derivative of the inner product `s ↦ g(γ s)(V s, Z s)` reduces to a
single covariant-derivative term when `V` is parallel along `γ`. -/
theorem IsParallelAlong.deriv_inner
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {V Z : ∀ t, TangentSpace I (γ t)}
    {hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ}
    {hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))}
    {hZ : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, Z t⟩ : TangentBundle I M))}
    (hVp : IsParallelAlong (I := I) g γ V hγ hV) (t : ℝ) :
    deriv (fun s => g.inner (γ s) (V s) (Z s)) t =
      g.inner (γ t) (V t) (covDerivAlong (I := I) g γ Z hγ hZ t) := by
  classical
  have hmc :=
    covDerivAlong_metric_compatibility (I := I) g hγ hV hZ t
  -- The metric-compatibility identity expands the derivative into a
  -- two-term sum; the first term vanishes since `V` is parallel.
  rw [hmc, hVp t]
  simp

/-- **Inner-product preservation with a non-parallel field.** If `V` is
parallel along `γ`, then for any smooth field `Z`, the inner product
`g(V, Z)` differs from `g(V, Z₀)` only through the integrated covariant
derivative of `Z`. Stated as a *pointwise vanishing condition*: at any
time `t` where `Z` is `∇`-parallel, the derivative of `g(V, Z)` is
zero. -/
theorem IsParallelAlong.deriv_inner_eq_zero_of_parallel
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {V Z : ∀ t, TangentSpace I (γ t)}
    {hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ}
    {hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))}
    {hZ : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, Z t⟩ : TangentBundle I M))}
    (hVp : IsParallelAlong (I := I) g γ V hγ hV)
    (hZp : IsParallelAlong (I := I) g γ Z hγ hZ) (t : ℝ) :
    deriv (fun s => g.inner (γ s) (V s) (Z s)) t = 0 := by
  rw [hVp.deriv_inner (hZ := hZ) t, hZp t]
  simp

end ParallelTransport
end Riemannian
end Geometry

end
