import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal
import DifferentialGeometry.Integral.Connection.MetricCompatible

/-!
# Metric compatibility of the chart-local Levi-Civita covariant derivative

The chart-local Levi-Civita covariant derivative
`chartLeviCivita g α : (Π x : M, TangentSpace I x) →
  (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)`,
defined chart-by-chart at the basepoint `α : M` (see
`LeviCivitaChartLocal.lean`), satisfies the metric-compatibility identity on
its open *good set*:
$$
  \mathrm{d}\bigl(b \mapsto g_b(Y_b, Z_b)\bigr)(x)\,v
    = g_x((\nabla_v Y)_x, Z_x) + g_x(Y_x, (\nabla_v Z)_x).
$$

In Mathlib's notation, with `cov := chartLeviCivita g α`, this reads
$$
  (\mathrm{mfderiv}\,I\,\mathbb{R}\,(b \mapsto g_b(Y_b, Z_b))\,x)\,v
    = g_x(\mathrm{cov}\,Y\,x\,v,\,Z_x) + g_x(Y_x,\,\mathrm{cov}\,Z\,x\,v).
$$

## Proof outline

1. **LHS**: Express `g_b(Y_b, Z_b)` for `b` in a neighborhood of the good-set
   point `x` using `g_inner_eq_chart_sum`. Then use
   `mfderiv_scalar_eq_chart_fderiv` to convert the manifold derivative into a
   Fréchet derivative on the chart target. The resulting object is the Fréchet
   derivative of a sum-of-products of three scalar functions on `E`, evaluated
   on `trivToE α x v`.

2. **RHS**: Expand `cov Y x v` and `cov Z x v` via `chartLeviCivita_apply`.
   Pair each through `g.inner x` against the other section using
   `g_inner_eq_chart_sum`. The result is a sum of two pieces, each involving
   chart Gram entries `G^E_{ij}`, Fréchet derivatives of the chart-pulled-back
   sections, and Christoffel-correction sums.

3. **Match**: Apply `partialDeriv_chartGramOnE_eq_chartChristoffel_sum` to
   substitute `∂_k G_{ij} = ∑_l Γ^l_{ki} G_{lj} + ∑_l Γ^l_{kj} G_{li}` in the
   expanded LHS. After the substitution, the LHS and RHS agree by direct
   algebraic comparison via `Finset.sum_congr`, `Finset.sum_comm`, the chart
   Gram symmetry, and `ring`.

The metric-compatibility property is the second of the two characterising
axioms of the Levi-Civita connection (the first being torsion-freeness, treated
in the sibling file `LeviCivitaChartTorsion.lean`). Together with the
additivity and Leibniz rule axioms verified in `LeviCivitaChartLocal.lean`,
the chart-local construction is shown to be the Levi-Civita connection on the
open good set at `α`.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- The chart-side scalar function `F_{Y,Z}` whose Fréchet derivative encodes
the metric-compatibility identity. -/
def chartInnerOnE (g : SmoothRiemannianMetric I M) (α : M)
    (Y Z : Π x : M, TangentSpace I x) (y : E) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
          (chartE_section_repr (I := I) α Y ((extChartAt I α).symm y))) i *
        ((chartModelBasis E).repr
          (chartE_section_repr (I := I) α Z ((extChartAt I α).symm y))) j *
        chartGramOnE (I := I) g α i j y

/-- Pointwise unfolding of `chartInnerOnE`. -/
@[simp] lemma chartInnerOnE_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (Y Z : Π x : M, TangentSpace I x) (y : E) :
    chartInnerOnE (I := I) g α Y Z y =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr
              (chartE_section_repr (I := I) α Y ((extChartAt I α).symm y))) i *
            ((chartModelBasis E).repr
              (chartE_section_repr (I := I) α Z ((extChartAt I α).symm y))) j *
            chartGramOnE (I := I) g α i j y := rfl

/-- On the chart target, `chartInnerOnE g α Y Z (φ b)` recovers the inner
product `g.inner b (Y b) (Z b)` whenever `b` lies in the chart source and the
trivialization base set. -/
lemma chartInnerOnE_eq_g_inner
    (g : SmoothRiemannianMetric I M) (α : M)
    (Y Z : Π x : M, TangentSpace I x) {b : M}
    (hb_src : b ∈ (extChartAt I α).source)
    (hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartInnerOnE (I := I) g α Y Z (extChartAt I α b) =
      g.inner b (Y b) (Z b) := by
  classical
  unfold chartInnerOnE
  have hb_inv : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_src
  have hG : ∀ i j : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i j (extChartAt I α b) =
        chartGramMatrix (I := I) g α b i j := by
    intro i j
    unfold chartGramOnE
    rw [hb_inv]
  have hYrepr : chartE_section_repr (I := I) α Y
      ((extChartAt I α).symm (extChartAt I α b)) =
        chartE_section_repr (I := I) α Y b := by rw [hb_inv]
  have hZrepr : chartE_section_repr (I := I) α Z
      ((extChartAt I α).symm (extChartAt I α b)) =
        chartE_section_repr (I := I) α Z b := by rw [hb_inv]
  rw [g_inner_eq_chart_sum (I := I) g α hb_base hb_src (Y b) (Z b)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hYrepr, hZrepr]
  rw [hG i j]
  rfl

/-- The component-extraction map: composing a differentiable function with the
linear functional `b.coord i` preserves differentiability. -/
private lemma differentiableAt_repr_comp
    {f : E → E} {y : E} (hf : DifferentiableAt ℝ f y)
    (i : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (fun y => ((chartModelBasis E).repr (f y)) i) y := by
  classical
  set ci : E →L[ℝ] ℝ := ((chartModelBasis E).coord i).toContinuousLinearMap
  have hclm : DifferentiableAt ℝ ci (f y) := ci.differentiableAt
  exact hclm.comp y hf

/-- `chartGramOnE g α i j` is differentiable at any interior point of the
chart target. -/
lemma chartGramOnE_differentiableAt_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) y := by
  have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (extChartAt I α).target :=
    chartGramOnE_contDiffOn (I := I) g α i j
  have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (interior (extChartAt I α).target) :=
    hcd.mono interior_subset
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y := hop_int.mem_nhds hy
  exact (hcd_int.contDiffAt hy_nhd).differentiableAt (by simp)

/-- `b ↦ g.inner b (Y b) (Z b)` is `EventuallyEq` to
`chartInnerOnE g α Y Z ∘ extChartAt I α` on a neighborhood of any good-set
point. -/
private lemma chartInnerOnE_eventuallyEq
    (g : SmoothRiemannianMetric I M) (α : M)
    (Y Z : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (fun b => g.inner b (Y b) (Z b))
      =ᶠ[𝓝 x]
      (chartInnerOnE (I := I) g α Y Z ∘ extChartAt I α) := by
  have hopen : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  have hnhds : chartLeviCivitaGoodSet (I := I) α ∈ 𝓝 x := hopen.mem_nhds hx
  filter_upwards [hnhds] with b hb
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  exact (chartInnerOnE_eq_g_inner (I := I) g α Y Z hb_src hb_base).symm

/-- The `i`-th component of the chart-pulled-back section. -/
private def chartReprComp
    (α : M) (Y : Π x : M, TangentSpace I x)
    (i : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ((chartModelBasis E).repr
      (chartE_section_repr (I := I) α Y ((extChartAt I α).symm y))) i

@[simp] private lemma chartReprComp_apply
    (α : M) (Y : Π x : M, TangentSpace I x)
    (i : Fin (Module.finrank ℝ E)) (y : E) :
    chartReprComp (I := I) α Y i y =
      ((chartModelBasis E).repr
          (chartE_section_repr (I := I) α Y ((extChartAt I α).symm y))) i := rfl

/-- The component function `chartReprComp α Y i` is differentiable at `φ x`
when the section `Y` is differentiable at `x` and `x` is in the good set. -/
private lemma chartReprComp_differentiableAt
    (α : M) (Y : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hY : MDiffAt (T% Y) x)
    (i : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (chartReprComp (I := I) α Y i) (extChartAt I α x) := by
  classical
  have hY_pull : DifferentiableAt ℝ
      (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
      (extChartAt I α x) :=
    differentiableAt_chartE_pullback_of_MDiff (I := I) α hx hY
  exact differentiableAt_repr_comp hY_pull i

/-- Fréchet derivative formula for `chartReprComp α Y i`: it is the `i`-th
component (under `b.repr`) of the Fréchet derivative of the chart-pullback,
WHEN the chart-pullback is differentiable at `extChartAt I α x`. -/
private lemma chartReprComp_fderiv_apply
    (α : M) (Y : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hY : MDiffAt (T% Y) x)
    (i : Fin (Module.finrank ℝ E)) (w : E) :
    fderiv ℝ (chartReprComp (I := I) α Y i) (extChartAt I α x) w =
      ((chartModelBasis E).repr
          (fderiv ℝ (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
            (extChartAt I α x) w)) i := by
  classical
  set fE : E → E := chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm
  set ci : E →L[ℝ] ℝ := ((chartModelBasis E).coord i).toContinuousLinearMap
  have hfun : chartReprComp (I := I) α Y i = ci ∘ fE := rfl
  have hfE_diff : DifferentiableAt ℝ fE (extChartAt I α x) :=
    differentiableAt_chartE_pullback_of_MDiff (I := I) α hx hY
  have hci_diff : DifferentiableAt ℝ ci (fE (extChartAt I α x)) := ci.differentiableAt
  have hcomp : fderiv ℝ (ci ∘ fE) (extChartAt I α x) =
      (fderiv ℝ ci (fE (extChartAt I α x))).comp (fderiv ℝ fE (extChartAt I α x)) :=
    fderiv_comp (extChartAt I α x) hci_diff hfE_diff
  have hci_fderiv : fderiv ℝ ci (fE (extChartAt I α x)) = ci :=
    ContinuousLinearMap.fderiv ci
  rw [hfun, hcomp, hci_fderiv]
  rfl

/-- Each three-fold product `chartReprComp α Y i · chartReprComp α Z j · G^E_{ij}`
is differentiable at `φ x`. -/
private lemma chartInnerOnE_summand_differentiableAt
    (g : SmoothRiemannianMetric I M) (α : M)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (i j : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (fun y => chartReprComp (I := I) α Y i y *
                  chartReprComp (I := I) α Z j y *
                  chartGramOnE (I := I) g α i j y) (extChartAt I α x) := by
  have hYi : DifferentiableAt ℝ (chartReprComp (I := I) α Y i)
      (extChartAt I α x) :=
    chartReprComp_differentiableAt (I := I) α Y hx hY i
  have hZj : DifferentiableAt ℝ (chartReprComp (I := I) α Z j)
      (extChartAt I α x) :=
    chartReprComp_differentiableAt (I := I) α Z hx hZ j
  have hG : DifferentiableAt ℝ (chartGramOnE (I := I) g α i j)
      (extChartAt I α x) :=
    chartGramOnE_differentiableAt_int (I := I) g α i j
      (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx)
  exact (hYi.mul hZj).mul hG

/-- The full `chartInnerOnE g α Y Z` function is differentiable at `φ x`. -/
private lemma chartInnerOnE_differentiableAt
    (g : SmoothRiemannianMetric I M) (α : M)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    DifferentiableAt ℝ (chartInnerOnE (I := I) g α Y Z) (extChartAt I α x) := by
  classical
  unfold chartInnerOnE
  apply DifferentiableAt.fun_sum
  intro i _
  apply DifferentiableAt.fun_sum
  intro j _
  exact chartInnerOnE_summand_differentiableAt (I := I) g α hx hY hZ i j

/-- Fréchet derivative formula for the three-fold-product summand. -/
private lemma chartInnerOnE_summand_fderiv_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (i j : Fin (Module.finrank ℝ E)) (w : E) :
    fderiv ℝ
        (fun y => chartReprComp (I := I) α Y i y *
                    chartReprComp (I := I) α Z j y *
                    chartGramOnE (I := I) g α i j y)
        (extChartAt I α x) w =
      fderiv ℝ (chartReprComp (I := I) α Y i) (extChartAt I α x) w *
          chartReprComp (I := I) α Z j (extChartAt I α x) *
          chartGramOnE (I := I) g α i j (extChartAt I α x) +
        chartReprComp (I := I) α Y i (extChartAt I α x) *
          fderiv ℝ (chartReprComp (I := I) α Z j) (extChartAt I α x) w *
          chartGramOnE (I := I) g α i j (extChartAt I α x) +
        chartReprComp (I := I) α Y i (extChartAt I α x) *
          chartReprComp (I := I) α Z j (extChartAt I α x) *
          fderiv ℝ (chartGramOnE (I := I) g α i j) (extChartAt I α x) w := by
  classical
  have hYi : DifferentiableAt ℝ (chartReprComp (I := I) α Y i)
      (extChartAt I α x) :=
    chartReprComp_differentiableAt (I := I) α Y hx hY i
  have hZj : DifferentiableAt ℝ (chartReprComp (I := I) α Z j)
      (extChartAt I α x) :=
    chartReprComp_differentiableAt (I := I) α Z hx hZ j
  have hG : DifferentiableAt ℝ (chartGramOnE (I := I) g α i j)
      (extChartAt I α x) :=
    chartGramOnE_differentiableAt_int (I := I) g α i j
      (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx)
  set y₀ : E := extChartAt I α x
  set u : E → ℝ := chartReprComp (I := I) α Y i
  set v : E → ℝ := chartReprComp (I := I) α Z j
  set ggij : E → ℝ := chartGramOnE (I := I) g α i j
  have huv : DifferentiableAt ℝ (fun y => u y * v y) y₀ := hYi.mul hZj
  have hfd_uv_g :
      fderiv ℝ (fun y => (u y * v y) * ggij y) y₀ =
        (u y₀ * v y₀) • fderiv ℝ ggij y₀ +
          (ggij y₀) • fderiv ℝ (fun y => u y * v y) y₀ :=
    fderiv_fun_mul huv hG
  have hfd_uv :
      fderiv ℝ (fun y => u y * v y) y₀ =
        (u y₀) • fderiv ℝ v y₀ + (v y₀) • fderiv ℝ u y₀ :=
    fderiv_fun_mul hYi hZj
  rw [show (fun y : E => chartReprComp (I := I) α Y i y *
                  chartReprComp (I := I) α Z j y *
                  chartGramOnE (I := I) g α i j y) =
      (fun y : E => (u y * v y) * ggij y) from rfl]
  rw [hfd_uv_g]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply]
  rw [hfd_uv]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply]
  simp only [smul_eq_mul]
  ring

/-- Fréchet derivative formula for the full `chartInnerOnE`. -/
private lemma chartInnerOnE_fderiv_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (w : E) :
    fderiv ℝ (chartInnerOnE (I := I) g α Y Z) (extChartAt I α x) w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (chartReprComp (I := I) α Y i) (extChartAt I α x) w *
              chartReprComp (I := I) α Z j (extChartAt I α x) *
              chartGramOnE (I := I) g α i j (extChartAt I α x) +
            chartReprComp (I := I) α Y i (extChartAt I α x) *
              fderiv ℝ (chartReprComp (I := I) α Z j) (extChartAt I α x) w *
              chartGramOnE (I := I) g α i j (extChartAt I α x) +
            chartReprComp (I := I) α Y i (extChartAt I α x) *
              chartReprComp (I := I) α Z j (extChartAt I α x) *
              fderiv ℝ (chartGramOnE (I := I) g α i j) (extChartAt I α x) w) := by
  classical
  have hF_eq : chartInnerOnE (I := I) g α Y Z =
      (fun y => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartReprComp (I := I) α Y i y *
            chartReprComp (I := I) α Z j y *
              chartGramOnE (I := I) g α i j y) := by
    funext y
    unfold chartInnerOnE chartReprComp
    rfl
  rw [hF_eq]
  rw [fderiv_fun_sum (fun i _ => by
    apply DifferentiableAt.fun_sum
    intro j _
    exact chartInnerOnE_summand_differentiableAt (I := I) g α hx hY hZ i j)]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [fderiv_fun_sum (fun j _ =>
    chartInnerOnE_summand_differentiableAt (I := I) g α hx hY hZ i j)]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact chartInnerOnE_summand_fderiv_apply (I := I) g α hx hY hZ i j w

/-- The manifold derivative of `b ↦ g.inner b (Y b) (Z b)` at a good-set point
`x`, applied to a tangent vector `v`, equals the Fréchet derivative of
`chartInnerOnE g α Y Z` at `φ x` applied to `trivToE α x v`. -/
private lemma mfderiv_g_inner_eq_chartInnerOnE_fderiv
    (g : SmoothRiemannianMetric I M) (α : M)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) v =
      fderiv ℝ (chartInnerOnE (I := I) g α Y Z) (extChartAt I α x)
        (trivToE (I := I) α x v) := by
  classical
  have hev := chartInnerOnE_eventuallyEq (I := I) g α Y Z hx
  rw [Filter.EventuallyEq.mfderiv_eq hev]
  have hx_src_chart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  have hcomp_at : MDiffAt (chartInnerOnE (I := I) g α Y Z ∘ extChartAt I α) x := by
    have hF_at : DifferentiableAt ℝ (chartInnerOnE (I := I) g α Y Z)
        (extChartAt I α x) :=
      chartInnerOnE_differentiableAt (I := I) g α hx hY hZ
    have hF_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
        (chartInnerOnE (I := I) g α Y Z) (extChartAt I α x) :=
      hF_at.mdifferentiableAt
    have hφ_mdiff : MDiffAt (extChartAt I α) x :=
      mdifferentiableAt_extChartAt (I := I) (x := α) hx_src_chart
    exact hF_mdiff.comp x hφ_mdiff
  have hmf_to_fderiv :
      (mfderiv I 𝓘(ℝ) (chartInnerOnE (I := I) g α Y Z ∘ extChartAt I α) x) v =
        fderiv ℝ
          ((chartInnerOnE (I := I) g α Y Z ∘ extChartAt I α) ∘
            (extChartAt I α).symm) (extChartAt I α x)
          (trivToE (I := I) α x v) :=
    mfderiv_scalar_eq_chart_fderiv (I := I) α
      (chartInnerOnE (I := I) g α Y Z ∘ extChartAt I α)
      hx_src_chart hx_int hcomp_at v
  refine hmf_to_fderiv.trans ?_
  have hev_pull :
      ((chartInnerOnE (I := I) g α Y Z ∘ extChartAt I α) ∘
        (extChartAt I α).symm) =ᶠ[𝓝 (extChartAt I α x)]
        chartInnerOnE (I := I) g α Y Z := by
    have htgt_open : IsOpen (interior ((extChartAt I α).target : Set E)) :=
      isOpen_interior
    have hnhds : interior ((extChartAt I α).target : Set E) ∈ 𝓝 (extChartAt I α x) :=
      htgt_open.mem_nhds hx_int
    filter_upwards [hnhds] with y hy
    have hy_tgt : y ∈ (extChartAt I α).target := interior_subset hy
    change chartInnerOnE (I := I) g α Y Z (extChartAt I α ((extChartAt I α).symm y)) =
      chartInnerOnE (I := I) g α Y Z y
    rw [(extChartAt I α).right_inv hy_tgt]
  rw [Filter.EventuallyEq.fderiv_eq hev_pull]

/-- The directional derivative of `chartGramOnE g α i j` along `w` equals the
basis expansion of `w` weighted by the partial derivatives. -/
private lemma fderiv_chartGramOnE_apply_eq_partialDeriv_sum
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {y₀ : E} (_hy₀ : y₀ ∈ interior (extChartAt I α).target) (w : E) :
    fderiv ℝ (chartGramOnE (I := I) g α i j) y₀ w =
      ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr w) k *
          partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y₀ := by
  classical
  have hw_decomp : w =
      ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr w) k • (chartModelBasis E) k :=
    (Module.Basis.sum_repr (chartModelBasis E) w).symm
  rw [show (fderiv ℝ (chartGramOnE (I := I) g α i j) y₀) w =
        (fderiv ℝ (chartGramOnE (I := I) g α i j) y₀)
          (∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr w) k • (chartModelBasis E) k) from by
    rw [← hw_decomp]]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul]
  rfl

/-- The `i`-th component of `christoffelCorrection α x Y v` under
`(chartModelBasis E).repr`. -/
private lemma christoffelCorrection_repr_apply
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) (Y : E)
    (v : TangentSpace I x) (i : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).repr
        (christoffelCorrection (I := I) g α x Y v)) i =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (trivToE (I := I) α x v)) k *
            ((chartModelBasis E).repr Y) l *
            chartChristoffel (I := I) g α k l i (extChartAt I α x) := by
  classical
  rw [christoffelCorrection_apply]
  rw [map_sum]
  rw [Finset.sum_apply']
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_sum]
  rw [Finset.sum_apply']
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_sum]
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single i]
  · rw [map_smul]
    rw [Finsupp.smul_apply]
    rw [Module.Basis.repr_self_apply]
    rw [if_pos rfl]
    rw [smul_eq_mul, mul_one]
  · intro c _ hci
    rw [map_smul]
    rw [Finsupp.smul_apply]
    rw [Module.Basis.repr_self_apply]
    rw [if_neg hci]
    simp
  · intro habs
    exact absurd (Finset.mem_univ i) habs

/-- The fully expanded LHS as a sum involving Fréchet derivatives, chart Gram
entries, and the `chartChristoffel` symbols (the latter via the chart metric
identity `partialDeriv_chartGramOnE_eq_chartChristoffel_sum`). -/
private lemma mfderiv_g_inner_chart_expand
    (g : SmoothRiemannianMetric I M) (α : M)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) v =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (((chartModelBasis E).repr
              (fderiv ℝ
                (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
                (extChartAt I α x) (trivToE (I := I) α x v))) i *
              ((chartModelBasis E).repr
                (chartE_section_repr (I := I) α Z x)) j *
              chartGramOnE (I := I) g α i j (extChartAt I α x) +
            ((chartModelBasis E).repr
              (chartE_section_repr (I := I) α Y x)) i *
              ((chartModelBasis E).repr
                (fderiv ℝ
                  (chartE_section_repr (I := I) α Z ∘ (extChartAt I α).symm)
                  (extChartAt I α x) (trivToE (I := I) α x v))) j *
              chartGramOnE (I := I) g α i j (extChartAt I α x) +
            ((chartModelBasis E).repr
              (chartE_section_repr (I := I) α Y x)) i *
              ((chartModelBasis E).repr
                (chartE_section_repr (I := I) α Z x)) j *
              (∑ k : Fin (Module.finrank ℝ E),
                ((chartModelBasis E).repr (trivToE (I := I) α x v)) k *
                  ((∑ l : Fin (Module.finrank ℝ E),
                      chartChristoffel (I := I) g α k i l (extChartAt I α x) *
                        chartGramOnE (I := I) g α l j (extChartAt I α x)) +
                  (∑ l : Fin (Module.finrank ℝ E),
                      chartChristoffel (I := I) g α k j l (extChartAt I α x) *
                        chartGramOnE (I := I) g α l i (extChartAt I α x))))) := by
  classical
  have hx_src : x ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  have hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  rw [mfderiv_g_inner_eq_chartInnerOnE_fderiv (I := I) g α hx hY hZ v]
  rw [chartInnerOnE_fderiv_apply (I := I) g α hx hY hZ
    (trivToE (I := I) α x v)]
  have hxinv : (extChartAt I α).symm (extChartAt I α x) = x :=
    (extChartAt I α).left_inv hx_src
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hreprY : chartReprComp (I := I) α Y i (extChartAt I α x) =
      ((chartModelBasis E).repr
        (chartE_section_repr (I := I) α Y x)) i := by
    unfold chartReprComp; rw [hxinv]
  have hreprZ : chartReprComp (I := I) α Z j (extChartAt I α x) =
      ((chartModelBasis E).repr
        (chartE_section_repr (I := I) α Z x)) j := by
    unfold chartReprComp; rw [hxinv]
  have hfderivY :
      fderiv ℝ (chartReprComp (I := I) α Y i) (extChartAt I α x)
        (trivToE (I := I) α x v) =
      ((chartModelBasis E).repr
          (fderiv ℝ
            (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x v))) i :=
    chartReprComp_fderiv_apply (I := I) α Y hx hY i (trivToE (I := I) α x v)
  have hfderivZ :
      fderiv ℝ (chartReprComp (I := I) α Z j) (extChartAt I α x)
        (trivToE (I := I) α x v) =
      ((chartModelBasis E).repr
          (fderiv ℝ
            (chartE_section_repr (I := I) α Z ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x v))) j :=
    chartReprComp_fderiv_apply (I := I) α Z hx hZ j (trivToE (I := I) α x v)
  rw [hreprY, hreprZ, hfderivY, hfderivZ]
  rw [fderiv_chartGramOnE_apply_eq_partialDeriv_sum (I := I) g α i j hx_int
    (trivToE (I := I) α x v)]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (trivToE (I := I) α x v)) k *
        partialDeriv (E := E) k (chartGramOnE (I := I) g α i j)
          (extChartAt I α x)) =
    ∑ k : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (trivToE (I := I) α x v)) k *
        ((∑ l : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k i l (extChartAt I α x) *
              chartGramOnE (I := I) g α l j (extChartAt I α x)) +
        (∑ l : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k j l (extChartAt I α x) *
              chartGramOnE (I := I) g α l i (extChartAt I α x))) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [partialDeriv_chartGramOnE_eq_chartChristoffel_sum (I := I) g α i j k
      hx_int]]

/-- Expansion of `g.inner x (chartLeviCivita g α Y x v) (Z x)` in chart
coordinates: a Fréchet-derivative piece plus a Christoffel-correction piece,
then weighted by `(b.repr Z x)_j · G^E_{ij}(φ x)` and summed over `i, j`. -/
private lemma g_inner_chartLeviCivita_Y_Z_expand
    (g : SmoothRiemannianMetric I M) (α : M)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) (v : TangentSpace I x) :
    g.inner x (chartLeviCivita (I := I) g α Y x v) (Z x) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ( ((chartModelBasis E).repr
                (fderiv ℝ
                  (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
                  (extChartAt I α x) (trivToE (I := I) α x v))) i +
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ((chartModelBasis E).repr (trivToE (I := I) α x v)) k *
                  ((chartModelBasis E).repr
                    (chartE_section_repr (I := I) α Y x)) l *
                  chartChristoffel (I := I) g α k l i (extChartAt I α x) ) *
            ((chartModelBasis E).repr
                (chartE_section_repr (I := I) α Z x)) j *
            chartGramOnE (I := I) g α i j (extChartAt I α x) := by
  classical
  have hx_src : x ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  rw [g_inner_eq_chart_sum (I := I) g α hx_base hx_src
        (chartLeviCivita (I := I) g α Y x v) (Z x)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hZ_repr :
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x (Z x) =
        chartE_section_repr (I := I) α Z x := rfl
  rw [hZ_repr]
  have hLC_apply :
      chartLeviCivita (I := I) g α Y x v =
        trivFromE (I := I) α x
          (fderiv ℝ
              (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
              (extChartAt I α x) (trivToE (I := I) α x v) +
            christoffelCorrection (I := I) g α x
              (chartE_section_repr (I := I) α Y x) v) :=
    chartLeviCivita_apply (I := I) g α Y hx v
  rw [hLC_apply]
  rw [show (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x
        (trivFromE (I := I) α x
          (fderiv ℝ
              (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
              (extChartAt I α x) (trivToE (I := I) α x v) +
            christoffelCorrection (I := I) g α x
              (chartE_section_repr (I := I) α Y x) v)) =
        (fderiv ℝ
            (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x v) +
          christoffelCorrection (I := I) g α x
            (chartE_section_repr (I := I) α Y x) v) from
    trivToE_trivFromE (I := I) α hx_base _]
  rw [show ((chartModelBasis E).repr
        (fderiv ℝ
          (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
          (extChartAt I α x) (trivToE (I := I) α x v) +
          christoffelCorrection (I := I) g α x
            (chartE_section_repr (I := I) α Y x) v)) i =
      ((chartModelBasis E).repr
            (fderiv ℝ
              (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
              (extChartAt I α x) (trivToE (I := I) α x v))) i +
        ((chartModelBasis E).repr
            (christoffelCorrection (I := I) g α x
              (chartE_section_repr (I := I) α Y x) v)) i from by
    rw [map_add]; rfl]
  rw [christoffelCorrection_repr_apply (I := I) g α x
    (chartE_section_repr (I := I) α Y x) v i]

/-- Expansion of `g.inner x (Y x) (chartLeviCivita g α Z x v)` in chart
coordinates. -/
private lemma g_inner_Y_chartLeviCivita_Z_expand
    (g : SmoothRiemannianMetric I M) (α : M)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) (v : TangentSpace I x) :
    g.inner x (Y x) (chartLeviCivita (I := I) g α Z x v) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr
              (chartE_section_repr (I := I) α Y x)) i *
            ( ((chartModelBasis E).repr
                  (fderiv ℝ
                    (chartE_section_repr (I := I) α Z ∘ (extChartAt I α).symm)
                    (extChartAt I α x) (trivToE (I := I) α x v))) j +
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr (trivToE (I := I) α x v)) k *
                    ((chartModelBasis E).repr
                      (chartE_section_repr (I := I) α Z x)) l *
                    chartChristoffel (I := I) g α k l j (extChartAt I α x) ) *
            chartGramOnE (I := I) g α i j (extChartAt I α x) := by
  classical
  have hx_src : x ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  rw [g_inner_eq_chart_sum (I := I) g α hx_base hx_src
        (Y x) (chartLeviCivita (I := I) g α Z x v)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hY_repr :
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x (Y x) =
        chartE_section_repr (I := I) α Y x := rfl
  rw [hY_repr]
  have hLC_apply :
      chartLeviCivita (I := I) g α Z x v =
        trivFromE (I := I) α x
          (fderiv ℝ
              (chartE_section_repr (I := I) α Z ∘ (extChartAt I α).symm)
              (extChartAt I α x) (trivToE (I := I) α x v) +
            christoffelCorrection (I := I) g α x
              (chartE_section_repr (I := I) α Z x) v) :=
    chartLeviCivita_apply (I := I) g α Z hx v
  rw [hLC_apply]
  rw [show (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x
        (trivFromE (I := I) α x
          (fderiv ℝ
              (chartE_section_repr (I := I) α Z ∘ (extChartAt I α).symm)
              (extChartAt I α x) (trivToE (I := I) α x v) +
            christoffelCorrection (I := I) g α x
              (chartE_section_repr (I := I) α Z x) v)) =
        (fderiv ℝ
            (chartE_section_repr (I := I) α Z ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x v) +
          christoffelCorrection (I := I) g α x
            (chartE_section_repr (I := I) α Z x) v) from
    trivToE_trivFromE (I := I) α hx_base _]
  rw [show ((chartModelBasis E).repr
        (fderiv ℝ
          (chartE_section_repr (I := I) α Z ∘ (extChartAt I α).symm)
          (extChartAt I α x) (trivToE (I := I) α x v) +
          christoffelCorrection (I := I) g α x
            (chartE_section_repr (I := I) α Z x) v)) j =
      ((chartModelBasis E).repr
            (fderiv ℝ
              (chartE_section_repr (I := I) α Z ∘ (extChartAt I α).symm)
              (extChartAt I α x) (trivToE (I := I) α x v))) j +
        ((chartModelBasis E).repr
            (christoffelCorrection (I := I) g α x
              (chartE_section_repr (I := I) α Z x) v)) j from by
    rw [map_add]; rfl]
  rw [christoffelCorrection_repr_apply (I := I) g α x
    (chartE_section_repr (I := I) α Z x) v j]

/-- **Algebraic core of the metric-compatibility match.** The arithmetic
identity needed to close the metric-compatibility theorem after both sides are
expanded in chart coordinates. The variables `B i, D j, w k` are the
basis-extracted components of the relevant chart-trivialised vectors,
`G i j` are the chart Gram entries (symmetric under `i ↔ j`), and `Γ k l i` is
the chart Christoffel symbol. -/
private lemma christoffel_match
    {n : ℕ}
    (B D w : Fin n → ℝ) (G : Fin n → Fin n → ℝ)
    (Γ : Fin n → Fin n → Fin n → ℝ)
    (hGsymm : ∀ i j, G i j = G j i) :
    (∑ i : Fin n, ∑ j : Fin n,
        B i * D j *
          (∑ k : Fin n, w k *
            ((∑ l : Fin n, Γ k i l * G l j) +
            (∑ l : Fin n, Γ k j l * G l i)))) =
      (∑ i : Fin n, ∑ j : Fin n,
        (∑ k : Fin n, ∑ l : Fin n, w k * B l * Γ k l i) * D j * G i j) +
      (∑ i : Fin n, ∑ j : Fin n,
        B i * (∑ k : Fin n, ∑ l : Fin n, w k * D l * Γ k l j) * G i j) := by
  classical
  have hLHS :
      (∑ i : Fin n, ∑ j : Fin n,
          B i * D j *
            (∑ k : Fin n, w k *
              ((∑ l : Fin n, Γ k i l * G l j) +
              (∑ l : Fin n, Γ k j l * G l i)))) =
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            B i * D j * w k * Γ k i l * G l j) +
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            B i * D j * w k * Γ k j l * G l i) := by
    rw [show
      (∑ i : Fin n, ∑ j : Fin n,
          B i * D j *
            (∑ k : Fin n, w k *
              ((∑ l : Fin n, Γ k i l * G l j) +
              (∑ l : Fin n, Γ k j l * G l i)))) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          B i * D j * w k *
              ((∑ l : Fin n, Γ k i l * G l j) +
              (∑ l : Fin n, Γ k j l * G l i))) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring]
    rw [show
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          B i * D j * w k *
              ((∑ l : Fin n, Γ k i l * G l j) +
              (∑ l : Fin n, Γ k j l * G l i))) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (B i * D j * w k * (∑ l : Fin n, Γ k i l * G l j) +
            B i * D j * w k * (∑ l : Fin n, Γ k j l * G l i))) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [mul_add]]
    have hdistr1 :
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            B i * D j * w k * (∑ l : Fin n, Γ k i l * G l j)) =
          (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
              B i * D j * w k * Γ k i l * G l j) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    have hdistr2 :
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            B i * D j * w k * (∑ l : Fin n, Γ k j l * G l i)) =
          (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
              B i * D j * w k * Γ k j l * G l i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    rw [show
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (B i * D j * w k * (∑ l : Fin n, Γ k i l * G l j) +
            B i * D j * w k * (∑ l : Fin n, Γ k j l * G l i))) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          B i * D j * w k * (∑ l : Fin n, Γ k i l * G l j)) +
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          B i * D j * w k * (∑ l : Fin n, Γ k j l * G l i)) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_add_distrib]]
    rw [hdistr1, hdistr2]
  rw [hLHS]
  have hRHS_Y :
      (∑ i : Fin n, ∑ j : Fin n,
          (∑ k : Fin n, ∑ l : Fin n, w k * B l * Γ k l i) * D j * G i j) =
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            (w k * B l * Γ k l i) * D j * G i j) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul, Finset.sum_mul]
  have hRHS_Z :
      (∑ i : Fin n, ∑ j : Fin n,
          B i * (∑ k : Fin n, ∑ l : Fin n, w k * D l * Γ k l j) * G i j) =
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            B i * (w k * D l * Γ k l j) * G i j) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hRHS_Y, hRHS_Z]
  have hMatch_Y :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          B i * D j * w k * Γ k i l * G l j) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          (w k * B l * Γ k l i) * D j * G i j) := by
    rw [show
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          B i * D j * w k * Γ k i l * G l j) =
      (∑ i : Fin n, ∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          B i * D j * w k * Γ k i l * G l j) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show (∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
              B i * D j * w k * Γ k i l * G l j) =
            (∑ j : Fin n, ∑ l : Fin n, ∑ k : Fin n,
              B i * D j * w k * Γ k i l * G l j) from by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        exact Finset.sum_comm]
      exact Finset.sum_comm]
    rw [show
      (∑ i : Fin n, ∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          B i * D j * w k * Γ k i l * G l j) =
      (∑ i : Fin n, ∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          B l * D j * w k * Γ k l i * G i j) from
      Finset.sum_comm]
    rw [show
      (∑ i : Fin n, ∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          B l * D j * w k * Γ k l i * G i j) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          B l * D j * w k * Γ k l i * G i j) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show (∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n,
              B l * D j * w k * Γ k l i * G i j) =
            (∑ j : Fin n, ∑ l : Fin n, ∑ k : Fin n,
              B l * D j * w k * Γ k l i * G i j) from
          Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  have hMatch_Z :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          B i * D j * w k * Γ k j l * G l i) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          B i * (w k * D l * Γ k l j) * G i j) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
              B i * D j * w k * Γ k j l * G l i) =
          (∑ j : Fin n, ∑ l : Fin n, ∑ k : Fin n,
              B i * D j * w k * Γ k j l * G l i) from by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact Finset.sum_comm]
    rw [show (∑ j : Fin n, ∑ l : Fin n, ∑ k : Fin n,
              B i * D j * w k * Γ k j l * G l i) =
          (∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n,
              B i * D j * w k * Γ k j l * G l i) from
        Finset.sum_comm]
    rw [show
      (∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          B i * D j * w k * Γ k j l * G l i) =
      (∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          B i * D l * w k * Γ k l j * G j i) from
      Finset.sum_comm]
    rw [show
      (∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          B i * D l * w k * Γ k l j * G j i) =
      (∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          B i * D l * w k * Γ k l j * G j i) from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hGsymm j i]
    ring
  rw [hMatch_Y, hMatch_Z]

/-- **Metric compatibility of the chart-local Levi-Civita.** On the open good
set at `α`, the chart-local Levi-Civita covariant derivative `chartLeviCivita
g α` is metric-compatible with the smooth Riemannian metric `g`.

The proof unfolds both sides of the metric-compatibility identity in
chart-α coordinates and matches them via the chart metric identity
`partialDeriv_chartGramOnE_eq_chartChristoffel_sum` together with the
algebraic match `christoffel_match`. -/
theorem chartLeviCivita_isMetricCompatibleOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    IsMetricCompatibleOn (chartLeviCivita (I := I) g α) g
      (chartLeviCivitaGoodSet (I := I) α) := by
  classical
  intro Y Z x hY hZ hx v
  rw [mfderiv_g_inner_chart_expand (I := I) g α hx hY hZ v]
  rw [g_inner_chartLeviCivita_Y_Z_expand (I := I) g α hx v,
      g_inner_Y_chartLeviCivita_Z_expand (I := I) g α hx v]
  set n := Module.finrank ℝ E with hn
  have hRHS_Y_distr :
    (∑ i : Fin n, ∑ j : Fin n,
        ( ((chartModelBasis E).repr
              (fderiv ℝ
                (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
                (extChartAt I α x) (trivToE (I := I) α x v))) i +
          ∑ k : Fin n,
            ∑ l : Fin n,
              ((chartModelBasis E).repr (trivToE (I := I) α x v)) k *
                ((chartModelBasis E).repr
                  (chartE_section_repr (I := I) α Y x)) l *
                chartChristoffel (I := I) g α k l i (extChartAt I α x) ) *
          ((chartModelBasis E).repr
              (chartE_section_repr (I := I) α Z x)) j *
          chartGramOnE (I := I) g α i j (extChartAt I α x)) =
    (∑ i : Fin n, ∑ j : Fin n,
        ((chartModelBasis E).repr
            (fderiv ℝ
              (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
              (extChartAt I α x) (trivToE (I := I) α x v))) i *
          ((chartModelBasis E).repr
              (chartE_section_repr (I := I) α Z x)) j *
          chartGramOnE (I := I) g α i j (extChartAt I α x)) +
    (∑ i : Fin n, ∑ j : Fin n,
        (∑ k : Fin n, ∑ l : Fin n,
          ((chartModelBasis E).repr (trivToE (I := I) α x v)) k *
            ((chartModelBasis E).repr
              (chartE_section_repr (I := I) α Y x)) l *
            chartChristoffel (I := I) g α k l i (extChartAt I α x)) *
          ((chartModelBasis E).repr
              (chartE_section_repr (I := I) α Z x)) j *
          chartGramOnE (I := I) g α i j (extChartAt I α x)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [add_mul, add_mul]
  have hRHS_Z_distr :
    (∑ i : Fin n, ∑ j : Fin n,
        ((chartModelBasis E).repr
            (chartE_section_repr (I := I) α Y x)) i *
          ( ((chartModelBasis E).repr
                (fderiv ℝ
                  (chartE_section_repr (I := I) α Z ∘ (extChartAt I α).symm)
                  (extChartAt I α x) (trivToE (I := I) α x v))) j +
            ∑ k : Fin n,
              ∑ l : Fin n,
                ((chartModelBasis E).repr (trivToE (I := I) α x v)) k *
                  ((chartModelBasis E).repr
                    (chartE_section_repr (I := I) α Z x)) l *
                  chartChristoffel (I := I) g α k l j (extChartAt I α x) ) *
          chartGramOnE (I := I) g α i j (extChartAt I α x)) =
    (∑ i : Fin n, ∑ j : Fin n,
        ((chartModelBasis E).repr
            (chartE_section_repr (I := I) α Y x)) i *
          ((chartModelBasis E).repr
            (fderiv ℝ
              (chartE_section_repr (I := I) α Z ∘ (extChartAt I α).symm)
              (extChartAt I α x) (trivToE (I := I) α x v))) j *
          chartGramOnE (I := I) g α i j (extChartAt I α x)) +
    (∑ i : Fin n, ∑ j : Fin n,
        ((chartModelBasis E).repr
            (chartE_section_repr (I := I) α Y x)) i *
          (∑ k : Fin n, ∑ l : Fin n,
            ((chartModelBasis E).repr (trivToE (I := I) α x v)) k *
              ((chartModelBasis E).repr
                (chartE_section_repr (I := I) α Z x)) l *
              chartChristoffel (I := I) g α k l j (extChartAt I α x)) *
          chartGramOnE (I := I) g α i j (extChartAt I α x)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_add, add_mul]
  rw [hRHS_Y_distr, hRHS_Z_distr]
  have hLHS_split :
    (∑ i : Fin n, ∑ j : Fin n,
        (((chartModelBasis E).repr
            (fderiv ℝ
              (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
              (extChartAt I α x) (trivToE (I := I) α x v))) i *
            ((chartModelBasis E).repr
              (chartE_section_repr (I := I) α Z x)) j *
            chartGramOnE (I := I) g α i j (extChartAt I α x) +
          ((chartModelBasis E).repr
            (chartE_section_repr (I := I) α Y x)) i *
            ((chartModelBasis E).repr
              (fderiv ℝ
                (chartE_section_repr (I := I) α Z ∘ (extChartAt I α).symm)
                (extChartAt I α x) (trivToE (I := I) α x v))) j *
            chartGramOnE (I := I) g α i j (extChartAt I α x) +
          ((chartModelBasis E).repr
            (chartE_section_repr (I := I) α Y x)) i *
            ((chartModelBasis E).repr
              (chartE_section_repr (I := I) α Z x)) j *
            (∑ k : Fin n,
              ((chartModelBasis E).repr (trivToE (I := I) α x v)) k *
                ((∑ l : Fin n,
                    chartChristoffel (I := I) g α k i l (extChartAt I α x) *
                      chartGramOnE (I := I) g α l j (extChartAt I α x)) +
                (∑ l : Fin n,
                    chartChristoffel (I := I) g α k j l (extChartAt I α x) *
                      chartGramOnE (I := I) g α l i (extChartAt I α x)))))) =
    (∑ i : Fin n, ∑ j : Fin n,
        ((chartModelBasis E).repr
            (fderiv ℝ
              (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
              (extChartAt I α x) (trivToE (I := I) α x v))) i *
          ((chartModelBasis E).repr
            (chartE_section_repr (I := I) α Z x)) j *
          chartGramOnE (I := I) g α i j (extChartAt I α x)) +
    (∑ i : Fin n, ∑ j : Fin n,
        ((chartModelBasis E).repr
            (chartE_section_repr (I := I) α Y x)) i *
          ((chartModelBasis E).repr
            (fderiv ℝ
              (chartE_section_repr (I := I) α Z ∘ (extChartAt I α).symm)
              (extChartAt I α x) (trivToE (I := I) α x v))) j *
          chartGramOnE (I := I) g α i j (extChartAt I α x)) +
    (∑ i : Fin n, ∑ j : Fin n,
        ((chartModelBasis E).repr
            (chartE_section_repr (I := I) α Y x)) i *
          ((chartModelBasis E).repr
            (chartE_section_repr (I := I) α Z x)) j *
          (∑ k : Fin n,
            ((chartModelBasis E).repr (trivToE (I := I) α x v)) k *
              ((∑ l : Fin n,
                  chartChristoffel (I := I) g α k i l (extChartAt I α x) *
                    chartGramOnE (I := I) g α l j (extChartAt I α x)) +
              (∑ l : Fin n,
                  chartChristoffel (I := I) g α k j l (extChartAt I α x) *
                    chartGramOnE (I := I) g α l i (extChartAt I α x))))) := by
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
  rw [hLHS_split]
  have hGsymm : ∀ a b : Fin n,
      chartGramOnE (I := I) g α a b (extChartAt I α x) =
        chartGramOnE (I := I) g α b a (extChartAt I α x) := by
    intro a b
    exact chartGramOnE_symm (I := I) g α a b (extChartAt I α x)
  have hmatch :=
    christoffel_match
      (n := n)
      (B := fun i => ((chartModelBasis E).repr
        (chartE_section_repr (I := I) α Y x)) i)
      (D := fun j => ((chartModelBasis E).repr
        (chartE_section_repr (I := I) α Z x)) j)
      (w := fun k => ((chartModelBasis E).repr (trivToE (I := I) α x v)) k)
      (G := fun a b => chartGramOnE (I := I) g α a b (extChartAt I α x))
      (Γ := fun a b c => chartChristoffel (I := I) g α a b c (extChartAt I α x))
      hGsymm
  linear_combination hmatch

end Connection
end Integral
end DifferentialGeometry
