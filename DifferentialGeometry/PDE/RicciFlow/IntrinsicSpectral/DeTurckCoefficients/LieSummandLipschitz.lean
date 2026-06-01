import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.ChristoffelPerturbation
import DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ChartVectorField

/-!
# Lipschitz dependence of the DeTurck Lie (gauge) summand on the metric 2-jet

For a fixed chart base point `α`, a fixed background metric `g_bg`, and two smooth
Riemannian metrics `g₁, g₂`, the chart-frame components of the DeTurck Lie (gauge)
summand
```
(𝓛_{W(g)} g)_{ij}(y) = ∑_k W^k(g)(y) · ∂_k G_{ij}(g)(y)
                       + ∑_k G_{kj}(g)(y) · ∂_i W^k(g)(y)
                       + ∑_k G_{ik}(g)(y) · ∂_j W^k(g)(y),
```
with the DeTurck vector-field components `W^k(g)(y) = chartDeTurckVFComp g g_bg α k y`
(carrying `∂g`), satisfy a Lipschitz estimate in the chart `2`-jet of the metric
difference `g₁ − g₂`:
```
|(𝓛_{W(g₁)} g₁)_{ij}(y) − (𝓛_{W(g₂)} g₂)_{ij}(y)| ≤ C · (chart 2-jet seminorm of (g₁−g₂) at y)
```
uniformly over a compact subset `K` of the chart-target interior and over the
"R-ball" of metrics (a uniform entry bound on the inverse-Gram matrices, exactly
the hypothesis supplied to the inverse-Gram / Christoffel perturbation leaves).

## Strategy

The Lie summand is a finite sum of products in the chart-coordinate building blocks

* `W^k(g) = chartDeTurckVFComp g g_bg α k` (a `1`-jet object: it carries `∂g`),
* `∂_m W^k(g)` (a `2`-jet object: it carries `∂²g`),
* `G_{ij}(g) = chartGramOnE g α i j` (a `0`-jet object),
* `∂_m G_{ij}(g)` (a `1`-jet object).

Each ingredient is `C^∞` on the chart-target interior, hence uniformly bounded on
a compact subset `K`, and each ingredient's `g₁ − g₂` difference is controlled by
the relevant jet-difference seminorm:

* `W^k` difference by the `1`-jet seminorm `chartMetricJet1DiffSup`, via the
  committed Christoffel/inverse-Gram perturbation atoms
  (`exists_chartChristoffel_lipschitz_on_compact`,
  `exists_chartInvGramMatrix_lipschitz_on_compact`);
* `∂_m W^k` difference by the `2`-jet seminorm `chartMetricJet2DiffSup`, via the
  committed Christoffel-derivative perturbation atom
  (`exists_chartChristoffelDeriv_lipschitz_on_compact`) plus the inverse-Gram
  partial-derivative perturbation lemma `partialDeriv_chartInvGramOnE_sub_abs_le`;
* `G_{ij}` difference by the `0`-jet (`chartGramDiffSup`), and `∂_m G_{ij}`
  difference by the first-partial aggregate (`chartGramPartialDiffSup`), both
  dominated by the `2`-jet seminorm.

The difference of each product is majorised by the difference-of-products identity
`A₁B₁ − A₂B₂ = (A₁ − A₂)B₁ + A₂(B₁ − B₂)`, and every piece reduces to a uniform
constant times a jet-difference seminorm `≤ chartMetricJet2DiffSup`.

## Main results

* `chartLieDeTurckComp` — the chart-frame `(i, j)` component of the DeTurck Lie
  (gauge) summand `(𝓛_{W(g)} g)_{ij}`, as a function on the chart target.
* `exists_chartDeTurckVFComp_lipschitz_on_compact` — the `W^k` Lipschitz bound
  against the `1`-jet seminorm, uniform over `K`.
* `exists_partialDeriv_chartDeTurckVFComp_lipschitz_on_compact` — the `∂_m W^k`
  Lipschitz bound against the `2`-jet seminorm, uniform over `K`.
* `exists_chartLieDeTurckComp_lipschitz_on_compact` — the headline Lie-summand
  bound: `|(𝓛_{W(g₁)} g₁)_{ij}(y) − (𝓛_{W(g₂)} g₂)_{ij}(y)| ≤ C · chartMetricJet2DiffSup g₁ g₂ α y`
  for all `y ∈ K`, uniform over `K`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Set Matrix
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- A function that is `C^∞` on the (open) chart-target interior is uniformly
bounded in absolute value on a compact subset `K`. -/
private lemma exists_bound_of_contDiffOn_int
    {f : E → ℝ} (α : M)
    (hf : ContDiffOn ℝ ∞ f (interior (extChartAt I α).target))
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |f y| ≤ C := by
  classical
  have hcont : ContinuousOn f K := (hf.continuousOn).mono hKsub
  by_cases hKne : K.Nonempty
  · have hcont_abs : ContinuousOn (fun y => |f y|) K :=
      continuous_abs.comp_continuousOn hcont
    obtain ⟨y₀, _hy₀K, hy₀max⟩ := hK.exists_isMaxOn hKne hcont_abs
    exact ⟨|f y₀|, abs_nonneg _, fun y hy => hy₀max hy⟩
  · exact ⟨0, le_refl 0, fun y hy => absurd ⟨y, hy⟩ hKne⟩

set_option linter.unusedFintypeInType false in
/-- A finite family of functions, each `C^∞` on the chart-target interior, admits
a single uniform bound on a compact subset `K`. -/
private lemma exists_uniform_bound_family
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (α : M) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (interior (extChartAt I α).target))
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ i, |f i y| ≤ C := by
  classical
  have hbound : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |f i y| ≤ C := fun i =>
    exists_bound_of_contDiffOn_int (I := I) α (hf i) hK hKsub
  choose C hC_nn hC_bd using hbound
  refine ⟨Finset.univ.sup' Finset.univ_nonempty C, ?_, ?_⟩
  · exact le_trans (hC_nn (Classical.arbitrary ι))
      (Finset.le_sup' C (Finset.mem_univ (Classical.arbitrary ι)))
  · intro y hy i
    exact (hC_bd i y hy).trans (Finset.le_sup' C (Finset.mem_univ i))

/-- The chart Christoffel symbol is `C^∞` on the chart-target interior. -/
private lemma chartChristoffel_contDiffOn_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (a b k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α a b k)
      (interior (extChartAt I α).target) :=
  chartChristoffel_contDiffOn_interior (I := I) g α a b k

/-- The chart DeTurck-VF component is `C^∞` on the chart-target interior. -/
private lemma chartDeTurckVFComp_contDiffOn_int
    (g g_bg : SmoothRiemannianMetric I M) (α : M) (k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartDeTurckVFComp (I := I) g g_bg α k)
      (interior (extChartAt I α).target) :=
  chartDeTurckVFComp_contDiffOn_interior (I := I) g g_bg α k

/-- The first partial of the chart DeTurck-VF component is `C^∞` on the
chart-target interior. -/
private lemma partial_chartDeTurckVFComp_contDiffOn_int
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (m k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g g_bg α k))
      (interior (extChartAt I α).target) := by
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartDeTurckVFComp (I := I) g g_bg α k))
      (interior (extChartAt I α).target) :=
    (chartDeTurckVFComp_contDiffOn_int (I := I) g g_bg α k).fderiv_of_isOpen
      isOpen_interior (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

/-- The chart Christoffel symbol is differentiable at an interior point. -/
private lemma chartChristoffel_differentiableAt_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (a b k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartChristoffel (I := I) g α a b k) y :=
  ((chartChristoffel_contDiffOn_int (I := I) g α a b k).contDiffAt
    (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

/-- The inverse-Gram entry is differentiable at an interior point. -/
private lemma chartInvGramOnE_differentiableAt_int'
    (g : SmoothRiemannianMetric I M) (α : M) (a b : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartInvGramOnE (I := I) g α a b) y :=
  (((chartInvGramOnE_contDiffOn (I := I) g α a b).mono interior_subset).contDiffAt
    (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

/-- **Leibniz expansion of `∂_m W^k`.** On the chart-target interior, the first
partial of the chart DeTurck-VF component is the product-rule expansion of its
defining double sum. -/
theorem partialDeriv_chartDeTurckVFComp_eq
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (m k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g g_bg α k) y =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α a b) y *
            (chartChristoffel (I := I) g α a b k y -
              chartChristoffel (I := I) g_bg α a b k y)
          + chartInvGramOnE (I := I) g α a b y *
            (partialDeriv (E := E) m (chartChristoffel (I := I) g α a b k) y -
              partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y)) := by
  classical
  have heq : chartDeTurckVFComp (I := I) g g_bg α k =
      fun z : E => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b z *
          (chartChristoffel (I := I) g α a b k z -
            chartChristoffel (I := I) g_bg α a b k z) := by
    funext z; rw [chartDeTurckVFComp_def]
  rw [show partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g g_bg α k) y =
        partialDeriv (E := E) m
          (fun z : E => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b z *
              (chartChristoffel (I := I) g α a b k z -
                chartChristoffel (I := I) g_bg α a b k z)) y from by rw [heq]]
  have hsummand_diff : ∀ a b : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun z : E => chartInvGramOnE (I := I) g α a b z *
          (chartChristoffel (I := I) g α a b k z -
            chartChristoffel (I := I) g_bg α a b k z)) y := by
    intro a b
    exact (chartInvGramOnE_differentiableAt_int' (I := I) g α a b hy).mul
      ((chartChristoffel_differentiableAt_int (I := I) g α a b k hy).sub
        (chartChristoffel_differentiableAt_int (I := I) g_bg α a b k hy))
  have hinner_diff : ∀ a : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun z : E => ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b z *
            (chartChristoffel (I := I) g α a b k z -
              chartChristoffel (I := I) g_bg α a b k z)) y :=
    fun a => DifferentiableAt.fun_sum (fun b _ => hsummand_diff a b)
  rw [partialDeriv_sum (i := m) Finset.univ
      (fun a => fun z : E => ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b z *
          (chartChristoffel (I := I) g α a b k z -
            chartChristoffel (I := I) g_bg α a b k z))
      (fun a _ => hinner_diff a)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [partialDeriv_sum (i := m) Finset.univ
      (fun b => fun z : E => chartInvGramOnE (I := I) g α a b z *
        (chartChristoffel (I := I) g α a b k z -
          chartChristoffel (I := I) g_bg α a b k z))
      (fun b _ => hsummand_diff a b)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [partialDeriv_mul (i := m) (chartInvGramOnE (I := I) g α a b)
      (fun z : E => chartChristoffel (I := I) g α a b k z -
        chartChristoffel (I := I) g_bg α a b k z)
      (chartInvGramOnE_differentiableAt_int' (I := I) g α a b hy)
      ((chartChristoffel_differentiableAt_int (I := I) g α a b k hy).sub
        (chartChristoffel_differentiableAt_int (I := I) g_bg α a b k hy))]
  rw [partialDeriv_sub (i := m) (chartChristoffel (I := I) g α a b k)
      (chartChristoffel (I := I) g_bg α a b k)
      (chartChristoffel_differentiableAt_int (I := I) g α a b k hy)
      (chartChristoffel_differentiableAt_int (I := I) g_bg α a b k hy)]

/-- Uniform bound on the chart Christoffel symbols over `K`. -/
private lemma exists_chartChristoffel_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ a b k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g α a b k y| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_family (I := I) α
    (fun p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)) =>
      chartChristoffel (I := I) g α p.1.1 p.1.2 p.2)
    (fun p => chartChristoffel_contDiffOn_int (I := I) g α p.1.1 p.1.2 p.2) hK hKsub
  exact ⟨C, hC_nn, fun y hy a b k => hC y hy ((a, b), k)⟩

/-- Uniform bound on the chart Christoffel difference `Γ(g) − Γ(g_bg)` over `K`. -/
private lemma exists_chartChristoffel_diff_bound_on_compact
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ a b k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g α a b k y -
          chartChristoffel (I := I) g_bg α a b k y| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_family (I := I) α
    (fun p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)) =>
      fun y : E => chartChristoffel (I := I) g α p.1.1 p.1.2 p.2 y -
        chartChristoffel (I := I) g_bg α p.1.1 p.1.2 p.2 y)
    (fun p => (chartChristoffel_contDiffOn_int (I := I) g α p.1.1 p.1.2 p.2).sub
      (chartChristoffel_contDiffOn_int (I := I) g_bg α p.1.1 p.1.2 p.2)) hK hKsub
  exact ⟨C, hC_nn, fun y hy a b k => hC y hy ((a, b), k)⟩

/-- Uniform bound on the inverse-Gram entries over `K`. -/
private lemma exists_invGramOnE_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ a b : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g α a b y| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_family (I := I) α
    (fun p : (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E)) =>
      chartInvGramOnE (I := I) g α p.1 p.2)
    (fun p => (chartInvGramOnE_contDiffOn (I := I) g α p.1 p.2).mono interior_subset) hK hKsub
  exact ⟨C, hC_nn, fun y hy a b => hC y hy (a, b)⟩

/-- Uniform bound on the first partials of the inverse-Gram entries over `K`. -/
private lemma exists_partial_invGramOnE_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ m a b : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartInvGramOnE (I := I) g α a b) y| ≤ C := by
  classical
  have hsmooth : ∀ p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞ (partialDeriv (E := E) p.1.1 (chartInvGramOnE (I := I) g α p.1.2 p.2))
        (interior (extChartAt I α).target) := by
    intro p
    have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartInvGramOnE (I := I) g α p.1.2 p.2))
        (interior (extChartAt I α).target) :=
      ((chartInvGramOnE_contDiffOn (I := I) g α p.1.2 p.2).mono interior_subset).fderiv_of_isOpen
        isOpen_interior (by rw [ENat.coe_top_add_one])
    unfold partialDeriv
    exact hfderiv.clm_apply contDiffOn_const
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_family (I := I) α
    (fun p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)) =>
      partialDeriv (E := E) p.1.1 (chartInvGramOnE (I := I) g α p.1.2 p.2))
    hsmooth hK hKsub
  exact ⟨C, hC_nn, fun y hy m a b => hC y hy ((m, a), b)⟩

/-- Uniform bound on the first partials of the chart Christoffel symbols over `K`. -/
private lemma exists_partial_chartChristoffel_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ m a b k : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartChristoffel (I := I) g α a b k) y| ≤ C := by
  classical
  have hsmooth : ∀ p : (((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E))) × (Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞ (partialDeriv (E := E) p.1.1.1
          (chartChristoffel (I := I) g α p.1.1.2 p.1.2 p.2))
        (interior (extChartAt I α).target) := by
    intro p
    have hfderiv : ContDiffOn ℝ ∞
        (fderiv ℝ (chartChristoffel (I := I) g α p.1.1.2 p.1.2 p.2))
        (interior (extChartAt I α).target) :=
      (chartChristoffel_contDiffOn_int (I := I) g α p.1.1.2 p.1.2 p.2).fderiv_of_isOpen
        isOpen_interior (by rw [ENat.coe_top_add_one])
    unfold partialDeriv
    exact hfderiv.clm_apply contDiffOn_const
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_family (I := I) α
    (fun p : (((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E))) × (Fin (Module.finrank ℝ E)) =>
      partialDeriv (E := E) p.1.1.1 (chartChristoffel (I := I) g α p.1.1.2 p.1.2 p.2))
    hsmooth hK hKsub
  exact ⟨C, hC_nn, fun y hy m a b k => hC y hy (((m, a), b), k)⟩

/-- Uniform bound on the chart Christoffel-derivative difference
`∂_m Γ(g) − ∂_m Γ(g_bg)` over `K`. -/
private lemma exists_partial_chartChristoffel_diff_bound_on_compact
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ m a b k : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartChristoffel (I := I) g α a b k) y -
          partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y| ≤ C := by
  classical
  have hsmooth : ∀ p : (((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E))) × (Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞
        (fun y : E =>
          partialDeriv (E := E) p.1.1.1 (chartChristoffel (I := I) g α p.1.1.2 p.1.2 p.2) y -
            partialDeriv (E := E) p.1.1.1 (chartChristoffel (I := I) g_bg α p.1.1.2 p.1.2 p.2) y)
        (interior (extChartAt I α).target) := by
    intro p
    have hg : ContDiffOn ℝ ∞
        (partialDeriv (E := E) p.1.1.1 (chartChristoffel (I := I) g α p.1.1.2 p.1.2 p.2))
        (interior (extChartAt I α).target) := by
      have hfderiv : ContDiffOn ℝ ∞
          (fderiv ℝ (chartChristoffel (I := I) g α p.1.1.2 p.1.2 p.2))
          (interior (extChartAt I α).target) :=
        (chartChristoffel_contDiffOn_int (I := I) g α p.1.1.2 p.1.2 p.2).fderiv_of_isOpen
          isOpen_interior (by rw [ENat.coe_top_add_one])
      unfold partialDeriv
      exact hfderiv.clm_apply contDiffOn_const
    have hg' : ContDiffOn ℝ ∞
        (partialDeriv (E := E) p.1.1.1 (chartChristoffel (I := I) g_bg α p.1.1.2 p.1.2 p.2))
        (interior (extChartAt I α).target) := by
      have hfderiv : ContDiffOn ℝ ∞
          (fderiv ℝ (chartChristoffel (I := I) g_bg α p.1.1.2 p.1.2 p.2))
          (interior (extChartAt I α).target) :=
        (chartChristoffel_contDiffOn_int (I := I) g_bg α p.1.1.2 p.1.2 p.2).fderiv_of_isOpen
          isOpen_interior (by rw [ENat.coe_top_add_one])
      unfold partialDeriv
      exact hfderiv.clm_apply contDiffOn_const
    exact hg.sub hg'
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_family (I := I) α
    (fun p : (((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E))) × (Fin (Module.finrank ℝ E)) =>
      fun y : E =>
        partialDeriv (E := E) p.1.1.1 (chartChristoffel (I := I) g α p.1.1.2 p.1.2 p.2) y -
          partialDeriv (E := E) p.1.1.1 (chartChristoffel (I := I) g_bg α p.1.1.2 p.1.2 p.2) y)
    hsmooth hK hKsub
  exact ⟨C, hC_nn, fun y hy m a b k => hC y hy (((m, a), b), k)⟩

/-- Uniform bound on the first partials of the chart Gram entries over `K`. -/
private lemma exists_partial_gramOnE_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ m a b : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartGramOnE (I := I) g α a b) y| ≤ C := by
  classical
  have hsmooth : ∀ p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞ (partialDeriv (E := E) p.1.1 (chartGramOnE (I := I) g α p.1.2 p.2))
        (interior (extChartAt I α).target) := by
    intro p
    have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartGramOnE (I := I) g α p.1.2 p.2))
        (interior (extChartAt I α).target) :=
      ((chartGramOnE_contDiffOn (I := I) g α p.1.2 p.2).mono interior_subset).fderiv_of_isOpen
        isOpen_interior (by rw [ENat.coe_top_add_one])
    unfold partialDeriv
    exact hfderiv.clm_apply contDiffOn_const
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_family (I := I) α
    (fun p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)) =>
      partialDeriv (E := E) p.1.1 (chartGramOnE (I := I) g α p.1.2 p.2))
    hsmooth hK hKsub
  exact ⟨C, hC_nn, fun y hy m a b => hC y hy ((m, a), b)⟩

/-- Uniform bound on the chart Gram entries over `K`. -/
private lemma exists_gramOnE_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ a b : Fin (Module.finrank ℝ E),
      |chartGramOnE (I := I) g α a b y| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_family (I := I) α
    (fun p : (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E)) =>
      chartGramOnE (I := I) g α p.1 p.2)
    (fun p => (chartGramOnE_contDiffOn (I := I) g α p.1 p.2).mono interior_subset) hK hKsub
  exact ⟨C, hC_nn, fun y hy a b => hC y hy (a, b)⟩

/-- Uniform bound on the chart DeTurck-VF components `W^k` over `K`. -/
private lemma exists_chartDeTurckVFComp_bound_on_compact
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ k : Fin (Module.finrank ℝ E),
      |chartDeTurckVFComp (I := I) g g_bg α k y| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_family (I := I) α
    (fun k : Fin (Module.finrank ℝ E) => chartDeTurckVFComp (I := I) g g_bg α k)
    (fun k => chartDeTurckVFComp_contDiffOn_int (I := I) g g_bg α k) hK hKsub
  exact ⟨C, hC_nn, fun y hy k => hC y hy k⟩

/-- Uniform bound on the first partials of the chart DeTurck-VF components `∂_m W^k`
over `K`. -/
private lemma exists_partial_chartDeTurckVFComp_bound_on_compact
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ m k : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g g_bg α k) y| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_family (I := I) α
    (fun p : (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E)) =>
      partialDeriv (E := E) p.1 (chartDeTurckVFComp (I := I) g g_bg α p.2))
    (fun p => partial_chartDeTurckVFComp_contDiffOn_int (I := I) g g_bg α p.1 p.2) hK hKsub
  exact ⟨C, hC_nn, fun y hy m k => hC y hy (m, k)⟩

/-- **Per-point Lipschitz bound for `W^k`.**  With the inverse-Gram `0`-jet
Lipschitz bound `Cinv · chartGramDiffSup`, the Christoffel difference Lipschitz
bound `CΓ · jet1`, a uniform Christoffel-difference bound `P` for `g₁`, and a
uniform inverse-Gram entry bound `M_b` for `g₂`,
`|W^k(g₁)(y) − W^k(g₂)(y)| ≤ n²·(Cinv·P + M_b·CΓ)·chartMetricJet1DiffSup g₁ g₂ α y`. -/
theorem chartDeTurckVFComp_sub_abs_le
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M) {y : E}
    {Cinv CΓ M_b P : ℝ}
    (hCinv_nn : 0 ≤ Cinv) (hMb_nn : 0 ≤ M_b) (hP_nn : 0 ≤ P)
    (hP : ∀ a b k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₁ α a b k y -
          chartChristoffel (I := I) g_bg α a b k y| ≤ P)
    (hMb : ∀ a b : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g₂ α a b y| ≤ M_b)
    (hCinv : ∀ a b : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g₁ α a b y - chartInvGramOnE (I := I) g₂ α a b y| ≤
        Cinv * chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y))
    (hCΓ : ∀ a b k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₁ α a b k y - chartChristoffel (I := I) g₂ α a b k y| ≤
        CΓ * chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y)
    (k : Fin (Module.finrank ℝ E)) :
    |chartDeTurckVFComp (I := I) g₁ g_bg α k y -
        chartDeTurckVFComp (I := I) g₂ g_bg α k y| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * (Cinv * P + M_b * CΓ) *
        chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  rw [chartDeTurckVFComp_def, chartDeTurckVFComp_def, ← Finset.sum_sub_distrib]
  set jet1 : ℝ := chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y with hjet1_def
  have hjet1_nn : 0 ≤ jet1 := chartMetricJet1DiffSup_nonneg _ _ _ _
  set gd : ℝ := chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) with hgd
  have hgd_le : gd ≤ jet1 := chartGramDiffSup_le_jet1 (I := I) (M := M) g₁ g₂ α y
  have hgd_nn : 0 ≤ gd := chartGramDiffSup_nonneg _ _ _ _
  have hterm : ∀ a : Fin (Module.finrank ℝ E),
      |(∑ b : Fin (Module.finrank ℝ E), chartInvGramOnE (I := I) g₁ α a b y *
            (chartChristoffel (I := I) g₁ α a b k y -
              chartChristoffel (I := I) g_bg α a b k y)) -
        (∑ b : Fin (Module.finrank ℝ E), chartInvGramOnE (I := I) g₂ α a b y *
            (chartChristoffel (I := I) g₂ α a b k y -
              chartChristoffel (I := I) g_bg α a b k y))| ≤
        (Module.finrank ℝ E : ℝ) * ((Cinv * P + M_b * CΓ) * jet1) := by
    intro a
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ : Fin (Module.finrank ℝ E) =>
      (Cinv * P + M_b * CΓ) * jet1) (fun b _ => ?_)) ?_
    · set A₁ : ℝ := chartInvGramOnE (I := I) g₁ α a b y with hA1
      set A₂ : ℝ := chartInvGramOnE (I := I) g₂ α a b y with hA2
      set B₁ : ℝ := chartChristoffel (I := I) g₁ α a b k y -
        chartChristoffel (I := I) g_bg α a b k y with hB1
      set B₂ : ℝ := chartChristoffel (I := I) g₂ α a b k y -
        chartChristoffel (I := I) g_bg α a b k y with hB2
      have hsplit : A₁ * B₁ - A₂ * B₂ = (A₁ - A₂) * B₁ + A₂ * (B₁ - B₂) := by ring
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      have h1 : |(A₁ - A₂) * B₁| ≤ Cinv * P * jet1 := by
        rw [abs_mul]
        calc |A₁ - A₂| * |B₁|
            ≤ (Cinv * gd) * P := mul_le_mul (hCinv a b) (hP a b k) (abs_nonneg _)
                (mul_nonneg hCinv_nn hgd_nn)
          _ = Cinv * P * gd := by ring
          _ ≤ Cinv * P * jet1 :=
              mul_le_mul_of_nonneg_left hgd_le (mul_nonneg hCinv_nn hP_nn)
      have hbdiff : B₁ - B₂ =
          chartChristoffel (I := I) g₁ α a b k y - chartChristoffel (I := I) g₂ α a b k y := by
        rw [hB1, hB2]; ring
      have h2 : |A₂ * (B₁ - B₂)| ≤ M_b * CΓ * jet1 := by
        rw [abs_mul, hbdiff]
        calc |A₂| * |chartChristoffel (I := I) g₁ α a b k y -
                chartChristoffel (I := I) g₂ α a b k y|
            ≤ M_b * (CΓ * jet1) := mul_le_mul (hMb a b) (hCΓ a b k) (abs_nonneg _) hMb_nn
          _ = M_b * CΓ * jet1 := by ring
      calc |(A₁ - A₂) * B₁| + |A₂ * (B₁ - B₂)|
          ≤ Cinv * P * jet1 + M_b * CΓ * jet1 := add_le_add h1 h2
        _ = (Cinv * P + M_b * CΓ) * jet1 := by ring
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : Fin (Module.finrank ℝ E) =>
    (Module.finrank ℝ E : ℝ) * ((Cinv * P + M_b * CΓ) * jet1)) (fun a _ => hterm a)) ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (Module.finrank ℝ E : ℝ) ^ 2 * (Cinv * P + M_b * CΓ) * jet1 =
        (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) * ((Cinv * P + M_b * CΓ) * jet1)) by ring]

/-- The manifold image of a compact subset of the chart-target interior is a
compact subset of the chart source. -/
private lemma symm_image_compact_subset_source
    (α : M) {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    IsCompact ((extChartAt I α).symm '' K) ∧
      (extChartAt I α).symm '' K ⊆ (chartAt H α).source := by
  have hKsub_target : K ⊆ (extChartAt I α).target := hKsub.trans interior_subset
  refine ⟨hK.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := I) α).mono hKsub_target), ?_⟩
  rintro x ⟨z, hzK, rfl⟩
  have hsource : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target (hKsub_target hzK)
  rwa [extChartAt_source_eq_chartAt_source (I := I)] at hsource

/-- **Uniform Lipschitz dependence of the chart DeTurck-VF components `W^k` on the
chart `1`-jet of the metric difference, over a compact subset of the chart-target
interior.**

For two smooth Riemannian metrics `g₁, g₂`, a fixed background metric `g_bg`, a
chart base point `α`, and a compact subset `K` of the interior of the chart-`α`
target, there is a single constant `C > 0` such that for every `y ∈ K` and every
index `k`,
```
|W^k(g₁)(y) − W^k(g₂)(y)| ≤ C · chartMetricJet1DiffSup g₁ g₂ α y .
```
On a fixed compact `R`-ball of metrics the uniform inverse-Gram entry bound `M_b`
may be taken uniform over the ball, so `C` becomes the desired `C(R)`. -/
theorem exists_chartDeTurckVFComp_lipschitz_on_compact
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ k : Fin (Module.finrank ℝ E),
      |chartDeTurckVFComp (I := I) g₁ g_bg α k y -
          chartDeTurckVFComp (I := I) g₂ g_bg α k y| ≤
        C * chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  obtain ⟨hK'_compact, hK'_sub⟩ := symm_image_compact_subset_source (I := I) α hK hKsub
  obtain ⟨Cinv, hCinv_pos, hCinv⟩ :=
    exists_chartInvGramMatrix_lipschitz_on_compact (I := I) (M := M) g₁ g₂ α hK'_compact hK'_sub
  obtain ⟨CΓ, hCΓ_pos, hCΓ⟩ :=
    exists_chartChristoffel_lipschitz_on_compact (I := I) (M := M) g₁ g₂ α hK hKsub
  obtain ⟨P, hP_nn, hP⟩ :=
    exists_chartChristoffel_diff_bound_on_compact (I := I) g₁ g_bg α hK hKsub
  obtain ⟨M_b, hMb_nn, hMb⟩ := exists_invGramOnE_bound_on_compact (I := I) g₂ α hK hKsub
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * (Cinv * P + M_b * CΓ) + 1, ?_, ?_⟩
  · have hnn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (Cinv * P + M_b * CΓ) := by
      refine mul_nonneg (by positivity) ?_
      have h1 : 0 ≤ Cinv * P := mul_nonneg hCinv_pos.le hP_nn
      have h2 : 0 ≤ M_b * CΓ := mul_nonneg hMb_nn hCΓ_pos.le
      linarith
    linarith
  intro y hy k
  have hxy_mem : (extChartAt I α).symm y ∈ (extChartAt I α).symm '' K := ⟨y, hy, rfl⟩
  have hCinv' : ∀ a b : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g₁ α a b y - chartInvGramOnE (I := I) g₂ α a b y| ≤
        Cinv * chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) := by
    intro a b
    simpa only [chartInvGramOnE_def] using hCinv ((extChartAt I α).symm y) hxy_mem a b
  have h_pt := chartDeTurckVFComp_sub_abs_le (I := I) (M := M) g₁ g₂ g_bg α
    hCinv_pos.le hMb_nn hP_nn
    (fun a b kk => hP y hy a b kk) (fun a b => hMb y hy a b) hCinv'
    (fun a b kk => hCΓ y hy a b kk) k
  have hjet1_nn : 0 ≤ chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y :=
    chartMetricJet1DiffSup_nonneg _ _ _ _
  refine h_pt.trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hjet1_nn

/-- **Per-point Lipschitz bound for `∂_m W^k`.**  On the chart-target interior,
with the inverse-Gram-partial Lipschitz bound `Cd · jet1`, the inverse-Gram `0`-jet
Lipschitz bound `Cinv · chartGramDiffSup`, the Christoffel difference Lipschitz
bound `CΓ · jet1`, the Christoffel-derivative difference Lipschitz bound
`CdΓ · jet2`, uniform Christoffel-difference bound `P` (for `g₁`), uniform
inverse-Gram entry bound `M_b` (for `g₂`), uniform inverse-Gram-partial bound `D`
(for `g₂`), and uniform Christoffel-derivative-difference bound `R` (for `g₁`),
```
|∂_m W^k(g₁)(y) − ∂_m W^k(g₂)(y)| ≤
    n²·(Cd·P + D·CΓ + Cinv·R + M_b·CdΓ)·chartMetricJet2DiffSup g₁ g₂ α y .
``` -/
theorem partialDeriv_chartDeTurckVFComp_sub_abs_le
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    {Cd Cinv CΓ CdΓ M_b P D R : ℝ}
    (hCd_nn : 0 ≤ Cd) (hCinv_nn : 0 ≤ Cinv) (hCΓ_nn : 0 ≤ CΓ)
    (hMb_nn : 0 ≤ M_b) (hP_nn : 0 ≤ P) (hD_nn : 0 ≤ D) (hR_nn : 0 ≤ R)
    (m k : Fin (Module.finrank ℝ E))
    (hCd : ∀ a b : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α a b) y -
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α a b) y| ≤
        Cd * chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hCinv : ∀ a b : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g₁ α a b y - chartInvGramOnE (I := I) g₂ α a b y| ≤
        Cinv * chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y))
    (hCΓ : ∀ a b kk : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₁ α a b kk y - chartChristoffel (I := I) g₂ α a b kk y| ≤
        CΓ * chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hCdΓ : ∀ a b kk : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b kk) y -
          partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α a b kk) y| ≤
        CdΓ * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hP : ∀ a b kk : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₁ α a b kk y -
          chartChristoffel (I := I) g_bg α a b kk y| ≤ P)
    (hMb : ∀ a b : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g₂ α a b y| ≤ M_b)
    (hD : ∀ a b : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α a b) y| ≤ D)
    (hR : ∀ a b kk : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b kk) y -
          partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b kk) y| ≤ R) :
    |partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g₁ g_bg α k) y -
        partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g₂ g_bg α k) y| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * (Cd * P + D * CΓ + Cinv * R + M_b * CdΓ) *
        chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  rw [partialDeriv_chartDeTurckVFComp_eq (I := I) g₁ g_bg α m k hy,
    partialDeriv_chartDeTurckVFComp_eq (I := I) g₂ g_bg α m k hy,
    ← Finset.sum_sub_distrib]
  set jet2 : ℝ := chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y with hjet2_def
  have hjet2_nn : 0 ≤ jet2 := chartMetricJet2DiffSup_nonneg _ _ _ _
  set jet1 : ℝ := chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y with hjet1_def
  have hjet1_le : jet1 ≤ jet2 := chartMetricJet1DiffSup_le_jet2 (I := I) (M := M) g₁ g₂ α y
  have hjet1_nn : 0 ≤ jet1 := chartMetricJet1DiffSup_nonneg _ _ _ _
  set gd : ℝ := chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) with hgd
  have hgd_nn : 0 ≤ gd := chartGramDiffSup_nonneg _ _ _ _
  have hgd_le2 : gd ≤ jet2 :=
    le_trans (chartGramDiffSup_le_jet1 (I := I) (M := M) g₁ g₂ α y) hjet1_le
  set C0 : ℝ := Cd * P + D * CΓ + Cinv * R + M_b * CdΓ with hC0_def
  have hterm : ∀ a : Fin (Module.finrank ℝ E),
      |(∑ b : Fin (Module.finrank ℝ E),
            (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α a b) y *
                (chartChristoffel (I := I) g₁ α a b k y -
                  chartChristoffel (I := I) g_bg α a b k y)
              + chartInvGramOnE (I := I) g₁ α a b y *
                (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b k) y -
                  partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y))) -
        (∑ b : Fin (Module.finrank ℝ E),
            (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α a b) y *
                (chartChristoffel (I := I) g₂ α a b k y -
                  chartChristoffel (I := I) g_bg α a b k y)
              + chartInvGramOnE (I := I) g₂ α a b y *
                (partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α a b k) y -
                  partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y)))| ≤
        (Module.finrank ℝ E : ℝ) * (C0 * jet2) := by
    intro a
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ : Fin (Module.finrank ℝ E) =>
      C0 * jet2) (fun b _ => ?_)) ?_
    · set dG₁ : ℝ := partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α a b) y with hdG1
      set dG₂ : ℝ := partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α a b) y with hdG2
      set G₁ : ℝ := chartInvGramOnE (I := I) g₁ α a b y with hG1
      set G₂ : ℝ := chartInvGramOnE (I := I) g₂ α a b y with hG2
      set Γd₁ : ℝ := chartChristoffel (I := I) g₁ α a b k y -
        chartChristoffel (I := I) g_bg α a b k y with hΓd1
      set Γd₂ : ℝ := chartChristoffel (I := I) g₂ α a b k y -
        chartChristoffel (I := I) g_bg α a b k y with hΓd2
      set dΓd₁ : ℝ := partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b k) y -
        partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y with hdΓd1
      set dΓd₂ : ℝ := partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α a b k) y -
        partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y with hdΓd2
      have hsplit :
          (dG₁ * Γd₁ + G₁ * dΓd₁) - (dG₂ * Γd₂ + G₂ * dΓd₂) =
            ((dG₁ - dG₂) * Γd₁ + dG₂ * (Γd₁ - Γd₂)) +
              ((G₁ - G₂) * dΓd₁ + G₂ * (dΓd₁ - dΓd₂)) := by ring
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      have hgroupA : |(dG₁ - dG₂) * Γd₁ + dG₂ * (Γd₁ - Γd₂)| ≤
          Cd * P * jet2 + D * CΓ * jet2 := by
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ?_ ?_
        · rw [abs_mul]
          have hΓd1_le : |Γd₁| ≤ P := hP a b k
          calc |dG₁ - dG₂| * |Γd₁|
              ≤ (Cd * jet1) * P := mul_le_mul (hCd a b) hΓd1_le (abs_nonneg _)
                  (mul_nonneg hCd_nn hjet1_nn)
            _ = Cd * P * jet1 := by ring
            _ ≤ Cd * P * jet2 := mul_le_mul_of_nonneg_left hjet1_le (mul_nonneg hCd_nn hP_nn)
        · rw [abs_mul]
          have hΓdiff : Γd₁ - Γd₂ =
              chartChristoffel (I := I) g₁ α a b k y -
                chartChristoffel (I := I) g₂ α a b k y := by rw [hΓd1, hΓd2]; ring
          calc |dG₂| * |Γd₁ - Γd₂|
              ≤ D * (CΓ * jet1) := by
                rw [hΓdiff]
                exact mul_le_mul (hD a b) (hCΓ a b k) (abs_nonneg _) hD_nn
            _ = D * CΓ * jet1 := by ring
            _ ≤ D * CΓ * jet2 := mul_le_mul_of_nonneg_left hjet1_le (mul_nonneg hD_nn hCΓ_nn)
      have hgroupB : |(G₁ - G₂) * dΓd₁ + G₂ * (dΓd₁ - dΓd₂)| ≤
          Cinv * R * jet2 + M_b * CdΓ * jet2 := by
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ?_ ?_
        · rw [abs_mul]
          have hG_le : |G₁ - G₂| ≤ Cinv * gd := hCinv a b
          have hdΓd1_le : |dΓd₁| ≤ R := hR a b k
          calc |G₁ - G₂| * |dΓd₁|
              ≤ (Cinv * gd) * R := mul_le_mul hG_le hdΓd1_le (abs_nonneg _)
                  (mul_nonneg hCinv_nn hgd_nn)
            _ = Cinv * R * gd := by ring
            _ ≤ Cinv * R * jet2 := mul_le_mul_of_nonneg_left hgd_le2 (mul_nonneg hCinv_nn hR_nn)
        · rw [abs_mul]
          have hdΓdiff : dΓd₁ - dΓd₂ =
              partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b k) y -
                partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α a b k) y := by
            rw [hdΓd1, hdΓd2]; ring
          calc |G₂| * |dΓd₁ - dΓd₂|
              ≤ M_b * (CdΓ * jet2) := by
                rw [hdΓdiff]
                exact mul_le_mul (hMb a b) (hCdΓ a b k) (abs_nonneg _) hMb_nn
            _ = M_b * CdΓ * jet2 := by ring
      calc |(dG₁ - dG₂) * Γd₁ + dG₂ * (Γd₁ - Γd₂)| +
              |(G₁ - G₂) * dΓd₁ + G₂ * (dΓd₁ - dΓd₂)|
          ≤ (Cd * P * jet2 + D * CΓ * jet2) + (Cinv * R * jet2 + M_b * CdΓ * jet2) :=
            add_le_add hgroupA hgroupB
        _ = C0 * jet2 := by rw [hC0_def]; ring
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : Fin (Module.finrank ℝ E) =>
    (Module.finrank ℝ E : ℝ) * (C0 * jet2)) (fun a _ => hterm a)) ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (Module.finrank ℝ E : ℝ) ^ 2 * C0 * jet2 =
        (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (C0 * jet2)) by ring]

/-- **Uniform Lipschitz dependence of the chart DeTurck-VF component derivatives
`∂_m W^k` on the chart `2`-jet of the metric difference, over a compact subset of
the chart-target interior.**

For two smooth Riemannian metrics `g₁, g₂`, a fixed background metric `g_bg`, a
chart base point `α`, a direction `m`, and a compact subset `K` of the interior of
the chart-`α` target, there is a single constant `C > 0` such that for every
`y ∈ K` and every index `k`,
```
|∂_m W^k(g₁)(y) − ∂_m W^k(g₂)(y)| ≤ C · chartMetricJet2DiffSup g₁ g₂ α y .
```
On a fixed compact `R`-ball of metrics the uniform bounds become uniform over the
ball, so `C` becomes the desired `C(R)`. -/
theorem exists_partialDeriv_chartDeTurckVFComp_lipschitz_on_compact
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M) (m : Fin (Module.finrank ℝ E))
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ k : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g₁ g_bg α k) y -
          partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g₂ g_bg α k) y| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  obtain ⟨hK'_compact, hK'_sub⟩ := symm_image_compact_subset_source (I := I) α hK hKsub
  obtain ⟨Cinv, hCinv_pos, hCinv⟩ :=
    exists_chartInvGramMatrix_lipschitz_on_compact (I := I) (M := M) g₁ g₂ α hK'_compact hK'_sub
  obtain ⟨CΓ, hCΓ_pos, hCΓ⟩ :=
    exists_chartChristoffel_lipschitz_on_compact (I := I) (M := M) g₁ g₂ α hK hKsub
  obtain ⟨CdΓ, hCdΓ_pos, hCdΓ⟩ :=
    exists_chartChristoffelDeriv_lipschitz_on_compact (I := I) (M := M) g₁ g₂ α m hK hKsub
  obtain ⟨Mb1, hMb1_nn, hMb1⟩ := exists_invGramOnE_bound_on_compact (I := I) g₁ α hK hKsub
  obtain ⟨Mb2, hMb2_nn, hMb2⟩ := exists_invGramOnE_bound_on_compact (I := I) g₂ α hK hKsub
  set M_b : ℝ := max Mb1 Mb2 with hMb_def
  have hMb_nn : 0 ≤ M_b := le_max_of_le_left hMb1_nn
  obtain ⟨Q, hQ_nn, hQ⟩ := exists_partial_gramOnE_bound_on_compact (I := I) g₁ α hK hKsub
  obtain ⟨P, hP_nn, hP⟩ :=
    exists_chartChristoffel_diff_bound_on_compact (I := I) g₁ g_bg α hK hKsub
  obtain ⟨D, hD_nn, hD⟩ := exists_partial_invGramOnE_bound_on_compact (I := I) g₂ α hK hKsub
  obtain ⟨R, hR_nn, hR⟩ :=
    exists_partial_chartChristoffel_diff_bound_on_compact (I := I) g₁ g_bg α hK hKsub
  set Cd : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Cinv * M_b * Q + M_b ^ 2) with hCd_def
  have hCd_nn : 0 ≤ Cd := by
    refine mul_nonneg (by positivity) ?_
    have h1 : 0 ≤ 2 * Cinv * M_b * Q := by positivity
    have h2 : 0 ≤ M_b ^ 2 := sq_nonneg _
    linarith
  set C0 : ℝ := Cd * P + D * CΓ + Cinv * R + M_b * CdΓ with hC0_def
  have hC0_nn : 0 ≤ C0 := by
    refine add_nonneg (add_nonneg (add_nonneg (mul_nonneg hCd_nn hP_nn)
      (mul_nonneg hD_nn hCΓ_pos.le)) (mul_nonneg hCinv_pos.le hR_nn))
      (mul_nonneg hMb_nn hCdΓ_pos.le)
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * C0 + 1, ?_, ?_⟩
  · have hnn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * C0 := mul_nonneg (by positivity) hC0_nn
    linarith
  intro y hy k
  have hy_int : y ∈ interior (extChartAt I α).target := hKsub hy
  have hxy_mem : (extChartAt I α).symm y ∈ (extChartAt I α).symm '' K := ⟨y, hy, rfl⟩
  have hCinv' : ∀ a b : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g₁ α a b y - chartInvGramOnE (I := I) g₂ α a b y| ≤
        Cinv * chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) := by
    intro a b
    simpa only [chartInvGramOnE_def] using hCinv ((extChartAt I α).symm y) hxy_mem a b
  have hMb1' : ∀ a b, |chartInvGramOnE (I := I) g₁ α a b y| ≤ M_b :=
    fun a b => (hMb1 y hy a b).trans (le_max_left _ _)
  have hMb2' : ∀ a b, |chartInvGramOnE (I := I) g₂ α a b y| ≤ M_b :=
    fun a b => (hMb2 y hy a b).trans (le_max_right _ _)
  have hCd : ∀ a b : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α a b) y -
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α a b) y| ≤
        Cd * chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y := by
    intro a b
    exact partialDeriv_chartInvGramOnE_sub_abs_le (I := I) (M := M) g₁ g₂ α hy_int
      hMb_nn hQ_nn hCinv_pos.le hMb1' hMb2' (fun mm aa bb => hQ y hy mm aa bb) hCinv' m a b
  have h_pt := partialDeriv_chartDeTurckVFComp_sub_abs_le (I := I) (M := M) g₁ g₂ g_bg α hy_int
    hCd_nn hCinv_pos.le hCΓ_pos.le hMb_nn hP_nn hD_nn hR_nn m k
    hCd hCinv' (fun a b kk => hCΓ y hy a b kk) (fun a b kk => hCdΓ y hy a b kk)
    (fun a b kk => hP y hy a b kk) hMb2' (fun a b => hD y hy m a b)
    (fun a b kk => hR y hy m a b kk)
  have hjet2_nn : 0 ≤ chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y :=
    chartMetricJet2DiffSup_nonneg _ _ _ _
  refine h_pt.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ hjet2_nn
  rw [← hC0_def]
  linarith

/-- The chart-`α` `(i, j)` component of the DeTurck Lie (gauge) summand
`(𝓛_{W(g)} g)_{ij}` at the chart point `y ∈ E`, with the DeTurck vector-field
components `W^k(g) = chartDeTurckVFComp g g_bg α k`. -/
def chartLieDeTurckComp (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      chartDeTurckVFComp (I := I) g g_bg α k y *
        partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y)
  + (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α k j y *
        partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g g_bg α k) y)
  + (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i k y *
        partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g g_bg α k) y)

@[simp] lemma chartLieDeTurckComp_def
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartLieDeTurckComp (I := I) g g_bg α i j y =
      (∑ k : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) g g_bg α k y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y)
      + (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α k j y *
            partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g g_bg α k) y)
      + (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i k y *
            partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g g_bg α k) y) := rfl

/-- A finite-sum difference of products `∑_k A^k₁ B^k₁ − ∑_k A^k₂ B^k₂`, with each
factor difference bounded by a jet seminorm and each factor uniformly bounded, is
bounded by `n·(Ca·Mb + Ma·Cb)·jet`.  This is the shared majorisation skeleton for
all three Lie-summand groups. -/
private lemma sum_prod_sub_abs_le
    {n : ℕ} (A₁ A₂ B₁ B₂ : Fin n → ℝ) {Ca Cb Ma Mb jet : ℝ}
    (hjet_nn : 0 ≤ jet) (hCa_nn : 0 ≤ Ca) (hMa_nn : 0 ≤ Ma)
    (hCa : ∀ k, |A₁ k - A₂ k| ≤ Ca * jet) (hCb : ∀ k, |B₁ k - B₂ k| ≤ Cb * jet)
    (hMa : ∀ k, |A₂ k| ≤ Ma) (hMb : ∀ k, |B₁ k| ≤ Mb) :
    |(∑ k, A₁ k * B₁ k) - (∑ k, A₂ k * B₂ k)| ≤
      (n : ℝ) * ((Ca * Mb + Ma * Cb) * jet) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : Fin n => (Ca * Mb + Ma * Cb) * jet)
    (fun k _ => ?_)) ?_
  · have hsplit : A₁ k * B₁ k - A₂ k * B₂ k =
        (A₁ k - A₂ k) * B₁ k + A₂ k * (B₁ k - B₂ k) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have h1 : |(A₁ k - A₂ k) * B₁ k| ≤ Ca * Mb * jet := by
      rw [abs_mul]
      calc |A₁ k - A₂ k| * |B₁ k|
          ≤ (Ca * jet) * Mb := mul_le_mul (hCa k) (hMb k) (abs_nonneg _)
              (mul_nonneg hCa_nn hjet_nn)
        _ = Ca * Mb * jet := by ring
    have h2 : |A₂ k * (B₁ k - B₂ k)| ≤ Ma * Cb * jet := by
      rw [abs_mul]
      calc |A₂ k| * |B₁ k - B₂ k|
          ≤ Ma * (Cb * jet) := mul_le_mul (hMa k) (hCb k) (abs_nonneg _) hMa_nn
        _ = Ma * Cb * jet := by ring
    calc |(A₁ k - A₂ k) * B₁ k| + |A₂ k * (B₁ k - B₂ k)|
        ≤ Ca * Mb * jet + Ma * Cb * jet := add_le_add h1 h2
      _ = (Ca * Mb + Ma * Cb) * jet := by ring
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]

set_option linter.unusedFintypeInType false in
/-- A direction-uniform `∂_m W^k` Lipschitz constant: a single `C > 0` such that
the bound `|∂_m W^k(g₁)(y) − ∂_m W^k(g₂)(y)| ≤ C · jet2` holds for every direction
`m`, every `y ∈ K`, and every index `k`.  Obtained by taking the maximum over the
finitely many directions of the per-direction constants. -/
private lemma exists_partialDeriv_chartDeTurckVFComp_lipschitz_alldir
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ m k : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g₁ g_bg α k) y -
          partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g₂ g_bg α k) y| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  have hper : ∀ m : Fin (Module.finrank ℝ E), ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K,
      ∀ k : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g₁ g_bg α k) y -
          partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g₂ g_bg α k) y| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := fun m =>
    exists_partialDeriv_chartDeTurckVFComp_lipschitz_on_compact (I := I) (M := M)
      g₁ g₂ g_bg α m hK hKsub
  choose C hC_pos hC using hper
  refine ⟨Finset.univ.sup' Finset.univ_nonempty C, ?_, ?_⟩
  · exact lt_of_lt_of_le (hC_pos (Classical.arbitrary _))
      (Finset.le_sup' C (Finset.mem_univ (Classical.arbitrary _)))
  · intro y hy m k
    refine (hC m y hy k).trans ?_
    refine mul_le_mul_of_nonneg_right (Finset.le_sup' C (Finset.mem_univ m)) ?_
    exact chartMetricJet2DiffSup_nonneg _ _ _ _

/-- **Uniform Lipschitz dependence of the chart-frame DeTurck Lie (gauge) summand
on the chart `2`-jet of the metric difference, over a compact subset of the
chart-target interior.**

For two smooth Riemannian metrics `g₁, g₂`, a fixed background metric `g_bg`, a
chart base point `α`, and a compact subset `K` of the interior of the chart-`α`
target, there is a single constant `C > 0` such that for every `y ∈ K` and all
indices `(i, j)`,
```
|(𝓛_{W(g₁)} g₁)_{ij}(y) − (𝓛_{W(g₂)} g₂)_{ij}(y)| ≤ C · chartMetricJet2DiffSup g₁ g₂ α y ,
```
where `(𝓛_{W(g)} g)_{ij} = chartLieDeTurckComp g g_bg α i j` and the DeTurck vector
field `W(g) = deTurckVF g g_bg` carries `∂g`, so the Lie derivative carries `∂²g`
— a genuine `2`-jet dependence.

The DeTurck vector-field components contribute a `1`-jet Lipschitz factor (their
own difference, via the Christoffel/inverse-Gram perturbation atoms) and a `2`-jet
Lipschitz factor (their first-partial difference, via the Christoffel-derivative
perturbation atom); the metric Gram factors contribute a `0`-jet and a `1`-jet
factor.  On a fixed compact `R`-ball of metrics the uniform bounds become uniform
over the ball, so `C` becomes the desired `C(R)`. -/
theorem exists_chartLieDeTurckComp_lipschitz_on_compact
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
      |chartLieDeTurckComp (I := I) g₁ g_bg α i j y -
          chartLieDeTurckComp (I := I) g₂ g_bg α i j y| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  obtain ⟨Cw, hCw_pos, hCw⟩ :=
    exists_chartDeTurckVFComp_lipschitz_on_compact (I := I) (M := M) g₁ g₂ g_bg α hK hKsub
  obtain ⟨U, hU_nn, hU⟩ := exists_chartDeTurckVFComp_bound_on_compact (I := I) g₂ g_bg α hK hKsub
  obtain ⟨Q, hQ_nn, hQ⟩ := exists_partial_gramOnE_bound_on_compact (I := I) g₁ α hK hKsub
  obtain ⟨Gb, hGb_nn, hGb⟩ := exists_gramOnE_bound_on_compact (I := I) g₂ α hK hKsub
  obtain ⟨Cdw, hCdw_pos, hCdw⟩ :=
    exists_partialDeriv_chartDeTurckVFComp_lipschitz_alldir (I := I) (M := M) g₁ g₂ g_bg α hK hKsub
  obtain ⟨V, hV_nn, hV⟩ :=
    exists_partial_chartDeTurckVFComp_bound_on_compact (I := I) g₁ g_bg α hK hKsub
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  refine ⟨n * ((Cw * Q + U * 1)
      + (1 * V + Gb * Cdw)
      + (1 * V + Gb * Cdw)) + 1, ?_, ?_⟩
  · have hn_nn : 0 ≤ n := by positivity
    have h1 : 0 ≤ Cw * Q := mul_nonneg hCw_pos.le hQ_nn
    have h2 : 0 ≤ U * 1 := by positivity
    have h3 : 0 ≤ 1 * V := by positivity
    have h4 : 0 ≤ Gb * Cdw := mul_nonneg hGb_nn hCdw_pos.le
    have : 0 ≤ n * ((Cw * Q + U * 1) + (1 * V + Gb * Cdw) + (1 * V + Gb * Cdw)) := by
      refine mul_nonneg hn_nn ?_; linarith
    linarith
  intro y hy i j
  have hjet2_nn : 0 ≤ chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y :=
    chartMetricJet2DiffSup_nonneg _ _ _ _
  have hjet1_le : chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y ≤
      chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y :=
    chartMetricJet1DiffSup_le_jet2 (I := I) (M := M) g₁ g₂ α y
  set jet2 : ℝ := chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y with hjet2_def
  have hCw2 : ∀ k : Fin (Module.finrank ℝ E),
      |chartDeTurckVFComp (I := I) g₁ g_bg α k y -
          chartDeTurckVFComp (I := I) g₂ g_bg α k y| ≤ Cw * jet2 := by
    intro k
    refine (hCw y hy k).trans ?_
    exact mul_le_mul_of_nonneg_left hjet1_le hCw_pos.le
  have hG_partial_diff : ∀ k : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y -
          partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y| ≤ 1 * jet2 := by
    intro k
    rw [one_mul]
    refine (partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup (I := I) (M := M)
      g₁ g₂ α y k i j).trans ?_
    exact (chartGramPartialDiffSup_le_jet1 (I := I) (M := M) g₁ g₂ α y).trans hjet1_le
  have hGram_diff : ∀ a b : Fin (Module.finrank ℝ E),
      |chartGramOnE (I := I) g₁ α a b y - chartGramOnE (I := I) g₂ α a b y| ≤ 1 * jet2 := by
    intro a b
    rw [one_mul, chartGramOnE_def, chartGramOnE_def]
    refine (chartGramMatrix_sub_entry_abs_le_gramDiffSup (I := I) (M := M)
      g₁ g₂ α ((extChartAt I α).symm y) a b).trans ?_
    exact (chartGramDiffSup_le_jet1 (I := I) (M := M) g₁ g₂ α y).trans hjet1_le
  rw [chartLieDeTurckComp_def, chartLieDeTurckComp_def]
  have hgroupC :
      |(∑ k, chartDeTurckVFComp (I := I) g₁ g_bg α k y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y) -
        (∑ k, chartDeTurckVFComp (I := I) g₂ g_bg α k y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y)| ≤
        n * ((Cw * Q + U * 1) * jet2) :=
    sum_prod_sub_abs_le
      (A₁ := fun k => chartDeTurckVFComp (I := I) g₁ g_bg α k y)
      (A₂ := fun k => chartDeTurckVFComp (I := I) g₂ g_bg α k y)
      (B₁ := fun k => partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y)
      (B₂ := fun k => partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y)
      hjet2_nn hCw_pos.le hU_nn hCw2 hG_partial_diff
      (fun k => hU y hy k) (fun k => hQ y hy k i j)
  have hgroupD1 :
      |(∑ k, chartGramOnE (I := I) g₁ α k j y *
            partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y) -
        (∑ k, chartGramOnE (I := I) g₂ α k j y *
            partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)| ≤
        n * ((1 * V + Gb * Cdw) * jet2) :=
    sum_prod_sub_abs_le
      (A₁ := fun k => chartGramOnE (I := I) g₁ α k j y)
      (A₂ := fun k => chartGramOnE (I := I) g₂ α k j y)
      (B₁ := fun k => partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y)
      (B₂ := fun k => partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)
      hjet2_nn (by norm_num) hGb_nn (fun k => hGram_diff k j)
      (fun k => hCdw y hy i k) (fun k => hGb y hy k j) (fun k => hV y hy i k)
  have hgroupD2 :
      |(∑ k, chartGramOnE (I := I) g₁ α i k y *
            partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y) -
        (∑ k, chartGramOnE (I := I) g₂ α i k y *
            partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)| ≤
        n * ((1 * V + Gb * Cdw) * jet2) :=
    sum_prod_sub_abs_le
      (A₁ := fun k => chartGramOnE (I := I) g₁ α i k y)
      (A₂ := fun k => chartGramOnE (I := I) g₂ α i k y)
      (B₁ := fun k => partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y)
      (B₂ := fun k => partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)
      hjet2_nn (by norm_num) hGb_nn (fun k => hGram_diff i k)
      (fun k => hCdw y hy j k) (fun k => hGb y hy i k) (fun k => hV y hy j k)
  have habc :
      |((∑ k, chartDeTurckVFComp (I := I) g₁ g_bg α k y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y)
          + (∑ k, chartGramOnE (I := I) g₁ α k j y *
              partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y)
          + (∑ k, chartGramOnE (I := I) g₁ α i k y *
              partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y)) -
        ((∑ k, chartDeTurckVFComp (I := I) g₂ g_bg α k y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y)
          + (∑ k, chartGramOnE (I := I) g₂ α k j y *
              partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)
          + (∑ k, chartGramOnE (I := I) g₂ α i k y *
              partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y))| ≤
        (n * ((Cw * Q + U * 1) * jet2)
          + n * ((1 * V + Gb * Cdw) * jet2))
          + n * ((1 * V + Gb * Cdw) * jet2) := by
    rw [show
        (((∑ k, chartDeTurckVFComp (I := I) g₁ g_bg α k y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y)
          + (∑ k, chartGramOnE (I := I) g₁ α k j y *
              partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y)
          + (∑ k, chartGramOnE (I := I) g₁ α i k y *
              partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y)) -
        ((∑ k, chartDeTurckVFComp (I := I) g₂ g_bg α k y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y)
          + (∑ k, chartGramOnE (I := I) g₂ α k j y *
              partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)
          + (∑ k, chartGramOnE (I := I) g₂ α i k y *
              partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y))) =
        (((∑ k, chartDeTurckVFComp (I := I) g₁ g_bg α k y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y) -
          (∑ k, chartDeTurckVFComp (I := I) g₂ g_bg α k y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y))
          + ((∑ k, chartGramOnE (I := I) g₁ α k j y *
              partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y) -
            (∑ k, chartGramOnE (I := I) g₂ α k j y *
              partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)))
          + ((∑ k, chartGramOnE (I := I) g₁ α i k y *
              partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y) -
            (∑ k, chartGramOnE (I := I) g₂ α i k y *
              partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)) by ring]
    exact (abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add hgroupC hgroupD1)) hgroupD2)
  refine habc.trans ?_
  rw [show (n * ((Cw * Q + U * 1) * jet2) + n * ((1 * V + Gb * Cdw) * jet2)) +
        n * ((1 * V + Gb * Cdw) * jet2) =
      (n * ((Cw * Q + U * 1) + (1 * V + Gb * Cdw) + (1 * V + Gb * Cdw))) * jet2 by ring]
  refine mul_le_mul_of_nonneg_right ?_ hjet2_nn
  linarith

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
