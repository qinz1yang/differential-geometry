import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RealizeMetricChartGramDifference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.IteratedInvGramJetLipschitz

/-!
# Chart-Gram jets of a realized-metric difference are chart jets of the perturbation difference

For two `g_bg`-fibre-small perturbations `T, T'`, the realized metrics
`g₁ = g_bg + h_sym T`, `g₂ = g_bg + h_sym T'` have, on the chart-`α` target interior, a chart-Gram
matrix difference equal to the symmetrized raw chart-`α`-frame `(0,2)`-component of `T − T'`
(`chartGramOnE_realize_sub_eq_symm_rawComponent`).  Because this is an *equality of functions* on the
open chart-target interior, every iterated Fréchet derivative of the chart-Gram difference equals the
corresponding derivative of the symmetrized raw component.  Consequently the all-order chart-jet
seminorm difference `chartGramJetDiffSeminormSum N (realize T) (realize T')` is bounded by the chart
Fréchet jets of the raw chart components of `T − T'`.

This is the foundational chart-jet bridge that lets the chart-jet Faà-di-Bruno Lipschitz towers
(`IteratedChartRicciLieJetLipschitz`, `IteratedInvGramJetLipschitz`), which are phrased in terms of
`chartGramJetDiffSeminormSum`, be driven by the chart Fréchet jets of the perturbation difference.

The result is `δ`-witness independent: a realized metric depends only on `g_bg + h_sym T`, not on the
fibre-small witness `δ`, so any two fibre-small witnesses produce the same chart-Gram data.
-/

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 1600000

open Manifold Set Filter Topology
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The chart-Gram entry of a realized metric is `δ`-witness independent.**
Two fibre-small witnesses `(δ, hδ)`, `(δ', hδ')` for the same perturbation `T` produce realized
metrics with identical chart-`α` Gram entries (the realized metric depends only on `g_bg + h_sym T`,
not on the positivity witness). -/
theorem chartGramOnE_realize_delta_irrel
    (g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ')
    (α : M) (a b : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ) α a b =
      chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T hδ'_lt hδ') α a b := by
  funext y
  simp only [chartGramOnE_def, chartGramMatrix_apply,
    tensorSectionRealizeMetric_inner (I := I) g_bg T hδ_lt hδ,
    tensorSectionRealizeMetric_inner (I := I) g_bg T hδ'_lt hδ']

/-- **The chart-Gram entry difference of two realized metrics equals, on the chart-target interior,
the symmetrized chart-pulled raw component of the perturbation difference.**

On `interior (extChartAt I α).target`, the function
`chartGramOnE (realize T) α a b − chartGramOnE (realize T') α a b` equals
`(1/2)·(rawPullR (T − T') α ![] ![a,b] + rawPullR (T − T') α ![] ![b,a])` composed back through
`toEuclidean`, i.e. its values agree with the symmetrized raw chart-`α` component of `T − T'`. -/
theorem chartGramOnE_realize_sub_eqOn_symm_rawComponent
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ')
    (α : M) (a b : Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (fun y : E => chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)
            α a b y -
          chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T' hδ'_lt hδ') α a b y)
      (fun y : E => (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α ![] ![a, b]
            ((extChartAt I α).symm y) +
          tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α ![] ![b, a]
            ((extChartAt I α).symm y)))
      (interior (extChartAt I α).target) := by
  intro y hy
  have hp_src : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    have hy_t : y ∈ (extChartAt I α).target := interior_subset hy
    have := (extChartAt I α).map_target hy_t
    rwa [extChartAt_source] at this
  have hkey := chartGramOnE_realize_sub_eq_symm_rawComponent_two_witness (I := I) (M := M)
    g_bg T T' hδ_lt hδ hδ'_lt hδ' α a b y hp_src
  simpa using hkey

/-- The chart-pulled raw `(0,2)`-component of a tensor as a function on `E` (the chart target):
`tensorChartComponentRaw g 0 2 S α ![] Jdx ∘ (extChartAt I α).symm`. -/
def rawCompOnE (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] Jdx ((extChartAt I α).symm y)

open DifferentialGeometry.Analysis.Sobolev.Chart in
/-- `rawCompOnE` is `C^∞` on the chart-target interior. -/
lemma rawCompOnE_contDiffOn (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (rawCompOnE (I := I) (M := M) g S α Jdx)
      (interior (extChartAt I α).target) := by
  have h := chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g 0 2 S α
    (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx
  have hcomp := h.comp_continuousLinearMap (toEuclidean (E := E) : E →L[ℝ] _)
  have hsub : interior (extChartAt I α).target ⊆
      (⇑(toEuclidean (E := E) : E →L[ℝ] _)) ⁻¹' chartTargetEuclid (I := I) (M := M) α := by
    intro Y hY
    exact ⟨Y, interior_subset hY, rfl⟩
  have hE := hcomp.mono hsub
  refine hE.congr (fun Y hY => ?_)
  have hYt : Y ∈ (extChartAt I α).target := interior_subset hY
  have hmem : (toEuclidean (E := E)) Y ∈ chartTargetEuclid (I := I) (M := M) α :=
    ⟨Y, hYt, rfl⟩
  show tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] Jdx ((extChartAt I α).symm Y) =
    chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] Jdx)
      ((toEuclidean (E := E)) Y)
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hmem,
    (toEuclidean (E := E)).symm_apply_apply Y]

/-- The `E`-coordinate bare chart-jet content of a `(0,2)`-tensor `S` at chart `α`, point `y`,
order `N`: the sum over the two covariant index pairs of the order-`≤ N` Fréchet jets (within the
chart-target interior) of the raw chart components `rawCompOnE`. -/
def bareChartJetContentOnE (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (N : ℕ) (y : E) : ℝ :=
  ∑ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
    ∑ m ∈ Finset.range (N + 1),
      ‖iteratedFDerivWithin ℝ m (rawCompOnE (I := I) (M := M) g S α Jdx)
        (interior (extChartAt I α).target) y‖

lemma bareChartJetContentOnE_nonneg (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (α : M) (N : ℕ) (y : E) :
    0 ≤ bareChartJetContentOnE (I := I) (M := M) g S α N y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- **The chart-Gram jet-difference seminorm of two realized metrics is bounded by the `E`-coordinate
bare chart-jet content of the perturbation difference.**

On the chart-target interior, for every order `N`,
```
chartGramJetDiffSeminormSum N (realize T) (realize T') α (interior) y
  ≤ ∑_{a,b} iteratedFDerivSeminorm N (½·(rawCompOnE_{ab} + rawCompOnE_{ba})) (interior) y
  ≤ (Module.finrank ℝ E) · bareChartJetContentOnE (T − T') N y .
```
The first step is the chart-Gram difference EqOn identity
(`chartGramOnE_realize_sub_eqOn_symm_rawComponent`) lifted to all Fréchet orders
(`iteratedFDerivWithin_congr`); the second is the triangle inequality on the symmetrized raw
component. -/
theorem chartGramJetDiffSeminormSum_realize_le_bareChartJetContentOnE
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ')
    (α : M) (N : ℕ) {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    chartGramJetDiffSeminormSum (I := I) (M := M) N
        (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)
        (tensorSectionRealizeMetric (I := I) g_bg T' hδ'_lt hδ') α
        (interior (extChartAt I α).target) y ≤
      ((Module.finrank ℝ E) : ℝ) * bareChartJetContentOnE (I := I) (M := M) g_bg (T - T') α N y := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hs_open : IsOpen s := isOpen_interior

  have hpair : ∀ a b : Fin (Module.finrank ℝ E),
      iteratedFDerivSeminorm N
        (fun z => chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)
            α a b z -
          chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T' hδ'_lt hδ') α a b z)
        s y ≤
      ∑ m ∈ Finset.range (N + 1),
        ((1 / 2 : ℝ) *
          (‖iteratedFDerivWithin ℝ m (rawCompOnE (I := I) (M := M) g_bg (T - T') α ![a, b]) s y‖ +
            ‖iteratedFDerivWithin ℝ m (rawCompOnE (I := I) (M := M) g_bg (T - T') α ![b, a]) s y‖)) := by
    intro a b
    refine Finset.sum_le_sum (fun m _ => ?_)

    have hEq := chartGramOnE_realize_sub_eqOn_symm_rawComponent (I := I) (M := M)
      g_bg T T' hδ_lt hδ hδ'_lt hδ' α a b
    have hcongr := iteratedFDerivWithin_congr (𝕜 := ℝ) hEq hy m
    rw [hcongr]

    have hfun_eq : Set.EqOn
        (fun y : E => (1 / 2 : ℝ) *
          (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α ![] ![a, b]
              ((extChartAt I α).symm y) +
            tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α ![] ![b, a]
              ((extChartAt I α).symm y)))
        (fun y : E => (1 / 2 : ℝ) *
          (rawCompOnE (I := I) (M := M) g_bg (T - T') α ![a, b] y +
            rawCompOnE (I := I) (M := M) g_bg (T - T') α ![b, a] y)) s := by
      intro z _; rfl
    rw [iteratedFDerivWithin_congr (𝕜 := ℝ) hfun_eq hy m]

    have hcd_ab : ContDiffOn ℝ ∞ (rawCompOnE (I := I) (M := M) g_bg (T - T') α ![a, b]) s :=
      rawCompOnE_contDiffOn (I := I) (M := M) g_bg (T - T') α ![a, b]
    have hcd_ba : ContDiffOn ℝ ∞ (rawCompOnE (I := I) (M := M) g_bg (T - T') α ![b, a]) s :=
      rawCompOnE_contDiffOn (I := I) (M := M) g_bg (T - T') α ![b, a]
    have hreshape : (fun y : E => (1 / 2 : ℝ) *
          (rawCompOnE (I := I) (M := M) g_bg (T - T') α ![a, b] y +
            rawCompOnE (I := I) (M := M) g_bg (T - T') α ![b, a] y)) =
        (1 / 2 : ℝ) • (fun y : E => rawCompOnE (I := I) (M := M) g_bg (T - T') α ![a, b] y +
            rawCompOnE (I := I) (M := M) g_bg (T - T') α ![b, a] y) := by
      funext z; rw [Pi.smul_apply, smul_eq_mul]
    rw [hreshape,
      iteratedFDerivWithin_const_smul_apply
        (((hcd_ab.add hcd_ba).contDiffWithinAt hy).of_le (by exact_mod_cast le_top))
        hs_open.uniqueDiffOn hy]
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, show |(1 / 2 : ℝ)| = 1 / 2 from by norm_num]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hadd_reshape :
        (fun x : E => rawCompOnE (I := I) (M := M) g_bg (T - T') α ![a, b] x +
            rawCompOnE (I := I) (M := M) g_bg (T - T') α ![b, a] x) =
          rawCompOnE (I := I) (M := M) g_bg (T - T') α ![a, b] +
            rawCompOnE (I := I) (M := M) g_bg (T - T') α ![b, a] := rfl
    rw [hadd_reshape,
      iteratedFDerivWithin_add_apply (hcd_ab.contDiffWithinAt hy |>.of_le (by exact_mod_cast le_top))
        (hcd_ba.contDiffWithinAt hy |>.of_le (by exact_mod_cast le_top)) hs_open.uniqueDiffOn hy]
    exact norm_add_le _ _

  unfold chartGramJetDiffSeminormSum
  refine (Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hpair a b))).trans ?_

  set col : (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ := fun Jdx =>
    ∑ m ∈ Finset.range (N + 1),
      ‖iteratedFDerivWithin ℝ m (rawCompOnE (I := I) (M := M) g_bg (T - T') α Jdx) s y‖
    with hcol_def
  have hcol_nn : ∀ Jdx, 0 ≤ col Jdx := fun Jdx =>
    Finset.sum_nonneg fun m _ => norm_nonneg _

  have hLHS_eq : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ∑ m ∈ Finset.range (N + 1),
          ((1 / 2 : ℝ) *
            (‖iteratedFDerivWithin ℝ m (rawCompOnE (I := I) (M := M) g_bg (T - T') α ![a, b]) s y‖ +
              ‖iteratedFDerivWithin ℝ m (rawCompOnE (I := I) (M := M) g_bg (T - T') α ![b, a]) s y‖))) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (1 / 2 : ℝ) * (col ![a, b] + col ![b, a]) := by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    have hcab : col ![a, b] = ∑ m ∈ Finset.range (N + 1),
        ‖iteratedFDerivWithin ℝ m (rawCompOnE (I := I) (M := M) g_bg (T - T') α ![a, b]) s y‖ := rfl
    have hcba : col ![b, a] = ∑ m ∈ Finset.range (N + 1),
        ‖iteratedFDerivWithin ℝ m (rawCompOnE (I := I) (M := M) g_bg (T - T') α ![b, a]) s y‖ := rfl
    rw [hcab, hcba, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [hLHS_eq]

  have hsum_pair : ∀ f : (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ,
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), f ![a, b]) =
        ∑ Jdx : Fin 2 → Fin (Module.finrank ℝ E), f Jdx := by
    intro f
    rw [← Finset.sum_product']
    refine Fintype.sum_bijective (fun p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
        ![p.1, p.2]) ?_ _ _ ?_
    · refine (finTwoArrowEquiv (Fin (Module.finrank ℝ E))).symm.bijective.comp ?_
      exact Function.bijective_id
    · intro p; rfl
  have hsum_swap : ∀ f : (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ,
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), f ![b, a]) =
        ∑ Jdx : Fin 2 → Fin (Module.finrank ℝ E), f Jdx := by
    intro f
    rw [Finset.sum_comm]
    exact hsum_pair f
  have hcollapse :
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (1 / 2 : ℝ) * (col ![a, b] + col ![b, a])) =
      ∑ Jdx : Fin 2 → Fin (Module.finrank ℝ E), col Jdx := by

    have hsplit : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (1 / 2 : ℝ) * (col ![a, b] + col ![b, a])) =
        (∑ a, ∑ b, (1 / 2 : ℝ) * col ![a, b]) +
          (∑ a, ∑ b, (1 / 2 : ℝ) * col ![b, a]) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [mul_add]
    rw [hsplit, hsum_pair (fun J => (1 / 2 : ℝ) * col J),
      hsum_swap (fun J => (1 / 2 : ℝ) * col J)]
    rw [← Finset.mul_sum]
    ring
  rw [hcollapse]
  have hbare_eq : bareChartJetContentOnE (I := I) (M := M) g_bg (T - T') α N y =
      ∑ Jdx : Fin 2 → Fin (Module.finrank ℝ E), col Jdx := rfl
  rw [hbare_eq]
  have hn1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    have : 1 ≤ Module.finrank ℝ E :=
      Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))
    exact_mod_cast this
  have hbare_nn : 0 ≤ ∑ Jdx : Fin 2 → Fin (Module.finrank ℝ E), col Jdx :=
    Finset.sum_nonneg fun Jdx _ => hcol_nn Jdx
  nlinarith [hbare_nn, hn1]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
