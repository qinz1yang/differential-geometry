import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChristoffelPerturbation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RicciDiffAffine
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Single-difference-factor decomposition of the chart Ricci-tensor difference

For a fixed chart base point `α` on a smooth manifold `M` and two smooth Riemannian
metrics `g₁, g₂`, the chart-frame scalar Ricci difference
`Rc(g₁)_{ik}(y) − Rc(g₂)_{ik}(y)` is rewritten as a finite sum of terms in which
**every summand carries exactly one metric-difference factor** — a chart-Gram entry
difference `G₁ − G₂`, a first-partial difference `∂G₁ − ∂G₂`, or a second-partial
difference `∂²G₁ − ∂²G₂` — with the remaining factors being plain (undifferenced)
inverse-Gram, Gram-partial or Gram-second-partial data of `g₁` or `g₂`.

This is the purely algebraic decomposition feeding the per-field Faà-di-Bruno
Moser-tame `L²` development of the sealed `ricciTensor` difference: the bound brick
majorises each single-difference factor by the chart jet seminorm of `g₁ − g₂` and
each plain factor by its uniform bound.

## Telescoping atoms

The expression `Rc = ∑_j R^j{}_{ijk}` is, through `chartRiemannTensor`, a finite sum
of `∂Γ` terms and `Γ·Γ` terms in the chart Christoffel symbols `Γ^k_{ij}`.  Each
Christoffel symbol is `Γ^k_{ij}(g) = ½ ∑_l G^{kl}(g) · S^g_{ij,l}`, where
`G^{kl} = chartInvGramOnE g k l` and `S^g_{ij,l} = gramBracket g i j l`.  The
difference of a product telescopes as `A₁B₁ − A₂B₂ = (A₁−A₂)B₁ + A₂(B₁−B₂)`, isolating
single difference factors at every layer:

* the inverse-Gram difference `G₁^{kl} − G₂^{kl}` is the **exact** matrix-inversion
  identity `= ∑_{p,q} G₁^{kp} (G₂−G₁)_{pq} G₂^{ql}` (one `(G₂−G₁)_{pq}` factor each);
* the bracket difference `S^{g₁}_{ij,l} − S^{g₂}_{ij,l}` is a signed sum of three
  Gram-first-partial differences;
* the bracket-derivative difference is a signed sum of three Gram-second-partial
  differences.

## Main results

* `invGramOnE_sub_eq` — the exact entrywise inverse-Gram difference identity (on the
  chart-target interior, where the Gram matrices are invertible).
* `gramBracket_sub_eq`, `gramBracketDeriv_sub_eq` — the bracket and bracket-derivative
  differences as three single-difference factors each.
* `chartChristoffel_sub_eq` — the telescoped Christoffel difference (one difference
  factor per term).
* `partialDeriv_chartChristoffel_sub_eq` — the telescoped Christoffel-derivative
  difference on the chart-target interior.
* `chartRicciTensor_sub_eq_christoffelDiff` — **the master identity**: the chart Ricci
  difference as a finite sum of `∂Γ`-difference terms and `Γ·Γ`-difference terms, each
  carrying one Christoffel(-derivative) difference factor, which the supporting atoms
  expand into single Gram-difference factors.
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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The inverse-Gram entry difference (exact) -/

/-- **Exact entrywise inverse-Gram difference identity.**  At a chart-target-interior
point `y`, with `x := (extChartAt I α).symm y` in the chart base set so that both Gram
matrices are invertible, the inverse-Gram entry difference is the matrix-inversion
perturbation
`G₁^{kl}(y) − G₂^{kl}(y) = ∑_q ∑_p G₁^{kp}(y) · (G₂ − G₁)_{pq}(y) · G₂^{ql}(y)`,
where `(G₂ − G₁)_{pq}(y) = chartGramOnE g₂ α p q y − chartGramOnE g₁ α p q y` is the
single (undifferentiated) metric-difference factor in each summand. -/
theorem invGramOnE_sub_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y =
      ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₁ α k p y *
          (chartGramOnE (I := I) g₂ α p q y - chartGramOnE (I := I) g₁ α p q y) *
          chartInvGramOnE (I := I) g₂ α q l y := by
  classical
  set x : M := (extChartAt I α).symm y with hx_def
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    symm_mem_baseSet_of_mem_interior_target (I := I) α hy
  have hA_unit : IsUnit (chartGramMatrix (I := I) g₁ α x) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt (chartGramMatrix_det_pos (I := I) g₁ α hx_base))
  have hB_unit : IsUnit (chartGramMatrix (I := I) g₂ α x) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt (chartGramMatrix_det_pos (I := I) g₂ α hx_base))
  have hAB : IsUnit (chartGramMatrix (I := I) g₁ α x) ↔
      IsUnit (chartGramMatrix (I := I) g₂ α x) := ⟨fun _ => hB_unit, fun _ => hA_unit⟩
  have h_id : (chartGramMatrix (I := I) g₁ α x)⁻¹ - (chartGramMatrix (I := I) g₂ α x)⁻¹ =
      (chartGramMatrix (I := I) g₁ α x)⁻¹ *
        (chartGramMatrix (I := I) g₂ α x - chartGramMatrix (I := I) g₁ α x) *
        (chartGramMatrix (I := I) g₂ α x)⁻¹ := Matrix.inv_sub_inv hAB
  have h_entry :
      (chartGramMatrix (I := I) g₁ α x)⁻¹ k l - (chartGramMatrix (I := I) g₂ α x)⁻¹ k l =
        ((chartGramMatrix (I := I) g₁ α x)⁻¹ *
          (chartGramMatrix (I := I) g₂ α x - chartGramMatrix (I := I) g₁ α x) *
          (chartGramMatrix (I := I) g₂ α x)⁻¹) k l := by
    have := congrArg (fun X : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ =>
      X k l) h_id
    simpa using this
  have h_expand :
      ((chartGramMatrix (I := I) g₁ α x)⁻¹ *
          (chartGramMatrix (I := I) g₂ α x - chartGramMatrix (I := I) g₁ α x) *
          (chartGramMatrix (I := I) g₂ α x)⁻¹) k l =
        ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (chartGramMatrix (I := I) g₁ α x)⁻¹ k p *
            (chartGramMatrix (I := I) g₂ α x - chartGramMatrix (I := I) g₁ α x) p q *
            (chartGramMatrix (I := I) g₂ α x)⁻¹ q l := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_mul]
  have hkey :
      chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y =
        ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (chartGramMatrix (I := I) g₁ α x)⁻¹ k p *
            (chartGramMatrix (I := I) g₂ α x - chartGramMatrix (I := I) g₁ α x) p q *
            (chartGramMatrix (I := I) g₂ α x)⁻¹ q l := by
    rw [show chartInvGramOnE (I := I) g₁ α k l y = (chartGramMatrix (I := I) g₁ α x)⁻¹ k l from rfl,
      show chartInvGramOnE (I := I) g₂ α k l y = (chartGramMatrix (I := I) g₂ α x)⁻¹ k l from rfl,
      h_entry, h_expand]
  rw [hkey]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [show chartInvGramOnE (I := I) g₁ α k p y = (chartGramMatrix (I := I) g₁ α x)⁻¹ k p from rfl,
    show chartInvGramOnE (I := I) g₂ α q l y = (chartGramMatrix (I := I) g₂ α x)⁻¹ q l from rfl,
    show chartGramOnE (I := I) g₂ α p q y = chartGramMatrix (I := I) g₂ α x p q from rfl,
    show chartGramOnE (I := I) g₁ α p q y = chartGramMatrix (I := I) g₁ α x p q from rfl,
    Matrix.sub_apply]

/-! ### The bracket and bracket-derivative differences -/

/-- **The `gramBracket` difference as three single-partial-difference factors.**  At
every chart-coordinate point,
`S^{g₁}_{ij,l}(y) − S^{g₂}_{ij,l}(y)` equals the signed sum of the three Gram
first-partial differences `∂_i ΔG_{lj} + ∂_j ΔG_{li} − ∂_l ΔG_{ij}`, each isolating a
single difference factor `∂G₁ − ∂G₂`. -/
theorem gramBracket_sub_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) (y : E) :
    gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y =
      (partialDeriv (E := E) i (chartGramOnE (I := I) g₁ α l j) y -
          partialDeriv (E := E) i (chartGramOnE (I := I) g₂ α l j) y) +
        (partialDeriv (E := E) j (chartGramOnE (I := I) g₁ α l i) y -
          partialDeriv (E := E) j (chartGramOnE (I := I) g₂ α l i) y) -
        (partialDeriv (E := E) l (chartGramOnE (I := I) g₁ α i j) y -
          partialDeriv (E := E) l (chartGramOnE (I := I) g₂ α i j) y) := by
  unfold gramBracket
  ring

/-- **The `gramBracketDeriv` difference as three single-second-partial-difference
factors.**  At every chart-coordinate point,
`∂_m S^{g₁}_{ij,l}(y) − ∂_m S^{g₂}_{ij,l}(y)` equals the signed sum of the three
Gram second-partial differences, each isolating a single difference factor
`∂²G₁ − ∂²G₂`. -/
theorem gramBracketDeriv_sub_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (m i j l : Fin (Module.finrank ℝ E)) (y : E) :
    gramBracketDeriv (I := I) g₁ α m i j l y - gramBracketDeriv (I := I) g₂ α m i j l y =
      (partialDeriv (E := E) m (partialDeriv (E := E) i (chartGramOnE (I := I) g₁ α l j)) y -
          partialDeriv (E := E) m
            (partialDeriv (E := E) i (chartGramOnE (I := I) g₂ α l j)) y) +
        (partialDeriv (E := E) m (partialDeriv (E := E) j (chartGramOnE (I := I) g₁ α l i)) y -
          partialDeriv (E := E) m
            (partialDeriv (E := E) j (chartGramOnE (I := I) g₂ α l i)) y) -
        (partialDeriv (E := E) m (partialDeriv (E := E) l (chartGramOnE (I := I) g₁ α i j)) y -
          partialDeriv (E := E) m
            (partialDeriv (E := E) l (chartGramOnE (I := I) g₂ α i j)) y) := by
  unfold gramBracketDeriv
  ring

/-! ### The Christoffel difference (telescoped) -/

/-- **Telescoped chart Christoffel difference.**  At every chart-coordinate point, the
Christoffel difference splits, summand by summand, into a term carrying the inverse-Gram
difference `G₁^{kl} − G₂^{kl}` (frozen `g₁` bracket coefficient) plus a term carrying the
bracket difference `S^{g₁}_{ij,l} − S^{g₂}_{ij,l}` (frozen `g₂` inverse-Gram
coefficient).  Each of the two difference factors is itself a single-difference object
via `invGramOnE_sub_eq` and `gramBracket_sub_eq`. -/
theorem chartChristoffel_sub_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g₁ α i j k y - chartChristoffel (I := I) g₂ α i j k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        ((chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y) *
            gramBracket (I := I) g₁ α i j l y +
          chartInvGramOnE (I := I) g₂ α k l y *
            (gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y)) := by
  classical
  rw [chartChristoffel_eq_sum_invGramOnE_bracket, chartChristoffel_eq_sum_invGramOnE_bracket,
    ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

/-- **Telescoped chart Christoffel-derivative difference** on the chart-target interior.
Differentiating the Christoffel formula once (`partialDeriv_chartChristoffel_eq`) and
telescoping the resulting four-product Leibniz expansion isolates, for each `l`, the four
single-difference factors:
`∂_m G^{kl}` difference, bracket difference, `G^{kl}` difference, and bracket-derivative
difference, each with a frozen coefficient from `g₁` or `g₂`. -/
theorem partialDeriv_chartChristoffel_sub_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (m i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α i j k) y -
        partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α i j k) y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        ((partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y -
              partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y) *
            gramBracket (I := I) g₁ α i j l y +
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y *
            (gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y) +
          ((chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y) *
              gramBracketDeriv (I := I) g₁ α m i j l y +
            chartInvGramOnE (I := I) g₂ α k l y *
              (gramBracketDeriv (I := I) g₁ α m i j l y -
                gramBracketDeriv (I := I) g₂ α m i j l y))) := by
  classical
  rw [partialDeriv_chartChristoffel_eq (I := I) g₁ α m i j k hy,
    partialDeriv_chartChristoffel_eq (I := I) g₂ α m i j k hy,
    ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

/-! ### The master Ricci-difference identity -/

/-- The second-order (`∂Γ`) part of the chart Ricci difference, written as a sum over `j`
of Christoffel-derivative differences (one such difference factor per summand). -/
theorem chartRicciSecondOrderTerm_sub_eq_christoffelDerivDiff
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderTerm (I := I) g₁ α i k y -
        chartRicciSecondOrderTerm (I := I) g₂ α i k y =
      ∑ j : Fin (Module.finrank ℝ E),
        ((partialDeriv (E := E) j (chartChristoffel (I := I) g₁ α i k j) y -
              partialDeriv (E := E) j (chartChristoffel (I := I) g₂ α i k j) y) -
          (partialDeriv (E := E) k (chartChristoffel (I := I) g₁ α i j j) y -
            partialDeriv (E := E) k (chartChristoffel (I := I) g₂ α i j j) y)) := by
  classical
  rw [chartRicciSecondOrderTerm, chartRicciSecondOrderTerm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- The first-order (`Γ·Γ`) part of the chart Ricci difference, written as a sum over
`(j, m)` of telescoped products in which each summand carries exactly one Christoffel
difference factor (via `A₁B₁ − A₂B₂ = (A₁−A₂)B₁ + A₂(B₁−B₂)`). -/
theorem chartRicciFirstOrderTerm_sub_eq_christoffelDiff
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciFirstOrderTerm (I := I) g₁ α i k y -
        chartRicciFirstOrderTerm (I := I) g₂ α i k y =
      ∑ j : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        (((chartChristoffel (I := I) g₁ α j m j y -
                chartChristoffel (I := I) g₂ α j m j y) *
              chartChristoffel (I := I) g₁ α i k m y +
            chartChristoffel (I := I) g₂ α j m j y *
              (chartChristoffel (I := I) g₁ α i k m y -
                chartChristoffel (I := I) g₂ α i k m y)) -
          ((chartChristoffel (I := I) g₁ α k m j y -
                chartChristoffel (I := I) g₂ α k m j y) *
              chartChristoffel (I := I) g₁ α i j m y +
            chartChristoffel (I := I) g₂ α k m j y *
              (chartChristoffel (I := I) g₁ α i j m y -
                chartChristoffel (I := I) g₂ α i j m y))) := by
  classical
  rw [chartRicciFirstOrderTerm, chartRicciFirstOrderTerm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  ring

/-- **Master single-difference-factor identity for the chart Ricci difference.**

At every chart-coordinate point `y`, the chart-frame scalar Ricci difference splits as a
finite sum of `∂Γ`-difference terms (the second-order part) and `Γ·Γ`-difference terms
(the first-order part), in which **every summand carries exactly one Christoffel or
Christoffel-derivative difference factor**.  Those Christoffel(-derivative) differences
are in turn the single-Gram-difference objects produced by the telescoping atoms
`chartChristoffel_sub_eq` / `partialDeriv_chartChristoffel_sub_eq`, whose factors are the
exact inverse-Gram difference (`invGramOnE_sub_eq`), the bracket difference
(`gramBracket_sub_eq`), and the bracket-derivative difference (`gramBracketDeriv_sub_eq`).

This is the algebraic kernel consumed by the per-field Faà-di-Bruno Moser-tame `L²`
development of the sealed `ricciTensor` difference. -/
theorem chartRicciTensor_sub_eq_christoffelDiff
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciTensor (I := I) g₁ α i k y - chartRicciTensor (I := I) g₂ α i k y =
      (∑ j : Fin (Module.finrank ℝ E),
          ((partialDeriv (E := E) j (chartChristoffel (I := I) g₁ α i k j) y -
                partialDeriv (E := E) j (chartChristoffel (I := I) g₂ α i k j) y) -
            (partialDeriv (E := E) k (chartChristoffel (I := I) g₁ α i j j) y -
              partialDeriv (E := E) k (chartChristoffel (I := I) g₂ α i j j) y))) +
        (∑ j : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (((chartChristoffel (I := I) g₁ α j m j y -
                  chartChristoffel (I := I) g₂ α j m j y) *
                chartChristoffel (I := I) g₁ α i k m y +
              chartChristoffel (I := I) g₂ α j m j y *
                (chartChristoffel (I := I) g₁ α i k m y -
                  chartChristoffel (I := I) g₂ α i k m y)) -
            ((chartChristoffel (I := I) g₁ α k m j y -
                  chartChristoffel (I := I) g₂ α k m j y) *
                chartChristoffel (I := I) g₁ α i j m y +
              chartChristoffel (I := I) g₂ α k m j y *
                (chartChristoffel (I := I) g₁ α i j m y -
                  chartChristoffel (I := I) g₂ α i j m y)))) := by
  rw [chartRicciTensor_eq_secondOrder_add_firstOrder (I := I) g₁ α i k y,
    chartRicciTensor_eq_secondOrder_add_firstOrder (I := I) g₂ α i k y]
  rw [show chartRicciSecondOrderTerm (I := I) g₁ α i k y +
            chartRicciFirstOrderTerm (I := I) g₁ α i k y -
          (chartRicciSecondOrderTerm (I := I) g₂ α i k y +
            chartRicciFirstOrderTerm (I := I) g₂ α i k y) =
        (chartRicciSecondOrderTerm (I := I) g₁ α i k y -
            chartRicciSecondOrderTerm (I := I) g₂ α i k y) +
          (chartRicciFirstOrderTerm (I := I) g₁ α i k y -
            chartRicciFirstOrderTerm (I := I) g₂ α i k y) from by ring]
  rw [chartRicciSecondOrderTerm_sub_eq_christoffelDerivDiff (I := I) g₁ g₂ α i k y,
    chartRicciFirstOrderTerm_sub_eq_christoffelDiff (I := I) g₁ g₂ α i k y]

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
