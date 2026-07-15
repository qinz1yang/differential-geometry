import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartRicciStructuralDifference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieSummandLipschitz

/-!
# Single-difference-factor decomposition of the chart DeTurck Lie-summand difference

For a fixed chart base point `α` on a smooth manifold `M`, a fixed background metric
`g_bg`, and two smooth Riemannian metrics `g₁, g₂` (chart Grams `G₁, G₂`), the
chart-frame DeTurck Lie (gauge) summand `chartLieDeTurckComp g g_bg α i j`, i.e. the
classical coordinate expression of `(𝓛_{W(g)} g)_{ij}` with the DeTurck vector field
`W(g) = deTurckVF g g_bg`, is rewritten so that the metric difference
`(𝓛_{W(g₁)} g₁)_{ij} − (𝓛_{W(g₂)} g₂)_{ij}` becomes a finite sum of terms in which
**every summand carries exactly one metric-difference factor**.

This is the Lie/DeTurck-vector-field sibling of the chart Ricci-difference
decomposition (`ChartRicciStructuralDifference.lean`); together the two feed the
per-field Faà-di-Bruno Moser-tame `L²` development of the sealed DeTurck right-hand
side, in which each single-difference factor is majorised by the chart jet seminorm of
`g₁ − g₂` and each plain factor by its uniform bound.

## The two metric dependencies of the Lie summand

`𝓛_{W(g)} g` depends on `g` through **both** the vector field `W(g)` and the metric
being differentiated, so the difference telescopes both dependencies.  The chart
carrier
`(𝓛_{W(g)} g)_{ij} = ∑_k W^k ∂_k G_{ij} + ∑_k G_{kj} ∂_i W^k + ∑_k G_{ik} ∂_j W^k`
splits, group by group, with the product-difference identity
`A₁B₁ − A₂B₂ = (A₁−A₂)B₁ + A₂(B₁−B₂)`, into terms each carrying a single difference
factor — a vector-field-component difference `W^k(g₁) − W^k(g₂)`, a
vector-field-component-partial difference `∂_m W^k(g₁) − ∂_m W^k(g₂)`, a Gram-entry
difference `G₁ − G₂`, or a Gram-first-partial difference `∂G₁ − ∂G₂`.

The vector-field-component difference is itself a single-difference object: the DeTurck
component `W^k(g) = ∑_{a,b} G(g)^{ab} (Γ(g)^k{}_{ab} − Γ(g_bg)^k{}_{ab})` telescopes,
summand by summand, into a term carrying the **inverse-Gram difference**
`G₁^{ab} − G₂^{ab}` (frozen background-relative Christoffel coefficient
`Γ(g₁) − Γ(g_bg)`) plus a term carrying the **Christoffel difference**
`Γ(g₁)^k{}_{ab} − Γ(g₂)^k{}_{ab}` (frozen `g₂` inverse-Gram coefficient).  Each of
those two factors is in turn a single-Gram-difference object via the chart Ricci
brick's atoms `invGramOnE_sub_eq` and `chartChristoffel_sub_eq`; differentiating once
adds the bracket/inverse-Gram-derivative atoms in the usual Leibniz pattern.

## Main results

* `chartDeTurckVFComp_sub_eq` — the telescoped DeTurck vector-field component
  difference (one inverse-Gram-difference term and one Christoffel-difference term per
  index pair).
* `partialDeriv_chartDeTurckVFComp_sub_eq` — the telescoped vector-field-component
  partial-derivative difference, on the chart-target interior.
* `chartLieDeTurckCompZerothGroup_sub_eq`, `chartLieDeTurckCompFirstGroup_sub_eq`,
  `chartLieDeTurckCompSecondGroup_sub_eq` — the three Lie-summand groups, each
  telescoped so every summand carries one difference factor.
* `chartLieDeTurckComp_sub_eq` — **the master identity**: the chart DeTurck Lie-summand
  difference as a finite sum of the three telescoped groups, each carrying exactly one
  vector-field-component(-partial) or Gram(-partial) difference factor, which the
  supporting term-class lemmas expand into single Gram-difference factors.
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

/-! ### The DeTurck vector-field component difference (telescoped) -/

omit [I.Boundaryless] in
/-- **Telescoped DeTurck vector-field component difference.**  At every chart-coordinate
point, the component difference splits, summand by summand over the index pair `(a, b)`,
into a term carrying the inverse-Gram difference `G₁^{ab} − G₂^{ab}` (frozen
background-relative Christoffel coefficient `Γ(g₁)^k{}_{ab} − Γ(g_bg)^k{}_{ab}`) plus a
term carrying the Christoffel difference `Γ(g₁)^k{}_{ab} − Γ(g₂)^k{}_{ab}` (frozen `g₂`
inverse-Gram coefficient).  Each of the two difference factors is itself a
single-difference object via `invGramOnE_sub_eq` and `chartChristoffel_sub_eq`. -/
theorem chartDeTurckVFComp_sub_eq
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckVFComp (I := I) g₁ g_bg α k y -
        chartDeTurckVFComp (I := I) g₂ g_bg α k y =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((chartInvGramOnE (I := I) g₁ α a b y - chartInvGramOnE (I := I) g₂ α a b y) *
            (chartChristoffel (I := I) g₁ α a b k y -
              chartChristoffel (I := I) g_bg α a b k y) +
          chartInvGramOnE (I := I) g₂ α a b y *
            (chartChristoffel (I := I) g₁ α a b k y -
              chartChristoffel (I := I) g₂ α a b k y)) := by
  classical
  rw [chartDeTurckVFComp_def, chartDeTurckVFComp_def, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

omit [BoundarylessManifold I M] in
/-- **Telescoped DeTurck vector-field component partial-derivative difference** on the
chart-target interior.  Differentiating the component formula once
(`partialDeriv_chartDeTurckVFComp_eq`) and telescoping the resulting Leibniz expansion
isolates, for each index pair `(a, b)`, four single-difference factors: the
`∂_m G^{ab}` difference (frozen background-relative Christoffel coefficient), the
Christoffel difference (frozen `g₂` inverse-Gram-derivative coefficient), the `G^{ab}`
difference (frozen background-relative Christoffel-derivative coefficient), and the
Christoffel-derivative difference (frozen `g₂` inverse-Gram coefficient). -/
theorem partialDeriv_chartDeTurckVFComp_sub_eq
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (m k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g₁ g_bg α k) y -
        partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g₂ g_bg α k) y =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α a b) y -
              partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α a b) y) *
            (chartChristoffel (I := I) g₁ α a b k y -
              chartChristoffel (I := I) g_bg α a b k y) +
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α a b) y *
            (chartChristoffel (I := I) g₁ α a b k y -
              chartChristoffel (I := I) g₂ α a b k y) +
          ((chartInvGramOnE (I := I) g₁ α a b y - chartInvGramOnE (I := I) g₂ α a b y) *
              (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b k) y -
                partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y) +
            chartInvGramOnE (I := I) g₂ α a b y *
              (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b k) y -
                partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α a b k) y))) := by
  classical
  rw [partialDeriv_chartDeTurckVFComp_eq (I := I) g₁ g_bg α m k hy,
    partialDeriv_chartDeTurckVFComp_eq (I := I) g₂ g_bg α m k hy,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-! ### The three Lie-summand groups (telescoped) -/

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
/-- **Telescoped zeroth Lie-summand group** `∑_k W^k ∂_k G_{ij}`.  Each summand splits,
via `A₁B₁ − A₂B₂ = (A₁−A₂)B₁ + A₂(B₁−B₂)`, into a term carrying the vector-field
component difference `W^k(g₁) − W^k(g₂)` (frozen `g₁` Gram-first-partial) plus a term
carrying the Gram-first-partial difference `∂_k G₁_{ij} − ∂_k G₂_{ij}` (frozen `g₂`
vector-field component). -/
theorem chartLieDeTurckCompZerothGroup_sub_eq
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I) g₁ g_bg α k y *
          partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y) -
      (∑ k : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I) g₂ g_bg α k y *
          partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y) =
      ∑ k : Fin (Module.finrank ℝ E),
        ((chartDeTurckVFComp (I := I) g₁ g_bg α k y -
              chartDeTurckVFComp (I := I) g₂ g_bg α k y) *
            partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y +
          chartDeTurckVFComp (I := I) g₂ g_bg α k y *
            (partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y -
              partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y)) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
/-- **Telescoped first Lie-summand group** `∑_k G_{kj} ∂_i W^k`.  Each summand splits
into a term carrying the Gram-entry difference `G₁_{kj} − G₂_{kj}` (frozen `g₁`
vector-field-component partial) plus a term carrying the vector-field-component partial
difference `∂_i W^k(g₁) − ∂_i W^k(g₂)` (frozen `g₂` Gram entry). -/
theorem chartLieDeTurckCompFirstGroup_sub_eq
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ α k j y *
          partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y) -
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₂ α k j y *
          partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y) =
      ∑ k : Fin (Module.finrank ℝ E),
        ((chartGramOnE (I := I) g₁ α k j y - chartGramOnE (I := I) g₂ α k j y) *
            partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y +
          chartGramOnE (I := I) g₂ α k j y *
            (partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y -
              partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
/-- **Telescoped second Lie-summand group** `∑_k G_{ik} ∂_j W^k`.  Each summand splits
into a term carrying the Gram-entry difference `G₁_{ik} − G₂_{ik}` (frozen `g₁`
vector-field-component partial) plus a term carrying the vector-field-component partial
difference `∂_j W^k(g₁) − ∂_j W^k(g₂)` (frozen `g₂` Gram entry). -/
theorem chartLieDeTurckCompSecondGroup_sub_eq
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ α i k y *
          partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y) -
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₂ α i k y *
          partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y) =
      ∑ k : Fin (Module.finrank ℝ E),
        ((chartGramOnE (I := I) g₁ α i k y - chartGramOnE (I := I) g₂ α i k y) *
            partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y +
          chartGramOnE (I := I) g₂ α i k y *
            (partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y -
              partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-! ### The master DeTurck Lie-summand difference identity -/

omit [BoundarylessManifold I M] in
/-- **Master single-difference-factor identity for the chart DeTurck Lie-summand
difference.**

At every chart-coordinate point `y`, the chart-frame DeTurck Lie (gauge) summand
difference `(𝓛_{W(g₁)} g₁)_{ij}(y) − (𝓛_{W(g₂)} g₂)_{ij}(y)` splits as the sum of the
three telescoped Lie-summand groups, in which **every summand carries exactly one
vector-field-component(-partial) or Gram(-partial) difference factor**.  The
vector-field-component differences `W^k(g₁) − W^k(g₂)` and their partials are in turn
the single-Gram-difference objects produced by `chartDeTurckVFComp_sub_eq` /
`partialDeriv_chartDeTurckVFComp_sub_eq`, whose factors are the exact inverse-Gram
difference (`invGramOnE_sub_eq`) and the Christoffel(-derivative) difference
(`chartChristoffel_sub_eq` / `partialDeriv_chartChristoffel_sub_eq`); the Gram-entry
and Gram-first-partial differences are the single difference factors themselves.

This is the algebraic kernel for the Lie/DeTurck-vector-field half of the per-field
Faà-di-Bruno Moser-tame `L²` development of the sealed DeTurck right-hand side, the
sibling of `chartRicciTensor_sub_eq_christoffelDiff`. -/
theorem chartLieDeTurckComp_sub_eq
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartLieDeTurckComp (I := I) g₁ g_bg α i j y -
        chartLieDeTurckComp (I := I) g₂ g_bg α i j y =
      (∑ k : Fin (Module.finrank ℝ E),
          ((chartDeTurckVFComp (I := I) g₁ g_bg α k y -
                chartDeTurckVFComp (I := I) g₂ g_bg α k y) *
              partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y +
            chartDeTurckVFComp (I := I) g₂ g_bg α k y *
              (partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y -
                partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y))) +
        (∑ k : Fin (Module.finrank ℝ E),
            ((chartGramOnE (I := I) g₁ α k j y - chartGramOnE (I := I) g₂ α k j y) *
                partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y +
              chartGramOnE (I := I) g₂ α k j y *
                (partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y -
                  partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y))) +
          (∑ k : Fin (Module.finrank ℝ E),
            ((chartGramOnE (I := I) g₁ α i k y - chartGramOnE (I := I) g₂ α i k y) *
                partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y +
              chartGramOnE (I := I) g₂ α i k y *
                (partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y -
                  partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y))) := by
  classical
  rw [chartLieDeTurckComp_def, chartLieDeTurckComp_def]
  rw [show ((∑ k, chartDeTurckVFComp (I := I) g₁ g_bg α k y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y) +
            (∑ k, chartGramOnE (I := I) g₁ α k j y *
                partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y) +
            (∑ k, chartGramOnE (I := I) g₁ α i k y *
                partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y)) -
          ((∑ k, chartDeTurckVFComp (I := I) g₂ g_bg α k y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y) +
            (∑ k, chartGramOnE (I := I) g₂ α k j y *
                partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y) +
            (∑ k, chartGramOnE (I := I) g₂ α i k y *
                partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)) =
        ((∑ k, chartDeTurckVFComp (I := I) g₁ g_bg α k y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y) -
            (∑ k, chartDeTurckVFComp (I := I) g₂ g_bg α k y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y)) +
          (((∑ k, chartGramOnE (I := I) g₁ α k j y *
                  partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y) -
              (∑ k, chartGramOnE (I := I) g₂ α k j y *
                  partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)) +
            ((∑ k, chartGramOnE (I := I) g₁ α i k y *
                  partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y) -
              (∑ k, chartGramOnE (I := I) g₂ α i k y *
                  partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y))) from by
        ring]
  rw [chartLieDeTurckCompZerothGroup_sub_eq (I := I) g₁ g₂ g_bg α i j y,
    chartLieDeTurckCompFirstGroup_sub_eq (I := I) g₁ g₂ g_bg α i j y,
    chartLieDeTurckCompSecondGroup_sub_eq (I := I) g₁ g₂ g_bg α i j y]
  ring

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
