import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieSummandLipschitz
import DifferentialGeometry.PDE.DeTurck.DeTurckVFChartCoord
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric

/-!
# The Cartan-formula Lie matrix equals the textbook Christoffel Lie–DeTurck carrier

For two smooth Riemannian metrics `g` and `g_bg`, the DeTurck vector field
`W = deTurckVF g g_bg` has two parallel chart-coordinate descriptions of the
metric Lie-derivative component `(𝓛_W g)_{ij}`:

* the **abstract Cartan-formula chart matrix** `chartLieDerivMetricMatrix g W α i j x`,
  built from the bundled section's chart components `chartCoeff α W k`
  (`PDE/DeTurck/LieDerivativeMetric.lean`);
* the **textbook Christoffel carrier** `chartLieDeTurckComp g g_bg α i j (ϕ_α x)`,
  built from the explicit DeTurck-VF component function `chartDeTurckVFComp g g_bg α k`
  (`PDE/RicciFlow/IntrinsicSpectral/DeTurckCoefficients/LieSummandLipschitz.lean`).

Both compute the classical coordinate expression
`(𝓛_W g)_{ij} = W^k ∂_k g_{ij} + g_{kj} ∂_i W^k + g_{ik} ∂_j W^k`, so they must
agree.  The agreement is the chart-coordinate computation carried out here: on the
chart-`α` Levi-Civita good set `chartLeviCivitaGoodSet α` (off-centre points), the
two matrices coincide term by term.

## Strategy

The two carriers have different building blocks, identified by three facts proved
on the good set:

* the **vector-field component** matches the textbook one:
  `chartCoeff α W k x = chartDeTurckVFComp g g_bg α k (ϕ_α x)`, extracted from the
  bundled chart expansion `deTurckVF_apply_eq_chartDeTurckVFComp_sum`;
* the **Gram matrix** matches the pulled-back Gram density:
  `chartGramMatrix g α x k j = chartGramOnE g α k j (ϕ_α x)`, by the chart-inverse
  round-trip;
* the **vector-field partial derivative** matches: the two component functions
  `chartCoeffOnE α W k` and `chartDeTurckVFComp g g_bg α k` agree on the (open) chart
  image of the good set, hence have equal Fréchet partial derivatives at `ϕ_α x`.

## Main results

* `chartCoeff_eq_repr_trivToE` — on the trivialization base set, the chart component
  `chartCoeff α X k x` is the `k`-th model-basis coordinate of the trivialised section
  value `trivToE α x (X x)`.
* `chartCoeff_deTurckVF_eq_chartDeTurckVFComp` — on the good set, the bundled
  DeTurck-VF chart component equals the textbook component function:
  `chartCoeff α (deTurckVF g g_bg) k x = chartDeTurckVFComp g g_bg α k (ϕ_α x)`.
* `chartCoeffOnE_deTurckVF_eqOn_goodSet_image` — the two component functions agree on
  the chart image of the good set.
* `chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp` — the headline bridge:
  on the good set,
  `chartLieDerivMetricMatrix g (deTurckVF g g_bg) α i j x
     = chartLieDeTurckComp g g_bg α i j (ϕ_α x)`.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff Matrix BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

/-- **The chart component is the model-basis coordinate of the trivialised value.**
On the trivialization base set at `α`, `chartCoeff α X k x` equals the `k`-th
`chartModelBasis E`-coordinate of `trivToE α x (X x)`.  The continuous-linear
trivialisation map `trivToE α x` agrees with the trivialisation's second component
`(triv ⟨x, X x⟩).2` on the base set, which is exactly the value the chart component
extracts. -/
lemma chartCoeff_eq_repr_trivToE (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartCoeff (I := I) α X k x =
      ((chartModelBasis E).repr (trivToE (I := I) α x (X x))) k := by
  rw [chartCoeff_def]
  congr 1
  rw [trivToE,
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt_apply ℝ,
    (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem hx]

/-- **The bundled DeTurck-VF chart component equals the textbook component
function.**  On `chartLeviCivitaGoodSet α`,
`chartCoeff α (deTurckVF g g_bg) k x = chartDeTurckVFComp g g_bg α k (ϕ_α x)`.

The bundled section expands (by `deTurckVF_apply_eq_chartDeTurckVFComp_sum`) as
`(deTurckVF g g_bg) x = ∑ p, chartDeTurckVFComp g g_bg α p (ϕ_α x) • chartBasisVecFiber α p x`;
applying the (fiberwise-linear) trivialisation sends each `chartBasisVecFiber α p x`
to the model-basis vector `(chartModelBasis E) p`, so the `k`-th model-basis
coordinate of the sum collapses to `chartDeTurckVFComp g g_bg α k (ϕ_α x)`. -/
theorem chartCoeff_deTurckVF_eq_chartDeTurckVFComp
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartCoeff (I := I) α (deTurckVF (I := I) g g_bg) k x =
      chartDeTurckVFComp (I := I) g g_bg α k (extChartAt I α x) := by
  classical
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  rw [chartCoeff_eq_repr_trivToE (I := I) α (deTurckVF (I := I) g g_bg) k hx_base]
  rw [deTurckVF_apply_eq_chartDeTurckVFComp_sum (I := I) g g_bg α hx]
  rw [map_sum]
  rw [map_sum]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  have hbasis : ∀ p : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (trivToE (I := I) α x
          (chartDeTurckVFComp (I := I) g g_bg α p (extChartAt I α x) •
            chartBasisVecFiber (I := I) α p x))) k =
        (if p = k then chartDeTurckVFComp (I := I) g g_bg α p (extChartAt I α x)
          else 0) := by
    intro p
    rw [map_smul]
    have htriv : trivToE (I := I) α x (chartBasisVecFiber (I := I) α p x) =
        (chartModelBasis E) p := by
      have : chartBasisVecFiber (I := I) α p x =
          trivFromE (I := I) α x ((chartModelBasis E) p) := rfl
      rw [this, trivToE_trivFromE (I := I) α hx_base ((chartModelBasis E) p)]
    rw [htriv, map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_apply, smul_eq_mul]
    by_cases hpk : p = k
    · rw [if_pos hpk, if_pos hpk, mul_one]
    · rw [if_neg hpk, if_neg hpk, mul_zero]
  rw [Finset.sum_congr rfl (fun p _ => hbasis p)]
  rw [Finset.sum_ite_eq' Finset.univ k
    (fun p => chartDeTurckVFComp (I := I) g g_bg α p (extChartAt I α x))]
  rw [if_pos (Finset.mem_univ k)]

/-- **The two DeTurck-VF chart functions agree on the chart image of the good set.**
For every `y ∈ (extChartAt I α) '' chartLeviCivitaGoodSet α`,
`chartCoeffOnE α (deTurckVF g g_bg) k y = chartDeTurckVFComp g g_bg α k y`.  Writing
`y = ϕ_α b` for `b` in the good set, the chart-inverse round-trip
`(extChartAt I α).symm (ϕ_α b) = b` reduces the left side to the bundled chart
component at `b`, which equals the textbook component at `ϕ_α b` by
`chartCoeff_deTurckVF_eq_chartDeTurckVFComp`. -/
theorem chartCoeffOnE_deTurckVF_eqOn_goodSet_image
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    Set.EqOn (chartCoeffOnE (I := I) α (deTurckVF (I := I) g g_bg) k)
      (chartDeTurckVFComp (I := I) g g_bg α k)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  rintro y ⟨b, hb_good, rfl⟩
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb_good
  rw [chartCoeffOnE, (extChartAt I α).left_inv hb_src]
  exact chartCoeff_deTurckVF_eq_chartDeTurckVFComp (I := I) g g_bg α k hb_good

/-- **Equality of the Fréchet partial derivatives of the two DeTurck-VF chart
functions at a good-set chart point.**  Since the two functions agree on the open
chart image of the good set (`chartCoeffOnE_deTurckVF_eqOn_goodSet_image`), which is
a neighbourhood of `ϕ_α x` for `x` in the good set, their partial derivatives in
every model-basis direction `m` at `ϕ_α x` coincide. -/
theorem partialDeriv_chartCoeffOnE_deTurckVF_eq
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (m k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    partialDeriv (E := E) m
        (chartCoeffOnE (I := I) α (deTurckVF (I := I) g g_bg) k) (extChartAt I α x) =
      partialDeriv (E := E) m
        (chartDeTurckVFComp (I := I) g g_bg α k) (extChartAt I α x) := by
  have hU_open : IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : extChartAt I α x ∈
      (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α := ⟨x, hx, rfl⟩
  have heqOn := chartCoeffOnE_deTurckVF_eqOn_goodSet_image (I := I) g g_bg α k
  have heventually :
      chartCoeffOnE (I := I) α (deTurckVF (I := I) g g_bg) k =ᶠ[𝓝 (extChartAt I α x)]
        chartDeTurckVFComp (I := I) g g_bg α k :=
    heqOn.eventuallyEq_of_mem (hU_open.mem_nhds hx_mem)
  rw [partialDeriv, partialDeriv, heventually.fderiv_eq]

/-- **The Cartan-formula Lie matrix equals the textbook Christoffel Lie–DeTurck
carrier.**  For the DeTurck vector field `W = deTurckVF g g_bg` and a point `x` in
the chart-`α` Levi-Civita good set,
```
chartLieDerivMetricMatrix g W α i j x = chartLieDeTurckComp g g_bg α i j (ϕ_α x).
```
Both are the classical coordinate expression
`(𝓛_W g)_{ij} = W^k ∂_k g_{ij} + g_{kj} ∂_i W^k + g_{ik} ∂_j W^k`; the abstract
matrix uses the bundled chart components `chartCoeff α W k` and Gram entries
`chartGramMatrix g α x`, the textbook carrier uses `chartDeTurckVFComp g g_bg α k`
and `chartGramOnE g α`.  The three pieces match on the good set:
`chartCoeff α W k x = chartDeTurckVFComp g g_bg α k (ϕ_α x)`,
`chartGramMatrix g α x = chartGramOnE g α (ϕ_α x)`, and the corresponding
partial-derivative factors agree by locality of the Fréchet derivative. -/
theorem chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartLieDerivMetricMatrix (I := I) g (deTurckVF (I := I) g g_bg) α i j x =
      chartLieDeTurckComp (I := I) g g_bg α i j (extChartAt I α x) := by
  classical
  have hx_src : x ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  have hgram : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramMatrix (I := I) g α x a b =
        chartGramOnE (I := I) g α a b (extChartAt I α x) := by
    intro a b
    rw [chartGramOnE, (extChartAt I α).left_inv hx_src]
  rw [chartLieDerivMetricMatrix_def, chartLieDeTurckComp_def]
  refine congr_arg₂ (· + ·) (congr_arg₂ (· + ·) ?_ ?_) ?_
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartCoeff_deTurckVF_eq_chartDeTurckVFComp (I := I) g g_bg α k hx]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hgram k j,
      partialDeriv_chartCoeffOnE_deTurckVF_eq (I := I) g g_bg α i k hx]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hgram i k,
      partialDeriv_chartCoeffOnE_deTurckVF_eq (I := I) g g_bg α j k hx]

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
