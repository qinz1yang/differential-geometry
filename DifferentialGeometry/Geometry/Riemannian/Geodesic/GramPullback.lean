import DifferentialGeometry.Geometry.Hessian
import DifferentialGeometry.Geometry.Riemannian.Geodesic.ChartTransition
import DifferentialGeometry.Integral.Measure.Invariance

set_option linter.unusedSectionVars false
set_option linter.style.show false

/-!
# Gram-matrix pullback under the chart-transition map

For two basepoints `α β : M` on a smooth Riemannian manifold and a chart-target
point `x : E` lying in the chart-α image of the chart-α-β overlap, the
chart-coordinate Gram matrix at the chart-β picture decomposes against the
chart-α picture via the Fréchet derivative of the chart-transition map.

This file packages two equivalent forms of the resulting identity:

* `chartTransitionAtEntry α β x i a` — the `(i, a)` entry of
  `chartTransitionAt α β x : E →L[ℝ] E` in the canonical model-space basis
  `chartModelBasis E`. (A scalar.)
* `chartGramOnE_eq_sum_chartTransition` — the standard transformation
  law for a `(0, 2)`-covariant tensor:
  `G_α(x)_{ij} = ∑ a b, (DT_{αβ})^a_i(x) (DT_{αβ})^b_j(x) G_β(T x)_{ab}`,
  with the chart-α data on the LHS expressed in chart-β data on the RHS.
* `chartGramOnE_pullback_under_chartTransition` — the inverse direction,
  obtained by exchanging the roles of α and β.

Both forms reduce to `chartGramMatrix_pullback_eq_sum` from
`Integral/Measure/Invariance.lean`; the new content is the bridge from the
manifold-level Jacobian `tangentCoordChange I α β p` to the chart-level
Jacobian `chartTransitionAt α β x` valid in the boundaryless setting (where
`fderivWithin (range I) = fderiv`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The `(i, a)`-entry of the chart-transition Fréchet derivative
`chartTransitionAt α β x : E →L[ℝ] E` in the canonical model-space basis
`chartModelBasis E`. With `J := chartTransitionAt α β x` and `eₖ` the
model-basis vectors, this is the `i`-th coordinate of `J(e_a)`. -/
def chartTransitionAtEntry (α β : M) (x : E)
    (i a : Fin (Module.finrank ℝ E)) : ℝ :=
  (chartModelBasis E).repr
    (chartTransitionAt (I := I) α β x ((chartModelBasis E) a)) i

@[simp] lemma chartTransitionAtEntry_def (α β : M) (x : E)
    (i a : Fin (Module.finrank ℝ E)) :
    chartTransitionAtEntry (I := I) α β x i a =
      (chartModelBasis E).repr
        (chartTransitionAt (I := I) α β x
          ((chartModelBasis E) a)) i := rfl

omit [IsManifold I ∞ M] in
private lemma fderivWithin_range_I_eq_fderiv [I.Boundaryless]
    (f : E → E) (y : E) :
    fderivWithin ℝ f (Set.range I) y = fderiv ℝ f y := by
  have h : (Set.range I : Set E) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ (I := I)
  rw [h, fderivWithin_univ]

/-- Bridge: on the chart overlap, the manifold-level Jacobian `tangentCoordChange`
agrees with the chart-level Jacobian `chartTransitionAt`. -/
lemma tangentCoordChange_eq_chartTransitionAt [I.Boundaryless]
    (α β : M) (p : M) :
    tangentCoordChange I α β p =
      chartTransitionAt (I := I) α β (extChartAt I α p) := by
  rw [tangentCoordChange_def]
  rw [chartTransitionAt_def]
  rw [chartTransitionMap_def]
  exact fderivWithin_range_I_eq_fderiv (I := I)
    (extChartAt I β ∘ (extChartAt I α).symm) (extChartAt I α p)

theorem chartGramOnE_eq_sum_chartTransition [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α β : M) (x : E)
    (hx : x ∈ (extChartAt I α) ''
              ((chartAt H α).source ∩ (chartAt H β).source))
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) g α i j x =
      ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        chartTransitionAtEntry (I := I) α β x a i *
        chartTransitionAtEntry (I := I) α β x b j *
        chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β x) := by
  classical
  obtain ⟨p, ⟨hp_α_src, hp_β_src⟩, hp_eq⟩ := hx
  have hp_ext_α : p ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hp_α_src
  have hp_ext_β : p ∈ (extChartAt I β).source := by
    rw [extChartAt_source (I := I)]; exact hp_β_src
  have hx_eq : extChartAt I α p = x := hp_eq
  have hp_symm : (extChartAt I α).symm x = p := by
    rw [← hx_eq, (extChartAt I α).left_inv hp_ext_α]
  have h_tβ : chartTransitionMap (I := I) α β x = extChartAt I β p := by
    change extChartAt I β ((extChartAt I α).symm x) = extChartAt I β p
    rw [hp_symm]
  have hp_triv_α : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change p ∈ (chartAt H α).source; exact hp_α_src
  have hp_triv_β : p ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    change p ∈ (chartAt H β).source; exact hp_β_src
  have h_lhs :
      chartGramOnE (I := I) g α i j x =
        chartGramMatrix g α p i j := by
    change chartGramMatrix g α ((extChartAt I α).symm x) i j =
        chartGramMatrix g α p i j
    rw [hp_symm]
  have h_rhs_inner : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g β a b
        (chartTransitionMap (I := I) α β x) =
      chartGramMatrix g β p a b := by
    intro a b
    change chartGramMatrix g β
        ((extChartAt I β).symm (chartTransitionMap (I := I) α β x)) a b =
      chartGramMatrix g β p a b
    rw [h_tβ, (extChartAt I β).left_inv hp_ext_β]
  rw [h_lhs]
  rw [chartGramMatrix_pullback_eq_sum (I := I) g β α
        hp_triv_β hp_triv_α i j]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [h_rhs_inner k l]
  congr 1
  congr 1
  · rw [transitionMatrix_apply]
    rw [tangentCoordChange_eq_chartTransitionAt (I := I) α β p]
    simp only [chartTransitionAtEntry_def, hx_eq]
  · rw [transitionMatrix_apply]
    rw [tangentCoordChange_eq_chartTransitionAt (I := I) α β p]
    simp only [chartTransitionAtEntry_def, hx_eq]

theorem chartGramOnE_pullback_under_chartTransition [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α β : M) (x : E)
    (hx : x ∈ (extChartAt I α) ''
              ((chartAt H α).source ∩ (chartAt H β).source))
    (a b : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β x) =
      ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        chartTransitionAtEntry (I := I) β α
            (chartTransitionMap (I := I) α β x) i a *
        chartTransitionAtEntry (I := I) β α
            (chartTransitionMap (I := I) α β x) j b *
        chartGramOnE (I := I) g α i j x := by
  classical
  obtain ⟨p, ⟨hp_α_src, hp_β_src⟩, hp_eq⟩ := hx
  have hp_ext_α : p ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hp_α_src
  have hp_ext_β : p ∈ (extChartAt I β).source := by
    rw [extChartAt_source (I := I)]; exact hp_β_src
  have hx_eq : extChartAt I α p = x := hp_eq
  have hp_symm : (extChartAt I α).symm x = p := by
    rw [← hx_eq, (extChartAt I α).left_inv hp_ext_α]
  have h_tβ : chartTransitionMap (I := I) α β x = extChartAt I β p := by
    change extChartAt I β ((extChartAt I α).symm x) = extChartAt I β p
    rw [hp_symm]
  have hp_triv_α : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change p ∈ (chartAt H α).source; exact hp_α_src
  have hp_triv_β : p ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    change p ∈ (chartAt H β).source; exact hp_β_src
  have h_lhs :
      chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β x) =
        chartGramMatrix g β p a b := by
    change chartGramMatrix g β
        ((extChartAt I β).symm (chartTransitionMap (I := I) α β x)) a b =
      chartGramMatrix g β p a b
    rw [h_tβ, (extChartAt I β).left_inv hp_ext_β]
  have h_rhs_inner : ∀ i j : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i j x =
        chartGramMatrix g α p i j := by
    intro i j
    change chartGramMatrix g α ((extChartAt I α).symm x) i j =
      chartGramMatrix g α p i j
    rw [hp_symm]
  rw [h_lhs]
  rw [chartGramMatrix_pullback_eq_sum (I := I) g α β
        hp_triv_α hp_triv_β a b]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [h_rhs_inner i j]
  congr 1
  congr 1
  · rw [transitionMatrix_apply]
    rw [tangentCoordChange_eq_chartTransitionAt (I := I) β α p]
    simp only [chartTransitionAtEntry_def, h_tβ]
  · rw [transitionMatrix_apply]
    rw [tangentCoordChange_eq_chartTransitionAt (I := I) β α p]
    simp only [chartTransitionAtEntry_def, h_tβ]

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
