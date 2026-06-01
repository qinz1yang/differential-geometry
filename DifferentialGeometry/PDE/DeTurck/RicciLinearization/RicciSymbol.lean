import DifferentialGeometry.PDE.DeTurck.RicciLinearization.RicciSymbolFormula

/-!
# The linearized-Ricci principal symbol as a bundled tensor symbol

The component-level description of the linearized-Ricci principal symbol — the four-term
formula `ricciSymbolComp g x ξ t i k`, with its closed form, `ℝ`-linearity in the input
bilinear form `t`, and `(i, k)`-symmetry on a symmetric input — is assembled here into a
single bundled object: a `TensorSymbol I M`.

A `TensorSymbol I M` attaches, to every base point `x : M` and every covector `ξ : E`, a
linear endomorphism of the `(0,2)`-tensor fibre
`Fib x = TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ`.  The linearized-Ricci symbol
`ricciSymbol g` is the endomorphism `t ↦ s`, where the output bilinear form `s` is
reconstructed from its chart components by
$$s(v, w) = \sum_{i,k} v_i\, w_k\, \sigma_{ik}(\xi)(t),
  \qquad v_i = (\text{chartModelBasis } E).\mathrm{repr}\, v\, i,$$
and `σ_{ik}(ξ)(t) = ricciSymbolComp g x ξ t i k` is the component formula.

## Contents

* `ricciSymbolOutput` — the output bilinear form `s` reconstructed from the components
  `ricciSymbolComp g x ξ t i k`, packaged as a fibre element
  `TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ` via `LinearMap.mk₂`.
* `ricciSymbol` — the bundled `TensorSymbol I M`: at `(x, ξ)` the linear endomorphism
  `t ↦ ricciSymbolOutput g x ξ t` of the fibre.
* `ricciSymbol_apply_apply` — the component characterization: evaluating the output on the
  model-basis vectors returns the component formula,
  `(ricciSymbol g x ξ t) (e_i) (e_k) = ricciSymbolComp g x ξ t i k`.
* `ricciSymbol_apply_eq_closedForm` — the classical four-term closed form for the output's
  components, obtained by combining `ricciSymbol_apply_apply` with
  `ricciSymbolComp_eq_closedForm`.
* `ricciSymbol_apply_symm` — the bundled symbol maps symmetric forms to symmetric forms.

## Conventions

A covector at `x` is recorded as a model vector `ξ : E`, with chart components
`ξ_a = (chartModelBasis E).repr ξ a` (the same convention as `Symbol.lean` and
`RicciSymbolFormula.lean`).  The fibre `TangentSpace I x` is definitionally the model
space `E`, so the model-basis vectors `chartModelBasis E i` are admissible arguments of a
fibre bilinear form, and `(chartModelBasis E).repr` provides chart components of fibre
vectors.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section Output

/-- Additivity of a single model-basis coordinate of a model vector.  It is the
`map_add` of the coordinate `LinearMap` `(chartModelBasis E).coord i`, rephrased through
`Module.Basis.coord_apply` in terms of `(chartModelBasis E).repr`. -/
private lemma chartModelBasis_repr_apply_add (v₁ v₂ : E)
    (i : Fin (Module.finrank ℝ E)) :
    (chartModelBasis E).repr (v₁ + v₂) i =
      (chartModelBasis E).repr v₁ i + (chartModelBasis E).repr v₂ i := by
  rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply, ← Module.Basis.coord_apply,
    map_add]

/-- Homogeneity of a single model-basis coordinate of a model vector.  It is the
`map_smul` of the coordinate `LinearMap` `(chartModelBasis E).coord i`, rephrased through
`Module.Basis.coord_apply` in terms of `(chartModelBasis E).repr`. -/
private lemma chartModelBasis_repr_apply_smul (a : ℝ) (v : E)
    (i : Fin (Module.finrank ℝ E)) :
    (chartModelBasis E).repr (a • v) i = a * (chartModelBasis E).repr v i := by
  rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply, map_smul, smul_eq_mul]

/-- The **output bilinear form** of the linearized-Ricci symbol at `(x, ξ)` applied to the
input bilinear form `t`.

It is the fibre element `s : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ` whose
value on `(v, w)` is
$$s(v, w) = \sum_{i,k} v_i\, w_k\, \sigma_{ik}(\xi)(t),$$
with `v_i = (chartModelBasis E).repr v i`, `w_k = (chartModelBasis E).repr w k` the chart
components and `σ_{ik}(\xi)(t) = ricciSymbolComp g x ξ t i k` the four-term symbol
component formula.

The two-variable map is bilinear (built with `LinearMap.mk₂`): the summand
`v_i · w_k · σ_{ik}` depends linearly on `v` through the functional `v ↦ v_i` and on `w`
through `w ↦ w_k`, with `σ_{ik}` constant in `v, w`. -/
def ricciSymbolOutput (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun v w : E =>
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr v i * (chartModelBasis E).repr w k *
            ricciSymbolComp (I := I) g x ξ t i k)
    (fun v₁ v₂ w => by
      dsimp only
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [chartModelBasis_repr_apply_add]
      ring)
    (fun a v w => by
      dsimp only
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [chartModelBasis_repr_apply_smul]
      ring)
    (fun v w₁ w₂ => by
      dsimp only
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [chartModelBasis_repr_apply_add]
      ring)
    (fun a v w => by
      dsimp only
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [chartModelBasis_repr_apply_smul]
      ring) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ)

/-- Evaluation of `ricciSymbolOutput` on a pair of fibre vectors: the reconstruction
formula `s(v, w) = ∑_{i,k} v_i w_k σ_{ik}(ξ)(t)`. -/
@[simp] lemma ricciSymbolOutput_apply_apply (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (v w : TangentSpace I x) :
    ricciSymbolOutput (I := I) g x ξ t v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr v i * (chartModelBasis E).repr w k *
            ricciSymbolComp (I := I) g x ξ t i k := rfl

/-- The output bilinear form is **additive** in the input bilinear form: this is the
component additivity `ricciSymbolComp_add` carried through the reconstruction sum. -/
lemma ricciSymbolOutput_add (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    ricciSymbolOutput (I := I) g x ξ (t + t') =
      ricciSymbolOutput (I := I) g x ξ t + ricciSymbolOutput (I := I) g x ξ t' := by
  ext v w
  rw [LinearMap.add_apply, LinearMap.add_apply, ricciSymbolOutput_apply_apply,
    ricciSymbolOutput_apply_apply, ricciSymbolOutput_apply_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ricciSymbolComp_add]
  ring

/-- The output bilinear form is **homogeneous** in the input bilinear form: this is the
component homogeneity `ricciSymbolComp_smul` carried through the reconstruction sum. -/
lemma ricciSymbolOutput_smul (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) (a : ℝ)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    ricciSymbolOutput (I := I) g x ξ (a • t) =
      a • ricciSymbolOutput (I := I) g x ξ t := by
  ext v w
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
    ricciSymbolOutput_apply_apply, ricciSymbolOutput_apply_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ricciSymbolComp_smul]
  ring

end Output

section Bundle

/-- The **bundled linearized-Ricci principal symbol** as a `TensorSymbol I M`.

At each base point `x` and covector `ξ` it is the linear endomorphism of the
`(0,2)`-tensor fibre `TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ` sending the input
bilinear form `t` to the output bilinear form `ricciSymbolOutput g x ξ t` — the form
reconstructed from the four-term symbol components `ricciSymbolComp g x ξ t i k`.

This packages the component-level linearized-Ricci symbol into the same bundled symbol
type (`TensorSymbol`) that the strict-parabolicity statement of the Ricci–DeTurck operator
is phrased against. -/
def ricciSymbol (g : SmoothRiemannianMetric I M) : TensorSymbol (E := E) I M :=
  fun x ξ =>
    { toFun := fun t => ricciSymbolOutput (I := I) g x ξ t
      map_add' := fun t t' => ricciSymbolOutput_add (I := I) g x ξ t t'
      map_smul' := fun a t => by
        simpa using ricciSymbolOutput_smul (I := I) g x ξ a t }

/-- Unfolding lemma: the bundled symbol `ricciSymbol g` at `(x, ξ)`, applied to an input
bilinear form `t`, is the output bilinear form `ricciSymbolOutput g x ξ t`. -/
@[simp] lemma ricciSymbol_apply (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    ricciSymbol (I := I) g x ξ t = ricciSymbolOutput (I := I) g x ξ t := rfl

/-- **Component characterization of the bundled linearized-Ricci symbol.**

Evaluating the output bilinear form `ricciSymbol g x ξ t` on the model-basis vectors
`chartModelBasis E i` and `chartModelBasis E k` returns exactly the four-term symbol
component `ricciSymbolComp g x ξ t i k`:
$$(\sigma(\xi)(t))(e_i, e_k) = \sigma_{ik}(\xi)(t).$$

This is the bridge between the bundled `LinearMap` endomorphism and the concrete
component formula: the reconstruction sum collapses against the basis, because the
coordinates of a basis vector are a Kronecker delta
(`(chartModelBasis E).repr (chartModelBasis E i) = Finsupp.single i 1`). -/
theorem ricciSymbol_apply_apply (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    (ricciSymbol (I := I) g x ξ t)
        ((chartModelBasis E) i) ((chartModelBasis E) k) =
      ricciSymbolComp (I := I) g x ξ t i k := by
  classical
  rw [ricciSymbol_apply, ricciSymbolOutput_apply_apply]
  rw [(chartModelBasis E).repr_self, (chartModelBasis E).repr_self]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single k]
    · rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
      ring
    · intro k' _ hk'
      rw [Finsupp.single_eq_of_ne hk']
      ring
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  · intro i' _ hi'
    rw [Finsupp.single_eq_of_ne hi']
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **The bundled linearized-Ricci symbol in classical closed form.**

Combining the component characterization `ricciSymbol_apply_apply` with the closed-form
component theorem `ricciSymbolComp_eq_closedForm`, the value of the output bilinear form
on the model-basis vectors is the classical four-term contracted symbol of the linearized
Ricci operator:
$$(\sigma(\xi)(t))(e_i, e_k) = \tfrac12\,\xi_i \sum_l \xi^l\, t_{lk}
    + \tfrac12\,\xi_k \sum_j \xi^j\, t_{ij}
    - \tfrac12\,|\xi|^2_g\, t_{ik}
    - \tfrac12\,\xi_i\xi_k\, \operatorname{tr}_g t,$$
with `ξ_a = (chartModelBasis E).repr ξ a` the chart components of the covector, `ξ^m` the
raised covector, `∑_l ξ^l t_{lk} = raisedFormContraction`,
`∑_j ξ^j t_{ij} = raisedFormContractionSnd`, `|ξ|²_g = metricCovectorNormSq`, and
`tr_g t = formMetricTrace`. -/
theorem ricciSymbol_apply_eq_closedForm (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    (ricciSymbol (I := I) g x ξ t)
        ((chartModelBasis E) i) ((chartModelBasis E) k) =
      (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ i *
          raisedFormContraction (I := I) g x ξ t k) +
        (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ k *
          raisedFormContractionSnd (I := I) g x ξ t i) -
        (1 / 2 : ℝ) * (metricCovectorNormSq (I := I) g x ξ *
          formComp (I := I) x t i k) -
        (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ i *
          (chartModelBasis E).repr ξ k * formMetricTrace (I := I) g x t) := by
  rw [ricciSymbol_apply_apply, ricciSymbolComp_eq_closedForm]

/-- **The bundled linearized-Ricci symbol preserves symmetry.**

For a symmetric input bilinear form `t` (`t v w = t w v`), the output bilinear form
`ricciSymbol g x ξ t` is again symmetric.  Evaluated on the model basis this is the
component symmetry `ricciSymbolComp_symm` (`σ_{ik}(ξ)(t) = σ_{ki}(ξ)(t)`), transported to
arbitrary fibre vectors `v, w` through the reconstruction sum: swapping `v ↔ w`
interchanges the roles of the two coordinate families and the `(i, k)`-swap, leaving the
sum unchanged. -/
theorem ricciSymbol_apply_symm (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (v w : TangentSpace I x) :
    (ricciSymbol (I := I) g x ξ t) v w = (ricciSymbol (I := I) g x ξ t) w v := by
  rw [ricciSymbol_apply, ricciSymbolOutput_apply_apply,
    ricciSymbolOutput_apply_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ricciSymbolComp_symm (I := I) g x ξ t ht k i]
  ring

end Bundle

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
