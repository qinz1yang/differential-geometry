import DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.DeTurckCorrectionSymbolFormula

/-!
# The linearized-DeTurck-correction principal symbol as a bundled tensor symbol

The component-level description of the linearized-DeTurck-correction principal symbol — the
gauge-symbol formula `deTurckCorrSymbolComp g g' x ξ t i j`, with its closed form,
`ℝ`-linearity in the input bilinear form `t`, and `(i, j)`-symmetry — is assembled here
into a single bundled object: a `TensorSymbol I M`.

A `TensorSymbol I M` attaches, to every base point `x : M` and every covector `ξ : E`, a
linear endomorphism of the `(0,2)`-tensor fibre
`Fib x = TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ`.  The linearized-DeTurck-correction
symbol `deTurckCorrectionSymbol g g'` is the endomorphism `t ↦ s`, where the output bilinear
form `s` is reconstructed from its chart components by
$$s(v, w) = \sum_{i,j} v_i\, w_j\, \sigma_{ij}(\xi)(t),
  \qquad v_i = (\text{chartModelBasis } E).\mathrm{repr}\, v\, i,$$
and `σ_{ij}(ξ)(t) = deTurckCorrSymbolComp g g' x ξ t i j` is the component formula.

## Contents

* `deTurckCorrectionSymbolOutput` — the output bilinear form `s` reconstructed from the
  components `deTurckCorrSymbolComp g g' x ξ t i j`, packaged as a fibre element
  `TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ` via `LinearMap.mk₂`.
* `deTurckCorrectionSymbol` — the bundled `TensorSymbol I M`: at `(x, ξ)` the linear
  endomorphism `t ↦ deTurckCorrectionSymbolOutput g g' x ξ t` of the fibre.
* `deTurckCorrectionSymbol_apply_apply` — the component characterization: evaluating the
  output on the model-basis vectors returns the component formula,
  `(deTurckCorrectionSymbol g g' x ξ t) (e_i) (e_j) = deTurckCorrSymbolComp g g' x ξ t i j`.
* `deTurckCorrectionSymbol_apply_eq_closedForm` — the classical gauge-symbol closed form for
  the output's components, obtained by combining `deTurckCorrectionSymbol_apply_apply` with
  `deTurckCorrSymbolComp_eq_closedForm`.
* `deTurckCorrectionSymbol_apply_symm` — the bundled symbol maps every bilinear form to a
  symmetric bilinear form (the gauge symbol is manifestly symmetric, so no symmetry
  hypothesis on the input is needed).
* `deTurckCorrectionSymbol_background_independent` — the bundled symbol does not depend on
  the background metric `g'`.

## Conventions

A covector at `x` is recorded as a model vector `ξ : E`, with chart components
`ξ_a = (chartModelBasis E).repr ξ a` (the same convention as `Symbol.lean` and
`DeTurckCorrectionSymbolFormula.lean`).  The fibre `TangentSpace I x` is definitionally the
model space `E`, so the model-basis vectors `chartModelBasis E i` are admissible arguments
of a fibre bilinear form, and `(chartModelBasis E).repr` provides chart components of fibre
vectors.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace DeTurckLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

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

/-- The **output bilinear form** of the linearized-DeTurck-correction symbol at `(x, ξ)`
applied to the input bilinear form `t`.

It is the fibre element `s : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ` whose
value on `(v, w)` is
$$s(v, w) = \sum_{i,j} v_i\, w_j\, \sigma_{ij}(\xi)(t),$$
with `v_i = (chartModelBasis E).repr v i`, `w_j = (chartModelBasis E).repr w j` the chart
components and `σ_{ij}(\xi)(t) = deTurckCorrSymbolComp g g' x ξ t i j` the gauge-symbol
component formula.

The two-variable map is bilinear (built with `LinearMap.mk₂`): the summand
`v_i · w_j · σ_{ij}` depends linearly on `v` through the functional `v ↦ v_i` and on `w`
through `w ↦ w_j`, with `σ_{ij}` constant in `v, w`. -/
def deTurckCorrectionSymbolOutput (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun v w : E =>
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr v i * (chartModelBasis E).repr w j *
            deTurckCorrSymbolComp (I := I) g g' x ξ t i j)
    (fun v₁ v₂ w => by
      dsimp only
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [chartModelBasis_repr_apply_add]
      ring)
    (fun a v w => by
      dsimp only
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [chartModelBasis_repr_apply_smul]
      ring)
    (fun v w₁ w₂ => by
      dsimp only
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [chartModelBasis_repr_apply_add]
      ring)
    (fun a v w => by
      dsimp only
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [chartModelBasis_repr_apply_smul]
      ring) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ)

/-- Evaluation of `deTurckCorrectionSymbolOutput` on a pair of fibre vectors: the
reconstruction formula `s(v, w) = ∑_{i,j} v_i w_j σ_{ij}(ξ)(t)`. -/
@[simp] lemma deTurckCorrectionSymbolOutput_apply_apply (g g' : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (v w : TangentSpace I x) :
    deTurckCorrectionSymbolOutput (I := I) g g' x ξ t v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr v i * (chartModelBasis E).repr w j *
            deTurckCorrSymbolComp (I := I) g g' x ξ t i j := rfl

/-- The output bilinear form is **additive** in the input bilinear form: this is the
component additivity `deTurckCorrSymbolComp_add` carried through the reconstruction sum. -/
lemma deTurckCorrectionSymbolOutput_add (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    deTurckCorrectionSymbolOutput (I := I) g g' x ξ (t + t') =
      deTurckCorrectionSymbolOutput (I := I) g g' x ξ t +
        deTurckCorrectionSymbolOutput (I := I) g g' x ξ t' := by
  ext v w
  rw [LinearMap.add_apply, LinearMap.add_apply, deTurckCorrectionSymbolOutput_apply_apply,
    deTurckCorrectionSymbolOutput_apply_apply, deTurckCorrectionSymbolOutput_apply_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deTurckCorrSymbolComp_add]
  ring

/-- The output bilinear form is **homogeneous** in the input bilinear form: this is the
component homogeneity `deTurckCorrSymbolComp_smul` carried through the reconstruction
sum. -/
lemma deTurckCorrectionSymbolOutput_smul (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (a : ℝ) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    deTurckCorrectionSymbolOutput (I := I) g g' x ξ (a • t) =
      a • deTurckCorrectionSymbolOutput (I := I) g g' x ξ t := by
  ext v w
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
    deTurckCorrectionSymbolOutput_apply_apply, deTurckCorrectionSymbolOutput_apply_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deTurckCorrSymbolComp_smul]
  ring

end Output

section Bundle

/-- The **bundled linearized-DeTurck-correction principal symbol** as a `TensorSymbol I M`.

At each base point `x` and covector `ξ` it is the linear endomorphism of the
`(0,2)`-tensor fibre `TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ` sending the input
bilinear form `t` to the output bilinear form `deTurckCorrectionSymbolOutput g g' x ξ t` —
the form reconstructed from the gauge-symbol components `deTurckCorrSymbolComp g g' x ξ t i j`.

This packages the component-level linearized-DeTurck-correction symbol into the same
bundled symbol type (`TensorSymbol`) that the strict-parabolicity statement of the
Ricci–DeTurck operator is phrased against. -/
def deTurckCorrectionSymbol (g g' : SmoothRiemannianMetric I M) :
    TensorSymbol (E := E) I M :=
  fun x ξ =>
    { toFun := fun t => deTurckCorrectionSymbolOutput (I := I) g g' x ξ t
      map_add' := fun t t' => deTurckCorrectionSymbolOutput_add (I := I) g g' x ξ t t'
      map_smul' := fun a t => by
        simpa using deTurckCorrectionSymbolOutput_smul (I := I) g g' x ξ a t }

/-- Unfolding lemma: the bundled symbol `deTurckCorrectionSymbol g g'` at `(x, ξ)`, applied
to an input bilinear form `t`, is the output bilinear form
`deTurckCorrectionSymbolOutput g g' x ξ t`. -/
@[simp] lemma deTurckCorrectionSymbol_apply (g g' : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    deTurckCorrectionSymbol (I := I) g g' x ξ t =
      deTurckCorrectionSymbolOutput (I := I) g g' x ξ t := rfl

/-- **Component characterization of the bundled linearized-DeTurck-correction symbol.**

Evaluating the output bilinear form `deTurckCorrectionSymbol g g' x ξ t` on the model-basis
vectors `chartModelBasis E i` and `chartModelBasis E j` returns exactly the gauge-symbol
component `deTurckCorrSymbolComp g g' x ξ t i j`:
$$(\sigma(\xi)(t))(e_i, e_j) = \sigma_{ij}(\xi)(t).$$

This is the bridge between the bundled `LinearMap` endomorphism and the concrete
component formula: the reconstruction sum collapses against the basis, because the
coordinates of a basis vector are a Kronecker delta
(`(chartModelBasis E).repr (chartModelBasis E i) = Finsupp.single i 1`). -/
theorem deTurckCorrectionSymbol_apply_apply (g g' : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    (deTurckCorrectionSymbol (I := I) g g' x ξ t)
        ((chartModelBasis E) i) ((chartModelBasis E) j) =
      deTurckCorrSymbolComp (I := I) g g' x ξ t i j := by
  classical
  rw [deTurckCorrectionSymbol_apply, deTurckCorrectionSymbolOutput_apply_apply]
  rw [(chartModelBasis E).repr_self, (chartModelBasis E).repr_self]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
      ring
    · intro j' _ hj'
      rw [Finsupp.single_eq_of_ne hj']
      ring
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro i' _ hi'
    rw [Finsupp.single_eq_of_ne hi']
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **The bundled linearized-DeTurck-correction symbol in classical closed form.**

Combining the component characterization `deTurckCorrectionSymbol_apply_apply` with the
closed-form component theorem `deTurckCorrSymbolComp_eq_closedForm`, the value of the
output bilinear form on the model-basis vectors is the classical **gauge symbol** of the
linearized DeTurck-correction operator:
$$(\sigma(\xi)(t))(e_i, e_j) = \xi_i \sum_l \xi^l\, t_{jl}
    + \xi_j \sum_l \xi^l\, t_{il}
    - \xi_i\xi_j\, \operatorname{tr}_g t,$$
with `ξ_a = (chartModelBasis E).repr ξ a` the chart components of the covector, `ξ^l` the
raised covector, `∑_l ξ^l t_{jl} = raisedFormContractionSnd g x ξ t j` the second-slot
raised contraction of `t`, and `tr_g t = formMetricTrace g x t` the metric trace. -/
theorem deTurckCorrectionSymbol_apply_eq_closedForm (g g' : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    (deTurckCorrectionSymbol (I := I) g g' x ξ t)
        ((chartModelBasis E) i) ((chartModelBasis E) j) =
      (chartModelBasis E).repr ξ i *
          raisedFormContractionSnd (I := I) g x ξ t j +
        (chartModelBasis E).repr ξ j *
          raisedFormContractionSnd (I := I) g x ξ t i -
        (chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ j *
          formMetricTrace (I := I) g x t := by
  rw [deTurckCorrectionSymbol_apply_apply, deTurckCorrSymbolComp_eq_closedForm]

/-- **The bundled linearized-DeTurck-correction symbol produces symmetric forms.**

For *any* input bilinear form `t`, the output bilinear form `deTurckCorrectionSymbol g g' x ξ t`
is symmetric.  Evaluated on the model basis this is the component symmetry
`deTurckCorrSymbolComp_symm` (`σ_{ij}(ξ)(t) = σ_{ji}(ξ)(t)`, which holds unconditionally
because the gauge symbol is manifestly `(i, j)`-symmetric), transported to arbitrary fibre
vectors `v, w` through the reconstruction sum: swapping `v ↔ w` interchanges the roles of
the two coordinate families and the `(i, j)`-swap, leaving the sum unchanged.  No symmetry
hypothesis on `t` is required. -/
theorem deTurckCorrectionSymbol_apply_symm (g g' : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (v w : TangentSpace I x) :
    (deTurckCorrectionSymbol (I := I) g g' x ξ t) v w =
      (deTurckCorrectionSymbol (I := I) g g' x ξ t) w v := by
  rw [deTurckCorrectionSymbol_apply, deTurckCorrectionSymbolOutput_apply_apply,
    deTurckCorrectionSymbolOutput_apply_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deTurckCorrSymbolComp_symm (I := I) g g' x ξ t j i]
  ring

/-- **The bundled linearized-DeTurck-correction symbol does not depend on the background
metric.**  The component formula `deTurckCorrSymbolComp` carries the background-metric
parameter `g'` for signature uniformity only and never uses it
(`deTurckCorrSymbolComp_background_independent`), so the bundled symbol is the same for any
two background metrics `g'₁`, `g'₂`. -/
theorem deTurckCorrectionSymbol_background_independent
    (g g'₁ g'₂ : SmoothRiemannianMetric I M) :
    deTurckCorrectionSymbol (I := I) g g'₁ = deTurckCorrectionSymbol (I := I) g g'₂ := by
  funext x ξ
  ext t v w
  rw [deTurckCorrectionSymbol_apply, deTurckCorrectionSymbol_apply,
    deTurckCorrectionSymbolOutput_apply_apply, deTurckCorrectionSymbolOutput_apply_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deTurckCorrSymbolComp_background_independent (I := I) g g'₁ g'₂]

end Bundle

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
