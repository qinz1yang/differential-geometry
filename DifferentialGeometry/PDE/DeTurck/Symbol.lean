import DifferentialGeometry.Geometry.HessianTrace

/-!
# Principal symbols of second-order operators on tensor fields

For a second-order linear differential operator `L` acting on tensor fields over a
Riemannian manifold, the **principal symbol** `σ(L)(x, ξ)` at a base point `x` and a
covector `ξ` is the fiberwise linear endomorphism of the tensor fibre obtained from the
leading (second-order) part of `L` by the formal substitution `∂_i ∂_j ↦ −ξ_i ξ_j` and
discarding all first- and zeroth-order terms.  (The minus sign is the standard
principal-symbol factor: substituting `∂_j ↦ i ξ_j` turns `∂_i ∂_j` into
`(i ξ_i)(i ξ_j) = −ξ_i ξ_j`.)

This file provides a *thin* vocabulary for stating which symbol a concrete operator has.
It is deliberately minimal — there is no general pseudodifferential calculus here.  The
objects are:

* `OperatorSymbol F` — a fibre-generic principal symbol: for each base point `x : M` and
  covector `ξ : E` a linear endomorphism of the fibre `F x`.  The fibre `F` is a family
  `M → Type*`; the two instantiations used downstream are the constant scalar fibre
  `F x = ℝ` and the `(0,2)`-tensor fibre
  `F x = (TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)`.
* `TensorSymbol I M` / `ScalarSymbol M` — the `(0,2)`-tensor and scalar special cases.
* `isotropicSymbol F c` — the symbol `ξ ↦ c(x, ξ) • id`, built from a scalar coefficient
  function.  The geometrically relevant coefficient is `−|ξ|²_g`.
* `metricCovectorNormSq g x ξ` — the squared `g`-norm `g^{ij} ξ_i ξ_j` of a covector,
  expressed in chart coordinates through the inverse Gram matrix `chartInvGramMatrix`.
* `IsStrictlyParabolic` — the predicate "the symbol equals `−|ξ|²_g · id` for every `x`
  and every `ξ ≠ 0`", which is the clean target for "the Ricci–DeTurck operator is
  strictly parabolic".
* `secondOrderSymbol F a` — the substitution helper: the symbol of a chart operator
  whose leading part is `∑_{i,j} a^{ij}(x) · ∂_i ∂_j h` is
  `ξ ↦ −(∑_{i,j} a^{ij}(x) ξ_i ξ_j) • id`.

## Conventions

* **Covector convention.** A covector at `x` in chart coordinates is recorded as a model
  vector `ξ : E`; its components `ξ_i` are the coordinates `(chartModelBasis E).repr ξ i`
  in the fixed model basis.  (Equivalently `ξ` is the coefficient vector of `ξ_i dx^i`.)
* **Sign convention.** The geometer's Laplacian `Δ_g = div ∘ grad` has spectrum in
  `(-∞, 0]`.  Its principal symbol is `σ(Δ_g)(x, ξ) = −|ξ|²_g`, which is
  negative-definite for `ξ ≠ 0`.  An operator `L` driving the evolution `∂_t u = L u` is
  **strictly parabolic** exactly when `σ(L)(x, ξ) = −|ξ|²_g · id` for `ξ ≠ 0`; this is
  the content of `IsStrictlyParabolic`.

## Main results

* `metricCovectorNormSq_nonneg` — `|ξ|²_g ≥ 0` at chart-source points.
* `metricCovectorNormSq_pos` — `|ξ|²_g > 0` for `ξ ≠ 0` at chart-source points.
* `secondOrderSymbol_apply` — the substitution formula for `secondOrderSymbol`.
* `laplacianSymbol_eq_isotropic` — the scalar Laplacian `Δ_g` has principal symbol
  `−|ξ|²_g · id`, i.e. it is the isotropic symbol with coefficient `−|ξ|²_g`.
* `laplacianSymbol_isStrictlyParabolic` — the scalar-Laplacian symbol is strictly
  parabolic.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A **principal symbol** of a second-order linear operator acting on sections of a
vector bundle with fibre family `F : M → Type*`.

For each base point `x : M` and covector `ξ : E` (recorded as a model vector — see the
covector convention), it is a linear endomorphism of the fibre `F x`.  This is the
leading (second-order) part of the operator after the formal substitution
`∂_i ∂_j ↦ −ξ_i ξ_j`. -/
abbrev OperatorSymbol (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] : Type _ :=
  ∀ x : M, E → (F x →ₗ[ℝ] F x)

variable (I M) in
/-- The principal symbol of a second-order operator acting on `(0,2)`-tensor fields.

The `(0,2)`-tensor fibre at `x` is `TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ` (the
carrier `pointwiseBilin` uses), so a `TensorSymbol` attaches to every `x` and covector
`ξ` a linear endomorphism of that bilinear-form space.  This is the symbol type the
Ricci–DeTurck strict-parabolicity statement is phrased against. -/
abbrev TensorSymbol : Type _ :=
  OperatorSymbol (E := E)
    (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)

variable (M) in
/-- The principal symbol of a second-order operator acting on scalar functions (constant
fibre `ℝ`).  Used for the validation example: the scalar Laplace–Beltrami operator. -/
abbrev ScalarSymbol : Type _ :=
  OperatorSymbol (E := E) (fun _ : M => ℝ)

/-- The squared `g`-norm of a covector `ξ`, expressed in the chart at `x`:
$$|\xi|^2_g(x) = \sum_{i,j} g^{ij}(x)\, \xi_i\, \xi_j,$$
where `g^{ij} = chartInvGramMatrix g x x` is the chart inverse metric and
`ξ_i = (chartModelBasis E).repr ξ i` are the chart components of the covector `ξ`. -/
def metricCovectorNormSq (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j *
        ((chartModelBasis E).repr ξ i) * ((chartModelBasis E).repr ξ j)

@[simp] lemma metricCovectorNormSq_def (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    metricCovectorNormSq (I := I) g x ξ =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            ((chartModelBasis E).repr ξ i) * ((chartModelBasis E).repr ξ j) := rfl

/-- The squared `g`-norm of the zero covector vanishes. -/
@[simp] lemma metricCovectorNormSq_zero (g : SmoothRiemannianMetric I M) (x : M) :
    metricCovectorNormSq (I := I) g x 0 = 0 := by
  simp [metricCovectorNormSq]

/-- The chart inverse Gram matrix at `x` (in the chart at `x` itself) is
positive-definite. -/
private lemma chartInvGramMatrix_self_posDef (g : SmoothRiemannianMetric I M) (x : M) :
    (chartInvGramMatrix (I := I) g x x).PosDef := by
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hG : (chartGramMatrix (I := I) g x x).PosDef :=
    chartGramMatrix_posDef (I := I) g x hx
  rw [chartInvGramMatrix]
  exact hG.inv

/-- The quadratic form of the chart inverse Gram matrix evaluated on the coordinate
vector of a covector `ξ` equals `metricCovectorNormSq g x ξ`. -/
private lemma metricCovectorNormSq_eq_dotProduct_mulVec
    (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    metricCovectorNormSq (I := I) g x ξ =
      star (fun i => (chartModelBasis E).repr ξ i) ⬝ᵥ
        (chartInvGramMatrix (I := I) g x x) *ᵥ
          (fun i => (chartModelBasis E).repr ξ i) := by
  classical
  rw [metricCovectorNormSq_def]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **Non-negativity of `|ξ|²_g`.**  The squared `g`-norm of any covector is
non-negative. -/
theorem metricCovectorNormSq_nonneg (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    0 ≤ metricCovectorNormSq (I := I) g x ξ := by
  classical
  rw [metricCovectorNormSq_eq_dotProduct_mulVec]
  exact (chartInvGramMatrix_self_posDef (I := I) g x).posSemidef.dotProduct_mulVec_nonneg _

/-- **Strict positivity of `|ξ|²_g` for nonzero covectors.**  The squared `g`-norm of a
nonzero covector is strictly positive. -/
theorem metricCovectorNormSq_pos (g : SmoothRiemannianMetric I M) (x : M)
    {ξ : E} (hξ : ξ ≠ 0) :
    0 < metricCovectorNormSq (I := I) g x ξ := by
  classical
  rw [metricCovectorNormSq_eq_dotProduct_mulVec]
  have hcoord : (fun i => (chartModelBasis E).repr ξ i) ≠ 0 := by
    intro hzero
    apply hξ
    have hrepr : (chartModelBasis E).repr ξ = 0 := by
      ext i
      exact congrFun hzero i
    have := congrArg (chartModelBasis E).repr.symm hrepr
    simpa using this
  exact (chartInvGramMatrix_self_posDef (I := I) g x).dotProduct_mulVec_pos hcoord

/-- The **isotropic symbol** with scalar coefficient `c`: for each base point `x` and
covector `ξ`, the fibrewise endomorphism `c x ξ • LinearMap.id`.

This is fibre-generic: it produces an `OperatorSymbol F` for any fibre family `F`.  The
geometrically relevant instance uses the coefficient `c x ξ = −|ξ|²_g`. -/
def isotropicSymbol (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (c : M → E → ℝ) :
    OperatorSymbol (E := E) F :=
  fun x ξ => (c x ξ) • LinearMap.id

@[simp] lemma isotropicSymbol_apply (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (c : M → E → ℝ) (x : M) (ξ : E) :
    isotropicSymbol (E := E) F c x ξ = (c x ξ) • LinearMap.id := rfl

/-- The isotropic symbol applied to a fibre element scales it by the coefficient. -/
@[simp] lemma isotropicSymbol_apply_apply (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (c : M → E → ℝ) (x : M) (ξ : E)
    (v : F x) :
    isotropicSymbol (E := E) F c x ξ v = (c x ξ) • v := by
  rw [isotropicSymbol_apply]
  rfl

/-- The **Ricci–DeTurck isotropic coefficient** `(x, ξ) ↦ −|ξ|²_g`.  This is the scalar
coefficient of the strictly-parabolic isotropic symbol. -/
def deTurckSymbolCoeff (g : SmoothRiemannianMetric I M) : M → E → ℝ :=
  fun x ξ => -metricCovectorNormSq (I := I) g x ξ

@[simp] lemma deTurckSymbolCoeff_apply (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    deTurckSymbolCoeff (I := I) g x ξ = -metricCovectorNormSq (I := I) g x ξ := rfl

/-- A symbol `σ` (on the fibre family `F`) is **strictly parabolic** with respect to the
metric `g` when, at every base point `x` and every nonzero covector `ξ`, it equals the
isotropic symbol with coefficient `−|ξ|²_g`:
$$\sigma(x, \xi) = -|\xi|^2_g \cdot \mathrm{id}, \qquad \xi \neq 0.$$

Since `|ξ|²_g > 0` for `ξ ≠ 0` (`metricCovectorNormSq_pos`), this says the symbol is
negative-definite away from the zero covector — the defining property of strict
(uniform) parabolicity for the evolution `∂_t u = σ u`, in the geometer's sign
convention `Δ = div ∘ grad`. -/
def IsStrictlyParabolic (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (g : SmoothRiemannianMetric I M) (σ : OperatorSymbol (E := E) F) : Prop :=
  ∀ x : M, ∀ ξ : E, ξ ≠ 0 →
    σ x ξ = isotropicSymbol (E := E) F (deTurckSymbolCoeff (I := I) g) x ξ

/-- Unfolding lemma for `IsStrictlyParabolic`: the symbol equals `−|ξ|²_g • id` at every
nonzero covector. -/
lemma isStrictlyParabolic_iff (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (g : SmoothRiemannianMetric I M) (σ : OperatorSymbol (E := E) F) :
    IsStrictlyParabolic (E := E) F g σ ↔
      ∀ x : M, ∀ ξ : E, ξ ≠ 0 →
        σ x ξ = (-metricCovectorNormSq (I := I) g x ξ) • LinearMap.id :=
  Iff.rfl

/-- The isotropic symbol with coefficient `−|ξ|²_g` is itself strictly parabolic.  This
is the reference strictly-parabolic symbol the Ricci–DeTurck operator must match. -/
theorem isStrictlyParabolic_isotropic_deTurckSymbolCoeff (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (g : SmoothRiemannianMetric I M) :
    IsStrictlyParabolic (E := E) F g
      (isotropicSymbol (E := E) F (deTurckSymbolCoeff (I := I) g)) :=
  fun _ _ _ => rfl

/-- The **principal symbol of a second-order chart operator** whose leading part is
`∑_{i,j} a^{ij}(x) · ∂_i ∂_j h`, where `a x` is the coefficient matrix at the base point
`x`.

By the substitution `∂_i ∂_j ↦ −ξ_i ξ_j` this is the isotropic symbol with scalar
coefficient
$$-\sum_{i,j} a^{ij}(x)\, \xi_i\, \xi_j,$$
the chart components being `ξ_i = (chartModelBasis E).repr ξ i`.  It is fibre-generic:
the same leading-coefficient matrix `a` produces a symbol on any fibre family `F`. -/
def secondOrderSymbol (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (a : M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) :
    OperatorSymbol (E := E) F :=
  fun x ξ =>
    (-∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          a x i j * ((chartModelBasis E).repr ξ i) * ((chartModelBasis E).repr ξ j)) •
      LinearMap.id

/-- **Substitution formula for `secondOrderSymbol`.**  The symbol of the leading part
`∑ a^{ij} ∂_i ∂_j` is, at `(x, ξ)`, the scalar `−∑_{i,j} a^{ij}(x) ξ_i ξ_j` times the
fibre identity. -/
@[simp] lemma secondOrderSymbol_apply (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (a : M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (x : M) (ξ : E) :
    secondOrderSymbol (E := E) F a x ξ =
      (-∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            a x i j * ((chartModelBasis E).repr ξ i) *
              ((chartModelBasis E).repr ξ j)) • LinearMap.id := rfl

/-- The symbol of a second-order chart operator with leading-coefficient matrix `a`,
applied to a fibre element `v`, scales `v` by `−∑ a^{ij} ξ_i ξ_j`. -/
@[simp] lemma secondOrderSymbol_apply_apply (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (a : M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (x : M) (ξ : E) (v : F x) :
    secondOrderSymbol (E := E) F a x ξ v =
      (-∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            a x i j * ((chartModelBasis E).repr ξ i) *
              ((chartModelBasis E).repr ξ j)) • v := by
  rw [secondOrderSymbol_apply]
  rfl

/-- **The symbol of a chart operator with inverse-metric leading part is the
Ricci–DeTurck isotropic symbol.**

When the leading-coefficient matrix is the chart inverse metric `g^{ij}` itself, the
contraction `∑ g^{ij} ξ_i ξ_j` is exactly `|ξ|²_g`, so the second-order symbol equals the
isotropic symbol with coefficient `−|ξ|²_g`.  This is the bridge identifying the symbol
of a `g^{ij} ∂_i ∂_j`-type leading part (in particular the scalar Laplacian) with the
strictly-parabolic reference symbol. -/
theorem secondOrderSymbol_invGram_eq_isotropic (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (g : SmoothRiemannianMetric I M) :
    secondOrderSymbol (E := E) F (fun x => chartInvGramMatrix (I := I) g x x) =
      isotropicSymbol (E := E) F (deTurckSymbolCoeff (I := I) g) := by
  funext x ξ
  rw [secondOrderSymbol_apply, isotropicSymbol_apply, deTurckSymbolCoeff_apply,
    metricCovectorNormSq_def]

/-- A second-order chart operator whose leading-coefficient matrix is the chart inverse
metric `g^{ij}` has a strictly-parabolic principal symbol. -/
theorem secondOrderSymbol_invGram_isStrictlyParabolic (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (g : SmoothRiemannianMetric I M) :
    IsStrictlyParabolic (E := E) F g
      (secondOrderSymbol (E := E) F (fun x => chartInvGramMatrix (I := I) g x x)) := by
  rw [secondOrderSymbol_invGram_eq_isotropic]
  exact isStrictlyParabolic_isotropic_deTurckSymbolCoeff (E := E) F g

/-- The **principal symbol of the scalar Laplace–Beltrami operator** `Δ_g`.

In a chart the leading (second-order) part of `Δ_g f` is `∑_{i,j} g^{ij}(x) ∂_i ∂_j f`
(see `chartHessTrace_expand`), so the symbol is `secondOrderSymbol` applied to the chart
inverse metric `g^{ij}`.  It is a `ScalarSymbol` (constant fibre `ℝ`, since `Δ_g` acts on
functions).  By `laplacianSymbol_eq_isotropic` this is the isotropic symbol `−|ξ|²_g`. -/
def laplacianSymbol (g : SmoothRiemannianMetric I M) : ScalarSymbol (E := E) M :=
  secondOrderSymbol (E := E) (fun _ : M => ℝ)
    (fun x => chartInvGramMatrix (I := I) g x x)

@[simp] lemma laplacianSymbol_apply (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    laplacianSymbol (I := I) g x ξ =
      (-∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x i j *
              ((chartModelBasis E).repr ξ i) *
                ((chartModelBasis E).repr ξ j)) • LinearMap.id := rfl

/-- **Validation: the scalar Laplacian has the isotropic symbol `−|ξ|²_g · id`.**

The leading part of `Δ_g` in chart coordinates is `∑ g^{ij} ∂_i ∂_j f`
(`chartHessTrace_expand` exhibits exactly this second-order term, the remaining terms
being first order), so by the substitution `∂_i ∂_j ↦ −ξ_i ξ_j` the principal symbol is
`−∑ g^{ij} ξ_i ξ_j = −|ξ|²_g` times the (scalar) identity.  This confirms the abstraction
reproduces the textbook symbol of the Laplace–Beltrami operator. -/
theorem laplacianSymbol_eq_isotropic (g : SmoothRiemannianMetric I M) :
    laplacianSymbol (I := I) g =
      isotropicSymbol (E := E) (fun _ : M => ℝ) (deTurckSymbolCoeff (I := I) g) := by
  rw [laplacianSymbol, secondOrderSymbol_invGram_eq_isotropic]

/-- Pointwise form of `laplacianSymbol_eq_isotropic`: at each `x` and `ξ`, the
scalar-Laplacian symbol is the endomorphism `−|ξ|²_g • id` of `ℝ`. -/
theorem laplacianSymbol_apply_eq (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    laplacianSymbol (I := I) g x ξ =
      (-metricCovectorNormSq (I := I) g x ξ) • LinearMap.id := by
  rw [laplacianSymbol_eq_isotropic, isotropicSymbol_apply, deTurckSymbolCoeff_apply]

/-- The scalar-Laplacian symbol applied to a scalar `t : ℝ` scales it by `−|ξ|²_g`. -/
theorem laplacianSymbol_apply_apply (g : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : ℝ) :
    laplacianSymbol (I := I) g x ξ t =
      (-metricCovectorNormSq (I := I) g x ξ) • t := by
  rw [laplacianSymbol_apply_eq]
  rfl

/-- **Validation: the scalar-Laplacian symbol is strictly parabolic.**

Since `Δ_g` has symbol `−|ξ|²_g · id` (`laplacianSymbol_eq_isotropic`), and `|ξ|²_g > 0`
for `ξ ≠ 0`, the symbol is negative-definite away from the zero covector — `Δ_g` is a
strictly parabolic operator.  This is the model statement that the Ricci–DeTurck
operator's symbol must replicate. -/
theorem laplacianSymbol_isStrictlyParabolic (g : SmoothRiemannianMetric I M) :
    IsStrictlyParabolic (E := E) (fun _ : M => ℝ) g (laplacianSymbol (I := I) g) := by
  rw [laplacianSymbol_eq_isotropic]
  exact isStrictlyParabolic_isotropic_deTurckSymbolCoeff (E := E) (fun _ : M => ℝ) g

/-- The scalar-Laplacian symbol, evaluated at a nonzero covector, is the scalar
endomorphism `−|ξ|²_g • id` with a strictly negative coefficient. -/
theorem laplacianSymbol_neg_of_ne_zero (g : SmoothRiemannianMetric I M) (x : M)
    {ξ : E} (hξ : ξ ≠ 0) :
    laplacianSymbol (I := I) g x ξ =
        (-metricCovectorNormSq (I := I) g x ξ) • LinearMap.id ∧
      metricCovectorNormSq (I := I) g x ξ > 0 :=
  ⟨laplacianSymbol_apply_eq (I := I) g x ξ,
    metricCovectorNormSq_pos (I := I) g x hξ⟩

end DeTurck
end PDE
end DifferentialGeometry
