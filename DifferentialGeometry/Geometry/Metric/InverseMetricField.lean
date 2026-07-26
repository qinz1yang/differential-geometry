import DifferentialGeometry.Geometry.Operator.MetricSharpSmooth
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.CotangentRiemannian
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Geometry.Metric.ChartGram

/-!
# The inverse metric (cometric) as a smooth bundle operator field

For a smooth Riemannian metric `g` on a smooth manifold `M` modelled on a real inner-product
space `E`, the metric flat map `g_x^\flat : T_x M \to T_x^* M`, `v \mapsto g_x(v, \cdot)`, is a
linear isomorphism on each fibre (positive-definiteness).  Its inverse — the **musical sharp**
`g_x^\sharp : T_x^* M \to T_x M` — is the index-raising operator of the *inverse metric*
(cometric) `g^{-1}`.  The fibrewise sharp `metricSharp` and its smoothness as a tangent-bundle
section already live in `Geometry/Operator/Gradient.lean` and `Geometry/Operator/MetricSharpSmooth.lean`;
this file packages the sharp as a **smooth section of the bundle homomorphism**
`Hom(T^*M, TM)` — the inverse metric as a first-class reusable operator field — together with
its evaluation, the inverse property `g(\sharp \alpha, w) = \alpha(w)`, its self-vanishing on
the zero covector (non-vacuity), and the cometric scalar `g^{-1}(\alpha, \beta)` with a
fibrewise envelope.

The inverse-metric operator field raises a single covariant index, so its natural fibre is the
homomorphism `T^*M \to TM`, i.e. a fibre of `Hom(Tensor0S 1, TM)`.  This is exactly the shape
the Koszul contraction `D = g^{-1}\cdot(\nabla_0 h)` of the connection-difference development
uses (raising the lowered index of a covariant derivative), so it stays coherent with the
existing sharp/cometric calculus (`metricSharp`, `cotangentSharp`, `cotangentInner`).

## Main definitions

* `inverseMetricSharpFib g x` — the fibrewise inverse-metric sharp, a continuous linear map
  `Tensor0SSpace 1 I x →L[ℝ] TangentSpace I x` (raise a covector to a vector via `g`).
* `inverseMetricSharpField g` — the inverse-metric sharp as a smooth section of the bundle
  homomorphism `Hom(T^*M, TM)`.
* `cometricBilin g x` — the cometric scalar `g^{-1}(α, β)` on cotangent vectors at `x`.

## Main results

* `inverseMetricSharpFib_inner` — the inverse property: `g.inner x (♯ α) w = cotangentToDual α w`.
* `inverseMetricSharpFib_zero` — the sharp of the zero covector is the zero vector
  (non-vacuity litmus: the inverse metric is not a constant — it genuinely raises indices, and
  injectivity forces a nonzero image for a nonzero covector via `inverseMetricSharpFib_inner`).
* `inverseMetricSharpField_apply` — its fibre value at `x` is `inverseMetricSharpFib g x`.
* `inverseMetricSharpField_contMDiff` — the inverse-metric operator field is a smooth section
  of `Hom(T^*M, TM)` (the content of the packaging).
* `cometricBilin_eq_inner_sharp` / `cometricBilin_symm` — the cometric pairing equals the
  `g`-inner product of the two sharps and is symmetric.
* `cometricBilin_self_pos` — positive-definiteness of the inverse metric (rejects the degenerate
  witness: a nonzero covector has strictly positive cometric self-pairing).
* `cometricBilin_contMDiff` — the cometric scalar of two smooth cotangent sections is smooth.
* `exists_uniform_cometricBilin_bound` — the uniform sup envelope on the compact manifold: the
  cometric pairing of two smooth cotangent sections is bounded by a single constant over all of
  `M` (mirroring the `UniformCurvatureSup` pattern, via continuity of the smooth scalar and
  compactness).
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor0SBundle
open TensorMultilinear (contMDiffAt_section_apply contMDiff_section_apply)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The fibrewise inverse-metric sharp -/

/-- **The fibrewise inverse-metric sharp** at `x`: the index-raising operator
`Tensor0SSpace 1 I x →L[ℝ] TangentSpace I x` that sends a covector `α` to the unique tangent
vector `α^\sharp` with `g_x(α^\sharp, \cdot) = α`.  It is `metricSharp` precomposed with the
covector-to-dual identification `cotangentToDual`, closed to a continuous-linear map on the
finite-dimensional cotangent fibre.  This is the fibrewise inverse metric `g^{-1}`. -/
def inverseMetricSharpFib (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 1 I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α => metricSharp (I := I) g x (cotangentToDualLinear (I := I) (x := x) α)
      map_add' := fun α β => by
        rw [map_add (cotangentToDualLinear (I := I) (x := x))]
        rw [metricSharp_def, metricSharp_def, metricSharp_def, map_add]
      map_smul' := fun c α => by
        rw [map_smul (cotangentToDualLinear (I := I) (x := x))]
        rw [metricSharp_def, metricSharp_def, map_smul]; rfl }

@[simp] lemma inverseMetricSharpFib_apply (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) :
    inverseMetricSharpFib (I := I) g x α =
      metricSharp (I := I) g x (cotangentToDualLinear (I := I) (x := x) α) := by
  rw [inverseMetricSharpFib, LinearMap.coe_toContinuousLinearMap']; rfl

/-- **The inverse property of the sharp** (defining identity of the inverse metric).  Pairing
the raised vector `♯ α` against any tangent vector `w` with the metric recovers the covector:
`g_x(♯ α, w) = α(w)`.  This is the fibrewise statement that `g^\sharp` inverts `g^\flat`. -/
lemma inverseMetricSharpFib_inner (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    g.inner x (inverseMetricSharpFib (I := I) g x α) w =
      cotangentToDualLinear (I := I) (x := x) α w := by
  rw [inverseMetricSharpFib_apply]
  exact inner_metricSharp (I := I) g x (cotangentToDualLinear (I := I) (x := x) α) w

/-- **Self-vanishing of the inverse-metric sharp on the zero covector** (non-vacuity litmus).
The sharp of the zero covector is the zero vector.  Conversely, by `inverseMetricSharpFib_inner`
the sharp recovers the covector through the metric pairing, so a *nonzero* covector has a
*nonzero* raised vector — the inverse metric genuinely raises indices and is not the trivial
map. -/
@[simp] lemma inverseMetricSharpFib_zero (g : SmoothRiemannianMetric I M) (x : M) :
    inverseMetricSharpFib (I := I) g x 0 = 0 := by
  rw [inverseMetricSharpFib_apply, map_zero]
  rw [metricSharp_def, map_zero]

/-- **The inverse-metric sharp recovers a nonzero vector from a nonzero covector.**  If the
covector `α` is nonzero then its raised vector `♯ α` is nonzero.  This is the genuine-content
(rejects-the-degenerate-witness) companion of `inverseMetricSharpFib_zero`: the inverse metric
does not collapse covectors. -/
lemma inverseMetricSharpFib_ne_zero_of_ne_zero (g : SmoothRiemannianMetric I M) (x : M)
    {α : Tensor0SSpace 1 I x} (hα : α ≠ 0) :
    inverseMetricSharpFib (I := I) g x α ≠ 0 := by
  intro hzero
  apply hα

  have hdual : cotangentToDualLinear (I := I) (x := x) α = 0 := by
    ext w
    rw [← inverseMetricSharpFib_inner (I := I) g x α w, hzero]
    simp
  exact cotangentToDualLinear_injective (I := I) (x := x) (by rw [hdual, map_zero])

/-! ## The cometric scalar (fibrewise) -/

/-- **The cometric scalar** `g^{-1}(α, β)` on cotangent vectors at `x`: the inverse-metric inner
product of two covectors, defined as the `g`-inner product of their raised vectors.  This is the
`(2, 0)`-cometric, the canonical inverse metric on `T^*M`. -/
def cometricBilin (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) : ℝ :=
  g.inner x (inverseMetricSharpFib (I := I) g x α) (inverseMetricSharpFib (I := I) g x β)

/-- The cometric scalar equals the `g`-inner product of the two sharps. -/
lemma cometricBilin_eq_inner_sharp (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cometricBilin (I := I) g x α β =
      g.inner x (inverseMetricSharpFib (I := I) g x α)
        (inverseMetricSharpFib (I := I) g x β) := rfl

/-- The cometric scalar equals the covector `α` evaluated on the raised vector `♯ β` (the
inverse property in scalar form). -/
lemma cometricBilin_eq_dual_sharp (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cometricBilin (I := I) g x α β =
      cotangentToDualLinear (I := I) (x := x) α (inverseMetricSharpFib (I := I) g x β) := by
  rw [cometricBilin_eq_inner_sharp]
  exact inverseMetricSharpFib_inner (I := I) g x α (inverseMetricSharpFib (I := I) g x β)

/-- The cometric scalar is symmetric: `g^{-1}(α, β) = g^{-1}(β, α)`. -/
lemma cometricBilin_symm (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cometricBilin (I := I) g x α β = cometricBilin (I := I) g x β α := by
  rw [cometricBilin_eq_inner_sharp, cometricBilin_eq_inner_sharp]
  exact g.symm x _ _

/-- The cometric scalar of a covector with itself is nonnegative, and is zero only when the
covector is zero (positive-definiteness of the inverse metric).  This rejects the degenerate
witness. -/
lemma cometricBilin_self_nonneg (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) :
    0 ≤ cometricBilin (I := I) g x α α := by
  rw [cometricBilin_eq_inner_sharp]
  rcases eq_or_ne (inverseMetricSharpFib (I := I) g x α) 0 with h | h
  · rw [h]; simp
  · exact le_of_lt (g.pos x (inverseMetricSharpFib (I := I) g x α) h)

/-- The cometric scalar of a *nonzero* covector with itself is strictly positive: the inverse
metric is positive-definite (it does not collapse covectors).  This is the genuine-content
companion of `cometricBilin_self_nonneg`. -/
lemma cometricBilin_self_pos (g : SmoothRiemannianMetric I M) (x : M)
    {α : Tensor0SSpace 1 I x} (hα : α ≠ 0) :
    0 < cometricBilin (I := I) g x α α := by
  rw [cometricBilin_eq_inner_sharp]
  exact g.pos x (inverseMetricSharpFib (I := I) g x α)
    (inverseMetricSharpFib_ne_zero_of_ne_zero (I := I) g x hα)

/-! ## Smoothness of the inverse-metric operator field -/

variable [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [I.Boundaryless] [BoundarylessManifold I M] in
/-- **On-chart-source smoothness of a smooth cotangent section's chart-frame components.**  For
a globally smooth `(0, 1)`-tensor (cotangent) section `Y` and the chart-`γ` frame vector
`chartBasisVecFiber γ j`, the scalar `b ↦ (Y b)(chartBasisVecFiber γ j b)` is `C^∞` on the
chart-`γ` source.  This is the on-source localisation of the multilinear bundle evaluation
`contMDiff_section_apply`: at each source point the chart frame is smooth (on the open base set
= chart source) and `Y` is globally smooth, so the evaluation is `ContMDiffAt`, hence smooth on
the source.  It discharges the chart-component hypothesis of `metricSharp_contMDiff_total`. -/
theorem cotangentSection_chartComponent_contMDiffOn
    (Y : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (γ : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => Tensor0SSpace.toModel (Y b)
        (fun _ : Fin 1 => chartBasisVecFiber (I := I) γ j b))
      (chartAt H γ).source := by
  intro x₀ hx₀
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_section_apply (n := 1) (T := fun b => Y b) (x₀ := x₀)
  · exact Y.contMDiff.contMDiffAt
  · intro i
    have hbase : (trivializationAt E (TangentSpace I) γ).baseSet = (chartAt H γ).source :=
      TangentBundle.trivializationAt_baseSet (I := I) γ
    have hx₀base : x₀ ∈ (trivializationAt E (TangentSpace I) γ).baseSet := by
      rw [hbase]; exact hx₀
    have hopen : IsOpen (trivializationAt E (TangentSpace I) γ).baseSet :=
      (trivializationAt E (TangentSpace I) γ).open_baseSet
    exact (chartBasisVec_contMDiffOn (I := I) γ j x₀ hx₀base).contMDiffAt
      (hopen.mem_nhds hx₀base)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **Smoothness of the inverse-metric operator field.**  The fibrewise sharp
`x ↦ inverseMetricSharpFib g x : Hom(T^*M, TM)` is a smooth section of the bundle
homomorphism.

The proof applies the pointwise-smoothness bridge `contMDiff_clm_section_of_pointwise`: for
every globally smooth cotangent section `Y` the vector field `x ↦ ♯ (Y x)` is smooth.  The
latter is `metricSharp_contMDiff_total` applied to the smooth covector field
`cotangentToDual ∘ Y`, whose chart-frame components are smooth by
`cotangentSection_chartComponent_contMDiffOn`. -/
theorem inverseMetricSharpField_contMDiff (g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E →L[ℝ] E)
        (E := fun z : M => Tensor0SSpace 1 I z →L[ℝ] TangentSpace I z) x
        (inverseMetricSharpFib (I := I) g x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun x => inverseMetricSharpFib (I := I) g x)
  intro Y
  have hmain : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b
        (metricSharp (I := I) g b (cotangentToDualLinear (I := I) (x := b) (Y b)))) := by
    apply metricSharp_contMDiff_total (I := I) g
    intro γ j
    have hcongr : (fun b : M => (cotangentToDualLinear (I := I) (x := b) (Y b))
          (chartBasisVecFiber (I := I) γ j b)) =
        (fun b : M => Tensor0SSpace.toModel (Y b)
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) γ j b)) := by
      funext b
      rw [cotangentToDualLinear_apply, cotangentToDual_apply]
      rfl
    rw [hcongr]
    exact cotangentSection_chartComponent_contMDiffOn (I := I) Y γ j
  refine hmain.congr (fun x => ?_)
  change TotalSpace.mk' E x
      (metricSharp (I := I) g x (cotangentToDualLinear (I := I) (x := x) (Y x))) =
    TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
      (inverseMetricSharpFib (I := I) g x (Y x))
  rw [inverseMetricSharpFib_apply]

/-- **The inverse-metric operator field** (cometric / index-raise) of a smooth Riemannian
metric `g`, as a smooth section of the bundle homomorphism `Hom(T^*M, TM)`.  Its fibre value at
`x` is the fibrewise inverse-metric sharp `inverseMetricSharpFib g x`; smoothness is
`inverseMetricSharpField_contMDiff`.  This is the first-class reusable inverse metric. -/
def inverseMetricSharpField (g : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; Tensor0SModel 1 ℝ E →L[ℝ] E,
      (fun x : M => Tensor0SSpace 1 I x →L[ℝ] TangentSpace I x)⟯ where
  toFun := fun x : M => inverseMetricSharpFib (I := I) g x
  contMDiff_toFun := inverseMetricSharpField_contMDiff (I := I) g

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
@[simp] lemma inverseMetricSharpField_apply (g : SmoothRiemannianMetric I M) (x : M) :
    inverseMetricSharpField (I := I) g x = inverseMetricSharpFib (I := I) g x := rfl

/-! ## The cometric scalar -/

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- **Smoothness of the cometric scalar.**  For two globally smooth cotangent sections `α`, `β`,
the cometric scalar `x ↦ g^{-1}(α x, β x)` is `C^∞` on `M`.  Via `cometricBilin_eq_dual_sharp`
the value is the smooth covector `α` evaluated on the smooth raised vector `♯ β`
(`inverseMetricSharpField_contMDiff` makes `♯ β` smooth), so the multilinear bundle evaluation
`contMDiff_section_apply` applies. -/
theorem cometricBilin_contMDiff (g : SmoothRiemannianMetric I M)
    (α β : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => cometricBilin (I := I) g x (α x) (β x)) := by
  have hsharpβ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b
        (metricSharp (I := I) g b (cotangentToDualLinear (I := I) (x := b) (β b)))) := by
    apply metricSharp_contMDiff_total (I := I) g
    intro γ j
    have hcongr : (fun b : M => (cotangentToDualLinear (I := I) (x := b) (β b))
          (chartBasisVecFiber (I := I) γ j b)) =
        (fun b : M => Tensor0SSpace.toModel (β b)
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) γ j b)) := by
      funext b
      rw [cotangentToDualLinear_apply, cotangentToDual_apply]
      rfl
    rw [hcongr]
    exact cotangentSection_chartComponent_contMDiffOn (I := I) β γ j
  have hidentity : (fun x : M => cometricBilin (I := I) g x (α x) (β x)) =
      (fun b : M => Tensor0SSpace.toModel (α b)
        (fun _ : Fin 1 =>
          metricSharp (I := I) g b (cotangentToDualLinear (I := I) (x := b) (β b)))) := by
    funext b
    rw [cometricBilin_eq_dual_sharp, inverseMetricSharpFib_apply,
      cotangentToDualLinear_apply, cotangentToDual_apply]
    rfl
  rw [hidentity]
  apply contMDiff_section_apply (n := 1) (T := fun b => α b) α.contMDiff
  intro i
  exact hsharpβ

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- **Uniform sup envelope of the cometric pairing on a closed manifold.**  For two globally
smooth cotangent sections `α`, `β` on a compact manifold, there is a single constant `C`,
uniform over `M`, bounding `|g^{-1}(α x, β x)|` at every base point.  This is the cometric
analogue of the `UniformCurvatureSup` pattern: the cometric pairing is a smooth (hence
continuous) scalar function on the compact `M`, so it attains a finite bound.  It packages the
inverse metric's `≤ 0`-jet sup data on the closed manifold. -/
theorem exists_uniform_cometricBilin_bound [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (α β : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, |cometricBilin (I := I) g x (α x) (β x)| ≤ C := by
  have hcont : Continuous (fun x : M => cometricBilin (I := I) g x (α x) (β x)) :=
    (cometricBilin_contMDiff (I := I) g α β).continuous
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨0, le_refl 0, fun x => (hM.false x).elim⟩
  · obtain ⟨x₀, -, hx₀⟩ := (isCompact_univ (X := M)).exists_isMaxOn (univ_nonempty)
      (continuous_abs.comp hcont).continuousOn
    refine ⟨|cometricBilin (I := I) g x₀ (α x₀) (β x₀)|, abs_nonneg _, fun x => ?_⟩
    exact hx₀ (mem_univ x)

end DifferentialGeometry
