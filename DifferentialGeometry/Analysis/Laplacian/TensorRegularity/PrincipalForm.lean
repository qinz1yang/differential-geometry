import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.ChartPrimitives
import DifferentialGeometry.Analysis.Laplacian.Operator.ChartLocalLaplacian

/-!
# The principal-part elliptic bilinear form for tensor sections

A chart-local elliptic-regularity analysis of the connection Laplacian on
`(r, s)`-tensor sections proceeds by routing through the scalar chart components
`tensorChartComp g r s T α Idx Jdx`. In a chart, the Dirichlet bilinear form
attached to the connection Laplacian has a **principal part that is
component-diagonal**: each scalar chart component pairs only with itself, through
the second-order operator whose divergence-form coefficient is the
volume-weighted inverse Gram matrix `√(det g) · gᵏˡ`. That coefficient is
precisely the principal part of the scalar Laplace–Beltrami operator.

This file packages that principal part as a
`SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN)` — the
exact divergence-form data structure consumed by the Euclidean elliptic
interior-regularity engine — so that the engine can be applied per scalar
component.

## Construction

The volume-weighted inverse Gram matrix `weightedInvGramEuclid g α` is smooth
and uniformly elliptic only on the *open* chart-Euclidean target
`chartTargetEuclid α`; it degenerates towards the boundary of that target. A
uniformly elliptic `SmoothEllipticBilinearForm` on all of `EuclN` therefore
cannot agree with it everywhere. The correct device — already provided by the
scalar campaign as `exists_smooth_metric_extension` — fixes a compact
`K ⊆ chartTargetEuclid α` and produces a globally smooth, globally uniformly
elliptic form that agrees with `weightedInvGramEuclid g α` exactly on `K`
(interpolating to the identity matrix off a compact neighborhood of `K`). The
principal-part form for tensor sections is *the same form*: rather than
re-deriving the off-chart smooth uniformly-elliptic extension, we reuse the
scalar construction directly.

`tensorPrincipalForm g α hK hK_target` is hence the
`SmoothEllipticBilinearForm` extracted from `exists_smooth_metric_extension`
for the supplied compact `K`. Its zeroth-order coefficient is `0`, and on `K`
its principal coefficient matrix equals `weightedInvGramEuclid g α`.

## Main definitions

* `tensorPrincipalForm g α hK hK_target` — the divergence-form data for the
  component-diagonal principal part of the tensor connection Laplacian, a
  `SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN)`.

## Main results

* `tensorPrincipalForm_a_eq_weightedInvGramEuclid` — on the chosen compact `K`,
  the principal coefficient matrix `(tensorPrincipalForm …).a` agrees entrywise
  with `weightedInvGramEuclid g α` (which equals `√(det g) · gᵏˡ`).
* `tensorPrincipalForm_c` — the zeroth-order coefficient
  `(tensorPrincipalForm …).c` is identically `0`.
* `tensorPrincipalForm_c_apply` — pointwise form of `tensorPrincipalForm_c`.
* `tensorPrincipalForm_eq_scalar_metric_form` — `tensorPrincipalForm` is, by
  construction, a `SmoothEllipticBilinearForm` produced by the scalar metric
  extension `exists_smooth_metric_extension`: it satisfies the same
  agreement-on-`K` and `c = 0` characterisation. This records that the tensor
  principal part *is* the scalar Laplace–Beltrami principal part.
* `tensorPrincipalForm_symm`, `tensorPrincipalForm_coercive` — the symmetry and
  uniform-ellipticity (coercivity) of the principal coefficient matrix,
  re-exposed from the structure fields for downstream use.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Laplacian.MetricExtension

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The Euclidean chart primitive `weightedInvGramEuclid g α k l` coincides with
the metric-extension pull-back `weightedInvGramOnEuclid g α k l`. Both are the
volume-weighted inverse Gram entry `√(det g) · gᵏˡ` in chart-Euclidean
coordinates; the equality is definitional. -/
theorem weightedInvGramEuclid_eq_weightedInvGramOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    weightedInvGramEuclid (I := I) g α k l =
      weightedInvGramOnEuclid (I := I) g α k l :=
  rfl

/-- Existence of the divergence-form data for the component-diagonal principal
part: a `SmoothEllipticBilinearForm` on `Set.univ : Set EuclN` whose principal
coefficient matrix agrees on the compact `K` with `weightedInvGramEuclid g α`
(the volume-weighted inverse Gram matrix `√(det g) · gᵏˡ`) and whose
zeroth-order coefficient is identically `0`. This is the `∃ B`-payload of
`exists_smooth_metric_extension`. -/
theorem exists_tensorPrincipalForm
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN),
      (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramEuclid (I := I) g α i j y) ∧
      B.c = (fun _ : EuclN => (0 : ℝ)) := by
  obtain ⟨_, _, _, _, _, B, hB_agree, hB_c⟩ :=
    exists_smooth_metric_extension (I := I) (M := M) g α hK hK_target
  exact ⟨B, hB_agree, hB_c⟩

/-- **The principal-part elliptic bilinear form for tensor sections.**

For a smooth Riemannian metric `g` on a closed (compact, boundaryless) smooth
manifold `M`, a chart point `α : M`, and a compact set
`K ⊆ chartTargetEuclid α`, this is the smooth uniformly-elliptic divergence-form
data of the component-diagonal principal part of the connection Laplacian's
chart Dirichlet form.

It is, by construction, the `SmoothEllipticBilinearForm` produced by the scalar
metric extension `exists_smooth_metric_extension`: rather than rebuilding the
off-chart smooth uniformly-elliptic extension of `weightedInvGramEuclid g α`, we
reuse the scalar Laplace–Beltrami principal-part form directly. The principal
coefficient matrix `(tensorPrincipalForm g α hK hK_target).a` agrees on `K` with
`weightedInvGramEuclid g α` (`= √(det g) · gᵏˡ`), and the zeroth-order
coefficient is identically `0`. -/
def tensorPrincipalForm
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN) :=
  Classical.choose (exists_tensorPrincipalForm (I := I) (M := M) g α hK hK_target)

/-- Defining property of `tensorPrincipalForm`: it satisfies the agreement-on-`K`
and `c = 0` characterisation of the scalar metric-extension form. -/
theorem tensorPrincipalForm_spec
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y i j =
          weightedInvGramEuclid (I := I) g α i j y) ∧
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).c =
        (fun _ : EuclN => (0 : ℝ)) :=
  Classical.choose_spec (exists_tensorPrincipalForm (I := I) (M := M) g α hK hK_target)

/-- **Coefficient bridge (principal part).** On the compact `K ⊆ chartTargetEuclid α`,
the principal coefficient matrix of `tensorPrincipalForm` agrees entrywise with
`weightedInvGramEuclid g α` — the volume-weighted inverse Gram matrix
`√(det g) · gᵏˡ` in chart-Euclidean coordinates. -/
theorem tensorPrincipalForm_a_eq_weightedInvGramEuclid
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {y : EuclN} (hy : y ∈ K) (i j : Fin (Module.finrank ℝ E)) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y i j =
      weightedInvGramEuclid (I := I) g α i j y :=
  (tensorPrincipalForm_spec (I := I) (M := M) g α hK hK_target).1 y hy i j

/-- **Coefficient bridge (zeroth order).** The zeroth-order coefficient of
`tensorPrincipalForm` is identically the zero function: the principal part of
the connection Laplacian carries no zeroth-order term. -/
theorem tensorPrincipalForm_c
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).c =
      (fun _ : EuclN => (0 : ℝ)) :=
  (tensorPrincipalForm_spec (I := I) (M := M) g α hK hK_target).2

/-- Pointwise form of `tensorPrincipalForm_c`: the zeroth-order coefficient
vanishes at every point. -/
theorem tensorPrincipalForm_c_apply
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (y : EuclN) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).c y = 0 := by
  rw [tensorPrincipalForm_c (I := I) (M := M) g α hK hK_target]

/-- **Identification with the scalar principal part.** `tensorPrincipalForm` is a
`SmoothEllipticBilinearForm` produced by the scalar metric extension
`exists_smooth_metric_extension`: it agrees on `K` with `weightedInvGramEuclid`
and has vanishing zeroth-order coefficient. Equivalently, the component-diagonal
principal part of the tensor connection Laplacian is the principal part of the
scalar Laplace–Beltrami operator. -/
theorem tensorPrincipalForm_eq_scalar_metric_form
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN),
      B = tensorPrincipalForm (I := I) (M := M) g α hK hK_target ∧
      (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramEuclid (I := I) g α i j y) ∧
      B.c = (fun _ : EuclN => (0 : ℝ)) :=
  ⟨tensorPrincipalForm (I := I) (M := M) g α hK hK_target, rfl,
    tensorPrincipalForm_spec (I := I) (M := M) g α hK hK_target⟩

/-- The principal coefficient matrix of `tensorPrincipalForm` is symmetric:
`a y i j = a y j i` for all `y, i, j`. -/
theorem tensorPrincipalForm_symm
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (y : EuclN) (i j : Fin (Module.finrank ℝ E)) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y i j =
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y j i :=
  (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).symm y i j

/-- The lower ellipticity constant of `tensorPrincipalForm` is strictly
positive. -/
theorem tensorPrincipalForm_lam_pos
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    0 < (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).lam :=
  (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).hlam_pos

/-- **Uniform ellipticity of `tensorPrincipalForm`.** The principal coefficient
matrix is coercive on all of `EuclN`: with `lam > 0` its lower ellipticity
constant, `lam · ‖ξ‖² ≤ ⟪ξ, a y · ξ⟫` for every point `y` and every direction
`ξ`. -/
theorem tensorPrincipalForm_coercive
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (y : EuclN) (ξ : EuclN) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).lam * ‖ξ‖ ^ 2 ≤
      ⟪ξ, DeGiorgi.matMulE
        ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y) ξ⟫_ℝ :=
  (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).coercive y
    (Set.mem_univ y) ξ

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
