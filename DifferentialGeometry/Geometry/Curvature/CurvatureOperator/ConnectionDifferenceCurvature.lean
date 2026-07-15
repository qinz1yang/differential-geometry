import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection

/-!
# The curvature-difference identity of two covariant derivatives

Given two covariant derivatives `∇₀, ∇₁` on a vector bundle `V` over a smooth manifold `M`,
their Riemann curvature operators differ by terms built entirely from the *difference tensor*
`D := ∇₁ - ∇₀` (Mathlib's `CovariantDerivative.difference`, a one-form valued in the
endomorphisms of `V`).  Writing the section-level curvature as
`R^∇(X, Y) Z = ∇_X(∇_Y Z) - ∇_Y(∇_X Z) - ∇_{[X, Y]} Z` (`riemannSec`), substituting
`∇₁ = ∇₀ + D`, and collecting yields the classical formula
$$
  R^{∇₁}(X, Y) Z = R^{∇₀}(X, Y) Z
    + (∇₀_X D)(Y, Z) - (∇₀_Y D)(X, Z)
    + D(X, D(Y, Z)) - D(Y, D(X, Z)).
$$

This file proves the identity at the generality the on-disk curvature machinery supports
(arbitrary covariant derivatives on a general vector bundle), then specialises the Ricci
contraction to the Levi-Civita pair `∇₀ = LeviCivita g₀`, `∇₁ = LeviCivita g₁`, where the
difference tensor is `connDiff g₁ g₀ = CovariantDerivative.difference (LeviCivita g₁)
(LeviCivita g₀)`.

## Conventions

We follow Mathlib's argument convention `cov.toFun σ x v ≅ (∇_v σ)(x)`, so
`covApply cov X Z = ∇_X Z`.  The difference one-form satisfies
`CovariantDerivative.difference cov₁ cov₀ x (σ x) v = (∇₁_v σ - ∇₀_v σ)(x)` on sections `σ`
differentiable at `x` (`diff_eval`); thus `D = ∇₁ - ∇₀`.  The "bilinear difference section"
`diffSec cov₀ cov₁ X Z` is the section `b ↦ D b (Z b) (X b)`, i.e. `D(X, Z)` on paper.

## Main definitions

* `diffSec cov₀ cov₁ X Z` — the section `D(X, Z) : b ↦ D b (Z b) (X b)`.
* `covDerivDiff cov₀ cov₁ X Y Z x` — the directional covariant derivative `(∇₀_X D)(Y, Z) (x)`
  of the difference (1,2)-tensor under `∇₀`, on the tangent bundle.

## Main theorems

* `riemannSec_difference_raw` — the raw (torsion-free-hypothesis-free) curvature-difference
  expansion, valid for arbitrary covariant derivatives on any vector bundle.
* `riemannSec_difference` — the grouped classical identity for torsion-free `∇₀` on the
  tangent bundle, with the first-order terms packaged as `covDerivDiff`.
* `ricciTensor_sub_eq_basisSum` — the Ricci-trace corollary: the difference of the two Ricci
  tensors at a point is the model-basis trace of the per-slot section-level curvature
  difference, the form consumed by the metric-difference (DeTurck) telescoping.
* `ricciTensor_sub_eq_basisSum_difference` — the same, with the per-slot curvature difference
  expanded into the grouped `covDerivDiff`-plus-quadratic `D`-terms via `riemannSec_difference`.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open VectorField

section GeneralBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle 1 F V I]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] in
/-- Evaluation of the difference one-form on a section value, expanded into the two covariant
derivatives.  On a section `σ` differentiable at `x`,
`CovariantDerivative.difference cov₁ cov₀ x (σ x) v = (∇₁_v σ - ∇₀_v σ)(x)`. -/
theorem diff_eval (cov₀ cov₁ : CovariantDerivative I F V)
    {σ : Π x, V x} {x : M} (hσ : MDiffAt (T% σ) x) (v : TangentSpace I x) :
    CovariantDerivative.difference cov₁ cov₀ x (σ x) v
      = cov₁.toFun σ x v - cov₀.toFun σ x v := by
  have h := cov₁.isCovariantDerivativeOnUniv.difference_apply
    cov₀.isCovariantDerivativeOnUniv (x := x) (mem_univ x) (σ := σ) hσ
  have := congrArg (fun (φ : TangentSpace I x →L[ℝ] V x) => φ v) h
  simp only [ContinuousLinearMap.sub_apply] at this
  rw [show CovariantDerivative.difference cov₁ cov₀ =
      cov₁.isCovariantDerivativeOnUniv.difference cov₀.isCovariantDerivativeOnUniv from rfl]
  exact this

/-- The **bilinear difference section** `D(X, Z) := b ↦ D b (Z b) (X b)`, where
`D = CovariantDerivative.difference cov₁ cov₀` is the difference one-form.  This is the
covariant-derivative correction `∇₁_X Z - ∇₀_X Z` on differentiable `Z` (`covApply_cov1_eq`). -/
def diffSec (cov₀ cov₁ : CovariantDerivative I F V)
    (X : Π b : M, TangentSpace I b) (Z : Π b : M, V b) : Π b : M, V b :=
  fun b => CovariantDerivative.difference cov₁ cov₀ b (Z b) (X b)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] in
/-- On a section `Z` differentiable at `b`, `∇₁_X Z = ∇₀_X Z + D(X, Z)` pointwise. -/
theorem covApply_cov1_eq (cov₀ cov₁ : CovariantDerivative I F V)
    {X : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {b : M} (hZ : MDiffAt (T% Z) b) :
    covApply cov₁ X Z b = covApply cov₀ X Z b + diffSec cov₀ cov₁ X Z b := by
  simp only [covApply, diffSec]
  rw [diff_eval cov₀ cov₁ hZ]
  abel

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] in
/-- On a section `Z` differentiable at `b`, `D(X, Z) = ∇₁_X Z - ∇₀_X Z` pointwise. -/
theorem diffSec_eq_sub (cov₀ cov₁ : CovariantDerivative I F V)
    {X : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {b : M} (hZ : MDiffAt (T% Z) b) :
    diffSec cov₀ cov₁ X Z b = covApply cov₁ X Z b - covApply cov₀ X Z b := by
  simp only [diffSec, covApply]
  rw [diff_eval cov₀ cov₁ hZ]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [BoundarylessManifold I M] in
/-- **Smoothness of the bilinear difference section.**  For smooth covariant derivatives and
smooth tangent field `X` and section `Z`, the difference section `D(X, Z)` is smooth. -/
theorem diffSec_contMDiff (cov₀ cov₁ : CovariantDerivative I F V)
    [CovariantDerivative.ContMDiffCovariantDerivative cov₀ ∞]
    [CovariantDerivative.ContMDiffCovariantDerivative cov₁ ∞]
    {X : Π b : M, TangentSpace I b} {Z : Π b : M, V b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z)) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (diffSec cov₀ cov₁ X Z)) := by
  have hZ' : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z) := hZ.of_le le_self_add
  have h1 : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov₁ X Z)) Set.univ :=
    covApply_contMDiffOn (cov := cov₁) hX hZ
  have h0 : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov₀ X Z)) Set.univ :=
    covApply_contMDiffOn (cov := cov₀) hX hZ
  have hsub := h1.sub_section h0
  rw [← contMDiffOn_univ]
  refine hsub.congr (fun b _hb => ?_)
  have hZb : MDiffAt (T% Z) b := (hZ' b).mdifferentiableAt (by simp)
  change (⟨b, diffSec cov₀ cov₁ X Z b⟩ : TotalSpace F V) =
      ⟨b, ((fun y => covApply cov₁ X Z y) - (fun y => covApply cov₀ X Z y)) b⟩
  rw [Pi.sub_apply, diffSec_eq_sub cov₀ cov₁ hZb]

section Smooth

variable (cov₀ cov₁ : CovariantDerivative I F V)
  [CovariantDerivative.ContMDiffCovariantDerivative cov₀ ∞]
  [CovariantDerivative.ContMDiffCovariantDerivative cov₁ ∞]
  {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b}
  (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
  (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
  (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [BoundarylessManifold I M] in
include hY hZ in
/-- Expansion of the outer `∇₁` term `∇₁_X(∇₁_Y Z) (x)` into its `∇₀`-curvature contributions
plus the difference-one-form correction.  This is the technical heart of the curvature
expansion: the inner section `∇₁_Y Z` is rewritten as `∇₀_Y Z + D(Y, Z)`, the outer `∇₁` is
expanded via `diff_eval`, and the `∇₀`-derivative is split by additivity.  The differentiated
slot `X` enters only as a direction value, so only the smoothness of `Y, Z` is required. -/
theorem covApply_cov1_outer_expand (x : M) :
    cov₁.toFun (covApply cov₁ Y Z) x (X x) =
      cov₀.toFun (covApply cov₀ Y Z) x (X x)
      + cov₀.toFun (diffSec cov₀ cov₁ Y Z) x (X x)
      + CovariantDerivative.difference cov₁ cov₀ x
          ((covApply cov₀ Y Z + diffSec cov₀ cov₁ Y Z) x) (X x) := by
  classical
  have hZ1 : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
  have hcov0YZ : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov₀ Y Z)) Set.univ :=
    covApply_contMDiffOn (cov := cov₀) hY hZ1
  have hcov1YZ : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov₁ Y Z)) Set.univ :=
    covApply_contMDiffOn (cov := cov₁) hY hZ1
  have hdiffYZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (diffSec cov₀ cov₁ Y Z)) :=
    diffSec_contMDiff cov₀ cov₁ hY hZ1
  have hcov0YZ_at : MDiffAt (T% (covApply cov₀ Y Z)) x :=
    (hcov0YZ.contMDiffAt (Filter.univ_mem)).mdifferentiableAt (by simp)
  have hcov1YZ_at : MDiffAt (T% (covApply cov₁ Y Z)) x :=
    (hcov1YZ.contMDiffAt (Filter.univ_mem)).mdifferentiableAt (by simp)
  have hdiffYZ_at : MDiffAt (T% (diffSec cov₀ cov₁ Y Z)) x :=
    (hdiffYZ x).mdifferentiableAt (by simp)
  have hsum_at : MDiffAt (T% (covApply cov₀ Y Z + diffSec cov₀ cov₁ Y Z)) x :=
    mdifferentiableAt_add_section hcov0YZ_at hdiffYZ_at
  have hZ_nhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% Z) b :=
    Filter.Eventually.of_forall (hZ.mdifferentiable (by simp))
  have hev : ∀ᶠ b in 𝓝 x,
      covApply cov₁ Y Z b = (covApply cov₀ Y Z + diffSec cov₀ cov₁ Y Z) b := by
    filter_upwards [hZ_nhd] with b hZb
    rw [Pi.add_apply]
    exact covApply_cov1_eq cov₀ cov₁ hZb
  have hswap : cov₁.toFun (covApply cov₁ Y Z) x =
      cov₁.toFun (covApply cov₀ Y Z + diffSec cov₀ cov₁ Y Z) x :=
    cov₁.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hcov1YZ_at hsum_at
      (Filter.univ_mem) hev
  rw [hswap]
  have hexp : cov₁.toFun (covApply cov₀ Y Z + diffSec cov₀ cov₁ Y Z) x (X x) =
      cov₀.toFun (covApply cov₀ Y Z + diffSec cov₀ cov₁ Y Z) x (X x)
      + CovariantDerivative.difference cov₁ cov₀ x
          ((covApply cov₀ Y Z + diffSec cov₀ cov₁ Y Z) x) (X x) := by
    rw [diff_eval cov₀ cov₁ hsum_at]
    abel
  rw [hexp]
  have hadd0 : cov₀.toFun (covApply cov₀ Y Z + diffSec cov₀ cov₁ Y Z) x =
      cov₀.toFun (covApply cov₀ Y Z) x + cov₀.toFun (diffSec cov₀ cov₁ Y Z) x :=
    cov₀.isCovariantDerivativeOnUniv.add hcov0YZ_at hdiffYZ_at
  rw [hadd0]
  simp only [ContinuousLinearMap.add_apply]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [CovariantDerivative.ContMDiffCovariantDerivative cov₀ ∞]
  [CovariantDerivative.ContMDiffCovariantDerivative cov₁ ∞] hX hY hZ in
/-- Expansion of the bracket term `∇₁_W Z (x)` into `∇₀_W Z (x) + D(W, Z)(x)`. -/
theorem covApply_cov1_bracket_expand {x : M} (hZx : MDiffAt (T% Z) x) (w : TangentSpace I x) :
    cov₁.toFun Z x w = cov₀.toFun Z x w
      + CovariantDerivative.difference cov₁ cov₀ x (Z x) w := by
  rw [diff_eval cov₀ cov₁ hZx]
  abel

omit [CompleteSpace E] [FiniteDimensional ℝ E] [BoundarylessManifold I M] in
include hX hY hZ in
/-- **Raw curvature-difference expansion** of two covariant derivatives on a general vector
bundle, requiring no torsion hypothesis.  The first-order block is written un-grouped as the
covariant `∇₀`-derivatives of the difference section, plus the bracket-direction
difference-one-form term; the second-order block is the quadratic `D`-pairing.  See
`riemannSec_difference` for the grouped classical form on the tangent bundle. -/
theorem riemannSec_difference_raw (x : M) :
    riemannSec cov₁ X Y Z x =
      riemannSec cov₀ X Y Z x
      + (cov₀.toFun (diffSec cov₀ cov₁ Y Z) x (X x)
          - cov₀.toFun (diffSec cov₀ cov₁ X Z) x (Y x)
          - CovariantDerivative.difference cov₁ cov₀ x (Z x)
              (VectorField.mlieBracket I X Y x))
      + (CovariantDerivative.difference cov₁ cov₀ x (covApply cov₀ Y Z x) (X x)
          - CovariantDerivative.difference cov₁ cov₀ x (covApply cov₀ X Z x) (Y x))
      + (CovariantDerivative.difference cov₁ cov₀ x (diffSec cov₀ cov₁ Y Z x) (X x)
          - CovariantDerivative.difference cov₁ cov₀ x (diffSec cov₀ cov₁ X Z x) (Y x)) := by
  classical
  have hZx : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt (by simp)
  rw [riemannSec_def cov₁ X Y Z x]
  rw [covApply_cov1_outer_expand (X := X) (Y := Y) cov₀ cov₁ hY hZ x]
  rw [covApply_cov1_outer_expand (X := Y) (Y := X) cov₀ cov₁ hX hZ x]
  rw [covApply_cov1_bracket_expand cov₀ cov₁ hZx (VectorField.mlieBracket I X Y x)]
  rw [riemannSec_def cov₀ X Y Z x]
  have hsplitX : CovariantDerivative.difference cov₁ cov₀ x
        ((covApply cov₀ Y Z + diffSec cov₀ cov₁ Y Z) x) (X x) =
      CovariantDerivative.difference cov₁ cov₀ x (covApply cov₀ Y Z x) (X x)
      + CovariantDerivative.difference cov₁ cov₀ x (diffSec cov₀ cov₁ Y Z x) (X x) := by
    rw [Pi.add_apply, map_add, ContinuousLinearMap.add_apply]
  have hsplitY : CovariantDerivative.difference cov₁ cov₀ x
        ((covApply cov₀ X Z + diffSec cov₀ cov₁ X Z) x) (Y x) =
      CovariantDerivative.difference cov₁ cov₀ x (covApply cov₀ X Z x) (Y x)
      + CovariantDerivative.difference cov₁ cov₀ x (diffSec cov₀ cov₁ X Z x) (Y x) := by
    rw [Pi.add_apply, map_add, ContinuousLinearMap.add_apply]
  rw [hsplitX, hsplitY]
  abel

end Smooth

end GeneralBundle

section Tangent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]

variable (cov₀ cov₁ : CovariantDerivative I E (TangentSpace I : M → Type _))
  [CovariantDerivative.ContMDiffCovariantDerivative cov₀ ∞]
  [CovariantDerivative.ContMDiffCovariantDerivative cov₁ ∞]

/-- The directional **covariant derivative of the difference (1,2)-tensor** `D = ∇₁ - ∇₀`
under `∇₀`, on the tangent bundle:
`(∇₀_X D)(Y, Z) (x) = ∇₀_X(D(Y, Z)) (x) - D(∇₀_X Y, Z)(x) - D(Y, ∇₀_X Z)(x)`.
With Mathlib's argument convention this expands to
`cov₀.toFun (D(Y, Z)) x (X x) - D x (Z x) (∇₀_X Y (x)) - D x (∇₀_X Z (x)) (Y x)`, the standard
coordinate-free covariant derivative of a `(1,2)`-tensor along `X`. -/
def covDerivDiff (X Y Z : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  cov₀.toFun (diffSec cov₀ cov₁ Y Z) x (X x)
    - CovariantDerivative.difference cov₁ cov₀ x (Z x) (covApply cov₀ X Y x)
    - CovariantDerivative.difference cov₁ cov₀ x (covApply cov₀ X Z x) (Y x)

variable {X Y Z : Π b : M, TangentSpace I b}
  (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
  (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
  (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))

omit [BoundarylessManifold I M] in
include hX hY hZ in
/-- **Grouped (classical) curvature-difference identity** for a torsion-free `∇₀` on the
tangent bundle:
$$
  R^{∇₁}(X, Y) Z = R^{∇₀}(X, Y) Z
    + (∇₀_X D)(Y, Z) - (∇₀_Y D)(X, Z)
    + D(X, D(Y, Z)) - D(Y, D(X, Z)),
$$
where `D = CovariantDerivative.difference cov₁ cov₀`.  The grouping of the first-order terms
into `covDerivDiff` uses the torsion-free identity `∇₀_X Y - ∇₀_Y X = [X, Y]` to absorb the
bracket-direction term. -/
theorem riemannSec_difference (htor : cov₀.torsion = 0) (x : M) :
    riemannSec cov₁ X Y Z x =
      riemannSec cov₀ X Y Z x
      + (covDerivDiff cov₀ cov₁ X Y Z x - covDerivDiff cov₀ cov₁ Y X Z x)
      + (CovariantDerivative.difference cov₁ cov₀ x (diffSec cov₀ cov₁ Y Z x) (X x)
          - CovariantDerivative.difference cov₁ cov₀ x (diffSec cov₀ cov₁ X Z x) (Y x)) := by
  classical
  have hXx : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hYx : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  rw [riemannSec_difference_raw cov₀ cov₁ hX hY hZ x]
  unfold covDerivDiff
  have htf : covApply cov₀ X Y x - covApply cov₀ Y X x = VectorField.mlieBracket I X Y x :=
    covApply_sub_eq_mlieBracket cov₀ htor hXx hYx
  have hbr : CovariantDerivative.difference cov₁ cov₀ x (Z x)
        (VectorField.mlieBracket I X Y x) =
      CovariantDerivative.difference cov₁ cov₀ x (Z x) (covApply cov₀ X Y x)
        - CovariantDerivative.difference cov₁ cov₀ x (Z x) (covApply cov₀ Y X x) := by
    rw [← htf, map_sub]
  rw [hbr]
  abel

end Tangent

section Ricci

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure

/-- **Ricci-trace corollary (per-slot section form).**  For two smooth Riemannian metrics
`g₀, g₁` and fibre vectors `v, w ∈ T_x M`, the difference of their Ricci tensors at `x` is the
model-basis trace of the per-slot section-level curvature difference of the two Levi-Civita
covariant derivatives, evaluated on the smooth extensions of the model-basis frame and of
`v, w`:
$$
  \mathrm{Ric}^{g₁}(v, w) - \mathrm{Ric}^{g₀}(v, w)
    = \sum_i \bigl[\,b\bigr]_i\Bigl(R^{∇₁}(B_i, V) W - R^{∇₀}(B_i, V) W\Bigr)(x),
$$
where `b = chartModelBasis E`, `B_i = smoothExtensionTangent x (b i)`,
`V = smoothExtensionTangent x v`, `W = smoothExtensionTangent x w`.  This is the form the
DeTurck metric-difference telescoping consumes: each summand is a section-level curvature
difference, expandable into the difference-tensor terms via `riemannSec_difference`. -/
theorem ricciTensor_sub_eq_basisSum (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₀ x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
            (riemannSec (LeviCivita (I := I) g₁)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x w) x) i
          - (chartModelBasis E).repr
            (riemannSec (LeviCivita (I := I) g₀)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x w) x) i) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set b := chartModelBasis E with hb
  set V := smoothExtensionTangent (I := I) x v with hV
  set W := smoothExtensionTangent (I := I) x w with hW
  have hV_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V) := smoothExtensionTangent_contMDiff x v
  have hW_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W) := smoothExtensionTangent_contMDiff x w
  have hVx : V x = v := smoothExtensionTangent_eq x v
  have hWx : W x = w := smoothExtensionTangent_eq x w
  rw [ricciTensor_apply_basisSum (I := I) g₁ x v w,
      ricciTensor_apply_basisSum (I := I) g₀ x v w,
      ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  set B := smoothExtensionTangent (I := I) x (b i) with hB
  have hB_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B) := smoothExtensionTangent_contMDiff x (b i)
  have hBx : B x = b i := smoothExtensionTangent_eq x (b i)
  have h1 : riemannOp (LeviCivita (I := I) g₁) x (b i) v w =
      riemannSec (LeviCivita (I := I) g₁) B V W x := by
    rw [show (b i : TangentSpace I x) = B x from hBx.symm, show v = V x from hVx.symm,
        show w = W x from hWx.symm,
        riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁) hB_sm hV_sm hW_sm]
  have h0 : riemannOp (LeviCivita (I := I) g₀) x (b i) v w =
      riemannSec (LeviCivita (I := I) g₀) B V W x := by
    rw [show (b i : TangentSpace I x) = B x from hBx.symm, show v = V x from hVx.symm,
        show w = W x from hWx.symm,
        riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀) hB_sm hV_sm hW_sm]
  rw [h1, h0]

/-- **Ricci-trace corollary (expanded difference-tensor form).**  Combining
`ricciTensor_sub_eq_basisSum` with the grouped curvature-difference identity
`riemannSec_difference` (applied to `∇₀ = LeviCivita g₀`, `∇₁ = LeviCivita g₁`, which is
torsion-free), the Ricci difference at `x` is the model-basis trace of the grouped
difference-tensor terms:
$$
  \mathrm{Ric}^{g₁}(v, w) - \mathrm{Ric}^{g₀}(v, w)
    = \sum_i \bigl[\,b\bigr]_i\Bigl(
        (∇₀_{B_i} D)(V, W) - (∇₀_V D)(B_i, W)
        + D(B_i, D(V, W)) - D(V, D(B_i, W))
      \Bigr)(x),
$$
where `D = CovariantDerivative.difference (LeviCivita g₁) (LeviCivita g₀)` (definitionally
`connDiff g₁ g₀`).  This is the fully expanded telescoping kernel. -/
theorem ricciTensor_sub_eq_basisSum_difference (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₀ x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x w) x
              - covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x w) x)
            + (CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x v)
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - CovariantDerivative.difference (LeviCivita (I := I) g₁)
                    (LeviCivita (I := I) g₀) x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x v x))) i := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [ricciTensor_sub_eq_basisSum (I := I) g₀ g₁ x v w]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  set B := smoothExtensionTangent (I := I) x ((chartModelBasis E) i) with hB
  set V := smoothExtensionTangent (I := I) x v with hV
  set W := smoothExtensionTangent (I := I) x w with hW
  have hB_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B) :=
    smoothExtensionTangent_contMDiff x ((chartModelBasis E) i)
  have hV_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V) := smoothExtensionTangent_contMDiff x v
  have hW_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W) := smoothExtensionTangent_contMDiff x w
  have htor : (LeviCivita (I := I) g₀).torsion = 0 := LeviCivita_torsion_eq_zero (I := I) g₀
  have hdiff := riemannSec_difference (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
    hB_sm hV_sm hW_sm htor x
  have hdiff_sub :
      riemannSec (LeviCivita (I := I) g₁) B V W x
        - riemannSec (LeviCivita (I := I) g₀) B V W x =
      (covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) B V W x
          - covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) V B W x)
        + (CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
              (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) V W x) (B x)
            - CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
              (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) B W x) (V x)) := by
    rw [hdiff]; abel
  have hreprsub :
      (chartModelBasis E).repr (riemannSec (LeviCivita (I := I) g₁) B V W x) i
        - (chartModelBasis E).repr (riemannSec (LeviCivita (I := I) g₀) B V W x) i =
      (chartModelBasis E).repr
        (riemannSec (LeviCivita (I := I) g₁) B V W x
          - riemannSec (LeviCivita (I := I) g₀) B V W x) i := by
    have hms : (chartModelBasis E).repr
        (riemannSec (LeviCivita (I := I) g₁) B V W x
          - riemannSec (LeviCivita (I := I) g₀) B V W x) =
        (chartModelBasis E).repr (riemannSec (LeviCivita (I := I) g₁) B V W x)
          - (chartModelBasis E).repr (riemannSec (LeviCivita (I := I) g₀) B V W x) :=
      map_sub (chartModelBasis E).repr _ _
    rw [hms, Finsupp.sub_apply]
  rw [hreprsub, hdiff_sub]

end Ricci

end Connection
end Integral
end DifferentialGeometry
