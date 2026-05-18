import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Connection.CurvatureBundling
import DifferentialGeometry.Integral.Connection.Ricci

/-!
# Intrinsic Riemann curvature at a point

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`, the bundled
Levi-Civita covariant derivative gives at each base point `x : M` a continuous
trilinear form on the tangent space — the value at `x` of the Riemann curvature
endomorphism `(V, W) ↦ R(V, W) X`.

This file packages that bundled form as `intrinsicRiemann g x`, specialised to the
tangent-bundle case `V = TangentSpace I` of the general `riemannOp`. The
chart-independence is built in: `intrinsicRiemann` is defined directly as the
bundled fibre-trilinear form, not via any specific chart.

## Main contents

* `intrinsicRiemann g x` — the bundled trilinear form
  `T_x M →L[ℝ] T_x M →L[ℝ] T_x M →L[ℝ] T_x M`.
* `intrinsicRiemann_apply_smooth` — the section-evaluation formula on smooth global
  tangent-bundle sections, identifying `intrinsicRiemann g x (X x) (Y x) (Z x)` with
  `riemannSec (LeviCivita g) X Y Z x`.
* `intrinsicRiemann_swap` — antisymmetry in the first two arguments.
* `intrinsicRiemann_self_eq_zero` — vanishing on coincident first two arguments.
* `intrinsicRiemann_metric_skew` — metric skew-symmetry in the last argument.
* `intrinsicRiemann_first_bianchi` — first Bianchi identity at a point.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **Intrinsic Riemann curvature operator at a point.** For a smooth
Riemannian metric `g` on a boundaryless smooth manifold `M`, the bundled
Levi-Civita connection provides at each `x : M` a continuous trilinear
form `T_x M × T_x M × T_x M → T_x M` — the value of the curvature
endomorphism `(X, Y) ↦ R(X, Y) Z` at `x`.

This is the intrinsic counterpart of the chart-local
`chartRiemannTensor` in `Geometry/Curvature/Riemann.lean`. The two are
related by the standard component formula but the intrinsic version is
chart-independent by construction. -/
noncomputable def intrinsicRiemann
    (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x :=
  riemannOp (cov := LeviCivita (I := I) g) x

/-- **Smooth-section application formula for `intrinsicRiemann`.** For
smooth global tangent-bundle sections `X, Y, Z`, the value of
`intrinsicRiemann g x` on `(X x, Y x, Z x)` equals the section-level
Riemann tensor `riemannSec (LeviCivita g) X Y Z` at `x`. -/
theorem intrinsicRiemann_apply_smooth
    (g : SmoothRiemannianMetric I M) {x : M}
    {X Y Z : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    intrinsicRiemann (I := I) g x (X x) (Y x) (Z x) =
      riemannSec (LeviCivita (I := I) g) X Y Z x := by
  unfold intrinsicRiemann
  exact riemannOp_apply_smooth (cov := LeviCivita (I := I) g) hX hY hZ

/-- **Antisymmetry in the first two arguments.** The intrinsic curvature
satisfies `R(V, W) X = -R(W, V) X` at every point. Inherited from the
general `riemannOp_swap` valid for every `CovariantDerivative`. -/
theorem intrinsicRiemann_swap
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W X : TangentSpace I x) :
    intrinsicRiemann (I := I) g x V W X =
      -intrinsicRiemann (I := I) g x W V X := by
  unfold intrinsicRiemann
  exact riemannOp_swap (cov := LeviCivita (I := I) g) x V W X

/-- **Antisymmetry at coincident slots.** `R(V, V) X = 0` for every
tangent vector `V` and every `X` at `x`. From antisymmetry with `W = V`:
`R(V, V) X = -R(V, V) X`, hence `2 · R(V, V) X = 0`, hence `R(V, V) X = 0`. -/
theorem intrinsicRiemann_self_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (V X : TangentSpace I x) :
    intrinsicRiemann (I := I) g x V V X = 0 := by
  have h := intrinsicRiemann_swap (I := I) g x V V X
  -- `h : intrinsicRiemann g x V V X = -intrinsicRiemann g x V V X`.
  -- Hence `2 • a = 0` and so `a = 0`, since `2 ≠ 0` in `ℝ`.
  set a : TangentSpace I x := intrinsicRiemann (I := I) g x V V X with ha
  have ha_eq : a = -a := h
  have hsum : a + a = 0 := by
    nth_rewrite 2 [ha_eq]
    exact add_neg_cancel a
  have h2 : (2 : ℝ) • a = 0 := by
    rw [two_smul]; exact hsum
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp h2).resolve_left h2ne

/-- **Metric skew-symmetry in the last argument.** For every smooth Riemannian
metric `g` on a boundaryless manifold and every quadruple of tangent vectors at
`x`,
$$
  g\bigl(R(V, W) X, Y\bigr) + g\bigl(X, R(V, W) Y\bigr) = 0.
$$
Proved by extending each fibre vector to a globally smooth tangent-bundle
section via `smoothExtensionTangent`, applying the section-level identity
`riemannSec_metric_skew`, and unwinding through `intrinsicRiemann_apply_smooth`. -/
theorem intrinsicRiemann_metric_skew
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W X Y : TangentSpace I x) :
    g.inner x (intrinsicRiemann (I := I) g x V W X) Y +
      g.inner x X (intrinsicRiemann (I := I) g x V W Y) = 0 := by
  classical
  -- Smooth extensions of the four fibre vectors.
  set V' := smoothExtensionTangent (I := I) x V with hV'def
  set W' := smoothExtensionTangent (I := I) x W with hW'def
  set X' := smoothExtensionTangent (I := I) x X with hX'def
  set Y' := smoothExtensionTangent (I := I) x Y with hY'def
  have hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V') :=
    smoothExtensionTangent_contMDiff x V
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W') :=
    smoothExtensionTangent_contMDiff x W
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X') :=
    smoothExtensionTangent_contMDiff x X
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y') :=
    smoothExtensionTangent_contMDiff x Y
  have hVx : V' x = V := smoothExtensionTangent_eq x V
  have hWx : W' x = W := smoothExtensionTangent_eq x W
  have hXx : X' x = X := smoothExtensionTangent_eq x X
  have hYx : Y' x = Y := smoothExtensionTangent_eq x Y
  -- Rewrite the fibre vectors as values of the smooth extensions.
  rw [show V = V' x from hVx.symm, show W = W' x from hWx.symm,
      show X = X' x from hXx.symm, show Y = Y' x from hYx.symm,
      intrinsicRiemann_apply_smooth (I := I) g hV hW hX,
      intrinsicRiemann_apply_smooth (I := I) g hV hW hY]
  -- Apply the section-level metric skewness identity.
  exact riemannSec_metric_skew (I := I) g hV hW hX hY

/-- **First Bianchi identity for the intrinsic Riemann curvature.** For every smooth
Riemannian metric `g` on a boundaryless smooth manifold `M` and every triple of tangent
vectors `V, W, X` at `x`,
$$
  R(V, W) X + R(W, X) V + R(X, V) W = 0.
$$
Proved by extending the three fibre vectors to globally smooth tangent-bundle sections
via `smoothExtensionTangent`, converting each `intrinsicRiemann` term to the
section-level `riemannSec` via `intrinsicRiemann_apply_smooth`, and applying the
section-level Bianchi identity `riemannSec_first_bianchi_levi_civita`. -/
theorem intrinsicRiemann_first_bianchi
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W X : TangentSpace I x) :
    intrinsicRiemann (I := I) g x V W X +
      intrinsicRiemann (I := I) g x W X V +
      intrinsicRiemann (I := I) g x X V W = 0 := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- Smooth extensions of the three fibre vectors.
  set V' := smoothExtensionTangent (I := I) x V with hV'def
  set W' := smoothExtensionTangent (I := I) x W with hW'def
  set X' := smoothExtensionTangent (I := I) x X with hX'def
  have hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V') :=
    smoothExtensionTangent_contMDiff x V
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W') :=
    smoothExtensionTangent_contMDiff x W
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X') :=
    smoothExtensionTangent_contMDiff x X
  have hVx : V' x = V := smoothExtensionTangent_eq x V
  have hWx : W' x = W := smoothExtensionTangent_eq x W
  have hXx : X' x = X := smoothExtensionTangent_eq x X
  -- Pointwise `MDifferentiableAt` at `x` for each smooth section.
  have hV_at : MDiffAt (T% V') x := (hV x).mdifferentiableAt (by simp)
  have hW_at : MDiffAt (T% W') x := (hW x).mdifferentiableAt (by simp)
  have hX_at : MDiffAt (T% X') x := (hX x).mdifferentiableAt (by simp)
  -- Smoothness of intermediate `covApply` sections. `covApply_mdifferentiableAt`
  -- takes the second argument with smoothness `∞ + 1`, which is satisfied by `∞`.
  have hW_top : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% W') := by simpa using hW
  have hV_top : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% V') := by simpa using hV
  have hX_top : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% X') := by simpa using hX
  have hcVW : MDiffAt (T% (covApply (LeviCivita (I := I) g) V' W')) x :=
    covApply_mdifferentiableAt (cov := LeviCivita (I := I) g) hV hW_top
  have hcWV : MDiffAt (T% (covApply (LeviCivita (I := I) g) W' V')) x :=
    covApply_mdifferentiableAt (cov := LeviCivita (I := I) g) hW hV_top
  have hcVX : MDiffAt (T% (covApply (LeviCivita (I := I) g) V' X')) x :=
    covApply_mdifferentiableAt (cov := LeviCivita (I := I) g) hV hX_top
  have hcXV : MDiffAt (T% (covApply (LeviCivita (I := I) g) X' V')) x :=
    covApply_mdifferentiableAt (cov := LeviCivita (I := I) g) hX hV_top
  have hcWX : MDiffAt (T% (covApply (LeviCivita (I := I) g) W' X')) x :=
    covApply_mdifferentiableAt (cov := LeviCivita (I := I) g) hW hX_top
  have hcXW : MDiffAt (T% (covApply (LeviCivita (I := I) g) X' W')) x :=
    covApply_mdifferentiableAt (cov := LeviCivita (I := I) g) hX hW_top
  -- Manifold-Lie-bracket smoothness for the three pairs.
  haveI : IsManifold I 2 M := by
    have h_le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le
  haveI : IsManifold I (minSmoothness ℝ 2 : WithTop ℕ∞) M := by
    have h_eq : (minSmoothness ℝ 2 : WithTop ℕ∞) = (2 : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]
    rw [h_eq]; infer_instance
  haveI : IsManifold I ((1 : ℕ∞) + 1) M := by
    have h_eq : ((1 : ℕ∞) + 1 : WithTop ℕ∞) = (2 : WithTop ℕ∞) := rfl
    rw [h_eq]; infer_instance
  haveI : IsManifold I ((2 : ℕ∞) + 1) M := by
    have h_eq : ((2 : ℕ∞) + 1 : WithTop ℕ∞) = (3 : WithTop ℕ∞) := rfl
    rw [h_eq]
    have h_le3 : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le3
  have h_le_inf2 : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
  have hmlieBr : ∀ {U U' : Π b : M, TangentSpace I b},
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% U) →
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% U') →
      MDiffAt (T% (VectorField.mlieBracket I U U')) x := by
    intro U U' hU hU'
    have hU2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% U) x := (hU x).of_le h_le_inf2
    have hU'2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% U') x := (hU' x).of_le h_le_inf2
    have hmin : minSmoothness ℝ ((1 : ℕ∞) + 1) ≤ (2 : ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]; decide
    exact (hU2.mlieBracket_vectorField (m := 1) (n := 2) hU'2 hmin).mdifferentiableAt
      (by decide)
  have hbrVW : MDiffAt (T% (VectorField.mlieBracket I V' W')) x := hmlieBr hV hW
  have hbrWX : MDiffAt (T% (VectorField.mlieBracket I W' X')) x := hmlieBr hW hX
  have hbrXV : MDiffAt (T% (VectorField.mlieBracket I X' V')) x := hmlieBr hX hV
  -- Eventual smoothness on a neighbourhood of `x`.
  have hVnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% V') b :=
    Filter.Eventually.of_forall (hV.mdifferentiable (by simp))
  have hWnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% W') b :=
    Filter.Eventually.of_forall (hW.mdifferentiable (by simp))
  have hXnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% X') b :=
    Filter.Eventually.of_forall (hX.mdifferentiable (by simp))
  -- Order-`minSmoothness ℝ 2` smoothness for the Jacobi step.
  have h_min2_le : (minSmoothness ℝ 2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_cast
  have hV2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% V') x :=
    (hV x).of_le h_min2_le
  have hW2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% W') x :=
    (hW x).of_le h_min2_le
  have hX2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% X') x :=
    (hX x).of_le h_min2_le
  -- Rewrite each fibre vector as the value of the corresponding smooth extension
  -- at `x` and convert each `intrinsicRiemann` term to its section-level form.
  rw [show V = V' x from hVx.symm, show W = W' x from hWx.symm,
      show X = X' x from hXx.symm,
      intrinsicRiemann_apply_smooth (I := I) g hV hW hX,
      intrinsicRiemann_apply_smooth (I := I) g hW hX hV,
      intrinsicRiemann_apply_smooth (I := I) g hX hV hW]
  -- Apply the section-level first Bianchi identity.
  exact riemannSec_first_bianchi_levi_civita (I := I) g
    hV_at hW_at hX_at hVnhd hWnhd hXnhd
    hcVW hcWV hcVX hcXV hcWX hcXW
    hbrVW hbrWX hbrXV hV2 hW2 hX2

end Curvature
end Riemannian
end Geometry
end DifferentialGeometry

end
