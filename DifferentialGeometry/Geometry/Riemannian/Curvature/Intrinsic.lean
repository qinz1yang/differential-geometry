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

/-- **Antisymmetry on the metric second pair.** As a four-form on
`(T_x M)^4` via the metric, the intrinsic Riemann tensor is antisymmetric
in the slots `(X, Y)`: `g(R(V, W) X, Y) = -g(R(V, W) Y, X)`.

This is `intrinsicRiemann_metric_skew` rewritten as a sign-change. The
two forms are equivalent over a real symmetric inner product: the
"add equals zero" form follows from `g.symm` applied to one term. -/
theorem intrinsicRiemann_metric_swap_second_pair
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W X Y : TangentSpace I x) :
    g.inner x (intrinsicRiemann (I := I) g x V W X) Y =
      -g.inner x (intrinsicRiemann (I := I) g x V W Y) X := by
  have h := intrinsicRiemann_metric_skew (I := I) g x V W X Y
  -- h : g(R(V,W) X, Y) + g(X, R(V,W) Y) = 0
  have hsym : g.inner x X (intrinsicRiemann (I := I) g x V W Y) =
      g.inner x (intrinsicRiemann (I := I) g x V W Y) X :=
    g.symm x X (intrinsicRiemann (I := I) g x V W Y)
  rw [hsym] at h
  linarith

/-- **Pair-swap symmetry of the intrinsic Riemann tensor.** As a four-form on
`(T_x M)^4` via the metric, the intrinsic Riemann tensor is invariant under
exchanging the first pair `(V, W)` with the second pair `(X, Y)`:
$$
  g\bigl(R(V, W) X, Y\bigr) = g\bigl(R(X, Y) V, W\bigr).
$$
This is a purely algebraic consequence of the four previously-established
symmetries: antisymmetry in the first pair (`intrinsicRiemann_swap`),
antisymmetry in the metric second pair
(`intrinsicRiemann_metric_swap_second_pair`), and the first Bianchi
identity (`intrinsicRiemann_first_bianchi`). The classical Spivak / do
Carmo proof applies the Bianchi identity in four cyclic ways and combines
them via the antisymmetries; the linear combination
`(B1) + (B2) - (B3) - (B4)` reduces to `2 · (LHS − RHS) = 0`. -/
theorem intrinsicRiemann_metric_pair_swap
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W X Y : TangentSpace I x) :
    g.inner x (intrinsicRiemann (I := I) g x V W X) Y =
      g.inner x (intrinsicRiemann (I := I) g x X Y V) W := by
  -- Abbreviation `Rm A B C D = g(R(A,B) C, D)`.
  set Rm : TangentSpace I x → TangentSpace I x → TangentSpace I x →
      TangentSpace I x → ℝ :=
    fun A B C D => g.inner x (intrinsicRiemann (I := I) g x A B C) D
    with hRm
  -- Antisymmetry of Rm in the first pair (S1):
  -- Rm A B C D = -Rm B A C D, from intrinsicRiemann_swap.
  have h_swap1 : ∀ A B C D : TangentSpace I x, Rm A B C D = -Rm B A C D := by
    intro A B C D
    simp only [hRm]
    rw [intrinsicRiemann_swap (I := I) g x A B C]
    simp [ContinuousLinearMap.neg_apply]
  -- Antisymmetry of Rm in the second pair (S2):
  -- Rm A B C D = -Rm A B D C, from intrinsicRiemann_metric_swap_second_pair.
  have h_swap2 : ∀ A B C D : TangentSpace I x, Rm A B C D = -Rm A B D C := by
    intro A B C D
    simp only [hRm]
    exact intrinsicRiemann_metric_swap_second_pair (I := I) g x A B C D
  -- Linearised Bianchi identity:
  -- Rm A B C D + Rm B C A D + Rm C A B D = 0,
  -- obtained by inner-producting the first Bianchi identity with D.
  have h_bianchi : ∀ A B C D : TangentSpace I x,
      Rm A B C D + Rm B C A D + Rm C A B D = 0 := by
    intro A B C D
    have hB := intrinsicRiemann_first_bianchi (I := I) g x A B C
    -- hB : R(A,B) C + R(B,C) A + R(C,A) B = 0.
    have hev :
        g.inner x (intrinsicRiemann (I := I) g x A B C +
          intrinsicRiemann (I := I) g x B C A +
          intrinsicRiemann (I := I) g x C A B) D =
        g.inner x (0 : TangentSpace I x) D := by rw [hB]
    -- Distribute g.inner x · D over the sum.
    have hzero : g.inner x (0 : TangentSpace I x) D = 0 := by
      simp
    have hadd1 : g.inner x (intrinsicRiemann (I := I) g x A B C +
        intrinsicRiemann (I := I) g x B C A +
        intrinsicRiemann (I := I) g x C A B) D =
        g.inner x (intrinsicRiemann (I := I) g x A B C +
          intrinsicRiemann (I := I) g x B C A) D +
          g.inner x (intrinsicRiemann (I := I) g x C A B) D := by
      have := (g.inner x).map_add
        (intrinsicRiemann (I := I) g x A B C +
          intrinsicRiemann (I := I) g x B C A)
        (intrinsicRiemann (I := I) g x C A B)
      exact congrArg (fun f : TangentSpace I x →L[ℝ] ℝ => f D) this
    have hadd2 : g.inner x (intrinsicRiemann (I := I) g x A B C +
        intrinsicRiemann (I := I) g x B C A) D =
        g.inner x (intrinsicRiemann (I := I) g x A B C) D +
          g.inner x (intrinsicRiemann (I := I) g x B C A) D := by
      have := (g.inner x).map_add
        (intrinsicRiemann (I := I) g x A B C)
        (intrinsicRiemann (I := I) g x B C A)
      exact congrArg (fun f : TangentSpace I x →L[ℝ] ℝ => f D) this
    rw [hadd1, hadd2, hzero] at hev
    -- Now hev expresses the sum of three Rm-terms equals 0.
    simp only [hRm]
    linarith
  -- The four Bianchi instances we need:
  have hB1 : Rm V W X Y + Rm W X V Y + Rm X V W Y = 0 := h_bianchi V W X Y
  have hB2 : Rm W X Y V + Rm X Y W V + Rm Y W X V = 0 := h_bianchi W X Y V
  have hB3 : Rm X Y V W + Rm Y V X W + Rm V X Y W = 0 := h_bianchi X Y V W
  have hB4 : Rm Y V W X + Rm V W Y X + Rm W Y V X = 0 := h_bianchi Y V W X
  -- Convert each "off-diagonal" cross-term to a canonical form via S2.
  -- B1 rewrite: Rm W X V Y = -Rm W X Y V.
  have h12 : Rm W X V Y = -Rm W X Y V := h_swap2 W X V Y
  -- B2 rewrite: Rm X Y W V = -Rm X Y V W.
  have h22 : Rm X Y W V = -Rm X Y V W := h_swap2 X Y W V
  -- B3 rewrite: Rm Y V X W = -Rm Y V W X.
  have h32 : Rm Y V X W = -Rm Y V W X := h_swap2 Y V X W
  -- B4 rewrite: Rm V W Y X = -Rm V W X Y.
  have h42 : Rm V W Y X = -Rm V W X Y := h_swap2 V W Y X
  -- Reduce the four "extra" cross-terms via S1 + S2 to a canonical form.
  -- Claim: Rm X V W Y = Rm V X Y W.
  --   By S1: Rm X V W Y = -Rm V X W Y.
  --   By S2: Rm V X W Y = -Rm V X Y W.
  -- Hence Rm X V W Y = -(-Rm V X Y W) = Rm V X Y W.
  have hXVWY_eq : Rm X V W Y = Rm V X Y W := by
    have s1 : Rm X V W Y = -Rm V X W Y := h_swap1 X V W Y
    have s2 : Rm V X W Y = -Rm V X Y W := h_swap2 V X W Y
    rw [s1, s2]; ring
  -- Claim: Rm Y W X V = Rm W Y V X.
  --   By S1: Rm Y W X V = -Rm W Y X V.
  --   By S2: Rm W Y X V = -Rm W Y V X.
  -- Hence Rm Y W X V = Rm W Y V X.
  have hYWXV_eq : Rm Y W X V = Rm W Y V X := by
    have s1 : Rm Y W X V = -Rm W Y X V := h_swap1 Y W X V
    have s2 : Rm W Y X V = -Rm W Y V X := h_swap2 W Y X V
    rw [s1, s2]; ring
  -- B1 + B2 - B3 - B4 = 0; substitute h12, h22, h32, h42 and the two
  -- equalities `hXVWY_eq`, `hYWXV_eq` to reduce to
  -- `2 · Rm V W X Y - 2 · Rm X Y V W = 0`, then divide by 2.
  -- The substitution flow is:
  --   B1 ⇒ Rm V W X Y + (-Rm W X Y V) + Rm X V W Y = 0.
  --   B2 ⇒ Rm W X Y V + (-Rm X Y V W) + Rm Y W X V = 0.
  --   B3 ⇒ Rm X Y V W + (-Rm Y V W X) + Rm V X Y W = 0.
  --   B4 ⇒ Rm Y V W X + (-Rm V W X Y) + Rm W Y V X = 0.
  -- (B1) + (B2) - (B3) - (B4):
  --   +Rm V W X Y -Rm W X Y V +Rm X V W Y
  --   +Rm W X Y V -Rm X Y V W +Rm Y W X V
  --   -Rm X Y V W +Rm Y V W X -Rm V X Y W
  --   -Rm Y V W X +Rm V W X Y -Rm W Y V X
  -- The ±Rm W X Y V and ±Rm Y V W X pairs cancel.
  -- Using hXVWY_eq, the Rm X V W Y - Rm V X Y W pair vanishes.
  -- Using hYWXV_eq, the Rm Y W X V - Rm W Y V X pair vanishes.
  -- Survivors: 2 · Rm V W X Y - 2 · Rm X Y V W = 0.
  have hkey : 2 * Rm V W X Y - 2 * Rm X Y V W = 0 := by
    -- Rewrite hB1..hB4 using the second-pair S2 facts.
    rw [h12] at hB1
    rw [h22] at hB2
    rw [h32] at hB3
    rw [h42] at hB4
    -- Now hB1, hB2, hB3, hB4 each contain the canonical "Rm V W X Y" or
    -- "Rm X Y V W" term plus exactly two cross terms each.
    linarith [hXVWY_eq, hYWXV_eq, hB1, hB2, hB3, hB4]
  -- Cancel the factor of 2.
  have : Rm V W X Y - Rm X Y V W = 0 := by linarith
  -- Rewrite back to the original goal.
  change Rm V W X Y = Rm X Y V W
  linarith

end Curvature
end Riemannian
end Geometry
end DifferentialGeometry

end
