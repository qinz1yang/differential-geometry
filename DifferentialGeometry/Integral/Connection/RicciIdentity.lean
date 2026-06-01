import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.Integral.Connection.ChartBridge.Gradient
import DifferentialGeometry.Geometry.Laplacian

/-!
# Ricci identities for vectors and 1-forms; trace-commutator identity for the gradient

This file develops the three classical **Ricci identities** for the Levi-Civita covariant
derivative of a smooth Riemannian metric `g : SmoothRiemannianMetric I M`:

## Vector Ricci identity

For any covariant derivative `cov` on the tangent bundle, smooth tangent fields `X`, `Y`,
`V`, and a point `x : M`, the section-level Riemann formula
$$
  R(X, Y) V := \nabla_X (\nabla_Y V) - \nabla_Y (\nabla_X V) - \nabla_{[X, Y]} V
$$
is built into the definition of `riemannSec`. We expose this as the
**vector Ricci identity** `ricci_identity_vector`, providing a usable callsite for the
direct unfolding.

## 1-form Ricci identity

For the cotangent extension of any covariant derivative `cov` (denoted `cotangentCov cov`),
smooth tangent fields `X`, `Y`, `W`, and a smooth cotangent section `θ`, the iterated
commutator on `θ` evaluated against `W x` equals minus the contraction of `θ` against the
section-level Riemann curvature on `W`:
$$
  \bigl[(\nabla^*_X \nabla^*_Y \theta) - (\nabla^*_Y \nabla^*_X \theta)
        - (\nabla^*_{[X, Y]}\,\theta)\bigr](W(x))
    = -\,\theta\bigl(R(X, Y) W\bigr)(x).
$$
Here `(∇^*_Y θ)` is interpreted as the cotangent section
`b ↦ (cotangentCov cov).toFun θ b (Y b)`, and `(∇^*_X (∇^*_Y θ))` is the cotangent
covariant derivative of that section along `X`. The proof uses the dual-pairing Leibniz
identity `cotangentCov_dualPairing` iteratively, combined with the foundational identity
`extDerivFun_apply_mlieBracket` for the second derivative of a scalar along a Lie
bracket.

## Trace-commutator identity for the gradient

The **trace-commutator** (also known as the heart-of-Bochner reduction) packages the
abstract Ricci tensor at `(∇f, w)` as the basis-coefficient sum of the section-level
Riemann curvature on a smooth global tangent frame:
$$
  \mathrm{Ric}_x\bigl(\nabla f,\, w\bigr) =
    \sum_i (\mathrm{finBasis}\,\mathbb R\,E).\mathrm{repr}\bigl(R(B_i, w)(\nabla f)(x)\bigr)_i.
$$

A fully bundled connection Laplacian on tangent vectors is constructed in a downstream
file. Here we provide:

* `localConnLap_vector cov B V x` — the **local connection Laplacian** of a tangent
  section `V` at the point `x`, computed against a smooth tangent frame `B : Fin n → Π b,
  TangentSpace I b`. The definition matches the textbook trace formula
  `Δ_∇ V = ∑_i (∇_{B_i} ∇_{B_i} V - ∇_{∇_{B_i} B_i} V)`.

* `ricciTensor_gradFun_eq_frame_sum_riemannSec` — the **trace identity** at the heart of Bochner.
  It is the trace formulation of the vector Ricci identity (item 1) plus the basis
  expansion of the abstract Ricci tensor.
-/

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- **Vector Ricci identity.** For any covariant derivative `cov` on the tangent bundle,
smooth tangent vector fields `X`, `Y`, `V`, and a point `x : M`, the iterated covariant
derivative commutator equals the section-level Riemann curvature:
$$
  \nabla_X(\nabla_Y V)\,(x) - \nabla_Y(\nabla_X V)\,(x) - \nabla_{[X, Y]} V\,(x)
    = R(X, Y) V\,(x).
$$
With Mathlib's argument convention `cov.toFun σ x v ≅ (∇_v σ)(x)`, this is the equality
$$
  \mathrm{cov.toFun}(\nabla_Y V)(x)(X(x))
    - \mathrm{cov.toFun}(\nabla_X V)(x)(Y(x))
    - \mathrm{cov.toFun}(V)(x)([X, Y]_x)
    = \mathrm{riemannSec}\,\mathrm{cov}\,X\,Y\,V\,x.
$$
The identity is purely definitional (`riemannSec_def`). -/
theorem ricci_identity_vector
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y V : Π b : M, TangentSpace I b) (x : M) :
    cov.toFun (covApply cov Y V) x (X x) - cov.toFun (covApply cov X V) x (Y x)
        - cov.toFun V x (VectorField.mlieBracket I X Y x) =
      riemannSec cov X Y V x :=
  (riemannSec_def cov X Y V x).symm

/-- The **iterated cotangent connection** of a cotangent section `θ` along smooth
tangent fields `X` and `Y`, evaluated at `(x, W(x))`. Concretely:
$$
  (\nabla^*_X \nabla^*_Y \theta)\,x\,(W(x))
    := \bigl((\mathrm{cotangentCov}\,\mathrm{cov})
          (\,b \mapsto (\mathrm{cotangentCov}\,\mathrm{cov})(\theta)\,b\,(Y(b)))\,
          x\,(X(x))\bigr)\,(W(x)).
$$
The intermediate cotangent section `b ↦ (cotangentCov θ) b (Y b)` is the cotangent
covariant derivative of `θ` along the smooth vector field `Y`. -/
private noncomputable def iterCotangentCov
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (θ : Π b : M, TangentSpace I b →L[ℝ] ℝ)
    (X Y W : Π b : M, TangentSpace I b) (x : M) : ℝ :=
  ((cotangentCov cov).toFun
    (fun b : M => (cotangentCov cov).toFun θ b (Y b)) x (X x)) (W x)

/-- **1-form Ricci identity.** Let `cov : CovariantDerivative I E (TangentSpace I)` be a
covariant derivative of class `C^∞` on the tangent bundle of a smooth manifold `M`. For
smooth tangent vector fields `X, Y, W`, a smooth cotangent section `θ`, and a point
`x : M`, the iterated cotangent commutator on `θ` applied to `W x` equals minus the
contraction of `θ` against the section-level Riemann curvature on `W`:
$$
  \bigl[(\nabla^*_X \nabla^*_Y \theta)\,(W) - (\nabla^*_Y \nabla^*_X \theta)\,(W)
        - (\nabla^*_{[X, Y]}\,\theta)(W)\bigr](x)
    = -\,\theta(x)\bigl(R(X, Y) W\,(x)\bigr).
$$
The required smoothness on `f := b ↦ θ(b)(W(b))` enables the foundational scalar-bracket
identity `extDerivFun_apply_mlieBracket`. -/
theorem ricci_identity_oneForm
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y W : Π b : M, TangentSpace I b}
    {θ : Π b : M, TangentSpace I b →L[ℝ] ℝ}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hθ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (θ b)))
    (x : M) :
    iterCotangentCov cov θ X Y W x - iterCotangentCov cov θ Y X W x -
        ((cotangentCov cov).toFun θ x (VectorField.mlieBracket I X Y x)) (W x) =
      - θ x (riemannSec cov X Y W x) := by
  classical
  have hX_at : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hW_at : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  have hθ_at : MDiffAtCotangent θ x := (hθ x).mdifferentiableAt (by simp)
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => θ b (W b)) :=
    cotangentCov_pairing_contMDiff hθ hW
  have hf_2 : ContMDiffAt I 𝓘(ℝ) 2 (fun b : M => θ b (W b)) x := by
    have hle : (2 : WithTop ℕ∞) ≤ ∞ := by
      have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
      simpa using h1
    exact (hf_smooth x).of_le hle
  have hx_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    (I.isInteriorPoint_iff (x := x)).mp BoundarylessManifold.isInteriorPoint
  have hcYW_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov Y W)) := by
    intro b
    exact (covApply_contMDiffOn (cov := cov) hY (by simpa using hW)).contMDiffAt
      (Filter.univ_mem)
  have hcXW_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X W)) := by
    intro b
    exact (covApply_contMDiffOn (cov := cov) hX (by simpa using hW)).contMDiffAt
      (Filter.univ_mem)
  have hcYW_at : MDiffAt (T% (covApply cov Y W)) x :=
    (hcYW_smooth x).mdifferentiableAt (by simp)
  have hcXW_at : MDiffAt (T% (covApply cov X W)) x :=
    (hcXW_smooth x).mdifferentiableAt (by simp)
  have hpair_Y_glob :
      (fun b : M => extDerivFun (I := I) (fun b' : M => θ b' (W b')) b (Y b)) =
      (fun b : M => ((cotangentCov cov).toFun θ b (Y b)) (W b) +
        θ b (cov.toFun W b (Y b))) := by
    funext b
    have hθ_b : MDiffAtCotangent θ b := (hθ b).mdifferentiableAt (by simp)
    have hW_b : MDiffAt (T% W) b := (hW b).mdifferentiableAt (by simp)
    exact cotangentCov_dualPairing cov hθ_b hW_b (Y b)
  have hpair_X_glob :
      (fun b : M => extDerivFun (I := I) (fun b' : M => θ b' (W b')) b (X b)) =
      (fun b : M => ((cotangentCov cov).toFun θ b (X b)) (W b) +
        θ b (cov.toFun W b (X b))) := by
    funext b
    have hθ_b : MDiffAtCotangent θ b := (hθ b).mdifferentiableAt (by simp)
    have hW_b : MDiffAt (T% W) b := (hW b).mdifferentiableAt (by simp)
    exact cotangentCov_dualPairing cov hθ_b hW_b (X b)
  haveI : IsManifold I 2 M := by
    have h_le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le
  haveI : CompleteSpace E := inferInstance
  have hfound :
      extDerivFun (I := I) (fun b : M => θ b (W b)) x
        (VectorField.mlieBracket I X Y x) =
      extDerivFun (I := I)
        (fun b : M => extDerivFun (I := I) (fun b' : M => θ b' (W b')) b (Y b)) x (X x) -
      extDerivFun (I := I)
        (fun b : M => extDerivFun (I := I) (fun b' : M => θ b' (W b')) b (X b)) x (Y x) :=
    extDerivFun_apply_mlieBracket hX_at hY_at hf_2 hx_int
  rw [hpair_Y_glob, hpair_X_glob] at hfound
  have hpair_br : extDerivFun (I := I) (fun b : M => θ b (W b)) x
        (VectorField.mlieBracket I X Y x) =
      ((cotangentCov cov).toFun θ x (VectorField.mlieBracket I X Y x)) (W x) +
        θ x (cov.toFun W x (VectorField.mlieBracket I X Y x)) :=
    cotangentCov_dualPairing cov hθ_at hW_at (VectorField.mlieBracket I X Y x)
  rw [hpair_br] at hfound
  have hsum1_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M => ((cotangentCov cov).toFun θ b (Y b)) (W b)) x := by
    have h_smooth :=
      cotangentCov_double_apply_smooth cov hθ
        ⟨fun b : M => Y b, hY⟩ ⟨fun b : M => W b, hW⟩
    exact (h_smooth x).mdifferentiableAt (by simp)
  have hsum2_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M => θ b (cov.toFun W b (Y b))) x := by
    have h_eq_fn : (fun b : M => θ b (cov.toFun W b (Y b))) =
        (fun b : M => θ b (covApply cov Y W b)) := by funext b; rfl
    rw [h_eq_fn]
    have hsmooth := cotangentCov_pairing_contMDiff hθ hcYW_smooth
    exact (hsmooth x).mdifferentiableAt (by simp)
  have hsum3_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M => ((cotangentCov cov).toFun θ b (X b)) (W b)) x := by
    have h_smooth :=
      cotangentCov_double_apply_smooth cov hθ
        ⟨fun b : M => X b, hX⟩ ⟨fun b : M => W b, hW⟩
    exact (h_smooth x).mdifferentiableAt (by simp)
  have hsum4_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M => θ b (cov.toFun W b (X b))) x := by
    have h_eq_fn : (fun b : M => θ b (cov.toFun W b (X b))) =
        (fun b : M => θ b (covApply cov X W b)) := by funext b; rfl
    rw [h_eq_fn]
    have hsmooth := cotangentCov_pairing_contMDiff hθ hcXW_smooth
    exact (hsmooth x).mdifferentiableAt (by simp)
  have hadd_X : extDerivFun (I := I)
        (fun b : M => ((cotangentCov cov).toFun θ b (Y b)) (W b) +
          θ b (cov.toFun W b (Y b))) x =
      extDerivFun (I := I)
          (fun b : M => ((cotangentCov cov).toFun θ b (Y b)) (W b)) x +
        extDerivFun (I := I) (fun b : M => θ b (cov.toFun W b (Y b))) x :=
    extDerivFun_add hsum1_diff hsum2_diff
  have hadd_Y : extDerivFun (I := I)
        (fun b : M => ((cotangentCov cov).toFun θ b (X b)) (W b) +
          θ b (cov.toFun W b (X b))) x =
      extDerivFun (I := I)
          (fun b : M => ((cotangentCov cov).toFun θ b (X b)) (W b)) x +
        extDerivFun (I := I) (fun b : M => θ b (cov.toFun W b (X b))) x :=
    extDerivFun_add hsum3_diff hsum4_diff
  have hadd_X_app : extDerivFun (I := I)
        (fun b : M => ((cotangentCov cov).toFun θ b (Y b)) (W b) +
          θ b (cov.toFun W b (Y b))) x (X x) =
      extDerivFun (I := I)
          (fun b : M => ((cotangentCov cov).toFun θ b (Y b)) (W b)) x (X x) +
        extDerivFun (I := I) (fun b : M => θ b (cov.toFun W b (Y b))) x (X x) := by
    rw [hadd_X]; rfl
  have hadd_Y_app : extDerivFun (I := I)
        (fun b : M => ((cotangentCov cov).toFun θ b (X b)) (W b) +
          θ b (cov.toFun W b (X b))) x (Y x) =
      extDerivFun (I := I)
          (fun b : M => ((cotangentCov cov).toFun θ b (X b)) (W b)) x (Y x) +
        extDerivFun (I := I) (fun b : M => θ b (cov.toFun W b (X b))) x (Y x) := by
    rw [hadd_Y]; rfl
  rw [hadd_X_app, hadd_Y_app] at hfound
  have hθY_at : MDiffAtCotangent
      (fun b : M => (cotangentCov cov).toFun θ b (Y b)) x := by
    have h_section :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)))
          (fun b : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
            (E := fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) b
            ((cotangentCov cov).toFun θ b)) x := by
      have hres :=
        (cotangentCov_isContMDiff (cov := cov)).contMDiff.contMDiff
          (σ := θ) (hθ.of_le (by rw [ENat.coe_top_add_one])).contMDiffOn
      exact (hres x (Set.mem_univ x)).contMDiffAt (Filter.univ_mem) |>.mdifferentiableAt
        (by simp)
    exact h_section.clm_bundle_apply (v := Y) hY_at
  have hθX_at : MDiffAtCotangent
      (fun b : M => (cotangentCov cov).toFun θ b (X b)) x := by
    have h_section :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)))
          (fun b : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
            (E := fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) b
            ((cotangentCov cov).toFun θ b)) x := by
      have hres :=
        (cotangentCov_isContMDiff (cov := cov)).contMDiff.contMDiff
          (σ := θ) (hθ.of_le (by rw [ENat.coe_top_add_one])).contMDiffOn
      exact (hres x (Set.mem_univ x)).contMDiffAt (Filter.univ_mem) |>.mdifferentiableAt
        (by simp)
    exact h_section.clm_bundle_apply (v := X) hX_at
  have h_iter_X : extDerivFun (I := I)
        (fun b : M => ((cotangentCov cov).toFun θ b (Y b)) (W b)) x (X x) =
      ((cotangentCov cov).toFun
          (fun b : M => (cotangentCov cov).toFun θ b (Y b)) x (X x)) (W x) +
        ((cotangentCov cov).toFun θ x (Y x)) (cov.toFun W x (X x)) :=
    cotangentCov_dualPairing cov hθY_at hW_at (X x)
  have h_iter_Y : extDerivFun (I := I)
        (fun b : M => ((cotangentCov cov).toFun θ b (X b)) (W b)) x (Y x) =
      ((cotangentCov cov).toFun
          (fun b : M => (cotangentCov cov).toFun θ b (X b)) x (Y x)) (W x) +
        ((cotangentCov cov).toFun θ x (X x)) (cov.toFun W x (Y x)) :=
    cotangentCov_dualPairing cov hθX_at hW_at (Y x)
  rw [h_iter_X, h_iter_Y] at hfound
  have hB_eq : extDerivFun (I := I)
      (fun b : M => θ b (cov.toFun W b (Y b))) x (X x) =
      ((cotangentCov cov).toFun θ) x (X x) (covApply cov Y W x) +
        θ x (cov.toFun (covApply cov Y W) x (X x)) := by
    have hpair := cotangentCov_dualPairing cov hθ_at hcYW_at (X x)
    have h_eq_fn : (fun b : M => θ b (cov.toFun W b (Y b))) =
        (fun b : M => θ b (covApply cov Y W b)) := by funext b; rfl
    rw [h_eq_fn]; exact hpair
  have hB'_eq : extDerivFun (I := I)
      (fun b : M => θ b (cov.toFun W b (X b))) x (Y x) =
      ((cotangentCov cov).toFun θ) x (Y x) (covApply cov X W x) +
        θ x (cov.toFun (covApply cov X W) x (Y x)) := by
    have hpair := cotangentCov_dualPairing cov hθ_at hcXW_at (Y x)
    have h_eq_fn : (fun b : M => θ b (cov.toFun W b (X b))) =
        (fun b : M => θ b (covApply cov X W b)) := by funext b; rfl
    rw [h_eq_fn]; exact hpair
  rw [hB_eq, hB'_eq] at hfound
  rw [show riemannSec cov X Y W x =
      cov.toFun (covApply cov Y W) x (X x) - cov.toFun (covApply cov X W) x (Y x)
        - cov.toFun W x (VectorField.mlieBracket I X Y x) from rfl]
  have hθ_lin :
      θ x (cov.toFun (covApply cov Y W) x (X x) -
        cov.toFun (covApply cov X W) x (Y x) -
        cov.toFun W x (VectorField.mlieBracket I X Y x)) =
      θ x (cov.toFun (covApply cov Y W) x (X x))
        - θ x (cov.toFun (covApply cov X W) x (Y x))
        - θ x (cov.toFun W x (VectorField.mlieBracket I X Y x)) := by
    rw [show (cov.toFun (covApply cov Y W) x (X x) -
            cov.toFun (covApply cov X W) x (Y x) -
            cov.toFun W x (VectorField.mlieBracket I X Y x)) =
        (cov.toFun (covApply cov Y W) x (X x) -
            cov.toFun (covApply cov X W) x (Y x)) -
          cov.toFun W x (VectorField.mlieBracket I X Y x) from rfl,
        map_sub, map_sub]
  rw [hθ_lin]
  have h_covYW : covApply cov Y W x = cov.toFun W x (Y x) := rfl
  have h_covXW : covApply cov X W x = cov.toFun W x (X x) := rfl
  rw [h_covYW, h_covXW] at hfound
  unfold iterCotangentCov
  linarith

/-- The **local connection Laplacian on tangent sections** with respect to a smooth
global tangent frame `B : Fin n → Π b, TangentSpace I b`. With the standing argument
convention `cov.toFun σ x v ≅ (∇_v σ)(x)`, this is the textbook formula
$$
  (\Delta_\nabla^{B} V)(x)
    := \sum_i \bigl(\nabla_{B_i x}\nabla_{B_i} V - \nabla_{(\nabla_{B_i} B_i)(x)} V\bigr).
$$
The dependence on `B` is genuine in the absence of an orthonormality hypothesis. The
downstream connection-Laplacian instance proves frame-invariance under `g`-orthonormal
frames; here we expose the frame-dependent operator at the level needed by the
trace-commutator identity. -/
noncomputable def localConnLap_vector
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (V : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    (cov.toFun (covApply cov (B i) V) x (B i x) -
      cov.toFun V x (cov.toFun (B i) x (B i x)))

/-- The defining identity for `localConnLap_vector`. -/
lemma localConnLap_vector_def
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (V : Π b : M, TangentSpace I b) (x : M) :
    localConnLap_vector cov B V x =
      ∑ i : Fin (Module.finrank ℝ E),
        (cov.toFun (covApply cov (B i) V) x (B i x) -
          cov.toFun V x (cov.toFun (B i) x (B i x))) := rfl

/-- **Frame-trace expansion of the Ricci tensor at the gradient.** Let `g` be a smooth
Riemannian metric on `M`, let `f : M → ℝ` be a smooth scalar, let `w` be a smooth tangent
vector field, and let `B : Fin n → Π b, TangentSpace I b` be a smooth global tangent frame
agreeing with the model basis `chartModelBasis E` at the point `x`. Then the Ricci tensor
at `(∇f, w)` equals the `chartModelBasis E`-coordinate sum of the section-level Riemann
curvature `riemannSec (LeviCivita g)` on the frame:
$$
  \mathrm{Ric}_x\bigl(\nabla f,\, w\bigr) =
    \sum_i (\mathrm{chartModelBasis}\,E).\mathrm{repr}
      \bigl(R(B_i, w)(\nabla f)(x)\bigr)_i.
$$
Here `∇f` is `gradFun g f` and `R = riemannSec (LeviCivita g)`.

The proof is the basis-trace expansion `ricciTensor_apply_smooth_basisSum`
(with `Y := w`, `Z := ∇f`) composed with `ricciTensor_symm` to put the gradient in the
first slot. This frame-trace identity is the algebraic ingredient consumed downstream when
assembling the connection-Laplacian/gradient commutator
`Δ_∇(∇f) = ∇(Δ_g f) + Ric^♯(∇f)`; that commutator itself is NOT proved here. -/
theorem ricciTensor_gradFun_eq_frame_sum_riemannSec [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {w : Π b : M, TangentSpace I b}
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (x : M) (hBx : ∀ i, B i x = (chartModelBasis E) i) :
    ricciTensor (I := I) g x (gradFun (I := I) g f x) (w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (riemannSec (LeviCivita (I := I) g) (B i) w
            (fun y => gradFun (I := I) g f y) x) i := by
  classical
  have h_grad_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
        (gradFun (I := I) g f y)) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hbasisSum := ricciTensor_apply_smooth_basisSum (I := I) g
    (Y := w) (Z := fun y => gradFun (I := I) g f y)
    (B := B) hw h_grad_smooth hB x hBx
  rw [ricciTensor_symm (I := I) g x (gradFun (I := I) g f x) (w x)]
  exact hbasisSum

/-- The (1,1)-Ricci endomorphism `ricciSharp g x v` of a tangent vector `v ∈ T_x M`. By the
defining identity (see `inner_ricciSharp`), it is the unique vector `W ∈ T_x M` such that
`g_x(W, w) = ricciTensor g x v w` for every `w ∈ T_x M`. -/
noncomputable def ricciSharpVec
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  metricSharp (I := I) g x ((ricciTensor (I := I) g x v).toLinearMap)

/-- **Defining identity for `ricciSharpVec`.** For any `v, w ∈ T_x M`,
`g_x(\mathrm{Ric}^\sharp(v), w) = \mathrm{Ric}_x(v, w)`. -/
lemma inner_ricciSharpVec
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.inner x (ricciSharpVec (I := I) g x v) w = ricciTensor (I := I) g x v w := by
  unfold ricciSharpVec
  exact inner_metricSharp (I := I) g x ((ricciTensor (I := I) g x v).toLinearMap) w

/-- Symmetric form of the defining identity. -/
lemma inner_ricciSharpVec_right
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.inner x w (ricciSharpVec (I := I) g x v) = ricciTensor (I := I) g x v w := by
  rw [g.symm x w (ricciSharpVec (I := I) g x v)]
  exact inner_ricciSharpVec (I := I) g x v w

/-- The vector `ricciSharpVec g x v` is **uniquely** characterised by its defining
inner-product identity: any `W ∈ T_x M` with `g.inner x W w = ricciTensor g x v w` for all
`w` is equal to `ricciSharpVec g x v`. -/
lemma ricciSharpVec_unique
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x)
    {W : TangentSpace I x}
    (hW : ∀ w : TangentSpace I x,
      g.inner x W w = ricciTensor (I := I) g x v w) :
    W = ricciSharpVec (I := I) g x v := by
  apply metricFlatLinear_injective (I := I) g x
  ext w
  rw [metricFlatLinear_apply, metricFlatLinear_apply]
  rw [hW w]
  exact (inner_ricciSharpVec (I := I) g x v w).symm

/-- Additivity of `ricciSharpVec` in the input vector. -/
lemma ricciSharpVec_add
    (g : SmoothRiemannianMetric I M) (x : M) (v v' : TangentSpace I x) :
    ricciSharpVec (I := I) g x (v + v') =
      ricciSharpVec (I := I) g x v + ricciSharpVec (I := I) g x v' := by
  refine (ricciSharpVec_unique (I := I) g x (v + v')
    (W := ricciSharpVec (I := I) g x v + ricciSharpVec (I := I) g x v') ?_).symm
  intro w
  rw [show g.inner x (ricciSharpVec (I := I) g x v + ricciSharpVec (I := I) g x v') w =
        g.inner x (ricciSharpVec (I := I) g x v) w +
          g.inner x (ricciSharpVec (I := I) g x v') w from
      by rw [map_add, ContinuousLinearMap.add_apply]]
  rw [inner_ricciSharpVec (I := I) g x v w,
      inner_ricciSharpVec (I := I) g x v' w]
  rw [show ricciTensor (I := I) g x (v + v') w =
        ricciTensor (I := I) g x v w + ricciTensor (I := I) g x v' w from by
      rw [map_add, ContinuousLinearMap.add_apply]]

/-- Real-scalar homogeneity of `ricciSharpVec` in the input vector. -/
lemma ricciSharpVec_smul
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ) (v : TangentSpace I x) :
    ricciSharpVec (I := I) g x (c • v) = c • ricciSharpVec (I := I) g x v := by
  refine (ricciSharpVec_unique (I := I) g x (c • v)
    (W := c • ricciSharpVec (I := I) g x v) ?_).symm
  intro w
  rw [show g.inner x (c • ricciSharpVec (I := I) g x v) w =
        c * g.inner x (ricciSharpVec (I := I) g x v) w from
      by rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]]
  rw [inner_ricciSharpVec (I := I) g x v w]
  rw [show ricciTensor (I := I) g x (c • v) w =
        c * ricciTensor (I := I) g x v w from by
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]]

/-- The (1,1)-Ricci endomorphism `ricciSharp g x : T_x M →L[ℝ] T_x M`, packaged as a
continuous linear map. The definition uses the underlying linear-algebraic map
`v ↦ ricciSharpVec g x v` (linear by `ricciSharpVec_add` / `ricciSharpVec_smul`),
upgraded to a continuous map via finite-dimensional automatic continuity. -/
noncomputable def ricciSharp
    (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ricciSharpVec (I := I) g x v
      map_add' := fun v v' => ricciSharpVec_add (I := I) g x v v'
      map_smul' := fun c v => by
        simpa using ricciSharpVec_smul (I := I) g x c v }

/-- Defining identity for `ricciSharp` as a continuous linear endomorphism: it agrees with
`ricciSharpVec` pointwise. -/
@[simp] lemma ricciSharp_apply
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    ricciSharp (I := I) g x v = ricciSharpVec (I := I) g x v := rfl

/-- **Inner-product defining identity for `ricciSharp`.** For any `v, w ∈ T_x M`,
`g_x(\mathrm{Ric}^\sharp(v), w) = \mathrm{Ric}_x(v, w)`. -/
theorem inner_ricciSharp
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.inner x (ricciSharp (I := I) g x v) w = ricciTensor (I := I) g x v w := by
  rw [ricciSharp_apply]
  exact inner_ricciSharpVec (I := I) g x v w

/-- Symmetric form: `g_x(w, \mathrm{Ric}^\sharp(v)) = \mathrm{Ric}_x(v, w)`. -/
theorem inner_ricciSharp_right
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.inner x w (ricciSharp (I := I) g x v) = ricciTensor (I := I) g x v w := by
  rw [ricciSharp_apply]
  exact inner_ricciSharpVec_right (I := I) g x v w

/-- **Bridge between `g(∇_X (∇f), Y)` and the abstract Hessian.** For the Levi-Civita
covariant derivative, the inner product `g(∇_X (∇f), Y)` agrees with the abstract Hessian
`abstractHessian g f x (X x) (Y x)`. This identity links the local (Hessian) and global
(covariant-derivative-of-gradient) descriptions of the second-order behaviour of `f`,
through the metric duality `g(grad f, ·) = mfderiv f`. -/
theorem inner_cov_gradFun_eq_abstractHessian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (_hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (X x)) (Y x) =
      abstractHessian (I := I) g f x (X x) (Y x) := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  set θ : Π b : M, TangentSpace I b →L[ℝ] ℝ := extDerivFun (I := I) f with hθ_def
  have h_grad_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
        (gradFun (I := I) g f y)) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have h_grad_at : MDiffAt (T% (fun b => gradFun (I := I) g f b)) x :=
    (h_grad_smooth x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hθ_at : MDiffAtCotangent θ x := by
    have hext_smooth :=
      cotangentCov_extDerivFun_smooth (I := I) hf
    exact (hext_smooth x).mdifferentiableAt (by simp)
  have hpair := cotangentCov_dualPairing cov hθ_at h_grad_at (X x)
  have hpair' := cotangentCov_dualPairing cov hθ_at hY_at (X x)
  have h_eq_fn : (fun b : M => extDerivFun (I := I) f b (Y b)) =
      (fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) := by
    funext b
    exact (gradFun_metricDual_extDerivFun (I := I) g f b (Y b)).symm
  have hmc := (LeviCivita_isMetricCompatible (I := I) g).apply h_grad_at hY_at (X x)
  have hmc' : extDerivFun (I := I) (fun b => g.inner b (gradFun (I := I) g f b) (Y b)) x (X x) =
      g.inner x (cov.toFun (fun b => gradFun (I := I) g f b) x (X x)) (Y x) +
        g.inner x (gradFun (I := I) g f x) (cov.toFun Y x (X x)) := by
    have hext_eq : extDerivFun (I := I) (fun b => g.inner b (gradFun (I := I) g f b) (Y b)) x (X x) =
        (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) x) (X x) := rfl
    rw [hext_eq, hmc]
  have h_lhs_eq : extDerivFun (I := I) (fun b : M => θ b (Y b)) x (X x) =
      extDerivFun (I := I) (fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) x (X x) := by
    have h_eq : (fun b : M => θ b (Y b)) =
        (fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) := h_eq_fn
    rw [h_eq]
  rw [h_lhs_eq] at hpair'
  have h_grad_inner : g.inner x (gradFun (I := I) g f x) (cov.toFun Y x (X x)) =
      θ x (cov.toFun Y x (X x)) := by
    rw [gradFun_metricDual_extDerivFun (I := I) g f x (cov.toFun Y x (X x))]
  have hkey : g.inner x (cov.toFun (fun b => gradFun (I := I) g f b) x (X x)) (Y x) =
      ((cotangentCov cov).toFun θ x (X x)) (Y x) := by
    have hlhs : extDerivFun (I := I) (fun b => g.inner b (gradFun (I := I) g f b) (Y b)) x (X x) =
        g.inner x (cov.toFun (fun b => gradFun (I := I) g f b) x (X x)) (Y x) +
          g.inner x (gradFun (I := I) g f x) (cov.toFun Y x (X x)) := hmc'
    rw [h_grad_inner] at hlhs
    have h := hlhs.symm.trans hpair'
    linarith [h]
  rw [hkey]
  rfl

/-- **Heart-of-Bochner identity, inner-product / abstract-Hessian formulation.** Combining
the symmetry of the abstract Hessian with the bridge between `g(∇_X(∇f), Y)` and the
abstract Hessian, the inner product `g(∇_X(∇f), Y)` is symmetric in `(X, Y)` at any point
where `f` is `C²`. This is the engine identity that, traced over any orthonormal frame,
produces the heart-of-Bochner reduction. -/
theorem inner_cov_gradFun_symm [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (X x)) (Y x) =
      g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (Y x)) (X x) := by
  classical
  rw [inner_cov_gradFun_eq_abstractHessian (I := I) g hf hX hY,
      inner_cov_gradFun_eq_abstractHessian (I := I) g hf hY hX]
  exact abstractHessian_symm (I := I) g (hf.contMDiffAt.of_le (by
    have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    simpa using h1)) (X x) (Y x)

/-- **Section-level Hessian symmetry for the gradient.** As scalar functions on `M`, the
inner products `b ↦ g(∇_{X b}(∇f)(b), Y b)` and `b ↦ g(∇_{Y b}(∇f)(b), X b)` are equal.
This is the global form of `inner_cov_gradFun_symm` and is the natural input for
metric-compatibility differentiation steps in the heart-of-Bochner derivation. -/
theorem inner_cov_gradFun_symm_globally [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (fun b : M => g.inner b ((LeviCivita (I := I) g).toFun
                  (fun b' => gradFun (I := I) g f b') b (X b)) (Y b)) =
      (fun b : M => g.inner b ((LeviCivita (I := I) g).toFun
                  (fun b' => gradFun (I := I) g f b') b (Y b)) (X b)) := by
  funext b
  exact inner_cov_gradFun_symm (I := I) g hf hX hY

/-- **Heart-of-Bochner inner-product reduction at the curvature step.** For smooth tangent
fields `B`, `w` and smooth scalar `f` (with `f` of class `C∞`), the section-level vector
Ricci identity applied to `B, w, ∇f` plus metric skewness of the Riemann curvature
encodes the curvature contribution of the heart-of-Bochner identity:
$$
  g_x\bigl(\nabla_B \nabla_w (\nabla f) - \nabla_w \nabla_B (\nabla f) - \nabla_{[B, w]}(\nabla f),\, B\bigr) =
    g_x\bigl(R(B, w)(\nabla f),\, B\bigr) = - g_x\bigl(\nabla f,\, R(B, w) B\bigr).
$$
The right-most equality is the metric skewness of `riemannSec` (already exposed). -/
theorem heart_of_bochner_curvature_term [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {B w : Π b : M, TangentSpace I b} {x : M}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) :
    g.inner x (riemannSec (LeviCivita (I := I) g) B w
                (fun b => gradFun (I := I) g f b) x) (B x) =
      - g.inner x (gradFun (I := I) g f x)
          (riemannSec (LeviCivita (I := I) g) B w B x) := by
  have h := riemannSec_metric_skew (I := I) g (X := B) (Y := w)
    (Z := fun b => gradFun (I := I) g f b) (W := B) (x := x) hB hw
    (gradFun_contMDiff_total_section (I := I) g hf) hB
  linarith

/-- **Riesz uniqueness reduction for the heart-of-Bochner vector identity.** Two tangent
vectors `LHS, RHS ∈ T_x M` are equal iff `g.inner x LHS w = g.inner x RHS w` for every
`w ∈ T_x M`. This is the standard Riesz uniqueness on a finite-dimensional inner-product
space; we package it as a named lemma to highlight its role as the entry point from the
inner-product formulation to the vector formulation of the heart-of-Bochner identity. -/
lemma vector_eq_iff_inner_eq
    (g : SmoothRiemannianMetric I M) (x : M)
    (LHS RHS : TangentSpace I x) :
    LHS = RHS ↔ ∀ w : TangentSpace I x, g.inner x LHS w = g.inner x RHS w := by
  refine ⟨fun h _ => by rw [h], fun h => ?_⟩
  apply metricFlatLinear_injective (I := I) g x
  ext w
  rw [metricFlatLinear_apply, metricFlatLinear_apply]
  exact h w

/-- **Frame-traced inner product of the connection Laplacian on `∇f` against `w`.** This
is the LHS of the heart-of-Bochner identity in inner-product form, displayed in the trace
form that the downstream connection-Laplacian Bochner derivation will work with. It
unfolds the local connection-Laplacian against the inner product, applying metric
compatibility in two steps and the abstract-Hessian bridge to pre-organise the data into
the four atomic pieces:

* `B_i (Hess f(B_i, w))` — second-derivative term;
* `Hess f(B_i, ∇_{B_i} w)` — connection-correction in `w`;
* `Hess f(∇_{B_i} B_i, w)` — connection-correction in `B`.

The final assembly into `mfderiv (Δf) (w x) + ricciTensor g x (∇f x) (w x)` requires
orthonormality of the frame `B` at `x` and is performed in a downstream file. -/
lemma localConnLap_vector_grad_inner_eq_hessian_diff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (_hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {w : Π b : M, TangentSpace I b}
    (_hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (_hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (x : M) :
    g.inner x (localConnLap_vector (LeviCivita (I := I) g) B
                  (fun b => gradFun (I := I) g f b) x) (w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x ((LeviCivita (I := I) g).toFun
                    (covApply (LeviCivita (I := I) g) (B i)
                      (fun b => gradFun (I := I) g f b)) x (B i x)) (w x) -
          g.inner x ((LeviCivita (I := I) g).toFun
                      (fun b => gradFun (I := I) g f b) x
                      ((LeviCivita (I := I) g).toFun (B i) x (B i x))) (w x)) := by
  classical
  unfold localConnLap_vector
  set u : Fin (Module.finrank ℝ E) → TangentSpace I x := fun i =>
    (LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) (B i)
          (fun b => gradFun (I := I) g f b)) x (B i x) -
      (LeviCivita (I := I) g).toFun
        (fun b => gradFun (I := I) g f b) x
        ((LeviCivita (I := I) g).toFun (B i) x (B i x)) with hu_def
  have h1 : g.inner x (∑ i : Fin (Module.finrank ℝ E), u i) =
      ∑ i : Fin (Module.finrank ℝ E), g.inner x (u i) := map_sum _ _ _
  have h2 : ∀ S : Finset (Fin (Module.finrank ℝ E)),
      (∑ i ∈ S, g.inner x (u i)) (w x) = ∑ i ∈ S, g.inner x (u i) (w x) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, ContinuousLinearMap.add_apply, ih]
  rw [h1, h2]
  refine Finset.sum_congr rfl ?_
  intro i _
  show g.inner x (u i) (w x) = _
  rw [hu_def]
  rw [map_sub, ContinuousLinearMap.sub_apply]

/-- **Heart-of-Bochner vector identity, conditional form.** Given a smooth frame
`B : Fin n → Π b, TangentSpace I b` and a smooth scalar `f : M → ℝ`, suppose the
inner-product reduction holds: for every smooth tangent test field `w` (and at the point
`x`),
$$
  g_x\bigl((\Delta_\nabla^B \nabla f)(x), w(x)\bigr) =
    g_x\bigl(\nabla(\Delta_g f)(x), w(x)\bigr) + g_x\bigl(\mathrm{Ric}^\sharp(\nabla f x), w(x)\bigr).
$$
Then the vector identity holds:
$$
  (\Delta_\nabla^B \nabla f)(x) = \nabla(\Delta_g f)(x) + \mathrm{Ric}^\sharp(\nabla f x).
$$
The hypothesis is exactly the inner-product form of the heart-of-Bochner identity, which
holds for `B` orthonormal at `x` by the algebraic content packaged in
`inner_cov_gradFun_eq_abstractHessian`, `inner_cov_gradFun_symm`, and
`heart_of_bochner_curvature_term` together with the Hessian-trace-equals-Laplacian
identity (in turn the divergence-of-gradient identity). -/
theorem heart_of_bochner_of_inner_form [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (_hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (x : M)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (localConnLap_vector (LeviCivita (I := I) g) B
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    localConnLap_vector (LeviCivita (I := I) g) B
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) := by
  rw [vector_eq_iff_inner_eq (I := I) g x]
  intro w
  rw [hInner w]
  rw [show g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x)) w =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
        g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w from
    by rw [map_add, ContinuousLinearMap.add_apply]]

end Connection
end Integral
end DifferentialGeometry
