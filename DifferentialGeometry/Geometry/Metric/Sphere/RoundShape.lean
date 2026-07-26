import DifferentialGeometry.Geometry.Metric.Sphere.RoundProjConnLC
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Shape operator and Gauss equation for the round sphere (Step C)

The outward unit normal of `S^n ⊂ E` at `x` is the position vector `↑x`.  Differentiating the
constraint `⟪dι Y, ↑·⟫ = 0` (tangent vectors are orthogonal to the normal) gives the shape-operator
identity `⟪D_v(dι Y), ↑x⟫ = −g(Y, v)`.  This is the analytic input to the Gauss equation that
computes the round sphere's sectional curvature.

## Main results

* `ambDeriv_inner_normal` — `⟪ambDeriv Y x v, ↑x⟫ = −roundInner x (Y x) v` (shape operator = identity).
* `ambDeriv_gauss` — the Gauss formula `D_v(dι Y) = dι(∇_v Y) − g(Y,v)·x`.
* `ambDeriv2` / `ambDeriv_bracket_symm` — the second ambient derivative and its bracket symmetry
  (ambient flatness), the keystone of the Gauss-equation computation.
* `inner_dIncl_metricCov` — the paired tangential reduction `⟪dι(∇_v S), dι W⟫ = ⟪D_v(dι S), dι W⟫`.
* `mdiffAt_inner_left` — differentiability of `p ↦ ⟪w, F p⟫`.
-/

noncomputable section

open Bundle Manifold Set Metric Module VectorField
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

omit [FiniteDimensional ℝ E] in
/-- **Shape operator = identity.**  Differentiating the orthogonality `⟪dι Y, ↑·⟫ = 0`, the normal
component of the ambient derivative of a pushed section is `⟪ambDeriv Y x v, ↑x⟫ = −g(Y x, v)`. -/
theorem ambDeriv_inner_normal {Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x}
    {x : sphere (0 : E) 1}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x)
    (v : TangentSpace (𝓡 n) x) :
    ⟪ambDeriv (n := n) Y x v, (↑x : E)⟫ = - roundInner (n := n) x (Y x) v := by
  have hYd := dInclField_mdifferentiableAt (n := n) hY
  have hcoeC : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ ((↑) : sphere (0 : E) 1 → E) x :=
    contMDiff_coe_sphere.contMDiffAt
  have hcoe : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x :=
    hcoeC.mdifferentiableAt (by simp)
  -- The orthogonality constraint, identically zero on the sphere.
  have hf0 : (fun b => ⟪dInclField (n := n) Y b, (↑b : E)⟫) = fun _ => (0 : ℝ) := by
    funext b
    refine Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self (↑b : E)) ?_
    rw [dInclField_apply, ← range_mfderiv_coe_sphere (n := n) b]
    exact ⟨Y b, rfl⟩
  -- Differentiate via the inner-product product rule; the constraint has zero derivative.
  have hmf := mfderiv_inner (n := n) hYd hcoe v
  have hf0' : mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      (fun b => ⟪dInclField (n := n) Y b, (↑b : E)⟫) x v = 0 := by
    rw [hf0]; simp only [mfderiv_const]; rfl
  have hmf2 := hf0'.symm.trans hmf
  -- The normal-derivative term is the metric pairing.
  have hcoeval : mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v = dIncl (n := n) x v := rfl
  have hroundeq : ⟪dInclField (n := n) Y x,
      mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v⟫ = roundInner (n := n) x (Y x) v := by
    rw [hcoeval, dInclField_apply, roundInner_apply]
  rw [hroundeq] at hmf2
  exact eq_neg_of_add_eq_zero_left hmf2.symm

omit [FiniteDimensional ℝ E] in
/-- **Gauss formula for the round sphere.**  The ambient directional derivative of a pushed tangent
section splits into its tangential part (the projection connection `∇ = projConn`) and a normal part
governed by the metric: `D_v(dι Y) = dι(∇_v Y) − g(Y, v)·x`.  (Outward unit normal `ν = ↑x`.) -/
theorem ambDeriv_gauss {Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x}
    {x : sphere (0 : E) 1}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x)
    (v : TangentSpace (𝓡 n) x) :
    ambDeriv (n := n) Y x v
      = dIncl (n := n) x (projConn (n := n) Y x v) - roundInner (n := n) x (Y x) v • (↑x : E) := by
  have hnorm : ‖(↑x : E)‖ = 1 := norm_eq_of_mem_sphere x
  -- Singleton projection onto the normal line (unit `↑x`).
  have hsing : (ℝ ∙ (↑x : E)).starProjection (ambDeriv (n := n) Y x v)
      = ⟪(↑x : E), ambDeriv (n := n) Y x v⟫ • (↑x : E) := by
    rw [Submodule.starProjection_singleton, hnorm]; norm_num
  -- Tangential part = `w − ⟪x, w⟫ • x`.
  have hproj : dIncl (n := n) x (projConn (n := n) Y x v)
      = ambDeriv (n := n) Y x v - ⟪(↑x : E), ambDeriv (n := n) Y x v⟫ • (↑x : E) := by
    rw [dIncl_projConn, Submodule.coe_orthogonalProjection_apply]
    have hsplit := (ℝ ∙ (↑x : E)).starProjection_add_starProjection_orthogonal
      (ambDeriv (n := n) Y x v)
    rw [hsing] at hsplit
    exact eq_sub_of_add_eq (by rw [add_comm]; exact hsplit)
  -- Identify the normal coefficient via the shape-operator identity (C1).
  have hcomm : ⟪(↑x : E), ambDeriv (n := n) Y x v⟫ = - roundInner (n := n) x (Y x) v := by
    rw [real_inner_comm]; exact ambDeriv_inner_normal (n := n) hY v
  rw [hproj, hcomm]
  module

/-- The ambient second directional derivative `v ↦ D_v(D_W(dι Z))` as an `E`-valued CLM (codomain
ascribed to `E` to avoid the per-point `TangentSpace 𝓘(ℝ,E)` synonym, exactly as `ambDeriv` does). -/
noncomputable def ambDeriv2
    (Z W : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1) : TangentSpace (𝓡 n) x →L[ℝ] E :=
  (mfderiv (𝓡 n) 𝓘(ℝ, E) (fun p => ambDeriv (n := n) (⇑Z) p (W p)) x :
    TangentSpace (𝓡 n) x →L[ℝ] E)

omit [FiniteDimensional ℝ E] in
@[simp] theorem ambDeriv2_apply
    (Z W : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    ambDeriv2 (n := n) Z W x v
      = mfderiv (𝓡 n) 𝓘(ℝ, E) (fun p => ambDeriv (n := n) (⇑Z) p (W p)) x v := rfl

/-- **Ambient flatness / second-derivative bracket symmetry.**  For a smooth section `Z` and smooth
fields `X, Y` on the sphere, the iterated ambient derivative of `dι Z` is symmetric up to the bracket:
`D_X(D_Y(dι Z)) − D_Y(D_X(dι Z)) = D_{[X,Y]}(dι Z)`.  The two MDiffAt hypotheses are the smoothness of
the first covariant derivatives `D_Y(dι Z)`, `D_X(dι Z)` (supplied at the call site via
`cov_smooth_apply_contMDiffAt` + the Gauss formula).  Proved by the functional test against every
ambient `w`, applying `embedDeriv_mlieBracket` to the first-level field `embedDeriv Z (innerCoordFun w)`. -/
theorem ambDeriv_bracket_symm
    (Z X Y : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1)
    (hDY : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      (fun p => ambDeriv (n := n) (⇑Z) p (Y p)) x)
    (hDX : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      (fun p => ambDeriv (n := n) (⇑Z) p (X p)) x) :
    ambDeriv2 (n := n) Z Y x (X x) - ambDeriv2 (n := n) Z X x (Y x)
      = ambDeriv (n := n) (⇑Z) x (mlieBracket (𝓡 n) (⇑X) (⇑Y) x) := by
  simp only [ambDeriv2_apply]
  refine ext_inner_left ℝ fun w => ?_
  -- `dι Z` is differentiable everywhere (smooth section).
  have hZdiff : ∀ p : sphere (0 : E) 1,
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) (⇑Z)) p := fun p =>
    dInclField_mdifferentiableAt (n := n) (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  -- Level-0 field `g w = embedDeriv Z (innerCoordFun w) = ⟪w, dι Z ·⟫`.
  set gw := embedDeriv (𝓡 n) (sphere (0 : E) 1) Z (innerCoordFun (E := E) (n := n) w) with hgwdef
  have hgw : (⇑gw : sphere (0 : E) 1 → ℝ) = fun p => ⟪w, dInclField (n := n) (⇑Z) p⟫ := by
    funext p
    change vectorFieldAction (𝓡 n) (sphere (0 : E) 1) Z (innerCoordFun w) p = _
    simp only [vectorFieldAction]
    rw [show extDerivFun (I := 𝓡 n) (innerCoordFun w) p (Z p)
          = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (innerCoordFun (E := E) (n := n) w) p (Z p) from rfl,
      mfderiv_innerCoordFun, dInclField_apply]
  -- Level-1 field `embedDeriv W g w = ⟪w, D_W(dι Z) ·⟫`, for any smooth field `W`.
  have hWlevel : ∀ (W : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯),
      (⇑(embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw) : sphere (0 : E) 1 → ℝ)
        = fun p => ⟪w, ambDeriv (n := n) (⇑Z) p (W p)⟫ := by
    intro W
    funext p
    change vectorFieldAction (𝓡 n) (sphere (0 : E) 1) W gw p = _
    simp only [vectorFieldAction]
    rw [show extDerivFun (I := 𝓡 n) gw p (W p)
          = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (⇑gw) p (W p) from rfl,
      hgw, mfderiv_inner_left w (hZdiff p) (W p), ambDeriv_apply]
  -- Level-2: differentiate the level-1 field, using the supplied smoothness of `D_W(dι Z)`.
  have hsecond : ∀ (V W : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯),
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (fun p => ambDeriv (n := n) (⇑Z) p (W p)) x →
      (embedDeriv (𝓡 n) (sphere (0 : E) 1) V
          (embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw) : sphere (0 : E) 1 → ℝ) x
        = ⟪w, mfderiv (𝓡 n) 𝓘(ℝ, E)
            (fun p => ambDeriv (n := n) (⇑Z) p (W p)) x (V x)⟫ := by
    intro V W hD
    change vectorFieldAction (𝓡 n) (sphere (0 : E) 1) V
      (embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw) x = _
    simp only [vectorFieldAction]
    rw [show extDerivFun (I := 𝓡 n) (embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw) x (V x)
          = mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
              (⇑(embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw)) x (V x) from rfl,
      hWlevel W, mfderiv_inner_left w hD (V x)]
  -- The bracket identity at `x`.
  have hbr := embedDeriv_mlieBracket (I := 𝓡 n) (M := sphere (0 : E) 1) X Y gw
  have hbrx : (embedDeriv (𝓡 n) (sphere (0 : E) 1)
        (mlieBracketSection (𝓡 n) (sphere (0 : E) 1) X Y) gw : sphere (0 : E) 1 → ℝ) x
      = (embedDeriv (𝓡 n) (sphere (0 : E) 1) X
          (embedDeriv (𝓡 n) (sphere (0 : E) 1) Y gw) : sphere (0 : E) 1 → ℝ) x
        - (embedDeriv (𝓡 n) (sphere (0 : E) 1) Y
            (embedDeriv (𝓡 n) (sphere (0 : E) 1) X gw) : sphere (0 : E) 1 → ℝ) x := by
    have h := DFunLike.congr_fun hbr x
    simpa using h
  -- Bracket-section level: `embedDeriv [X,Y] g w x = ⟪w, D_{[X,Y]}(dι Z)⟫`.
  have hbrlevel : (embedDeriv (𝓡 n) (sphere (0 : E) 1)
        (mlieBracketSection (𝓡 n) (sphere (0 : E) 1) X Y) gw : sphere (0 : E) 1 → ℝ) x
      = ⟪w, ambDeriv (n := n) (⇑Z) x (mlieBracket (𝓡 n) (⇑X) (⇑Y) x)⟫ := by
    rw [hWlevel (mlieBracketSection (𝓡 n) (sphere (0 : E) 1) X Y)]
    rfl
  rw [hbrlevel, hsecond X Y hDY, hsecond Y X hDX] at hbrx
  rw [inner_sub_right]
  exact hbrx.symm

/-- **Paired tangential reduction.**  The connection value `∇_v S = metricCov g S x v` paired against a
tangent vector equals the ambient derivative paired against it (the normal part of `D_v(dι S)` drops
out): `⟪dι(∇_v S), dι W⟫ = ⟪D_v(dι S), dι W⟫`.  The orthogonal projection is self-adjoint and fixes the
tangent vector `dι W`. -/
theorem inner_dIncl_metricCov
    {S : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x} {x : sphere (0 : E) 1}
    (hS : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (S y))) x)
    (v W : TangentSpace (𝓡 n) x) :
    ⟪dIncl (n := n) x (Integral.Connection.metricCov (roundMetric (E := E) (n := n)) S x v),
        dIncl (n := n) x W⟫
      = ⟪ambDeriv (n := n) S x v, dIncl (n := n) x W⟫ := by
  rw [← projConn_eq_metricCov hS v, dIncl_projConn, ← Submodule.starProjection_apply]
  have hmem : dIncl (n := n) x W ∈ (ℝ ∙ (↑x : E))ᗮ := by
    rw [← range_mfderiv_coe_sphere (n := n) x]; exact ⟨W, rfl⟩
  have h0 := Submodule.starProjection_inner_eq_zero (K := (ℝ ∙ (↑x : E))ᗮ)
    (ambDeriv (n := n) S x v) (dIncl (n := n) x W) hmem
  rw [inner_sub_left, sub_eq_zero] at h0
  exact h0.symm

omit [FiniteDimensional ℝ E] in
/-- Differentiability companion of `mfderiv_inner_left`: `p ↦ ⟪w, F p⟫` is differentiable.  Stated with
`F` generic so a concrete coercion is passed as an argument, avoiding the chart mis-inference that a
bare `MDifferentiableAt (fun p => ⟪w, ↑p⟫)` triggers. -/
theorem mdiffAt_inner_left (w : E) {F : sphere (0 : E) 1 → E} {x : sphere (0 : E) 1}
    (hF : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) F x) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun p => ⟪w, F p⟫) x := by
  haveI : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) (F x)) :=
    inferInstanceAs (InnerProductSpace ℝ E)
  exact ((innerSL ℝ w).hasFDerivAt.hasMFDerivAt.comp x hF.hasMFDerivAt).mdifferentiableAt

omit [FiniteDimensional ℝ E] in
/-- **Normal-direction Leibniz term (scalar form).**  The derivative of `φ · ⟪w, ↑·⟫` paired with a
fixed `w ⊥ ↑x` keeps only the `φ(x)·⟪w, dι v⟫` term — the `dφ` term dies.  Stated through the *bundled*
`innerCoordFun w` (never a bare `⟪w, ↑·⟫` lambda), so it never re-elaborates the bare-coercion
`mfderiv` that demands a false `ChartedSpace E` instance. -/
theorem mfderiv_mul_innerCoordFun_of_inner_eq_zero
    (w : E) {φ : sphere (0 : E) 1 → ℝ} {x : sphere (0 : E) 1}
    (hφ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) φ x) (horth : ⟪w, (↑x : E)⟫ = 0)
    (v : TangentSpace (𝓡 n) x) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
        (fun p => φ p * (innerCoordFun (E := E) (n := n) w) p) x v
      = φ x * ⟪w, dIncl (n := n) x v⟫ := by
  set ψ : sphere (0 : E) 1 → ℝ := ⇑(innerCoordFun (E := E) (n := n) w) with hψdef
  have hψ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) ψ x :=
    (innerCoordFun (E := E) (n := n) w).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hψx : ψ x = 0 := by rw [hψdef]; simpa [innerCoordFun] using horth
  -- Rewrite `mfderiv ψ x` to a CLEAN-codomain CLM (`T_x →L ℝ`, not the `TangentSpace 𝓘(ℝ,ℝ)`
  -- synonym) so that `smul_apply`/`comp_apply` reduce.
  have hψCLM : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) ψ x = (innerSL ℝ w).comp (dIncl (n := n) x) := by
    ext u
    show mfderiv (𝓡 n) 𝓘(ℝ, ℝ) ψ x u = ⟪w, dIncl (n := n) x u⟫
    exact mfderiv_innerCoordFun (E := E) (n := n) w x u
  show mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (φ * ψ) x v = φ x * ⟪w, dIncl (n := n) x v⟫
  rw [(hφ.hasMFDerivAt.mul hψ.hasMFDerivAt).mfderiv]
  simp only [hψx, hψCLM, zero_smul, add_zero]
  change φ x • (((innerSL ℝ w).comp (dIncl (n := n) x)) v) = φ x * ⟪w, dIncl (n := n) x v⟫
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]

set_option maxHeartbeats 800000 in
/-- **Nested-derivative expansion (Gauss + flatness input).**  Pairing the ambient derivative of the
nested connection section `A = ∇_{Yf} Z` against a tangent vector splits into the second ambient
derivative `ambDeriv2` (cancelled later by flatness) and a Gram term; the normal part of the Gauss
formula only survives as `g(Z,Yf)·⟪dι v, dι W⟫`. -/
theorem inner_ambDeriv_nested
    (Z Yf : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1) (v W : TangentSpace (𝓡 n) x)
    (hD : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      (fun p => ambDeriv (n := n) (⇑Z) p (Yf p)) x) :
    ⟪ambDeriv (n := n)
        (fun p => Integral.Connection.metricCov (roundMetric (E := E) (n := n)) (⇑Z) p (Yf p)) x v,
        dIncl (n := n) x W⟫
      = ⟪dIncl (n := n) x W, ambDeriv2 (n := n) Z Yf x v⟫
        + roundInner (n := n) x (Z x) (Yf x) * ⟪dIncl (n := n) x W, dIncl (n := n) x v⟫ := by
  have hZp : ∀ p, MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y ((⇑Z) y))) p := fun p =>
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hZd : ∀ p, MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) (⇑Z)) p := fun p =>
    dInclField_mdifferentiableAt (n := n) (hZp p)
  have hYfd : ∀ p, MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) (⇑Yf)) p := fun p =>
    dInclField_mdifferentiableAt (n := n) (Yf.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have hcoeC : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ ((↑) : sphere (0 : E) 1 → E) x :=
    contMDiff_coe_sphere.contMDiffAt
  have hcoeM : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x :=
    hcoeC.mdifferentiableAt (by simp)
  -- Gauss formula for the nested section's pushed field.
  have hAfun : dInclField (n := n)
        (fun p => Integral.Connection.metricCov (roundMetric (E := E) (n := n)) (⇑Z) p (Yf p))
      = fun p => ambDeriv (n := n) (⇑Z) p (Yf p)
          + roundInner (n := n) p (Z p) (Yf p) • (↑p : E) := by
    funext p
    rw [dInclField_apply, ← projConn_eq_metricCov (hZp p) (Yf p),
      ambDeriv_gauss (n := n) (hZp p) (Yf p)]
    module
  -- `φ p = g(Z,Yf)` is smooth.
  have hφ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun p => roundInner (n := n) p (Z p) (Yf p)) x := by
    have hb : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun p => ⟪dInclField (n := n) (⇑Z) p, dInclField (n := n) (⇑Yf) p⟫) x _ :=
      ((isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E)).hasFDerivAt
        (dInclField (n := n) (⇑Z) x, dInclField (n := n) (⇑Yf) x)).hasMFDerivAt.comp x
        ((hZd x).hasMFDerivAt.prodMk (hYfd x).hasMFDerivAt)
    have heq : (fun p => roundInner (n := n) p (Z p) (Yf p))
        = fun p => ⟪dInclField (n := n) (⇑Z) p, dInclField (n := n) (⇑Yf) p⟫ := by
      funext p; rw [roundInner_apply]; rfl
    rw [heq]; exact hb.mdifferentiableAt
  -- The nested pushed field is differentiable at `x`.
  have hAd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n)
        (fun p => Integral.Connection.metricCov (roundMetric (E := E) (n := n)) (⇑Z) p (Yf p))) x := by
    rw [hAfun]; exact hD.add (hφ.smul hcoeM)
  have hψ0 : ⟪dIncl (n := n) x W, (↑x : E)⟫ = (0 : ℝ) :=
    Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self _)
      (by rw [← range_mfderiv_coe_sphere (n := n) x]; exact ⟨W, rfl⟩)
  -- Move to the scalar field `⟪dι W, dι A ·⟫` and split via the Gauss form (`innerCoordFun` for the
  -- normal part, so no bare `⟪dι W, ↑·⟫` lambda appears).
  rw [ambDeriv_apply, real_inner_comm, ← mfderiv_inner_left (dIncl (n := n) x W) hAd v]
  have hscal : (fun p => ⟪dIncl (n := n) x W, dInclField (n := n)
        (fun p => Integral.Connection.metricCov (roundMetric (E := E) (n := n)) (⇑Z) p (Yf p)) p⟫)
      = (fun p => ⟪dIncl (n := n) x W, ambDeriv (n := n) (⇑Z) p (Yf p)⟫)
          + (fun p => roundInner (n := n) p (Z p) (Yf p)
              * (innerCoordFun (E := E) (n := n) (dIncl (n := n) x W)) p) := by
    funext p
    simp only [Pi.add_apply, hAfun, inner_add_right, inner_smul_right]
    rfl
  have hMh1 : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun p => ⟪dIncl (n := n) x W, ambDeriv (n := n) (⇑Z) p (Yf p)⟫) x :=
    mdiffAt_inner_left (dIncl (n := n) x W) hD
  have hMh2 : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun p => roundInner (n := n) p (Z p) (Yf p)
        * (innerCoordFun (E := E) (n := n) (dIncl (n := n) x W)) p) x :=
    hφ.mul ((innerCoordFun (E := E) (n := n)
      (dIncl (n := n) x W)).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  -- Rewrite both derivative CLMs to CLEAN-codomain `T_x →L ℝ` form (dodging the `TangentSpace 𝓘(ℝ,ℝ)`
  -- synonym that blocks `add_apply`), then split and evaluate.
  have h1CLM : mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      (fun p => ⟪dIncl (n := n) x W, ambDeriv (n := n) (⇑Z) p (Yf p)⟫) x
        = (innerSL ℝ (dIncl (n := n) x W)).comp (ambDeriv2 (n := n) Z Yf x) := by
    ext u
    show mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
        (fun p => ⟪dIncl (n := n) x W, ambDeriv (n := n) (⇑Z) p (Yf p)⟫) x u
          = ⟪dIncl (n := n) x W, ambDeriv2 (n := n) Z Yf x u⟫
    rw [mfderiv_inner_left (dIncl (n := n) x W) hD u, ← ambDeriv2_apply]
  have hψ0' : (innerCoordFun (E := E) (n := n) (dIncl (n := n) x W)) x = 0 := by
    simpa [innerCoordFun] using hψ0
  have hψCLM : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (innerCoordFun (E := E) (n := n) (dIncl (n := n) x W)) x
      = (innerSL ℝ (dIncl (n := n) x W)).comp (dIncl (n := n) x) := by
    ext u
    show mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (innerCoordFun (E := E) (n := n) (dIncl (n := n) x W)) x u
        = ⟪dIncl (n := n) x W, dIncl (n := n) x u⟫
    exact mfderiv_innerCoordFun (E := E) (n := n) (dIncl (n := n) x W) x u
  have h2CLM : mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      (fun p => roundInner (n := n) p (Z p) (Yf p)
        * (innerCoordFun (E := E) (n := n) (dIncl (n := n) x W)) p) x
        = (roundInner (n := n) x (Z x) (Yf x))
          • (innerSL ℝ (dIncl (n := n) x W)).comp (dIncl (n := n) x) := by
    show mfderiv (𝓡 n) 𝓘(ℝ, ℝ) ((fun p => roundInner (n := n) p (Z p) (Yf p))
        * ⇑(innerCoordFun (E := E) (n := n) (dIncl (n := n) x W))) x = _
    rw [(hφ.hasMFDerivAt.mul ((innerCoordFun (E := E) (n := n)
      (dIncl (n := n) x W)).contMDiff.contMDiffAt.mdifferentiableAt (by simp)).hasMFDerivAt).mfderiv,
      hψCLM, hψ0', zero_smul, add_zero]
  rw [hscal, mfderiv_add hMh1 hMh2, h1CLM, h2CLM]
  rfl

/-- The first ambient covariant derivative `p ↦ D_{Yf}(dι Z)` of one smooth section along another is
differentiable (the hypothesis `ambDeriv_bracket_symm`/`inner_ambDeriv_nested` need).  Via the Gauss
formula it equals `dι(∇_{Yf} Z) − g(Z,Yf)·ν`, both summands smooth (`metricCov` sections are smooth). -/
theorem ambDeriv_section_mdiffAt
    (Z Yf : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (fun p => ambDeriv (n := n) (⇑Z) p (Yf p)) x := by
  have hZp : ∀ p, MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y ((⇑Z) y))) p := fun p =>
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hZd : ∀ p, MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) (⇑Z)) p := fun p =>
    dInclField_mdifferentiableAt (n := n) (hZp p)
  have hYfd : ∀ p, MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) (⇑Yf)) p := fun p =>
    dInclField_mdifferentiableAt (n := n) (Yf.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have hcoeC : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ ((↑) : sphere (0 : E) 1 → E) x :=
    contMDiff_coe_sphere.contMDiffAt
  have hcoeM : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x :=
    hcoeC.mdifferentiableAt (by simp)
  have hφ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun p => roundInner (n := n) p (Z p) (Yf p)) x := by
    have hb : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun p => ⟪dInclField (n := n) (⇑Z) p, dInclField (n := n) (⇑Yf) p⟫) x _ :=
      ((isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E)).hasFDerivAt
        (dInclField (n := n) (⇑Z) x, dInclField (n := n) (⇑Yf) x)).hasMFDerivAt.comp x
        ((hZd x).hasMFDerivAt.prodMk (hYfd x).hasMFDerivAt)
    have heq : (fun p => roundInner (n := n) p (Z p) (Yf p))
        = fun p => ⟪dInclField (n := n) (⇑Z) p, dInclField (n := n) (⇑Yf) p⟫ := by
      funext p; rw [roundInner_apply]; rfl
    rw [heq]; exact hb.mdifferentiableAt
  have hAd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n)
        (fun p => Integral.Connection.metricCov (roundMetric (E := E) (n := n)) (⇑Z) p (Yf p))) x :=
    dInclField_mdifferentiableAt (n := n)
      ((Integral.Connection.CovariantDerivative.cov_smooth_apply_contMDiffAt
        (Integral.Connection.metricCov (roundMetric (E := E) (n := n)))
        (Integral.Connection.metricCov_smooth (roundMetric (E := E) (n := n))) Yf Z x).mdifferentiableAt
        (by simp))
  have hAfun : dInclField (n := n)
        (fun p => Integral.Connection.metricCov (roundMetric (E := E) (n := n)) (⇑Z) p (Yf p))
      = fun p => ambDeriv (n := n) (⇑Z) p (Yf p)
          + roundInner (n := n) p (Z p) (Yf p) • (↑p : E) := by
    funext p
    rw [dInclField_apply, ← projConn_eq_metricCov (hZp p) (Yf p),
      ambDeriv_gauss (n := n) (hZp p) (Yf p)]
    module
  rw [eq_sub_of_add_eq hAfun.symm]
  exact hAd.sub (hφ.smul hcoeM)

set_option maxHeartbeats 800000 in
/-- **The Gauss equation (pre-pairing).**  For smooth sections `X Y Z`, the metric Riemann curvature of
the round sphere paired against a tangent vector is the Gram combination
`⟪dι R(X,Y)Z, dι W⟫ = g(Z,Y)·⟪dι X, dι W⟫ − g(Z,X)·⟪dι Y, dι W⟫`.  The second-derivative parts cancel by
ambient flatness (`ambDeriv_bracket_symm`); the projection corrections drop out against the tangent
`dι W`; the Gauss normal terms survive as the Gram products. -/
theorem dIncl_curv_inner
    (Z X Y : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1) (W : TangentSpace (𝓡 n) x)
    (hDY : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      (fun p => ambDeriv (n := n) (⇑Z) p (Y p)) x)
    (hDX : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      (fun p => ambDeriv (n := n) (⇑Z) p (X p)) x) :
    ⟪dIncl (n := n) x (Integral.Connection.CovariantDerivative.riemannCurvatureAux
        (Integral.Connection.metricCov (roundMetric (E := E) (n := n))) (⇑X) (⇑Y) (⇑Z) x),
        dIncl (n := n) x W⟫
      = roundInner (n := n) x (Z x) (Y x) * ⟪dIncl (n := n) x (X x), dIncl (n := n) x W⟫
        - roundInner (n := n) x (Z x) (X x) * ⟪dIncl (n := n) x (Y x), dIncl (n := n) x W⟫ := by
  set g := roundMetric (E := E) (n := n) with hg
  -- Differentiability of the three sections fed to the connection.
  have hZb : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y ((⇑Z) y))) x :=
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hA : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        ((fun p => Integral.Connection.metricCov g (⇑Z) p (Y p)) y))) x :=
    (Integral.Connection.CovariantDerivative.cov_smooth_apply_contMDiffAt
      (Integral.Connection.metricCov g) (Integral.Connection.metricCov_smooth g) Y Z x).mdifferentiableAt (by simp)
  have hB : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        ((fun p => Integral.Connection.metricCov g (⇑Z) p (X p)) y))) x :=
    (Integral.Connection.CovariantDerivative.cov_smooth_apply_contMDiffAt
      (Integral.Connection.metricCov g) (Integral.Connection.metricCov_smooth g) X Z x).mdifferentiableAt (by simp)
  -- Expand the curvature operator and inject `dι`, pairing with `dι W`.
  rw [show Integral.Connection.CovariantDerivative.riemannCurvatureAux
        (Integral.Connection.metricCov g) (⇑X) (⇑Y) (⇑Z) x
      = Integral.Connection.metricCov g (fun p => Integral.Connection.metricCov g (⇑Z) p (Y p)) x (X x)
        - Integral.Connection.metricCov g (fun p => Integral.Connection.metricCov g (⇑Z) p (X p)) x (Y x)
        - Integral.Connection.metricCov g (⇑Z) x (mlieBracket (𝓡 n) (⇑X) (⇑Y) x) from rfl,
    map_sub, map_sub, inner_sub_left, inner_sub_left,
    inner_dIncl_metricCov hA (X x) W, inner_dIncl_metricCov hB (Y x) W,
    inner_dIncl_metricCov hZb (mlieBracket (𝓡 n) (⇑X) (⇑Y) x) W,
    inner_ambDeriv_nested Z Y x (X x) W hDY, inner_ambDeriv_nested Z X x (Y x) W hDX]
  -- Flatness cancels the second-derivative parts; `real_inner_comm` aligns the Gram products.
  have hflat := ambDeriv_bracket_symm Z X Y x hDY hDX
  have hbr : ⟪dIncl (n := n) x W, ambDeriv2 (n := n) Z Y x (X x)⟫
      - ⟪dIncl (n := n) x W, ambDeriv2 (n := n) Z X x (Y x)⟫
        = ⟪ambDeriv (n := n) (⇑Z) x (mlieBracket (𝓡 n) (⇑X) (⇑Y) x), dIncl (n := n) x W⟫ := by
    rw [← inner_sub_right, hflat, real_inner_comm]
  rw [real_inner_comm (dIncl (n := n) x W) (dIncl (n := n) x (X x)),
    real_inner_comm (dIncl (n := n) x W) (dIncl (n := n) x (Y x))]
  linarith [hbr]

end Geometry
end DifferentialGeometry
