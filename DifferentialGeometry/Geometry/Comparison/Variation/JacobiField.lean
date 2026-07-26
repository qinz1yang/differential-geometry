import DifferentialGeometry.Geometry.Comparison.Variation.CovariantCommutationCurvature

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Jacobi fields along a curve

`IsJacobiAlong g γ J`: the Jacobi equation `D_t² J + R(J, γ̇)γ̇ = 0` for a vector
field `J` along a curve `γ`, with `D_t` the intrinsic covariant derivative along the
curve (`covDerivAlong`) and the curvature operator in the `riemannOp` form — the
exact shape produced by the covariant-derivative commutation theorem
`commute_ds_dt_curvature_innerS` (`riemannOp x u v w = R(u,v)w` slot order), so that
the variation-through-geodesics proof lines up without reshaping.

This is stage 2 of the normal-coordinate metric-bound route (MSM135 Chapter 4 Step B,
B0; see `Geometry/Flow/RicciFlow/HCGCompactness/B0NormalCoordBounds.md`): the
coordinate vector fields of a normal chart are Jacobi fields along the radial
geodesics, and their Grönwall estimates produce the uniform `∂^α g_{ij}` bounds.
-/

noncomputable section

open Set Function Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- The velocity field of a curve, in the `mfderiv` form used by the
covariant-commutation theorem. -/
noncomputable def curveVelocity (γ : ℝ → M) (t : ℝ) : TangentSpace I (γ t) :=
  mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)

/-- **The Jacobi equation at a single parameter.**  `D_t² J + R(J, γ̇)γ̇ = 0` at `t`,
with `D_t = covDerivAlong g γ` and the curvature operator in the `riemannOp` slot
order of the covariant-commutation theorems (`riemannOp x u v w = R(u,v)w`). -/
def IsJacobiAt (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ) : Prop :=
  covDerivAlong (I := I) g γ
      (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
    + (DifferentialGeometry.Integral.Connection.riemannOp
        (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
        (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
    = 0

/-- **The Jacobi equation along a curve.**  `D_t² J + R(J, γ̇)γ̇ = 0` pointwise, with
`D_t = covDerivAlong g γ` and the curvature operator in the `riemannOp` slot order of
`commute_ds_dt_curvature_innerS` (`riemannOp x u v w = R(u,v)w`). -/
def IsJacobiAlong (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) : Prop :=
  ∀ t : ℝ, IsJacobiAt (I := I) g γ J t

/-- Unfolding lemma for the Jacobi equation at a point. -/
theorem isJacobiAlong_iff (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) :
    IsJacobiAlong (I := I) g γ J ↔
      ∀ t : ℝ,
        covDerivAlong (I := I) g γ
            (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
          = - (DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
              (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := by
  constructor
  · intro hJ t
    have h : covDerivAlong (I := I) g γ
          (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
        + (DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
            (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
        = 0 := hJ t
    linear_combination (norm := module) h
  · intro hJ t
    have h := hJ t
    change covDerivAlong (I := I) g γ
          (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
        + (DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
            (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
        = 0
    linear_combination (norm := module) h

/-- Read the second covariant derivative directly from the pointwise Jacobi
equation. -/
theorem jacobi_d2_eq
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) {t : ℝ}
    (hJ : IsJacobiAt (I := I) g γ J t) :
    covDerivAlong (I := I) g γ
        (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
      = - (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := by
  change covDerivAlong (I := I) g γ
        (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
      + (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
      = 0 at hJ
  linear_combination (norm := module) hJ

/-- Wronskian pairing of two vector fields along the same curve.  For Jacobi
fields this quantity is constant. -/
def jacobiWronskian
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ) : ℝ :=
  g.inner (γ t) (covDerivAlong (I := I) g γ J t) (K t) -
    g.inner (γ t) (J t) (covDerivAlong (I := I) g γ K t)

/-- The Wronskian of two pointwise Jacobi fields has zero derivative under
pointwise curve regularity. -/
theorem wronskian_deriv_at
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hJdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hKdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ K t) t)
    (hDJdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hDKdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ K s) t) t)
    (hJ : IsJacobiAt (I := I) g γ J t)
    (hK : IsJacobiAt (I := I) g γ K t) :
    HasDerivAt (jacobiWronskian (I := I) g γ J K) 0 t := by
  have hleft := inner_deriv_at (I := I) hn g γ
    (fun s => covDerivAlong (I := I) g γ J s) K t hγ hDJdiff hKdiff
  have hright := inner_deriv_at (I := I) hn g γ J
    (fun s => covDerivAlong (I := I) g γ K s) t hγ hJdiff hDKdiff
  have hsub := hleft.sub hright
  have hJ2 := jacobi_d2_eq (I := I) g γ J hJ
  have hK2 := jacobi_d2_eq (I := I) g γ K hK
  have hcurv := DifferentialGeometry.Integral.Connection.riemannOp_diag_symm
    (I := I) g (γ t) (curveVelocity (I := I) γ t) (J t) (K t)
  refine (hsub.congr_deriv ?_)
  rw [hJ2, hK2]
  simp only [map_neg, ContinuousLinearMap.neg_apply]
  linarith

/-- Smooth-curve wrapper for `wronskian_deriv_at`. -/
theorem hasDerivAt_wronsk
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ)
    (hJdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hKdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ K t) t)
    (hDJdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hDKdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ K s) t) t)
    (hJ : IsJacobiAt (I := I) g γ J t)
    (hK : IsJacobiAt (I := I) g γ K t) :
    HasDerivAt (jacobiWronskian (I := I) g γ J K) 0 t :=
  wronskian_deriv_at (I := I) hn g γ J K t hγ.contMDiffAt
    hJdiff hKdiff hDJdiff hDKdiff hJ hK

/-- Two Jacobi fields that vanish initially have zero Wronskian on an interval
when the curve is smooth at each point of that interval. -/
theorem wronskian_zero_on
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) {b : ℝ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hKdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ K t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hDKdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ K s) t) t)
    (hJacJ : ∀ t ∈ Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ J t)
    (hJacK : ∀ t ∈ Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ K t)
    (hJ0 : J 0 = 0) (hK0 : K 0 = 0) :
    ∀ t ∈ Icc (0 : ℝ) b, jacobiWronskian (I := I) g γ J K t = 0 := by
  have hderiv : ∀ t ∈ Icc (0 : ℝ) b,
      HasDerivAt (jacobiWronskian (I := I) g γ J K) 0 t := by
    intro t ht
    exact wronskian_deriv_at (I := I) hn g γ J K t (hγ t ht)
      (hJdiff t ht) (hKdiff t ht) (hDJdiff t ht) (hDKdiff t ht)
      (hJacJ t ht) (hJacK t ht)
  have hcont : ContinuousOn (jacobiWronskian (I := I) g γ J K)
      (Icc (0 : ℝ) b) := by
    intro t ht
    exact (hderiv t ht).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont (fun t ht =>
    (hderiv t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
  have hzero : jacobiWronskian (I := I) g γ J K 0 = 0 := by
    simp only [jacobiWronskian, hJ0, hK0, map_zero,
      ContinuousLinearMap.zero_apply, sub_self]
  intro t ht
  rw [hconst t ht, hzero]

/-- Two Jacobi fields that vanish at the initial endpoint have zero Wronskian
throughout the interval. -/
theorem wronskian_eq_zero
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) {b : ℝ}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hKdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ K t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hDKdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ K s) t) t)
    (hJacJ : ∀ t ∈ Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ J t)
    (hJacK : ∀ t ∈ Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ K t)
    (hJ0 : J 0 = 0) (hK0 : K 0 = 0) :
    ∀ t ∈ Icc (0 : ℝ) b, jacobiWronskian (I := I) g γ J K t = 0 :=
  wronskian_zero_on (I := I) hn g γ J K (fun _ _ => hγ.contMDiffAt)
    hJdiff hKdiff hDJdiff hDKdiff hJacJ hJacK hJ0 hK0

/-- A pointwise Jacobi equation plus a curvature-term norm bound gives the
second-covariant-derivative norm bound used by Gronwall estimates. -/
theorem ode_bound_of_isJacobiAt
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) {K t : ℝ}
    (hJ : IsJacobiAt (I := I) g γ J t)
    (hcurv :
      g.inner (γ t)
        ((DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t))
        ((DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t))
      ≤ K ^ 2 * g.inner (γ t) (J t) (J t)) :
    g.inner (γ t)
      (covDerivAlong (I := I) g γ
        (fun s : ℝ => covDerivAlong (I := I) g γ J s) t)
      (covDerivAlong (I := I) g γ
        (fun s : ℝ => covDerivAlong (I := I) g γ J s) t)
      ≤ K ^ 2 * g.inner (γ t) (J t) (J t) := by
  have hD :
      covDerivAlong (I := I) g γ
          (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
        = - (DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
            (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := by
    have h := hJ
    change covDerivAlong (I := I) g γ
          (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
        + (DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
            (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
        = 0 at h
    linear_combination (norm := module) h
  rw [hD]
  simpa using hcurv

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
