import DifferentialGeometry.Geometry.Exponential.Cartan.Local
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse
import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.MetricData
import DifferentialGeometry.Geometry.Thurston.Models.HomogeneousCompleteness
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Curvature.Metric.Sectional
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.PartialDiffeomorph
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Curvature.WarpedProduct.Exponential

/-!
# Constant curvature and the three isotropic Thurston models

Chapter 7, survey packet P4. A complete metric on a manifold modeled on `ℝ³` has constant
sectional curvature `κ ∈ {1, 0, -1}` (`HasConstantSectionalCurvature`, stated with
`Riemannian.sectionalCurvature` on linearly independent pairs) iff it has a Thurston atlas of
`constantCurvatureModel κ` (round `S³`, `E³`, coordinate `H³`):
`hasThurstonAtlas_iff_hasConstantSectionalCurvature`. The converse direction
`hasConstantSectionalCurvature_of_hasThurstonAtlas` needs no completeness.

The forward direction is the Cartan theorem `modelAtlas_of_riemannOp_eq_smul`, the
`R(X, Y) Z = κ (⟨Y, Z⟩ X - ⟨X, Z⟩ Y)` version of the library's `κ = 1` Jacobi transfer
(`expDiff_sq_xfer_smul`, `cartanPartialDiffeomorph_inner_smul`); completeness is used because
the library's exponential maps are global. The coordinate hyperbolic metric has curvature `-1`
(`coordinateModelMetric_hyperbolic_hasConstantSectionalCurvature`) as the pullback of the warped
product `dt² + e^{-2t} g_{ℝ²}` over the whole line, a line version of
`Curvature/WarpedProduct/Exponential.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Bundle
open scoped Topology Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection

namespace GC.Geometry

section Cartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  [I'.Boundaryless]
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' ∞ M'] [T2Space M'] [SigmaCompactSpace M']

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable
  [RiemannianBundle (fun x : M' ↦ TangentSpace I' x)]
  [PseudoEMetricSpace M'] [IsRiemannianManifold I' M'] [CompleteSpace M']
  [IsContinuousRiemannianBundle E (fun x : M' ↦ TangentSpace I' x)]

theorem expDiff_sq_xfer_smul (κ : ℝ)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (g' : SmoothRiemannianMetric I' M')
    (hEnorm' : ∀ (x : M') (v : TangentSpace I' x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g'.inner x v v)))
    (p : M) (p' : M') (u w : E)
    (i : E ≃L[ℝ] E)
    (hi : ∀ a b : E, g'.inner p' (i a) (i b) = g.inner p a b)
    (hR : ∀ (x : M) (X Y Z : TangentSpace I x),
      (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) x)
        X Y Z =
          κ • (g.inner x Y Z • X - g.inner x X Z • Y))
    (hR' : ∀ (x : M') (X Y Z : TangentSpace I' x),
      (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I') g') x)
        X Y Z =
          κ • (g'.inner x Y Z • X - g'.inner x X Z • Y)) :
    g'.inner
        (expMapIntrinsic (I := I') g' hEnorm' p'
          (show TangentSpace I' p' from i u))
        (mfderiv 𝓘(ℝ, E) I'
          (fun v : E => expMapIntrinsic (I := I') g' hEnorm' p'
            (show TangentSpace I' p' from v))
          (i u) (i w))
        (mfderiv 𝓘(ℝ, E) I'
          (fun v : E => expMapIntrinsic (I := I') g' hEnorm' p'
            (show TangentSpace I' p' from v))
          (i u) (i w))
      =
    g.inner
        (expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from u))
        (mfderiv 𝓘(ℝ, E) I
          (fun v : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from v))
          u w)
        (mfderiv 𝓘(ℝ, E) I
          (fun v : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from v))
          u w) := by
  classical
  let _ : Nonempty (Fin (Module.finrank ℝ (TangentSpace I p))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  let Fvar : ℝ → ℝ → M := fun s =>
    intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from u + s • w)
  let Fvar' : ℝ → ℝ → M' := fun s =>
    intrinsicGeodesic (I := I') g' hEnorm' p'
      (show TangentSpace I' p' from i u + s • i w)
  let γ : ℝ → M :=
    intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from u)
  let γ' : ℝ → M' :=
    intrinsicGeodesic (I := I') g' hEnorm' p'
      (show TangentSpace I' p' from i u)
  let Y : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => Fvar s t) 0 (1 : ℝ)
  let Y' : ∀ t : ℝ, TangentSpace I' (γ' t) := fun t =>
    mfderiv 𝓘(ℝ, ℝ) I' (fun s : ℝ => Fvar' s t) 0 (1 : ℝ)
  let V : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)
  let V' : ∀ t : ℝ, TangentSpace I' (γ' t) := fun t =>
    mfderiv 𝓘(ℝ, ℝ) I' γ' t (1 : ℝ)
  have hFvar : IsSmoothVariation (I := I) Fvar := by
    change ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ)
      (fun q : ℝ × ℝ => Fvar q.1 q.2)
    exact (intrinsicVar_smooth (I := I) g hEnorm p u w).of_le
      ENat.LEInfty.out
  have hFvar' : IsSmoothVariation (I := I') Fvar' := by
    change ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I' (8 : ℕ)
      (fun q : ℝ × ℝ => Fvar' q.1 q.2)
    exact (intrinsicVar_smooth (I := I') g' hEnorm' p' (i u) (i w)).of_le
      ENat.LEInfty.out
  have hcentral : Fvar 0 = γ := by
    funext t
    simp only [Fvar, γ, zero_smul, add_zero]
  have hcentral' : Fvar' 0 = γ' := by
    funext t
    simp only [Fvar', γ', zero_smul, add_zero]
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) γ := by
    have hincl : ContMDiff 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun t : ℝ => ((0 : ℝ), t)) :=
      contMDiff_const.prodMk contMDiff_id
    have hs := (hFvar : ContMDiff _ _ _ _).comp hincl
    change ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (Fvar 0) at hs
    rw [hcentral] at hs
    exact hs
  have hγ' : ContMDiff 𝓘(ℝ, ℝ) I' (8 : ℕ) γ' := by
    have hincl : ContMDiff 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun t : ℝ => ((0 : ℝ), t)) :=
      contMDiff_const.prodMk contMDiff_id
    have hs := (hFvar' : ContMDiff _ _ _ _).comp hincl
    change ContMDiff 𝓘(ℝ, ℝ) I' (8 : ℕ) (Fvar' 0) at hs
    rw [hcentral'] at hs
    exact hs
  have hγ0 : γ 0 = p := by
    simpa only [γ] using
      intrinsicGeodesic_zero (I := I) g hEnorm p
        (show TangentSpace I p from u)
  have hγ0' : γ' 0 = p' := by
    simpa only [γ'] using
      intrinsicGeodesic_zero (I := I') g' hEnorm' p'
        (show TangentSpace I' p' from i u)
  obtain ⟨basis, hbasis⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
      (I := I) g p
  have hseed : ∀ a b,
      g.inner (γ 0) (basis a) (basis b) =
        if a = b then (1 : ℝ) else 0 := by
    intro a b
    rw [hγ0]
    exact hbasis a b
  have hseed' : ∀ a b,
      g'.inner (γ' 0) (i (basis a)) (i (basis b)) =
        if a = b then (1 : ℝ) else 0 := by
    intro a b
    rw [hγ0']
    with_unfolding_all
      exact (hi (basis a) (basis b)).trans (hbasis a b)
  have hγ2 : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ :=
    hγ.of_le (by norm_num)
  have hγ2' : ContMDiff 𝓘(ℝ, ℝ) I' (2 : ℕ∞) γ' :=
    hγ'.of_le (by norm_num)
  obtain ⟨frame, hframe0, hframeDiff, hframePar, hframeON⟩ :=
    exists_parallel_frame (I := I) g γ (N := 2) (by norm_num) hγ2
      (by norm_num : (0 : ℝ) < 1) basis hseed
  obtain ⟨frame', hframe0', hframeDiff', hframePar', hframeON'⟩ :=
    exists_parallel_frame (I := I') g' γ' (N := 2) (by norm_num) hγ2'
      (by norm_num : (0 : ℝ) < 1) (fun a => i (basis a)) hseed'
  have hVdiff : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t := by
    intro t _
    have h :=
      velocityField_chartRep_differentiableAt (I := I) Fvar hFvar t
    rw [hcentral] at h
    simpa only [V] using h
  have hVdiff' : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (chartRepAt (I := I') γ' V' t) t := by
    intro t _
    have h :=
      velocityField_chartRep_differentiableAt (I := I') Fvar' hFvar' t
    rw [hcentral'] at h
    simpa only [V'] using h
  have hVpar : ∀ t ∈ Icc (0 : ℝ) 1,
      covDerivAlong (I := I) g γ V t = 0 := by
    intro t _
    apply covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
      (I := I) g γ t
      (hγ.contMDiffAt.of_le (by norm_num))
    simpa only [γ] using
      intrinsicGeodesic_isGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u) t
  have hVpar' : ∀ t ∈ Icc (0 : ℝ) 1,
      covDerivAlong (I := I') g' γ' V' t = 0 := by
    intro t _
    apply covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
      (I := I') g' γ' t
      (hγ'.contMDiffAt.of_le (by norm_num))
    simpa only [γ'] using
      intrinsicGeodesic_isGeodesic (I := I') g' hEnorm' p'
        (show TangentSpace I' p' from i u) t
  have hV0 : (V 0 : E) = u := by
    simpa only [V, γ] using
      intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p
        (show TangentSpace I p from u)
  have hV0' : (V' 0 : E) = i u := by
    simpa only [V', γ'] using
      intrinsicGeodesic_mfderiv_zero (I := I') g' hEnorm' p'
        (show TangentSpace I' p' from i u)
  have hvelCoord : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a,
      g.inner (γ t) (frame a t) (V t) = g.inner p (basis a) u := by
    intro t ht a
    have hconst :=
      parallel_transport_preserves_inner_product (I := I) g γ
        (N := 2) (by norm_num) hγ2
        (frame a) V (hframeDiff a) hVdiff (hframePar a) hVpar t ht
    rw [hframe0 a, hγ0] at hconst
    simpa only [hV0] using hconst
  have hvelCoord' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a,
      g'.inner (γ' t) (frame' a t) (V' t) =
        g.inner p (basis a) u := by
    intro t ht a
    have hconst :=
      parallel_transport_preserves_inner_product (I := I') g' γ'
        (N := 2) (by norm_num) hγ2'
        (frame' a) V' (hframeDiff' a) hVdiff' (hframePar' a) hVpar' t ht
    rw [hframe0' a, hγ0'] at hconst
    rw [show V' 0 = i u from hV0'] at hconst
    exact hconst.trans (hi (basis a) u)
  have hspeed : ∀ t : ℝ,
      g.inner (γ t) (V t) (V t) = g.inner p u u := by
    intro t
    change g.inner
        (intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u) t)
        (mfderiv 𝓘(ℝ, ℝ) I
          (intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u)) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u)) t (1 : ℝ)) =
      g.inner p (show TangentSpace I p from u)
        (show TangentSpace I p from u)
    exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p
      (show TangentSpace I p from u) t
  have hspeed' : ∀ t : ℝ,
      g'.inner (γ' t) (V' t) (V' t) = g.inner p u u := by
    intro t
    have hs :=
      intrinsicGeodesic_speedSq_eq (I := I') g' hEnorm' p'
        (show TangentSpace I' p' from i u) t
    change g'.inner
        (intrinsicGeodesic (I := I') g' hEnorm' p'
          (show TangentSpace I' p' from i u) t)
        (mfderiv 𝓘(ℝ, ℝ) I'
          (intrinsicGeodesic (I := I') g' hEnorm' p'
            (show TangentSpace I' p' from i u)) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I'
          (intrinsicGeodesic (I := I') g' hEnorm' p'
            (show TangentSpace I' p' from i u)) t (1 : ℝ)) =
      g.inner p (show TangentSpace I p from u)
        (show TangentSpace I p from u)
    exact hs.trans (hi u u)
  let a0 : Fin (Module.finrank ℝ (TangentSpace I p)) →
      Fin (Module.finrank ℝ (TangentSpace I p)) → ℝ := fun a b =>
    κ * (g.inner p u u * (if a = b then 1 else 0) -
      g.inner p (basis b) u * g.inner p (basis a) u)
  have hcoef : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a b,
      g.inner (γ t) (frame a t)
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
              (γ t))
            (frame b t) (V t) (V t))
        = a0 a b := by
    intro t ht a b
    rw [hR]
    simp only [map_sub, map_smul, smul_eq_mul]
    rw [hspeed t, hframeON t ht a b, hvelCoord t ht b, hvelCoord t ht a]
  have hcoef' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a b,
      g'.inner (γ' t) (frame' a t)
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I') g')
              (γ' t))
            (frame' b t) (V' t) (V' t))
        = a0 a b := by
    intro t ht a b
    rw [hR']
    simp only [map_sub, map_smul, smul_eq_mul]
    rw [hspeed' t, hframeON' t ht a b, hvelCoord' t ht b, hvelCoord' t ht a]
  let C : ℝ := ∑ a, ∑ b, |a0 a b|
  have hC : 0 ≤ C :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a b,
      |g.inner (γ t) (frame a t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (γ t))
          (frame b t) (V t) (V t))| ≤ C := by
    intro t ht a b
    rw [hcoef t ht a b]
    calc
      |a0 a b| ≤ ∑ b', |a0 a b'| :=
        Finset.single_le_sum
          (s := Finset.univ)
          (f := fun b' => |a0 a b'|)
          (fun b' _ => abs_nonneg (a0 a b'))
          (Finset.mem_univ b)
      _ ≤ ∑ a', ∑ b', |a0 a' b'| :=
        Finset.single_le_sum
          (s := Finset.univ)
          (f := fun a' => ∑ b', |a0 a' b'|)
          (fun a' _ => Finset.sum_nonneg fun b' _ => abs_nonneg (a0 a' b'))
          (Finset.mem_univ a)
      _ = C := rfl
  have hYdiff : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (chartRepAt (I := I) γ Y t) t := by
    intro t _
    have h :=
      variationField_chartRep_differentiableAt (I := I) Fvar hFvar t
    rw [hcentral] at h
    change DifferentiableAt ℝ (chartRepAt (I := I) γ Y t) t at h
    exact h
  have hYdiff' : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (chartRepAt (I := I') γ' Y' t) t := by
    intro t _
    have h :=
      variationField_chartRep_differentiableAt (I := I') Fvar' hFvar' t
    rw [hcentral'] at h
    change DifferentiableAt ℝ (chartRepAt (I := I') γ' Y' t) t at h
    exact h
  have hDYdiff : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ Y s) t) t := by
    intro t _
    have h := variationField_covDeriv_chartRep_differentiableAt
      (I := I) g Fvar hFvar t
    rw [hcentral] at h
    change DifferentiableAt ℝ (chartRepAt (I := I) γ
      (fun s => covDerivAlong (I := I) g γ Y s) t) t at h
    exact h
  have hDYdiff' : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (chartRepAt (I := I') γ'
        (fun s => covDerivAlong (I := I') g' γ' Y' s) t) t := by
    intro t _
    have h := variationField_covDeriv_chartRep_differentiableAt
      (I := I') g' Fvar' hFvar' t
    rw [hcentral'] at h
    change DifferentiableAt ℝ (chartRepAt (I := I') γ'
      (fun s => covDerivAlong (I := I') g' γ' Y' s) t) t at h
    exact h
  have hJ : ∀ t ∈ Icc (0 : ℝ) 1, IsJacobiAt (I := I) g γ Y t := by
    intro t _
    simpa only [γ, Y, Fvar, zero_smul, add_zero] using
      intrinsic_jacobi (I := I) g hEnorm p u w t
  have hJ' : ∀ t ∈ Icc (0 : ℝ) 1, IsJacobiAt (I := I') g' γ' Y' t := by
    intro t _
    simpa only [γ', Y', Fvar', zero_smul, add_zero] using
      intrinsic_jacobi (I := I') g' hEnorm' p' (i u) (i w) t
  have hY0 : Y 0 = 0 := by
    have hconst : (fun s : ℝ => Fvar s 0) = fun _ : ℝ => p := by
      funext s
      exact intrinsicGeodesic_zero (I := I) g hEnorm p
        (show TangentSpace I p from u + s • w)
    simp only [Y]
    rw [hconst, mfderiv_const]
    rfl
  have hY0' : Y' 0 = 0 := by
    have hconst : (fun s : ℝ => Fvar' s 0) = fun _ : ℝ => p' := by
      funext s
      exact intrinsicGeodesic_zero (I := I') g' hEnorm' p'
        (show TangentSpace I' p' from i u + s • i w)
    simp only [Y']
    rw [hconst, mfderiv_const]
    rfl
  have hD0 : (covDerivAlong (I := I) g γ Y 0 : E) = w := by
    simpa only [γ, Y, Fvar, zero_smul, add_zero] using
      intrinsic_jacobi_d0 (I := I) g hEnorm p u w
  have hD0' : (covDerivAlong (I := I') g' γ' Y' 0 : E) = i w := by
    simpa only [γ', Y', Fvar', zero_smul, add_zero] using
      intrinsic_jacobi_d0 (I := I') g' hEnorm' p' (i u) (i w)
  have hcoord : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a,
      g.inner (γ t) (frame a t) (Y t) =
        g'.inner (γ' t) (frame' a t) (Y' t) := by
    apply jacobi_coord_xfer (I := I) (I' := I') (n := (8 : ℕ))
      (by norm_num) g γ g' γ' frame frame' Y Y' hC
      (fun t _ => hγ.contMDiffAt) (fun t _ => hγ'.contMDiffAt)
      hframeDiff hframeDiff' hframePar hframePar' hframeON hframeON'
      (fun _ _ => by rw [Fintype.card_fin]; rfl)
      (fun _ _ => by rw [Fintype.card_fin]; rfl)
      hYdiff hYdiff' hDYdiff hDYdiff' hJ hJ'
      (fun t ht a b => (hcoef t ht a b).trans (hcoef' t ht a b).symm)
      hCbound
    · intro a
      rw [hY0, hY0']
      simp
    · intro a
      rw [show covDerivAlong (I := I) g γ Y 0 = w from hD0,
        show covDerivAlong (I := I') g' γ' Y' 0 = i w from hD0',
        hframe0 a, hframe0' a, hγ0, hγ0']
      with_unfolding_all
        exact (hi (basis a) w).symm
  have hnormY :
      g'.inner (γ' 1) (Y' 1) (Y' 1) =
        g.inner (γ 1) (Y 1) (Y 1) := by
    rw [inner_self_eq_sum_sq (I := I') g' (γ' 1)
        (by rw [Fintype.card_fin]; rfl)
        (fun a => frame' a 1) (hframeON' 1 (by norm_num)),
      inner_self_eq_sum_sq (I := I) g (γ 1)
        (by rw [Fintype.card_fin]; rfl)
        (fun a => frame a 1) (hframeON 1 (by norm_num))]
    exact Finset.sum_congr rfl fun a _ => by
      rw [hcoord 1 (by norm_num) a]
  have hYone := intrinsic_jacobi_one (I := I) g hEnorm p u w
  have hYone' :=
    intrinsic_jacobi_one (I := I') g' hEnorm' p' (i u) (i w)
  dsimp only [Y, Y', Fvar, Fvar'] at hnormY
  rw [hYone, hYone'] at hnormY
  dsimp only [γ, γ', expMapIntrinsic] at hnormY
  exact hnormY

theorem cartanMap_sq_smul (κ : ℝ)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (g' : SmoothRiemannianMetric I' M')
    (hEnorm' : ∀ (x : M') (w : TangentSpace I' x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g'.inner x w w)))
    {c : M} (B : DiagonalInverseBranch (I := I) g hEnorm c) (p : M)
    (p' : M') (i : E ≃L[ℝ] E)
    (hi : ∀ a b : E, g'.inner p' (i a) (i b) = g.inner p a b)
    (hR : ∀ (x : M) (X Y Z : TangentSpace I x),
      (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) x)
        X Y Z =
          κ • (g.inner x Y Z • X - g.inner x X Z • Y))
    (hR' : ∀ (x : M') (X Y Z : TangentSpace I' x),
      (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I') g') x)
        X Y Z =
          κ • (g'.inner x Y Z • X - g'.inner x X Z • Y))
    {x : M} (hx : (p, x) ∈ B.dom) (Y : TangentSpace I x) :
    g'.inner (cartanMap B p g' hEnorm' p' i x)
        (mfderiv I I' (cartanMap B p g' hEnorm' p' i) x Y)
        (mfderiv I I' (cartanMap B p g' hEnorm' p' i) x Y) =
      g.inner x Y Y := by
  let invf : M → E := fun z => ((B.inv (p, z)).snd : E)
  let midf : M → E := (fun z : E => i z) ∘ invf
  let expf : E → M := fun u =>
    expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from u)
  let expf' : E → M' := fun u =>
    expMapIntrinsic (I := I') g' hEnorm' p'
      (show TangentSpace I' p' from u)
  let u : E := invf x
  let w : E := mfderiv I 𝓘(ℝ, E) invf x Y
  let U : Set M := (fun z : M => (p, z)) ⁻¹' B.dom
  have hUopen : IsOpen U := by
    exact B.hom.open_target.preimage (continuous_const.prodMk continuous_id)
  have hxU : x ∈ U := hx
  have hinvOn : ContMDiffOn I 𝓘(ℝ, E) ∞ invf U := by
    simpa only [invf, U] using
      B.inv_fiberCoordinates_contMDiffOn_at_fixed_base (S := U) (fun z hz => hz)
  have hinv : MDifferentiableAt I 𝓘(ℝ, E) invf x :=
    (hinvOn.contMDiffAt (hUopen.mem_nhds hxU)).mdifferentiableAt
      (by simp)
  have hiDiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun z : E => i z) (invf x) :=
    i.mdifferentiableAt
  have hmid : MDifferentiableAt I 𝓘(ℝ, E) midf x := by
    exact hiDiff.comp x hinv
  have hexpInf : ContMDiffAt 𝓘(ℝ, E) I' ∞ expf' (midf x) :=
    (intrinsicFiber_smooth (I := I') g' hEnorm' p').contMDiffAt
  have hexp' : MDifferentiableAt 𝓘(ℝ, E) I' expf' (midf x) :=
    hexpInf.mdifferentiableAt (by simp)
  have hmidDeriv :
      mfderiv I 𝓘(ℝ, E) midf x Y = i w := by
    have hchain :=
      mfderiv_comp_apply
        (I := I) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E))
        (g := fun z : E => i z) (f := invf) (x := x)
        hiDiff hinv Y
    rw [ContinuousLinearEquiv.mfderiv_eq] at hchain
    change mfderiv I 𝓘(ℝ, E) ((fun z : E => i z) ∘ invf) x Y =
      i.toContinuousLinearMap (mfderiv I 𝓘(ℝ, E) invf x Y)
    exact hchain
  have hmapDeriv :
      mfderiv I I' (cartanMap B p g' hEnorm' p' i) x Y =
        mfderiv 𝓘(ℝ, E) I' expf' (i u) (i w) := by
    have hchain :=
      mfderiv_comp_apply
        (I := I) (I' := 𝓘(ℝ, E)) (I'' := I')
        (g := expf') (f := midf) (x := x)
        hexp' hmid Y
    rw [hmidDeriv] at hchain
    have hfun : cartanMap B p g' hEnorm' p' i = expf' ∘ midf := by
      funext z
      rfl
    rw [hfun]
    have hmidU : midf x = i u := by
      rfl
    rw [hmidU] at hchain
    exact hchain
  have htransfer :=
    expDiff_sq_xfer_smul (I := I) (I' := I') κ
      g hEnorm g' hEnorm' p p' u w i hi hR hR'
  have hbase : expf u = x := by
    simpa only [expf, invf, u] using B.exp_eq hx
  have hright :
      mfderiv 𝓘(ℝ, E) I expf u w = Y := by
    have hx' : x ∈ (B.fixed p).dom := by
      simpa only [DiagonalInverseBranch.fixed_target] using hx
    have h := exp_inv_mfderiv (I := I) (B.fixed p) hx' Y
    have hinvFun : (B.fixed p).inv = invf := by
      rfl
    rw [hinvFun] at h
    have hexp :
        (fun z : E =>
          expMapIntrinsic (I := I) g hEnorm p
            ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm z)) =
          expf := by
      funext z
      simp only [expf, tangentSpaceModelContinuousLinearEquiv_symm_apply]
    dsimp only at h
    rw [hexp] at h
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h
    change
      tangentSpaceModelContinuousLinearEquiv (I := I) (expf u)
          (mfderiv 𝓘(ℝ, E) I expf u w) =
        tangentSpaceModelContinuousLinearEquiv (I := I) x Y at h
    rw [hbase] at h
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) x).injective
    exact h
  have htransfer' :
      g'.inner (expf' (i u))
          (mfderiv 𝓘(ℝ, E) I' expf' (i u) (i w))
          (mfderiv 𝓘(ℝ, E) I' expf' (i u) (i w)) =
        g.inner (expf u)
          (mfderiv 𝓘(ℝ, E) I expf u w)
          (mfderiv 𝓘(ℝ, E) I expf u w) := by
    simpa only [expf, expf'] using htransfer
  have hsource :
      g.inner (expf u)
          (mfderiv 𝓘(ℝ, E) I expf u w)
          (mfderiv 𝓘(ℝ, E) I expf u w) =
        g.inner x Y Y := by
    rw [hbase] at hright ⊢
    rw [hright]
  rw [hmapDeriv]
  change
    g'.inner (expf' (i u))
        (mfderiv 𝓘(ℝ, E) I' expf' (i u) (i w))
        (mfderiv 𝓘(ℝ, E) I' expf' (i u) (i w)) =
      g.inner x Y Y
  exact htransfer'.trans hsource

theorem cartanMap_inner_smul (κ : ℝ)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (g' : SmoothRiemannianMetric I' M')
    (hEnorm' : ∀ (x : M') (w : TangentSpace I' x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g'.inner x w w)))
    {c : M} (B : DiagonalInverseBranch (I := I) g hEnorm c) (p : M)
    (p' : M') (i : E ≃L[ℝ] E)
    (hi : ∀ a b : E, g'.inner p' (i a) (i b) = g.inner p a b)
    (hR : ∀ (x : M) (X Y Z : TangentSpace I x),
      (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) x)
        X Y Z =
          κ • (g.inner x Y Z • X - g.inner x X Z • Y))
    (hR' : ∀ (x : M') (X Y Z : TangentSpace I' x),
      (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I') g') x)
        X Y Z =
          κ • (g'.inner x Y Z • X - g'.inner x X Z • Y))
    {x : M} (hx : (p, x) ∈ B.dom)
    (Y Z : TangentSpace I x) :
    g'.inner (cartanMap B p g' hEnorm' p' i x)
        (mfderiv I I' (cartanMap B p g' hEnorm' p' i) x Y)
        (mfderiv I I' (cartanMap B p g' hEnorm' p' i) x Z) =
      g.inner x Y Z := by
  exact inner_eq_of_diag g g' x (cartanMap B p g' hEnorm' p' i x)
    (mfderiv I I' (cartanMap B p g' hEnorm' p' i) x)
    (cartanMap_sq_smul κ g hEnorm g' hEnorm' B p p' i hi hR hR' hx) Y Z

theorem cartanPartialDiffeomorph_inner_smul (κ : ℝ)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (g' : SmoothRiemannianMetric I' M')
    (hEnorm' : ∀ (x : M') (w : TangentSpace I' x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g'.inner x w w)))
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p)
    {p' : M'} (B' : DiagonalInverseBranch (I := I') g' hEnorm' p')
    (i : E ≃L[ℝ] E)
    (hi : ∀ a b : E, g'.inner p' (i a) (i b) = g.inner p a b)
    (hR : ∀ (x : M) (X Y Z : TangentSpace I x),
      (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) x)
        X Y Z =
          κ • (g.inner x Y Z • X - g.inner x X Z • Y))
    (hR' : ∀ (x : M') (X Y Z : TangentSpace I' x),
      (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I') g') x)
        X Y Z =
          κ • (g'.inner x Y Z • X - g'.inner x X Z • Y))
    {x : M} (hx : x ∈ (cartanPartialDiffeomorph B B' i).source)
    (Y Z : TangentSpace I x) :
    g'.inner (cartanPartialDiffeomorph B B' i x)
        (mfderiv I I' (cartanPartialDiffeomorph B B' i) x Y)
        (mfderiv I I' (cartanPartialDiffeomorph B B' i) x Z) =
      g.inner x Y Z := by
  have hdom : (p, x) ∈ B.dom := by
    have hx' := hx.1.1
    change (p, x) ∈ B.dom at hx'
    exact hx'
  rw [cartanPartialDiffeomorph_coe B B' i]
  exact cartanMap_inner_smul κ g hEnorm g' hEnorm' B p p' i hi hR hR'
    hdom Y Z

end Cartan

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'} [J.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem modelAtlas_of_riemannOp_eq_smul [Nonempty N] (κ : ℝ)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (hg : RiemannianMetricComplete g) (hh : RiemannianMetricComplete h)
    (hRg : ∀ (x : M) (X Y Z : TangentSpace I x),
      riemannOp (LeviCivita (I := I) g) x X Y Z =
        κ • (g.inner x Y Z • X - g.inner x X Z • Y))
    (hRh : ∀ (y : N) (X Y Z : TangentSpace J y),
      riemannOp (LeviCivita (I := J) h) y X Y Z =
        κ • (h.inner y Y Z • X - h.inner y X Z • Y)) :
    ModelAtlas g h := by
  intro x
  let q : N := Classical.arbitrary N
  obtain ⟨e, he⟩ := Tensor0SBundle.MetricFiberData.exists_metric_linearEquiv
    (Tensor0SBundle.tangentMetricData (I := J) h q).metric
    (Tensor0SBundle.tangentMetricData (I := I) g x).metric rfl
  let i : E ≃L[ℝ] E := LinearEquiv.toContinuousLinearEquiv (e : E ≃ₗ[ℝ] E)
  have hi : ∀ a b : E, g.inner x (i a) (i b) = h.inner q a b := fun a b => he a b
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hg.complete
  let : IsManifold J 1 N :=
    IsManifold.of_le (I := J) (M := N) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace J N
  let : T3Space N := inferInstance
  let : RiemannianBundle (fun y : N => TangentSpace J y) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : N => TangentSpace J y) :=
    ⟨⟨h.inner, h.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric J N
  let : CompleteSpace N := hh.complete
  have hEg : IsMetricNorm (I := I) (M := M) g := fun z v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g z v
  have hEh : IsMetricNorm (I := J) (M := N) h := fun z v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := J) h z v
  let B := standardDiagonalInverseBranch (I := J) h hEh q
  let B' := standardDiagonalInverseBranch (I := I) g hEg x
  refine ⟨cartanPartialDiffeomorph B B' i, ?_, ?_⟩
  · have hq := cartanPartialDiffeomorph_center_mem_source B B' i
    have hcenter : cartanPartialDiffeomorph B B' i q = x := by
      have hc : cartanPartialDiffeomorph B B' i q = cartanMap B q g hEg x i q :=
        congrFun (cartanPartialDiffeomorph_coe B B' i) q
      rw [hc]
      change expMapIntrinsic (I := I) g hEg x
        (show TangentSpace I x from i (B.fixedBasePartialDiffeomorph.symm q)) = x
      rw [B.fixedBasePartialDiffeomorph_symm_center, map_zero]
      exact expMapIntrinsic_zero (I := I) g hEg x
    have hmem := (cartanPartialDiffeomorph B B' i).map_source hq
    rwa [hcenter] at hmem
  · intro y hy v w
    exact cartanPartialDiffeomorph_inner_smul κ h hEh g hEg B B' i hi hRh hRg hy v w

end Assembly

section Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def HasConstantSectionalCurvature (g : SmoothRiemannianMetric I M) (κ : ℝ) : Prop :=
  ∀ (p : M) (v w : TangentSpace I p),
    LinearIndependent ℝ ![v, w] → Riemannian.sectionalCurvature g p v w = κ

omit [FiniteDimensional ℝ E] in
private theorem denominator_eq_zero_of_not_linearIndependent
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (hdep : ¬ LinearIndependent ℝ ![v, w]) :
    g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 = 0 := by
  have hnonneg : 0 ≤ g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 := by
    simpa only [Riemannian.sectionalCurvatureDenominator_def]
      using Riemannian.sectionalCurvatureDenominator_nonneg g x v w
  have hnotpos : ¬ 0 < g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 := by
    intro hpos
    exact hdep (Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
      g x v w (by
        simpa only [Riemannian.sectionalCurvatureDenominator_def] using hpos))
  exact le_antisymm (le_of_not_gt hnotpos) hnonneg

theorem hasConstantSectionalCurvature_iff [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (κ : ℝ) :
    HasConstantSectionalCurvature g κ ↔
      ∀ (x : M) (X Y : TangentSpace I x),
        metricRm04StandardAt g x X Y Y X =
          κ * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  constructor
  · intro hsec x v w
    by_cases hLI : LinearIndependent ℝ ![v, w]
    · have hden : 0 < g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 := by
        simpa only [Riemannian.sectionalCurvatureDenominator_def]
          using Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent g x v w hLI
      have hcurv := hsec x v w hLI
      rw [Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div] at hcurv
      field_simp [ne_of_gt hden] at hcurv
      linarith
    · rw [metricRm04StandardAt_eq_zero_of_not_linearIndependent g x v w hLI]
      have hden := denominator_eq_zero_of_not_linearIndependent g x v w hLI
      have hden' : g.inner x v v * g.inner x w w -
          g.inner x v w * g.inner x v w = 0 := by
        simpa only [pow_two] using hden
      rw [hden', mul_zero]
  · intro hsec x v w hLI
    have hden : 0 < g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 := by
      simpa only [Riemannian.sectionalCurvatureDenominator_def]
        using Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent g x v w hLI
    rw [Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div, hsec x v w]
    field_simp [ne_of_gt hden]

theorem riemannOp_eq_smul_of_hasConstantSectionalCurvature [I.Boundaryless] [T2Space M]
    {g : SmoothRiemannianMetric I M} {κ : ℝ} (hg : HasConstantSectionalCurvature g κ)
    (x : M) (X Y Z : TangentSpace I x) :
    riemannOp (LeviCivita (I := I) g) x X Y Z =
      κ • (g.inner x Y Z • X - g.inner x X Z • Y) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by decide)
  exact riemannOp_of_rm g x κ
    (metricRm_of_sec g x κ ((hasConstantSectionalCurvature_iff g κ).mp hg x)) X Y Z

theorem hasConstantSectionalCurvature_of_modelAtlas [I.Boundaryless] [T2Space M]
    {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N} {κ : ℝ}
    (hh : HasConstantSectionalCurvature h κ) (hA : ModelAtlas g h) :
    HasConstantSectionalCurvature g κ := by
  rw [hasConstantSectionalCurvature_iff] at hh ⊢
  intro x X Y
  obtain ⟨e, hx, he⟩ := hA x
  obtain ⟨y, hy, rfl⟩ : ∃ y ∈ e.source, e y = x :=
    ⟨e.symm x, e.map_target hx, e.right_inv hx⟩
  let L := (PartialDiffeomorph.isLocalDiffeomorphAt J I ∞ e hy).mfderivToContinuousLinearEquiv
    (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  obtain ⟨a, rfl⟩ : ∃ a : TangentSpace J y, mfderiv J I e y a = X :=
    ⟨L.symm X, L.apply_symm_apply X⟩
  obtain ⟨b, rfl⟩ : ∃ b : TangentSpace J y, mfderiv J I e y b = Y :=
    ⟨L.symm Y, L.apply_symm_apply Y⟩
  let U : TopologicalSpace.Opens N := ⟨e.source, e.open_source⟩
  have hmet : ∀ z : U, ∀ v w : TangentSpace J z,
      h.inner z.val v w = g.inner (e z.val) (mfderiv J I e z.val v)
        (mfderiv J I e z.val w) := fun z v w => (he z.val z.property v w).symm
  rw [← metricRm04StandardAt_eq_of_partialDiffeomorph_restriction e U subset_rfl h g hmet
      ⟨y, hy⟩ a b b a, hh y a b, he y hy a a, he y hy b b, he y hy a b]

end Curvature

section LineWarped

private def lineMetric : SmoothRiemannianMetric (𝓡 1) (EuclideanSpace ℝ (Fin 1)) :=
  euclideanMetric (E := EuclideanSpace ℝ (Fin 1))

private theorem lineMetric_inner (p : EuclideanSpace ℝ (Fin 1))
    (v w : EuclideanSpace ℝ (Fin 1)) : lineMetric.inner p v w = v 0 * w 0 := by
  unfold lineMetric
  erw [euclideanMetric_inner]
  change inner ℝ v w = v 0 * w 0
  simp [PiLp.inner_apply, mul_comm]

private def lineUnit : Cₛ^∞⟮𝓡 1; EuclideanSpace ℝ (Fin 1),
    (TangentSpace (𝓡 1) : EuclideanSpace ℝ (Fin 1) → Type _)⟯ where
  toFun _ := WithLp.toLp 2 (fun _ => (1 : ℝ))
  contMDiff_toFun := by
    intro x
    erw [contMDiffAt_section]
    simp only [trivializationAt_model_space_apply]
    exact contMDiffAt_const

private theorem lineUnit_parallel (p : EuclideanSpace ℝ (Fin 1))
    (v : TangentSpace (𝓡 1) p) : (LeviCivita lineMetric) lineUnit p v = 0 := by
  have h := (leviCivitaConnectionOfMetric_isMetricCompatible lineMetric).mvfderiv_inner v
    lineUnit.mdifferentiableAt lineUnit.mdifferentiableAt
  have he : (fun x => lineMetric.inner x (lineUnit x) (lineUnit x)) =
      fun _ => (1 : ℝ) := by
    funext x
    erw [lineMetric_inner]
    change (1 : ℝ) * 1 = 1
    exact mul_one 1
  rw [he, mvfderiv_const] at h
  erw [lineMetric_inner, lineMetric_inner] at h
  let a : EuclideanSpace ℝ (Fin 1) := (LeviCivita lineMetric) lineUnit p v
  change (0 : ℝ) = a 0 * 1 + 1 * a 0 at h
  have hz : a 0 = 0 := by linarith
  change a = 0
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa only [hi, PiLp.zero_apply] using hz

open DifferentialGeometry.Geometry.Operator

private def lineDepth (p : EuclideanSpace ℝ (Fin 1)) : ℝ := p 0

private theorem lineDepth_smooth :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ lineDepth := by
  change ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞
    (fun q : EuclideanSpace ℝ (Fin 1) => PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0 q)
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).contDiff.contMDiff

private theorem lineDepth_mfderiv (p : EuclideanSpace ℝ (Fin 1)) :
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ) lineDepth p =
      PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0 := by
  change mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun q : EuclideanSpace ℝ (Fin 1) =>
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0 q) p = _
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).mfderiv_eq

private theorem line_comp_depth_deriv
    {φ : ℝ → ℝ} {d : ℝ} (p : EuclideanSpace ℝ (Fin 1))
    (hφ : HasDerivAt φ d (lineDepth p)) (v : EuclideanSpace ℝ (Fin 1)) :
    mvfderiv (𝓡 1) (fun q => φ (lineDepth q)) p v = d * v 0 := by
  have hc := mvfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 1)
    (f := lineDepth) (g := φ) p hφ.differentiableAt.mdifferentiableAt
    (lineDepth_smooth.mdifferentiable (by simp) p) v
  erw [lineDepth_mfderiv] at hc
  change mvfderiv (𝓡 1) (fun q => φ (lineDepth q)) p v =
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ (lineDepth p) (v 0) at hc
  erw [mfderiv_eq_fderiv, hφ.hasFDerivAt.fderiv] at hc
  change mvfderiv (𝓡 1) (fun q => φ (lineDepth q)) p v = v 0 * d at hc
  exact hc.trans (mul_comm _ _)

private def lineExp (κ : ℝ) (p : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  Real.exp (-κ * lineDepth p)

private theorem lineExp_smooth (κ : ℝ) :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (lineExp κ) :=
  Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul lineDepth_smooth)

private theorem lineExp_deriv (κ : ℝ) (p : EuclideanSpace ℝ (Fin 1))
    (v : EuclideanSpace ℝ (Fin 1)) :
    mvfderiv (𝓡 1) (lineExp κ) p v =
      (-κ * lineExp κ p) * v 0 := by
  have hd : HasDerivAt (fun s : ℝ => Real.exp (-κ * s))
      (-κ * Real.exp (-κ * lineDepth p)) (lineDepth p) := by
    simpa only [id_eq, mul_one, mul_comm] using
      ((hasDerivAt_id (lineDepth p)).const_mul (-κ)).exp
  exact line_comp_depth_deriv p hd v

private theorem lineExp_grad (κ : ℝ) (p : EuclideanSpace ℝ (Fin 1)) :
    gradFun lineMetric (lineExp κ) p =
      (-κ * lineExp κ p) • lineUnit p := by
  apply DifferentialGeometry.Geometry.Connection.SmoothRiemannianMetric.eq_of_inner_eq
    lineMetric
  intro w
  rw [gradFun_metricDual_mvfderiv]
  erw [lineExp_deriv, lineMetric_inner]
  let w₀ : EuclideanSpace ℝ (Fin 1) := w
  change (-κ * lineExp κ p) * w₀ 0 =
    ((-κ * lineExp κ p) * 1) * w₀ 0
  rw [mul_one]

private theorem lineExp_coefficient_deriv (κ : ℝ) (p : EuclideanSpace ℝ (Fin 1))
    (v : EuclideanSpace ℝ (Fin 1)) :
    mvfderiv (𝓡 1) (fun q => -κ * lineExp κ q) p v =
      (κ ^ 2 * lineExp κ p) * v 0 := by
  have hd : HasDerivAt (fun s : ℝ => -κ * Real.exp (-κ * s))
      (-κ * (Real.exp (-κ * lineDepth p) * (-κ))) (lineDepth p) := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id (lineDepth p)).const_mul (-κ)).exp).const_mul (-κ)
  have hh := line_comp_depth_deriv p hd v
  change mvfderiv (𝓡 1) (fun q => -κ * lineExp κ q) p v =
    (-κ * (lineExp κ p * (-κ))) * v 0 at hh
  rw [hh]
  ring

private theorem lineExp_cov_grad (κ : ℝ) (p : EuclideanSpace ℝ (Fin 1))
    (v : EuclideanSpace ℝ (Fin 1)) :
    (LeviCivita lineMetric) (gradFun lineMetric (lineExp κ)) p v =
      (κ ^ 2 * Real.exp (-κ * p 0) * v 0) • lineUnit p := by
  let a : EuclideanSpace ℝ (Fin 1) → ℝ := fun q => -κ * lineExp κ q
  let σ : (q : EuclideanSpace ℝ (Fin 1)) → TangentSpace (𝓡 1) q :=
    fun q => lineUnit q
  let C : CovariantDerivative (𝓡 1) (EuclideanSpace ℝ (Fin 1))
      (TangentSpace (𝓡 1) : EuclideanSpace ℝ (Fin 1) → Type _) :=
    LeviCivita lineMetric
  let v₀ : TangentSpace (𝓡 1) p := v
  let b : ℝ := κ ^ 2 * lineExp κ p * v 0
  have hg : gradFun lineMetric (lineExp κ) = a • σ :=
    funext (lineExp_grad κ)
  have hcoeff : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) a p :=
    (contMDiff_const.mul (lineExp_smooth κ)).mdifferentiable (by simp) p
  have hσ : MDifferentiableAt (𝓡 1) (𝓡 1).tangent (T% σ) p :=
    lineUnit.mdifferentiableAt
  have hleib : C (a • σ) p = a p • C σ p +
      (mvfderiv (𝓡 1) a p).smulRight (σ p) :=
    C.isCovariantDerivativeOnUniv.leibniz hσ hcoeff
  have hv := congrArg
    (fun L : TangentSpace (𝓡 1) p →L[ℝ] TangentSpace (𝓡 1) p => L v₀) hleib
  change C (a • σ) p v₀ =
    a p • (C σ p v₀) + (mvfderiv (𝓡 1) a p v₀) • σ p at hv
  have hparallel : C σ p v₀ = 0 := lineUnit_parallel p v₀
  have hda : mvfderiv (𝓡 1) a p v₀ = b :=
    lineExp_coefficient_deriv κ p v
  have hr := congrArg₂
    (fun (w : TangentSpace (𝓡 1) p) (c : ℝ) => a p • w + c • σ p)
    hparallel hda
  have hz : a p • (0 : TangentSpace (𝓡 1) p) + b • σ p = b • σ p := by
    rw [smul_zero, zero_add]
  have htransport := congrArg
    (fun X : (q : EuclideanSpace ℝ (Fin 1)) → TangentSpace (𝓡 1) q => C X p v₀) hg
  exact htransport.trans (hv.trans (hr.trans hz))

open DifferentialGeometry.Geometry.Curvature

private theorem lineExp_mixed_curvature
    {F K N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
    (h : SmoothRiemannianMetric J N) (κ : ℝ)
    (p : EuclideanSpace ℝ (Fin 1) × N) (u z : EuclideanSpace ℝ (Fin 1))
    (v w : TangentSpace J p.2) :
    metricRm04StandardAt
      (lineMetric.warpedProduct h (lineExp κ) (lineExp_smooth κ)
        (fun q => Real.exp_pos (-κ * lineDepth q)))
      p (u, 0) (0, v) (0, w) (z, 0) =
      -κ ^ 2 * Real.exp (-2 * κ * p.1 0) * u 0 * z 0 * h.inner p.2 v w := by
  have hm := metricRm04StandardAt_warpedProduct_mixed lineMetric h
    (lineExp κ) (lineExp_smooth κ)
    (fun q => Real.exp_pos (-κ * lineDepth q)) p u z v w
  have hg := lineExp_cov_grad κ p.1 u
  have hp := congrArg
    (fun a : TangentSpace (𝓡 1) p.1 => lineMetric.inner p.1 z a) hg
  have hs : lineMetric.inner p.1 z
      ((κ ^ 2 * Real.exp (-κ * p.1 0) * u 0) • lineUnit p.1) =
      z 0 * (κ ^ 2 * Real.exp (-κ * p.1 0) * u 0) := by
    erw [lineMetric_inner]
    change z 0 * ((κ ^ 2 * Real.exp (-κ * p.1 0) * u 0) * 1) = _
    rw [mul_one]
  have he : Real.exp (-κ * p.1 0) ^ 2 = Real.exp (-2 * κ * p.1 0) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine hm.trans ?_
  rw [hp.trans hs]
  change -(Real.exp (-κ * p.1 0) * h.inner p.2 v w) *
    (z 0 * (κ ^ 2 * Real.exp (-κ * p.1 0) * u 0)) = _
  rw [← he]
  ring

private theorem sectional_split {S : Type*} [AddCommGroup S] [Module ℝ S]
    {R : S → S → S → S → ℝ} (hR : IsAlgCurvForm R)
    (e U V : S) (a b : ℝ)
    (hUVU : R U V U e = 0) (hUVV : R U V V e = 0) :
    R (a • e + U) (b • e + V) (b • e + V) (a • e + U) =
      a ^ 2 * R e V V e - 2 * a * b * R e U V e +
        b ^ 2 * R e U U e + R U V V U := by
  have hs₂ (c : ℝ) (x y z w : S) : R x (c • y) z w = c * R x y z w := by
    rw [hR.anti_first, hR.smul_left, hR.anti_first y x]
    ring
  have hs₃ (c : ℝ) (x y z w : S) : R x y (c • z) w = c * R x y z w := by
    rw [hR.pair_swap, hR.smul_left, hR.pair_swap z w]
  have hs₄ (c : ℝ) (x y z w : S) : R x y z (c • w) = c * R x y z w := by
    rw [hR.anti_last, hs₃, hR.anti_last x y w]
    ring
  have hfirst (x y z : S) : R x x y z = 0 := by
    have hh := hR.anti_first x x y z
    linarith
  have hlast (x y z : S) : R x y z z = 0 := by
    have hh := hR.anti_last x y z z
    linarith
  have hmix : R e V U e = R e U V e := by
    have hh := hR.bianchi e V U e
    have hh' := hR.anti_first U e V e
    rw [hlast] at hh
    linarith
  have h₁ : R e V V U = 0 := by rw [hR.pair_swap, hR.anti_first, hR.anti_last, hUVV]; ring
  have h₂ : R U e V U = 0 := by rw [hR.pair_swap, hR.anti_first, hUVU]; ring
  have h₃ : R U V e U = 0 := by rw [hR.anti_last, hUVU]; ring
  have h₄ : R e V e U = -R e U V e := by rw [hR.anti_last, hmix]
  have h₅ : R U e V e = -R e U V e := hR.anti_first _ _ _ _
  have h₆ : R U e e U = R e U U e := by rw [hR.anti_first, hR.anti_last e U]; ring
  simp only [hR.add_left, hR.add_two, hR.add_three, hR.add_four,
    hR.smul_left, hs₂, hs₃, hs₄, hfirst, hlast,
    hUVV, h₁, h₂, h₃, h₄, h₅, h₆]
  ring

private theorem sectional_zero_four {S : Type*} [AddCommGroup S] [Module ℝ S]
    {R : S → S → S → S → ℝ} (hR : IsAlgCurvForm R) (a b c : S) :
    R a b c 0 = 0 := by
  have hz : R 0 c a b = 0 := by
    simpa only [zero_smul, zero_mul] using hR.smul_left 0 c c a b
  rw [hR.pair_swap, hR.anti_first, hz, neg_zero]

private theorem lineExp_square (κ : ℝ) (p : EuclideanSpace ℝ (Fin 1)) :
    lineExp κ p ^ 2 = Real.exp (-2 * κ * p 0) := by
  change Real.exp (-κ * p 0) ^ 2 = Real.exp (-2 * κ * p 0)
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem lineExp_grad_norm (κ : ℝ) (p : EuclideanSpace ℝ (Fin 1)) :
    lineMetric.inner p (gradFun lineMetric (lineExp κ) p)
      (gradFun lineMetric (lineExp κ) p) =
      κ ^ 2 * Real.exp (-2 * κ * p 0) := by
  erw [lineExp_grad, lineMetric_inner]
  change ((-κ * lineExp κ p) * 1) * ((-κ * lineExp κ p) * 1) = _
  rw [← lineExp_square κ p]
  ring

private theorem exponential_sectional_scalar (κ t a b A B C Q : ℝ) :
    a ^ 2 * (-κ ^ 2 * t * B) - 2 * a * b * (-κ ^ 2 * t * C) +
      b ^ 2 * (-κ ^ 2 * t * A) + t * (Q - κ ^ 2 * t * (A * B - C ^ 2)) =
      t * Q - κ ^ 2 * ((a * a + t * A) * (b * b + t * B) -
        (a * b + t * C) ^ 2) := by ring


variable {F K N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

private abbrev lineWarped (h : SmoothRiemannianMetric J N) (κ : ℝ) :=
  lineMetric.warpedProduct h (lineExp κ) (lineExp_smooth κ)
    (fun q => Real.exp_pos (-κ * lineDepth q))

private theorem lineWarped_triple (h : SmoothRiemannianMetric J N) (κ : ℝ)
    (p : EuclideanSpace ℝ (Fin 1) × N) (a b c : F) :
    metricRm04StandardAt (lineWarped h κ) p
      (0, a) (0, b) (0, c) (lineUnit p.1, 0) = 0 := by
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let Rf : F → F → F → F → ℝ := metricRm04StandardAt h p.2
  have hRf : IsAlgCurvForm Rf :=
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule h p.2)
  have hh := metricRm04StandardAt_warpedProduct_vertical lineMetric h
    (lineExp κ) (lineExp_smooth κ)
    (fun q => Real.exp_pos (-κ * lineDepth q)) p a b c 0 (lineUnit p.1)
  have ha : h.inner p.2 0 a = 0 := by rw [map_zero]; rfl
  have hb : h.inner p.2 0 b = 0 := by rw [map_zero]; rfl
  have hz : metricRm04StandardAt h p.2 a b c 0 = 0 := sectional_zero_four hRf a b c
  erw [hz, ha, hb] at hh
  erw [hh]
  ring

private theorem lineWarped_mixed (h : SmoothRiemannianMetric J N) (κ : ℝ)
    (p : EuclideanSpace ℝ (Fin 1) × N) (a b : F) :
    metricRm04StandardAt (lineWarped h κ) p
      (lineUnit p.1, 0) (0, a) (0, b) (lineUnit p.1, 0) =
      -κ ^ 2 * Real.exp (-2 * κ * p.1 0) * h.inner p.2 a b := by
  have hh := lineExp_mixed_curvature h κ p (lineUnit p.1) (lineUnit p.1) a b
  change metricRm04StandardAt (lineWarped h κ) p
      (lineUnit p.1, 0) (0, a) (0, b) (lineUnit p.1, 0) =
      -κ ^ 2 * Real.exp (-2 * κ * p.1 0) * 1 * 1 * h.inner p.2 a b at hh
  simpa only [mul_one] using hh

private theorem lineWarped_vertical (h : SmoothRiemannianMetric J N) (κ : ℝ)
    (p : EuclideanSpace ℝ (Fin 1) × N) (a b : F) :
    metricRm04StandardAt (lineWarped h κ) p (0, a) (0, b) (0, b) (0, a) =
      Real.exp (-2 * κ * p.1 0) * (metricRm04StandardAt h p.2 a b b a -
        κ ^ 2 * Real.exp (-2 * κ * p.1 0) *
          (h.inner p.2 a a * h.inner p.2 b b - h.inner p.2 a b ^ 2)) := by
  have hh := metricRm04StandardAt_warpedProduct_vertical lineMetric h
    (lineExp κ) (lineExp_smooth κ)
    (fun q => Real.exp_pos (-κ * lineDepth q)) p a b b a 0
  rw [lineExp_square, lineExp_grad_norm] at hh
  exact hh.trans (by ring)

private theorem lineWarped_pair (h : SmoothRiemannianMetric J N) (κ : ℝ)
    (p : EuclideanSpace ℝ (Fin 1) × N) (a b : EuclideanSpace ℝ (Fin 1) × F) :
    (lineWarped h κ).inner p a b = a.1 0 * b.1 0 +
      Real.exp (-2 * κ * p.1 0) * h.inner p.2 a.2 b.2 := by
  erw [SmoothRiemannianMetric.warpedProduct_inner, lineMetric_inner]
  rw [lineExp_square]

omit [FiniteDimensional ℝ F] in
private theorem line_vector_split (p : EuclideanSpace ℝ (Fin 1))
    (a : EuclideanSpace ℝ (Fin 1) × F) :
    a.1 0 • (lineUnit p, (0 : F)) + (0, a.2) = a := by
  apply Prod.ext
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    change a.1 0 * 1 + 0 = a.1 i
    rw [hi, mul_one, add_zero]
  · change a.1 0 • (0 : F) + a.2 = a.2
    rw [smul_zero, zero_add]

private theorem lineWarped_sectional_expansion
    (h : SmoothRiemannianMetric J N) (κ : ℝ) (p : EuclideanSpace ℝ (Fin 1) × N)
    (v w : EuclideanSpace ℝ (Fin 1) × F) :
    metricRm04StandardAt (lineWarped h κ) p v w w v =
      (v.1 0) ^ 2 * (-κ ^ 2 * Real.exp (-2 * κ * p.1 0) * h.inner p.2 w.2 w.2) -
      2 * v.1 0 * w.1 0 * (-κ ^ 2 * Real.exp (-2 * κ * p.1 0) * h.inner p.2 v.2 w.2) +
      (w.1 0) ^ 2 * (-κ ^ 2 * Real.exp (-2 * κ * p.1 0) * h.inner p.2 v.2 v.2) +
      Real.exp (-2 * κ * p.1 0) * (metricRm04StandardAt h p.2 v.2 w.2 w.2 v.2 -
        κ ^ 2 * Real.exp (-2 * κ * p.1 0) *
          (h.inner p.2 v.2 v.2 * h.inner p.2 w.2 w.2 - h.inner p.2 v.2 w.2 ^ 2)) := by
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let R : (EuclideanSpace ℝ (Fin 1) × F) → (EuclideanSpace ℝ (Fin 1) × F) →
      (EuclideanSpace ℝ (Fin 1) × F) → (EuclideanSpace ℝ (Fin 1) × F) → ℝ :=
    metricRm04StandardAt (lineWarped h κ) p
  have hR : IsAlgCurvForm R :=
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (lineWarped h κ) p)
  have hs := sectional_split hR (lineUnit p.1, (0 : F)) (0, v.2) (0, w.2)
    (v.1 0) (w.1 0) (lineWarped_triple h κ p v.2 w.2 v.2)
    (lineWarped_triple h κ p v.2 w.2 w.2)
  erw [line_vector_split p.1 v, line_vector_split p.1 w] at hs
  change R v w w v = _
  refine hs.trans ?_
  change (v.1 0) ^ 2 * metricRm04StandardAt (lineWarped h κ) p
      (lineUnit p.1, 0) (0, w.2) (0, w.2) (lineUnit p.1, 0) -
    2 * v.1 0 * w.1 0 * metricRm04StandardAt (lineWarped h κ) p
      (lineUnit p.1, 0) (0, v.2) (0, w.2) (lineUnit p.1, 0) +
    (w.1 0) ^ 2 * metricRm04StandardAt (lineWarped h κ) p
      (lineUnit p.1, 0) (0, v.2) (0, v.2) (lineUnit p.1, 0) +
    metricRm04StandardAt (lineWarped h κ) p (0, v.2) (0, w.2) (0, w.2) (0, v.2) = _
  rw [lineWarped_mixed, lineWarped_mixed, lineWarped_mixed, lineWarped_vertical]

private theorem lineExp_sectional
    (h : SmoothRiemannianMetric J N) (κ : ℝ) (p : EuclideanSpace ℝ (Fin 1) × N)
    (v w : EuclideanSpace ℝ (Fin 1) × F) :
    let G := lineMetric.warpedProduct h (lineExp κ) (lineExp_smooth κ)
      (fun q => Real.exp_pos (-κ * lineDepth q))
    metricRm04StandardAt G p v w w v =
      Real.exp (-2 * κ * p.1 0) * metricRm04StandardAt h p.2 v.2 w.2 w.2 v.2 -
      κ ^ 2 * (G.inner p v v * G.inner p w w - G.inner p v w ^ 2) := by
  change metricRm04StandardAt (lineWarped h κ) p v w w v = _
  rw [lineWarped_sectional_expansion]
  change _ = Real.exp (-2 * κ * p.1 0) * metricRm04StandardAt h p.2 v.2 w.2 w.2 v.2 -
    κ ^ 2 * ((lineWarped h κ).inner p v v * (lineWarped h κ).inner p w w -
      (lineWarped h κ).inner p v w ^ 2)
  rw [lineWarped_pair, lineWarped_pair, lineWarped_pair]
  exact exponential_sectional_scalar κ (Real.exp (-2 * κ * p.1 0))
    (v.1 0) (w.1 0) (h.inner p.2 v.2 v.2) (h.inner p.2 w.2 w.2)
    (h.inner p.2 v.2 w.2) (metricRm04StandardAt h p.2 v.2 w.2 w.2 v.2)

end LineWarped

section HyperbolicModel

private def hypBase : ModelCoordinates →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (EuclideanSpace.equiv (Fin 1) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun _ => EuclideanSpace.proj (2 : Fin 3))

private def hypFiber : ModelCoordinates →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin 2 => EuclideanSpace.proj (Fin.castSucc i))

private def hypJoin :
    EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2) →L[ℝ] ModelCoordinates :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![
      (EuclideanSpace.proj (0 : Fin 2)).comp (ContinuousLinearMap.snd ℝ _ _),
      (EuclideanSpace.proj (1 : Fin 2)).comp (ContinuousLinearMap.snd ℝ _ _),
      (EuclideanSpace.proj (0 : Fin 1)).comp (ContinuousLinearMap.fst ℝ _ _)])

private theorem hypBase_apply (p : ModelCoordinates) : hypBase p 0 = p 2 := rfl

private theorem hypFiber_apply (p : ModelCoordinates) (i : Fin 2) :
    hypFiber p i = p (Fin.castSucc i) := rfl

private theorem hyp_inner_eq (p v w : ModelCoordinates) :
    coordinateInner .hyperbolic p v w = hypBase v 0 * hypBase w 0 +
      Real.exp (-2 * 1 * hypBase p 0) * inner ℝ (hypFiber v) (hypFiber w) := by
  have he : Real.exp (-2 * 1 * p 2) = Real.exp (-p 2) * Real.exp (-p 2) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hypBase_apply, hypBase_apply, hypBase_apply, he]
  simp only [coordinateInner, coordinateCoframe, Fin.sum_univ_three, PiLp.inner_apply,
    Fin.sum_univ_two, hypFiber_apply]
  simp
  ring

private def hypSplit : Diffeomorph (𝓡 3) ((𝓡 1).prod (𝓡 2)) ModelCoordinates
    (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) ∞ where
  toFun p := (hypBase p, hypFiber p)
  invFun q := hypJoin q
  left_inv p := by
    ext j
    fin_cases j <;> simp [hypBase, hypFiber, hypJoin]
  right_inv q := by
    ext i
    · fin_cases i
      simp [hypBase, hypJoin]
    · fin_cases i <;> simp [hypFiber, hypJoin]
  contMDiff_toFun := hypBase.contDiff.contMDiff.prodMk hypFiber.contDiff.contMDiff
  contMDiff_invFun := hypJoin.contDiff.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)

private theorem hypSplit_mfderiv (p : ModelCoordinates) (v : TangentSpace (𝓡 3) p) :
    mfderiv (𝓡 3) ((𝓡 1).prod (𝓡 2)) hypSplit p v = (hypBase v, hypFiber v) := by
  have h := mfderiv_prodMk (I := 𝓡 3) (I' := 𝓡 1) (I'' := 𝓡 2)
    (hypBase.mdifferentiableAt (x := p)) (hypFiber.mdifferentiableAt (x := p))
  change mfderiv (𝓡 3) ((𝓡 1).prod (𝓡 2)) (fun x => (hypBase x, hypFiber x)) p v = _
  rw [h, hypBase.mfderiv_eq, hypFiber.mfderiv_eq]
  rfl

private abbrev hypWarped :=
  lineWarped (euclideanMetric (E := EuclideanSpace ℝ (Fin 2))) 1

private theorem coordinateModelMetric_hyperbolic_eq :
    coordinateModelMetric .hyperbolic =
      Diffeomorph.pullbackMetricCross hypWarped hypSplit := by
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  rw [Diffeomorph.pullbackMetricCross_inner, hypSplit_mfderiv, hypSplit_mfderiv]
  erw [coordinateModelMetric_inner, lineWarped_pair]
  exact hyp_inner_eq p v w

theorem coordinateModelMetric_hyperbolic_hasConstantSectionalCurvature :
    HasConstantSectionalCurvature (coordinateModelMetric .hyperbolic) (-1) := by
  rw [hasConstantSectionalCurvature_iff, coordinateModelMetric_hyperbolic_eq]
  intro p X Y
  rw [metricRm04Standard_pullbackCross, Diffeomorph.pullbackMetricCross_inner,
    Diffeomorph.pullbackMetricCross_inner, Diffeomorph.pullbackMetricCross_inner,
    hypSplit_mfderiv, hypSplit_mfderiv]
  have hs := lineExp_sectional (euclideanMetric (E := EuclideanSpace ℝ (Fin 2))) 1
    (hypSplit p) (hypBase X, hypFiber X) (hypBase Y, hypFiber Y)
  have hz : ∀ (q : EuclideanSpace ℝ (Fin 2)) (a b : TangentSpace (𝓡 2) q),
      metricRm04StandardAt (euclideanMetric (E := EuclideanSpace ℝ (Fin 2))) q a b b a = 0 := by
    intro q a b
    rw [metricRm04StandardAt_apply, euclideanMetric_metricRm04At_eq_zero]
    rfl
  have h0 := hz (hypSplit p).2 (hypFiber X) (hypFiber Y)
  dsimp only at hs
  refine hs.trans ?_
  simp only [hypWarped, lineWarped]
  linear_combination Real.exp (-2 * 1 * (hypSplit p).1 0) * h0

end HyperbolicModel

section Thurston

local instance factFinrankEuclideanFourConstantCurvature : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

private instance : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := ⟨by simp⟩

theorem sphericalModelMetric_hasConstantSectionalCurvature :
    HasConstantSectionalCurvature sphericalModelMetric 1 :=
  (hasConstantSectionalCurvature_iff _ 1).mpr fun x X Y => by
    rw [one_mul]
    exact roundMetric_sec_value x X Y

theorem euclideanModelMetric_hasConstantSectionalCurvature :
    HasConstantSectionalCurvature euclideanModelMetric 0 :=
  (hasConstantSectionalCurvature_iff _ 0).mpr fun x X Y => by
    rw [zero_mul, metricRm04StandardAt_apply]
    simp only [euclideanModelMetric, euclideanMetric_metricRm04At_eq_zero]
    rfl

def constantCurvatureModel (κ : ℝ) : ThurstonModel :=
  if κ = 1 then .spherical else if κ = 0 then .euclidean else .hyperbolic

theorem constantCurvatureModel_one : constantCurvatureModel 1 = .spherical := by
  simp [constantCurvatureModel]

theorem constantCurvatureModel_zero : constantCurvatureModel 0 = .euclidean := by
  simp [constantCurvatureModel]

theorem constantCurvatureModel_neg_one : constantCurvatureModel (-1) = .hyperbolic := by
  norm_num [constantCurvatureModel]

variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem hasThurstonAtlas_spherical_of_hasConstantSectionalCurvature [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hg : HasConstantSectionalCurvature g 1) : HasThurstonAtlas g .spherical := by
  have : Nonempty RoundThree := ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  exact modelAtlas_of_riemannOp_eq_smul 1 g sphericalModelMetric hcomplete
    sphericalModel_complete (riemannOp_eq_smul_of_hasConstantSectionalCurvature hg)
    (riemannOp_eq_smul_of_hasConstantSectionalCurvature
      sphericalModelMetric_hasConstantSectionalCurvature)

theorem hasThurstonAtlas_euclidean_of_hasConstantSectionalCurvature [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hg : HasConstantSectionalCurvature g 0) : HasThurstonAtlas g .euclidean :=
  modelAtlas_of_riemannOp_eq_smul 0 g euclideanModelMetric hcomplete
    euclideanModel_complete (riemannOp_eq_smul_of_hasConstantSectionalCurvature hg)
    (riemannOp_eq_smul_of_hasConstantSectionalCurvature
      euclideanModelMetric_hasConstantSectionalCurvature)

theorem hasThurstonAtlas_hyperbolic_of_hasConstantSectionalCurvature [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hg : HasConstantSectionalCurvature g (-1)) : HasThurstonAtlas g .hyperbolic := by
  change CoordinateModelAtlas g .hyperbolic
  rw [coordinateModelAtlas_iff_actualModelAtlas]
  exact modelAtlas_of_riemannOp_eq_smul (-1) g (coordinateModelMetric .hyperbolic) hcomplete
    (coordinateModelMetric_complete .hyperbolic)
    (riemannOp_eq_smul_of_hasConstantSectionalCurvature hg)
    (riemannOp_eq_smul_of_hasConstantSectionalCurvature
      coordinateModelMetric_hyperbolic_hasConstantSectionalCurvature)

theorem hasThurstonAtlas_of_constantCurvature [SigmaCompactSpace M] {κ : ℝ}
    (hκ : κ = 1 ∨ κ = 0 ∨ κ = -1)
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hg : HasConstantSectionalCurvature g κ) :
    HasThurstonAtlas g (constantCurvatureModel κ) := by
  rcases hκ with rfl | rfl | rfl
  · rw [constantCurvatureModel_one]
    exact hasThurstonAtlas_spherical_of_hasConstantSectionalCurvature g hcomplete hg
  · rw [constantCurvatureModel_zero]
    exact hasThurstonAtlas_euclidean_of_hasConstantSectionalCurvature g hcomplete hg
  · rw [constantCurvatureModel_neg_one]
    exact hasThurstonAtlas_hyperbolic_of_hasConstantSectionalCurvature g hcomplete hg

theorem hasConstantSectionalCurvature_of_hasThurstonAtlas_spherical
    {g : SmoothRiemannianMetric I M} (hA : HasThurstonAtlas g .spherical) :
    HasConstantSectionalCurvature g 1 :=
  hasConstantSectionalCurvature_of_modelAtlas
    sphericalModelMetric_hasConstantSectionalCurvature hA

theorem hasConstantSectionalCurvature_of_hasThurstonAtlas_euclidean
    {g : SmoothRiemannianMetric I M} (hA : HasThurstonAtlas g .euclidean) :
    HasConstantSectionalCurvature g 0 :=
  hasConstantSectionalCurvature_of_modelAtlas
    euclideanModelMetric_hasConstantSectionalCurvature hA

theorem hasConstantSectionalCurvature_of_hasThurstonAtlas_hyperbolic
    {g : SmoothRiemannianMetric I M} (hA : HasThurstonAtlas g .hyperbolic) :
    HasConstantSectionalCurvature g (-1) :=
  hasConstantSectionalCurvature_of_modelAtlas
    coordinateModelMetric_hyperbolic_hasConstantSectionalCurvature
    ((coordinateModelAtlas_iff_actualModelAtlas g .hyperbolic).mp hA)

theorem hasConstantSectionalCurvature_of_hasThurstonAtlas {κ : ℝ}
    (hκ : κ = 1 ∨ κ = 0 ∨ κ = -1)
    {g : SmoothRiemannianMetric I M} (hA : HasThurstonAtlas g (constantCurvatureModel κ)) :
    HasConstantSectionalCurvature g κ := by
  rcases hκ with rfl | rfl | rfl
  · rw [constantCurvatureModel_one] at hA
    exact hasConstantSectionalCurvature_of_hasThurstonAtlas_spherical hA
  · rw [constantCurvatureModel_zero] at hA
    exact hasConstantSectionalCurvature_of_hasThurstonAtlas_euclidean hA
  · rw [constantCurvatureModel_neg_one] at hA
    exact hasConstantSectionalCurvature_of_hasThurstonAtlas_hyperbolic hA

theorem hasThurstonAtlas_iff_hasConstantSectionalCurvature [SigmaCompactSpace M] {κ : ℝ}
    (hκ : κ = 1 ∨ κ = 0 ∨ κ = -1)
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g) :
    HasThurstonAtlas g (constantCurvatureModel κ) ↔ HasConstantSectionalCurvature g κ :=
  ⟨hasConstantSectionalCurvature_of_hasThurstonAtlas hκ,
    hasThurstonAtlas_of_constantCurvature hκ g hcomplete⟩

end Thurston

end GC.Geometry
