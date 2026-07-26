import DifferentialGeometry.Geometry.Comparison.Variation.CartanTransfer
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Exponential.IntrinsicSmooth
import DifferentialGeometry.Geometry.Exponential.JacobiVariation
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Metric.InnerExpansion

set_option autoImplicit false

/-!
# Constant-curvature exponential differential norm transfer

The scalar Cartan transfer theorem is applied to the intrinsic Jacobi
variations of two curvature-one manifolds.  A metric-preserving linear
equivalence at the launch points seeds matching parallel orthonormal frames.
-/

noncomputable section

open Set Function Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  [I'.Boundaryless]
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' ∞ M'] [T2Space M'] [SigmaCompactSpace M']
  [T2Space (TangentBundle I' M')]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [ConnectedSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable
  [RiemannianBundle (fun x : M' ↦ TangentSpace I' x)]
  [PseudoEMetricSpace M'] [IsRiemannianManifold I' M'] [CompleteSpace M']
  [ConnectedSpace M']
  [IsContinuousRiemannianBundle E (fun x : M' ↦ TangentSpace I' x)]

/-- A linear isometry between the launch tangent metrics transfers the squared
norm of the intrinsic exponential differential between curvature-one
manifolds. -/
theorem expDiff_sq_xfer
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (g' : SmoothRiemannianMetric I' M')
    (hEnorm' : ∀ (x : M') (v : TangentSpace I' x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g'.inner x v v)))
    (p : M) (p' : M') (u w : E)
    (i : E ≃L[ℝ] E)
    (hi : ∀ a b : E, g'.inner p' (i a) (i b) = g.inner p a b)
    (hR : ∀ (x : M) (X Y Z : TangentSpace I x),
      (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) x)
        X Y Z =
          g.inner x Y Z • X - g.inner x X Z • Y)
    (hR' : ∀ (x : M') (X Y Z : TangentSpace I' x),
      (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I') g') x)
        X Y Z =
          g'.inner x Y Z • X - g'.inner x X Z • Y) :
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
  letI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I p))) :=
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
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis
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
    rw [hγ0', hi]
    exact hbasis a b
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
    intro t _ht
    have h :=
      velocityField_chartRep_differentiableAt (I := I) g Fvar hFvar t
    rw [hcentral] at h
    simpa only [V] using h
  have hVdiff' : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (chartRepAt (I := I') γ' V' t) t := by
    intro t _ht
    have h :=
      velocityField_chartRep_differentiableAt (I := I') g' Fvar' hFvar' t
    rw [hcentral'] at h
    simpa only [V'] using h
  have hVpar : ∀ t ∈ Icc (0 : ℝ) 1,
      covDerivAlong (I := I) g γ V t = 0 := by
    intro t _ht
    apply covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
      (I := I) g γ t
      (hγ.contMDiffAt.of_le (by norm_num))
    simpa only [γ] using
      intrinsicGeodesic_isGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u) t
  have hVpar' : ∀ t ∈ Icc (0 : ℝ) 1,
      covDerivAlong (I := I') g' γ' V' t = 0 := by
    intro t _ht
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
        (N := 2) (by norm_num) hγ2 (by norm_num : (0 : ℝ) ≤ 1)
        (frame a) V (hframeDiff a) hVdiff (hframePar a) hVpar t ht
    rw [hframe0 a, hγ0] at hconst
    simpa only [hV0] using hconst
  have hvelCoord' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a,
      g'.inner (γ' t) (frame' a t) (V' t) =
        g.inner p (basis a) u := by
    intro t ht a
    have hconst :=
      parallel_transport_preserves_inner_product (I := I') g' γ'
        (N := 2) (by norm_num) hγ2' (by norm_num : (0 : ℝ) ≤ 1)
        (frame' a) V' (hframeDiff' a) hVdiff' (hframePar' a) hVpar' t ht
    rw [hframe0' a, hγ0'] at hconst
    rw [show V' 0 = i u from hV0'] at hconst
    exact hconst.trans (hi (basis a) u)
  have hspeed : ∀ t : ℝ,
      g.inner (γ t) (V t) (V t) = g.inner p u u := by
    intro t
    simpa only [γ, V] using
      intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p
        (show TangentSpace I p from u) t
  have hspeed' : ∀ t : ℝ,
      g'.inner (γ' t) (V' t) (V' t) = g.inner p u u := by
    intro t
    have hs :=
      intrinsicGeodesic_speedSq_eq (I := I') g' hEnorm' p'
        (show TangentSpace I' p' from i u) t
    simpa only [γ', V', hi u u] using hs
  let a0 : Fin (Module.finrank ℝ (TangentSpace I p)) →
      Fin (Module.finrank ℝ (TangentSpace I p)) → ℝ := fun a b =>
    g.inner p u u * (if a = b then 1 else 0) -
      g.inner p (basis b) u * g.inner p (basis a) u
  have hcoef : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a b,
      g.inner (γ t) (frame a t)
          ((DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
              (γ t))
            (frame b t) (V t) (V t))
        = a0 a b := by
    intro t ht a b
    rw [hR]
    simp only [map_sub, map_smul, smul_eq_mul]
    rw [hspeed t, hframeON t ht a b, hvelCoord t ht b, hvelCoord t ht a]
  have hcoef' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a b,
      g'.inner (γ' t) (frame' a t)
          ((DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I') g')
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
        ((DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
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
    intro t _ht
    have h :=
      variationField_chartRep_differentiableAt (I := I) g Fvar hFvar t
    rw [hcentral] at h
    simpa only [Y] using h
  have hYdiff' : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (chartRepAt (I := I') γ' Y' t) t := by
    intro t _ht
    have h :=
      variationField_chartRep_differentiableAt (I := I') g' Fvar' hFvar' t
    rw [hcentral'] at h
    simpa only [Y'] using h
  have hDYdiff : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ Y s) t) t := by
    intro t _ht
    have h := variationField_covDeriv_chartRep_differentiableAt
      (I := I) g Fvar hFvar t
    rw [hcentral] at h
    simpa only [Y] using h
  have hDYdiff' : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (chartRepAt (I := I') γ'
        (fun s => covDerivAlong (I := I') g' γ' Y' s) t) t := by
    intro t _ht
    have h := variationField_covDeriv_chartRep_differentiableAt
      (I := I') g' Fvar' hFvar' t
    rw [hcentral'] at h
    simpa only [Y'] using h
  have hJ : ∀ t ∈ Icc (0 : ℝ) 1, IsJacobiAt (I := I) g γ Y t := by
    intro t _ht
    simpa only [γ, Y, Fvar, zero_smul, add_zero] using
      intrinsic_jacobi (I := I) g hEnorm p u w t
  have hJ' : ∀ t ∈ Icc (0 : ℝ) 1, IsJacobiAt (I := I') g' γ' Y' t := by
    intro t _ht
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
        hframe0 a, hframe0' a, hγ0, hγ0', hi]
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
  have hYone :
      Y 1 =
        mfderiv 𝓘(ℝ, E) I
          (fun v : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from v))
          u w := by
    simpa only [Y, Fvar] using
      intrinsic_jacobi_one (I := I) g hEnorm p u w
  have hYone' :
      Y' 1 =
        mfderiv 𝓘(ℝ, E) I'
          (fun v : E => expMapIntrinsic (I := I') g' hEnorm' p'
            (show TangentSpace I' p' from v))
          (i u) (i w) := by
    simpa only [Y', Fvar'] using
      intrinsic_jacobi_one (I := I') g' hEnorm' p' (i u) (i w)
  simpa only [γ, γ', expMapIntrinsic, hYone, hYone'] using hnormY

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
