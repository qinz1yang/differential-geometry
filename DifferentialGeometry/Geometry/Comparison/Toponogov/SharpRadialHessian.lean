import DifferentialGeometry.Geometry.Comparison.Hessian.Radial

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open Exponential
open Variation
open CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private theorem exists_intrinsicJacobi_one_eq
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {u : TangentSpace I p}
    (hu : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source)
    (Y : TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p u 1)) :
    ∃ w : TangentSpace I p,
      intrinsicJacobi (I := I) g hEnorm p u w 1 = Y := by
  let eP : TangentSpace I p ≃L[Real] E :=
    tangentSpaceModelContinuousLinearEquiv (I := I) p
  let uE : E := eP u
  let expf : E → M := fun v =>
    expMapIntrinsic (I := I) g hEnorm p (eP.symm v)
  let q : M := expf uE
  let eU : TangentSpace 𝓘(Real, E) uE ≃L[Real] E :=
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) uE
  let eQ : TangentSpace I q ≃L[Real] E :=
    tangentSpaceModelContinuousLinearEquiv (I := I) q
  have hq : q ∈ B.dom := by
    have hqexp : q = B.hom uE := B.hom_eq hu
    rw [hqexp]
    exact B.hom.map_source hu
  have hinv : B.inv q = uE := by
    simpa only [q, expf, uE, eP] using B.left_inv hu
  let dInv : E := eU (mfderiv I 𝓘(Real, E) B.inv q Y)
  let w : TangentSpace I p := eP.symm dInv
  refine ⟨w, ?_⟩
  have hexpInv := exp_inv_mfderiv (I := I) B hq Y
  rw [hinv] at hexpInv
  have hmodel :
      eQ (mfderiv 𝓘(Real, E) I expf uE (eU.symm dInv)) = eQ Y := by
    dsimp only [q, expf, uE, eP, eU, eQ, dInv] at hexpInv ⊢
    exact hexpInv
  have hexp :
      mfderiv 𝓘(Real, E) I expf uE (eU.symm dInv) = Y :=
    eQ.injective hmodel
  let expOld : E → M := fun v =>
    expMapIntrinsic (I := I) g hEnorm p
      (v : TangentSpace I p)
  have hexpFun : expOld = expf := by
    funext v
    simp only [expOld, expf, eP,
      tangentSpaceModelContinuousLinearEquiv_symm_apply]
  have hcurve :
      (fun s : Real => intrinsicGeodesic (I := I) g hEnorm p
        (uE + s • dInv : TangentSpace I p) 1) =
        fun s => intrinsicGeodesic (I := I) g hEnorm p
          (u + s • w) 1 := by
    funext s
    congr 2
  have hj := intrinsic_jacobi_one (I := I) g hEnorm p uE dInv
  change
    mfderiv 𝓘(Real, Real) I
        (fun s : Real => intrinsicGeodesic (I := I) g hEnorm p
          (uE + s • dInv : TangentSpace I p) 1)
        0 (1 : Real) =
      mfderiv 𝓘(Real, E) I expOld uE
        (dInv : TangentSpace 𝓘(Real, E) uE) at hj
  rw [hexpFun] at hj
  have hdir :
      (dInv : TangentSpace 𝓘(Real, E) uE) = eU.symm dInv := by
    with_unfolding_all rfl
  have hrhs :
      mfderiv 𝓘(Real, E) I expf uE
          (dInv : TangentSpace 𝓘(Real, E) uE) = Y := by
    rw [hdir]
    exact hexp
  rw [hrhs] at hj
  rw [hcurve] at hj
  with_unfolding_all exact hj

private theorem branchHess_perp_radial_eq_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p)
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (hv : 0 < g.inner p v v)
    (hsrc : tangentSpaceModelContinuousLinearEquiv (I := I) p v ∈
      B.hom.source)
    (Y : TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm p v 1))
    (hYperp : g.inner
      (intrinsicGeodesic (I := I) g hEnorm p v 1)
      (curveVelocity (I := I)
        (intrinsicGeodesic (I := I) g hEnorm p v) 1) Y = 0) :
    hessFun (I := I) g (branchRadius (I := I) g B)
        (intrinsicGeodesic (I := I) g hEnorm p v 1) Y
        (curveVelocity (I := I)
          (intrinsicGeodesic (I := I) g hEnorm p v) 1) = 0 := by
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p v
  let J : TangentSpace I p → ∀ t, TangentSpace I (γ t) := fun w =>
    intrinsicJacobi (I := I) g hEnorm p v w
  obtain ⟨w, hw⟩ :=
    exists_intrinsicJacobi_one_eq (I := I) g hEnorm p B hsrc Y
  have hGauss := intrinsicJacobi_perp (I := I) g hEnorm p v w
  have hGauss' :
      g.inner (intrinsicGeodesic (I := I) g hEnorm p v 1)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p v) 1)
          (intrinsicJacobi (I := I) g hEnorm p v w 1) =
        g.inner p v w := by
    with_unfolding_all exact hGauss
  have hvw : g.inner p v w = 0 := by
    rw [hw, hYperp] at hGauss'
    exact hGauss'.symm
  have hDperp :
      g.inner (γ 1) (covDerivAlong (I := I) g γ (J w) 1)
        (curveVelocity (I := I) γ 1) = 0 := by
    rw [g.symm (γ 1)]
    simpa only [γ, J] using
      intrinsicJacobi_dperp (I := I) g hEnorm p v w one_ne_zero hvw
  have hshape := branchHess_jacobi (I := I) B hsrc hv
    (w₁ := w) (w₂ := v)
  dsimp only at hshape
  change hessFun (I := I) g (branchRadius (I := I) g B) (γ 1)
    (J w 1) (intrinsicJacobi (I := I) g hEnorm p v v 1) = _ at hshape
  rw [intrinsicJacobi_self (I := I) g hEnorm p v, hDperp, hvw,
    zero_div, zero_mul, zero_div, sub_zero] at hshape
  rw [← hw]
  simpa only [γ, J] using hshape

private theorem branchHess_symm
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p)
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (hv : 0 < g.inner p v v)
    (hsrc : tangentSpaceModelContinuousLinearEquiv (I := I) p v ∈
      B.hom.source)
    (Y Z : TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm p v 1)) :
    hessFun (I := I) g (branchRadius (I := I) g B)
        (intrinsicGeodesic (I := I) g hEnorm p v 1) Y Z =
      hessFun (I := I) g (branchRadius (I := I) g B)
        (intrinsicGeodesic (I := I) g hEnorm p v 1) Z Y := by
  let q : M := expMapIntrinsic (I := I) g hEnorm p v
  obtain ⟨U, hUopen, hqU, hrU⟩ :=
    branchRadius_open (I := I) B hsrc hv
  obtain ⟨rSmooth, hrSmooth, hr_eq⟩ :=
    DifferentialGeometry.exists_smooth_germ (I := I) hUopen hqU hrU
  have hcongr := hessFun_congr (I := I) g hr_eq
  have hsymm := hessFun_symm_of_boundaryless (I := I) g hrSmooth q Y Z
  change hessFun (I := I) g (branchRadius (I := I) g B) q Y Z =
    hessFun (I := I) g (branchRadius (I := I) g B) q Z Y
  calc
    _ = hessFun (I := I) g rSmooth q Y Z := by
      exact congrArg (fun T => T Y Z) hcongr.symm
    _ = hessFun (I := I) g rSmooth q Z Y := hsymm
    _ = _ := by
      exact congrArg (fun T => T Z Y) hcongr

theorem branchHess_sharp_le_of_minimizing_of_sectional_curvature_nonnegative
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (L : Real)
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (hL : 0 < L)
    (hu : g.inner p u u = 1)
    (hsrc : tangentSpaceModelContinuousLinearEquiv (I := I) p (L • u) ∈
      B.hom.source)
    (hmin : ∀ η : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 η (Set.Icc 0 L) →
      η 0 = p →
      η L = intrinsicGeodesic (I := I) g hEnorm p u L →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u) 0 L ≤
        arcLength (I := I) g η 0 L)
    (hsec : ∀ t ∈ Set.Icc (0 : Real) L,
      metricRm04At (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u t) ∈
        DifferentialGeometry.tensor04SectionalNonnegativeCone
          (I := I) (M := M))
    (Y : TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1)) :
    hessFun (I := I) g (branchRadius (I := I) g B)
        (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y ≤
      (g.inner (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y -
        (g.inner (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1)
          (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm p (L • u)) 1)
          Y / L) ^ 2) / L := by
  let v : TangentSpace I p := L • u
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p v
  let q : M := γ 1
  let V : TangentSpace I q := curveVelocity (I := I) γ 1
  let Hess := hessFun (I := I) g (branchRadius (I := I) g B) q
  have hv : 0 < g.inner p v v := by
    dsimp only [v]
    rw [gInner_smul_self (I := I) g p L u, hu]
    positivity
  have hVsq : g.inner q V V = L ^ 2 := by
    calc
      g.inner q V V = g.inner p v v := by
        with_unfolding_all exact
          intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p v 1
      _ = L ^ 2 := by
        dsimp only [v]
        rw [gInner_smul_self (I := I) g p L u, hu, mul_one]
  let a : Real := g.inner q V Y / L ^ 2
  let Z : TangentSpace I q := Y - a • V
  have hZperp : g.inner q V Z = 0 := by
    dsimp only [Z, a]
    rw [map_sub, map_smul, smul_eq_mul, hVsq]
    field_simp
    ring
  have hZbound : Hess Z Z ≤ g.inner q Z Z / L := by
    simpa only [Hess, q, γ, v] using
      branchHess_le_of_minimizing_of_sectional_curvature_nonnegative
        (I := I) g hEnorm p u L B hL hu hsrc hmin hsec Z
  have hZV : Hess Z V = 0 := by
    simpa only [Hess, q, γ, v, V] using
      branchHess_perp_radial_eq_zero (I := I) g hEnorm p v B hv hsrc Z hZperp
  have hsymm : Hess Z V = Hess V Z := by
    simpa only [Hess, q, γ, v, V] using
      branchHess_symm (I := I) g hEnorm p v B hv hsrc Z V
  have hVZ : Hess V Z = 0 := hsymm.symm.trans hZV
  have hsrcv : (v : E) ∈ B.hom.source := by
    with_unfolding_all exact hsrc
  have hVV : Hess V V = 0 := by
    simpa only [Hess, q, γ, v, V] using
      branchHess_radial (I := I) B (u := v) hsrcv hv
  have hYdecomp : Y = Z + a • V := by
    dsimp only [Z]
    module
  have hHZaV : Hess Z (a • V) = 0 := by
    calc
      Hess Z (a • V) = a • Hess Z V := (Hess Z).map_smul a V
      _ = 0 := by rw [hZV, smul_zero]
  have hHaVZ : Hess (a • V) Z = 0 := by
    calc
      Hess (a • V) Z = a • Hess V Z := LinearMap.map_smul₂ Hess a V Z
      _ = 0 := by rw [hVZ, smul_zero]
  have hHaVaV : Hess (a • V) (a • V) = 0 := by
    calc
      Hess (a • V) (a • V) = a • Hess V (a • V) :=
        LinearMap.map_smul₂ Hess a V (a • V)
      _ = a • (a • Hess V V) := by rw [(Hess V).map_smul]
      _ = 0 := by rw [hVV, smul_zero, smul_zero]
  have hHdecomp : Hess Y Y = Hess Z Z := by
    rw [hYdecomp]
    have hleft := LinearMap.map_add₂ Hess Z (a • V) (Z + a • V)
    have hrightZ := (Hess Z).map_add Z (a • V)
    have hrightaV := (Hess (a • V)).map_add Z (a • V)
    calc
      Hess (Z + a • V) (Z + a • V) =
          (Hess Z Z + Hess Z (a • V)) +
            (Hess (a • V) Z + Hess (a • V) (a • V)) :=
        hleft.trans
          (congrArg₂ (fun x y : Real => x + y) hrightZ hrightaV)
      _ = Hess Z Z := by rw [hHZaV, hHaVZ, hHaVaV]; ring
  have hZVinner : g.inner q Z V = 0 := by
    rw [g.symm q]
    exact hZperp
  have hGZaV : g.inner q Z (a • V) = 0 := by
    calc
      g.inner q Z (a • V) = a • g.inner q Z V :=
        (g.inner q Z).map_smul a V
      _ = 0 := by rw [hZVinner, smul_zero]
  have hGaVZ : g.inner q (a • V) Z = 0 := by
    calc
      g.inner q (a • V) Z = a • g.inner q V Z :=
        ContinuousLinearMap.map_smul₂ (g.inner q) a V Z
      _ = 0 := by rw [hZperp, smul_zero]
  have hGaVaV :
      g.inner q (a • V) (a • V) = a ^ 2 * g.inner q V V := by
    rw [ContinuousLinearMap.map_smul₂, ContinuousLinearMap.map_smul,
      smul_eq_mul]
    ring
  have hnorm :
      g.inner q Y Y = g.inner q Z Z + a ^ 2 * g.inner q V V := by
    rw [hYdecomp]
    have hleft :=
      ContinuousLinearMap.map_add₂ (g.inner q) Z (a • V) (Z + a • V)
    have hrightZ := (g.inner q Z).map_add Z (a • V)
    have hrightaV := (g.inner q (a • V)).map_add Z (a • V)
    calc
      g.inner q (Z + a • V) (Z + a • V) =
          (g.inner q Z Z + g.inner q Z (a • V)) +
            (g.inner q (a • V) Z + g.inner q (a • V) (a • V)) :=
        hleft.trans
          (congrArg₂ (fun x y : Real => x + y) hrightZ hrightaV)
      _ = g.inner q Z Z + a ^ 2 * g.inner q V V := by
        rw [hGZaV, hGaVZ, hGaVaV]
        ring
  have hradial : a ^ 2 * g.inner q V V = (g.inner q V Y / L) ^ 2 := by
    rw [hVsq]
    dsimp only [a]
    field_simp
  have hnorm_exact : g.inner q Z Z =
      g.inner q Y Y - (g.inner q V Y / L) ^ 2 := by
    rw [hradial] at hnorm
    linarith only [hnorm]
  calc
    Hess Y Y = Hess Z Z := hHdecomp
    _ ≤ g.inner q Z Z / L := hZbound
    _ = (g.inner q Y Y - (g.inner q V Y / L) ^ 2) / L := by rw [hnorm_exact]


theorem branchHess_gradient_le_of_minimizing_of_sectional_curvature_nonnegative
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (L : Real)
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (hL : 0 < L)
    (hu : g.inner p u u = 1)
    (hsrc : tangentSpaceModelContinuousLinearEquiv (I := I) p (L • u) ∈
      B.hom.source)
    (hmin : ∀ η : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 η (Set.Icc 0 L) →
      η 0 = p →
      η L = intrinsicGeodesic (I := I) g hEnorm p u L →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u) 0 L ≤
        arcLength (I := I) g η 0 L)
    (hsec : ∀ t ∈ Set.Icc (0 : Real) L,
      metricRm04At (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u t) ∈
        DifferentialGeometry.tensor04SectionalNonnegativeCone
          (I := I) (M := M))
    (Y : TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1)) :
    hessFun (I := I) g (branchRadius (I := I) g B)
        (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y ≤
      (g.inner (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y -
        (g.inner (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1)
          (gradientFun (I := I) g (branchRadius (I := I) g B)
            (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1)) Y) ^ 2) / L := by
  let v : TangentSpace I p := L • u
  let q : M := intrinsicGeodesic (I := I) g hEnorm p v 1
  let V : TangentSpace I q :=
    curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm p v) 1
  have hvsq : g.inner p v v = L ^ 2 := by
    dsimp only [v]
    rw [gInner_smul_self (I := I) g p L u, hu, mul_one]
  have hv : 0 < g.inner p v v := hvsq.symm ▸ sq_pos_of_pos hL
  have hgrad : gradientFun (I := I) g (branchRadius (I := I) g B) q =
      L⁻¹ • V := by
    have h := grad_branchRadius (I := I) B hsrc hv
    rw [hvsq, Real.sqrt_sq_eq_abs, abs_of_pos hL] at h
    with_unfolding_all exact h
  have hradial : g.inner q
      (gradientFun (I := I) g (branchRadius (I := I) g B) q) Y =
      g.inner q V Y / L := by
    rw [hgrad, ContinuousLinearMap.map_smul₂, smul_eq_mul]
    ring
  have h := branchHess_sharp_le_of_minimizing_of_sectional_curvature_nonnegative
    (I := I) g hEnorm p u L B hL hu hsrc hmin hsec Y
  change hessFun (I := I) g (branchRadius (I := I) g B) q Y Y ≤
    (g.inner q Y Y -
      (g.inner q (gradientFun (I := I) g (branchRadius (I := I) g B) q) Y) ^ 2) / L
  rw [hradial]
  exact h

end Riemannian
end Geometry
end DifferentialGeometry

end
