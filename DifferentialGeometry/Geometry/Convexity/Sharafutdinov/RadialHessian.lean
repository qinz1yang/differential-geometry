import DifferentialGeometry.Geometry.Comparison.Hessian.Radial
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false

open private branchHess_perp_le_of_minimizing branchHess_perp_radial_eq_zero branchHess_symm
  from DifferentialGeometry.Geometry.Comparison.Hessian.Radial

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Matrix Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem branchHess_le_perpendicular_sq_of_minimizing
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
    let q := intrinsicGeodesic (I := I) g hEnorm p (L • u) 1
    let V := curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm p (L • u)) 1
    hessFun (I := I) g (branchRadius (I := I) g B) q Y Y ≤
      (g.inner q Y Y - (g.inner q V Y) ^ 2 / L ^ 2) / L := by
  dsimp only
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
  have hsec' : ∀ t ∈ Set.Icc (0 : Real) L,
      ∀ W : TangentSpace I
          (intrinsicGeodesic (I := I) g hEnorm p u t),
        0 ≤ metricRm04StandardAt (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u t) W
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t) W := by
    intro t ht W
    exact
      (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
        (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p u t)).mp
          (hsec t ht) W
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t)
  have hZbound : Hess Z Z ≤ g.inner q Z Z / L := by
    simpa only [Hess, q, γ, v] using
      branchHess_perp_le_of_minimizing (I := I) g hEnorm p u L B
        hL hu hsrc hmin hsec' Z hZperp
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
  have hnorm_exact :
      g.inner q Z Z = g.inner q Y Y - (g.inner q V Y) ^ 2 / L ^ 2 := by
    rw [hnorm, hVsq]
    dsimp only [a]
    field_simp [hL.ne']
    ring
  calc
    Hess Y Y = Hess Z Z := hHdecomp
    _ ≤ g.inner q Z Z / L := hZbound
    _ = (g.inner q Y Y - (g.inner q V Y) ^ 2 / L ^ 2) / L := by rw [hnorm_exact]

theorem branchHess_le_gradient_sq_of_minimizing
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
    let q := intrinsicGeodesic (I := I) g hEnorm p (L • u) 1
    hessFun (I := I) g (branchRadius (I := I) g B) q Y Y ≤
      (g.inner q Y Y -
        (g.inner q Y (gradientFun (I := I) g (branchRadius (I := I) g B) q)) ^ 2) / L := by
  dsimp only
  let q := intrinsicGeodesic (I := I) g hEnorm p (L • u) 1
  let V := curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm p (L • u)) 1
  have hv : 0 < g.inner p (L • u) (L • u) := by
    rw [gInner_smul_self (I := I) g p L u, hu]
    positivity
  have hroot : Real.sqrt (g.inner p (L • u) (L • u)) = L := by
    rw [sqrt_gInner_smul_self (I := I) g p hL.le u, hu, Real.sqrt_one, mul_one]
  have hgrad : gradientFun (I := I) g (branchRadius (I := I) g B) q = L⁻¹ • V := by
    have h := grad_branchRadius (I := I) B hsrc hv
    rw [hroot] at h
    convert! h using 1
  have hpair : g.inner q Y (gradientFun (I := I) g (branchRadius (I := I) g B) q) =
      g.inner q V Y / L := by
    rw [hgrad, map_smul, smul_eq_mul, g.symm q Y V, div_eq_inv_mul]
  have h := branchHess_le_perpendicular_sq_of_minimizing
    g hEnorm p u L B hL hu hsrc hmin hsec Y
  change hessFun (I := I) g (branchRadius (I := I) g B) q Y Y ≤
    (g.inner q Y Y - (g.inner q Y
      (gradientFun (I := I) g (branchRadius (I := I) g B) q)) ^ 2) / L
  rw [hpair, div_pow]
  exact h

end DifferentialGeometry.Geometry.Topology

end
