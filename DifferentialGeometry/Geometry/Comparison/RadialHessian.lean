import DifferentialGeometry.Analysis.ODE.IndexForm
import DifferentialGeometry.Geometry.Comparison.RadialLaplacian
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrameIndex
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariationMinimiser
import DifferentialGeometry.Geometry.Comparison.Variation.VariationFieldSmooth
import DifferentialGeometry.Geometry.Connection.ParallelTransport.SmoothAlongExpansion
import DifferentialGeometry.Geometry.Curvature.CoordRm04Bridge
import DifferentialGeometry.Geometry.Curvature.SectionalCone

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
    (p : M) (B : ExpInvBranch (I := I) g hEnorm p)
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
    rw [show q = B.hom uE from B.hom_eq hu]
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
      (show TangentSpace I p from v)
  have hexpFun : expOld = expf := by
    funext v
    simp only [expOld, expf, eP,
      tangentSpaceModelContinuousLinearEquiv_symm_apply]
  have hcurve :
      (fun s : Real => intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from uE + s • dInv) 1) =
        fun s => intrinsicGeodesic (I := I) g hEnorm p
          (u + s • w) 1 := by
    funext s
    congr 2
  have hj := intrinsic_jacobi_one (I := I) g hEnorm p uE dInv
  change
    mfderiv 𝓘(Real, Real) I
        (fun s : Real => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from uE + s • dInv) 1)
        0 (1 : Real) =
      mfderiv 𝓘(Real, E) I expOld uE
        (show TangentSpace 𝓘(Real, E) uE from dInv) at hj
  rw [hexpFun] at hj
  have hdir :
      (show TangentSpace 𝓘(Real, E) uE from dInv) = eU.symm dInv := by
    with_unfolding_all rfl
  have hrhs :
      mfderiv 𝓘(Real, E) I expf uE
          (show TangentSpace 𝓘(Real, E) uE from dInv) = Y := by
    rw [hdir]
    exact hexp
  rw [hrhs] at hj
  rw [hcurve] at hj
  with_unfolding_all exact hj

private theorem intrinsicJacobi_endpoint_deriv_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u w : TangentSpace I p) (L : Real)
    (hL : 0 < L)
    (hu : g.inner p u u = 1)
    (huw : g.inner p u w = 0)
    (hmin : ∀ η : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 η (Set.Icc 0 L) →
      η 0 = p →
      η L = intrinsicGeodesic (I := I) g hEnorm p u L →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u) 0 L ≤
        arcLength (I := I) g η 0 L)
    (hsec : ∀ t ∈ Set.Icc (0 : Real) L,
      ∀ Z : TangentSpace I
          (intrinsicGeodesic (I := I) g hEnorm p u t),
        0 ≤ metricRm04StdAt (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u t) Z
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t) Z) :
    let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
    let J := intrinsicJacobi (I := I) g hEnorm p u w
    g.inner (γ L) (covDerivAlong (I := I) g γ J L) (J L) ≤
      g.inner (γ L) (J L) (J L) / L := by
  classical
  dsimp only
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  let J : ∀ t, TangentSpace I (γ t) :=
    intrinsicJacobi (I := I) g hEnorm p u w
  let DJ : ∀ t, TangentSpace I (γ t) :=
    fun t => covDerivAlong (I := I) g γ J t
  have hγ_smooth : ContMDiff 𝓘(Real, Real) I ∞ γ := by
    apply contMDiffOn_univ.mp
    refine Geodesic.isGeodesicOn_contMDiffOn_infty
      (I := I) g isOpen_univ ?_ ?_
    · exact
        (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u).isGeodesicOn
          Set.univ
    · exact
        (intrinsicGeodesic_continuous (I := I) g hEnorm p u).continuousOn
  have hgeo : Geodesic.IsGeodesic (I := I) g γ := by
    simpa only [γ] using
      intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u
  have hUnit : ∀ t ∈ Set.Icc (0 : Real) L,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) = 1 := by
    intro t _
    exact (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u t).trans hu
  have hJdiff : ∀ t, DifferentiableAt Real
      (chartRepAt (I := I) γ J t) t := by
    intro t
    simpa only [γ, J] using
      (intrJacobi_diff (I := I) g hEnorm p u w t).1
  have hDJdiff : ∀ t, DifferentiableAt Real
      (chartRepAt (I := I) γ DJ t) t := by
    intro t
    simpa only [γ, J, DJ] using
      (intrJacobi_diff (I := I) g hEnorm p u w t).2
  have hJac : IsJacobiAlong (I := I) g γ J := by
    rw [show γ = fun t =>
      intrinsicGeodesic (I := I) g hEnorm p u t by rfl]
    with_unfolding_all exact
      (intrinsic_jacobi (I := I) g hEnorm p (u : E) (w : E))
  have hJ0 : J 0 = 0 := by
    simpa only [γ, J] using
      intrinsicJacobi_zero (I := I) g hEnorm p u w
  have hJperp : ∀ t,
      g.inner (γ t) (J t) (curveVelocity (I := I) γ t) = 0 := by
    intro t
    by_cases ht : t = 0
    · subst t
      rw [hJ0]
      simp
    · rw [g.symm (γ t) (J t) (curveVelocity (I := I) γ t)]
      simpa only [γ, J] using
        intrJacobi_perp_ne (I := I) g hEnorm p u w ht huw
  let f : Real → Real → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from (u : E) + s • (w : E)) t
  have hf : IsSmoothVariation (I := I) f := by
    change ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : Nat)
      (fun q : Real × Real =>
        intrinsicGeodesic (I := I) g hEnorm p (u + q.1 • w) q.2)
    with_unfolding_all exact
      ((intrinsicVar_smooth (I := I) g hEnorm p (u : E) (w : E)).of_le
        ENat.LEInfty.out)
  have hf_infty : ContMDiff
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I ∞
      (fun q : Real × Real => f q.1 q.2) := by
    with_unfolding_all exact
      (intrinsicVar_smooth (I := I) g hEnorm p (u : E) (w : E))
  have hJ_bundle : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (J t)) := by
    have hbase : (fun t => f 0 t) = γ := by
      funext t
      simp only [f, γ, zero_smul, add_zero]
    have hfield :
        (fun t => mfderiv 𝓘(Real, Real) I (fun s => f s t) 0 (1 : Real)) =
          J := by
      funext t
      with_unfolding_all rfl
    have hraw := varField_smooth (I := I) f hf_infty
    refine hraw.congr fun t => ?_
    refine TotalSpace.ext (congrFun hbase t).symm ?_
    exact heq_of_eq (congrFun hfield t).symm
  have hUnit0 :
      g.inner (γ 0) (curveVelocity (I := I) γ 0)
        (curveVelocity (I := I) γ 0) = 1 :=
    hUnit 0 ⟨le_rfl, hL.le⟩
  obtain ⟨F, hFdiff, hFpar, hFON, hFperp, hFbundle⟩ :=
    exists_parallel_perp_frame (I := I) g γ hγ_smooth hL
      (hgeo.isGeodesicOn (Set.Icc 0 L)) hUnit0
  let e : Fin (Module.finrank Real E - 1) →
      ∀ t, TangentSpace I (γ t) := fun i => (F i).toFun
  let R : Real →
      EuclideanSpace Real (Fin (Module.finrank Real E - 1)) →L[Real]
        EuclideanSpace Real (Fin (Module.finrank Real E - 1)) :=
    perpCurvOp (I := I) g γ e
  let y : Real → EuclideanSpace Real (Fin (Module.finrank Real E - 1)) :=
    perpCoeff (I := I) g e J
  let v : Real → EuclideanSpace Real (Fin (Module.finrank Real E - 1)) :=
    perpCoeff (I := I) g e DJ
  have hspeed (t : Real) (ht : t ∈ Set.Icc (0 : Real) L) :
      0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) := by
    rw [hUnit t ht]
    exact zero_lt_one
  have hode (t : Real) (ht : t ∈ Set.Icc (0 : Real) L) :
      HasDerivAt y (v t) t ∧
        HasDerivAt v (-(R t) (y t)) t := by
    simpa only [y, v, R, e, DJ] using
      perpCoeff_ode (I := I) (n := ∞) (by simp) g γ e J t
        hγ_smooth.contMDiffAt
        (fun i => hFdiff i t ht)
        (hJdiff t) (hDJdiff t)
        (fun i => hFpar i t ht)
        (hJac t) (by simp) (hspeed t ht)
        (fun i => hFperp t ht i)
        (hJperp t) (fun i j => hFON t ht i j)
  have hsol : DifferentialGeometry.Analysis.ODE.IsJacobiSolOn R 0 L y v :=
    { deriv_fst := fun t ht => (hode t ht).1.hasDerivWithinAt
      deriv_snd := fun t ht => (hode t ht).2.hasDerivWithinAt }
  have hR_smooth : ContDiff Real ∞ R := by
    simpa only [R, e] using
      perpCurv_smooth (I := I) g γ hγ_smooth e
        (fun i => hFbundle i)
  have hR_symm : ∀ t, ∀ a b :
      EuclideanSpace Real (Fin (Module.finrank Real E - 1)),
      inner Real (R t a) b = inner Real a (R t b) := by
    intro t a b
    simpa only [R, e] using
      perpCurv_symm (I := I) g γ e t a b
  have hy_smooth : ContDiff Real ∞ y := by
    simpa only [y, e] using
      perpCoeff_smooth (I := I) g e J
        (fun i => hFbundle i) hJ_bundle
  have hy0 : y 0 = 0 := by
    exact perpCoeff_zero (I := I) g e J 0 hJ0
  let c : EuclideanSpace Real (Fin (Module.finrank Real E - 1)) := y L
  let z : Real → EuclideanSpace Real (Fin (Module.finrank Real E - 1)) :=
    fun t => (t / L) • c
  let dz : Real → EuclideanSpace Real (Fin (Module.finrank Real E - 1)) :=
    fun _ => (1 / L) • c
  have hz_deriv (t : Real) : HasDerivAt z (dz t) t := by
    let T :
        (Fin (Module.finrank Real E - 1) → Real) ≃L[Real]
          EuclideanSpace Real (Fin (Module.finrank Real E - 1)) :=
      (EuclideanSpace.equiv _ _).symm
    have hpi : HasDerivAt
        (fun s : Real => fun i => (s / L) * c i)
        (fun i => (1 / L) * c i) t := by
      rw [hasDerivAt_pi]
      intro i
      simpa using ((hasDerivAt_id t).div_const L).mul_const (c i)
    have hT := T.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hpi
    change HasDerivAt
      ((fun q => T q) ∘ fun s : Real => fun i => (s / L) * c i)
      (T (fun i => (1 / L) * c i)) t at hT
    have hfun :
        ((fun q => T q) ∘ fun s : Real => fun i => (s / L) * c i) =
          fun s => (s / L) • c := by
      funext s
      apply (EuclideanSpace.equiv _ _).injective
      ext i
      change s / L * c i = ((s / L) • c :
        EuclideanSpace Real (Fin (Module.finrank Real E - 1))) i
      rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    have hval : T (fun i => (1 / L) * c i) = (1 / L) • c := by
      apply (EuclideanSpace.equiv _ _).injective
      ext i
      change 1 / L * c i = ((1 / L) • c :
        EuclideanSpace Real (Fin (Module.finrank Real E - 1))) i
      rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [hfun, hval] at hT
    simpa only [z, dz] using hT
  have hz_smooth : ContDiff Real ∞ z := by
    exact (contDiff_id.div_const L).smul contDiff_const
  have hdz_smooth : ContDiff Real ∞ dz := by
    exact contDiff_const
  have hz0 : z 0 = y 0 := by
    rw [hy0]
    simp [z]
  have hzL : z L = y L := by
    change (L / L) • c = y L
    rw [div_self hL.ne', one_smul]
  let d := z - y
  let de := dz - v
  have hd_smooth : ContDiff Real ∞ d := hz_smooth.sub hy_smooth
  have hd_deriv (t : Real) (ht : t ∈ Set.Icc (0 : Real) L) :
      HasDerivAt d (de t) t := by
    exact (hz_deriv t).sub (hode t ht).1
  let D : ∀ t, TangentSpace I (γ t) :=
    fun t => perpFrameLift (I := I) e d t
  have hD_bundle : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (D t)) := by
    simpa only [D] using
      perpLift_smooth (I := I) hγ_smooth e d hd_smooth
        (fun i => hFbundle i)
  have hDperp : ∀ t ∈ Set.Icc (0 : Real) L,
      g.inner (γ t) (D t) (curveVelocity (I := I) γ t) = 0 := by
    intro t ht
    exact perpLift_perp (I := I) g e d t
      (curveVelocity (I := I) γ t) (fun i => hFperp t ht i)
  have hd0 : d 0 = 0 := by
    dsimp only [d]
    exact sub_eq_zero.mpr hz0
  have hdL : d L = 0 := by
    dsimp only [d]
    exact sub_eq_zero.mpr hzL
  have hD0 : D 0 = 0 :=
    perpLift_zero (I := I) e d 0 hd0
  have hDL : D L = 0 :=
    perpLift_zero (I := I) e d L hdL
  have hD_nonneg : 0 ≤ indexForm (I := I) g γ 0 L D D :=
    indexForm_nonneg_of_minimising_geodesic
      (I := I) g hEnorm γ L D hL hγ_smooth hD_bundle
      (hgeo.isGeodesicOn (Set.Icc 0 L))
      (by
        intro η hη hη0 hηL
        apply hmin η hη
        · simpa only [γ, intrinsicGeodesic_zero] using hη0
        · simpa only [γ] using hηL)
      hUnit hDperp hD0 hDL
  have hindex_D := perpLift_indexForm (I := I) g γ e d d 0 L
    (fun t _ => hd_smooth.differentiable (by simp) t)
    (fun t _ => hd_smooth.differentiable (by simp) t)
    (fun i t ht => hFdiff i t (by simpa [Set.uIcc_of_le hL.le] using ht))
    (fun i t ht => hFpar i t (by simpa [Set.uIcc_of_le hL.le] using ht))
    (fun t ht i j => hFON t (by simpa [Set.uIcc_of_le hL.le] using ht) i j)
  have hderiv_d : ∀ t ∈ Set.Icc (0 : Real) L, deriv d t = de t := by
    intro t ht
    exact (hd_deriv t ht).deriv
  have hindex_deriv :
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L d (deriv d) d (deriv d) =
        DifferentialGeometry.Analysis.ODE.indexForm R 0 L d de d de := by
    rw [DifferentialGeometry.Analysis.ODE.indexForm_def,
      DifferentialGeometry.Analysis.ODE.indexForm_def]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hL.le] at ht
    simp only [DifferentialGeometry.Analysis.ODE.indexIntegrand,
      hderiv_d t ht]
  have hsub : 0 ≤
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L d de d de := by
    rw [hindex_D, hindex_deriv] at hD_nonneg
    exact hD_nonneg
  have hindex_le :
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L y v y v ≤
        DifferentialGeometry.Analysis.ODE.indexForm R 0 L z dz z dz := by
    exact hsol.indexForm_le hL.le hR_smooth.continuous.continuousOn
      hR_symm
      (fun t ht => (hz_deriv t).hasDerivWithinAt)
      hdz_smooth.continuous.continuousOn hz0 hzL hsub
  have hindex_y :
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L y v y v =
        inner Real (v L) (y L) := by
    rw [hsol.indexForm_eq_sub hL.le hR_smooth.continuous.continuousOn
      hsol.deriv_fst hsol.contOn_snd, hy0]
    simp
  have hcurv_nonneg (t : Real) (ht : t ∈ Set.Icc (0 : Real) L) :
      0 ≤ inner Real (R t (z t)) (z t) := by
    rw [perpCurv_inner (I := I) g γ e (z t) (z t) t]
    change 0 ≤ g.inner (γ t)
      ((riemannOp (LeviCivita (I := I) g) (γ t))
        (perpFrameLift (I := I) e z t)
        (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t))
      (perpFrameLift (I := I) e z t)
    rw [g.symm (γ t)]
    rw [← rm04_eq_inner_riem (I := I) g (γ t)
      (perpFrameLift (I := I) e z t) (curveVelocity (I := I) γ t)
      (curveVelocity (I := I) γ t) (perpFrameLift (I := I) e z t)]
    exact hsec t ht (perpFrameLift (I := I) e z t)
  have hindex_z :
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L z dz z dz ≤
        inner Real c c / L := by
    rw [DifferentialGeometry.Analysis.ODE.indexForm_def]
    have hint : IntervalIntegrable
        (DifferentialGeometry.Analysis.ODE.indexIntegrand R z dz z dz)
        MeasureTheory.volume 0 L :=
      DifferentialGeometry.Analysis.ODE.intInt_indexIntegrand
        (by simpa [Set.uIcc_of_le hL.le] using
          hR_smooth.continuous.continuousOn)
        (by simpa [Set.uIcc_of_le hL.le] using
          hz_smooth.continuous.continuousOn)
        (by simpa [Set.uIcc_of_le hL.le] using
          hdz_smooth.continuous.continuousOn)
        (by simpa [Set.uIcc_of_le hL.le] using
          hz_smooth.continuous.continuousOn)
        (by simpa [Set.uIcc_of_le hL.le] using
          hdz_smooth.continuous.continuousOn)
    have hmono := intervalIntegral.integral_mono_on hL.le hint
      intervalIntegrable_const (fun t ht => by
        rw [DifferentialGeometry.Analysis.ODE.indexIntegrand]
        have hcurv := hcurv_nonneg t ht
        dsimp only [dz]
        rw [real_inner_smul_left, real_inner_smul_right]
        exact sub_le_self _ hcurv)
    rw [intervalIntegral.integral_const, sub_zero] at hmono
    simp only [smul_eq_mul] at hmono
    have hcalc : L * ((1 / L) * ((1 / L) * inner Real c c)) =
        inner Real c c / L := by
      field_simp [hL.ne']
    rw [hcalc] at hmono
    exact hmono
  have hcoeff_le : inner Real (v L) (y L) ≤ inner Real c c / L := by
    rw [← hindex_y]
    exact hindex_le.trans hindex_z
  have hJLperp :
      g.inner (γ L) (J L) (curveVelocity (I := I) γ L) = 0 :=
    hJperp L
  have hDJLperp :
      g.inner (γ L) (DJ L) (curveVelocity (I := I) γ L) = 0 := by
    rw [g.symm (γ L)]
    simpa only [γ, J, DJ] using
      intrJacobi_dperp (I := I) g hEnorm p u w hL.ne' huw
  have hJ_expand : perpFrameLift (I := I) e y L = J L :=
    perpLift_coeff (I := I) g e J L (by simp)
      (hspeed L ⟨hL.le, le_rfl⟩)
      (fun i => hFperp L ⟨hL.le, le_rfl⟩ i) hJLperp
      (fun i j => hFON L ⟨hL.le, le_rfl⟩ i j)
  have hDJ_expand : perpFrameLift (I := I) e v L = DJ L :=
    perpLift_coeff (I := I) g e DJ L (by simp)
      (hspeed L ⟨hL.le, le_rfl⟩)
      (fun i => hFperp L ⟨hL.le, le_rfl⟩ i) hDJLperp
      (fun i j => hFON L ⟨hL.le, le_rfl⟩ i j)
  have hinner_coeff :
      g.inner (γ L) (DJ L) (J L) = inner Real (v L) (y L) := by
    rw [← hDJ_expand, ← hJ_expand]
    exact perpLift_inner (I := I) g e (v L) (y L) L
      (fun i j => hFON L ⟨hL.le, le_rfl⟩ i j)
  have hnorm_coeff :
      g.inner (γ L) (J L) (J L) = inner Real c c := by
    rw [← hJ_expand]
    dsimp only [c]
    exact perpLift_inner (I := I) g e (y L) (y L) L
      (fun i j => hFON L ⟨hL.le, le_rfl⟩ i j)
  rw [hinner_coeff, hnorm_coeff]
  exact hcoeff_le

private theorem branchHess_perp_le_of_minimizing
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (L : Real)
    (B : ExpInvBranch (I := I) g hEnorm p)
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
      ∀ Z : TangentSpace I
          (intrinsicGeodesic (I := I) g hEnorm p u t),
        0 ≤ metricRm04StdAt (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u t) Z
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t) Z)
    (Y : TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1))
    (hYperp : g.inner
      (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1)
      (curveVelocity (I := I)
        (intrinsicGeodesic (I := I) g hEnorm p (L • u)) 1) Y = 0) :
    hessFun (I := I) g (branchRadius (I := I) g B)
        (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y ≤
      g.inner (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y / L := by
  let uL : TangentSpace I p := L • u
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  let γL : Real → M := intrinsicGeodesic (I := I) g hEnorm p uL
  have hsrc' : tangentSpaceModelContinuousLinearEquiv (I := I) p uL ∈
      B.hom.source := by
    simpa only [uL] using hsrc
  obtain ⟨W, hW⟩ :=
    exists_intrinsicJacobi_one_eq (I := I) g hEnorm p B hsrc' Y
  have hGauss := intrinsicJacobi_perp (I := I) g hEnorm p uL W
  have hGauss' :
      g.inner (intrinsicGeodesic (I := I) g hEnorm p uL 1)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p uL) 1)
          (intrinsicJacobi (I := I) g hEnorm p uL W 1) =
        g.inner p uL W := by
    with_unfolding_all exact hGauss
  have huLW : g.inner p uL W = 0 := by
    rw [hW, hYperp] at hGauss'
    exact hGauss'.symm
  have huW : g.inner p u W = 0 := by
    have hscaled : L * g.inner p u W = 0 := by
      simpa only [uL, map_smul, smul_apply, smul_eq_mul] using huLW
    exact (mul_eq_zero.mp hscaled).resolve_left hL.ne'
  let w : TangentSpace I p := L⁻¹ • W
  have hLw : L • w = W := by
    dsimp only [w]
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have huw : g.inner p u w = 0 := by
    dsimp only [w]
    rw [map_smul (g.inner p u), smul_eq_mul, huW, mul_zero]
  let J : ∀ t, TangentSpace I (γ t) :=
    intrinsicJacobi (I := I) g hEnorm p u w
  let JL : ∀ t, TangentSpace I (γL t) :=
    intrinsicJacobi (I := I) g hEnorm p uL W
  have hγscale (t : Real) : γL t = γ (L * t) := by
    dsimp only [γL, γ, uL]
    rw [← intrinsicGeodesic_smul (I := I) g hEnorm p u (L * t)]
    rw [← intrinsicGeodesic_smul (I := I) g hEnorm p (L • u) t]
    apply congrArg (fun v : TangentSpace I p =>
      intrinsicGeodesic (I := I) g hEnorm p v 1)
    module
  have hJLscale (t : Real) : @Eq E (JL t : E) (J (L * t) : E) := by
    have hscale := intrinsicJacobi_smul (I := I) g hEnorm p u w L t
    rw [hLw] at hscale
    with_unfolding_all exact hscale
  have hDJscale :
      @Eq E (covDerivAlong (I := I) g γL JL 1 : E)
        (L • covDerivAlong (I := I) g γ J L : E) := by
    have hcong := covDerivAlong_congr_curve (I := I) (t := (1 : Real)) g JL
      (fun t => J (L * t))
      (Filter.Eventually.of_forall hγscale)
      (Filter.Eventually.of_forall hJLscale)
    have hcomp := covDeriv_comp_mul (I := I) g γ J L 1
    rw [mul_one] at hcomp
    exact hcong.trans hcomp
  have hJLone : JL 1 = Y := by
    simpa only [JL] using hW
  have hJoneScale : @Eq E (JL 1 : E) (J L : E) := by
    have hscale := hJLscale 1
    rw [mul_one] at hscale
    exact hscale
  have hq : γL 1 = γ L := by
    simpa only [mul_one] using hγscale 1
  have hindex := intrinsicJacobi_endpoint_deriv_le
    (I := I) g hEnorm p u w L hL hu huw hmin hsec
  have huL_pos : 0 < g.inner p uL uL := by
    dsimp only [uL]
    rw [gInner_smul_self (I := I) g p L u, hu]
    positivity
  have hroot : Real.sqrt (g.inner p uL uL) = L := by
    dsimp only [uL]
    rw [sqrt_gInner_smul_self (I := I) g p hL.le u, hu, Real.sqrt_one,
      mul_one]
  have hshape := branchHess_shape (I := I) B hsrc' huL_pos
    (w₁ := W) (w₂ := W) huLW huLW
  dsimp only at hshape
  rw [show intrinsicGeodesic (I := I) g hEnorm p uL = γL by rfl] at hshape
  rw [show intrinsicJacobi (I := I) g hEnorm p uL W = JL by rfl] at hshape
  rw [hroot] at hshape
  have hleft :
      g.inner (γL 1) (covDerivAlong (I := I) g γL JL 1) (JL 1) / L =
        g.inner (γ L) (covDerivAlong (I := I) g γ J L) (J L) := by
    rw [hq]
    rw [hDJscale, hJoneScale]
    rw [map_smul (g.inner (γ L)), smul_apply, smul_eq_mul,
      mul_div_cancel_left₀ _ hL.ne']
  have hright :
      g.inner (γL 1) (JL 1) (JL 1) / L =
        g.inner (γ L) (J L) (J L) / L := by
    rw [hq, hJoneScale]
  rw [← hJLone, hshape, hleft, hright]
  exact hindex

private theorem branchHess_perp_radial_eq_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p)
    (B : ExpInvBranch (I := I) g hEnorm p)
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
      intrJacobi_dperp (I := I) g hEnorm p v w one_ne_zero hvw
  have hshape := branchHess_jacobi (I := I) B hsrc hv
    (w₁ := w) (w₂ := v)
  dsimp only at hshape
  rw [show intrinsicGeodesic (I := I) g hEnorm p v = γ by rfl] at hshape
  rw [show intrinsicJacobi (I := I) g hEnorm p v w = J w by rfl] at hshape
  rw [intrJacobi_self (I := I) g hEnorm p v, hDperp, hvw,
    zero_div, zero_mul, zero_div, sub_zero] at hshape
  rw [← hw]
  simpa only [γ, J] using hshape

private theorem branchHess_symm
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p)
    (B : ExpInvBranch (I := I) g hEnorm p)
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

theorem branchHess_le_of_minimizing_of_sectional_curvature_nonnegative
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (L : Real)
    (B : ExpInvBranch (I := I) g hEnorm p)
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
      g.inner (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y / L := by
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
  have hVpos : 0 < g.inner q V V := hVsq.symm ▸ sq_pos_of_pos hL
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
        0 ≤ metricRm04StdAt (I := I) g
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
  have hnorm_le : g.inner q Z Z ≤ g.inner q Y Y := by
    rw [hnorm]
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg a) hVpos.le)
  calc
    Hess Y Y = Hess Z Z := hHdecomp
    _ ≤ g.inner q Z Z / L := hZbound
    _ ≤ g.inner q Y Y / L := (div_le_div_iff_of_pos_right hL).2 hnorm_le

end Riemannian
end Geometry
end DifferentialGeometry

end
