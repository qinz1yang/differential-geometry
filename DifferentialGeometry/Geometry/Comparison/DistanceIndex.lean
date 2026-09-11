import DifferentialGeometry.Analysis.ODE.IndexForm.Basic
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AffineReparam
import DifferentialGeometry.Geometry.Comparison.Laplacian.Radial
import DifferentialGeometry.Geometry.Comparison.Variation.Field.Smoothness
import DifferentialGeometry.Geometry.Comparison.Variation.RicciIntegral

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

theorem intrinsicJacobi_endpoint_indexForm_le_of_minimizing
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
    (F : Fin (Module.finrank Real E - 1) →
      ∀ t : Real, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p u t))
    (hFdiff : ∀ i, ∀ t ∈ Set.Icc (0 : Real) L,
      DifferentiableAt Real (chartRepAt (I := I)
        (intrinsicGeodesic (I := I) g hEnorm p u) (F i) t) t)
    (hFpar : ∀ i, ∀ t ∈ Set.Icc (0 : Real) L,
      covDerivAlong (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u) (F i) t = 0)
    (hFON : ∀ t ∈ Set.Icc (0 : Real) L, ∀ i j,
      g.inner (intrinsicGeodesic (I := I) g hEnorm p u t) (F i t) (F j t) =
        if i = j then 1 else 0)
    (hFperp : ∀ t ∈ Set.Icc (0 : Real) L, ∀ i,
      g.inner (intrinsicGeodesic (I := I) g hEnorm p u t) (F i t)
        (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm p u) t) = 0)
    (hFbundle : ∀ i, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun t => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (intrinsicGeodesic (I := I) g hEnorm p u t) (F i t)))
    (φ : Real → Real) (hφ : ContDiff Real ∞ φ)
    (hφ0 : φ 0 = 0) (hφL : φ L = 1) :
    let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
    let J := intrinsicJacobi (I := I) g hEnorm p u w
    let c := perpCoeff (I := I) g F J L
    let V := fun s => perpFrameLift (I := I) F (fun q => φ q • c) s
    g.inner (γ L) (covDerivAlong (I := I) g γ J L) (J L) ≤
      indexForm (I := I) g γ 0 L V V := by
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
      (intrinsicJacobi_diff (I := I) g hEnorm p u w t).1
  have hDJdiff : ∀ t, DifferentiableAt Real
      (chartRepAt (I := I) γ DJ t) t := by
    intro t
    simpa only [γ, J, DJ] using
      (intrinsicJacobi_diff (I := I) g hEnorm p u w t).2
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
        intrinsicJacobi_perp_ne (I := I) g hEnorm p u w ht huw
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
  let e : Fin (Module.finrank Real E - 1) →
      ∀ t, TangentSpace I (γ t) := F
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
  have hsol : DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn R 0 L y v :=
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
    fun t => φ t • c
  let dz : Real → EuclideanSpace Real (Fin (Module.finrank Real E - 1)) :=
    fun t => deriv φ t • c
  have hz_deriv (t : Real) : HasDerivAt z (dz t) t :=
    (hφ.differentiable (by simp) t).hasDerivAt.smul_const c
  have hz_smooth : ContDiff Real ∞ z := hφ.smul_const c
  have hdz_smooth : ContDiff Real ∞ dz :=
    (contDiff_infty_iff_deriv.mp hφ).2.smul_const c
  have hz0 : z 0 = y 0 := by
    rw [hy0]
    simp only [z, hφ0, zero_smul]
  have hzL : z L = y L := by
    simp only [z, hφL, one_smul, c]
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
      (I := I) g γ L D hL.le
      (hD_bundle.of_le
        (show (8 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from ENat.LEInfty.out))
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
  have hJLperp :
      g.inner (γ L) (J L) (curveVelocity (I := I) γ L) = 0 :=
    hJperp L
  have hDJLperp :
      g.inner (γ L) (DJ L) (curveVelocity (I := I) γ L) = 0 := by
    rw [g.symm (γ L)]
    simpa only [γ, J, DJ] using
      intrinsicJacobi_dperp (I := I) g hEnorm p u w hL.ne' huw
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
  have hindex_z := perpLift_indexForm (I := I) g γ e z z 0 L
    (fun t _ => hz_smooth.differentiable (by simp) t)
    (fun t _ => hz_smooth.differentiable (by simp) t)
    (fun i t ht => hFdiff i t (by simpa [Set.uIcc_of_le hL.le] using ht))
    (fun i t ht => hFpar i t (by simpa [Set.uIcc_of_le hL.le] using ht))
    (fun t ht => hFON t (by simpa [Set.uIcc_of_le hL.le] using ht))
  have hdz : deriv z = dz := funext fun t => (hz_deriv t).deriv
  rw [hdz] at hindex_z
  change g.inner (γ L) (DJ L) (J L) ≤
    indexForm (I := I) g γ 0 L
      (fun t => perpFrameLift (I := I) e z t)
      (fun t => perpFrameLift (I := I) e z t)
  rw [hinner_coeff, hindex_z, ← hindex_y]
  exact hindex_le

private theorem sum_intrinsicJacobi_endpoint_deriv_le_weighted_ricci
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p)
    (w : Fin (Module.finrank Real E - 1) → TangentSpace I p) (L : Real)
    (hL : 0 < L)
    (hu : g.inner p u u = 1)
    (huw : ∀ i, g.inner p u (w i) = 0)
    (hmin : ∀ η : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 η (Set.Icc 0 L) →
      η 0 = p →
      η L = intrinsicGeodesic (I := I) g hEnorm p u L →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u) 0 L ≤
        arcLength (I := I) g η 0 L)
    (F : Fin (Module.finrank Real E - 1) →
      ∀ t : Real, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p u t))
    (hFdiff : ∀ i, ∀ t ∈ Set.Icc (0 : Real) L,
      DifferentiableAt Real (chartRepAt (I := I)
        (intrinsicGeodesic (I := I) g hEnorm p u) (F i) t) t)
    (hFpar : ∀ i, ∀ t ∈ Set.Icc (0 : Real) L,
      covDerivAlong (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u) (F i) t = 0)
    (hFON : ∀ t ∈ Set.Icc (0 : Real) L, ∀ i j,
      g.inner (intrinsicGeodesic (I := I) g hEnorm p u t) (F i t) (F j t) =
        if i = j then 1 else 0)
    (hFperp : ∀ t ∈ Set.Icc (0 : Real) L, ∀ i,
      g.inner (intrinsicGeodesic (I := I) g hEnorm p u t) (F i t)
        (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm p u) t) = 0)
    (hFbundle : ∀ i, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun t => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (intrinsicGeodesic (I := I) g hEnorm p u t) (F i t)))
    (hJ : ∀ i, intrinsicJacobi (I := I) g hEnorm p u (w i) L = F i L)
    (φ : Real → Real) (hφ : ContDiff Real ∞ φ)
    (hφ0 : φ 0 = 0) (hφL : φ L = 1) :
    let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
    let J := fun i => intrinsicJacobi (I := I) g hEnorm p u (w i)
    (∑ i, g.inner (γ L) (covDerivAlong (I := I) g γ (J i) L) (J i L)) ≤
      ∫ t in (0 : Real)..L,
        ((Module.finrank Real E - 1 : Real) * deriv φ t ^ 2 -
          φ t ^ 2 * ricciTensor (I := I) g (γ t)
            (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) := by
  classical
  dsimp only
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  let J := fun i => intrinsicJacobi (I := I) g hEnorm p u (w i)
  let y : Fin (Module.finrank Real E - 1) →
      Real → EuclideanSpace Real (Fin (Module.finrank Real E - 1)) :=
    fun i t => φ t • EuclideanSpace.single i (1 : Real)
  let dy : Fin (Module.finrank Real E - 1) →
      Real → EuclideanSpace Real (Fin (Module.finrank Real E - 1)) :=
    fun i t => deriv φ t • EuclideanSpace.single i (1 : Real)
  have hy (i) : ContDiff Real ∞ (y i) := hφ.smul_const _
  have hdy (i) : ContDiff Real ∞ (dy i) :=
    (contDiff_infty_iff_deriv.mp hφ).2.smul_const _
  have hyder (i) : deriv (y i) = dy i := by
    funext t
    exact ((hφ.differentiable (by simp) t).hasDerivAt.smul_const _).deriv
  have hcoeff (i) : perpCoeff (I := I) g F (J i) L =
      EuclideanSpace.single i (1 : Real) := by
    ext j
    simp only [perpCoeff_apply, J, hJ, hFON L ⟨hL.le, le_rfl⟩]
    simp [eq_comm]
  have hbound (i) :
      g.inner (γ L) (covDerivAlong (I := I) g γ (J i) L) (J i L) ≤
        DifferentialGeometry.Analysis.ODE.indexForm
          (perpCurvOp (I := I) g γ F) 0 L (y i) (dy i) (y i) (dy i) := by
    have h := intrinsicJacobi_endpoint_indexForm_le_of_minimizing
      (I := I) g hEnorm p u (w i) L hL hu (huw i) hmin
      F hFdiff hFpar hFON hFperp hFbundle φ hφ hφ0 hφL
    dsimp only at h
    change g.inner (γ L) (covDerivAlong (I := I) g γ (J i) L) (J i L) ≤
      indexForm (I := I) g γ 0 L
        (fun t => perpFrameLift (I := I) F
          (fun q => φ q • perpCoeff (I := I) g F (J i) L) t)
        (fun t => perpFrameLift (I := I) F
          (fun q => φ q • perpCoeff (I := I) g F (J i) L) t) at h
    rw [hcoeff i] at h
    have hidx := perpLift_indexForm (I := I) g γ F (y i) (y i) 0 L
      (fun t _ => (hy i).differentiable (by simp) t)
      (fun t _ => (hy i).differentiable (by simp) t)
      (fun j t ht => hFdiff j t (by simpa [Set.uIcc_of_le hL.le] using ht))
      (fun j t ht => hFpar j t (by simpa [Set.uIcc_of_le hL.le] using ht))
      (fun t ht => hFON t (by simpa [Set.uIcc_of_le hL.le] using ht))
    rw [hyder i] at hidx
    exact h.trans_eq hidx
  have hγ : ContMDiff 𝓘(Real, Real) I ∞ γ :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hR : ContDiff Real ∞ (perpCurvOp (I := I) g γ F) :=
    perpCurv_smooth (I := I) g γ hγ F hFbundle
  have hint (i) : IntervalIntegrable
      (DifferentialGeometry.Analysis.ODE.indexIntegrand
        (perpCurvOp (I := I) g γ F) (y i) (dy i) (y i) (dy i))
      MeasureTheory.volume 0 L :=
    DifferentialGeometry.Analysis.ODE.intInt_indexIntegrand
      hR.continuous.continuousOn (hy i).continuous.continuousOn
      (hdy i).continuous.continuousOn (hy i).continuous.continuousOn
      (hdy i).continuous.continuousOn
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hbound i)
  apply hsum.trans_eq
  simp only [DifferentialGeometry.Analysis.ODE.indexForm_def]
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hint i)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : Real) L := by simpa [uIcc_of_le hL.le] using ht
  have hunit : g.inner (γ t) (curveVelocity (I := I) γ t)
      (curveVelocity (I := I) γ t) = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u t).trans hu
  simpa only [y, dy, γ, curveVelocity, DifferentialGeometry.Analysis.ODE.indexIntegrand] using
    sum_indexIntegrand_eq_weighted_ricci (I := I) g γ F t (φ t) (deriv φ t)
      hunit (hFON t ht') (hFperp t ht')

theorem branchHess_intrinsicJacobi_eq_endpoint
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u w : TangentSpace I p) (L : Real)
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (hL : 0 < L) (hu : g.inner p u u = 1)
    (hsrc : tangentSpaceModelContinuousLinearEquiv (I := I) p (L • u) ∈ B.hom.source)
    (huw : g.inner p u w = 0) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let J := intrinsicJacobi (I := I) g hEnorm p u w
    hessFun (I := I) g (branchRadius (I := I) g B) (γ L) (J L) (J L) =
      g.inner (γ L) (covDerivAlong (I := I) g γ J L) (J L) := by
  let uL : TangentSpace I p := L • u
  let W : TangentSpace I p := L • w
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  let γL : Real → M := intrinsicGeodesic (I := I) g hEnorm p uL
  let J : ∀ t, TangentSpace I (γ t) := intrinsicJacobi (I := I) g hEnorm p u w
  let JL : ∀ t, TangentSpace I (γL t) := intrinsicJacobi (I := I) g hEnorm p uL W
  have hsrc' : tangentSpaceModelContinuousLinearEquiv (I := I) p uL ∈ B.hom.source := hsrc
  have huLW : g.inner p uL W = 0 := by
    simp only [uL, W, map_smul, smul_apply, smul_eq_mul, huw, mul_zero]
  have hγscale (t : Real) : γL t = γ (L * t) := by
    dsimp only [γL, γ, uL]
    rw [← intrinsicGeodesic_smul (I := I) g hEnorm p u (L * t)]
    rw [← intrinsicGeodesic_smul (I := I) g hEnorm p (L • u) t]
    apply congrArg (fun v : TangentSpace I p => intrinsicGeodesic (I := I) g hEnorm p v 1)
    module
  have hJLscale (t : Real) : @Eq E (JL t : E) (J (L * t) : E) := by
    with_unfolding_all exact intrinsicJacobi_smul (I := I) g hEnorm p u w L t
  have hDJscale : @Eq E (covDerivAlong (I := I) g γL JL 1 : E)
      (L • covDerivAlong (I := I) g γ J L : E) := by
    have hcong := covDerivAlong_congr_curve (I := I) (t := (1 : Real)) g JL
      (fun t => J (L * t))
      (Filter.Eventually.of_forall hγscale) (Filter.Eventually.of_forall hJLscale)
    have hcomp := covDeriv_comp_mul (I := I) g γ J L 1
    rw [mul_one] at hcomp
    exact hcong.trans hcomp
  have hJoneScale : @Eq E (JL 1 : E) (J L : E) := by
    have h := hJLscale 1
    rw [mul_one] at h
    exact h
  have hq : γL 1 = γ L := by simpa only [mul_one] using hγscale 1
  have huL_pos : 0 < g.inner p uL uL := by
    dsimp only [uL]
    rw [gInner_smul_self (I := I) g p L u, hu]
    positivity
  have hroot : Real.sqrt (g.inner p uL uL) = L := by
    dsimp only [uL]
    rw [sqrt_gInner_smul_self (I := I) g p hL.le u, hu, Real.sqrt_one, mul_one]
  have hshape := branchHess_shape (I := I) B hsrc' huL_pos
    (w₁ := W) (w₂ := W) huLW huLW
  dsimp only at hshape
  rw [show intrinsicGeodesic (I := I) g hEnorm p uL = γL by rfl] at hshape
  rw [show intrinsicJacobi (I := I) g hEnorm p uL W = JL by rfl] at hshape
  rw [hroot, hq, hJoneScale, hDJscale] at hshape
  simpa only [map_smul, smul_apply, smul_eq_mul,
    mul_div_cancel_left₀ _ hL.ne'] using hshape

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private theorem linIndep_ortho
    {ι : Type*} [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : ι → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    LinearIndependent Real v := by
  let b : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    { toFun := fun x => (g.inner p x).toLinearMap
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  apply LinearMap.linearIndependent_of_isOrthoᵢ (B := b)
  · intro i j hij
    change g.inner p (v i) (v j) = 0
    rw [hON i j, if_neg hij]
  · intro i
    change g.inner p (v i) (v i) ≠ 0
    simp [hON]


theorem branchLap_eq_sum_hessian_of_orthonormal_perp_frame
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p)
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (hsrc : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source)
    (hu : 0 < g.inner p u u)
    (F : Fin (Module.finrank Real E - 1) →
      TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p u 1))
    (hFON : ∀ i j, g.inner (intrinsicGeodesic (I := I) g hEnorm p u 1)
      (F i) (F j) = if i = j then 1 else 0)
    (hFperp : ∀ i, g.inner (intrinsicGeodesic (I := I) g hEnorm p u 1)
      (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm p u) 1) (F i) = 0) :
    laplacian (I := I) (LeviCivita (I := I) g) g (branchRadius (I := I) g B)
        (intrinsicGeodesic (I := I) g hEnorm p u 1) =
      ∑ i, hessFun (I := I) g (branchRadius (I := I) g B)
        (intrinsicGeodesic (I := I) g hEnorm p u 1) (F i) (F i) := by
  classical
  let γ := intrinsicGeodesic (I := I) g hEnorm p u
  let q := γ 1
  let Z : TangentSpace I q := curveVelocity (I := I) γ 1
  let Hess := hessTensorAt (I := I) g (branchRadius (I := I) g B) q
  obtain ⟨U, hUopen, hqU, hrU⟩ := branchRadius_open (I := I) B hsrc hu
  have hqU' : q ∈ U := by convert hqU using 1; rfl
  have hZ : 0 < g.inner q Z Z := by
    change 0 < g.inner (γ 1) (curveVelocity (I := I) γ 1) (curveVelocity (I := I) γ 1)
    exact (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u 1).symm ▸ hu
  have hsplit := Tensor.RSTensor.trace_eq_line_add (I := I) g Z F Hess
    hZ hFperp (linIndep_ortho (I := I) g q F hFON) (Fintype.card_fin _)
  have hradial : Hess (vec2 (I := I) Z Z) = 0 := by
    rw [hessTensorAt_apply]
    exact branchHess_radial (I := I) B hsrc hu
  have hGram : (Matrix.of fun i j => g.inner q (F i) (F j)) =
      (1 : Matrix (Fin (Module.finrank Real E - 1)) (Fin (Module.finrank Real E - 1)) Real) := by
    ext i j
    simpa only [Matrix.of_apply, Matrix.one_apply] using hFON i j
  have hlap := lap_eq_hess_on
    (I := I) g hUopen hrU hqU'
  rw [hlap]
  dsimp only at hsplit
  rw [hradial, mul_zero, zero_add, hGram, inv_one, Matrix.one_mul] at hsplit
  simpa only [Matrix.trace, Matrix.diag, Matrix.of_apply, Hess, hessTensorAt_apply] using hsplit

private theorem branchLap_le_weighted_ricci_of_minimizing
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p)
    (w : Fin (Module.finrank Real E - 1) → TangentSpace I p) (L : Real)
    (hL : 0 < L)
    (hu : g.inner p u u = 1)
    (huw : ∀ i, g.inner p u (w i) = 0)
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (hsrc : tangentSpaceModelContinuousLinearEquiv (I := I) p (L • u) ∈ B.hom.source)
    (hmin : ∀ η : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 η (Set.Icc 0 L) →
      η 0 = p →
      η L = intrinsicGeodesic (I := I) g hEnorm p u L →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u) 0 L ≤
        arcLength (I := I) g η 0 L)
    (F : Fin (Module.finrank Real E - 1) →
      ∀ t : Real, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p u t))
    (hFdiff : ∀ i, ∀ t ∈ Set.Icc (0 : Real) L,
      DifferentiableAt Real (chartRepAt (I := I)
        (intrinsicGeodesic (I := I) g hEnorm p u) (F i) t) t)
    (hFpar : ∀ i, ∀ t ∈ Set.Icc (0 : Real) L,
      covDerivAlong (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u) (F i) t = 0)
    (hFON : ∀ t ∈ Set.Icc (0 : Real) L, ∀ i j,
      g.inner (intrinsicGeodesic (I := I) g hEnorm p u t) (F i t) (F j t) =
        if i = j then 1 else 0)
    (hFperp : ∀ t ∈ Set.Icc (0 : Real) L, ∀ i,
      g.inner (intrinsicGeodesic (I := I) g hEnorm p u t) (F i t)
        (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm p u) t) = 0)
    (hFbundle : ∀ i, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun t => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (intrinsicGeodesic (I := I) g hEnorm p u t) (F i t)))
    (hJ : ∀ i, intrinsicJacobi (I := I) g hEnorm p u (w i) L = F i L)
    (φ : Real → Real) (hφ : ContDiff Real ∞ φ)
    (hφ0 : φ 0 = 0) (hφL : φ L = 1) :
    let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
    laplacian (I := I) (LeviCivita (I := I) g) g
        (branchRadius (I := I) g B) (γ L) ≤
      ∫ t in (0 : Real)..L,
        ((Module.finrank Real E - 1 : Real) * deriv φ t ^ 2 -
          φ t ^ 2 * ricciTensor (I := I) g (γ t)
            (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) := by
  classical
  dsimp only
  let γ := intrinsicGeodesic (I := I) g hEnorm p u
  let γL := intrinsicGeodesic (I := I) g hEnorm p (L • u)
  let F' : Fin (Module.finrank Real E - 1) → TangentSpace I (γL 1) :=
    fun i => (F i L : E)
  have hq : γL 1 = γ L := intrinsicGeodesic_smul (I := I) g hEnorm p u L
  have hJL (i) : @Eq E
      (intrinsicJacobi (I := I) g hEnorm p (L • u) (L • w i) 1 : E)
      (F i L : E) := by
    have h := intrinsicJacobi_smul (I := I) g hEnorm p u (w i) L 1
    rw [mul_one, hJ] at h
    exact h
  have hFON' : ∀ i j, g.inner (γL 1) (F' i) (F' j) =
      if i = j then 1 else 0 := by
    intro i j
    dsimp only [F']
    rw [hq]
    exact hFON L ⟨hL.le, le_rfl⟩ i j
  have hFperp' : ∀ i, g.inner (γL 1) (curveVelocity (I := I) γL 1) (F' i) = 0 := by
    intro i
    change g.inner (γL 1) (curveVelocity (I := I) γL 1) (F i L : E) = 0
    rw [← hJL i]
    have hgauss := intrinsicJacobi_perp (I := I) g hEnorm p (L • u) (L • w i)
    change g.inner (γL 1) (curveVelocity (I := I) γL 1)
      (intrinsicJacobi (I := I) g hEnorm p (L • u) (L • w i) 1) = _ at hgauss
    rw [hgauss]
    simp only [map_smul, smul_apply, smul_eq_mul, huw, mul_zero]
  have huL : 0 < g.inner p (L • u) (L • u) := by
    rw [gInner_smul_self (I := I) g p L u, hu]
    positivity
  have htrace := branchLap_eq_sum_hessian_of_orthonormal_perp_frame
    (I := I) g hEnorm p (L • u) B hsrc huL F' hFON' hFperp'
  change laplacian (I := I) (LeviCivita (I := I) g) g (branchRadius (I := I) g B) (γL 1) =
    ∑ i, hessFun (I := I) g (branchRadius (I := I) g B) (γL 1) (F' i) (F' i) at htrace
  dsimp only [F'] at htrace
  rw [hq] at htrace
  rw [htrace]
  have hindex := sum_intrinsicJacobi_endpoint_deriv_le_weighted_ricci
    (I := I) g hEnorm p u w L hL hu huw hmin F hFdiff hFpar hFON hFperp hFbundle hJ φ hφ hφ0 hφL
  dsimp only at hindex
  convert hindex using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← hJ i]
  exact branchHess_intrinsicJacobi_eq_endpoint (I := I) g hEnorm p u (w i) L B hL hu hsrc (huw i)

theorem branchLap_le_ricci_integral_of_minimizing
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (L : Real)
    (hL : 0 < L) (hu : g.inner p u u = 1)
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (hsrc : tangentSpaceModelContinuousLinearEquiv (I := I) p (L • u) ∈ B.hom.source)
    (hmin : ∀ η : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 η (Set.Icc 0 L) →
      η 0 = p → η L = intrinsicGeodesic (I := I) g hEnorm p u L →
      arcLength (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u) 0 L ≤
        arcLength (I := I) g η 0 L)
    (φ : Real → Real) (hφ : ContDiff Real ∞ φ)
    (hφ0 : φ 0 = 0) (hφL : φ L = 1) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    laplacian (I := I) (LeviCivita (I := I) g) g
        (branchRadius (I := I) g B) (γ L) ≤
      ∫ t in (0 : Real)..L,
        ((Module.finrank Real E - 1 : Real) * deriv φ t ^ 2 -
          φ t ^ 2 * ricciTensor (I := I) g (γ t)
            (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) := by
  classical
  let γ := intrinsicGeodesic (I := I) g hEnorm p u
  let γL := intrinsicGeodesic (I := I) g hEnorm p (L • u)
  have hγ : ContMDiff 𝓘(Real, Real) I ∞ γ := intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hgeo : Geodesic.IsGeodesic (I := I) g γ := intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u
  have hunit0 : g.inner (γ 0) (curveVelocity (I := I) γ 0) (curveVelocity (I := I) γ 0) = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u 0).trans hu
  obtain ⟨F, hFdiff, hFpar, hFON, hFperp, hFbundle⟩ :=
    exists_parallel_perp_frame (I := I) g γ hγ hL (hgeo.isGeodesicOn (Icc 0 L)) hunit0
  let e : Fin (Module.finrank Real E - 1) → ∀ t, TangentSpace I (γ t) := fun i => (F i).toFun
  have hq : γL 1 = γ L := intrinsicGeodesic_smul (I := I) g hEnorm p u L
  have hγscale : γL = fun s => γ (L * s + 0) := by
    funext t
    dsimp only [γL, γ]
    rw [add_zero, ← intrinsicGeodesic_smul (I := I) g hEnorm p u (L * t),
      ← intrinsicGeodesic_smul (I := I) g hEnorm p (L • u) t]
    congr 1
    module
  have hvelscale : @Eq E (curveVelocity (I := I) γL 1 : E)
      (L • curveVelocity (I := I) γ L : E) := by
    have h := curveVelocity_comp_affine (I := I) γ L 0 1
      (hγ.contMDiffAt.mdifferentiableAt (by simp))
    rw [mul_one, add_zero] at h
    rw [hγscale]
    exact h
  have hpre (i : Fin (Module.finrank Real E - 1)) :
      ∃ w : TangentSpace I p,
        g.inner p u w = 0 ∧ intrinsicJacobi (I := I) g hEnorm p u w L = e i L := by
    let Y : TangentSpace I (γL 1) := (e i L : E)
    obtain ⟨W, hW⟩ := exists_intrinsicJacobi_one_eq (I := I) g hEnorm p B hsrc Y
    have hYperp : g.inner (γL 1) (curveVelocity (I := I) γL 1) Y = 0 := by
      dsimp only [Y]
      rw [hq, hvelscale, map_smul, smul_apply, smul_eq_mul, g.symm]
      have hperp : g.inner (γ L) (e i L) (curveVelocity (I := I) γ L) = 0 :=
        hFperp L ⟨hL.le, le_rfl⟩ i
      rw [hperp, mul_zero]
    have hgauss := intrinsicJacobi_perp (I := I) g hEnorm p (L • u) W
    change g.inner (γL 1) (curveVelocity (I := I) γL 1)
      (intrinsicJacobi (I := I) g hEnorm p (L • u) W 1) = g.inner p (L • u) W at hgauss
    rw [hW, hYperp, map_smul, smul_apply, smul_eq_mul] at hgauss
    have huW : g.inner p u W = 0 := (mul_eq_zero.mp hgauss.symm).resolve_left hL.ne'
    let w : TangentSpace I p := L⁻¹ • W
    have hLw : L • w = W := by simp only [w, smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
    refine ⟨w, ?_, ?_⟩
    · simp only [w, map_smul, smul_eq_mul, huW, mul_zero]
    · have hscale := intrinsicJacobi_smul (I := I) g hEnorm p u w L 1
      rw [← hLw] at hW
      rw [mul_one] at hscale
      exact hscale.symm.trans hW
  choose w huw hw using hpre
  exact branchLap_le_weighted_ricci_of_minimizing (I := I) g hEnorm p u w L hL hu huw
    B hsrc hmin e hFdiff hFpar hFON hFperp hFbundle hw φ hφ hφ0 hφL

end Riemannian
end Geometry
end DifferentialGeometry
