import DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci
import DifferentialGeometry.Geometry.Comparison.Hessian.Radial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Batteries.Tactic.OpenPrivate

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

open private exists_intrinsicJacobi_one_eq branchHess_perp_radial_eq_zero
  branchHess_symm from DifferentialGeometry.Geometry.Comparison.Hessian.Radial

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open Exponential
open Variation
open CovariantDerivativeAlong



def modelRadial (K t : Real) : Real :=
  if K = 0 then t else Real.sinh (Real.sqrt (-K) * t) / Real.sqrt (-K)

def modelRadialDeriv (K t : Real) : Real :=
  if K = 0 then 1 else Real.cosh (Real.sqrt (-K) * t)

def modelRadialLogDeriv (K L : Real) : Real :=
  modelRadialDeriv K L / modelRadial K L


theorem modelRadial_eq_of_eq_zero {K : Real} (hK : K = 0) :
    modelRadial K = fun t : Real => t := by
  funext t
  simp [modelRadial, hK]


theorem modelRadialDeriv_eq_of_eq_zero {K : Real} (hK : K = 0) :
    modelRadialDeriv K = fun _ : Real => (1 : Real) := by
  funext t
  simp [modelRadialDeriv, hK]


theorem modelRadial_eq_of_ne_zero {K : Real} (hK : K ≠ 0) :
    modelRadial K =
      fun t : Real => Real.sinh (Real.sqrt (-K) * t) / Real.sqrt (-K) := by
  funext t
  simp only [modelRadial, if_neg hK]


theorem modelRadialDeriv_eq_of_ne_zero {K : Real} (hK : K ≠ 0) :
    modelRadialDeriv K = fun t : Real => Real.cosh (Real.sqrt (-K) * t) := by
  funext t
  simp only [modelRadialDeriv, if_neg hK]


theorem modelRadial_apply_of_eq_zero {K : Real} (hK : K = 0) (t : Real) :
    modelRadial K t = t :=
  congrFun (modelRadial_eq_of_eq_zero hK) t


theorem modelRadialDeriv_apply_of_eq_zero {K : Real} (hK : K = 0) (t : Real) :
    modelRadialDeriv K t = 1 :=
  congrFun (modelRadialDeriv_eq_of_eq_zero hK) t


theorem modelRadial_apply_of_ne_zero {K : Real} (hK : K ≠ 0) (t : Real) :
    modelRadial K t = Real.sinh (Real.sqrt (-K) * t) / Real.sqrt (-K) :=
  congrFun (modelRadial_eq_of_ne_zero hK) t


theorem modelRadialDeriv_apply_of_ne_zero {K : Real} (hK : K ≠ 0) (t : Real) :
    modelRadialDeriv K t = Real.cosh (Real.sqrt (-K) * t) :=
  congrFun (modelRadialDeriv_eq_of_ne_zero hK) t


@[simp]
theorem modelRadial_zero (K : Real) : modelRadial K 0 = 0 := by
  by_cases hK : K = 0
  · rw [modelRadial_apply_of_eq_zero hK]
  · rw [modelRadial_apply_of_ne_zero hK, mul_zero, Real.sinh_zero, zero_div]


@[simp]
theorem modelRadialDeriv_zero (K : Real) : modelRadialDeriv K 0 = 1 := by
  by_cases hK : K = 0
  · rw [modelRadialDeriv_apply_of_eq_zero hK]
  · rw [modelRadialDeriv_apply_of_ne_zero hK, mul_zero, Real.cosh_zero]

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_modelRadial {K : Real} (hK : K ≤ 0) (t : Real) :
    HasDerivAt (modelRadial K) (modelRadialDeriv K t) t := by
  rcases eq_or_lt_of_le hK with hzero | hneg
  · rw [modelRadial_eq_of_eq_zero hzero, modelRadialDeriv_apply_of_eq_zero hzero]
    exact hasDerivAt_id t
  · have hKne : K ≠ 0 := ne_of_lt hneg
    have hkpos : (0 : Real) < Real.sqrt (-K) := Real.sqrt_pos.mpr (by linarith)
    have hkne : Real.sqrt (-K) ≠ 0 := hkpos.ne'
    rw [modelRadial_eq_of_ne_zero hKne, modelRadialDeriv_apply_of_ne_zero hKne]
    have h1 : HasDerivAt (fun s : Real => Real.sqrt (-K) * s) (Real.sqrt (-K)) t := by
      simpa using (hasDerivAt_id t).const_mul (Real.sqrt (-K))
    have h2 : HasDerivAt (fun s : Real => Real.sinh (Real.sqrt (-K) * s))
        (Real.cosh (Real.sqrt (-K) * t) * Real.sqrt (-K)) t :=
      (Real.hasDerivAt_sinh (Real.sqrt (-K) * t)).comp t h1
    have h3 := h2.div_const (Real.sqrt (-K))
    have hval : Real.cosh (Real.sqrt (-K) * t) * Real.sqrt (-K) / Real.sqrt (-K) =
        Real.cosh (Real.sqrt (-K) * t) := by
      rw [mul_div_assoc, div_self hkne, mul_one]
    rwa [hval] at h3

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_modelRadialDeriv {K : Real} (hK : K ≤ 0) (t : Real) :
    HasDerivAt (modelRadialDeriv K) (-K * modelRadial K t) t := by
  rcases eq_or_lt_of_le hK with hzero | hneg
  · rw [modelRadialDeriv_eq_of_eq_zero hzero, modelRadial_apply_of_eq_zero hzero, hzero]
    simpa using hasDerivAt_const t (1 : Real)
  · have hKne : K ≠ 0 := ne_of_lt hneg
    have hkpos : (0 : Real) < Real.sqrt (-K) := Real.sqrt_pos.mpr (by linarith)
    have hkne : Real.sqrt (-K) ≠ 0 := hkpos.ne'
    have hksq : Real.sqrt (-K) * Real.sqrt (-K) = -K :=
      Real.mul_self_sqrt (by linarith)
    have hdiv : -K / Real.sqrt (-K) = Real.sqrt (-K) :=
      (div_eq_iff hkne).mpr hksq.symm
    rw [modelRadialDeriv_eq_of_ne_zero hKne, modelRadial_apply_of_ne_zero hKne]
    have h1 : HasDerivAt (fun s : Real => Real.sqrt (-K) * s) (Real.sqrt (-K)) t := by
      simpa using (hasDerivAt_id t).const_mul (Real.sqrt (-K))
    have h2 : HasDerivAt (fun s : Real => Real.cosh (Real.sqrt (-K) * s))
        (Real.sinh (Real.sqrt (-K) * t) * Real.sqrt (-K)) t :=
      (Real.hasDerivAt_cosh (Real.sqrt (-K) * t)).comp t h1
    have hval : -K * (Real.sinh (Real.sqrt (-K) * t) / Real.sqrt (-K)) =
        Real.sinh (Real.sqrt (-K) * t) * Real.sqrt (-K) := by
      calc
        -K * (Real.sinh (Real.sqrt (-K) * t) / Real.sqrt (-K)) =
            -K / Real.sqrt (-K) * Real.sinh (Real.sqrt (-K) * t) := by
          ring
        _ = Real.sqrt (-K) * Real.sinh (Real.sqrt (-K) * t) := by
          rw [hdiv]
        _ = Real.sinh (Real.sqrt (-K) * t) * Real.sqrt (-K) := by
          ring
    rw [hval]
    exact h2


theorem modelRadial_pos {K : Real} (hK : K ≤ 0) {t : Real} (ht : 0 < t) :
    0 < modelRadial K t := by
  rcases eq_or_lt_of_le hK with hzero | hneg
  · rwa [modelRadial_apply_of_eq_zero hzero]
  · have hKne : K ≠ 0 := ne_of_lt hneg
    have hkpos : (0 : Real) < Real.sqrt (-K) := Real.sqrt_pos.mpr (by linarith)
    rw [modelRadial_apply_of_ne_zero hKne]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hkpos ht)) hkpos


theorem modelRadialDeriv_pos {K : Real} (hK : K ≤ 0) (t : Real) :
    0 < modelRadialDeriv K t := by
  rcases eq_or_lt_of_le hK with hzero | hneg
  · rw [modelRadialDeriv_apply_of_eq_zero hzero]
    exact one_pos
  · rw [modelRadialDeriv_apply_of_ne_zero (ne_of_lt hneg)]
    exact Real.cosh_pos _

set_option backward.isDefEq.respectTransparency false in
theorem contDiff_modelRadial (K : Real) : ContDiff Real ∞ (modelRadial K) := by
  by_cases hK : K = 0
  · rw [modelRadial_eq_of_eq_zero hK]
    exact contDiff_id
  · rw [modelRadial_eq_of_ne_zero hK]
    exact (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)).div_const _

set_option backward.isDefEq.respectTransparency false in
theorem contDiff_modelRadialDeriv (K : Real) :
    ContDiff Real ∞ (modelRadialDeriv K) := by
  by_cases hK : K = 0
  · rw [modelRadialDeriv_eq_of_eq_zero hK]
    exact contDiff_const
  · rw [modelRadialDeriv_eq_of_ne_zero hK]
    exact Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)


theorem continuous_modelRadial (K : Real) : Continuous (modelRadial K) :=
  (contDiff_modelRadial K).continuous


theorem continuous_modelRadialDeriv (K : Real) : Continuous (modelRadialDeriv K) :=
  (contDiff_modelRadialDeriv K).continuous

theorem integral_modelRadialDeriv_sq_sub {K : Real} (hK : K ≤ 0) (L : Real) :
    (∫ t in (0 : Real)..L,
        (modelRadialDeriv K t ^ 2 - K * modelRadial K t ^ 2)) =
      modelRadial K L * modelRadialDeriv K L := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : Real) L,
      HasDerivAt (fun s : Real => modelRadial K s * modelRadialDeriv K s)
        (modelRadialDeriv K t ^ 2 - K * modelRadial K t ^ 2) t := by
    intro t _
    have h := (hasDerivAt_modelRadial hK t).mul (hasDerivAt_modelRadialDeriv hK t)
    have hval : modelRadialDeriv K t * modelRadialDeriv K t +
        modelRadial K t * (-K * modelRadial K t) =
          modelRadialDeriv K t ^ 2 - K * modelRadial K t ^ 2 := by
      ring
    rwa [hval] at h
  have hint : IntervalIntegrable
      (fun t : Real => modelRadialDeriv K t ^ 2 - K * modelRadial K t ^ 2)
      MeasureTheory.volume 0 L :=
    (((continuous_modelRadialDeriv K).pow 2).sub
      (continuous_const.mul ((continuous_modelRadial K).pow 2))).intervalIntegrable 0 L
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, modelRadial_zero,
    zero_mul, sub_zero]

private theorem mul_cosh_le_one_add_mul_sinh (x : Real) :
    x * Real.cosh x ≤ (1 + x) * Real.sinh x := by
  have hE : (0 : Real) < Real.exp x := Real.exp_pos x
  have hkey : 2 * x + 1 ≤ Real.exp x * Real.exp x := by
    have h := Real.add_one_le_exp (x + x)
    rw [Real.exp_add] at h
    linarith
  have hinv : (0 : Real) < (Real.exp x)⁻¹ := inv_pos.mpr hE
  have hstep : (2 * x + 1) * (Real.exp x)⁻¹ ≤ Real.exp x := by
    have h := mul_le_mul_of_nonneg_right hkey hinv.le
    rwa [mul_assoc, mul_inv_cancel₀ hE.ne', mul_one] at h
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  nlinarith [hstep]


theorem modelRadialLogDeriv_zero_curvature (L : Real) :
    modelRadialLogDeriv 0 L = 1 / L := by
  rw [modelRadialLogDeriv, modelRadialDeriv_apply_of_eq_zero rfl,
    modelRadial_apply_of_eq_zero rfl]


theorem modelRadialLogDeriv_of_ne_zero {K : Real} (hK : K ≠ 0) (L : Real) :
    modelRadialLogDeriv K L =
      Real.cosh (Real.sqrt (-K) * L) * Real.sqrt (-K) /
        Real.sinh (Real.sqrt (-K) * L) := by
  rw [modelRadialLogDeriv, modelRadialDeriv_apply_of_ne_zero hK,
    modelRadial_apply_of_ne_zero hK, div_div_eq_mul_div]


theorem modelRadialLogDeriv_pos {K : Real} (hK : K ≤ 0) {L : Real} (hL : 0 < L) :
    0 < modelRadialLogDeriv K L :=
  div_pos (modelRadialDeriv_pos hK L) (modelRadial_pos hK hL)

theorem modelRadialLogDeriv_le {K : Real} (hK : K ≤ 0) {L : Real} (hL : 0 < L) :
    modelRadialLogDeriv K L ≤ 1 / L + Real.sqrt (-K) := by
  rcases eq_or_lt_of_le hK with hzero | hneg
  · subst hzero
    rw [modelRadialLogDeriv_zero_curvature, neg_zero, Real.sqrt_zero]
    linarith
  · have hKne : K ≠ 0 := ne_of_lt hneg
    have hkpos : (0 : Real) < Real.sqrt (-K) := Real.sqrt_pos.mpr (by linarith)
    have hx : (0 : Real) < Real.sqrt (-K) * L := mul_pos hkpos hL
    have hsinh : 0 < Real.sinh (Real.sqrt (-K) * L) := Real.sinh_pos_iff.mpr hx
    have hhelp := mul_cosh_le_one_add_mul_sinh (Real.sqrt (-K) * L)
    rw [modelRadialLogDeriv_of_ne_zero hKne, div_le_iff₀ hsinh]
    have hrw : 1 / L + Real.sqrt (-K) = (1 + Real.sqrt (-K) * L) / L := by
      rw [add_div, mul_div_assoc, div_self hL.ne', mul_one]
    rw [hrw, div_mul_eq_mul_div, le_div_iff₀ hL]
    nlinarith [hhelp]



def SectionalBoundedBelowAt {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M) (x : M) (K : Real) : Prop :=
  ∀ v w : TangentSpace I x,
    K * (g.inner x v v * g.inner x w w - g.inner x v w ^ 2) ≤
      metricRm04StandardAt (I := I) (M := M) g x v w w v


def SectionalBoundedBelow {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M) (K : Real) : Prop :=
  ∀ x : M, SectionalBoundedBelowAt (I := I) g x K

theorem sectionalBoundedBelowAt_zero_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M) (x : M) :
    SectionalBoundedBelowAt (I := I) g x 0 ↔
      metricRm04At (I := I) (M := M) g x ∈
        DifferentialGeometry.tensor04SectionalNonnegativeCone (I := I) (M := M) := by
  rw [metricRm04At_mem_tensor04SectionalNonnegativeCone_iff]
  constructor
  · intro h v w
    simpa using h v w
  · intro h v w
    simpa using h v w

theorem ricci_lower_of_sectionalBoundedBelowAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H} [I.Boundaryless] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (x : M) {K : Real}
    (hsec : SectionalBoundedBelowAt (I := I) g x K) (v : TangentSpace I x) :
    ((Module.finrank Real E - 1 : Nat) : Real) * K * g.inner x v v ≤
      ricciTensor (I := I) g x v v := by
  classical
  by_cases hv : v = 0
  · subst hv
    simp
  let : Nontrivial E := ⟨⟨v, 0, hv⟩⟩
  let : NeZero (Module.finrank Real E) :=
    ⟨(Module.finrank_pos (R := Real) (M := E)).ne'⟩
  have hvpos : 0 < g.inner x v v := g.pos x v hv
  obtain ⟨e, hON, hperp⟩ := exists_perp_pos (I := I) g x v hvpos
  rw [← BonnetMyers.ricci_eq_sum_perp (I := I) g x v hvpos e hON hperp]
  have hterm : ∀ i : Fin (Module.finrank Real E - 1),
      K * g.inner x v v ≤
        g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) v v) (e i) := by
    intro i
    have hei : g.inner x (e i) (e i) = 1 := by simpa using hON i i
    have hperpi : g.inner x (e i) v = 0 := hperp i
    calc
      K * g.inner x v v =
          K * (g.inner x (e i) (e i) * g.inner x v v - g.inner x (e i) v ^ 2) := by
        rw [hei, hperpi]
        ring
      _ ≤ metricRm04StandardAt (I := I) (M := M) g x (e i) v v (e i) := hsec (e i) v
      _ = g.inner x (e i) (riemannOp (LeviCivita (I := I) g) x (e i) v v) :=
        rm04_eq_inner_riem (I := I) (M := M) g x (e i) v v (e i)
      _ = g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) v v) (e i) :=
        g.symm x (e i) _
  have hsum :
      ((Module.finrank Real E - 1 : Nat) : Real) * K * g.inner x v v =
        ∑ _i : Fin (Module.finrank Real E - 1), K * g.inner x v v := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum]
  exact Finset.sum_le_sum fun i _ => hterm i

theorem ricciLower_of_sectionalBoundedBelow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H} [I.Boundaryless] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {K : Real}
    (hsec : SectionalBoundedBelow (I := I) g K) :
    BonnetMyers.RicciBoundedBelow (I := I) g
      (((Module.finrank Real E - 1 : Nat) : Real) * K) :=
  fun x v => ricci_lower_of_sectionalBoundedBelowAt (I := I) g x (hsec x) v



section Radial

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

private theorem intrinsicJacobi_endpoint_deriv_le_of_sectional_lower_bound
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u w : TangentSpace I p) (L K : Real)
    (hK : K ≤ 0)
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
        K * g.inner (intrinsicGeodesic (I := I) g hEnorm p u t) Z Z ≤
          metricRm04StandardAt (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm p u t) Z
            (curveVelocity (I := I)
              (intrinsicGeodesic (I := I) g hEnorm p u) t)
            (curveVelocity (I := I)
              (intrinsicGeodesic (I := I) g hEnorm p u) t) Z) :
    let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
    let J := intrinsicJacobi (I := I) g hEnorm p u w
    g.inner (γ L) (covDerivAlong (I := I) g γ J L) (J L) ≤
      modelRadialLogDeriv K L * g.inner (γ L) (J L) (J L) := by
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
  have hsL : (0 : Real) < modelRadial K L := modelRadial_pos hK hL
  have hsLne : modelRadial K L ≠ 0 := hsL.ne'
  let c : EuclideanSpace Real (Fin (Module.finrank Real E - 1)) := y L
  let z : Real → EuclideanSpace Real (Fin (Module.finrank Real E - 1)) :=
    fun t => (modelRadial K t / modelRadial K L) • c
  let dz : Real → EuclideanSpace Real (Fin (Module.finrank Real E - 1)) :=
    fun t => (modelRadialDeriv K t / modelRadial K L) • c
  have hz_deriv (t : Real) : HasDerivAt z (dz t) t := by
    simpa only [z, dz] using
      ((hasDerivAt_modelRadial hK t).div_const (modelRadial K L)).smul_const c
  have hz_smooth : ContDiff Real ∞ z := by
    exact ((contDiff_modelRadial K).div_const _).smul contDiff_const
  have hdz_smooth : ContDiff Real ∞ dz := by
    exact ((contDiff_modelRadialDeriv K).div_const _).smul contDiff_const
  have hz0 : z 0 = y 0 := by
    rw [hy0]
    simp [z]
  have hzL : z L = y L := by
    change (modelRadial K L / modelRadial K L) • c = y L
    rw [div_self hsLne, one_smul]
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
      (I := I) g γ L D hL.le (hD_bundle.of_le ENat.LEInfty.out)
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
  have hcurv_lower (t : Real) (ht : t ∈ Set.Icc (0 : Real) L) :
      K * inner Real (z t) (z t) ≤ inner Real (R t (z t)) (z t) := by
    have hZ : g.inner (γ t) (perpFrameLift (I := I) e z t)
        (perpFrameLift (I := I) e z t) = inner Real (z t) (z t) :=
      perpLift_inner (I := I) g e (z t) (z t) t (fun i j => hFON t ht i j)
    rw [perpCurv_inner (I := I) g γ e (z t) (z t) t, ← hZ]
    change K * g.inner (γ t) (perpFrameLift (I := I) e z t)
        (perpFrameLift (I := I) e z t) ≤
      g.inner (γ t)
        ((riemannOp (LeviCivita (I := I) g) (γ t))
          (perpFrameLift (I := I) e z t)
          (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t))
        (perpFrameLift (I := I) e z t)
    rw [g.symm (γ t)
      ((riemannOp (LeviCivita (I := I) g) (γ t))
        (perpFrameLift (I := I) e z t)
        (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t))
      (perpFrameLift (I := I) e z t)]
    rw [← rm04_eq_inner_riem (I := I) g (γ t)
      (perpFrameLift (I := I) e z t) (curveVelocity (I := I) γ t)
      (curveVelocity (I := I) γ t) (perpFrameLift (I := I) e z t)]
    exact hsec t ht (perpFrameLift (I := I) e z t)
  have hindex_z :
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L z dz z dz ≤
        modelRadialLogDeriv K L * inner Real c c := by
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
    have hcmp_cont : Continuous (fun t : Real =>
        (modelRadialDeriv K t ^ 2 - K * modelRadial K t ^ 2) *
          (inner Real c c / modelRadial K L ^ 2)) :=
      (((continuous_modelRadialDeriv K).pow 2).sub
        (continuous_const.mul ((continuous_modelRadial K).pow 2))).mul continuous_const
    have hpoint : ∀ t ∈ Set.Icc (0 : Real) L,
        DifferentialGeometry.Analysis.ODE.indexIntegrand R z dz z dz t ≤
          (modelRadialDeriv K t ^ 2 - K * modelRadial K t ^ 2) *
            (inner Real c c / modelRadial K L ^ 2) := by
      intro t ht
      have hzz : inner Real (z t) (z t) =
          (modelRadial K t / modelRadial K L) ^ 2 * inner Real c c := by
        dsimp only [z]
        rw [real_inner_smul_left, real_inner_smul_right]
        ring
      have hdzdz : inner Real (dz t) (dz t) =
          (modelRadialDeriv K t / modelRadial K L) ^ 2 * inner Real c c := by
        dsimp only [dz]
        rw [real_inner_smul_left, real_inner_smul_right]
        ring
      have hlow := hcurv_lower t ht
      rw [hzz] at hlow
      have hrhs : (modelRadialDeriv K t ^ 2 - K * modelRadial K t ^ 2) *
          (inner Real c c / modelRadial K L ^ 2) =
            (modelRadialDeriv K t / modelRadial K L) ^ 2 * inner Real c c -
              K * ((modelRadial K t / modelRadial K L) ^ 2 * inner Real c c) := by
        ring
      rw [DifferentialGeometry.Analysis.ODE.indexIntegrand, hdzdz, hrhs]
      linarith [hlow]
    have hmono := intervalIntegral.integral_mono_on hL.le hint
      (hcmp_cont.intervalIntegrable 0 L) hpoint
    have hpow : modelRadial K L * (modelRadial K L ^ 2)⁻¹ =
        (modelRadial K L)⁻¹ := by
      rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hsLne, one_mul]
    have hval : modelRadial K L * modelRadialDeriv K L *
        (inner Real c c / modelRadial K L ^ 2) =
          modelRadialLogDeriv K L * inner Real c c := by
      rw [modelRadialLogDeriv, div_eq_mul_inv, div_eq_mul_inv]
      calc
        modelRadial K L * modelRadialDeriv K L *
            (inner Real c c * (modelRadial K L ^ 2)⁻¹) =
              modelRadialDeriv K L * inner Real c c *
                (modelRadial K L * (modelRadial K L ^ 2)⁻¹) := by
          ring
        _ = modelRadialDeriv K L * inner Real c c * (modelRadial K L)⁻¹ := by
          rw [hpow]
        _ = modelRadialDeriv K L * (modelRadial K L)⁻¹ * inner Real c c := by
          ring
    rw [DifferentialGeometry.Analysis.ODE.indexForm_def]
    refine hmono.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_mul_const,
      integral_modelRadialDeriv_sq_sub hK L, hval]
  have hcoeff_le :
      inner Real (v L) (y L) ≤ modelRadialLogDeriv K L * inner Real c c := by
    rw [← hindex_y]
    exact hindex_le.trans hindex_z
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
  have hnorm_coeff :
      g.inner (γ L) (J L) (J L) = inner Real c c := by
    rw [← hJ_expand]
    dsimp only [c]
    exact perpLift_inner (I := I) g e (y L) (y L) L
      (fun i j => hFON L ⟨hL.le, le_rfl⟩ i j)
  rw [hinner_coeff, hnorm_coeff]
  exact hcoeff_le

private theorem branchHess_perp_le_of_minimizing_of_sectional_lower_bound
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (L K : Real)
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (hK : K ≤ 0)
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
        K * g.inner (intrinsicGeodesic (I := I) g hEnorm p u t) Z Z ≤
          metricRm04StandardAt (I := I) g
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
      modelRadialLogDeriv K L *
        g.inner (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y := by
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
    change @Eq E
      (intrinsicJacobi (I := I) g hEnorm p uL W t : E)
      (intrinsicJacobi (I := I) g hEnorm p u w (L * t) : E)
    rw [show uL = L • u by rfl, ← hLw]
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
  have hindex :=
    intrinsicJacobi_endpoint_deriv_le_of_sectional_lower_bound
      (I := I) g hEnorm p u w L K hK hL hu huw hmin hsec
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
      g.inner (γL 1) (JL 1) (JL 1) = g.inner (γ L) (J L) (J L) := by
    rw [hq, hJoneScale]
  rw [← hJLone, hshape, hleft, hright]
  exact hindex

theorem branchHess_le_of_minimizing_of_sectional_lower_bound
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (L K : Real)
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (hK : K ≤ 0)
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
      SectionalBoundedBelowAt (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p u t) K)
    (Y : TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1)) :
    hessFun (I := I) g (branchRadius (I := I) g B)
        (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y ≤
      modelRadialLogDeriv K L *
        g.inner (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y := by
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
        K * g.inner (intrinsicGeodesic (I := I) g hEnorm p u t) W W ≤
          metricRm04StandardAt (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm p u t) W
            (curveVelocity (I := I)
              (intrinsicGeodesic (I := I) g hEnorm p u) t)
            (curveVelocity (I := I)
              (intrinsicGeodesic (I := I) g hEnorm p u) t) W := by
    intro t ht W
    have hunit :
        g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t) = 1 :=
      (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u t).trans hu
    have hbound := hsec t ht W
      (curveVelocity (I := I)
        (intrinsicGeodesic (I := I) g hEnorm p u) t)
    rw [hunit, mul_one] at hbound
    nlinarith [hbound, hK,
      sq_nonneg (g.inner (intrinsicGeodesic (I := I) g hEnorm p u t) W
        (curveVelocity (I := I)
          (intrinsicGeodesic (I := I) g hEnorm p u) t))]
  have hZbound : Hess Z Z ≤ modelRadialLogDeriv K L * g.inner q Z Z := by
    simpa only [Hess, q, γ, v] using
      branchHess_perp_le_of_minimizing_of_sectional_lower_bound
        (I := I) g hEnorm p u L K B hK hL hu hsrc hmin hsec' Z hZperp
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
    _ ≤ modelRadialLogDeriv K L * g.inner q Z Z := hZbound
    _ ≤ modelRadialLogDeriv K L * g.inner q Y Y :=
      mul_le_mul_of_nonneg_left hnorm_le (modelRadialLogDeriv_pos hK hL).le

theorem branchHess_le_of_minimizing_of_sectional_lower_bound_zero
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
      g.inner (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y / L := by
  have h := branchHess_le_of_minimizing_of_sectional_lower_bound
    (I := I) g hEnorm p u L 0 B le_rfl hL hu hsrc hmin
    (fun t ht => (sectionalBoundedBelowAt_zero_iff (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm p u t)).2 (hsec t ht)) Y
  rwa [modelRadialLogDeriv_zero_curvature, one_div_mul_eq_div] at h

end Radial

end Riemannian
end Geometry
end DifferentialGeometry

end
