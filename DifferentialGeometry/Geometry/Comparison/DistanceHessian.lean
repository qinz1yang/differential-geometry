import DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci
import DifferentialGeometry.Geometry.Comparison.DistanceCalabi
import DifferentialGeometry.Geometry.Comparison.RadialHessian

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry

open Geometry.Riemannian
open Geometry.Riemannian.Exponential
open Geometry.Riemannian.HopfRinow
open Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem calabiDist_hess_support_on
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {O x : M} (hOx : O ≠ x)
    (hfin : riemannianEDist I O x ≠ (⊤ : ENNReal)) :
    let r := (riemannianEDist I O x).toReal
    ∃ rho : M → Real, ∃ U : Set M,
      IsOpen U ∧
      x ∈ U ∧
      ContMDiffOn I 𝓘(Real, Real) ∞ rho U ∧
      rho x = r ∧
      (∀ᶠ y in nhds x, (riemannianEDist I O y).toReal ≤ rho y) ∧
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) = 1 ∧
      ∀ Y : TangentSpace I x,
        hessFun (I := I) g rho x Y Y ≤ 2 * g.inner x Y Y / r := by
  dsimp only
  let r : Real := (riemannianEDist I O x).toReal
  have hdist_ne : riemannianEDist I O x ≠ 0 := by
    intro hzero
    exact hOx (riemannianEDist_eq_zero_imp_eq (I := I) O x hzero)
  have hr : 0 < r := ENNReal.toReal_pos hdist_ne hfin
  have hRic : Geometry.Riemannian.BonnetMyers.RicciBoundedBelow (I := I) g 0 :=
    Geometry.Riemannian.BonnetMyers.ricciLower_of_sec (I := I) g hsec
  obtain ⟨tail, _hrho_inf, hrho_x, hupper, _hrho_ev, _hrho_grad,
      hgrad_norm, _hlap⟩ :=
    exists_calabiData (I := I) g hEnorm 0 le_rfl (by simpa using hRic) hOx hfin
  let rho : M → Real := fun y =>
    tail.left + branchRadius (I := I) g tail.branch y
  let e : TangentSpace I tail.p := tail.ell⁻¹ • tail.u
  have he_unit : g.inner tail.p e e = 1 :=
    tail.inner_normalized_tangent
  have hscale : tail.ell • e = tail.u := by
    dsimp only [e]
    rw [smul_smul, mul_inv_cancel₀ tail.ell_pos.ne', one_smul]
  let gamma : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm tail.p e
  have hend : gamma tail.ell = x :=
    tail.intrinsicGeodesic_normalized_tangent_ell
  have hmin : ∀ eta : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 eta (Set.Icc 0 tail.ell) →
      eta 0 = tail.p → eta tail.ell = gamma tail.ell →
      arcLength (I := I) g gamma 0 tail.ell ≤
        arcLength (I := I) g eta 0 tail.ell := by
    intro eta heta heta0 hetaell
    exact tail.arcLength_normalized_tangent_le rfl heta heta0 (hetaell.trans hend)
  have hsrc :
      tangentSpaceModelContinuousLinearEquiv (I := I) tail.p
          (tail.ell • e) ∈ tail.branch.hom.source := by
    rw [hscale]
    with_unfolding_all exact tail.source_mem
  have hsec_tail : ∀ t ∈ Set.Icc (0 : Real) tail.ell,
      metricRm04At (I := I) g (gamma t) ∈
        tensor04SectionalNonnegativeCone (I := I) (M := M) := by
    intro t _
    exact hsec (gamma t)
  have hend' :
      intrinsicGeodesic (I := I) g hEnorm tail.p (tail.ell • e) 1 = x := by
    rw [hscale, ← expMapIntrinsic_def]
    exact tail.exp_eq
  have hcomp :=
    Geometry.Riemannian.branchHess_le_of_minimizing_of_sectional_curvature_nonnegative
      (I := I) g hEnorm tail.p e tail.ell tail.branch tail.ell_pos he_unit
        hsrc hmin hsec_tail
  rw [hend'] at hcomp
  obtain ⟨U, hUopen, hxU, hbrU⟩ :=
    branchRadius_open (I := I) tail.branch tail.source_mem
      (Real.sqrt_pos.mp (tail.u_norm.symm ▸ tail.ell_pos))
  rw [tail.exp_eq] at hxU
  have hhess := hessFun_add_const (I := I) g tail.left hUopen hbrU hxU
  refine ⟨rho, U, hUopen, hxU, contMDiffOn_const.add hbrU,
    hrho_x, hupper, hgrad_norm, ?_⟩
  intro Y
  have htail_bound :
      hessFun (I := I) g rho x Y Y ≤ g.inner x Y Y / tail.ell := by
    change hessFun (I := I) g
        (fun y => tail.left + branchRadius (I := I) g tail.branch y) x Y Y ≤ _
    rw [show hessFun (I := I) g
        (fun y => tail.left + branchRadius (I := I) g tail.branch y) x =
          hessFun (I := I) g (branchRadius (I := I) g tail.branch) x from hhess]
    exact hcomp Y
  refine htail_bound.trans ?_
  apply (div_le_div_iff₀ tail.ell_pos hr).2
  have hnorm : 0 ≤ g.inner x Y Y := gInner_self_nonneg (I := I) g x Y
  have hrell : r ≤ 2 * tail.ell := by
    linarith [tail.half_le]
  nlinarith [mul_nonneg hnorm (sub_nonneg.mpr hrell)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem calabiDist_hess_support
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {O x : M} (hOx : O ≠ x)
    (hfin : riemannianEDist I O x ≠ (⊤ : ENNReal)) :
    let r := (riemannianEDist I O x).toReal
    ∃ rho : M → Real,
      ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
      rho x = r ∧
      (∀ᶠ y in nhds x, (riemannianEDist I O y).toReal ≤ rho y) ∧
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) = 1 ∧
      ∀ Y : TangentSpace I x,
        hessFun (I := I) g rho x Y Y ≤ 2 * g.inner x Y Y / r := by
  dsimp only
  obtain ⟨rho, U, hU, hxU, hrho, hvalue, hupper, hgrad, hhess⟩ :=
    calabiDist_hess_support_on (I := I) (M := M) g hEnorm hsec hOx hfin
  exact ⟨rho, hrho.contMDiffAt (hU.mem_nhds hxU), hvalue, hupper,
    hgrad, hhess⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem calabiDist_hess_support_of_complete_metric
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {O x : M} (hOx : O ≠ x)
    (hfin : riemannianEDistOf (I := I) g O x ≠ (⊤ : ENNReal)) :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    letI : TopologicalSpace.MetrizableSpace M :=
      Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : RiemannianBundle (fun y : M => TangentSpace I y) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M := inferInstance
    letI : CompleteSpace M := hcomplete.complete
    let r := (riemannianEDist I O x).toReal
    ∃ rho : M → Real,
      ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
      rho x = r ∧
      (∀ᶠ y in nhds x, (riemannianEDist I O y).toReal ≤ rho y) ∧
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) = 1 ∧
      ∀ Y : TangentSpace I x,
        hessFun (I := I) g rho x Y Y ≤ 2 * g.inner x Y Y / r := by
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let _ : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := inferInstance
  let _ : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro y v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g y v
  have hfin' : riemannianEDist I O x ≠ (⊤ : ENNReal) := by
    simpa [riemannianEDistOf] using hfin
  exact calabiDist_hess_support (I := I) (M := M) g hEnorm hsec hOx hfin'

end DifferentialGeometry

end
