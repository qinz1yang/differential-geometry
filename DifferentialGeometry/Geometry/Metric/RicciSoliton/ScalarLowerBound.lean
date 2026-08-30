import DifferentialGeometry.Geometry.Comparison.DistanceCalabi
import DifferentialGeometry.Geometry.Comparison.HessianAlongGeodesic
import DifferentialGeometry.Geometry.Comparison.HopfRinowProper
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciPointwise
import DifferentialGeometry.Geometry.Comparison.Volume.JacobiRiccati
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Metric.InnerExpansion
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Identities
import DifferentialGeometry.Geometry.Operator.LaplacianMinimum
import DifferentialGeometry.Geometry.Operator.WeightedOmoriYau
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricContinuity

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open Riemannian
open Riemannian.BonnetMyers
open Riemannian.CovariantDerivativeAlong
open Riemannian.Exponential
open Riemannian.Geodesic
open Riemannian.Variation
open Riemannian.Volume
open Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

private theorem log_one_add_sq_hasDerivAt (t : Real) :
    HasDerivAt (fun s : Real => Real.log (1 + s ^ 2))
      (2 * t / (1 + t ^ 2)) t := by
  have hpoly : HasDerivAt (fun s : Real => 1 + s ^ 2) (2 * t) t := by
    convert! ((hasDerivAt_id t).pow 2).const_add 1 using 1
    all_goals norm_num
  exact hpoly.log (by positivity)

private theorem deriv_log_one_add_sq (t : Real) :
    deriv (fun s : Real => Real.log (1 + s ^ 2)) t =
      2 * t / (1 + t ^ 2) :=
  (log_one_add_sq_hasDerivAt t).deriv

private theorem deriv_deriv_log_one_add_sq (t : Real) :
    deriv (deriv (fun s : Real => Real.log (1 + s ^ 2))) t =
      2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2 := by
  have hfirst :
      deriv (fun s : Real => Real.log (1 + s ^ 2)) =
        fun s => 2 * s / (1 + s ^ 2) := by
    funext s
    exact deriv_log_one_add_sq s
  rw [hfirst]
  have hnum : HasDerivAt (fun s : Real => 2 * s) 2 t := by
    convert! (hasDerivAt_id t).const_mul 2 using 1
    all_goals norm_num
  have hden : HasDerivAt (fun s : Real => 1 + s ^ 2) (2 * t) t := by
    convert! ((hasDerivAt_id t).pow 2).const_add 1 using 1
    all_goals norm_num
  have hquot := hnum.div hden (by positivity)
  change deriv ((fun s : Real => 2 * s) / fun s => 1 + s ^ 2) t = _
  rw [hquot.deriv]
  ring

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem exists_log_one_add_sq_distance_support_data
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (O x : M) (r : Real) (hr : 0 < r) (rho : M → Real)
    (hrho_inf : ContMDiffAt I 𝓘(Real, Real) ∞ rho x)
    (hrho_x : rho x = r)
    (hupper : ∀ᶠ y in 𝓝 x,
      (riemannianEDistOf (I := I) g O y).toReal ≤ rho y)
    (hrho_eventually : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) rho y)
    (hgrad_rho : MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M => gradientFun (I := I) g rho y) x)
    (hnorm : g.inner x (gradientFun (I := I) g rho x)
      (gradientFun (I := I) g rho x) = 1) :
    ∃ phi : M → Real,
      ContMDiffAt I 𝓘(Real, Real) ∞ phi x ∧
      phi x = Real.log (1 + r ^ 2) ∧
      (∀ᶠ y in 𝓝 x,
        Real.log (1 + (riemannianEDistOf (I := I) g O y).toReal ^ 2) ≤ phi y) ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) phi y) ∧
      MDifferentiableAt I (I.prod 𝓘(Real, E))
        (T% fun y : M => gradientFun (I := I) g phi y) x ∧
      Real.sqrt (g.inner x (gradientFun (I := I) g phi x)
        (gradientFun (I := I) g phi x)) = 2 * r / (1 + r ^ 2) ∧
      laplacian (I := I) (LeviCivita (I := I) g) g phi x -
          g.inner x (gradFun (I := I) g f x)
            (gradientFun (I := I) g phi x) =
        (2 * r / (1 + r ^ 2)) *
          (laplacian (I := I) (LeviCivita (I := I) g) g rho x -
            g.inner x (gradFun (I := I) g f x)
              (gradientFun (I := I) g rho x)) +
          2 * (1 - r ^ 2) / (1 + r ^ 2) ^ 2 := by
  let outer : Real → Real := fun s => Real.log (1 + s ^ 2)
  let phi : M → Real := fun y => outer (rho y)
  have hinside : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => 1 + rho y ^ 2) x :=
    contMDiffAt_const.add (hrho_inf.pow 2)
  have hphi_inf : ContMDiffAt I 𝓘(Real, Real) ∞ phi x := by
    exact (Real.contDiffAt_log.2 (by positivity : (1 + rho x ^ 2) ≠ 0)).comp_contMDiffAt
      (x := x) hinside
  have hrho_nonneg : ∀ᶠ y in 𝓝 x, 0 ≤ rho y := by
    exact hrho_inf.continuousAt
      (Ici_mem_nhds (hrho_x.symm ▸ hr))
  have hphi_upper : ∀ᶠ y in 𝓝 x,
      Real.log (1 + (riemannianEDistOf (I := I) g O y).toReal ^ 2) ≤ phi y := by
    filter_upwards [hupper, hrho_nonneg] with y hy hnonneg
    have hdist : 0 ≤ (riemannianEDistOf (I := I) g O y).toReal :=
      ENNReal.toReal_nonneg
    apply Real.log_le_log (by positivity)
    nlinarith
  have hphi_eventually : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) phi y := by
    filter_upwards [hrho_eventually] with y hy
    have hpoly : MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => 1 + rho z ^ 2) y :=
      mdifferentiableAt_const.add (hy.pow 2)
    exact (Real.differentiableAt_log
      (by positivity : 1 + rho y ^ 2 ≠ 0)).mdifferentiableAt.comp y hpoly
  have hgrad_phi : MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M => gradientFun (I := I) g phi y) x :=
    (gradientFun_contMDiffAt (I := I) g hphi_inf).mdifferentiableAt (by simp)
  have hrho_mdiff : MDifferentiableAt I 𝓘(Real, Real) rho x :=
    hrho_inf.mdifferentiableAt (by simp)
  have houter_at : DifferentiableAt Real outer (rho x) := by
    rw [hrho_x]
    exact (log_one_add_sq_hasDerivAt r).differentiableAt
  have hgrad_eq : gradientFun (I := I) g phi x =
      (2 * r / (1 + r ^ 2)) • gradientFun (I := I) g rho x := by
    have h := gradientFun_comp (I := I) g houter_at hrho_mdiff
    change gradientFun (I := I) g phi x = _ at h
    rw [hrho_x, deriv_log_one_add_sq] at h
    exact h
  have hcoef : 0 ≤ 2 * r / (1 + r ^ 2) := by positivity
  have hgrad_norm : Real.sqrt
      (g.inner x (gradientFun (I := I) g phi x)
        (gradientFun (I := I) g phi x)) = 2 * r / (1 + r ^ 2) := by
    rw [hgrad_eq, sqrt_inner_smul, abs_of_nonneg hcoef, hnorm, Real.sqrt_one,
      mul_one]
  have houter_diff : Differentiable Real outer :=
    fun t => (log_one_add_sq_hasDerivAt t).differentiableAt
  have houter_deriv_diff : DifferentiableAt Real (deriv outer) r := by
    have hfirst : deriv outer = fun s => 2 * s / (1 + s ^ 2) := by
      funext s
      exact deriv_log_one_add_sq s
    rw [hfirst]
    have : 1 + r ^ 2 ≠ 0 := by positivity
    fun_prop
  have houter_deriv_diff_x : DifferentiableAt Real (deriv outer) (rho x) := by
    rw [hrho_x]
    exact houter_deriv_diff
  have hlap := laplacian_comp_at (I := I)
    (LeviCivita (I := I) g) g houter_diff houter_deriv_diff_x
      hrho_eventually hgrad_rho
  change laplacian (I := I) (LeviCivita (I := I) g) g phi x = _ at hlap
  rw [hrho_x, deriv_log_one_add_sq, deriv_deriv_log_one_add_sq, hnorm] at hlap
  refine ⟨phi, hphi_inf, ?_, hphi_upper, hphi_eventually, hgrad_phi,
    hgrad_norm, ?_⟩
  · simp only [phi, outer, hrho_x]
  · rw [hlap, hgrad_eq, map_smul, smul_eq_mul]
    ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_log_one_add_sq_distance_base_support
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (f : C^∞⟮I, M; Real⟯) (O : M) :
    ∃ phi : M → Real,
      isWeightedLaplacianUpperSupportAt (I := I) g f
        (fun y => Real.log
          (1 + (riemannianEDistOf (I := I) g O y).toReal ^ 2))
        O 1
        |laplacian (I := I) (LeviCivita (I := I) g) g phi O -
          g.inner O (gradFun (I := I) g f O)
            (gradientFun (I := I) g phi O)| phi := by
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
  have hzero : ¬ IsConjVec (I := I) g hEnorm O (0 : E) := by
    unfold IsConjVec
    simp only [not_not]
    have hfun :
        (fun b : E => expMapIntrinsic (I := I) g hEnorm O
          ((tangentSpaceModelContinuousLinearEquiv (I := I) O).symm b)) =
          fun b : E => expMapIntrinsic (I := I) g hEnorm O
            (show TangentSpace I O from b) := by
      funext b
      rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
    rw [hfun, mfderiv_expMapIntrinsic_at_zero (I := I) g hEnorm O]
    intro a b hab
    have habModel := congrArg
      (tangentSpaceModelContinuousLinearEquiv
        (I := I)
        (expMapIntrinsic (I := I) g hEnorm O
          ((tangentSpaceModelContinuousLinearEquiv
            (I := I) O).symm (0 : E)))) hab
    change a = b at habModel
    exact habModel
  obtain ⟨B, hBzero⟩ := branch_of_not_conj (I := I) g hEnorm hzero
  have hOexp : expMapIntrinsic (I := I) g hEnorm O
      (0 : TangentSpace I O) = O :=
    expMapIntrinsic_zero (I := I) g hEnorm O
  have hOdom : O ∈ B.dom := by
    have hmap : B.hom (0 : E) ∈ B.dom := B.hom.map_source hBzero
    have hhom : B.hom (0 : E) = O := by
      have h := B.hom_eq hBzero
      change expMapIntrinsic (I := I) g hEnorm O (0 : TangentSpace I O) =
        B.hom (0 : E) at h
      rw [hOexp] at h
      exact h.symm
    simpa only [hhom] using hmap
  have hBinvO : B.inv O = 0 := by
    have h := B.left_inv hBzero
    change B.inv (expMapIntrinsic (I := I) g hEnorm O
      (0 : TangentSpace I O)) = (0 : E) at h
    rw [hOexp] at h
    exact h
  let energy : M → Real := branchEnergy (I := I) g B
  let phi : M → Real := fun y => Real.log (1 + 2 * energy y)
  have henergyOn : ContMDiffOn I (modelWithCornersSelf Real Real) ∞ energy B.dom := by
    have hinv := B.inv_inf
    let e : E →L[Real] TangentSpace I O :=
      (tangentSpaceModelContinuousLinearEquiv (I := I) O).symm.toContinuousLinearMap
    have he : ContMDiffOn I (modelWithCornersSelf Real (TangentSpace I O)) ∞
        (fun y : M => e (B.inv y)) B.dom :=
      contMDiffOn_const.clm_apply hinv
    have hinner : ContMDiffOn I (modelWithCornersSelf Real Real) ∞
        (fun y : M => g.inner O (e (B.inv y)) (e (B.inv y))) B.dom :=
      (contMDiffOn_const.clm_apply he).clm_apply he
    have henergy' : ContMDiffOn I (modelWithCornersSelf Real Real) ∞
        (fun y : M => (1 / 2 : Real) *
          g.inner O (e (B.inv y)) (e (B.inv y))) B.dom :=
      contMDiffOn_const.mul hinner
    refine henergy'.congr ?_
    intro y hy
    simp only [energy, branchEnergy]
    rfl
  have henergyO : energy O = 0 := by
    simp only [energy, branchEnergy, hBinvO]
    norm_num
  have hinsideOn : ContMDiffOn I (modelWithCornersSelf Real Real) ∞
      (fun y : M => 1 + 2 * energy y) B.dom :=
    contMDiffOn_const.add (contMDiffOn_const.mul henergyOn)
  have hinsideO : 1 + 2 * energy O ≠ 0 := by rw [henergyO]; norm_num
  have hphiO : ContMDiffAt I (modelWithCornersSelf Real Real) ∞ phi O := by
    exact (Real.contDiffAt_log.2 hinsideO).comp_contMDiffAt
      (x := O) (hinsideOn.contMDiffAt (B.hom.open_target.mem_nhds hOdom))
  have hupper : ∀ᶠ y in nhds O,
      Real.log (1 + (riemannianEDistOf (I := I) g O y).toReal ^ 2) ≤ phi y := by
    filter_upwards [B.hom.open_target.mem_nhds hOdom] with y hy
    have hed := B.edist_le_radius hy
    have hr_nonneg : 0 ≤ branchRadius (I := I) g B y := Real.sqrt_nonneg _
    have hreal : (riemannianEDist I O y).toReal ≤
        branchRadius (I := I) g B y := by
      have := ENNReal.toReal_mono (by simp) hed
      simpa only [ENNReal.toReal_ofReal hr_nonneg] using this
    have hsquare : (riemannianEDist I O y).toReal ^ 2 ≤ 2 * energy y := by
      have hs : (riemannianEDist I O y).toReal ^ 2 ≤
          branchRadius (I := I) g B y ^ 2 := by
        nlinarith [(ENNReal.toReal_nonneg :
          0 ≤ (riemannianEDist I O y).toReal)]
      have hradiusSq : branchRadius (I := I) g B y ^ 2 = 2 * energy y := by
        simp only [branchRadius, energy, branchEnergy]
        rw [Real.sq_sqrt]
        · ring
        · exact gInner_self_nonneg (I := I) g O _
      rwa [hradiusSq] at hs
    apply Real.log_le_log (by positivity)
    change 1 + (riemannianEDist I O y).toReal ^ 2 ≤ 1 + 2 * energy y
    linarith
  have hphi_value : phi O = 0 := by
    simp only [phi, henergyO]
    norm_num
  have hpsi_value : Real.log
      (1 + (riemannianEDistOf (I := I) g O O).toReal ^ 2) = 0 := by
    rw [riemannianEDistOf_self]
    norm_num
  have hphi_eventually : ∀ᶠ y in nhds O,
      MDifferentiableAt I (modelWithCornersSelf Real Real) phi y := by
    have hphiOn : ContMDiffOn I (modelWithCornersSelf Real Real) ∞ phi
        (B.dom ∩ {y | 0 < 1 + 2 * energy y}) := by
      intro y hy
      exact (Real.contDiffAt_log.2 hy.2.ne').contMDiffAt.comp_contMDiffWithinAt y
        (hinsideOn.mono inter_subset_left y hy)
    have hmem : O ∈ B.dom ∩ {y | 0 < 1 + 2 * energy y} := by
      refine ⟨hOdom, ?_⟩
      change 0 < 1 + 2 * energy O
      rw [henergyO]
      norm_num
    have hopen : IsOpen (B.dom ∩ {y | 0 < 1 + 2 * energy y}) := by
      exact hinsideOn.continuousOn.isOpen_inter_preimage
        B.hom.open_target isOpen_Ioi
    filter_upwards [hopen.mem_nhds hmem] with y hy
    exact ((hphiOn y hy).contMDiffAt
      (hopen.mem_nhds hy)).mdifferentiableAt (by simp)
  have hgrad_phi : MDifferentiableAt I (I.prod (modelWithCornersSelf Real E))
      (T% fun y : M => gradientFun (I := I) g phi y) O :=
    (gradientFun_contMDiffAt (I := I) g hphiO).mdifferentiableAt (by simp)
  have hlocalMin : IsLocalMin phi O := by
    filter_upwards [hupper] with y hy
    rw [hphi_value]
    exact le_trans (Real.log_nonneg (by norm_num)) hy
  have hgrad_zero : gradientFun (I := I) g phi O = 0 :=
    gradientFun_eq_zero_at_spatial_min (I := I) g hlocalMin
      (hphiO.mdifferentiableAt (by simp))
  refine ⟨phi, hphiO, ?_, hupper, hphi_eventually, hgrad_phi, ?_, ?_⟩
  · change phi O = Real.log
      (1 + (riemannianEDistOf (I := I) g O O).toReal ^ 2)
    rw [hphi_value, hpsi_value]
  · rw [hgrad_zero]
    simp
  · exact le_abs_self _

def isWeightedDistanceUpperSupport
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (σ : Real) (O x : M) (r C : Real) (rho : M → Real) : Prop :=
  ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
    rho x = r ∧
    (∀ᶠ y in 𝓝 x, (riemannianEDistOf (I := I) g O y).toReal ≤ rho y) ∧
    (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) rho y) ∧
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M => gradientFun (I := I) g rho y) x ∧
    g.inner x (gradientFun (I := I) g rho x)
        (gradientFun (I := I) g rho x) = 1 ∧
    laplacian (I := I) (LeviCivita (I := I) g) g rho x -
        g.inner x (gradFun (I := I) g f x)
          (gradientFun (I := I) g rho x) ≤ C - σ / 2 * r

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_local_soliton_control
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (hcomplete : RiemannianMetricComplete (I := I) g) (O : M) :
    ∃ q B : Real, 0 ≤ q ∧ 0 ≤ B ∧
      (0 < Module.finrank Real E - 1 →
        ∀ y : M,
          riemannianEDistOf (I := I) g O y ≤ ENNReal.ofReal 4 →
            ∀ v : TangentSpace I y,
              -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) *
                  g.inner y v v ≤ ricciTensor (I := I) g y v v) ∧
      (∀ y : M,
        riemannianEDistOf (I := I) g O y ≤ ENNReal.ofReal 4 →
          Real.sqrt (normGradSqFun (I := I) g f y) ≤ B) := by
  classical
  let K : Set M := {y : M |
    riemannianEDistOf (I := I) g O y ≤ ENNReal.ofReal 4}
  let A : M → Real := fun y =>
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04 (I := I) (M := M) g y))
  let G : M → Real := fun y =>
    Real.sqrt (normGradSqFun (I := I) g f y)
  have hK : IsCompact K :=
    RiemannianMetricComplete.closedEBall_isCompact (I := I) hcomplete O 4
  have hOK : O ∈ K := by
    dsimp only [K]
    change riemannianEDistOf (I := I) g O O ≤ ENNReal.ofReal 4
    rw [riemannianEDistOf_self]
    exact bot_le
  have hA : Continuous A := by
    exact Real.continuous_sqrt.comp
      (Tensor0SBundle.normSq0S_cont (I := I) g
        (metricRm04 (I := I) (M := M) g))
  have hG : Continuous G := by
    exact Real.continuous_sqrt.comp
      (normGradSqFun_continuous (I := I) g f.contMDiff)
  obtain ⟨a, haK, ha⟩ := hK.exists_isMaxOn ⟨O, hOK⟩ hA.continuousOn
  obtain ⟨b, hbK, hb⟩ := hK.exists_isMaxOn ⟨O, hOK⟩ hG.continuousOn
  let Rm : Real := A a
  let B : Real := G b
  let q : Real := (Module.finrank Real E : Real) ^ 2 * Rm + 1
  have hRm : 0 ≤ Rm := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hq : 0 ≤ q := by
    dsimp only [q]
    positivity
  refine ⟨q, B, hq, hB, ?_, ?_⟩
  · intro hd y hy v
    have hyK : y ∈ K := hy
    have hAy : A y ≤ Rm := ha hyK
    have hlocal := ricciLowerAt_of_rm (I := I) g hAy v
    have hdR : (1 : Real) ≤ ((Module.finrank Real E - 1 : Nat) : Real) := by
      exact_mod_cast hd
    have hnRm : 0 ≤ (Module.finrank Real E : Real) ^ 2 * Rm :=
      mul_nonneg (sq_nonneg _) hRm
    have hcoef :
        (Module.finrank Real E : Real) ^ 2 * Rm ≤
          ((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2 := by
      dsimp only [q]
      nlinarith
    have hinner := gInner_self_nonneg (I := I) g y v
    have hmul := mul_le_mul_of_nonneg_right hcoef hinner
    apply le_trans _ hlocal
    calc
      -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) * g.inner y v v =
          -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2 *
            g.inner y v v) := by ring
      _ ≤ -((Module.finrank Real E : Real) ^ 2 * Rm * g.inner y v v) :=
        neg_le_neg hmul
      _ = -((Module.finrank Real E : Real) ^ 2 * Rm) * g.inner y v v := by ring
  · intro y hy
    exact hb hy

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private theorem gradientRicciSoliton_weightedMean_antitone
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (f : C^∞⟮I, M; Real⟯) (σ : Real)
    (hsol : gradientRicciSoliton (I := I) g f σ)
    {O x : M} {r : Real}
    (tail : CalabiTailData (I := I) g hEnorm O x r)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I tail.p)
    (hv : LinearIndependent Real v)
    (hperp : ∀ i, g.inner tail.p tail.u (v i) = 0)
    {s : Real} (hs : 0 < s) :
    let γ : Real → M :=
      intrinsicGeodesic (I := I) g hEnorm tail.p tail.u
    let V := fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (v i)
    let ell := Real.sqrt (g.inner tail.p tail.u tail.u)
    AntitoneOn
      (fun t => curveMean (I := I) g γ V t - deriv (f ∘ γ) t +
        σ / 2 * ell ^ 2 * t) (Set.Icc s 1) := by
  classical
  dsimp only
  let γ : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm tail.p tail.u
  let V : Fin (Module.finrank Real E - 1) → ∀ t, TangentSpace I (γ t) :=
    fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (v i)
  let ell : Real := Real.sqrt (g.inner tail.p tail.u tail.u)
  let z : Real → Real := fun t =>
    curveMean (I := I) g γ V t - deriv (f ∘ γ) t +
      σ / 2 * ell ^ 2 * t
  have hell : 0 < ell := by
    dsimp only [ell]
    rw [tail.u_norm]
    exact tail.ell_pos
  have hγInf : ContMDiff 𝓘(Real, Real) I ∞ γ :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm tail.p tail.u
  have hfγM : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ (f ∘ γ) :=
    f.contMDiff.comp hγInf
  have hfγ : ContDiff Real ∞ (f ∘ γ) :=
    contMDiff_iff_contDiff.mp hfγM
  have hspeed : ∀ t : Real,
      g.inner (γ t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t) = ell ^ 2 := by
    intro t
    calc
      g.inner (γ t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t) =
          g.inner tail.p tail.u tail.u := by
        exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm tail.p tail.u t
      _ = ell ^ 2 := (Real.sq_sqrt
        (gInner_self_nonneg (I := I) g tail.p tail.u)).symm
  have hderiv : ∀ t ∈ Set.Ioo (0 : Real) tail.b,
      HasDerivAt z
          (-Matrix.trace ((curveShape (I := I) g γ V t) ^ 2)) t ∧
        0 ≤ Matrix.trace ((curveShape (I := I) g γ V t) ^ 2) := by
    intro t ht
    have hγt : ContMDiffAt 𝓘(Real, Real) I (2 : WithTop ℕ∞) γ t :=
      hγInf.contMDiffAt.of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hVdiff : ∀ i,
        DifferentiableAt Real (chartRepAt (I := I) γ (V i) t) t := by
      intro i
      simpa only [γ, V] using
        (intrJacobi_diff (I := I) g hEnorm tail.p tail.u (v i) t).1
    have hDVdiff : ∀ i,
        DifferentiableAt Real
          (chartRepAt (I := I) γ
            (fun a => covDerivAlong (I := I) g γ (V i) a) t) t := by
      intro i
      simpa only [γ, V] using
        (intrJacobi_diff (I := I) g hEnorm tail.p tail.u (v i) t).2
    have hVperp : ∀ i,
        g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0 := by
      intro i
      simpa only [γ, V] using
        Riemannian.VolumeComparison.intrJacobi_perp_ne
          (I := I) g hEnorm tail.p tail.u (v i)
          ht.1.ne' (hperp i)
    have hDVperp : ∀ i,
        g.inner (γ t) (curveVelocity (I := I) γ t)
          (covDerivAlong (I := I) g γ (V i) t) = 0 := by
      intro i
      simpa only [γ, V] using
        intrJacobi_dperp
          (I := I) g hEnorm tail.p tail.u (v i)
          ht.1.ne' (hperp i)
    have hLI : LinearIndependent Real fun i => V i t := by
      simpa only [γ, V] using
        intrinsicJacobi_linearIndependent_of_noConjVec
          (I := I) g hEnorm tail.p tail.u v hv ht.1.ne'
            (tail.no_conj t ht)
    have hW : ∀ i j, jacobiWronskian (I := I) g γ (V i) (V j) t = 0 := by
      intro i j
      exact wronskian_eq_zero (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
        g γ (V i) (V j)
        (hγInf.of_le
          (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
        (fun a _ => by simpa only [γ, V] using
          (intrJacobi_diff (I := I) g hEnorm tail.p tail.u (v i) a).1)
        (fun a _ => by simpa only [γ, V] using
          (intrJacobi_diff (I := I) g hEnorm tail.p tail.u (v j) a).1)
        (fun a _ => by simpa only [γ, V] using
          (intrJacobi_diff (I := I) g hEnorm tail.p tail.u (v i) a).2)
        (fun a _ => by simpa only [γ, V] using
          (intrJacobi_diff (I := I) g hEnorm tail.p tail.u (v j) a).2)
        (fun a _ => by
          change IsJacobiAt (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm tail.p tail.u)
            (intrinsicJacobi (I := I) g hEnorm tail.p tail.u (v i)) a
          exact intrinsic_jacobi
            (I := I) g hEnorm tail.p (tail.u : E) (v i : E) a)
        (fun a _ => by
          change IsJacobiAt (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm tail.p tail.u)
            (intrinsicJacobi (I := I) g hEnorm tail.p tail.u (v j)) a
          exact intrinsic_jacobi
            (I := I) g hEnorm tail.p (tail.u : E) (v j : E) a)
        (by simp [V]) (by simp [V]) t ⟨ht.1.le, ht.2.le⟩
    have hJ : ∀ i, IsJacobiAt (I := I) g γ (V i) t := by
      intro i
      exact intrinsic_jacobi
        (I := I) g hEnorm tail.p (tail.u : E) (v i : E) t
    have hspeedPos : 0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) := by
      rw [hspeed]
      positivity
    obtain ⟨e, heON, heperp⟩ :=
      exists_perp_pos (I := I) g (γ t) (curveVelocity (I := I) γ t) hspeedPos
    have hmean := hasDerivAt_mean_perp (I := I) (n := (2 : WithTop ℕ∞))
      (by norm_num) g γ V t (curveVelocity (I := I) γ t) (by simp)
      hspeedPos hVperp hDVperp hγt hVdiff hDVdiff hLI hW hJ
    have hcurv := curvTrace_eq_ricci (I := I) g γ V t
      (curveVelocity (I := I) γ t) rfl (by simp) hspeedPos hVperp hLI
      e heON heperp
    have hshape := mean_sq_le_shape (I := I) g γ V t
      (curveVelocity (I := I) γ t) (by simp) hspeedPos hVperp hDVperp hLI hW
      e heON heperp
    have hshapeNonneg :
        0 ≤ Matrix.trace ((curveShape (I := I) g γ V t) ^ 2) := by
      by_cases hd0 : Module.finrank Real E - 1 = 0
      · let _ : IsEmpty (Fin (Module.finrank Real E - 1)) := by
          rw [hd0]
          exact Fin.isEmpty
        simp only [Matrix.trace, Finset.sum_of_isEmpty]
        exact le_rfl
      · have hd : 0 < Module.finrank Real E - 1 := Nat.pos_of_ne_zero hd0
        have hdR : (0 : Real) < ((Module.finrank Real E - 1 : Nat) : Real) := by
          exact_mod_cast hd
        nlinarith [sq_nonneg (curveMean (I := I) g γ V t)]
    have hpotSecond := deriv2_comp_geo (I := I) g f.contMDiff hγInf
      (intrinsicGeodesic_isGeodesic (I := I) g hEnorm tail.p tail.u) t
    change (deriv^[2] (f ∘ γ)) t =
      hessFun (I := I) g f (γ t)
        (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) at hpotSecond
    have hpotDeriv : HasDerivAt (deriv (f ∘ γ))
        ((deriv^[2] (f ∘ γ)) t) t := by
      have hfγ2 : ContDiff Real 2 (f ∘ γ) := hfγ.of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
      exact (hfγ2.differentiable_deriv_two t).hasDerivAt
    have hlin : HasDerivAt (fun a : Real => σ / 2 * ell ^ 2 * a)
        (σ / 2 * ell ^ 2) t := by
      exact hasDerivAt_const_mul (x := t) (σ / 2 * ell ^ 2)
    have hz := (hmean.sub hpotDeriv).add hlin
    refine ⟨hz.congr_deriv ?_, hshapeNonneg⟩
    · rw [hcurv, hpotSecond]
      have hsolt := hsol (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t)
      rw [hspeed] at hsolt
      linarith
  have hderivIcc : ∀ t ∈ Set.Icc s 1,
      HasDerivAt z (-Matrix.trace ((curveShape (I := I) g γ V t) ^ 2)) t := by
    intro t ht
    exact (hderiv t ⟨hs.trans_le ht.1, ht.2.trans_lt tail.one_lt⟩).1
  have hcont : ContinuousOn z (Set.Icc s 1) := by
    intro t ht
    exact (hderivIcc t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn Real z (interior (Set.Icc s 1)) := by
    intro t ht
    exact (hderivIcc t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc s 1) hcont hdiff
    (fun t ht => by
      rw [(hderivIcc t (interior_subset ht)).deriv]
      exact neg_nonpos.mpr
        (hderiv t ⟨hs.trans_le (interior_subset ht).1,
          (interior_subset ht).2.trans_lt tail.one_lt⟩).2)
  simpa only [z] using hanti

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem gradientRicciSoliton_exists_weightedDistanceUpperSupport
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (σ : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (O : M) :
    ∃ C : Real, ∀ x : M,
      3 ≤ (riemannianEDistOf (I := I) g O x).toReal →
        ∃ rho : M → Real,
          isWeightedDistanceUpperSupport (I := I) g f σ O x
            (riemannianEDistOf (I := I) g O x).toReal C rho := by
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
  obtain ⟨q, B, hq, hB, hRic, hGrad⟩ :=
    exists_local_soliton_control (I := I) g f hcomplete O
  let d : Real := ((Module.finrank Real E - 1 : Nat) : Real)
  let C : Real := d + d * q + B + σ
  refine ⟨C, ?_⟩
  intro x hx
  let r : Real := (riemannianEDistOf (I := I) g O x).toReal
  have hr : 0 < r := by
    dsimp only [r]
    linarith
  have hfin : riemannianEDist I O x ≠ (⊤ : ENNReal) :=
    riemannianEDist_ne_top (I := I) O x
  obtain ⟨u, hexp, hlen⟩ :=
    minExp_of_ne_top (I := I) g hEnorm O x hfin
  have hr_eq : (riemannianEDist I O x).toReal = r := by
    rfl
  have hlen' : Real.sqrt (g.inner O u u) = r := hlen.trans hr_eq
  have hs₀ : 1 / r ∈ Set.Ioo (0 : Real) 1 := by
    constructor
    · positivity
    · apply (div_lt_one hr).2
      linarith
  have hs₀half : 1 / r ≤ (1 : Real) / 2 := by
    apply (div_le_div_iff₀ hr (by norm_num : (0 : Real) < 2)).2
    linarith
  obtain ⟨tail, hleft, hell⟩ :=
    exists_calabiTail_of_split (I := I) g hEnorm u hexp hlen' hr hr_eq.symm
      (1 / r) hs₀ hs₀half
  have hleft_one : tail.left = 1 := by
    rw [hleft]
    field_simp [hr.ne']
  have hell_sub : tail.ell = r - 1 := by
    rw [hell]
    field_simp [hr.ne']
  have hell_two : 2 ≤ tail.ell := by
    rw [hell_sub]
    linarith
  let γ : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm tail.p tail.u
  let s : Real := 1 / tail.ell
  let b : Real := 2 / tail.ell
  have hs : 0 < s := by
    dsimp only [s]
    positivity
  have hsb : s < b := by
    dsimp only [s, b]
    exact (div_lt_div_iff_of_pos_right tail.ell_pos).2 (by norm_num)
  have hb_one : b ≤ 1 := by
    dsimp only [b]
    apply (div_le_iff₀ tail.ell_pos).2
    simpa only [one_mul] using hell_two
  have hs_one : s ≤ 1 := by
    exact hsb.le.trans hb_one
  have hb_tail : b < tail.b := hb_one.trans_lt tail.one_lt
  have hball : ∀ t ∈ Set.Icc (0 : Real) b,
      riemannianEDistOf (I := I) g O (γ t) ≤ ENNReal.ofReal 4 := by
    intro t ht
    have hellt : 0 ≤ tail.ell * t :=
      mul_nonneg tail.ell_pos.le ht.1
    have hdist :=
      intrinsicGeodesic_riemannianEDist_le
        (I := I) g hEnorm tail.p tail.u
          (s := (0 : Real)) (t := t) ht.1
    have hseg :
        riemannianEDist I tail.p (γ t) ≤
          ENNReal.ofReal (tail.ell * t) := by
      rw [intrinsicGeodesic_zero (I := I) g hEnorm tail.p tail.u] at hdist
      simpa only [γ, tail.u_norm, sub_zero] using hdist
    have hellb : tail.ell * b = 2 := by
      dsimp only [b]
      field_simp [tail.ell_pos.ne']
    have hmul : tail.ell * t ≤ 2 := by
      calc
        tail.ell * t ≤ tail.ell * b :=
          mul_le_mul_of_nonneg_left ht.2 tail.ell_pos.le
        _ = 2 := hellb
    have hreal : tail.left + tail.ell * t ≤ 4 := by
      rw [hleft_one]
      linarith
    change riemannianEDist I O (γ t) ≤ ENNReal.ofReal 4
    calc
      riemannianEDist I O (γ t) ≤
          riemannianEDist I O tail.p + riemannianEDist I tail.p (γ t) :=
        Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal tail.left + ENNReal.ofReal (tail.ell * t) :=
        add_le_add tail.left_edist.le hseg
      _ = ENNReal.ofReal (tail.left + tail.ell * t) :=
        (ENNReal.ofReal_add tail.left_nonneg hellt).symm
      _ ≤ ENNReal.ofReal 4 := ENNReal.ofReal_le_ofReal hreal
  have hu_pos : 0 < g.inner tail.p tail.u tail.u := by
    apply Real.sqrt_pos.mp
    rw [tail.u_norm]
    exact tail.ell_pos
  have hno : ∀ t ∈ Set.Ioo (0 : Real) b,
      ¬ IsConjVec (I := I) g hEnorm tail.p
        ((t • tail.u : TangentSpace I tail.p) : E) := by
    intro t ht
    exact tail.no_conj t ⟨ht.1, ht.2.trans hb_tail⟩
  have hRicSeed : 0 < Module.finrank Real E - 1 →
      ∀ t ∈ Set.Ioo (0 : Real) b,
        -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) *
            g.inner (γ t) (curveVelocity (I := I) γ t)
              (curveVelocity (I := I) γ t) ≤
          ricciTensor (I := I) g (γ t)
            (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t) := by
    intro hd t ht
    exact hRic hd (γ t) (hball t ⟨ht.1.le, ht.2.le⟩)
      (curveVelocity (I := I) γ t)
  obtain ⟨w, hwLI, hwperp, hmean⟩ :=
    exists_intrMean_at_on (I := I) g hEnorm tail.p tail.u q s b
      hq hs hsb hu_pos hno hRicSeed
  dsimp only at hmean
  rw [tail.u_norm] at hmean
  have hsell : s * tail.ell = 1 := by
    dsimp only [s]
    field_simp [tail.ell_pos.ne']
  have hmean' :
      curveMean (I := I) g γ
          (fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (w i)) s /
          tail.ell ≤ d + d * q := by
    dsimp only [d]
    rw [hsell, div_one] at hmean
    exact hmean
  have hmeanRaw :
      curveMean (I := I) g γ
          (fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (w i)) s ≤
        (d + d * q) * tail.ell :=
    (div_le_iff₀ tail.ell_pos).1 hmean'
  have hγInf : ContMDiff 𝓘(Real, Real) I ∞ γ :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm tail.p tail.u
  have hderivSeed :=
    deriv_comp_eq_inner_grad_velocity (I := I) g f.contMDiff hγInf s
  change deriv (f ∘ γ) s =
    g.inner (γ s) (gradFun (I := I) g f (γ s))
      (curveVelocity (I := I) γ s) at hderivSeed
  have hspeedSeed :
      Real.sqrt (g.inner (γ s) (curveVelocity (I := I) γ s)
        (curveVelocity (I := I) γ s)) = tail.ell := by
    have hspeed :=
      intrinsicGeodesic_speedSq_eq (I := I) g hEnorm tail.p tail.u s
    change g.inner (γ s) (curveVelocity (I := I) γ s)
      (curveVelocity (I := I) γ s) = g.inner tail.p tail.u tail.u at hspeed
    rw [hspeed, tail.u_norm]
  have hcs := abs_inner_le_sqrt_mul_sqrt (I := I) g (γ s)
    (gradFun (I := I) g f (γ s)) (curveVelocity (I := I) γ s)
  change |g.inner (γ s) (gradFun (I := I) g f (γ s))
      (curveVelocity (I := I) γ s)| ≤
    Real.sqrt (normGradSqFun (I := I) g f (γ s)) *
      Real.sqrt (g.inner (γ s) (curveVelocity (I := I) γ s)
        (curveVelocity (I := I) γ s)) at hcs
  rw [← hderivSeed, hspeedSeed] at hcs
  have hgradSeed : Real.sqrt (normGradSqFun (I := I) g f (γ s)) ≤ B :=
    hGrad (γ s) (hball s ⟨hs.le, hsb.le⟩)
  have hderivAbs : |deriv (f ∘ γ) s| ≤ B * tail.ell :=
    hcs.trans (mul_le_mul_of_nonneg_right hgradSeed tail.ell_pos.le)
  have hpotRaw : -deriv (f ∘ γ) s ≤ B * tail.ell :=
    (neg_le_abs _).trans hderivAbs
  have hanti :=
    gradientRicciSoliton_weightedMean_antitone
      (I := I) g hEnorm f σ hsol tail w hwLI hwperp hs
  dsimp only at hanti
  rw [tail.u_norm] at hanti
  have htransport := hanti ⟨le_rfl, hs_one⟩ ⟨hs_one, le_rfl⟩ hs_one
  have hseedSigma : σ / 2 * tail.ell ^ 2 * s = σ / 2 * tail.ell := by
    calc
      σ / 2 * tail.ell ^ 2 * s =
          σ / 2 * tail.ell * (s * tail.ell) := by ring
      _ = σ / 2 * tail.ell := by rw [hsell, mul_one]
  dsimp only at htransport
  rw [mul_one, hseedSigma] at htransport
  change curveMean (I := I) g γ
      (fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (w i)) 1 -
        deriv (f ∘ γ) 1 + σ / 2 * tail.ell ^ 2 ≤
      curveMean (I := I) g γ
          (fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (w i)) s -
        deriv (f ∘ γ) s + σ / 2 * tail.ell at htransport
  have hendpointEll :
      curveMean (I := I) g γ
          (fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (w i)) 1 -
          deriv (f ∘ γ) 1 ≤
        (d + d * q + B + σ / 2 - σ / 2 * tail.ell) * tail.ell := by
    nlinarith
  have hendpointRaw :
      curveMean (I := I) g γ
          (fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (w i)) 1 -
          deriv (f ∘ γ) 1 ≤
        C * tail.ell - σ / 2 * r * tail.ell := by
    calc
      _ ≤ (d + d * q + B + σ / 2 - σ / 2 * tail.ell) * tail.ell :=
        hendpointEll
      _ = C * tail.ell - σ / 2 * r * tail.ell := by
        dsimp only [C]
        rw [hell_sub]
        ring
  obtain ⟨hrho_inf, hrho_x, hupper, hrho_ev, hrho_grad,
      hgrad_norm, hlap_eq⟩ :=
    calabiData_of_tail_of_frame (I := I) g hEnorm tail w hwLI hwperp
  let rho : M → Real := fun y =>
    tail.left + branchRadius (I := I) g tail.branch y
  have hinner_eq := tail.inner_grad_support_eq_deriv f
  have hweighted :
      laplacian (I := I) (LeviCivita (I := I) g) g rho x -
          g.inner x (gradFun (I := I) g f x)
            (gradientFun (I := I) g rho x) ≤ C - σ / 2 * r := by
    rw [hlap_eq, hinner_eq]
    rw [← sub_div]
    apply (div_le_iff₀ tail.ell_pos).2
    calc
      _ ≤ C * tail.ell - σ / 2 * r * tail.ell := hendpointRaw
      _ = (C - σ / 2 * r) * tail.ell := by ring
  refine ⟨rho, hrho_inf, ?_, ?_, hrho_ev, hrho_grad,
    hgrad_norm, ?_⟩
  · simpa only [r] using hrho_x
  · simpa only [riemannianEDistOf] using hupper
  · simpa only [r] using hweighted

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem gradientRicciSoliton_exists_weightedLogDistanceUpperSupport
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma) (O : M) :
    ∃ A B : Real, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ x : M, ∃ phi : M → Real,
        isWeightedLaplacianUpperSupportAt (I := I) g f
          (fun y => Real.log
            (1 + (riemannianEDistOf (I := I) g O y).toReal ^ 2))
          x A B phi := by
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
  obtain ⟨C, hfar⟩ :=
    gradientRicciSoliton_exists_weightedDistanceUpperSupport
      (I := I) g f sigma hcomplete hsol O
  obtain ⟨q, G, hq, hG, hRic, hGrad⟩ :=
    exists_local_soliton_control (I := I) g f hcomplete O
  obtain ⟨phiO, hbase⟩ :=
    exists_log_one_add_sq_distance_base_support (I := I) g hcomplete f O
  let d : Real := ((Module.finrank Real E - 1 : Nat) : Real)
  let baseBound : Real :=
    |laplacian (I := I) (LeviCivita (I := I) g) g phiO O -
      g.inner O (gradFun (I := I) g f O)
        (gradientFun (I := I) g phiO O)|
  let radialBound : Real :=
    4 * d + d * q + G + |C| + |sigma| + 2
  let B : Real := radialBound + baseBound
  have hd : 0 ≤ d := by
    dsimp only [d]
    positivity
  have hbaseBound : 0 ≤ baseBound := by
    dsimp only [baseBound]
    positivity
  have hradialBound : 0 ≤ radialBound := by
    dsimp only [radialBound]
    positivity
  have hB : 0 ≤ B := add_nonneg hradialBound hbaseBound
  have hcoef_le_one : ∀ s : Real, 2 * s / (1 + s ^ 2) ≤ 1 := by
    intro s
    apply (div_le_iff₀ (by positivity : (0 : Real) < 1 + s ^ 2)).2
    nlinarith [sq_nonneg (s - 1)]
  have hsecond_le_two : ∀ s : Real,
      2 * (1 - s ^ 2) / (1 + s ^ 2) ^ 2 ≤ 2 := by
    intro s
    apply (div_le_iff₀
      (sq_pos_of_pos (by positivity : (0 : Real) < 1 + s ^ 2))).2
    nlinarith [sq_nonneg (s ^ 2)]
  have hfar_real : ∀ {s D tau : Real}, 0 ≤ s →
      (2 * s / (1 + s ^ 2)) * (D - tau / 2 * s) +
          2 * (1 - s ^ 2) / (1 + s ^ 2) ^ 2 ≤
        |D| + |tau| + 2 := by
    intro s D tau hs
    have hden : 0 < 1 + s ^ 2 := by positivity
    have ha0 : 0 ≤ 2 * s / (1 + s ^ 2) := by positivity
    have ha1 := hcoef_le_one s
    have ht0 : 0 ≤ s ^ 2 / (1 + s ^ 2) := by positivity
    have ht1 : s ^ 2 / (1 + s ^ 2) ≤ 1 := by
      apply (div_le_iff₀ hden).2
      linarith
    have hD : (2 * s / (1 + s ^ 2)) * D ≤ |D| := by
      calc
        (2 * s / (1 + s ^ 2)) * D ≤
            (2 * s / (1 + s ^ 2)) * |D| :=
          mul_le_mul_of_nonneg_left (le_abs_self D) ha0
        _ ≤ 1 * |D| :=
          mul_le_mul_of_nonneg_right ha1 (abs_nonneg D)
        _ = |D| := one_mul _
    have htau : -tau * (s ^ 2 / (1 + s ^ 2)) ≤ |tau| := by
      calc
        -tau * (s ^ 2 / (1 + s ^ 2)) ≤
            |tau| * (s ^ 2 / (1 + s ^ 2)) :=
          mul_le_mul_of_nonneg_right (neg_le_abs tau) ht0
        _ ≤ |tau| * 1 :=
          mul_le_mul_of_nonneg_left ht1 (abs_nonneg tau)
        _ = |tau| := mul_one _
    have hsplit :
        (2 * s / (1 + s ^ 2)) * (D - tau / 2 * s) =
          (2 * s / (1 + s ^ 2)) * D -
            tau * (s ^ 2 / (1 + s ^ 2)) := by
      field_simp [hden.ne']
    rw [hsplit]
    linarith [hsecond_le_two s]
  have hsingular : ∀ {s : Real}, 0 < s →
      (2 * s / (1 + s ^ 2)) * (2 * d / s) ≤ 4 * d := by
    intro s hs
    have hden : 0 < 1 + s ^ 2 := by positivity
    have heq : (2 * s / (1 + s ^ 2)) * (2 * d / s) =
        4 * d / (1 + s ^ 2) := by
      field_simp [hs.ne', hden.ne']
      ring
    rw [heq]
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (by norm_num : (0 : Real) ≤ 4) hd]
  refine ⟨1, B, zero_le_one, hB, ?_⟩
  intro x
  by_cases hOx : x = O
  · subst x
    obtain ⟨hphi_inf, hphi_value, hphi_upper, hphi_eventually,
        hgrad_phi, hgrad_bound, hweighted⟩ := hbase
    refine ⟨phiO, hphi_inf, hphi_value, hphi_upper, hphi_eventually,
      hgrad_phi, hgrad_bound, ?_⟩
    calc
      _ ≤ baseBound := hweighted
      _ ≤ B := by
        dsimp only [B]
        linarith
  · let r : Real := (riemannianEDist I O x).toReal
    have hfin : riemannianEDist I O x ≠ (⊤ : ENNReal) :=
      riemannianEDist_ne_top (I := I) O x
    have hdist_ne : riemannianEDist I O x ≠ 0 := by
      intro hzero
      exact hOx (riemannianEDist_eq_zero_imp_eq (I := I) O x hzero).symm
    have hr : 0 < r :=
      ENNReal.toReal_pos hdist_ne hfin
    have hcoef_nonneg : 0 ≤ 2 * r / (1 + r ^ 2) := by positivity
    have hcoef_bound := hcoef_le_one r
    by_cases hlarge : 3 ≤ r
    · obtain ⟨rho, hrho_inf, hrho_value, hrho_upper, hrho_eventually,
          hgrad_rho, hnorm_rho, hweighted_rho⟩ := hfar x hlarge
      have hdistance_eq :
          (riemannianEDistOf (I := I) g O x).toReal = r := by
        rfl
      rw [hdistance_eq] at hweighted_rho
      obtain ⟨phi, hphi_inf, hphi_value, hphi_upper, hphi_eventually,
          hgrad_phi, hgrad_norm, hweighted_phi⟩ :=
        exists_log_one_add_sq_distance_support_data
          (I := I) g f O x r hr rho hrho_inf hrho_value hrho_upper
            hrho_eventually hgrad_rho hnorm_rho
      refine ⟨phi, hphi_inf, hphi_value, hphi_upper, hphi_eventually,
        hgrad_phi, ?_, ?_⟩
      · rw [hgrad_norm]
        exact hcoef_bound
      · rw [hweighted_phi]
        calc
          (2 * r / (1 + r ^ 2)) *
                (laplacian (I := I) (LeviCivita (I := I) g) g rho x -
                  g.inner x (gradFun (I := I) g f x)
                    (gradientFun (I := I) g rho x)) +
              2 * (1 - r ^ 2) / (1 + r ^ 2) ^ 2 ≤
              (2 * r / (1 + r ^ 2)) * (C - sigma / 2 * r) +
                2 * (1 - r ^ 2) / (1 + r ^ 2) ^ 2 :=
            add_le_add
              (mul_le_mul_of_nonneg_left hweighted_rho hcoef_nonneg) le_rfl
          _ ≤ |C| + |sigma| + 2 := hfar_real hr.le
          _ ≤ B := by
            dsimp only [B, radialBound]
            nlinarith [mul_nonneg hd hq]
    · have hsmall : r < 3 := lt_of_not_ge hlarge
      have hR : (riemannianEDist I O x).toReal < 4 := by
        dsimp only [r] at hsmall
        linarith
      have hRicBall : 0 < Module.finrank Real E - 1 →
          ∀ y ∈ Metric.eball O (ENNReal.ofReal 4),
            ∀ w : TangentSpace I y,
              -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) *
                  g.inner y w w ≤ ricciTensor (I := I) g y w w := by
        intro hdim y hy w
        apply hRic hdim y _ w
        rw [Metric.mem_eball', IsRiemannianManifold.out (I := I) O y] at hy
        simpa only [riemannianEDistOf] using hy.le
      obtain ⟨tail, hreach, hdata⟩ :=
        exists_calabiData_lt (I := I) g hEnorm q hq
          (O := O) (x := x) (R := 4) hRicBall (Ne.symm hOx) hfin hR
      let rho : M → Real := fun y =>
        tail.left + branchRadius (I := I) g tail.branch y
      change ContMDiffAt I (modelWithCornersSelf Real Real) ∞ rho x ∧
          rho x = r ∧
          (∀ᶠ y in nhds x, (riemannianEDist I O y).toReal ≤ rho y) ∧
          (∀ᶠ y in nhds x,
            MDifferentiableAt I (modelWithCornersSelf Real Real) rho y) ∧
          MDifferentiableAt I (I.prod (modelWithCornersSelf Real E))
            (T% fun y : M => gradientFun (I := I) g rho y) x ∧
          g.inner x (gradientFun (I := I) g rho x)
              (gradientFun (I := I) g rho x) = 1 ∧
          laplacian (I := I) (LeviCivita (I := I) g) g rho x ≤
            2 * d / r + d * q at hdata
      obtain ⟨hrho_inf, hrho_value, hrho_upper, hrho_eventually,
        hgrad_rho, hnorm_rho, hlap_rho⟩ := hdata
      have hx4 : riemannianEDistOf (I := I) g O x ≤ ENNReal.ofReal 4 := by
        apply (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mp
        rw [ENNReal.toReal_ofReal (by norm_num : (0 : Real) ≤ 4)]
        dsimp only [r] at hsmall
        linarith
      have hcs := abs_inner_le_sqrt_mul_sqrt (I := I) g x
        (gradFun (I := I) g f x) (gradientFun (I := I) g rho x)
      change |g.inner x (gradFun (I := I) g f x)
          (gradientFun (I := I) g rho x)| ≤
        Real.sqrt (normGradSqFun (I := I) g f x) *
          Real.sqrt (g.inner x (gradientFun (I := I) g rho x)
            (gradientFun (I := I) g rho x)) at hcs
      rw [hnorm_rho, Real.sqrt_one, mul_one] at hcs
      have hinner_rho :
          -g.inner x (gradFun (I := I) g f x)
              (gradientFun (I := I) g rho x) ≤ G :=
        (neg_le_abs _).trans (hcs.trans (hGrad x hx4))
      have hweighted_rho :
          laplacian (I := I) (LeviCivita (I := I) g) g rho x -
              g.inner x (gradFun (I := I) g f x)
                (gradientFun (I := I) g rho x) ≤
            2 * d / r + d * q + G := by
        linarith
      obtain ⟨phi, hphi_inf, hphi_value, hphi_upper, hphi_eventually,
          hgrad_phi, hgrad_norm, hweighted_phi⟩ :=
        exists_log_one_add_sq_distance_support_data
          (I := I) g f O x r hr rho hrho_inf hrho_value hrho_upper
            hrho_eventually hgrad_rho hnorm_rho
      have hrest_nonneg : 0 ≤ d * q + G :=
        add_nonneg (mul_nonneg hd hq) hG
      have hrest :
          (2 * r / (1 + r ^ 2)) * (d * q + G) ≤ d * q + G := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hcoef_bound hrest_nonneg
      refine ⟨phi, hphi_inf, hphi_value, hphi_upper, hphi_eventually,
        hgrad_phi, ?_, ?_⟩
      · rw [hgrad_norm]
        exact hcoef_bound
      · rw [hweighted_phi]
        calc
          (2 * r / (1 + r ^ 2)) *
                (laplacian (I := I) (LeviCivita (I := I) g) g rho x -
                  g.inner x (gradFun (I := I) g f x)
                    (gradientFun (I := I) g rho x)) +
              2 * (1 - r ^ 2) / (1 + r ^ 2) ^ 2 ≤
              (2 * r / (1 + r ^ 2)) * (2 * d / r + d * q + G) +
                2 * (1 - r ^ 2) / (1 + r ^ 2) ^ 2 :=
            add_le_add
              (mul_le_mul_of_nonneg_left hweighted_rho hcoef_nonneg) le_rfl
          _ = (2 * r / (1 + r ^ 2)) * (2 * d / r) +
                (2 * r / (1 + r ^ 2)) * (d * q + G) +
                  2 * (1 - r ^ 2) / (1 + r ^ 2) ^ 2 := by ring
          _ ≤ 4 * d + (d * q + G) + 2 :=
            add_le_add (add_le_add (hsingular hr) hrest) (hsecond_le_two r)
          _ ≤ B := by
            dsimp only [B, radialBound]
            nlinarith [abs_nonneg C, abs_nonneg sigma, hbaseBound]

end DifferentialGeometry.Geometry
