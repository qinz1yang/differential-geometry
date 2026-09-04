import DifferentialGeometry.Analysis.Integration.Measure.Differentiation.Rademacher
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Injectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.LocalExponentialMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.LocalCostBranch

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold NNReal Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

theorem lCost_eq_branch
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (hZ : Z ∈ lInjDomain S T x tau)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    (fun y : M ↦ lCost S T x y tau) =ᶠ[nhds (lExp S T x Z tau)]
      lActBranch S hS T x Z tau hdom hconj := by
  let hloc := lExp_localDiffeo S hS T x Z tau hdom hconj
  let z : M := lExp S T x Z tau
  have hinvZ : hloc.localInverse z = Z :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hsrc : hloc.localInverse.source ∈ nhds z :=
    hloc.localInverse_open_source.mem_nhds hloc.localInverse_mem_source
  have hpre : hloc.localInverse ⁻¹' lInjDomain S T x tau ∈ nhds z := by
    apply hloc.localInverse_contMDiffAt.continuousAt.preimage_mem_nhds
    rw [hinvZ]
    exact (lInj_isOpen S hS T x tau).mem_nhds hZ
  rcases (mem_lExpPosDom S T x Z tau).1 hdom with
    ⟨htau, _hTtau, _hZdom⟩
  filter_upwards [hsrc, hpre] with y hySrc hyInj
  let W : TangentSpace I x := hloc.localInverse y
  obtain ⟨sigma, hsigma, hWmin⟩ := hyInj
  have hWminTau : (W, tau) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x W hWmin htau hsigma.le
  have hright : lExp S T x W tau = y :=
    hloc.localInverse_right_inv hySrc
  have hleft : hloc.localInverse (lExp S T x W tau) = W := by
    apply hloc.localInverse_left_inv
    exact hloc.localInverse.map_source hySrc
  have hlen :
      lLength S T (fun r : Real ↦ lExp S T x W r) 0 tau =
        lRegAction S T (lRegCurve S T x W) 0 (Real.sqrt tau) := by
    change lLength S T (squareRootReparametrization (lRegCurve S T x W)) 0 tau =
      lRegAction S T (lRegCurve S T x W) 0 (Real.sqrt tau)
    exact lLength_squareRootReparametrization_eq_lRegAction (I := I) S T (lRegCurve S T x W) tau htau.le
  change lCost S T x y tau =
    lRegAction S T (lRegCurve S T x (hloc.localInverse y))
      0 (Real.sqrt tau)
  rw [← hright, hleft, ← hlen]
  exact ((mem_lMinDomain S T x W tau).1 hWminTau).2.symm

theorem lCost_smooth
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    ∃ U : Set M, IsOpen U ∧ lExp S T x Z tau ∈ U ∧
      ContMDiffOn I (modelWithCornersSelf Real Real) ∞
        (fun y : M ↦ lCost S T x y tau) U := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hmin htau hsigma.le
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have hconj : ¬ IsLConj S T x Z tau :=
    lMinVec_nconj_lt S hS T x hmin hsigma
  obtain ⟨U, hUopen, hyU, hsmooth⟩ :=
    lActBranch_smooth S hS T x Z tau hdom hconj
  have heq := lCost_eq_branch S hS T x
    (Z := Z) (tau := tau) ⟨sigma, hsigma, hmin⟩ hdom hconj
  obtain ⟨V, hVsub, hVopen, hyV⟩ := mem_nhds_iff.mp heq
  refine ⟨U ∩ V, hUopen.inter hVopen, ⟨hyU, hyV⟩, ?_⟩
  refine (hsmooth.mono Set.inter_subset_left).congr ?_
  intro y hy
  exact hVsub hy.2

theorem lCost_hasMFD
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    HasMFDerivAt I (modelWithCornersSelf Real Real)
      (fun y : M ↦ lCost S T x y tau) (lExp S T x Z tau)
      (LinearMap.toContinuousLinearMap
        (metricFlatMap (I := I) (S.base.metric (T - tau))
          (lExp S T x Z tau)
          (lVelocity (I := I) (lRegCurve S T x Z)
            (Real.sqrt tau)))) := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hmin htau hsigma.le
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have hconj : ¬ IsLConj S T x Z tau :=
    lMinVec_nconj_lt S hS T x hmin hsigma
  exact (lActBranch_hasMFD S hS T x Z tau hdom hconj).congr_of_eventuallyEq
    (lCost_eq_branch S hS T x ⟨sigma, hsigma, hmin⟩ hdom hconj)

theorem lCost_grad
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    gradientFun (I := I) (S.base.metric (T - tau))
        (fun y : M ↦ lCost S T x y tau) (lExp S T x Z tau) =
      lVelocity (I := I) (lRegCurve S T x Z) (Real.sqrt tau) := by
  apply gradientFun_eq_of_flat
  ext V
  have hmfd := lCost_hasMFD S hS T x htau hZ
  have hd := congrArg (fun L : TangentSpace I (lExp S T x Z tau) →L[Real]
    TangentSpace (modelWithCornersSelf Real Real)
      (lCost S T x (lExp S T x Z tau) tau) ↦ L V) hmfd.mfderiv
  change mvfderiv (I := I) (fun y : M ↦ lCost S T x y tau)
    (lExp S T x Z tau) V = _
  rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv]
  have hd' := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real)
      (lCost S T x (lExp S T x Z tau) tau)) hd
  have hcast :
      (LinearMap.toContinuousLinearMap
        (metricFlatMap (I := I) (S.base.metric (T - tau))
          (lExp S T x Z tau)
          (lVelocity (I := I) (lRegCurve S T x Z)
            (Real.sqrt tau)))) V =
        (NormedSpace.fromTangentSpace (𝕜 := Real)
          (lCost S T x (lExp S T x Z tau) tau)).symm
            (metricFlatEquiv (I := I) (S.base.metric (T - tau))
              (lExp S T x Z tau)
              (lVelocity (I := I) (lRegCurve S T x Z)
                (Real.sqrt tau)) V) := by
    rfl
  calc
    _ = (NormedSpace.fromTangentSpace (𝕜 := Real)
        (lCost S T x (lExp S T x Z tau) tau))
          ((LinearMap.toContinuousLinearMap
            (metricFlatMap (I := I) (S.base.metric (T - tau))
              (lExp S T x Z tau)
              (lVelocity (I := I) (lRegCurve S T x Z)
                (Real.sqrt tau)))) V) := hd'
    _ = (NormedSpace.fromTangentSpace (𝕜 := Real)
        (lCost S T x (lExp S T x Z tau) tau))
          ((NormedSpace.fromTangentSpace (𝕜 := Real)
            (lCost S T x (lExp S T x Z tau) tau)).symm
              (metricFlatEquiv (I := I) (S.base.metric (T - tau))
                (lExp S T x Z tau)
                (lVelocity (I := I) (lRegCurve S T x Z)
                  (Real.sqrt tau)) V)) :=
      congrArg (NormedSpace.fromTangentSpace (𝕜 := Real)
        (lCost S T x (lExp S T x Z tau) tau)) hcast
    _ = _ := ContinuousLinearEquiv.apply_symm_apply _ _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lCost_hess_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau)
    (V : TangentSpace I (lExp S T x Z tau))
    (W : ∀ s, TangentSpace I (lRegCurve S T x Z s))
    {Ω : Set Real} (hΩ : IsOpen Ω)
    (hΩseg : Set.Icc (0 : Real) (Real.sqrt tau) ⊆ Ω)
    (hW : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent (8 : Nat)
      (fun s : Real ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (lRegCurve S T x Z s) (W s) : TangentBundle I M)) Ω)
    (hW0 : W 0 = 0) (hWb : W (Real.sqrt tau) = V) :
    hessFun (I := I) (S.base.metric (T - tau))
        (fun y : M ↦ lCost S T x y tau) (lExp S T x Z tau) V V ≤
      2 * lRegIndex S T (lRegCurve S T x Z) W W
        0 (Real.sqrt tau) := by
  rcases hZ with ⟨sigma, hsigma, hmin⟩
  have hZinj : Z ∈ lInjDomain S T x tau := ⟨sigma, hsigma, hmin⟩
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hmin htau hsigma.le
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have hconj : ¬ IsLConj S T x Z tau :=
    lMinVec_nconj_lt S hS T x hmin hsigma
  let b : Real := Real.sqrt tau
  let alpha : Real → M := lRegCurve S T x Z
  let y : M := lExp S T x Z tau
  let g := S.base.metric (T - tau)
  let z : E := Z
  have hb0 : 0 < b := by
    simpa only [b] using Real.sqrt_pos.2 htau
  have hbdom : b ∈ lRegDomain S T x Z := by
    simpa only [b] using
      ((mem_lExpPosDom S T x Z tau).1 hdom).2.2
  let hloc : IsLocalDiffeomorphAt (modelWithCornersSelf Real E) I ∞
      (fun W : E ↦ lExp S T x W tau) z := by
    simpa only [z] using lExp_localDiffeo S hS T x Z tau hdom hconj
  let U : TangentSpace I x :=
    mfderiv I (modelWithCornersSelf Real E) hloc.localInverse y V
  let J : (s : Real) → TangentSpace I (alpha s) :=
    lRegJacobiField S T x Z U
  let Q : (s : Real) → TangentSpace I (alpha s) := fun s ↦ W s - J s
  have hJ0 : J 0 = 0 := by
    simpa only [J, alpha] using lRegJacobi_zero S T x Z U
  have hJb : J b = V := by
    have hright :=
      (hloc.mfderivToContinuousLinearEquiv (by simp)).right_inv V
    change mfderiv (modelWithCornersSelf Real E) I
      (fun W : E ↦ lExp S T x W tau) z
        (mfderiv I (modelWithCornersSelf Real E) hloc.localInverse y V) = V at hright
    change lRegJacobiField S T x Z U (Real.sqrt tau) = V
    have hJac := lExpJacobi_eq (I := I) S T x Z U tau
    change mfderiv (modelWithCornersSelf Real E) I
      (fun W : E ↦ lExp S T x W tau) z U =
        lRegJacobiField S T x Z U (Real.sqrt tau) at hJac
    exact hJac.symm.trans hright
  have hQ0 : Q 0 = 0 := by
    change W 0 - J 0 = 0
    rw [hW0, hJ0, sub_self]
  have hQb : Q b = 0 := by
    change W b - J b = 0
    rw [show W b = V by simpa only [b] using hWb, hJb]
    apply sub_eq_zero.mpr
    rfl
  have hgeoRaw := lRegCurve_isLRegCurveOn (I := I) S hS T x Z hb0 hbdom
  obtain ⟨rho, a, d, ha0, hbd, hrho, hrhoEq, _hrhoDeriv,
      _hrhoRange, hrhoΩ, hJgSmooth, _hpairEq⟩ :=
    exists_lRegJacobiField_smoothGerm_in (I := I) S hS T x Z U hb0 hbdom Ω hΩ
      (by simpa only [b] using hΩseg)
  let gamma : Real → M := fun s ↦ alpha (rho s)
  let Jg : (s : Real) → TangentSpace I (gamma s) := fun s ↦ J (rho s)
  let Wg : (s : Real) → TangentSpace I (gamma s) := fun s ↦ W (rho s)
  let Qg : (s : Real) → TangentSpace I (gamma s) := fun s ↦ Wg s - Jg s
  have hseg : Set.Icc (0 : Real) b ⊆ Set.Ioo a d := by
    intro s hs
    exact ⟨ha0.trans_le hs.1, hs.2.trans_lt hbd⟩
  have hrhoGerm : ∀ s ∈ Set.Icc (0 : Real) b, rho =ᶠ[nhds s] id := by
    intro s hs
    have hsad := hseg hs
    filter_upwards [Ioo_mem_nhds hsad.1 hsad.2] with r hr
    exact hrhoEq ⟨hr.1.le, hr.2.le⟩
  have hgammaGerm : ∀ s ∈ Set.Icc (0 : Real) b,
      gamma =ᶠ[nhds s] alpha := by
    intro s hs
    filter_upwards [hrhoGerm s hs] with r hr
    simp only [gamma, id_eq, hr]
  have hJgGerm : ∀ s ∈ Set.Icc (0 : Real) b,
      ∀ᶠ r in nhds s, (Jg r : E) = (J r : E) := by
    intro s hs
    filter_upwards [hrhoGerm s hs] with r hr
    change (J (rho r) : E) = (J r : E)
    exact congrArg (fun q : Real ↦ (J q : E)) (by
      simpa only [id_eq] using hr)
  have hWgGerm : ∀ s ∈ Set.Icc (0 : Real) b,
      ∀ᶠ r in nhds s, (Wg r : E) = (W r : E) := by
    intro s hs
    filter_upwards [hrhoGerm s hs] with r hr
    change (W (rho r) : E) = (W r : E)
    exact congrArg (fun q : Real ↦ (W q : E))
      (by simpa only [id_eq] using hr)
  have hQgGerm : ∀ s ∈ Set.Icc (0 : Real) b,
      ∀ᶠ r in nhds s, (Qg r : E) = (Q r : E) := by
    intro s hs
    filter_upwards [hWgGerm s hs, hJgGerm s hs] with r hWr hJr
    change Wg r - Jg r = W r - J r
    rw [hWr, hJr]
    rfl
  have hgammaEq : Set.EqOn gamma alpha (Set.Icc (0 : Real) b) := by
    intro s hs
    exact (hgammaGerm s hs).self_of_nhds
  have hJgSmooth' : ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (gamma s) (Jg s) : TangentBundle I M)) := by
    simpa only [gamma, Jg, alpha, J] using hJgSmooth
  have hrhoM : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ rho :=
    contMDiff_iff_contDiff.mpr hrho
  have hWg8 : ContMDiff (modelWithCornersSelf Real Real) I.tangent (8 : Nat)
      (fun s : Real ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (gamma s) (Wg s) : TangentBundle I M)) := by
    rw [← contMDiffOn_univ]
    change ContMDiffOn (modelWithCornersSelf Real Real) I.tangent (8 : Nat)
      ((fun s ↦ TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (lRegCurve S T x Z s) (W s)) ∘ rho) Set.univ
    exact hW.comp
      ((hrhoM.of_le (by decide :
        (8 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffOn)
      (fun s _hs ↦ hrhoΩ s)
  have hJg8 := hJgSmooth'.of_le (by decide :
    (8 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hQg8 : ContMDiff (modelWithCornersSelf Real Real) I.tangent (8 : Nat)
      (fun s : Real ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (gamma s) (Qg s) : TangentBundle I M)) := by
    have hneg :=
      (contMDiff_const (c := (-1 : Real))).smul_bundle hJg8
    simpa only [Qg, Pi.sub_apply, neg_one_smul, sub_eq_add_neg] using
      hWg8.add_bundle hneg
  have hgeo : IsLRegCurveOn S T gamma (Set.uIcc (0 : Real) b) x Z := by
    have h0Icc : (0 : Real) ∈ Set.Icc (0 : Real) b := ⟨le_rfl, hb0.le⟩
    have h0germ := hgammaGerm 0 h0Icc
    refine ⟨?_, ?_, ?_⟩
    · exact (h0germ.self_of_nhds).trans hgeoRaw.1
    · have hvel : lVelocity (I := I) gamma 0 =
          lVelocity (I := I) alpha 0 := by
        unfold lVelocity
        rw [h0germ.mfderiv_eq
          (I := modelWithCornersSelf Real Real) (I' := I)]
        rfl
      exact hvel.trans hgeoRaw.2.1
    · intro s hs
      have hsIcc : s ∈ Set.Icc (0 : Real) b := by
        simpa only [Set.uIcc_of_le hb0.le] using hs
      exact lRegData_congr S T s (hgammaGerm s hsIcc)
        (hgeoRaw.2.2 s hs)
  have hminGamma : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta 0 = gamma 0 → delta b = gamma b →
      lRegAction S T gamma 0 b ≤ lRegAction S T delta 0 b := by
    intro delta hdelta hd0 hdb
    have hEq0 : gamma 0 = alpha 0 :=
      hgammaEq ⟨le_rfl, hb0.le⟩
    have hEqb : gamma b = alpha b :=
      hgammaEq ⟨hb0.le, le_rfl⟩
    have hraw := lMinVec_reg_min (I := I) S hS T x hminTau delta hdelta
      (hd0.trans hEq0) (hdb.trans hEqb)
    have haction : lRegAction S T gamma 0 b =
        lRegAction S T alpha 0 b := by
      apply lRegAction_congr (I := I) S T
      intro s hs
      have hs' : s ∈ Set.Ioo (0 : Real) b := by
        simpa only [Set.uIoo_of_le hb0.le] using hs
      exact hgammaEq ⟨hs'.1.le, hs'.2.le⟩
    rw [haction]
    simpa only [alpha, b] using hraw
  have hminVar : ∀ f : Real → Real → M,
      IsSmoothVariation (I := I) f →
      (∀ s, f 0 s = gamma s) →
      (∀ u, f u 0 = gamma 0) →
      (∀ u, f u b = gamma b) →
      IsLocalMin (fun u ↦ lRegAction S T (f u) 0 b) 0 := by
    intro f hf hf0 hfa hfb
    change ∀ᶠ u in nhds 0,
      lRegAction S T (f 0) 0 b ≤ lRegAction S T (f u) 0 b
    filter_upwards [] with u
    rw [show f 0 = gamma from funext hf0]
    exact hminGamma (f u)
      (((hf : ContMDiff _ _ _ _).comp
        (contMDiff_const.prodMk contMDiff_id)).of_le (by norm_num))
      (hfa u) (hfb u)
  have h0Icc : (0 : Real) ∈ Set.Icc (0 : Real) b := ⟨le_rfl, hb0.le⟩
  have hbIcc : b ∈ Set.Icc (0 : Real) b := ⟨hb0.le, le_rfl⟩
  have hQg0 : Qg 0 = 0 := by
    rw [(hQgGerm 0 h0Icc).self_of_nhds]
    exact hQ0
  have hQgb : Qg b = 0 := by
    rw [(hQgGerm b hbIcc).self_of_nhds]
    exact hQb
  have hQQgNonneg : 0 ≤ lRegIndex S T gamma Qg Qg 0 b :=
    lRegIndex_nonneg (I := I) S hS T gamma 0 b x Z hgeo Qg
      hQg8 hQg0 hQgb hminVar
  have hregG : ∀ s ∈ Set.uIcc (0 : Real) b,
      T - s ^ 2 ∈ D.regular := fun s hs ↦ (hgeo.2.2 s hs).1
  have hJg2 : ContMDiff (modelWithCornersSelf Real Real) I.tangent 2
      (fun s : Real ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (gamma s) (Jg s) : TangentBundle I M)) :=
    hJgSmooth'.of_le (by decide :
      (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hQg2 : ContMDiff (modelWithCornersSelf Real Real) I.tangent 2
      (fun s : Real ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (gamma s) (Qg s) : TangentBundle I M)) :=
    hQg8.of_le (by norm_num)
  have hJJgInt := intervalIntegrable_lRegIndexIntegrand_of_contMDiff (I := I) S hS T 0 b gamma Jg Jg
    hJg2 hJg2 hregG
  have hJQgInt := intervalIntegrable_lRegIndexIntegrand_of_contMDiff (I := I) S hS T 0 b gamma Jg Qg
    hJg2 hQg2 hregG
  have hQQgInt := intervalIntegrable_lRegIndexIntegrand_of_contMDiff (I := I) S hS T 0 b gamma Qg Qg
    hQg2 hQg2 hregG
  have hAlphaGerm : ∀ s ∈ Set.Ioo (0 : Real) b,
      alpha =ᶠ[nhds s] gamma := by
    intro s hs
    exact (hgammaGerm s ⟨hs.1.le, hs.2.le⟩).symm
  have hJGerm : ∀ s ∈ Set.Ioo (0 : Real) b,
      ∀ᶠ r in nhds s, (J r : E) = (Jg r : E) := by
    intro s hs
    exact Filter.EventuallyEq.symm
      (hJgGerm s ⟨hs.1.le, hs.2.le⟩)
  have hQGerm : ∀ s ∈ Set.Ioo (0 : Real) b,
      ∀ᶠ r in nhds s, (Q r : E) = (Qg r : E) := by
    intro s hs
    exact Filter.EventuallyEq.symm
      (hQgGerm s ⟨hs.1.le, hs.2.le⟩)
  have hJJInt : IntervalIntegrable (lRegIndexIntegrand S T alpha J J)
      MeasureTheory.volume 0 b :=
    (intervalIntegrable_lRegIndexIntegrand_congr_of_eventuallyEq (I := I) S T J J Jg Jg 0 b hb0.le
      hAlphaGerm hJGerm hJGerm).2 hJJgInt
  have hJQInt : IntervalIntegrable (lRegIndexIntegrand S T alpha J Q)
      MeasureTheory.volume 0 b :=
    (intervalIntegrable_lRegIndexIntegrand_congr_of_eventuallyEq (I := I) S T J Q Jg Qg 0 b hb0.le
      hAlphaGerm hJGerm hQGerm).2 hJQgInt
  have hQQInt : IntervalIntegrable (lRegIndexIntegrand S T alpha Q Q)
      MeasureTheory.volume 0 b :=
    (intervalIntegrable_lRegIndexIntegrand_congr_of_eventuallyEq (I := I) S T Q Q Qg Qg 0 b hb0.le
      hAlphaGerm hQGerm hQGerm).2 hQQgInt
  have hQQeq : lRegIndex S T alpha Q Q 0 b =
      lRegIndex S T gamma Qg Qg 0 b := by
    apply lRegIndex_congr_of_eventuallyEq (I := I) S T Q Q Qg Qg
    · intro s hs
      have hs' : s ∈ Set.Ioo (0 : Real) b := by
        simpa only [Set.uIoo_of_le hb0.le] using hs
      exact hAlphaGerm s hs'
    · intro s hs
      have hs' : s ∈ Set.Ioo (0 : Real) b := by
        simpa only [Set.uIoo_of_le hb0.le] using hs
      exact hQGerm s hs'
    · intro s hs
      have hs' : s ∈ Set.Ioo (0 : Real) b := by
        simpa only [Set.uIoo_of_le hb0.le] using hs
      exact hQGerm s hs'
  have hQQNonneg : 0 ≤ lRegIndex S T alpha Q Q 0 b := by
    rw [hQQeq]
    exact hQQgNonneg
  have hreg : ∀ s ∈ Set.uIcc (0 : Real) b,
      T - s ^ 2 ∈ D.regular := fun s hs ↦ (hgeoRaw.2.2 s hs).1
  have hAlphaMdiff : ∀ s ∈ Set.uIcc (0 : Real) b,
      ∀ᶠ r in nhds s,
        MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : Real) b := by
      simpa only [Set.uIcc_of_le hb0.le] using hs
    have hsdom : s ∈ lRegDomain S T x Z :=
      lRegDomain_seg S T x Z hbdom hsIcc.1 hsIcc.2
    filter_upwards [(lRegDomain_isOpen S T x Z).mem_nhds hsdom] with r hr
    let z : E := Z
    have hpair : ContMDiffAt (modelWithCornersSelf Real Real)
        ((modelWithCornersSelf Real E).prod
          (modelWithCornersSelf Real Real)) ∞
        (fun q : Real ↦ (z, q)) r :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    have hcurve : ContMDiffAt (modelWithCornersSelf Real Real) I ∞ alpha r := by
      change ContMDiffAt (modelWithCornersSelf Real Real) I ∞
        ((fun p : E × Real ↦ lRegCurve S T x p.1 p.2) ∘
          fun q : Real ↦ (z, q)) r
      exact (lRegCurve_smooth S hS T x hr).comp r hpair
    exact hcurve.mdifferentiableAt (by simp)
  have hA : ∀ s ∈ Set.uIcc (0 : Real) b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s := by
    intro s hs
    simpa only [alpha] using (hgeoRaw.2.2 s hs).2.2.1
  have hJac : IsLRegJacobi S T alpha J (Set.uIcc (0 : Real) b) := by
    simpa only [alpha, J] using lRegCurve_jacobi S hS T x Z U
      (Set.uIcc (0 : Real) b) (fun s hs ↦ by
        have hs' : s ∈ Set.Icc (0 : Real) b := by
          simpa only [Set.uIcc_of_le hb0.le] using hs
        exact lRegDomain_seg S T x Z hbdom hs'.1 hs'.2)
  have hJdiff : ∀ s ∈ Set.uIcc (0 : Real) b,
      DifferentiableAt Real (chartRepAt (I := I) alpha J s) s :=
    fun s hs ↦ (hJac s hs).2.1
  have hWdiff : ∀ s ∈ Set.uIcc (0 : Real) b,
      DifferentiableAt Real (chartRepAt (I := I) alpha W s) s :=
    fun s hs ↦ by
      have hsIcc : s ∈ Set.Icc (0 : Real) b := by
        simpa only [Set.uIcc_of_le hb0.le] using hs
      apply differentiableAt_chartRepAt_of_contMDiffAt_two (I := I)
      simpa only [alpha] using
        (hW.of_le (by norm_num)).contMDiffAt
          (hΩ.mem_nhds (hΩseg (by simpa only [b] using hsIcc)))
  have hQdiff : ∀ s ∈ Set.uIcc (0 : Real) b,
      DifferentiableAt Real (chartRepAt (I := I) alpha Q s) s := by
    intro s hs
    have hrep : chartRepAt (I := I) alpha Q s = fun r ↦
        chartRepAt (I := I) alpha W s r -
          chartRepAt (I := I) alpha J s r := by
      rw [show Q = fun r ↦ W r + (-1 : Real) • J r by
        funext r
        dsimp only [Q]
        module]
      rw [chartRepAt_add, chartRepAt_smul]
      funext r
      module
    rw [hrep]
    exact (hWdiff s hs).sub (hJdiff s hs)
  have hJQzero : lRegIndex S T alpha J Q 0 b = 0 := by
    have hgreen := lRegIndex_eq_half_boundary_of_isLRegJacobi (I := I) S hS T alpha J Q 0 b
      hreg hAlphaMdiff hA hJac hQdiff hJQInt
    rw [hgreen, hQ0, hQb]
    simp
  have hsquare := lRegIndex_add_smul_self (I := I) S T 1 alpha J Q 0 b
    hJdiff hQdiff hJJInt hJQInt hQQInt
  have hfield : (fun s ↦ J s + (1 : Real) • Q s) = W := by
    funext s
    dsimp only [Q]
    module
  rw [hfield] at hsquare
  have hdecomp : lRegIndex S T alpha W W 0 b =
      lRegIndex S T alpha J J 0 b + lRegIndex S T alpha Q Q 0 b := by
    rw [hsquare, hJQzero]
    ring
  have hJleW : lRegIndex S T alpha J J 0 b ≤
      lRegIndex S T alpha W W 0 b := by
    rw [hdecomp]
    linarith
  have hgreenJJ := lRegIndex_eq_half_boundary_of_isLRegJacobi (I := I) S hS T alpha J J 0 b
    hreg hAlphaMdiff hA hJac hJdiff hJJInt
  have hJJend : 2 * lRegIndex S T alpha J J 0 b =
      g.inner y (covDerivAlong (I := I) g alpha J b) V := by
    rw [hgreenJJ, hJ0, hJb]
    simp only [map_zero, sub_zero]
    rw [show T - b ^ 2 = T - tau by
      simp only [b, Real.sq_sqrt htau.le],
      show alpha b = y by rfl]
    ring
  have hcostBranch :
      hessFun (I := I) g (fun q : M ↦ lCost S T x q tau) y V V =
        hessFun (I := I) g
          (lActBranch S hS T x Z tau hdom hconj) y V V := by
    exact congrArg (fun A ↦ A V V)
      (hessFun_congr (I := I) g
        (lCost_eq_branch S hS T x hZinj hdom hconj))
  have hbranch :
      hessFun (I := I) g
          (lActBranch S hS T x Z tau hdom hconj) y V V =
        g.inner y (covDerivAlong (I := I) g alpha J b) V := by
    simpa only [g, y, alpha, J, U, b, hloc] using
      lActBranch_hess S hS T x Z tau hdom hconj V V
  calc
    hessFun (I := I) (S.base.metric (T - tau))
        (fun q : M ↦ lCost S T x q tau) (lExp S T x Z tau) V V =
      hessFun (I := I) g (fun q : M ↦ lCost S T x q tau) y V V := rfl
    _ = hessFun (I := I) g
          (lActBranch S hS T x Z tau hdom hconj) y V V := hcostBranch
    _ = g.inner y (covDerivAlong (I := I) g alpha J b) V := hbranch
    _ = 2 * lRegIndex S T alpha J J 0 b := hJJend.symm
    _ ≤ 2 * lRegIndex S T alpha W W 0 b :=
      mul_le_mul_of_nonneg_left hJleW (by norm_num)
    _ = 2 * lRegIndex S T (lRegCurve S T x Z) W W
        0 (Real.sqrt tau) := rfl

def redLength
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x y : M)
    (tau : Real) : Real :=
  lCost S T x y tau / (2 * Real.sqrt tau)

theorem redLength_smooth
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    ∃ U : Set M, IsOpen U ∧ lExp S T x Z tau ∈ U ∧
      ContMDiffOn I (modelWithCornersSelf Real Real) ∞
        (fun y : M ↦ redLength S T x y tau) U := by
  obtain ⟨U, hUopen, hyU, hsmooth⟩ :=
    lCost_smooth S hS T x htau hZ
  refine ⟨U, hUopen, hyU, ?_⟩
  have hmul := (contMDiffOn_const
    (c := (2 * Real.sqrt tau)⁻¹)).mul hsmooth
  refine hmul.congr ?_
  intro y _hy
  change lCost S T x y tau / (2 * Real.sqrt tau) =
    (2 * Real.sqrt tau)⁻¹ * lCost S T x y tau
  rw [div_eq_mul_inv, mul_comm]

theorem redLength_hess_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau)
    (V : TangentSpace I (lExp S T x Z tau))
    (W : ∀ s, TangentSpace I (lRegCurve S T x Z s))
    {Ω : Set Real} (hΩ : IsOpen Ω)
    (hΩseg : Set.Icc (0 : Real) (Real.sqrt tau) ⊆ Ω)
    (hW : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent (8 : Nat)
      (fun s : Real ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (lRegCurve S T x Z s) (W s) : TangentBundle I M)) Ω)
    (hW0 : W 0 = 0) (hWb : W (Real.sqrt tau) = V) :
    hessFun (I := I) (S.base.metric (T - tau))
        (fun y : M ↦ redLength S T x y tau)
        (lExp S T x Z tau) V V ≤
      lRegIndex S T (lRegCurve S T x Z) W W
        0 (Real.sqrt tau) / Real.sqrt tau := by
  let c : Real := (2 * Real.sqrt tau)⁻¹
  have hb : Real.sqrt tau ≠ 0 := (Real.sqrt_pos.2 htau).ne'
  have hc : 0 ≤ c := (inv_nonneg.mpr (mul_nonneg (by norm_num)
    (Real.sqrt_nonneg tau)))
  have hfun :
      (fun y : M ↦ redLength S T x y tau) =
        c • (fun y : M ↦ lCost S T x y tau) := by
    funext y
    simp only [redLength, c, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hfun, hessFun_smul]
  change c * hessFun (I := I) (S.base.metric (T - tau))
      (fun y : M ↦ lCost S T x y tau) (lExp S T x Z tau) V V ≤ _
  calc
    _ ≤ c * (2 * lRegIndex S T (lRegCurve S T x Z) W W
          0 (Real.sqrt tau)) :=
      mul_le_mul_of_nonneg_left
        (lCost_hess_le S hS T x htau hZ V W hΩ hΩseg hW hW0 hWb) hc
    _ = lRegIndex S T (lRegCurve S T x Z) W W
          0 (Real.sqrt tau) / Real.sqrt tau := by
      dsimp only [c]
      field_simp

theorem redLength_hasMFD
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    HasMFDerivAt I (modelWithCornersSelf Real Real)
      (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau)
      ((2 * Real.sqrt tau)⁻¹ • LinearMap.toContinuousLinearMap
        (metricFlatMap (I := I) (S.base.metric (T - tau))
          (lExp S T x Z tau)
          (lVelocity (I := I) (lRegCurve S T x Z)
            (Real.sqrt tau)))) := by
  have hcost :=
    (lCost_hasMFD S hS T x htau hZ).const_smul
      (2 * Real.sqrt tau)⁻¹
  apply hcost.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y ↦ by
    simp only [Pi.smul_apply, smul_eq_mul, redLength, div_eq_mul_inv]
    exact mul_comm _ _

theorem redLength_grad
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    gradientFun (I := I) (S.base.metric (T - tau))
        (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau) =
      (2 * Real.sqrt tau)⁻¹ •
        lVelocity (I := I) (lRegCurve S T x Z) (Real.sqrt tau) := by
  have hfun :
      (fun y : M ↦ redLength S T x y tau) =
        (2 * Real.sqrt tau)⁻¹ • (fun y : M ↦ lCost S T x y tau) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, redLength, div_eq_mul_inv]
    exact mul_comm _ _
  rw [hfun]
  rw [gradientFun_const_smul (I := I) (S.base.metric (T - tau))
    (2 * Real.sqrt tau)⁻¹
    (lCost_hasMFD S hS T x htau hZ).mdifferentiableAt]
  rw [lCost_grad S hS T x htau hZ]
  rfl

theorem redLength_grad_ray
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    gradientFun (I := I) (S.base.metric (T - tau))
        (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau) =
      lVelocity (I := I) (fun r : Real ↦ lExp S T x Z r) tau := by
  rw [redLength_grad S hS T x htau hZ]
  rw [lExp_vel_sqrt S T x Z htau]
  have hden : 2 * Real.sqrt tau ≠ 0 :=
    mul_ne_zero (by norm_num) (Real.sqrt_pos.2 htau).ne'
  exact inv_smul_smul₀ hden _

theorem lCost_hasDeriv
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    HasDerivAt
      (fun r : Real ↦ lCost S T x (lExp S T x Z tau) r)
      (Real.sqrt tau *
        (S.scalar (T - tau) (lExp S T x Z tau) -
          lSpeedSq S T (fun r : Real ↦ lExp S T x Z r) tau)) tau := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hmin htau hsigma.le
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have hconj : ¬ IsLConj S T x Z tau :=
    lMinVec_nconj_lt S hS T x hmin hsigma
  let J := (modelWithCornersSelf Real E).prod
    (modelWithCornersSelf Real Real)
  let K := I.prod (modelWithCornersSelf Real Real)
  let f : E × Real → M := fun p ↦ lExp S T x p.1 p.2
  let F : E × Real → M × Real := fun p ↦ (f p, p.2)
  let y : M := lExp S T x Z tau
  let q : Real → M × Real := fun r ↦ (y, r)
  let p : Real → E × Real := fun r ↦
    (lExpTime_local S hS T x Z tau hdom hconj).localInverse (q r)
  let A : E × Real → Real := fun z ↦
    lRegAction S T (lRegCurve S T x z.1) 0 (Real.sqrt z.2)
  let hloc : IsLocalDiffeomorphAt J K ∞ F (Z, tau) := by
    simpa only [J, K, F, f] using
      lExpTime_local S hS T x Z tau hdom hconj
  have hp0 : p tau = (Z, tau) := by
    have hp0' :=
      hloc.localInverse_left_inv hloc.localInverse_mem_target
    change hloc.localInverse (F (Z, tau)) = (Z, tau) at hp0'
    change p tau = (Z, tau)
    exact hp0'
  let b : Real := Real.sqrt tau
  let endMap : E → M := fun W ↦ lExp S T x W tau
  let Lz : E →L[Real] Real :=
    ((S.base.metric (T - tau)).inner y
      (lVelocity (I := I) (lRegCurve S T x Z) b)).comp
        (mfderiv (modelWithCornersSelf Real E) I endMap Z)
  let c : Real := lRegLagrangian S T (lRegCurve S T x Z) b / (2 * b)
  let L : E × Real →L[Real] Real :=
    Lz.comp (ContinuousLinearMap.fst Real E Real) +
      c • ContinuousLinearMap.snd Real E Real
  have hJoint : HasFDerivAt A L (Z, tau) := by
    exact hasFDerivAt_lRegAction_lRegCurve_sqrt S hS T x Z hdom
  have hq : HasMFDerivAt (modelWithCornersSelf Real Real) K q tau
      ((0 : TangentSpace (modelWithCornersSelf Real Real) tau →L[Real]
          TangentSpace I y).prod
        (ContinuousLinearMap.id Real
          (TangentSpace (modelWithCornersSelf Real Real) tau))) := by
    change HasMFDerivAt (modelWithCornersSelf Real Real) K
      (fun r ↦ (y, id r)) tau _
    exact (hasMFDerivAt_const (c := y) (x := tau)).prodMk
      (hasMFDerivAt_id tau)
  have hInv : MDifferentiableAt K J hloc.localInverse (q tau) := by
    simpa only [q, y, F, f] using
      hloc.localInverse_mdifferentiableAt (by simp)
  have hpM : HasMFDerivAt (modelWithCornersSelf Real Real) J p tau
      ((mfderiv K J hloc.localInverse (q tau)).comp
        ((0 : TangentSpace (modelWithCornersSelf Real Real) tau →L[Real]
            TangentSpace I y).prod
          (ContinuousLinearMap.id Real
            (TangentSpace (modelWithCornersSelf Real Real) tau)))) := by
    change HasMFDerivAt (modelWithCornersSelf Real Real) J
      (hloc.localInverse ∘ q) tau _
    exact hInv.hasMFDerivAt.comp tau hq
  let eT : E × Real := ((0 : E), (1 : Real))
  let v : E × Real := mfderiv K J hloc.localInverse (q tau) eT
  have hJointP : HasMFDerivAt J (modelWithCornersSelf Real Real)
      A (p tau) L := by
    rw [hp0]
    exact hJoint.hasMFDerivAt
  have hbranch : HasDerivAt (fun r : Real ↦ A (p r)) (L v) tau := by
    have hcomp := hJointP.hasFDerivAt.comp tau hpM.hasFDerivAt
    have hraw := hcomp.hasDerivAt
    change HasDerivAt (A ∘ p) (L v) tau
    exact hraw
  have hright : mfderiv J K F (Z, tau) v = eT := by
    have hright' :=
      (hloc.mfderivToContinuousLinearEquiv (by simp)).right_inv eT
    change mfderiv J K F (Z, tau)
      (mfderiv K J hloc.localInverse (q tau) eT) = eT at hright'
    exact hright'
  have hfdiff : MDifferentiableAt J I f (Z, tau) := by
    have hf := ((lExp_smoothOn S hS T x).contMDiffAt
      ((lExpPosDom_open S hS T x).mem_nhds hdom)).mdifferentiableAt
        (by simp)
    change MDifferentiableAt J I f (Z, tau) at hf
    exact hf
  have hsndDiff : MDifferentiableAt J (modelWithCornersSelf Real Real)
      (@Prod.snd E Real) (Z, tau) := by
    simpa only [J] using
      (mdifferentiableAt_snd : MDifferentiableAt J
        (modelWithCornersSelf Real Real) (@Prod.snd E Real) (Z, tau))
  have hFderiv : mfderiv J K F (Z, tau) =
      (mfderiv J I f (Z, tau)).prod
        (mfderiv J (modelWithCornersSelf Real Real) (@Prod.snd E Real)
          (Z, tau)) := by
    simpa only [F] using mfderiv_prodMk hfdiff hsndDiff
  have hsndDeriv :=
    (mfderiv_snd : mfderiv
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) (@Prod.snd E Real) (Z, tau) =
        ContinuousLinearMap.snd Real
          (TangentSpace (modelWithCornersSelf Real E) (show E from Z))
          (TangentSpace (modelWithCornersSelf Real Real) tau))
  rw [hFderiv, hsndDeriv] at hright
  change (mfderiv J I f (Z, tau) v, v.2) = ((0 : E), (1 : Real)) at hright
  have hExpZero : mfderiv J I f (Z, tau) v = 0 :=
    congrArg Prod.fst hright
  have hv2 : v.2 = 1 := congrArg Prod.snd hright
  have hsplit := mfderiv_prod_eq_add_apply hfdiff (v := v)
  have htimeVel :
      mfderiv (modelWithCornersSelf Real Real) I
          (fun r : Real ↦ f (Z, r)) tau v.2 =
        lVelocity (I := I) (fun r : Real ↦ lExp S T x Z r) tau := by
    rw [hv2]
    rfl
  have hsum :
      mfderiv (modelWithCornersSelf Real E) I
          (fun W : E ↦ f (W, tau)) Z v.1 +
        lVelocity (I := I) (fun r : Real ↦ lExp S T x Z r) tau = 0 := by
    rw [← htimeVel]
    exact hsplit.symm.trans hExpZero
  have hspace :
      mfderiv (modelWithCornersSelf Real E) I endMap Z v.1 =
        -lVelocity (I := I) (fun r : Real ↦ lExp S T x Z r) tau := by
    change mfderiv (modelWithCornersSelf Real E) I
      (fun W : E ↦ f (W, tau)) Z v.1 = _
    exact eq_neg_of_add_eq_zero_left hsum
  have hvel :
      lVelocity (I := I) (lRegCurve S T x Z) b =
        (2 * b) • lVelocity (I := I)
          (fun r : Real ↦ lExp S T x Z r) tau := by
    simpa only [b] using lExp_vel_sqrt S T x Z htau
  have hb0 : b ≠ 0 := (Real.sqrt_pos.2 htau).ne'
  have hbsq : b ^ 2 = tau := by
    simpa only [b] using Real.sq_sqrt htau.le
  have hLv : L v =
      b * (S.scalar (T - tau) y -
        lSpeedSq S T (fun r : Real ↦ lExp S T x Z r) tau) := by
    change ((S.base.metric (T - tau)).inner y
        (lVelocity (I := I) (lRegCurve S T x Z) b))
          (mfderiv (modelWithCornersSelf Real E) I endMap Z v.1) +
        c * v.2 = _
    simp only [c, lRegLagrangian]
    rw [hspace, hv2, hvel]
    have hendb : lRegCurve S T x Z b = y := by
      simp only [b, y, lExp]
    rw [hbsq, hendb]
    simp only [lSpeedSq]
    simp only [((S.base.metric (T - tau)).inner y).map_smul,
      smul_apply]
    simp only [((S.base.metric (T - tau)).inner y
      (lVelocity (I := I) (fun r : Real ↦ lExp S T x Z r) tau)).map_smul,
      ((S.base.metric (T - tau)).inner y
        (lVelocity (I := I) (fun r : Real ↦ lExp S T x Z r) tau)).map_neg,
      smul_eq_mul]
    field_simp [hb0]
    rw [hbsq]
    rw [show lExp S T x Z tau = y by rfl]
    ring
  have hEq : (fun r : Real ↦ A (p r)) =ᶠ[nhds tau]
      fun r : Real ↦ lCost S T x y r := by
    let rho : Real := (tau + sigma) / 2
    have htRho : tau < rho := by
      dsimp only [rho]
      linarith
    have hRhoS : rho < sigma := by
      dsimp only [rho]
      linarith
    have hZrho : Z ∈ lInjDomain S T x rho := ⟨sigma, hRhoS, hmin⟩
    have hsrc : ∀ᶠ r in nhds tau, q r ∈ hloc.localInverse.source := by
      apply hq.continuousAt.eventually
      have hcenter : q tau = F (Z, tau) := by rfl
      rw [hcenter]
      exact hloc.localInverse_open_source.mem_nhds
        hloc.localInverse_mem_source
    have hpos : ∀ᶠ r in nhds tau, 0 < r := eventually_gt_nhds htau
    have hlt : ∀ᶠ r in nhds tau, r < rho := eventually_lt_nhds htRho
    have hinj : ∀ᶠ r in nhds tau,
        (p r).1 ∈ lInjDomain S T x rho := by
      apply hpM.continuousAt.fst.eventually
      change lInjDomain S T x rho ∈ nhds (p tau).1
      rw [hp0]
      exact (lInj_isOpen S hS T x rho).mem_nhds hZrho
    filter_upwards [hsrc, hpos, hlt, hinj] with r hrSrc hrpos hrRho hpr
    have hright' := hloc.localInverse_right_inv hrSrc
    have hp2 : (p r).2 = r := by
      simpa only [F, f, q] using congrArg Prod.snd hright'
    have hend : lExp S T x (p r).1 r = y := by
      have hend' := congrArg Prod.fst hright'
      have hend'' : lExp S T x (p r).1 (p r).2 = y := by
        simpa only [F, f, q, p, hloc] using hend'
      rwa [hp2] at hend''
    obtain ⟨theta, hRhoTheta, hWmin⟩ := hpr
    have hrt : r ≤ theta := (hrRho.trans hRhoTheta).le
    have hWminr : ((p r).1, r) ∈ lMinDomain S T x :=
      lMinDomain_down S hS T x (p r).1 hWmin hrpos hrt
    have hcost := ((mem_lMinDomain S T x (p r).1 r).1 hWminr).2
    change lRegAction S T (lRegCurve S T x (p r).1) 0
        (Real.sqrt (p r).2) = lCost S T x y r
    rw [hp2]
    calc
      lRegAction S T (lRegCurve S T x (p r).1) 0 (Real.sqrt r) =
          lLength S T (fun s : Real ↦ lExp S T x (p r).1 s) 0 r := by
        change lRegAction S T (lRegCurve S T x (p r).1) 0 (Real.sqrt r) =
          lLength S T (squareRootReparametrization (lRegCurve S T x (p r).1)) 0 r
        exact (lLength_squareRootReparametrization_eq_lRegAction (I := I) S T (lRegCurve S T x (p r).1)
          r hrpos.le).symm
      _ = lCost S T x (lExp S T x (p r).1 r) r := hcost
      _ = lCost S T x y r := by rw [hend]
  have hcost := hbranch.congr_of_eventuallyEq hEq.symm
  rw [hLv] at hcost
  simpa only [A, p, y, b] using hcost

theorem redLength_hasDeriv
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    HasDerivAt
      (fun r : Real ↦ redLength S T x (lExp S T x Z tau) r)
      ((S.scalar (T - tau) (lExp S T x Z tau) -
          lSpeedSq S T (fun r : Real ↦ lExp S T x Z r) tau) / 2 -
        redLength S T x (lExp S T x Z tau) tau / (2 * tau)) tau := by
  let y : M := lExp S T x Z tau
  let gamma : Real → M := fun r ↦ lExp S T x Z r
  let b : Real := Real.sqrt tau
  have hcost : HasDerivAt (fun r : Real ↦ lCost S T x y r)
      (b * (S.scalar (T - tau) y - lSpeedSq S T gamma tau)) tau := by
    simpa only [y, gamma, b] using lCost_hasDeriv S hS T x htau hZ
  have hb0 : b ≠ 0 := (Real.sqrt_pos.2 htau).ne'
  have hden0 : 2 * b ≠ 0 := mul_ne_zero (by norm_num) hb0
  have hquot := hcost.div
    ((Real.hasDerivAt_sqrt htau.ne').const_mul 2) hden0
  have hbsq : b ^ 2 = tau := by
    simpa only [b] using Real.sq_sqrt htau.le
  have hderiv :
      (b * (S.scalar (T - tau) y - lSpeedSq S T gamma tau) *
          (2 * b) - lCost S T x y tau * (2 * (1 / (2 * b)))) /
          (2 * b) ^ 2 =
        (S.scalar (T - tau) y - lSpeedSq S T gamma tau) / 2 -
          redLength S T x y tau / (2 * tau) := by
    simp only [redLength]
    change _ =
      (S.scalar (T - tau) y - lSpeedSq S T gamma tau) / 2 -
        (lCost S T x y tau / (2 * b)) / (2 * tau)
    rw [← hbsq]
    field_simp [hb0]
  have hquot' : HasDerivAt
      ((fun r : Real ↦ lCost S T x y r) /
        fun r : Real ↦ 2 * Real.sqrt r)
      ((S.scalar (T - tau) y - lSpeedSq S T gamma tau) / 2 -
        redLength S T x y tau / (2 * tau)) tau := by
    apply hquot.congr_deriv
    simpa only [b] using hderiv
  have hred := hquot'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r ↦ by
      change redLength S T x y r = lCost S T x y r / (2 * Real.sqrt r)
      rfl)
  simpa only [y, gamma] using hred

theorem redLength_HJ
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    deriv (fun r : Real ↦ redLength S T x (lExp S T x Z tau) r) tau +
        (1 / 2 : Real) *
          (S.base.metric (T - tau)).inner (lExp S T x Z tau)
            (gradientFun (I := I) (S.base.metric (T - tau))
              (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau))
            (gradientFun (I := I) (S.base.metric (T - tau))
              (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau)) -
        (1 / 2 : Real) * S.scalar (T - tau) (lExp S T x Z tau) +
        redLength S T x (lExp S T x Z tau) tau / (2 * tau) = 0 := by
  rw [(redLength_hasDeriv S hS T x htau hZ).deriv]
  rw [redLength_grad_ray S hS T x htau hZ]
  simp only [lSpeedSq]
  ring

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
theorem redLength_mul
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x y : M)
    {tau : Real} (htau : 0 < tau) :
    (2 * Real.sqrt tau) * redLength S T x y tau = lCost S T x y tau := by
  have hden : 2 * Real.sqrt tau ≠ 0 :=
    mul_ne_zero (by norm_num) (Real.sqrt_pos.2 htau).ne'
  exact mul_div_cancel₀ _ hden

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
theorem redLength_eq_zero
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x y : M)
    {tau : Real} (htau : 0 < tau) :
    redLength S T x y tau = 0 ↔ lCost S T x y tau = 0 := by
  have hden : 2 * Real.sqrt tau ≠ 0 :=
    mul_ne_zero (by norm_num) (Real.sqrt_pos.2 htau).ne'
  simp only [redLength, div_eq_zero_iff, hden, or_false]

theorem redLength_diff_ae
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      {y : M | ¬ MDifferentiableAt I (modelWithCornersSelf Real Real)
        (fun z : M ↦ redLength S T x z tau) y} = 0 := by
  apply nondiff_null (I := I) (M := M) g
    (fun z : M ↦ redLength S T x z tau)
  intro p
  have hcost := lCost_chart_lip (I := I) S hS T x tau htau hslab p
  let c : Real := (2 * Real.sqrt tau)⁻¹
  intro z hz
  obtain ⟨K, U, hU, hLip⟩ := hcost hz
  refine ⟨‖c‖₊ * K, U, hU, ?_⟩
  have hcomp : LipschitzOnWith (‖c‖₊ * K)
      (fun q : E ↦ c • (((fun y : M ↦ lCost S T x y tau) ∘
        (extChartAt I p).symm) q)) U := by
    change LipschitzOnWith (‖c‖₊ * K)
      ((fun x : Real ↦ c • x) ∘
        (fun y : M ↦ lCost S T x y tau) ∘ (extChartAt I p).symm) U
    exact (lipschitzWith_smul c).lipschitzOnWith.comp hLip (mapsTo_univ _ _)
  have hfun :
      (fun q : E ↦ c • (((fun y : M ↦ lCost S T x y tau) ∘
          (extChartAt I p).symm) q)) =
        ((fun y : M ↦ redLength S T x y tau) ∘
          (extChartAt I p).symm) := by
    funext q
    simp only [redLength, Function.comp_apply, c, smul_eq_mul,
      div_eq_mul_inv, mul_comm]
  rwa [← hfun]

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
