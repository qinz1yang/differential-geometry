import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import DifferentialGeometry.Analysis.ODE.Gronwall.Integral
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Analysis.ODE

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional Real E] [T2Space M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem riemannianEDist_le_intervalIntegral_speed
    (g : SmoothRiemannianMetric I M)
    {gamma : Real → M} {a b : Real} (hab : a ≤ b)
    (hgamma : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma (Icc a b))
    {speed : Real → Real} (hspeed : ContinuousOn speed (Icc a b))
    (hspeed_nonneg : ∀ t ∈ Icc a b, 0 ≤ speed t)
    (hvel : ∀ t ∈ Icc a b,
      Real.sqrt (g.inner (gamma t)
        (mfderiv (modelWithCornersSelf Real Real) I gamma t 1)
        (mfderiv (modelWithCornersSelf Real Real) I gamma t 1)) ≤ speed t) :
    riemannianEDistOf (I := I) g (gamma a) (gamma b) ≤
      ENNReal.ofReal (∫ t in a..b, speed t) := by
  let cg : ContinuousRiemannianMetric E (fun x : M => TangentSpace I x) :=
    g.toContinuousRiemannianMetric
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨cg.toRiemannianMetric⟩
  have hpath : riemannianEDist I (gamma a) (gamma b) ≤
      pathELength I gamma a b :=
    riemannianEDist_le_pathELength hgamma rfl rfl hab
  change riemannianEDist I (gamma a) (gamma b) ≤ _
  refine hpath.trans ?_
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  have hpoint : ∀ t ∈ Icc a b,
      ‖mfderiv (modelWithCornersSelf Real Real) I gamma t 1‖ₑ ≤
        ENNReal.ofReal (speed t) := by
    intro t ht
    rw [tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g]
    exact ENNReal.ofReal_le_ofReal (hvel t ht)
  refine (setLIntegral_mono' measurableSet_Icc hpoint).trans_eq ?_
  have hint : IntegrableOn speed (Icc a b) := hspeed.integrableOn_Icc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc a b)] speed :=
    ae_restrict_of_forall_mem measurableSet_Icc hspeed_nonneg
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem integralCurve_linearGrowth_distance_le
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (p : M) {A T : Real} (hA : 0 ≤ A) (hT : 0 ≤ T)
    {v : (x : M) → TangentSpace I x} {gamma : Real → M}
    (hgamma : IsMIntegralCurve gamma v)
    (hgamma_smooth : ContMDiff (modelWithCornersSelf Real Real) I 1 gamma)
    (hgrowth : ∀ x : M,
      Real.sqrt (g.inner x (v x) (v x)) ≤
        A * (1 + (riemannianEDistOf (I := I) g p x).toReal)) :
    ∀ t ∈ Icc (0 : Real) T,
      1 + (riemannianEDistOf (I := I) g p (gamma t)).toReal ≤
        (1 + (riemannianEDistOf (I := I) g p (gamma 0)).toReal) *
          Real.exp (A * t) := by
  let rb : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let hcb : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let _ := rb
  let _ := hcb
  let r : Real → Real := fun t =>
    1 + (riemannianEDist I p (gamma t)).toReal
  have hfinite : ∀ x : M, riemannianEDist I p x ≠ (∞ : ENNReal) :=
    fun x => riemannianEDist_ne_top (I := I) p x
  have hdist_cont : Continuous
      (fun x : M => (riemannianEDist I p x).toReal) := by
    have h := continuousOn_riemannianEDist_toReal_on_finite (I := I) g p
    apply continuousOn_univ.mp
    simpa only [riemannianEDistOf] using h.mono (fun x _ => hfinite x)
  have hr_cont : Continuous r := by
    exact continuous_const.add (hdist_cont.comp hgamma.continuous)
  have hr_nonneg : ∀ t : Real, 0 ≤ r t := by
    intro t
    exact add_nonneg zero_le_one ENNReal.toReal_nonneg
  have hineq : ∀ t ∈ Icc (0 : Real) T,
      r t ≤ r 0 + A * ∫ s in (0 : Real)..t, r s := by
    intro t ht
    let speed : Real → Real := fun s => A * r s
    have hspeed_cont : ContinuousOn speed (Icc (0 : Real) t) :=
      (continuous_const.mul hr_cont).continuousOn
    have hspeed_nonneg : ∀ s ∈ Icc (0 : Real) t, 0 ≤ speed s := by
      intro s _
      exact mul_nonneg hA (hr_nonneg s)
    have hvel : ∀ s ∈ Icc (0 : Real) t,
        Real.sqrt (g.inner (gamma s)
          (mfderiv (modelWithCornersSelf Real Real) I gamma s 1)
          (mfderiv (modelWithCornersSelf Real Real) I gamma s 1)) ≤ speed s := by
      intro s _
      have hderiv :
          mfderiv (modelWithCornersSelf Real Real) I gamma s
              (1 : TangentSpace (modelWithCornersSelf Real Real) s) =
            v (gamma s) := by
        rw [(hgamma s).mfderiv]
        change (1 : Real) • v (gamma s) = v (gamma s)
        rw [one_smul]
      rw [hderiv]
      simpa only [riemannianEDistOf] using hgrowth (gamma s)
    have hcurve := riemannianEDist_le_intervalIntegral_speed
      (I := I) g ht.1 hgamma_smooth.contMDiffOn
      hspeed_cont hspeed_nonneg hvel
    have hcurve' : riemannianEDist I (gamma 0) (gamma t) ≤
        ENNReal.ofReal (∫ s in (0 : Real)..t, speed s) := by
      exact hcurve
    have htri : riemannianEDist I p (gamma t) ≤
        riemannianEDist I p (gamma 0) +
          ENNReal.ofReal (∫ s in (0 : Real)..t, speed s) :=
      (riemannianEDist_triangle (I := I) (x := p) (y := gamma 0)
        (z := gamma t)).trans (add_le_add le_rfl hcurve')
    have hspeed_int_nonneg : 0 ≤ ∫ s in (0 : Real)..t, speed s := by
      exact intervalIntegral.integral_nonneg ht.1 fun s hs =>
        hspeed_nonneg s hs
    have hreal := (ENNReal.toReal_le_toReal
      (hfinite (gamma t))
      ((ENNReal.add_ne_top).2 ⟨hfinite (gamma 0), ENNReal.ofReal_ne_top⟩)).mpr htri
    rw [ENNReal.toReal_add (hfinite (gamma 0)) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hspeed_int_nonneg] at hreal
    have hspeed_int : ∫ s in (0 : Real)..t, speed s =
        A * ∫ s in (0 : Real)..t, r s := by
      rw [intervalIntegral.integral_const_mul]
    rw [hspeed_int] at hreal
    simpa only [r, add_assoc, add_comm, add_left_comm] using
      add_le_add_left hreal 1
  have hgronwall := gronwall_integral_le hT hA hr_cont.continuousOn hineq
  intro t ht
  simpa only [r, riemannianEDistOf] using hgronwall t ht

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_globalIntegralCurve_of_linearGrowth
    [I.Boundaryless] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(Real, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (p : M) {A : Real} (hA : 0 ≤ A)
    (hgrowth : ∀ x : M,
      Real.sqrt (g.inner x (v x) (v x)) ≤
        A * (1 + (riemannianEDistOf (I := I) g p x).toReal)) :
    ∀ x : M, ∃ gamma : Real → M,
      gamma 0 = x ∧ IsMIntegralCurve gamma v := by
  classical
  by_cases hdim : Module.finrank Real E = 0
  · have hE : Subsingleton E :=
      (Module.finrank_zero_iff (R := Real) (M := E)).mp hdim
    intro x
    have hvx : v x = 0 := by
      apply (tangentSpaceModelContinuousLinearEquiv (I := I) x).injective
      exact hE.elim _ _
    exact ⟨fun _ : Real => x, rfl, isMIntegralCurve_const hvx⟩
  · let _ : NeZero (Module.finrank Real E) := ⟨hdim⟩
    let _ : CompleteSpace E := FiniteDimensional.complete Real E
    intro x
    have hv1 : CMDiff 1
        (fun y : M => (⟨y, v y⟩ : TangentBundle I M)) :=
      hv.of_le (by norm_num)
    apply (exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hv1 x).2
    intro a
    let T : Real := |a|
    let d0 : Real := (riemannianEDistOf (I := I) g p x).toReal
    let R : Real := (1 + d0) * Real.exp (A * T)
    let K : Set M :=
      {y | riemannianEDistOf (I := I) g p y ≤ ENNReal.ofReal R}
    have hK : IsCompact K := by
      exact RiemannianMetricComplete.closedEBall_isCompact
        (I := I) hg p R
    obtain ⟨chi, hchi, hchic, hchione, -, hchirange⟩ :=
      DifferentialGeometry.Analysis.exists_mfd_bump
        (I := I) (M := M) hK isOpen_univ (subset_univ K)
    let w : (y : M) → TangentSpace I y := fun y => chi y • v y
    have hw : ContMDiff I (I.prod 𝓘(Real, E)) ∞
        (fun y : M => (⟨y, w y⟩ : TangentBundle I M)) := by
      change ContMDiff I (I.prod 𝓘(Real, E)) ∞
        (fun y : M => (⟨y, (chi • v) y⟩ : TangentBundle I M))
      exact hchi.smul_section hv
    have hwc : IsCompact (tsupport w) := by
      change HasCompactSupport (fun y : M => chi y • v y)
      exact hchic.smul_right
    have hwgrowth : ∀ y : M,
        Real.sqrt (g.inner y (w y) (w y)) ≤
          A * (1 + (riemannianEDistOf (I := I) g p y).toReal) := by
      intro y
      have hchiy : chi y ∈ Icc (0 : Real) 1 :=
        hchirange ⟨y, rfl⟩
      calc
        Real.sqrt (g.inner y (w y) (w y)) =
            |chi y| * Real.sqrt (g.inner y (v y) (v y)) := by
          exact sqrt_inner_smul (I := I) g y (chi y) (v y)
        _ ≤ 1 * Real.sqrt (g.inner y (v y) (v y)) := by
          exact mul_le_mul_of_nonneg_right
            (abs_le.mpr ⟨by linarith [hchiy.1], hchiy.2⟩)
            (Real.sqrt_nonneg _)
        _ ≤ A * (1 + (riemannianEDistOf (I := I) g p y).toReal) := by
          simpa only [one_mul] using hgrowth y
    let hcompleteW :=
      exists_globalIntegralCurve_of_compactSupport w hw hwc
    let gamma : Real → M := curveAt w hcompleteW x
    have hgamma0 : gamma 0 = x := by
      exact curveAt_zero w hcompleteW x
    have hgammaW : IsMIntegralCurve gamma w :=
      curveAt_integralCurve w hcompleteW x
    have hgammaSmoothInf : ContMDiff 𝓘(Real, Real) I ∞ gamma := by
      have hflow :=
        contMDiff_globalFlow_joint_of_compactSupport w hw hwc
      have hpair : ContMDiff 𝓘(Real, Real) (𝓘(Real, Real).prod I) ∞
          (fun t : Real => (t, x)) :=
        contMDiff_id.prodMk (contMDiff_const (c := x))
      have hcomp := hflow.comp hpair
      change ContMDiff 𝓘(Real, Real) I ∞
        (curveAt w (exists_globalIntegralCurve_of_compactSupport w hw hwc) x)
      simpa only [Function.comp_def] using hcomp
    have hgammaSmooth : ContMDiff 𝓘(Real, Real) I 1 gamma :=
      hgammaSmoothInf.of_le (by norm_num)
    have hT : 0 ≤ T := abs_nonneg a
    have hforward := integralCurve_linearGrowth_distance_le
      (I := I) g p hA hT hgammaW hgammaSmooth hwgrowth
    let delta : Real → M := gamma ∘ fun s => -s
    let wneg : (y : M) → TangentSpace I y := (-1 : Real) • w
    have hdelta : IsMIntegralCurve delta wneg := by
      have hc := IsMIntegralCurve.comp_mul hgammaW (-1)
      have hcurve :
          (gamma ∘ fun s : Real => s * (-1)) = delta := by
        simp only [delta, mul_neg, mul_one]
      have hfield : (-1 : Real) • w = wneg := rfl
      rw [hcurve, hfield] at hc
      exact hc
    have hdeltaSmooth : ContMDiff 𝓘(Real, Real) I 1 delta := by
      have hneg : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞
          (fun s : Real => -s) :=
        ContMDiff.neg contMDiff_id
      have hcomp := hgammaSmoothInf.comp hneg
      simpa only [delta] using hcomp.of_le (by norm_num)
    have hwnegGrowth : ∀ y : M,
        Real.sqrt (g.inner y (wneg y) (wneg y)) ≤
          A * (1 + (riemannianEDistOf (I := I) g p y).toReal) := by
      intro y
      change Real.sqrt
        (g.inner y ((-1 : Real) • w y) ((-1 : Real) • w y)) ≤ _
      calc
        Real.sqrt (g.inner y ((-1 : Real) • w y) ((-1 : Real) • w y)) =
            |(-1 : Real)| * Real.sqrt (g.inner y (w y) (w y)) := by
          exact sqrt_inner_smul (I := I) g y (-1) (w y)
        _ = Real.sqrt (g.inner y (w y) (w y)) := by norm_num
        _ ≤ A * (1 + (riemannianEDistOf (I := I) g p y).toReal) :=
          hwgrowth y
    have hbackward := integralCurve_linearGrowth_distance_le
      (I := I) g p hA hT hdelta hdeltaSmooth hwnegGrowth
    refine ⟨gamma, hgamma0, ?_⟩
    intro t ht
    have htT : |t| ≤ T := by
      dsimp only [T]
      exact ((abs_lt.mpr ht).le.trans (le_abs_self a))
    have hdistR :
        1 + (riemannianEDistOf (I := I) g p (gamma t)).toReal ≤ R := by
      by_cases ht0 : 0 ≤ t
      · have htmem : t ∈ Icc (0 : Real) T :=
          ⟨ht0, (le_abs_self t).trans htT⟩
        have hbase :
            1 + (riemannianEDistOf (I := I) g p (gamma t)).toReal ≤
              (1 + d0) * Real.exp (A * t) := by
          simpa only [hgamma0, d0] using hforward t htmem
        have hexp : Real.exp (A * t) ≤ Real.exp (A * T) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htmem.2 hA)
        exact hbase.trans (by
          simpa only [R] using mul_le_mul_of_nonneg_left hexp
            (add_nonneg zero_le_one ENNReal.toReal_nonneg))
      · let s : Real := -t
        have hs0 : 0 ≤ s := by
          dsimp only [s]
          linarith
        have hsT : s ≤ T := by
          dsimp only [s]
          rw [← abs_of_nonpos (le_of_not_ge ht0)]
          exact htT
        have hbase :
            1 + (riemannianEDistOf (I := I) g p (gamma t)).toReal ≤
              (1 + d0) * Real.exp (A * s) := by
          simpa only [delta, Function.comp_apply, s, neg_neg, neg_zero, hgamma0, d0] using
            hbackward s ⟨hs0, hsT⟩
        have hexp : Real.exp (A * s) ≤ Real.exp (A * T) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT hA)
        exact hbase.trans (by
          simpa only [R] using mul_le_mul_of_nonneg_left hexp
            (add_nonneg zero_le_one ENNReal.toReal_nonneg))
    have hgammaK : gamma t ∈ K := by
      change riemannianEDistOf (I := I) g p (gamma t) ≤ ENNReal.ofReal R
      have hfinite :
          riemannianEDistOf (I := I) g p (gamma t) ≠ (∞ : ENNReal) := by
        let : RiemannianBundle (fun y : M => TangentSpace I y) :=
          ⟨g.toRiemannianMetric⟩
        let : IsContinuousRiemannianBundle E
            (fun y : M => TangentSpace I y) :=
          ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
        change riemannianEDist I p (gamma t) ≠ (∞ : ENNReal)
        exact riemannianEDist_ne_top (I := I) p (gamma t)
      rw [← ENNReal.ofReal_toReal hfinite]
      exact ENNReal.ofReal_le_ofReal (by linarith [hdistR])
    have hchiAt : chi (gamma t) = 1 :=
      ((eventually_nhdsSet_iff_forall.mp hchione) (gamma t) hgammaK).self_of_nhds
    have hwAt : w (gamma t) = v (gamma t) := by
      simp only [w, hchiAt, one_smul]
    have hderiv := hgammaW t
    rw [hwAt] at hderiv
    exact hderiv.hasMFDerivWithinAt

end DifferentialGeometry.Analysis.ODE
