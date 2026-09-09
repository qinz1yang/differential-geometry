import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarGradient
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Cutoff.Curvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Cutoff.FlowBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Scale.Transfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.DerivativeNorm

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator (gradientFun)
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff ENNReal Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private def shiUnitError (d : Nat) (T : Real) : Real :=
  let dR : Real := d
  let Lambda : Real := dR ^ 2
  let a : Real := 4
  let U : Real := Real.exp (Lambda * T)
  let Csq := Classical.choose
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_sq
  let Ceta := Classical.choose
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_bounds
  Csq * a ^ 2 * U ^ 2 +
    Ceta * (2 * (dR - 1) * a ^ 2 * U ^ 2 +
      a * U * Real.sqrt ((dR - 1) * Lambda) + a ^ 2 * U ^ 2)

private theorem shiUnitError_cont (d : Nat) :
    Continuous (shiUnitError d) := by
  unfold shiUnitError
  fun_prop

private def shiCost (d : Nat) : Real :=
  max (rmTowerCost d 0) (rmTowerCost d 1)

private theorem shiCost_nonneg (d : Nat) : 0 ≤ shiCost d :=
  (rmTowerCost_nonneg d 0).trans (le_max_left _ _)

private def shiUnitBound (d : ℕ) (T : ℝ) : ℝ :=
  let c := shiCost d
  2 * ((1 + 2 * c * T) * (1 + c * T) +
    9 * shiUnitError d T * (1 + 2 * c * T) * T) / T

private theorem exists_shi_time (d : ℕ) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ Real.exp (2 * (d : ℝ) ^ 2 * θ) < 2 ∧
      34 * shiUnitError d θ * θ ≤ 1 / 2 := by
  have hs : ContinuousAt (fun T : ℝ => Real.exp (2 * (d : ℝ) ^ 2 * T)) 0 := by fun_prop
  have he : ContinuousAt (fun T : ℝ => 34 * shiUnitError d T * T) 0 := by
    exact (continuousAt_const.mul (shiUnitError_cont d).continuousAt).mul continuousAt_id
  have hg := (hs.eventually_lt_const (show Real.exp (2 * (d : ℝ) ^ 2 * 0) < 2 by norm_num)).and
    (he.eventually_lt_const (show 34 * shiUnitError d 0 * 0 < (1 / 2 : ℝ) by norm_num))
  have hne := (hg.filter_mono nhdsWithin_le_nhds).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨θ, ⟨hshort, hsmall⟩, hθ⟩ := hne.exists
  exact ⟨θ, hθ.1, hθ.2, hshort, hsmall.le⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem shiError_eq_unit
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time)
    (hradius : B.radius = 1) (T : ℝ) :
    shiCutoffError B T = shiUnitError (Module.finrank ℝ E) T := by
  simp [FlowMetricBall.shiCutoffError, shiUnitError, hradius]

private theorem shiRm1_unit
    [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {T : Real} (hT : 0 < T) (hTone : T ≤ 1)
    (htime : (time : Real) = T) (hradius : B.radius = 1)
    (hreg : Set.Icc 0 T ⊆ D.regular)
    (hcomplete : ∀ s ∈ Set.Icc 0 T,
      RiemannianMetricComplete (I := I) (S.base.metric s))
    (hshort : Real.exp
      (2 * (Module.finrank Real E : Real) ^ 2 * T) < 2)
    (hsmall : 34 * shiUnitError (Module.finrank Real E) T * T ≤ 1 / 2)
    {t : Real} (ht : t ∈ Set.Icc (T / 2) T) {x : M}
    (hx : riemannianEDistOf (I := I) (S.base.metric t) B.center x <
      ENNReal.ofReal (1 / 8 : Real)) :
    nablaKRm04NormSqIntrinsic (I := I) S 1 t x ≤
      shiUnitBound (Module.finrank Real E) T := by
  let d := Module.finrank ℝ E
  let c := shiCost d
  have hc : 0 ≤ c := shiCost_nonneg d
  have hTB : Icc 0 T ⊆ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) := by
    intro s hs
    rw [htime, hradius]
    norm_num
    constructor <;> linarith [hs.1, hs.2, hTone]
  have hshortCut : Real.exp (2 * ((Module.finrank ℝ E : ℝ) ^ 2 / B.radius ^ 2) * T) < 2 := by
    simpa only [hradius, one_pow, div_one, mul_assoc] using hshort
  let cut := FlowMetricBall.shiParabolicCutoff hS B hB hT.le
    (fun s hs => hreg ⟨hs.1.le, hs.2⟩) hTB hcomplete hshortCut
  have hsmallCut : 34 * shiCutoffError B T * T ≤ 1 / 2 := by
    rw [shiError_eq_unit B hradius T]
    exact hsmall
  have hRm : ∀ s ∈ Icc 0 T, ∀ y, 0 < cut.chi s y →
      nablaKRm04NormSqIntrinsic S 0 s y ≤ (1 : ℝ) ^ 2 := by
    intro s hs y hy
    have hdist := DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.riemannianEDistOf_lt_of_shiCutoff_pos B hs.1 hy
    have hyset : y ∈ B.setAt s :=
      hdist.trans ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 (by linarith [B.radius_pos]))
    have hraw := hB.2 s (hTB hs) y hyset
    simpa only [hradius, one_pow, one_mul, FlowMetricBall.rmNormSq,
      nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hraw
  have hEstimate := nablaRm_normSq_cutoff_le hS cut hreg
    (show (0 : ℝ) ≤ 1 by norm_num) hT.le (by norm_num) hsmallCut hRm
  have hexp : Real.exp ((d : ℝ) ^ 2 * t) < 2 := by
    have harg : (d : ℝ) ^ 2 * t ≤ 2 * (d : ℝ) ^ 2 * T := by
      nlinarith [sq_nonneg (d : ℝ), ht.2, hT]
    exact (Real.exp_le_exp.mpr harg).trans_lt hshort
  have hplate : (1 / 8 : ℝ) ≤ 1 / (4 * Real.exp ((d : ℝ) ^ 2 * t)) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
      (mul_pos (by norm_num) (Real.exp_pos _))]
    nlinarith [hexp]
  have hchi : cut.chi t x = 1 := by
    apply FlowMetricBall.shiCutoff_eq_one_of_riemannianEDistOf_le
    apply hx.le.trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [hradius, one_pow, div_one, d] using hplate
  have ht0 : 0 ≤ t := by linarith [hT, ht.1]
  have hp := hEstimate t ⟨ht0, ht.2⟩ x
  rw [hchi, shiError_eq_unit B hradius T] at hp
  norm_num only [one_pow, mul_one] at hp
  have heps : 0 ≤ shiUnitError d T := by
    rw [← shiError_eq_unit B hradius T]
    exact FlowMetricBall.shiCutoffError_nonneg B T
  have hcT : 0 ≤ 1 + 2 * c * T := by positivity
  have htimeTerm := mul_le_mul_of_nonneg_left ht.2
    (mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 9 by norm_num) heps) hcT)
  have hleft := mul_le_mul_of_nonneg_right ht.1
    (nablaKRm04NormSqIntrinsic_nonneg S 1 t x)
  apply (le_div_iff₀ hT).2
  dsimp only [shiUnitBound, d, c, shiCost] at *
  nlinarith

private theorem shiRm1_scaled
    [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {theta : Real} (htheta : 0 < theta) (htheta_one : theta < 1)
    (hshort : Real.exp
      (2 * (Module.finrank Real E : Real) ^ 2 * theta) < 2)
    (hsmall : 34 * shiUnitError (Module.finrank Real E) theta * theta ≤ 1 / 2)
    (hreg : Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆
      D.regular)
    (hcomplete : ∀ q ∈ Set.Icc
      ((time : Real) - theta * B.radius ^ 2) (time : Real),
        RiemannianMetricComplete (I := I) (S.base.metric q))
    {t : Real}
    (ht : t ∈ Set.Icc
      ((time : Real) - theta * B.radius ^ 2 / 2) (time : Real))
    {x : M}
    (hx : riemannianEDistOf (I := I) (S.base.metric t) B.center x <
      ENNReal.ofReal (B.radius / 8)) :
    B.radius ^ 6 *
        nablaKRm04NormSqIntrinsic (I := I) S 1 t x ≤
      shiUnitBound (Module.finrank Real E) theta := by
  classical
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let : IsManifold I 2 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let R : Real := B.radius⁻¹ ^ 2
  let tau : Real := (time : Real) - theta * B.radius ^ 2
  have hR : 0 < R := by
    exact pow_pos (inv_pos.mpr B.radius_pos) 2
  have htau_window : tau ∈
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real) := by
    dsimp only [tau]
    constructor
    · nlinarith [sq_pos_of_pos B.radius_pos]
    · nlinarith [mul_nonneg htheta.le (sq_nonneg B.radius)]
  have htau : tau ∈ D.carrier := hB.1 htau_window
  have hpara (q : Real) :
      parabolicTime tau R q =
        (time : Real) - theta * B.radius ^ 2 + q * B.radius ^ 2 := by
    unfold parabolicTime
    dsimp only [tau, R]
    field_simp [ne_of_gt B.radius_pos]
  have hpara_end : parabolicTime tau R theta = (time : Real) := by
    rw [hpara]
    ring
  have htheta_carrier : theta ∈ (parabolicInterval D tau R htau).carrier := by
    change parabolicTime tau R theta ∈ D.carrier
    rw [hpara_end]
    exact time.2
  let st : (parabolicInterval D tau R htau).FlowTime :=
    ⟨theta, htheta_carrier⟩
  let B0 : FlowMetricBall S (parabolicFlowTime tau R htau st) :=
    { center := B.center
      radius := B.radius
      radius_pos := B.radius_pos }
  have htime0 :
      (parabolicFlowTime tau R htau st : Real) = (time : Real) := by
    simpa only [parabolicFlowTime_coe, st] using hpara_end
  have hB0 : B0.IsRmControlled := by
    constructor
    · intro s hs
      apply hB.1
      simpa only [B0, htime0] using hs
    · intro s hs y hy
      have hs' : s ∈ Set.Icc
          ((time : Real) - B.radius ^ 2) (time : Real) := by
        simpa only [B0, htime0] using hs
      have hy' : y ∈ B.setAt s := by
        simpa only [B0, FlowMetricBall.setAt] using hy
      simpa only [B0] using hB.2 s hs' y hy'
  let Sn : SolutionOn (I := I) (M := M) (parabolicInterval D tau R htau) :=
    parabolicSolution (I := I) S tau R hR htau
  let Bn : FlowMetricBall Sn st :=
    parabolicBall S tau R hR htau st B0
  have hSn : IsSolutionOn (I := I) Sn := by
    exact parabolicSolution_isSolutionOn (I := I) S hS tau R hR htau
  have hBn : Bn.IsRmControlled := by
    exact parabolicBall_rm (I := I) S tau R hR htau st B0 hB0
  have hsqrtR : Real.sqrt R = B.radius⁻¹ := by
    dsimp only [R]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr B.radius_pos)]
  have hBn_radius : Bn.radius = 1 := by
    dsimp only [Bn, parabolicBall, B0]
    rw [hsqrtR]
    exact inv_mul_cancel₀ (ne_of_gt B.radius_pos)
  have hregn : Set.Icc 0 theta ⊆
      (parabolicInterval D tau R htau).regular := by
    intro q hq
    change parabolicTime tau R q ∈ D.regular
    apply hreg
    rw [hpara]
    constructor
    · have hcoef : 0 < 1 - theta + q := by linarith [hq.1]
      have hprod : 0 < (1 - theta + q) * B.radius ^ 2 :=
        mul_pos hcoef (sq_pos_of_pos B.radius_pos)
      nlinarith
    · have hmul :=
        mul_le_mul_of_nonneg_right hq.2 (sq_nonneg B.radius)
      nlinarith
  have hcompleten : ∀ q ∈ Set.Icc 0 theta,
      RiemannianMetricComplete (I := I) (Sn.base.metric q) := by
    intro q hq
    have hq_old : parabolicTime tau R q ∈ Set.Icc
        ((time : Real) - theta * B.radius ^ 2) (time : Real) := by
      rw [hpara]
      have hlow := mul_nonneg hq.1 (sq_nonneg B.radius)
      have hupp :=
        mul_le_mul_of_nonneg_right hq.2 (sq_nonneg B.radius)
      constructor <;> nlinarith
    change RiemannianMetricComplete (I := I)
      (scaleMetric (I := I) R hR (S.base.metric (parabolicTime tau R q)))
    apply RiemannianMetricComplete.of_lower (hcomplete _ hq_old) hR
    intro y v
    rw [scaleMetric_inner]
  let q : Real := parabolicBackward tau R t
  have hq_time : parabolicTime tau R q = t := by
    exact parabolicTime_back (ne_of_gt hR)
  have hq_eq :
      (time : Real) - theta * B.radius ^ 2 + q * B.radius ^ 2 = t := by
    rw [← hpara q, hq_time]
  have hq : q ∈ Set.Icc (theta / 2) theta := by
    constructor
    · by_contra hnot
      have hlt : q < theta / 2 := lt_of_not_ge hnot
      have hmul :=
        mul_lt_mul_of_pos_right hlt (sq_pos_of_pos B.radius_pos)
      nlinarith [ht.1]
    · by_contra hnot
      have hlt : theta < q := lt_of_not_ge hnot
      have hmul :=
        mul_lt_mul_of_pos_right hlt (sq_pos_of_pos B.radius_pos)
      nlinarith [ht.2]
  have hx_scaled :
      riemannianEDistOf (I := I) (Sn.base.metric q) Bn.center x <
        ENNReal.ofReal (1 / 8 : Real) := by
    have hx' :
        riemannianEDistOf (I := I)
            (scaleMetric (I := I) R hR (S.base.metric t)) B.center x <
          ENNReal.ofReal (Real.sqrt R * (B.radius / 8)) := by
      change x ∈ {y : M | riemannianEDistOf (I := I)
        (scaleMetric (I := I) R hR (S.base.metric t)) B.center y <
          ENNReal.ofReal (Real.sqrt R * (B.radius / 8))}
      rw [edistBall_scale (I := I)]
      exact hx
    have hscale_radius : Real.sqrt R * (B.radius / 8) = 1 / 8 := by
      rw [hsqrtR]
      field_simp [ne_of_gt B.radius_pos]
    change riemannianEDistOf (I := I)
        (scaleMetric (I := I) R hR (S.base.metric (parabolicTime tau R q)))
          B.center x < ENNReal.ofReal (1 / 8 : Real)
    rw [hq_time, ← hscale_radius]
    exact hx'
  have hunit := shiRm1_unit (I := I) hSn Bn hBn htheta
    htheta_one.le rfl hBn_radius hregn hcompleten hshort hsmall hq hx_scaled
  have hscale := parabolicNablaRmNormSq (I := I) S tau R hR htau q x
  rw [hq_time] at hscale
  have hR_inv : R⁻¹ = B.radius ^ 2 := by
    dsimp only [R]
    field_simp [ne_of_gt B.radius_pos]
  calc
    B.radius ^ 6 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x =
        (R⁻¹) ^ 3 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x := by
          rw [hR_inv]
          ring
    _ = nablaKRm04NormSqIntrinsic (I := I) Sn 1 q x := hscale.symm
    _ ≤ shiUnitBound (Module.finrank Real E) theta := hunit

theorem shi_first_derivative_estimate :
    ∃ theta C : Real, 0 < theta ∧ theta < 1 ∧ 0 < C ∧
      ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
        IsSolutionOn (I := I) S →
        ∀ {time : RealTimeInterval.FlowTime D}
          (B : FlowMetricBall S time), B.IsRmControlled →
          Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
          (∀ q ∈ Set.Icc
            ((time : Real) - theta * B.radius ^ 2) (time : Real),
              RiemannianMetricComplete (I := I) (S.base.metric q)) →
          ∀ q ∈ Set.Icc
            ((time : Real) - theta * B.radius ^ 2 / 2) (time : Real),
            ∀ x : M,
              riemannianEDistOf (I := I) (S.base.metric q) B.center x <
                ENNReal.ofReal (B.radius / 8) →
              Real.sqrt
                  (nablaKRm04NormSqIntrinsic (I := I) S 1 q x) ≤
                C / B.radius ^ 3 := by
  by_cases hdim : Module.finrank ℝ E = 0
  · refine ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num, ?_⟩
    intro D S hS time B hB hreg hcomplete q hq x hx
    let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    have hv (v : TangentSpace I x) : v = 0 := by
      apply (tangentSpaceModelContinuousLinearEquiv (I := I) x).injective
      exact Subsingleton.elim _ _
    have hfield : nablaKRm04Field S q 1 x = 0 := by
      apply ContinuousMultilinearMap.ext
      intro v
      change (nablaKRm04Field S q 1 x) v = 0
      exact ContinuousMultilinearMap.map_coord_zero _ (0 : Fin (4 + 1)) (hv _)
    have hzero : nablaKRm04NormSqIntrinsic S 1 q x = 0 := by
      unfold nablaKRm04NormSqIntrinsic
      rw [hfield]
      exact ((Tensor0SBundle.tensor0SMetricData (S.base.metric q) x (4 + 1)).inner_self_eq_zero_iff 0).2 rfl
    rw [hzero, Real.sqrt_zero]
    exact div_nonneg zero_le_one (pow_nonneg B.radius_pos.le 3)
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let d : Nat := Module.finrank Real E
  obtain ⟨theta, htheta, htheta_one, hshort, hsmall⟩ := exists_shi_time d
  let A : Real := shiUnitBound d theta
  let C : Real := Real.sqrt A + 1
  have hC : 0 < C := by
    dsimp only [C]
    nlinarith [Real.sqrt_nonneg A]
  refine ⟨theta, C, htheta, htheta_one, hC, ?_⟩
  intro D S hS time B hB hreg hcomplete q hq x hx
  have hscaled := shiRm1_scaled (I := I) hS B hB htheta htheta_one
    (by simpa only [d] using hshort) (by simpa only [d] using hsmall)
    hreg hcomplete hq hx
  let W : Real := nablaKRm04NormSqIntrinsic (I := I) S 1 q x
  change B.radius ^ 6 * W ≤ A at hscaled
  have hW : 0 ≤ W := by
    exact nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 q x
  have hA : 0 ≤ A := by
    exact (mul_nonneg (pow_nonneg B.radius_pos.le 6) hW).trans hscaled
  have hsqrtW : (Real.sqrt W) ^ 2 = W := Real.sq_sqrt hW
  have hsqrtA : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
  have hroot : B.radius ^ 3 * Real.sqrt W ≤ Real.sqrt A := by
    apply (sq_le_sq₀
      (mul_nonneg (pow_nonneg B.radius_pos.le 3) (Real.sqrt_nonneg W))
      (Real.sqrt_nonneg A)).mp
    calc
      (B.radius ^ 3 * Real.sqrt W) ^ 2 = B.radius ^ 6 * W := by
        rw [mul_pow, hsqrtW]
        ring
      _ ≤ A := hscaled
      _ = (Real.sqrt A) ^ 2 := hsqrtA.symm
  apply (le_div_iff₀ (pow_pos B.radius_pos 3)).2
  dsimp only [C, W]
  nlinarith

theorem scalar_gradient_estimate :
    ∃ theta C : ℝ, 0 < theta ∧ theta < 1 ∧ 0 < C ∧
      ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
        IsSolutionOn S →
        ∀ {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time),
          B.IsRmControlled →
          Ioc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.regular →
          (∀ q ∈ Icc ((time : ℝ) - theta * B.radius ^ 2) (time : ℝ),
            RiemannianMetricComplete (S.base.metric q)) →
          ∀ q ∈ Icc ((time : ℝ) - theta * B.radius ^ 2 / 2) (time : ℝ),
            ∀ x (v : TangentSpace I x),
              riemannianEDistOf (S.base.metric q) B.center x <
                ENNReal.ofReal (B.radius / 8) →
              |(S.base.metric q).inner x
                (gradientFun (S.base.metric q) (S.scalar q) x) v| ≤
                  (C / B.radius ^ 3) * Real.sqrt ((S.base.metric q).inner x v v) := by
  obtain ⟨theta, K, htheta, hthetaOne, hK, hShi⟩ :=
    FlowMetricBall.shi_first_derivative_estimate (E := E) (I := I) (M := M)
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 < n ^ 2 + 1 := by positivity
  refine ⟨theta, (n ^ 2 + 1) * K, htheta, hthetaOne, mul_pos hn hK, ?_⟩
  intro D S hS time B hB hreg hcomplete q hq x v hx
  have hbound := hShi hS B hB hreg hcomplete q hq x hx
  calc
    |(S.base.metric q).inner x (gradientFun (S.base.metric q) (S.scalar q) x) v| ≤
        n ^ 2 * Real.sqrt (nablaKRm04NormSqIntrinsic S 1 q x) *
          Real.sqrt ((S.base.metric q).inner x v v) := by
      exact scalar_gradient_abs_le_nabla_rm (S.base.metric q) x v
    _ ≤ n ^ 2 * (K / B.radius ^ 3) *
        Real.sqrt ((S.base.metric q).inner x v v) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (sq_nonneg n))
        (Real.sqrt_nonneg _)
    _ = (n ^ 2 * K / B.radius ^ 3) *
        Real.sqrt ((S.base.metric q).inner x v v) := by ring
    _ ≤ ((n ^ 2 + 1) * K / B.radius ^ 3) *
        Real.sqrt ((S.base.metric q).inner x v v) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply div_le_div_of_nonneg_right _ (pow_nonneg B.radius_pos.le 3)
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hK.le

end DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall
