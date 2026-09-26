import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformKappaCanonicalThreshold
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedArmCylinderLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNeckLimit

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private theorem hornCurvatureOperatorLowerBoundAt_mono {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I3) (M := M) x) {K K' : ℝ}
    (h : curvatureOperatorLowerBoundAt (I := I3) g x A K) (hK : K ≤ K') :
    curvatureOperatorLowerBoundAt (I := I3) g x A K' := by
  intro n c v w
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I3) g x hdim
  have h1 := h n c v w
  have h2 := DimensionThree.algebraicCurvatureIdentityQuadraticEval_nonneg (I := I3) g x c v w
    basis horth
  have h3 := mul_le_mul_of_nonneg_right hK h2
  linarith

private theorem hornRescalePinchingFunction_antitone {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi) {A₀ A : ℝ} (hA₀ : 0 < A₀)
    (hA : A₀ ≤ A) (v : ℝ) :
    Perelman.rescalePinchingFunction A Phi v ≤ Perelman.rescalePinchingFunction A₀ Phi v := by
  have hApos : 0 < A := hA₀.trans_le hA
  unfold Perelman.rescalePinchingFunction
  rcases le_or_gt v 0 with hv | hv
  · have h1 : Phi (A * v) ≤ Phi (A₀ * v) := hPhi.mono (by nlinarith)
    have h2 : A⁻¹ ≤ A₀⁻¹ := inv_anti₀ hA₀ hA
    have h3 := hPhi.pos (A * v)
    calc A⁻¹ * Phi (A * v) ≤ A₀⁻¹ * Phi (A * v) := mul_le_mul_of_nonneg_right h2 h3.le
      _ ≤ A₀⁻¹ * Phi (A₀ * v) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hA₀.le)
  · have hq := hPhi.quotientAntitoneOn (show A₀ * v ∈ Ioi 0 from mul_pos hA₀ hv)
      (show A * v ∈ Ioi 0 from mul_pos hApos hv) (mul_le_mul_of_nonneg_right hA hv.le)
    have e1 : A⁻¹ * Phi (A * v) = v * (Phi (A * v) / (A * v)) := by
      field_simp
    have e2 : A₀⁻¹ * Phi (A₀ * v) = v * (Phi (A₀ * v) / (A₀ * v)) := by
      field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hq hv.le

theorem exists_uniform_orientedWitness_of_parabolically_noncollapsed
    {delta : ℝ} (hd : 0 < delta) (hd1 : delta < 1) {kappa : ℝ} (hkappa : 0 < kappa)
    {rho : ℝ} (hrho : 0 < rho) {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi) :
    ∃ Q₀ theta : ℝ, 0 < Q₀ ∧ 0 < theta ∧
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
        (x : P.Carrier) (t : ℝ), t < s → Q₀ ≤ G.flow.scalar t x →
        a ≤ t - theta / G.flow.scalar t x →
        Perelman.PhiAlmostNonnegative G.flow (Icc (t - theta / G.flow.scalar t x) t) Phi →
        (∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
          (B : Perelman.FlowMetricBall G.flow τ),
          t - theta / G.flow.scalar t x ≤ τ → (τ : ℝ) ≤ t → B.radius ≤ rho →
            B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed kappa) →
        OrientedWitness G.flow P.orientation delta (kappa / modelNoncollapseFactor) x t := by
  have hA₀ : 0 < (rho ^ 2)⁻¹ := by positivity
  set kappa' := kappa / modelNoncollapseFactor
  have hkappa' : 0 < kappa' := div_pos hkappa modelNoncollapseFactor_pos
  have hkeq : modelNoncollapseFactor * kappa' = kappa :=
    mul_div_cancel₀ _ modelNoncollapseFactor_pos.ne'
  obtain ⟨r, hr, -, hmodel⟩ := abstract_model_theorem.{u} (eps := delta) (kappa := kappa')
    (sigma := 1) (Phi := Perelman.rescalePinchingFunction (rho ^ 2)⁻¹ Phi) hd hd1 hkappa'
    one_pos (hPhi.rescale hA₀)
  refine ⟨(rho ^ 2)⁻¹ * (r ^ 2)⁻¹, (r ^ 2)⁻¹, by positivity, by positivity, ?_⟩
  intro P a s G x t hts hQ hwin hpinch hnc
  have hR : 0 < G.flow.scalar t x := lt_of_lt_of_le (by positivity) hQ
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = r ^ 2 * G.flow.scalar t x := ⟨_, rfl⟩
  have hA : 0 < A := by rw [hAdef]; positivity
  have hAinv : A⁻¹ = (r ^ 2)⁻¹ / G.flow.scalar t x := by
    rw [hAdef, mul_inv, div_eq_mul_inv]
  have hA0A : (rho ^ 2)⁻¹ ≤ A := by
    have h1 := mul_le_mul_of_nonneg_left hQ (sq_nonneg r)
    have e : r ^ 2 * ((rho ^ 2)⁻¹ * (r ^ 2)⁻¹) = (rho ^ 2)⁻¹ := by
      field_simp
    rw [hAdef]
    linarith
  have hAi : 0 < A⁻¹ := inv_pos.mpr hA
  have hwin' : a ≤ t - A⁻¹ := by rw [hAinv]; exact hwin
  have htime : parabolicTime (t - a - A⁻¹) A 1 + a = t := by
    simp only [parabolicTime, one_div]
    ring
  let c := ConnectedComponents.mk x
  let U := P.componentOpen c
  let _ : CompactSpace U := P.component_compact c
  let _ : ConnectedSpace U := P.component_connected c
  let xU : U := ⟨x, rfl⟩
  have hτ0 : 0 ≤ t - a - A⁻¹ := by linarith
  have hτle : t - a - A⁻¹ ≤ t - a := by linarith
  let W : RealTimeInterval := RealTimeInterval.closed (t - a - A⁻¹) (t - a) hτle
  have hWcar : W.carrier ⊆
      (RealTimeInterval.closedOpen 0 (s - a) (sub_pos.mpr G.lt)).carrier := by
    intro v hv
    change v ∈ Icc (t - a - A⁻¹) (t - a) at hv
    change v ∈ Ico 0 (s - a)
    exact ⟨hτ0.trans hv.1, by linarith [hv.2]⟩
  have hWreg : W.regular ⊆
      (RealTimeInterval.closedOpen 0 (s - a) (sub_pos.mpr G.lt)).regular := by
    intro v hv
    change v ∈ Ioo (t - a - A⁻¹) (t - a) at hv
    change v ∈ Ioo 0 (s - a)
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  let S1 := G.componentTimeShift c
  have hS1 : IsSolutionOn S1 := G.isSolutionOn_componentTimeShift c
  let Sw := S1.timeRestrict W
  have hSw : IsSolutionOn Sw := isSolutionOn_timeRestrict hS1 hWcar hWreg
  have hτW : t - a - A⁻¹ ∈ W.carrier := ⟨le_rfl, hτle⟩
  let S2 := parabolicSolution Sw (t - a - A⁻¹) A hA hτW
  have hS2 : IsSolutionOn S2 := parabolicSolution_isSolutionOn Sw hSw _ A hA hτW
  let D3 : RealTimeInterval := RealTimeInterval.closed 0 1 zero_le_one
  have h3car : D3.carrier ⊆ (parabolicInterval W (t - a - A⁻¹) A hτW).carrier := by
    intro v hv
    change v ∈ Icc 0 1 at hv
    change t - a - A⁻¹ + v / A ∈ Icc (t - a - A⁻¹) (t - a)
    have h1 : 0 ≤ v / A := div_nonneg hv.1 hA.le
    have h2 : v / A ≤ A⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left hAi.le hv.2
    constructor <;> linarith
  have h3reg : D3.regular ⊆ (parabolicInterval W (t - a - A⁻¹) A hτW).regular := by
    intro v hv
    change v ∈ Ioo 0 1 at hv
    change t - a - A⁻¹ + v / A ∈ Ioo (t - a - A⁻¹) (t - a)
    have h1 : 0 < v / A := div_pos hv.1 hA
    have h2 : v / A < A⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_lt_of_lt_one_left hAi hv.2
    constructor <;> linarith
  let S3 := S2.timeRestrict D3
  have hS3 : IsSolutionOn S3 := isSolutionOn_timeRestrict hS2 h3car h3reg
  have hpinW : Perelman.PhiAlmostNonnegative Sw W.carrier Phi := by
    intro v hv y
    change v ∈ Icc (t - a - A⁻¹) (t - a) at hv
    have hv' : v + a ∈ Icc (t - (r ^ 2)⁻¹ / G.flow.scalar t x) t := by
      rw [← hAinv]
      exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hG := hpinch (v + a) hv' y.val
    change curvatureOperatorLowerBoundAt ((G.flow.base.metric (v + a)).restrictOpen U) y
      (metricAlgebraicCurvatureTensorAt ((G.flow.base.metric (v + a)).restrictOpen U) y)
      (Phi (metricScalarAt ((G.flow.base.metric (v + a)).restrictOpen U) y))
    rw [← DifferentialGeometry.localPullMetric_subtype_val, metricScalarAt_localPull,
      curvatureOperatorLowerBoundAt_localPullMetric_iff]
    exact hG
  have hpin2 := Perelman.phiAlmostNonnegative_paraSolution Sw hA hτW hpinW
  have hpin3 : Perelman.PhiAlmostNonnegative S3 D3.carrier
      (Perelman.rescalePinchingFunction (rho ^ 2)⁻¹ Phi) := by
    intro v hv y
    exact hornCurvatureOperatorLowerBoundAt_mono _ _ _ (hpin2 v (h3car hv) y)
      (hornRescalePinchingFunction_antitone hPhi hA₀ hA0A _)
  have hncAux : Perelman.ParabolicallyKappaNoncollapsedBelowScale
      ((G.flow.timeShift a).timeRestrict W) kappa rho := by
    refine ⟨hrho, ?_⟩
    intro v B hB hctrl
    have hv : (v : ℝ) ∈ Icc (t - a - A⁻¹) (t - a) := v.2
    have hva : (v : ℝ) + a ∈ (RealTimeInterval.closedOpen a s G.lt).carrier := by
      change (v : ℝ) + a ∈ Ico a s
      exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hlo : t - (r ^ 2)⁻¹ / G.flow.scalar t x ≤ (v : ℝ) + a := by
      rw [← hAinv]
      linarith [hv.1]
    let B' : Perelman.FlowMetricBall G.flow ⟨(v : ℝ) + a, hva⟩ :=
      ⟨B.center, B.radius, B.radius_pos⟩
    have hctrl' : B'.IsParabolicallyRmControlled := by
      refine ⟨fun q hq => ?_, fun q hq y hy => ?_⟩
      · have hq' : q - a ∈ W.carrier :=
          hctrl.1 ⟨by linarith [hq.1], by linarith [hq.2]⟩
        change q - a ∈ Icc (t - a - A⁻¹) (t - a) at hq'
        change q ∈ Ico a s
        exact ⟨by linarith [hq'.1], by linarith [hq'.2]⟩
      · have h := hctrl.2 (q - a) ⟨by linarith [hq.1], by linarith [hq.2]⟩ y hy
        change B.radius ^ 4 * Perelman.FlowMetricBall.rmNormSq G.flow (q - a + a) y ≤ 1 at h
        rwa [sub_add_cancel] at h
    exact hnc ⟨(v : ℝ) + a, hva⟩ B' hlo (by linarith [hv.2]) hB hctrl'
  have hncW : Perelman.ParabolicallyKappaNoncollapsedBelowScale Sw kappa rho :=
    parabolicallyKappaNoncollapsedBelowScale_restrictOpen_of_isClosed hncAux U
      (P.componentOpen_isClosed c)
  have hnc2 := Perelman.parabolicallyKappaNoncollapsedBelowScale_parabolicSolution Sw
    (t - a - A⁻¹) A hA hτW kappa rho hncW
  have hle : 1 ≤ Real.sqrt A * rho := by
    have h1 : Real.sqrt ((rho ^ 2)⁻¹) = rho⁻¹ := by
      rw [Real.sqrt_inv, Real.sqrt_sq hrho.le]
    have h2 : rho⁻¹ ≤ Real.sqrt A := h1 ▸ Real.sqrt_le_sqrt hA0A
    calc (1 : ℝ) = rho⁻¹ * rho := (inv_mul_cancel₀ hrho.ne').symm
      _ ≤ Real.sqrt A * rho := mul_le_mul_of_nonneg_right h2 hrho.le
  have hnc3 : Perelman.ParabolicallyKappaNoncollapsedBelowScale S3
      (modelNoncollapseFactor * kappa') 1 := by
    have hres := parabolicallyKappaNoncollapsedBelowScale_timeRestrict (S := S2) (D' := D3) h3car
      hnc2
    rw [hkeq]
    exact ⟨one_pos, fun v B hB => hres.2 v B (le_trans hB hle)⟩
  have hcurv : ∀ a' b' : ℝ, a' ≤ b' → Icc a' b' ⊆ D3.carrier → ∃ K : ℝ,
      ∀ v ∈ Icc a' b', ∀ y, Perelman.FlowMetricBall.rmNormSq S3 v y ≤ K := by
    intro a' b' _ hsub
    obtain ⟨K, _, hK⟩ := exists_curvature_bound_on_carrier_interval_of_isSolutionOn
      (I := I3) (M := U) S3 hS3 hsub
    refine ⟨K, fun v hv y => ?_⟩
    have h := hK v hv y
    simpa only [Perelman.FlowMetricBall.rmNormSq, SolutionFamily.rm04, metricRm04_apply,
      SolutionOn.family_metric] using h
  have hhyp : ClosedModelHypotheses S3 kappa' 1
      (Perelman.rescalePinchingFunction (rho ^ 2)⁻¹ Phi) :=
    { isSolution := hS3
      complete := fun v _ => RiemannianMetricComplete.of_compact (I := I3) (M := U)
        (S3.base.metric v)
      curvature := hcurv
      pinching := hpin3
      noncollapse := hnc3 }
  have hthr : r⁻¹ ^ 2 ≤ S3.scalar 1 xU := by
    have h1 : S3.scalar 1 xU =
        A⁻¹ * S1.scalar (parabolicTime (t - a - A⁻¹) A 1) xU := by
      rw [show S3.scalar = S2.scalar from rfl, parabolicSolution_scalar]
      rfl
    have h2 : A⁻¹ * G.flow.scalar t x = r⁻¹ ^ 2 := by
      rw [hAdef]
      field_simp
    rw [h1, G.componentTimeShift_scalar c, htime]
    exact h2.ge
  have hw3 : OrientedWitness S3 (P.componentOrientation c) delta kappa' xU 1 :=
    hmodel U (P.componentOrientation c) 1 le_rfl S3 hhyp xU 1 ⟨le_rfl, le_rfl⟩ hthr
  have hw2 : OrientedWitness S2 (P.componentOrientation c) delta kappa' xU 1 :=
    orientedWitness_of_timeRestrict h3car hw3
  have hwW : OrientedWitness Sw (P.componentOrientation c) delta kappa' xU
      (parabolicTime (t - a - A⁻¹) A 1) :=
    (orientedWitness_paraSolution_iff Sw (P.componentOrientation c) hA hτW 1 xU
      delta kappa').mp hw2
  have hw1 : OrientedWitness S1 (P.componentOrientation c) delta kappa' xU
      (parabolicTime (t - a - A⁻¹) A 1) :=
    orientedWitness_of_timeRestrict hWcar hwW
  have hwG : OrientedWitness G.flow P.orientation delta kappa' x
      (parabolicTime (t - a - A⁻¹) A 1 + a) :=
    hw1.ofComponentTimeShift
  rw [htime] at hwG
  exact hwG

theorem exists_strongNeck_threshold_of_minimizing_arms
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1 / 11) {angle : ℝ} (hangle : 0 < angle)
    {kappa : ℝ} (hkappa : 0 < kappa) {rho : ℝ} (hrho : 0 < rho) {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi) :
    ∃ D Q₀ theta : ℝ, 0 < D ∧ 0 < Q₀ ∧ 0 < theta ∧
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
        (x : P.Carrier) (t : ℝ), t < s → Q₀ ≤ G.flow.scalar t x →
        a ≤ t - theta / G.flow.scalar t x →
        Perelman.PhiAlmostNonnegative G.flow (Icc (t - theta / G.flow.scalar t x) t) Phi →
        (∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
          (B : Perelman.FlowMetricBall G.flow τ),
          t - theta / G.flow.scalar t x ≤ τ → (τ : ℝ) ≤ t → B.radius ≤ rho →
            B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed kappa) →
        ∀ (arms : Fin 2 → MinimizingArm (G.flow.base.metric t) x) (ell : Fin 2 → ℝ),
          (∀ j, ell j ∈ Ioc 0 (arms j).length) →
          (∀ j, Real.sqrt (G.flow.scalar t x) * ell j ∈ Icc D (2 * D)) →
          angle ≤ comparisonAngle (ell 0) (ell 1)
            (metricDistance (G.flow.base.metric t) ((arms 0).point (ell 0))
              ((arms 1).point (ell 1))) →
          Nonempty (StrongNeck G.flow delta x t) := by
  classical
  obtain ⟨dseq, hdpos, hdzero, hlimit⟩ :=
    exists_windowed_tolerances_for_original_arm_cylinder_limit.{u}
  let eps : ℕ → ℝ := fun i => min (dseq i) (1 / 2)
  have heps : ∀ i, 0 < eps i := fun i => lt_min (hdpos i) (by norm_num)
  have heps1 : ∀ i, eps i < 1 := fun i => (min_le_right _ _).trans_lt (by norm_num)
  have hthr := fun i => exists_uniform_orientedWitness_of_parabolically_noncollapsed.{u}
    (heps i) (heps1 i) hkappa hrho hPhi
  choose Q th hQ hth hW using hthr
  by_contra hno
  have key : ∀ i : ℕ, ∃ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
      (x : P.Carrier) (t : ℝ) (arms : Fin 2 → MinimizingArm (G.flow.base.metric t) x)
      (ell : Fin 2 → ℝ),
      OrientedWitness G.flow P.orientation (eps i) (kappa / modelNoncollapseFactor) x t ∧
      (∀ j, ell j ∈ Ioc 0 (arms j).length) ∧
      (∀ j, Real.sqrt (G.flow.scalar t x) * ell j ∈ Icc ((i : ℝ) + 1) (2 * ((i : ℝ) + 1))) ∧
      angle ≤ comparisonAngle (ell 0) (ell 1)
        (metricDistance (G.flow.base.metric t) ((arms 0).point (ell 0))
          ((arms 1).point (ell 1))) ∧
      IsEmpty (StrongNeck G.flow delta x t) := by
    intro i
    by_contra hi
    apply hno
    refine ⟨(i : ℝ) + 1, Q i, th i, by positivity, hQ i, hth i, ?_⟩
    intro P a s G x t hts hQx hwin hpinch hnc arms ell hell hlen hang
    by_contra hn
    exact hi ⟨P, a, s, G, x, t, arms, ell, hW i P a s G x t hts hQx hwin hpinch hnc,
      hell, hlen, hang, not_nonempty_iff.mp hn⟩
  choose P a s G x t arms ell hOW hell hlen hang hempty using key
  let W := fun i => (hOW i).choose
  have hregular : ∀ i, Ioo (t i - (eps i * (G i).flow.scalar (t i) (x i))⁻¹) (t i) ⊆
      (RealTimeInterval.closedOpen (a i) (s i) (G i).lt).regular := by
    intro i
    simpa only [RealTimeInterval.closedOpen, interior_Icc, interior_Ico] using
      interior_mono (W i).window_mem
  obtain ⟨L, phi, hphi, hL, _hbase, F, hcmp, _p, _e, _hmark, _hmetric, hnecks, _⟩ :=
    hlimit (fun i => (P i).Carrier) (fun i => RealTimeInterval.closedOpen (a i) (s i) (G i).lt)
      (fun i => (G i).flow) (fun i => (G i).equation) (fun i => (P i).orientation)
      (kappa / modelNoncollapseFactor) x t eps W (fun i => min_le_left _ _) hregular
      arms ell hell hlen angle hangle (Eventually.of_forall hang)
  have hepsZero : Tendsto eps atTop (𝓝 0) :=
    squeeze_zero (fun i => (heps i).le) (fun i => min_le_left _ _) hdzero
  have htol : 0 < neckModelTolerance (delta / 2) := neckModelTolerance_pos (half_pos hdelta)
  let beta := min (neckModelTolerance (delta / 2) / 2) (1 / 22)
  have hbeta : 0 < beta := lt_min (half_pos htol) (by norm_num)
  have hbeta1 : beta < 1 / 11 := (min_le_right _ _).trans_lt (by norm_num)
  have hbetaTol : beta < neckModelTolerance (delta / 2) :=
    (min_le_left _ _).trans_lt (half_lt_self htol)
  obtain ⟨nk, _⟩ := hnecks beta hbeta hbeta1
  let _ : ConnectedSpace L.M := hL.connected
  have hcomplete : MetricComplete (L.atTime 0) := hL.complete 0 (by simp)
  have hev := StrongNeck.eventually_transport_of_windowed_models (fun i => (G i).equation) W
    hepsZero hregular L hcomplete hphi.tendsto_atTop F hcmp nk (half_pos hdelta)
    (by linarith) hbetaTol
  obtain ⟨i, nk', _⟩ := hev.exists
  have hpt : (W (phi i)).embedding (F.map i L.basepoint) = x (phi i) := by
    rw [show F.map i L.basepoint = (W (phi i)).model.basepoint from F.basepoint_map i]
    exact (W (phi i)).base_map
  have h2 : 2 * (delta / 2) = delta := by ring
  rw [hpt, h2] at nk'
  exact (hempty (phi i)).false nk'

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
