import DifferentialGeometry.Analysis.Elliptic.Planar.BoundaryCauchyJets
import DifferentialGeometry.Analysis.Elliptic.Planar.BoundaryCauchyTransport
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.BoundedCoefficient
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.WeakGaugeApproximation
import DifferentialGeometry.Analysis.Complex.WeakHolomorphic.Continuous
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.BoundedGauge
import Mathlib.Analysis.Analytic.Uniqueness

set_option autoImplicit false
noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem pair_eq_zero_on_half_ball_of_dbar_bound
    (a : ℂ) (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hk : 4 * R * C < 1 / 2)
    (Z : ℂ → ℂ × ℂ) (hZ : ContDiffOn ℝ 1 Z (ball a R))
    (hbound : ∀ z ∈ ball a R, ‖complexDbar Z z‖ ≤ C * ‖Z z‖)
    {b : ℂ} (hb : b ∈ ball a (R / 2)) (hzero : Z =ᶠ[𝓝 b] 0) :
    EqOn Z 0 (ball a (R / 2)) := by
  obtain ⟨A, hA, hAeq, hAbound, _⟩ :=
    exists_measurable_pair_dbar_coefficient isOpen_ball hZ hC hbound
  have hAR : AEStronglyMeasurable (fun z : closedBall a R => A z)
      (volume.comap ((↑) : closedBall a R → ℂ)) :=
    (hA.comp measurable_subtype_coe).aestronglyMeasurable
  have hAB : ∀ᵐ z : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)),
      ‖A z‖ ≤ C := Eventually.of_forall fun z => hAbound z
  obtain ⟨P, _, hnear, _, hrep, hunit, hweak⟩ :=
    DiskRegularity.ConsumerAudit.bounded_measurable_unit_gauge_with_weak_equation
      a R hR (fun z : closedBall a R => A z) hAR C hC hAB hk
  let P₀ : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := fun z =>
    1 + diskCauchyIntegral (fun w : closedBall a R => A w * P w) z
  let δ := (4 * R * C) / (1 - 4 * R * C)
  have hd : 0 < 1 - 4 * R * C := by linarith
  have hδ0 : 0 ≤ δ := div_nonneg (by positivity) hd.le
  have hδ : δ < 1 := (div_lt_one hd).mpr (by linarith)
  have hnear₀ : ∀ z ∈ closedBall a R, ‖P₀ z - 1‖ ≤ δ := by
    intro z hz
    have hrepz : P₀ z = P ⟨z, hz⟩ := hrep ⟨z, hz⟩
    rw [hrepz]
    exact ((P - 1).norm_coe_le_norm ⟨z, hz⟩).trans hnear
  obtain ⟨hcontinuous, hintegral⟩ := disk_gauge_inverse_section_weak_equation
    a R hR P P₀ A hrep hA.aestronglyMeasurable hδ0 hδ hC hnear₀ hAbound
    (fun φ hφ hc hs => (hweak φ hφ hc hs).2) Z hZ
    (fun z hz => (hAeq z hz).symm)
  let H : ℂ → ℂ × ℂ := fun z => Ring.inverse (P₀ z) (Z z)
  have hanalytic : AnalyticOnNhd ℂ H (ball a (R / 2)) := by
    apply analyticOnNhd_of_continuousOn_of_integral_realTestDbar_smul_eq_zero
      isOpen_ball hcontinuous
    intro φ hφ hc hs
    have hφc : ContDiff ℝ 1 (fun z => (φ z : ℂ)) :=
      (Complex.ofRealCLM.contDiff.comp hφ).of_le (by simp)
    have hh := hintegral (fun z => (φ z : ℂ)) hφc
      (hc.comp_left Complex.ofReal_zero)
      ((tsupport_comp_subset Complex.ofReal_zero φ).trans hs)
    have heq (z : ℂ) := complexDbar_ofReal (hφ.differentiable (by simp) z)
    simpa only [heq] using hh
  have hHzero : H =ᶠ[𝓝 b] 0 := by
    filter_upwards [hzero] with z hz
    simp only [H, hz, Pi.zero_apply, map_zero]
  have hH := hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball a (R / 2)).isPreconnected hb hHzero
  intro z hz
  have hzR : z ∈ closedBall a R :=
    ball_subset_closedBall ((ball_subset_ball (by linarith : R / 2 ≤ R)) hz)
  have hfactor : P₀ z (H z) = Z z := by
    change (P₀ z * Ring.inverse (P₀ z)) (Z z) = Z z
    rw [Ring.mul_inverse_cancel _ (hunit z hzR)]
    rfl
  simpa only [hH hz, Pi.zero_apply, map_zero] using hfactor.symm

/-- One-sided boundary Cauchy uniqueness for the full reduced scalar equation.
The same scalar function and its first derivative vanish near the marked seam
point on the original upper side. The equation retains both drift and potential;
no differential equation is imposed on the smooth extension below the seam.

This is the analytic receiving theorem for the selected-disk no-fold argument.
The geometric receiver must first provide Cauchy data along an actual seam arc
and either this flat-seam reduced equation or the corresponding transported
frontier jets. Pointwise conormal cancellation alone is insufficient. -/
theorem planar_boundary_cauchy_zero_germ
    {U : Set ℂ} (hU : IsOpen U) {v : ℂ → ℝ} {B : ℂ → ℂ} {q : ℂ → ℝ}
    (hv : ContDiffOn ℝ ∞ v U) (hB : ContDiffOn ℝ ∞ B U)
    (hq : ContDiffOn ℝ ∞ q U)
    (hpde : ∀ z ∈ U, 0 < z.im →
      Laplacian.laplacian v z + fderiv ℝ v z (B z) + q z * v z = 0)
    (hzero : ∀ z ∈ U, z.im = 0 → v z = 0 ∧ fderiv ℝ v z = 0)
    {a : ℂ} (ha : a ∈ U) (haim : a.im = 0) :
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ U ∧
      ∀ z ∈ ball a r, 0 ≤ z.im → v z = 0 ∧ fderiv ℝ v z = 0 := by
  classical
  obtain ⟨hA, hK⟩ := contDiffOn_planarGradientCoefficients hB hq
  let C := ‖planarGradientLinearCoefficient (B a) (q a)‖ +
    ‖planarGradientConjugateCoefficient (B a)‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hcont : ContinuousAt (fun z => ‖planarGradientLinearCoefficient (B z) (q z)‖ +
      ‖planarGradientConjugateCoefficient (B z)‖) a :=
    ((hA.continuousOn a ha).continuousAt (hU.mem_nhds ha)).norm.add
      (((hK.continuousOn a ha).continuousAt (hU.mem_nhds ha)).norm)
  have hnear : ∀ᶠ z in 𝓝 a,
      ‖planarGradientLinearCoefficient (B z) (q z)‖ +
        ‖planarGradientConjugateCoefficient (B z)‖ < C :=
    hcont.eventually_lt continuousAt_const (by dsimp [C]; linarith)
  have hboth : ∀ᶠ z in 𝓝 a, z ∈ U ∧
      ‖planarGradientLinearCoefficient (B z) (q z)‖ +
        ‖planarGradientConjugateCoefficient (B z)‖ < C := by
    filter_upwards [hU.mem_nhds ha, hnear] with z hz hc
    exact ⟨hz, hc⟩
  obtain ⟨T, hTsub, hTo, haT⟩ := _root_.mem_nhds_iff.mp hboth
  have hTU : T ⊆ U := fun z hz => (hTsub hz).1
  obtain ⟨r, hr, hrT⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hTo.mem_nhds haT)
  let R : ℝ := min r (1 / (16 * (C + 1)))
  have hR : 0 < R := lt_min hr (by positivity)
  have hRr : R ≤ r := min_le_left _ _
  have hsmall : R * (16 * (C + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 16 * (C + 1))).mp (min_le_right _ _)
  have hk : 4 * R * C < 1 / 2 := by nlinarith
  have hRT : ball a R ⊆ T :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hRr)).trans hrT
  let Z : ℂ → ℂ × ℂ := ({z : ℂ | 0 < z.im}).indicator (planarGradientSection v)
  obtain ⟨hZ, hbound, hinside, houtside⟩ :=
    planarGradientSection_zeroExtension_flat_seam hTo (hv.mono hTU)
      (hB.continuousOn.mono hTU) (hq.continuousOn.mono hTU)
      (fun z hz => hpde z (hTU hz)) (fun z hz => hzero z (hTU hz))
      (fun z hz _ => (hTsub hz).2.le)
  let b : ℂ := a - (R / 4 : ℝ) • Complex.I
  have hbim : b.im < 0 := by
    change (a - ((R / 4 : ℝ) : ℂ) * Complex.I).im < 0
    rw [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re, haim]
    linarith
  have hb : b ∈ ball a (R / 2) := by
    rw [mem_ball, dist_eq_norm]
    have hba : b - a = -((R / 4 : ℝ) • Complex.I) := by dsimp [b]; abel
    rw [hba, norm_neg, norm_smul, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < R / 4)]
    linarith
  have hZb : Z =ᶠ[𝓝 b] 0 := by
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hbim] with z hz
    exact houtside z hz.le
  have hvanish : EqOn Z 0 (ball a (R / 2)) :=
    pair_eq_zero_on_half_ball_of_dbar_bound a R C hR hC.le hk Z
      (hZ.mono hRT) (fun z hz => hbound z (hRT hz)) hb hZb
  refine ⟨R / 2, half_pos hR,
    ((ball_subset_ball (by linarith : R / 2 ≤ R)).trans hRT).trans hTU, ?_⟩
  intro z hz him
  rcases him.eq_or_lt with him | him
  · exact hzero z (hTU (hRT ((ball_subset_ball (by linarith : R / 2 ≤ R)) hz))) him.symm
  · apply (planarGradientSection_eq_zero_iff v z).mp
    rw [← hinside z him]
    exact hvanish hz

/-- Boundary uniqueness through the supplied isothermal map, retaining its
possibly curved image seam and the original scalar function. The principal
coordinates are data of the same original coefficients and are not reselected.
One coefficient and gauge are constructed for the literal zero-extended section
before transferring the conclusion back to the original side. -/
theorem planar_boundary_cauchy_zero_germ_in_same_isothermal_coordinates
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ) (c w : ℂ → ℝ)
    (e : OpenPartialHomeomorph ℂ ℂ) (lam : ℂ → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) e.source)
    (hbeta : ∀ i, ContDiffOn ℝ ∞ (fun x => beta x i) e.source)
    (hc : ContDiffOn ℝ ∞ c e.source) (hw : ContDiffOn ℝ ∞ w e.source)
    (hpos : ∀ x ∈ e.source, (A x).PosDef)
    (hpde : ∀ x ∈ e.source, 0 < x.im → planarScalarOperator A beta c w x = 0)
    (hzero : ∀ x ∈ e.source, x.im = 0 → w x = 0 ∧ fderiv ℝ w x = 0)
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (hlam : ContDiffOn ℝ ∞ lam e.source) (hlampos : ∀ x ∈ e.source, 0 < lam x)
    (hprincipal : ∀ x ∈ e.source, ∀ H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
      (∑ i : Fin 2, ∑ j : Fin 2, A x i j *
        H (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) i))
          (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) j))) =
        lam x * (H 1 1 + H Complex.I Complex.I))
    {a : ℂ} (ha : a ∈ e.source) (haim : a.im = 0) :
    let v : ℂ → ℝ := fun y => w (e.symm y)
    let s := e '' (e.source ∩ {x : ℂ | 0 < x.im})
    ∃ r : ℝ, 0 < r ∧ ball (e a) r ⊆ e.target ∧
      (∀ y ∈ ball (e a) r ∩ s, v y = 0 ∧ fderiv ℝ v y = 0) ∧
      ∃ T : Set ℂ, IsOpen T ∧ a ∈ T ∧ T ⊆ e.source ∧
        ∀ x ∈ T, 0 ≤ x.im → w x = 0 ∧ fderiv ℝ w x = 0 := by
  classical
  intro v s
  let B : ℂ → ℂ := fun y => (lam (e.symm y))⁻¹ •
    planarCoordinateDrift A beta e (e.symm y)
  let q : ℂ → ℝ := fun y => c (e.symm y) / lam (e.symm y)
  obtain ⟨hs, hst, hv, hB, hq, hPDE, hjets, hmap, hmem⟩ :=
    planarScalarOperator_isothermal_cauchy_data A beta c w e lam
      hA hbeta hc hw hpos hpde hzero he hei hlam hlampos hprincipal
  have hea := e.map_source ha
  obtain ⟨hL, hK⟩ := contDiffOn_planarGradientCoefficients hB hq
  let C := ‖planarGradientLinearCoefficient (B (e a)) (q (e a))‖ +
    ‖planarGradientConjugateCoefficient (B (e a))‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hcont : ContinuousAt (fun z => ‖planarGradientLinearCoefficient (B z) (q z)‖ +
      ‖planarGradientConjugateCoefficient (B z)‖) (e a) :=
    ((hL.continuousOn (e a) hea).continuousAt (e.open_target.mem_nhds hea)).norm.add
      (((hK.continuousOn (e a) hea).continuousAt (e.open_target.mem_nhds hea)).norm)
  have hnear : ∀ᶠ z in 𝓝 (e a),
      ‖planarGradientLinearCoefficient (B z) (q z)‖ +
        ‖planarGradientConjugateCoefficient (B z)‖ < C :=
    hcont.eventually_lt continuousAt_const (by dsimp [C]; linarith)
  have hboth : ∀ᶠ z in 𝓝 (e a), z ∈ e.target ∧
      ‖planarGradientLinearCoefficient (B z) (q z)‖ +
        ‖planarGradientConjugateCoefficient (B z)‖ < C := by
    filter_upwards [e.open_target.mem_nhds hea, hnear] with z hz hb
    exact ⟨hz, hb⟩
  obtain ⟨V, hVsub, hVo, heaV⟩ := _root_.mem_nhds_iff.mp hboth
  have hVt : V ⊆ e.target := fun z hz => (hVsub hz).1
  have hineq : ∀ z ∈ V ∩ s,
      ‖complexDbar (planarGradientSection v) z‖ ≤ C * ‖planarGradientSection v z‖ := by
    intro z hz
    change ‖(1 / 2 : ℂ) • (fderiv ℝ (planarGradientSection v) z 1 +
      Complex.I • fderiv ℝ (planarGradientSection v) z Complex.I)‖ ≤ _
    rw [planarGradientSection_dbar_eq (B z) (q z)
      ((hv.contDiffAt (e.open_target.mem_nhds (hVt hz.1))).of_le (by simp)) (hPDE z hz.2)]
    have hconj : ‖(starRingEnd ℂ (planarGradientSection v z).1,
        starRingEnd ℂ (planarGradientSection v z).2)‖ = ‖planarGradientSection v z‖ := by
      simp only [Prod.norm_def, Complex.norm_conj]
    calc
      _ ≤ ‖planarGradientLinearCoefficient (B z) (q z) (planarGradientSection v z)‖ +
          ‖planarGradientConjugateCoefficient (B z)
            (starRingEnd ℂ (planarGradientSection v z).1, starRingEnd ℂ (planarGradientSection v z).2)‖ := norm_add_le _ _
      _ ≤ ‖planarGradientLinearCoefficient (B z) (q z)‖ * ‖planarGradientSection v z‖ +
          ‖planarGradientConjugateCoefficient (B z)‖ *
            ‖(starRingEnd ℂ (planarGradientSection v z).1, starRingEnd ℂ (planarGradientSection v z).2)‖ :=
        add_le_add ((planarGradientLinearCoefficient (B z) (q z)).le_opNorm _)
          ((planarGradientConjugateCoefficient (B z)).le_opNorm _)
      _ = (‖planarGradientLinearCoefficient (B z) (q z)‖ +
          ‖planarGradientConjugateCoefficient (B z)‖) * ‖planarGradientSection v z‖ := by
        rw [hconj]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hVsub hz.1).2.le (norm_nonneg _)
  let Z : ℂ → ℂ × ℂ := s.indicator (planarGradientSection v)
  obtain ⟨hZ, _, hbound⟩ := complexDbar_indicator_of_frontier_firstJet_zero hVo hs
    (((contDiffOn_planarGradientSection e.open_target hv).of_le (by simp)).mono hVt)
    (fun z hz => hjets z ⟨hVt hz.1, hz.2⟩) hineq
  obtain ⟨r, hr, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hVo.mem_nhds heaV)
  let R : ℝ := min r (1 / (16 * (C + 1)))
  have hR : 0 < R := lt_min hr (by positivity)
  have hRr : R ≤ r := min_le_left _ _
  have hsmall : R * (16 * (C + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 16 * (C + 1))).mp (min_le_right _ _)
  have hk : 4 * R * C < 1 / 2 := by nlinarith
  have hRV : ball (e a) R ⊆ V :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hRr)).trans hrV
  let T := e.source ∩ e ⁻¹' ball (e a) (R / 2)
  have hT : IsOpen T := e.isOpen_inter_preimage isOpen_ball
  have haT : a ∈ T := ⟨ha, mem_ball_self (half_pos hR)⟩
  have halower : a ∈ closure {x : ℂ | x.im < 0} := by
    rw [Complex.closure_setOfPred_im_lt]
    exact haim.le
  obtain ⟨b, hbT, hbneg⟩ := mem_closure_iff.mp halower T hT haT
  let N := e.target ∩ e.symm ⁻¹' {x : ℂ | x.im < 0}
  have hN : IsOpen N := e.isOpen_inter_preimage_symm
    (isOpen_lt Complex.continuous_im continuous_const)
  have hebN : e b ∈ N := ⟨e.map_source hbT.1, by
    change (e.symm (e b)).im < 0
    rw [e.left_inv hbT.1]
    exact hbneg⟩
  have hZb : Z =ᶠ[𝓝 (e b)] 0 := by
    filter_upwards [hN.mem_nhds hebN] with z hz
    have hzs : z ∉ s := fun hh => lt_asymm ((hmem z hz.1).mp hh) hz.2
    exact indicator_of_notMem hzs _
  have hvanish : EqOn Z 0 (ball (e a) (R / 2)) :=
    pair_eq_zero_on_half_ball_of_dbar_bound (e a) R C hR hC.le hk Z
      (hZ.mono hRV) (fun z hz => hbound z (hRV hz)) hbT.2 hZb
  have hvalue : ∀ y ∈ ball (e a) (R / 2) ∩ s,
      v y = 0 ∧ fderiv ℝ v y = 0 := by
    intro y hy
    apply (planarGradientSection_eq_zero_iff v y).mp
    have hh := hvanish hy.1
    simpa only [Z, indicator_of_mem hy.2, Pi.zero_apply] using hh
  refine ⟨R / 2, half_pos hR,
    ((ball_subset_ball (by linarith : R / 2 ≤ R)).trans hRV).trans hVt,
    hvalue, T, hT, haT, inter_subset_left, ?_⟩
  intro x hx him
  rcases him.eq_or_lt with him | him
  · exact hzero x hx.1 him.symm
  · have hexs : e x ∈ s := ⟨x, ⟨hx.1, him⟩, rfl⟩
    obtain ⟨hv0, hdv0⟩ := hvalue (e x) ⟨hx.2, hexs⟩
    refine ⟨(hmap x hx.1).symm.trans hv0, ?_⟩
    have hnearMap : (fun z => v (e z)) =ᶠ[𝓝 x] w := by
      filter_upwards [e.open_source.mem_nhds hx.1] with z hz
      exact hmap z hz
    rw [← hnearMap.fderiv_eq, fderiv_fun_comp x
      ((hv.contDiffAt (e.open_target.mem_nhds (e.map_source hx.1))).differentiableAt (by simp))
      ((he.contDiffAt (e.open_source.mem_nhds hx.1)).differentiableAt (by simp)), hdv0]
    rfl

/-- One-sided uniqueness for a regular curved original seam, through the same
supplied isothermal map. The original side, scalar function and complete
operator are retained. A genuine open complementary side approaches the chosen
point; the literal zero extension therefore has an open zero set. Its single
coefficient/gauge construction proves the germ equality without an equation on
the complementary side. Actual two-sheet geometry must supply the stated side,
frontier parameters and Cauchy data. -/
theorem planar_boundary_cauchy_zero_germ_on_regular_side_in_same_isothermal_coordinates
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ) (c w : ℂ → ℝ)
    (e : OpenPartialHomeomorph ℂ ℂ) (lam : ℂ → ℝ)
    (S : Set ℂ) (hS : IsOpen S) (hSU : S ⊆ e.source)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) e.source)
    (hbeta : ∀ i, ContDiffOn ℝ ∞ (fun x => beta x i) e.source)
    (hc : ContDiffOn ℝ ∞ c e.source) (hw : ContDiffOn ℝ ∞ w e.source)
    (hpos : ∀ x ∈ e.source, (A x).PosDef)
    (hpde : ∀ x ∈ S, planarScalarOperator A beta c w x = 0)
    (hzero : ∀ x ∈ e.source ∩ frontier S, w x = 0 ∧ fderiv ℝ w x = 0)
    (hcurve : ∀ x ∈ e.source ∩ frontier S, ∃ (γ : ℝ → ℂ) (τ : ℂ),
      γ 0 = x ∧ HasDerivAt γ τ 0 ∧ τ ≠ 0 ∧
        ∀ᶠ t in 𝓝 0, γ t ∈ e.source ∩ frontier S)
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (hlam : ContDiffOn ℝ ∞ lam e.source) (hlampos : ∀ x ∈ e.source, 0 < lam x)
    (hprincipal : ∀ x ∈ e.source, ∀ H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
      (∑ i : Fin 2, ∑ j : Fin 2, A x i j *
        H (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) i))
          (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) j))) =
        lam x * (H 1 1 + H Complex.I Complex.I))
    {a : ℂ} (ha : a ∈ e.source) (haOther : a ∈ closure (interior Sᶜ)) :
    let v : ℂ → ℝ := fun y => w (e.symm y)
    let s := e '' (e.source ∩ S)
    ∃ r : ℝ, 0 < r ∧ ball (e a) r ⊆ e.target ∧
      (∀ y ∈ ball (e a) r ∩ s, v y = 0 ∧ fderiv ℝ v y = 0) ∧
      ∃ T : Set ℂ, IsOpen T ∧ a ∈ T ∧ T ⊆ e.source ∧
        ∀ x ∈ T ∩ closure S, w x = 0 ∧ fderiv ℝ w x = 0 := by
  classical
  intro v s
  let B : ℂ → ℂ := fun y => (lam (e.symm y))⁻¹ •
    planarCoordinateDrift A beta e (e.symm y)
  let q : ℂ → ℝ := fun y => c (e.symm y) / lam (e.symm y)
  obtain ⟨hs, hst, hv, hB, hq, hPDE, hjets, hmap, hmem⟩ :=
    planarScalarOperator_isothermal_cauchy_data_on_regular_side A beta c w e lam S hS hSU
      hA hbeta hc hw hpos hpde hzero hcurve he hei hlam hlampos hprincipal
  have hea := e.map_source ha
  obtain ⟨hL, hK⟩ := contDiffOn_planarGradientCoefficients hB hq
  let C := ‖planarGradientLinearCoefficient (B (e a)) (q (e a))‖ +
    ‖planarGradientConjugateCoefficient (B (e a))‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hcont : ContinuousAt (fun z => ‖planarGradientLinearCoefficient (B z) (q z)‖ +
      ‖planarGradientConjugateCoefficient (B z)‖) (e a) :=
    ((hL.continuousOn (e a) hea).continuousAt (e.open_target.mem_nhds hea)).norm.add
      (((hK.continuousOn (e a) hea).continuousAt (e.open_target.mem_nhds hea)).norm)
  have hnear : ∀ᶠ z in 𝓝 (e a),
      ‖planarGradientLinearCoefficient (B z) (q z)‖ +
        ‖planarGradientConjugateCoefficient (B z)‖ < C :=
    hcont.eventually_lt continuousAt_const (by dsimp [C]; linarith)
  have hboth : ∀ᶠ z in 𝓝 (e a), z ∈ e.target ∧
      ‖planarGradientLinearCoefficient (B z) (q z)‖ +
        ‖planarGradientConjugateCoefficient (B z)‖ < C := by
    filter_upwards [e.open_target.mem_nhds hea, hnear] with z hz hb
    exact ⟨hz, hb⟩
  obtain ⟨V, hVsub, hVo, heaV⟩ := _root_.mem_nhds_iff.mp hboth
  have hVt : V ⊆ e.target := fun z hz => (hVsub hz).1
  have hineq : ∀ z ∈ V ∩ s,
      ‖complexDbar (planarGradientSection v) z‖ ≤ C * ‖planarGradientSection v z‖ := by
    intro z hz
    change ‖(1 / 2 : ℂ) • (fderiv ℝ (planarGradientSection v) z 1 +
      Complex.I • fderiv ℝ (planarGradientSection v) z Complex.I)‖ ≤ _
    rw [planarGradientSection_dbar_eq (B z) (q z)
      ((hv.contDiffAt (e.open_target.mem_nhds (hVt hz.1))).of_le (by simp)) (hPDE z hz.2)]
    have hconj : ‖(starRingEnd ℂ (planarGradientSection v z).1,
        starRingEnd ℂ (planarGradientSection v z).2)‖ = ‖planarGradientSection v z‖ := by
      simp only [Prod.norm_def, Complex.norm_conj]
    calc
      _ ≤ ‖planarGradientLinearCoefficient (B z) (q z) (planarGradientSection v z)‖ +
          ‖planarGradientConjugateCoefficient (B z)
            (starRingEnd ℂ (planarGradientSection v z).1, starRingEnd ℂ (planarGradientSection v z).2)‖ := norm_add_le _ _
      _ ≤ ‖planarGradientLinearCoefficient (B z) (q z)‖ * ‖planarGradientSection v z‖ +
          ‖planarGradientConjugateCoefficient (B z)‖ *
            ‖(starRingEnd ℂ (planarGradientSection v z).1, starRingEnd ℂ (planarGradientSection v z).2)‖ :=
        add_le_add ((planarGradientLinearCoefficient (B z) (q z)).le_opNorm _)
          ((planarGradientConjugateCoefficient (B z)).le_opNorm _)
      _ = (‖planarGradientLinearCoefficient (B z) (q z)‖ +
          ‖planarGradientConjugateCoefficient (B z)‖) * ‖planarGradientSection v z‖ := by
        rw [hconj]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hVsub hz.1).2.le (norm_nonneg _)
  let Z : ℂ → ℂ × ℂ := s.indicator (planarGradientSection v)
  obtain ⟨hZ, _, hbound⟩ := complexDbar_indicator_of_frontier_firstJet_zero hVo hs
    (((contDiffOn_planarGradientSection e.open_target hv).of_le (by simp)).mono hVt)
    (fun z hz => hjets z ⟨hVt hz.1, hz.2⟩) hineq
  obtain ⟨r, hr, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hVo.mem_nhds heaV)
  let R : ℝ := min r (1 / (16 * (C + 1)))
  have hR : 0 < R := lt_min hr (by positivity)
  have hRr : R ≤ r := min_le_left _ _
  have hsmall : R * (16 * (C + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 16 * (C + 1))).mp (min_le_right _ _)
  have hk : 4 * R * C < 1 / 2 := by nlinarith
  have hRV : ball (e a) R ⊆ V :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hRr)).trans hrV
  let T := e.source ∩ e ⁻¹' ball (e a) (R / 2)
  have hT : IsOpen T := e.isOpen_inter_preimage isOpen_ball
  have haT : a ∈ T := ⟨ha, mem_ball_self (half_pos hR)⟩
  obtain ⟨b, hbT, hbOther⟩ := mem_closure_iff.mp haOther T hT haT
  let N := e.target ∩ e.symm ⁻¹' interior Sᶜ
  have hN : IsOpen N := e.isOpen_inter_preimage_symm isOpen_interior
  have hebN : e b ∈ N := ⟨e.map_source hbT.1, by
    change e.symm (e b) ∈ interior Sᶜ
    rw [e.left_inv hbT.1]
    exact hbOther⟩
  have hZb : Z =ᶠ[𝓝 (e b)] 0 := by
    filter_upwards [hN.mem_nhds hebN] with z hz
    have hzs : z ∉ s := fun hh => (interior_subset hz.2) ((hmem z hz.1).mp hh)
    exact indicator_of_notMem hzs _
  have hvanish : EqOn Z 0 (ball (e a) (R / 2)) :=
    pair_eq_zero_on_half_ball_of_dbar_bound (e a) R C hR hC.le hk Z
      (hZ.mono hRV) (fun z hz => hbound z (hRV hz)) hbT.2 hZb
  have hvalue : ∀ y ∈ ball (e a) (R / 2) ∩ s,
      v y = 0 ∧ fderiv ℝ v y = 0 := by
    intro y hy
    apply (planarGradientSection_eq_zero_iff v y).mp
    have hh := hvanish hy.1
    simpa only [Z, indicator_of_mem hy.2, Pi.zero_apply] using hh
  refine ⟨R / 2, half_pos hR,
    ((ball_subset_ball (by linarith : R / 2 ≤ R)).trans hRV).trans hVt,
    hvalue, T, hT, haT, inter_subset_left, ?_⟩
  intro x hx
  by_cases hxS : x ∈ S
  · have hexs : e x ∈ s := ⟨x, ⟨hx.1.1, hxS⟩, rfl⟩
    obtain ⟨hv0, hdv0⟩ := hvalue (e x) ⟨hx.1.2, hexs⟩
    refine ⟨(hmap x hx.1.1).symm.trans hv0, ?_⟩
    have hnearMap : (fun z => v (e z)) =ᶠ[𝓝 x] w := by
      filter_upwards [e.open_source.mem_nhds hx.1.1] with z hz
      exact hmap z hz
    rw [← hnearMap.fderiv_eq, fderiv_fun_comp x
      ((hv.contDiffAt (e.open_target.mem_nhds (e.map_source hx.1.1))).differentiableAt (by simp))
      ((he.contDiffAt (e.open_source.mem_nhds hx.1.1)).differentiableAt (by simp)), hdv0]
    rfl
  · have hxfront : x ∈ frontier S := by
      rw [frontier, hS.interior_eq]
      exact ⟨hx.2, hxS⟩
    exact hzero x ⟨hx.1.1, hxfront⟩

end DifferentialGeometry.Analysis
