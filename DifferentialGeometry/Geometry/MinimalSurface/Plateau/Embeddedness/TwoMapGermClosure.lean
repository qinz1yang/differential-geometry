import DifferentialGeometry.Analysis.Calculus.Inverse.TwoMapCommonProjection
import DifferentialGeometry.Geometry.HarmonicMap.TwoMapMinimalGraphDifference
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientZero
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Analysis.Elliptic.Planar.IsothermalPrincipal
import DifferentialGeometry.Analysis.Elliptic.Planar.FirstOrderReduction
import DifferentialGeometry.Analysis.Complex.CauchyTransform.BoundedFixedPoint
import DifferentialGeometry.Analysis.Complex.CauchyTransform.BoundedWeakEquation
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.BoundedCoefficient
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.WeakGaugeApproximation
import DifferentialGeometry.Analysis.Complex.WeakHolomorphic.Continuous
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option autoImplicit false
noncomputable section

open Set Filter Metric MeasureTheory Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

-- The following three private proofs are exact reuse of the already checked
-- bounded-gauge and boundary-Cauchy receiving mechanics. Only private visibility
-- replaces the old gauge consumer's public visibility; no supplier is changed.
private theorem integrable_and_integral_realTestDbar_eq_zero
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z : ℂ =>
      ((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) ∧
    (∫ z : ℂ,
      ((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) = 0 := by
  have hi (v : ℂ) : Integrable (fun z : ℂ => fderiv ℝ φ z v) :=
    ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v)
  have hz (v : ℂ) : (∫ z : ℂ, fderiv ℝ φ z v) = 0 := by
    have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (f := fun _ : ℂ => (1 : ℝ)) (g := φ) (v := v)
      (by simp)
      (by simpa using hi v)
      (by simpa using hφ.continuous.integrable_of_hasCompactSupport hc)
      (fun _ _ => differentiableAt_const _)
      (fun z _ => (hφ.differentiable one_ne_zero) z)
    simpa using hh
  have hi1 : Integrable (fun z : ℂ => (fderiv ℝ φ z (1 : ℂ) : ℂ)) := (hi 1).ofReal
  have hiI : Integrable (fun z : ℂ => (fderiv ℝ φ z Complex.I : ℂ)) := (hi Complex.I).ofReal
  refine ⟨(hi1.add (hiI.const_mul Complex.I)).div_const 2, ?_⟩
  rw [integral_div, integral_add hi1 (hiI.const_mul Complex.I), integral_const_mul]
  simp only [integral_complex_ofReal, hz, Complex.ofReal_zero, mul_zero, add_zero, zero_div]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- The gauge is selected once from the same bounded measurable coefficient. Its literal
ambient representative agrees at every disk point and satisfies the weak equation there. -/
private theorem bounded_measurable_unit_gauge_with_weak_equation
    (a : ℂ) (R : ℝ) (hR : 0 < R)
    (A : closedBall a R → V →L[ℂ] V)
    (hA : AEStronglyMeasurable A (volume.comap ((↑) : closedBall a R → ℂ)))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)),
      ‖A w‖ ≤ B)
    (hk : 4 * R * B < 1 / 2) :
    ∃ P : C(closedBall a R, V →L[ℂ] V),
      P = 1 + CauchyTransform.boundedCoefficientCauchyTransform hR A hA hB hbound P ∧
      ‖P - 1‖ ≤ (4 * R * B) / (1 - 4 * R * B) ∧
      (∀ z : closedBall a R, IsUnit (P z)) ∧
      (let P₀ : ℂ → V →L[ℂ] V := fun z =>
        1 + diskCauchyIntegral (fun w => A w * P w) z
       (∀ z : closedBall a R, P₀ z = P z) ∧
       (∀ z ∈ closedBall a R, IsUnit (P₀ z)) ∧
       ∀ (φ : ℂ → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
         tsupport φ ⊆ ball a R →
         Integrable (fun z : ℂ =>
           (((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) •
             P₀ z) ∧
         (∫ z : ℂ,
           (((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) •
             P₀ z) =
           -(∫ w : closedBall a R, (φ (w : ℂ) : ℂ) • (A w * P w)
             ∂(volume.comap ((↑) : closedBall a R → ℂ)))) := by
  obtain ⟨P, hP, hnear, hunit, hintegral⟩ :=
    CauchyTransform.exists_unit_bounded_integral_fixedPoint a R hR A hA B hB hbound hk
  refine ⟨P, hP, hnear, hunit, ?_⟩
  dsimp only
  refine ⟨fun z => (hintegral z).symm, ?_, ?_⟩
  · intro z hz
    exact (congrArg (fun T : V →L[ℂ] V => IsUnit T)
      (hintegral ⟨z, hz⟩)).mp (hunit ⟨z, hz⟩)
  · intro φ hφ hc hs
    have hprod : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)),
        ‖A w * P w‖ ≤ B * ‖P‖ := by
      filter_upwards [hbound] with w hw
      exact (norm_mul_le _ _).trans
        (mul_le_mul hw (P.norm_coe_le_norm w) (norm_nonneg _) hB)
    obtain ⟨hCi, hC⟩ := integrable_and_weak_equation_diskCauchyIntegral
      (fun w => A w * P w)
      (hA.mul P.continuous.stronglyMeasurable.aestronglyMeasurable) hprod hφ hc hs
    obtain ⟨hDi, hDzero⟩ := integrable_and_integral_realTestDbar_eq_zero hφ hc
    let D (z : ℂ) : ℂ :=
      ((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2
    have hconst : Integrable (fun z : ℂ => D z • (1 : V →L[ℂ] V)) := hDi.smul_const 1
    constructor
    · apply (hconst.add hCi).congr
      exact Eventually.of_forall fun z =>
        (smul_add (D z) 1 (diskCauchyIntegral (fun w => A w * P w) z)).symm
    · change (∫ z : ℂ, D z • (1 + diskCauchyIntegral (fun w => A w * P w) z)) = _
      simp_rw [smul_add]
      rw [integral_add hconst hCi, integral_smul_const, hDzero, zero_smul, zero_add]
      exact hC


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
    bounded_measurable_unit_gauge_with_weak_equation
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


-- This scalar step is internal to the two-map receiving theorem. The actual
-- nonempty open zero set is obtained from the approaching image germs below.
private theorem scalar_zero_germ_of_closure_interior_zero
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {v : ℂ → ℝ} {B : ℂ → ℂ} {q : ℂ → ℝ}
    (hv : ContDiffOn ℝ ∞ v Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hq : ContDiffOn ℝ ∞ q Ω)
    (hpde : ∀ z ∈ Ω,
      Laplacian.laplacian v z + fderiv ℝ v z (B z) + q z * v z = 0)
    {a : ℂ} (ha : a ∈ Ω)
    (hcl : a ∈ closure (interior (v ⁻¹' ({0} : Set ℝ)))) :
    ∀ᶠ z in 𝓝 a, v z = 0 := by
  obtain ⟨U, C, hU, haU, hUΩ, hC, hbound⟩ :=
    exists_local_planarGradientSection_dbar_bound hΩ hv hB hq hpde ha
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds haU)
  let R : ℝ := min r (1 / (16 * (C + 1)))
  have hR : 0 < R := lt_min hr (by positivity)
  have hRr : R ≤ r := min_le_left _ _
  have hsmall : R * (16 * (C + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 16 * (C + 1))).mp (min_le_right _ _)
  have hk : 4 * R * C < 1 / 2 := by nlinarith
  have hRU : ball a R ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hRr)).trans hrU
  obtain ⟨b, hbzero, hba⟩ := Metric.mem_closure_iff.mp hcl (R / 2) (half_pos hR)
  have hb : b ∈ ball a (R / 2) :=
    Metric.mem_ball.mpr (by simpa only [dist_comm] using hba)
  have hZb : planarGradientSection v =ᶠ[𝓝 b] 0 := by
    filter_upwards [isOpen_interior.mem_nhds hbzero] with z hz
    have hzero : v =ᶠ[𝓝 z] fun _ => (0 : ℝ) := mem_interior_iff_mem_nhds.mp hz
    apply (planarGradientSection_eq_zero_iff v z).mpr
    refine ⟨hzero.eq_of_nhds, ?_⟩
    simpa only [fderiv_const_apply] using hzero.fderiv_eq (𝕜 := ℝ)
  have hZ : ContDiffOn ℝ 1 (planarGradientSection v) (ball a R) :=
    ((contDiffOn_planarGradientSection hΩ hv).mono (hRU.trans hUΩ)).of_le (by simp)
  have hvanish : EqOn (planarGradientSection v) 0 (ball a (R / 2)) :=
    pair_eq_zero_on_half_ball_of_dbar_bound a R C hR hC.le hk _ hZ
      (fun z hz => hbound z (hRU hz)) hb hZb
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (half_pos hR))]
    with z hz
  exact ((planarGradientSection_eq_zero_iff v z).mp (hvanish hz)).1

-- B67's limit factorization, with the two literal maps kept separate.
private theorem range_fderiv_le_of_two_map_germ_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X₁ X₂ : ℂ → E} {s₁ s₂ : Set ℂ}
    (hs₁ : IsOpen s₁) (hs₂ : IsOpen s₂)
    (hX₁ : ContDiffOn ℝ ∞ X₁ s₁) (hX₂ : ContDiffOn ℝ ∞ X₂ s₂)
    {a b : ℂ} (ha : a ∈ s₁) (hb : b ∈ s₂) (hvalue : X₁ a = X₂ b)
    (hDb : Function.Injective (fderiv ℝ X₂ b))
    {α β : ℕ → ℂ} (hα : Tendsto α atTop (𝓝 a)) (hβ : Tendsto β atTop (𝓝 b))
    (hgerm : ∀ᶠ n in atTop, Filter.map X₁ (𝓝 (α n)) = Filter.map X₂ (𝓝 (β n))) :
    LinearMap.range (fderiv ℝ X₁ a).toLinearMap ≤
      LinearMap.range (fderiv ℝ X₂ b).toLinearMap := by
  obtain ⟨r, U, V, hU, hUb, hV, hbV, _hVs, hr, hleft, hrb⟩ :=
    Analysis.exists_smooth_local_leftInverse hs₂ hX₂ hb hDb
  have hra : r (X₁ a) = b := by rw [hvalue]; exact hrb
  have hXa : ContDiffAt ℝ ∞ X₁ a := hX₁.contDiffAt (hs₁.mem_nhds ha)
  have hXb : ContDiffAt ℝ ∞ X₂ b := hX₂.contDiffAt (hs₂.mem_nhds hb)
  have hraSmooth : ContDiffAt ℝ ∞ r (X₁ a) := by
    rw [hvalue]
    exact hr.contDiffAt (hU.mem_nhds hUb)
  have hXr : ContDiffAt ℝ ∞ X₂ (r (X₁ a)) := by rwa [hra]
  let G : ℂ → E := X₂ ∘ r ∘ X₁
  have hG : ContDiffAt ℝ ∞ G a := hXr.comp a (hraSmooth.comp a hXa)
  have hevent : ∀ᶠ n in atTop, fderiv ℝ G (α n) = fderiv ℝ X₁ (α n) := by
    filter_upwards [hβ.eventually (hV.mem_nhds hbV), hgerm] with n hn hgn
    have hfix : {y : E | X₂ (r y) = y} ∈ Filter.map X₂ (𝓝 (β n)) := by
      apply Filter.mem_map.mpr
      apply Filter.mem_of_superset (hV.mem_nhds hn)
      intro z hz
      change X₂ (r (X₂ z)) = X₂ z
      rw [hleft z hz]
    rw [← hgn] at hfix
    have heq : G =ᶠ[𝓝 (α n)] X₁ := Filter.mem_map.mp hfix
    exact heq.fderiv_eq
  have hDGa : ContinuousAt (fderiv ℝ G) a :=
    (hG.fderiv_right (m := 0) (by simp)).continuousAt
  have hDXa : ContinuousAt (fderiv ℝ X₁) a :=
    (hXa.fderiv_right (m := 0) (by simp)).continuousAt
  have hD : fderiv ℝ G a = fderiv ℝ X₁ a :=
    tendsto_nhds_unique (hDGa.tendsto.comp hα)
      ((hDXa.tendsto.comp hα).congr' (Filter.EventuallyEq.symm hevent))
  have hchain := (hXr.differentiableAt (by simp)).hasFDerivAt.comp a
    ((hraSmooth.differentiableAt (by simp)).hasFDerivAt.comp a
      (hXa.differentiableAt (by simp)).hasFDerivAt)
  have hfactor : fderiv ℝ X₁ a = (fderiv ℝ X₂ b).comp
      ((fderiv ℝ r (X₁ a)).comp (fderiv ℝ X₁ a)) := by
    exact hD.symm.trans (by simpa only [G, hra] using hchain.fderiv)
  rintro v ⟨z, rfl⟩
  refine ⟨fderiv ℝ r (X₁ a) (fderiv ℝ X₁ a z), ?_⟩
  exact (congrArg (fun L : ℂ →L[ℝ] E => L z) hfactor).symm

private theorem fixed_two_graphs_eventuallyEq_of_image_germs
    {E : Type*} {X₁ X₂ : ℂ → E} (P : E → ℂ)
    (e₁ e₂ : OpenPartialHomeomorph ℂ ℂ)
    (he₁ : (e₁ : ℂ → ℂ) = P ∘ X₁) (he₂ : (e₂ : ℂ → ℂ) = P ∘ X₂)
    {a b : ℂ} (ha : a ∈ e₁.source) (hb : b ∈ e₂.source)
    (hgerm : Filter.map X₁ (𝓝 a) = Filter.map X₂ (𝓝 b)) :
    (X₁ ∘ e₁.symm) =ᶠ[𝓝 (P (X₁ a))] (X₂ ∘ e₂.symm) := by
  have hpre : X₁ ⁻¹' (X₂ '' e₂.source) ∈ 𝓝 a := by
    apply Filter.mem_map.mp
    rw [hgerm]
    exact Filter.image_mem_map (e₂.open_source.mem_nhds hb)
  have hmap : Filter.map e₁.symm (𝓝 (P (X₁ a))) = 𝓝 a := by
    simpa only [he₁, Function.comp_apply] using e₁.symm_map_nhds_eq ha
  have ht : Tendsto e₁.symm (𝓝 (P (X₁ a))) (𝓝 a) := by
    change Filter.map e₁.symm (𝓝 (P (X₁ a))) ≤ 𝓝 a
    rw [hmap]
  have hat : P (X₁ a) ∈ e₁.target := by
    simpa only [he₁, Function.comp_apply] using e₁.map_source ha
  filter_upwards [ht.eventually hpre, e₁.open_target.mem_nhds hat] with y hy hyt
  obtain ⟨z, hz, hXz⟩ := hy
  have hey : e₂ z = y := by
    calc
      e₂ z = P (X₂ z) := congrFun he₂ z
      _ = P (X₁ (e₁.symm y)) := congrArg P hXz
      _ = e₁ (e₁.symm y) := (congrFun he₁ _).symm
      _ = y := e₁.right_inv hyt
  have hzy : e₂.symm y = z := by rw [← hey]; exact e₂.left_inv hz
  change X₁ (e₁.symm y) = X₂ (e₂.symm y)
  rw [hzy]
  exact hXz.symm

private theorem fixed_isothermal_interior_zero_accumulation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X₁ X₂ : ℂ → E} (P : E →L[ℝ] ℂ) (height : E → ℝ)
    (e₁ e₂ e : OpenPartialHomeomorph ℂ ℂ)
    (he₁ : (e₁ : ℂ → ℂ) = P ∘ X₁) (he₂ : (e₂ : ℂ → ℂ) = P ∘ X₂)
    {a b : ℂ} (ha : a ∈ e₁.source) (hb : b ∈ e₂.source)
    (he : P (X₁ a) ∈ e.source) (he0 : e (P (X₁ a)) = 0)
    (hXa : ContinuousAt X₁ a)
    {α β : ℕ → ℂ} (hα : Tendsto α atTop (𝓝 a)) (hβ : Tendsto β atTop (𝓝 b))
    (hgerm : ∀ᶠ n in atTop, Filter.map X₁ (𝓝 (α n)) = Filter.map X₂ (𝓝 (β n))) :
    let w : ℂ → ℝ := fun y => height (X₁ (e₁.symm y)) - height (X₂ (e₂.symm y))
    let v : ℂ → ℝ := w ∘ e.symm
    (0 : ℂ) ∈ closure (interior (v ⁻¹' ({0} : Set ℝ))) := by
  intro w v
  have hF : Tendsto (fun n => P (X₁ (α n))) atTop (𝓝 (P (X₁ a))) :=
    (P.continuous.continuousAt.comp hXa).tendsto.comp hα
  have htheta : Tendsto (fun n => e (P (X₁ (α n)))) atTop (𝓝 (0 : ℂ)) := by
    simpa only [he0, Function.comp_def] using (e.continuousAt he).tendsto.comp hF
  apply mem_closure_of_tendsto htheta
  filter_upwards [hα.eventually (e₁.open_source.mem_nhds ha),
    hβ.eventually (e₂.open_source.mem_nhds hb),
    hF.eventually (e.open_source.mem_nhds he), hgerm] with n hn₁ hn₂ hnE hgn
  have hgraph := fixed_two_graphs_eventuallyEq_of_image_germs P e₁ e₂ he₁ he₂ hn₁ hn₂ hgn
  have hw : ∀ᶠ y in 𝓝 (P (X₁ (α n))), w y = 0 := by
    filter_upwards [hgraph] with y hy
    change height (X₁ (e₁.symm y)) - height (X₂ (e₂.symm y)) = 0
    exact sub_eq_zero.mpr (congrArg height hy)
  have hi : Tendsto e.symm (𝓝 (e (P (X₁ (α n))))) (𝓝 (P (X₁ (α n)))) := by
    change Filter.map e.symm _ ≤ _
    rw [e.symm_map_nhds_eq hnE]
  exact mem_interior_iff_mem_nhds.mpr (hi.eventually hw)

section MorreyMaps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem smooth_chart_gradient
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {p : M}
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source) :
    ContDiffOn ℝ ∞ (fun z (i : Fin (Module.finrank ℝ E)) =>
      chartComplexGradient (E := E) p U i z) s := by
  have hX : ContDiffOn ℝ ∞ (fun z => extChartAt 𝓘(ℝ, E) p (U z)) s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchart z hz)).comp z (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt).contDiffWithinAt
  apply contDiffOn_pi.mpr
  intro i
  have hc := (chartCoordCLM E i).contDiff.comp_contDiffOn hX
  have hd := hc.fderiv_of_isOpen (m := ∞) hs (by simp)
  have ha := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hb := hd.clm_apply (contDiffOn_const (c := Complex.I))
  have hp := (ha.mul (contDiffOn_const (c := (2 : ℝ)⁻¹))).prodMk
    (hb.neg.mul (contDiffOn_const (c := (2 : ℝ)⁻¹)))
  refine (Complex.equivRealProdCLM.symm.contDiff.comp_contDiffOn hp).congr ?_
  intro z _
  change (⟨fderiv ℝ (fun q => chartCoordCLM E i (extChartAt 𝓘(ℝ, E) p (U q))) z 1 / 2,
      -fderiv ℝ (fun q => chartCoordCLM E i (extChartAt 𝓘(ℝ, E) p (U q))) z Complex.I / 2⟩ : ℂ) =
    Complex.equivRealProdCLM.symm _
  apply Complex.ext <;> simp [Function.comp_def,
    Complex.equivRealProdCLM_symm_apply, div_eq_mul_inv]

/-- Image-germ equality of two actual Morrey disks persists at regular interior
limit points. The two disks retain their own traces and the same original
metric. Rank is needed only at the two limit points. No global injectivity,
closedness, transversality alternative, or uniqueness premise is used. -/
theorem IsMorreyDisk.image_germs_eq_of_regular_interior_limit
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ₁ γ₂ : freeLoop M}
    {q₁ q₂ : C(closedDisk, M)}
    (h₁ : IsMorreyDisk g γ₁ q₁) (h₂ : IsMorreyDisk g γ₂ q₂)
    (hd3 : Module.finrank ℝ E = 3)
    {a b : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1)
    (hb : b ∈ Metric.ball (0 : ℂ) 1)
    (hvalue : diskExtension q₁ a = diskExtension q₂ b)
    (hDa : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q₁) a))
    (hDb : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q₂) b))
    {α β : ℕ → ℂ} (hα : Tendsto α atTop (𝓝 a))
    (hβ : Tendsto β atTop (𝓝 b))
    (hgerm : ∀ᶠ n in atTop,
      Filter.map (diskExtension q₁) (𝓝 (α n)) =
        Filter.map (diskExtension q₂) (𝓝 (β n))) :
    Filter.map (diskExtension q₁) (𝓝 a) =
      Filter.map (diskExtension q₂) (𝓝 b) := by
  classical
  let U₁ : ℂ → M := diskExtension q₁
  let U₂ : ℂ → M := diskExtension q₂
  let p := U₁ a
  let s₁ : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ U₁ ⁻¹' (chartAt E p).source
  let s₂ : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ U₂ ⁻¹' (chartAt E p).source
  let X₁ : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U₁ z)
  let X₂ : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U₂ z)
  have hUV : U₁ a = U₂ b := hvalue
  have hUc₁ : Continuous U₁ := q₁.continuous.comp diskRetraction_lipschitz.continuous
  have hUc₂ : Continuous U₂ := q₂.continuous.comp diskRetraction_lipschitz.continuous
  have hs₁ : IsOpen s₁ :=
    Metric.isOpen_ball.inter ((chartAt E p).open_source.preimage hUc₁)
  have hs₂ : IsOpen s₂ :=
    Metric.isOpen_ball.inter ((chartAt E p).open_source.preimage hUc₂)
  have has : a ∈ s₁ := ⟨ha, mem_chart_source E p⟩
  have hbs : b ∈ s₂ := ⟨hb, by
    change U₂ b ∈ (chartAt E p).source
    rw [← hUV]
    exact mem_chart_source E p⟩
  have hU₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₁ s₁ :=
    h₁.smoothInterior.mono inter_subset_left
  have hU₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₂ s₂ :=
    h₂.smoothInterior.mono inter_subset_left
  have hX₁ : ContDiffOn ℝ ∞ X₁ s₁ := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hz.2).comp z
      (hU₁.contMDiffAt (hs₁.mem_nhds hz))).contDiffAt).contDiffWithinAt
  have hX₂ : ContDiffOn ℝ ∞ X₂ s₂ := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hz.2).comp z
      (hU₂.contMDiffAt (hs₂.mem_nhds hz))).contDiffAt).contDiffWithinAt
  have hXvalue : X₁ a = X₂ b := congrArg (extChartAt 𝓘(ℝ, E) p) hvalue
  have hrankChart (U : ℂ → M) (z : ℂ)
      (hz : U z ∈ (chartAt E p).source)
      (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U z)
      (hi : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
      Function.Injective (fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (U w)) z) := by
    have hc := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hz
    have hDX : fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (U w)) z =
        (show E →L[ℝ] E from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
          (extChartAt 𝓘(ℝ, E) p) (U z)).comp
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) :=
      mfderiv_eq_fderiv.symm.trans
        (mfderiv_comp z (hc.mdifferentiableAt (by simp)) (hU.mdifferentiableAt (by simp)))
    rw [hDX]
    exact (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E))
      (show U z ∈ (extChartAt 𝓘(ℝ, E) p).source by
        simpa only [extChartAt_source] using hz)).injective.comp hi
  have hXDa : Function.Injective (fderiv ℝ X₁ a) :=
    hrankChart U₁ a has.2 (hU₁.contMDiffAt (hs₁.mem_nhds has)) hDa
  have hXDb : Function.Injective (fderiv ℝ X₂ b) :=
    hrankChart U₂ b hbs.2 (hU₂.contMDiffAt (hs₂.mem_nhds hbs)) hDb
  have hXgerm : ∀ᶠ n in atTop,
      Filter.map X₁ (𝓝 (α n)) = Filter.map X₂ (𝓝 (β n)) := by
    filter_upwards [hgerm] with n hn
    change Filter.map U₁ (𝓝 (α n)) = Filter.map U₂ (𝓝 (β n)) at hn
    change Filter.map ((extChartAt 𝓘(ℝ, E) p) ∘ U₁) (𝓝 (α n)) =
      Filter.map ((extChartAt 𝓘(ℝ, E) p) ∘ U₂) (𝓝 (β n))
    rw [← Filter.map_map, ← Filter.map_map, hn]
  have hrangeX : LinearMap.range (fderiv ℝ X₂ b).toLinearMap ≤
      LinearMap.range (fderiv ℝ X₁ a).toLinearMap :=
    range_fderiv_le_of_two_map_germ_limit hs₂ hs₁ hX₂ hX₁ hbs has hXvalue.symm
      hXDa hβ hα (by filter_upwards [hXgerm] with n hn using hn.symm)
  let ξ : ℂ → (Fin (Module.finrank ℝ E) → ℂ) :=
    fun z i => chartComplexGradient p U₁ i z
  let Q := chartGramBilin g p p
  let proj := chartLeadingPlaneProjection g p p (ξ a)
  let F₁ : ℂ → ℂ := fun z => proj (X₁ z)
  let F₂ : ℂ → ℂ := fun z => proj (X₂ z)
  let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
    (fun i => (2 : ℝ) * (w * ξ a i).re)
  have hUa := hU₁.contMDiffAt (hs₁.mem_nhds has)
  have hξ : ContDiffAt ℝ 1 ξ a :=
    ((smooth_chart_gradient hs₁ hU₁ (fun _ hz => hz.2)).contDiffAt
      (hs₁.mem_nhds has)).of_le (by simp)
  have hξne : ξ a ≠ 0 := by
    intro hzero
    have hgrad : ∀ i, chartComplexGradient p U₁ i a = 0 := fun i => congrFun hzero i
    have hDzero := (_root_.DifferentialGeometry.Geometry.chartComplexGradient_eq_zero_iff_mfderiv_eq_zero
      (hUa.of_le (by simp)) has.2).mp hgrad
    apply one_ne_zero (α := ℂ)
    apply hDa
    rw [hDzero]
    rfl
  have hfactor : ∀ᶠ z in 𝓝 a,
      (fun i => chartComplexGradient p U₁ i z) = (z - a) ^ (0 : ℕ) • ξ z := by
    filter_upwards [] with z
    simp only [pow_zero, one_smul]
    rfl
  obtain ⟨C, r, _, hr, _, _, herr⟩ :=
    chartComplexGradient_leading_projection_fderiv_error g hs₁ (hU₁.of_le (by simp))
      (fun z hz => h₁.conformal z hz.1) has has.2 hξ hξne hfactor
  have hFa : fderiv ℝ F₁ a = ContinuousLinearMap.id ℝ ℂ := by
    ext v
    have hbound := herr a (Metric.mem_ball_self hr) v
    change ‖fderiv ℝ F₁ a v - (a - a) ^ (0 : ℕ) * v‖ ≤
      C * ‖a - a‖ ^ (0 + 1) * ‖v‖ at hbound
    have hnorm : ‖fderiv ℝ F₁ a v - v‖ ≤ 0 := by
      simpa only [sub_self, norm_zero, Nat.zero_add, pow_zero, pow_one,
        one_mul, mul_zero, zero_mul] using hbound
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))
  have hF₁ : ContDiffOn ℝ ∞ F₁ s₁ := proj.contDiff.comp_contDiffOn hX₁
  have hDF : fderiv ℝ F₁ a = proj.comp (fderiv ℝ X₁ a) :=
    (proj.hasFDerivAt.comp a ((hX₁.contDiffAt (hs₁.mem_nhds has)).differentiableAt
      (by simp)).hasFDerivAt).fderiv
  have hPa : (proj.comp (fderiv ℝ X₁ a)).IsInvertible := by
    rw [← hDF, hFa]
    exact ⟨ContinuousLinearEquiv.refl ℝ ℂ, rfl⟩
  obtain ⟨e₁, e₂, hae₁, hbe₂, he₁s, he₂s, he₁, he₂, hei₁, hei₂, htargets⟩ :=
    Analysis.exists_two_map_common_projection_inverse_germs hs₁ hs₂ hX₁ hX₂ proj
      has hbs hXvalue hPa hXDb hrangeX
  change (e₁ : ℂ → ℂ) = F₁ at he₁
  change (e₂ : ℂ → ℂ) = F₂ at he₂
  have hnear : ∀ᶠ z in 𝓝 a, z ∈ s₁ ∧ (fderiv ℝ F₁ z).IsInvertible := by
    have hcont := (hF₁.continuousOn_fderiv_of_isOpen hs₁ (by simp) a has).continuousAt
      (hs₁.mem_nhds has)
    have hset : {L : ℂ →L[ℝ] ℂ | L.IsInvertible} ∈ 𝓝 (fderiv ℝ F₁ a) := by
      rw [hFa]
      exact (ContinuousLinearEquiv.refl ℝ ℂ).nhds
    filter_upwards [hs₁.mem_nhds has, hcont hset] with z hzs hzinv
    exact ⟨hzs, hzinv⟩
  obtain ⟨V, hVsub, hVo, haV⟩ := _root_.mem_nhds_iff.mp hnear
  have hVs : V ⊆ s₁ := fun z hz => (hVsub hz).1
  have hnull := chartComplexGradient_isotropic g (hUa.of_le (by simp)) has.2
    (h₁.conformal a ha)
  obtain ⟨N, hNN, hPN, hsplit, _⟩ :=
    chartLeadingPlaneProjection_exists_graph_germs g hd3 hVo (hU₁.mono hVs) haV
      (fun z hz => (hVs hz).2) hξne hnull (fun z hz _ => (hVsub hz).2)
  change Q N N = 1 at hNN
  change proj N = 0 at hPN
  change ∀ v : E, v = lift (proj v) + (Q N v) • N at hsplit
  have haChart : X₁ a ∈ (extChartAt 𝓘(ℝ, E) p).target :=
    (extChartAt 𝓘(ℝ, E) p).map_source (by
      simpa only [extChartAt_source] using
        (show U₁ a ∈ (chartAt E p).source from has.2))
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp
    (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p) (X₁ a) haChart
  let O : Set ℂ := (e₁.target ∩ e₂.target) ∩
    ((fun y => X₁ (e₁.symm y)) ⁻¹' Metric.ball (X₁ a) ε ∩
      (fun y => X₂ (e₂.symm y)) ⁻¹' Metric.ball (X₁ a) ε)
  have hXe₁ : ContDiffOn ℝ ∞ (fun y => X₁ (e₁.symm y)) e₁.target :=
    hX₁.comp hei₁ (fun y hy => he₁s (e₁.map_target hy))
  have hXe₂ : ContDiffOn ℝ ∞ (fun y => X₂ (e₂.symm y)) e₂.target :=
    hX₂.comp hei₂ (fun y hy => he₂s (e₂.map_target hy))
  have hOo : IsOpen O := by
    have ho₁ := hXe₁.continuousOn.isOpen_inter_preimage
      (t := Metric.ball (X₁ a) ε) e₁.open_target Metric.isOpen_ball
    have ho₂ := hXe₂.continuousOn.isOpen_inter_preimage
      (t := Metric.ball (X₁ a) ε) e₂.open_target Metric.isOpen_ball
    convert ho₁.inter ho₂ using 1
    ext y
    simp only [O, mem_inter_iff, mem_preimage]
    tauto
  have hFvalue : F₁ a = F₂ b := congrArg proj hXvalue
  have hinv₁ : e₁.symm (F₁ a) = a := by rw [← he₁]; exact e₁.left_inv hae₁
  have hinv₂ : e₂.symm (F₁ a) = b := by rw [hFvalue, ← he₂]; exact e₂.left_inv hbe₂
  have haO : F₁ a ∈ O := by
    refine ⟨htargets, ?_, ?_⟩
    · change X₁ (e₁.symm (F₁ a)) ∈ Metric.ball (X₁ a) ε
      rw [hinv₁]
      exact Metric.mem_ball_self hε
    · change X₂ (e₂.symm (F₁ a)) ∈ Metric.ball (X₁ a) ε
      rw [hinv₂, ← hXvalue]
      exact Metric.mem_ball_self hε
  have hOsub : O ⊆ e₁.target ∩ e₂.target := inter_subset_left
  have hsegment : ∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • X₂ (e₂.symm y) + t • X₁ (e₁.symm y) ∈
        (extChartAt 𝓘(ℝ, E) p).target := by
    intro y hy t ht
    exact hεsub ((convex_ball (X₁ a) ε) hy.2.2 hy.2.1
      (sub_nonneg.mpr ht.2) ht.1 (by ring))
  let height : E → ℝ := fun x => Q N (x - X₁ a)
  let H₁ : ℂ → ℝ := fun y => height (X₁ (e₁.symm y))
  let H₂ : ℂ → ℝ := fun y => height (X₂ (e₂.symm y))
  have hH₁ : ContDiffOn ℝ ∞ H₁ O :=
    (Q N).contDiff.comp_contDiffOn
      ((hXe₁.mono (hOsub.trans inter_subset_left)).sub contDiffOn_const)
  have hH₂ : ContDiffOn ℝ ∞ H₂ O :=
    (Q N).contDiff.comp_contDiffOn
      ((hXe₂.mono (hOsub.trans inter_subset_right)).sub contDiffOn_const)
  have hright₁ (y : ℂ) (hy : y ∈ O) : proj (X₁ (e₁.symm y)) = y := by
    change F₁ (e₁.symm y) = y
    rw [← he₁]
    exact e₁.right_inv (hOsub hy).1
  have hright₂ (y : ℂ) (hy : y ∈ O) : proj (X₂ (e₂.symm y)) = y := by
    change F₂ (e₂.symm y) = y
    rw [← he₂]
    exact e₂.right_inv (hOsub hy).2
  have hrecon₁ (y : ℂ) (hy : y ∈ O) :
      X₁ (e₁.symm y) = X₁ a + lift (y - F₁ a) + H₁ y • N := by
    have h := hsplit (X₁ (e₁.symm y) - X₁ a)
    rw [map_sub, hright₁ y hy] at h
    change X₁ (e₁.symm y) - X₁ a = lift (y - F₁ a) + H₁ y • N at h
    calc
      X₁ (e₁.symm y) = (lift (y - F₁ a) + H₁ y • N) + X₁ a :=
        sub_eq_iff_eq_add.mp h
      _ = X₁ a + lift (y - F₁ a) + H₁ y • N := by abel
  have hrecon₂ (y : ℂ) (hy : y ∈ O) :
      X₂ (e₂.symm y) = X₁ a + lift (y - F₁ a) + H₂ y • N := by
    have h := hsplit (X₂ (e₂.symm y) - X₁ a)
    rw [map_sub, hright₂ y hy] at h
    change X₂ (e₂.symm y) - X₁ a = lift (y - F₁ a) + H₂ y • N at h
    calc
      X₂ (e₂.symm y) = (lift (y - F₁ a) + H₂ y • N) + X₁ a :=
        sub_eq_iff_eq_add.mp h
      _ = X₁ a + lift (y - F₁ a) + H₂ y • N := by abel
  obtain ⟨A, beta, c, hA, hpos, hbeta, hc, hpde⟩ :=
    two_original_maps_graph_height_difference_on g p p (ξ a) N hNN hPN hsplit
      (a₁ := a) (a₂ := b) rfl hUV.symm hs₁ hs₂ hU₁ hU₂
      (fun z hz => h₁.conformal z hz.1) (fun z hz => h₂.conformal z hz.1)
      (fun z hz => h₁.harmonic z hz.1) (fun z hz => h₂.harmonic z hz.1)
      (fun _ hz => hz.2) (fun _ hz => hz.2) hOo hOo (Subset.refl O) ⟨F₁ a, haO⟩
      H₁ H₂ hH₁ hH₂ e₁.symm e₂.symm
      (hei₁.mono (hOsub.trans inter_subset_left))
      (hei₂.mono (hOsub.trans inter_subset_right))
      (fun _ hy => he₁s (e₁.map_target (hOsub hy).1))
      (fun _ hy => he₂s (e₂.map_target (hOsub hy).2))
      hright₁ hright₂ (fun _ _ => rfl) (fun _ _ => rfl) (by
        intro y hy t ht
        change (1 - t) • (X₁ a + lift (y - F₁ a) + H₂ y • N) +
          t • (X₁ a + lift (y - F₁ a) + H₁ y • N) ∈ _
        rw [← hrecon₂ y hy, ← hrecon₁ y hy]
        exact hsegment y hy t ht)
  let w : ℂ → ℝ := H₁ - H₂
  have hw : ContDiffOn ℝ ∞ w O := hH₁.sub hH₂
  have hpdeOriginal : ∀ y ∈ O, planarScalarOperator A beta c w y = 0 := hpde
  obtain ⟨e, lam, hep, _heO, he0, _he, _hei, _hlam, _hlampos,
    hv, hB, hq, hpdeReduced, hmap, _hzeros⟩ :=
    exists_local_isothermal_scalar_equation hOo A beta c w hA hbeta hc hw hpos
      hpdeOriginal haO
  let v : ℂ → ℝ := w ∘ e.symm
  have hcl : (0 : ℂ) ∈ closure (interior (v ⁻¹' ({0} : Set ℝ))) :=
    fixed_isothermal_interior_zero_accumulation proj height e₁ e₂ e he₁ he₂
      hae₁ hbe₂ hep he0 (hX₁.continuousOn.continuousAt (hs₁.mem_nhds has))
      hα hβ hXgerm
  have h0e : (0 : ℂ) ∈ e.target := by simpa only [he0] using e.map_source hep
  have hvzero : ∀ᶠ z in 𝓝 (0 : ℂ), v z = 0 :=
    scalar_zero_germ_of_closure_interior_zero e.open_target hv hB hq
      hpdeReduced h0e hcl
  have heT : Tendsto e (𝓝 (F₁ a)) (𝓝 (0 : ℂ)) := by
    simpa only [he0] using (e.continuousAt hep).tendsto
  have hwzero : ∀ᶠ y in 𝓝 (F₁ a), w y = 0 := by
    filter_upwards [heT.eventually hvzero, e.open_source.mem_nhds hep] with y hy hys
    exact (hmap y hys).symm.trans hy
  have hgraphs : (U₁ ∘ e₁.symm) =ᶠ[𝓝 (F₁ a)] (U₂ ∘ e₂.symm) := by
    filter_upwards [hwzero, hOo.mem_nhds haO] with y hy hyO
    have hheight : height (X₁ (e₁.symm y)) = height (X₂ (e₂.symm y)) :=
      sub_eq_zero.mp hy
    have hnormal : Q N (X₁ (e₁.symm y)) = Q N (X₂ (e₂.symm y)) := by
      simpa only [height, map_sub, sub_left_inj] using hheight
    apply (extChartAt 𝓘(ℝ, E) p).injOn
    · have hmem := (he₁s (e₁.map_target (hOsub hyO).1)).2
      change U₁ (e₁.symm y) ∈ (chartAt E p).source at hmem
      simpa only [extChartAt_source, Function.comp_def] using hmem
    · have hmem := (he₂s (e₂.map_target (hOsub hyO).2)).2
      change U₂ (e₂.symm y) ∈ (chartAt E p).source at hmem
      simpa only [extChartAt_source, Function.comp_def] using hmem
    · change X₁ (e₁.symm y) = X₂ (e₂.symm y)
      calc
        X₁ (e₁.symm y) =
            lift (proj (X₁ (e₁.symm y))) + Q N (X₁ (e₁.symm y)) • N := hsplit _
        _ = lift (proj (X₂ (e₂.symm y))) + Q N (X₂ (e₂.symm y)) • N := by
          rw [hright₁ y hyO, hright₂ y hyO, hnormal]
        _ = X₂ (e₂.symm y) := (hsplit _).symm
  have hmap₁ : Filter.map e₁.symm (𝓝 (F₁ a)) = 𝓝 a := by
    rw [← he₁]
    exact e₁.symm_map_nhds_eq hae₁
  have hmap₂ : Filter.map e₂.symm (𝓝 (F₁ a)) = 𝓝 b := by
    rw [hFvalue, ← he₂]
    exact e₂.symm_map_nhds_eq hbe₂
  change Filter.map U₁ (𝓝 a) = Filter.map U₂ (𝓝 b)
  rw [← hmap₁, ← hmap₂, Filter.map_map, Filter.map_map]
  exact Filter.map_congr hgraphs

end MorreyMaps

end DifferentialGeometry.Geometry
