import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialDistanceCutoff

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

variable [IsManifold I 1 M]



structure ShiSelfCoupledCutoff
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T A B Dcoef : Real) (Theta : Real → M → Real) where
  chi : M → Real
  support : Set M
  chi_continuous : Continuous chi
  chi_mem_Icc : ∀ x : M, chi x ∈ Set.Icc (0 : Real) 1
  support_compact : IsCompact support
  support_zero : ∀ x : M, x ∉ support → chi x = 0
  lower_support :
    ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M, 0 < chi x →
      Nonempty
        (ShiSelfCoupledLowerSupportAt (I := I) G T A
          (fun s y => B + Dcoef * Real.sqrt (chi y) * Theta s y)
          (fun _ y => chi y) t x)

def ShiInitialDistanceCutoff.toSelfCoupledCutoff
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {T r₁ r₂ A B Dcoef : Real} {p : M} {Theta : Real → M → Real}
    (cut : ShiInitialDistanceCutoff (I := I) S T p r₁ r₂ A B Dcoef Theta) :
    ShiSelfCoupledCutoff (I := I) (flowG (I := I) S) T A B Dcoef Theta where
  chi := cut.chi
  support := cut.support
  chi_continuous := cut.chi_continuous
  chi_mem_Icc := cut.chi_mem_Icc
  support_compact := cut.support_compact
  support_zero := cut.support_zero
  lower_support := cut.lower_support

def ShiCutoffLowerSupportAt.toSelfCoupled
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {T eps : Real} {χ : Real → M → Real} {t : Real} {x : M}
    (h : ShiCutoffLowerSupportAt (I := I) G T eps χ t x) :
    ShiSelfCoupledLowerSupportAt (I := I) G T eps (fun _ _ => eps) χ t x where
  phi := h.phi
  eq_at := h.eq_at
  lower_nhds := h.lower_nhds
  time_diff := h.time_diff
  space_diff_nhds := h.space_diff_nhds
  grad_diff := h.grad_diff
  grad_sq_le := h.grad_sq_le
  parabolic_le := h.parabolic_le

def bernsteinSelfCoupledBound (c C A B Dcoef kappa T : Real) : Real :=
  polynomialAbsorptionBound (T * Dcoef * kappa) (T * (B + 2 * A)) c C

theorem one_le_bernsteinSelfCoupledBound (c C A B Dcoef kappa T : Real) :
    1 ≤ bernsteinSelfCoupledBound c C A B Dcoef kappa T :=
  one_le_polynomialAbsorptionBound _ _ _ _

variable [I.Boundaryless]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]

theorem bernstein_quadratic_le_at_max_of_selfCoupled_lowerSupport
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {T A c C t₀ : Real} {Λ χ F : Real → M → Real} {x₀ : M}
    (low : ShiSelfCoupledLowerSupportAt (I := I) G T A Λ χ t₀ x₀)
    (ht₀ : t₀ ∈ Set.Icc 0 T) (ht₀pos : 0 < t₀) (hC : 0 ≤ C)
    (hchi0 : 0 ≤ χ t₀ x₀) (hchi1 : χ t₀ x₀ ≤ 1)
    (hF_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ F t x)
    (hF_time : DifferentiableWithinAt Real
      (fun s : Real => F s x₀) (Set.Icc 0 T) t₀)
    (hF_space : ∀ᶠ y in 𝓝 x₀, MDifferentiableAt I 𝓘(Real, Real) (F t₀) y)
    (hF_grad : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
      gradientFun (I := I) (G.metric t₀) (F t₀) y) x₀)
    (hmax : ∀ q : Real × M, q ∈ spacetimeSlab (M := M) T →
      χ q.1 q.2 * F q.1 q.2 ≤ χ t₀ x₀ * F t₀ x₀)
    (hF_evol : parabolicOperatorWithDrift (I := I) G T
        (fun _ y => (0 : TangentSpace I y)) F t₀ x₀ ≤
      -(c / t₀) * F t₀ x₀ ^ 2 + C / t₀) :
    c * (χ t₀ x₀ * F t₀ x₀) ^ 2 ≤
      C + t₀ * (χ t₀ x₀ * F t₀ x₀) * Λ t₀ x₀ +
        2 * A * t₀ * (χ t₀ x₀ * F t₀ x₀) := by
  have hPhi_max : ∀ᶠ q in 𝓝[spacetimeSlab (M := M) T] (t₀, x₀),
      low.phi q.1 q.2 * F q.1 q.2 ≤ low.phi t₀ x₀ * F t₀ x₀ := by
    filter_upwards [low.lower_nhds, self_mem_nhdsWithin] with q hq hqslab
    have h1 : low.phi q.1 q.2 * F q.1 q.2 ≤ χ q.1 q.2 * F q.1 q.2 :=
      mul_le_mul_of_nonneg_right hq.2 (hF_nonneg q.1 hqslab.1 q.2)
    have h2 := hmax q hqslab
    rw [low.eq_at]
    linarith
  have htend_time : Filter.Tendsto (fun s : Real => (s, x₀))
      (𝓝[Set.Icc 0 T] t₀) (𝓝[spacetimeSlab (M := M) T] (t₀, x₀)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcontmap : Continuous (fun s : Real => (s, x₀)) :=
        continuous_id.prodMk continuous_const
      exact (hcontmap.tendsto t₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact ⟨hs, Set.mem_univ x₀⟩
  have htend_space : Filter.Tendsto (fun y : M => (t₀, y))
      (𝓝 x₀) (𝓝[spacetimeSlab (M := M) T] (t₀, x₀)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(continuous_const.prodMk continuous_id).tendsto x₀, ?_⟩
    exact Filter.Eventually.of_forall fun y => ⟨ht₀, Set.mem_univ y⟩
  have htime_max : IsLocalMaxOn (fun s : Real => low.phi s x₀ * F s x₀)
      (Set.Icc 0 T) t₀ := htend_time.eventually hPhi_max
  have hspace_max : IsLocalMax (fun y : M => low.phi t₀ y * F t₀ y) x₀ :=
    htend_space.eventually hPhi_max
  have hphi_sp : ∀ᶠ y in 𝓝 x₀,
      MDifferentiableAt I 𝓘(Real, Real) (low.phi t₀) y := low.space_diff_nhds
  have hprod_sp : ∀ᶠ y in 𝓝 x₀, MDifferentiableAt I 𝓘(Real, Real)
      (fun z : M => low.phi t₀ z * F t₀ z) y := by
    filter_upwards [hphi_sp, hF_space] with y hy hFy
    exact hy.mul hFy
  have hprod_grad : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
      gradientFun (I := I) (G.metric t₀)
        (fun y : M => low.phi t₀ y * F t₀ y) z) x₀ := by
    have heq : (fun z : M => gradientFun (I := I) (G.metric t₀)
          (fun y : M => low.phi t₀ y * F t₀ y) z) =ᶠ[𝓝 x₀]
        (fun z : M => low.phi t₀ z •
            gradientFun (I := I) (G.metric t₀) (F t₀) z +
          F t₀ z • gradientFun (I := I) (G.metric t₀) (low.phi t₀) z) := by
      filter_upwards [hphi_sp, hF_space] with z hz hFz
      exact gradientFun_mul (I := I) (G.metric t₀) hz hFz
    have hsum : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
        low.phi t₀ z • gradientFun (I := I) (G.metric t₀) (F t₀) z +
          F t₀ z • gradientFun (I := I) (G.metric t₀) (low.phi t₀) z) x₀ :=
      mdifferentiableAt_add_section
        (hphi_sp.self_of_nhds.smul_section hF_grad)
        (hF_space.self_of_nhds.smul_section low.grad_diff)
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [heq] with z hz
    exact congrArg (fun q =>
      (⟨z, q⟩ : TotalSpace E (TangentSpace I : M → Type _))) hz
  have hlap_nonpos : laplacianAt (I := I) G t₀
      (fun y : M => low.phi t₀ y * F t₀ y) x₀ ≤ 0 :=
    laplacianAt_nonpos_at_spatial_max_of_isInteriorPoint (I := I) G t₀
      hspace_max BoundarylessManifold.isInteriorPoint
      hprod_sp.self_of_nhds hprod_sp hprod_grad
  have hgrad_zero : gradientFun (I := I) (G.metric t₀)
      (fun y : M => low.phi t₀ y * F t₀ y) x₀ = 0 := by
    have hneg : gradientFun (I := I) (G.metric t₀)
        (fun y : M => -(low.phi t₀ y * F t₀ y)) x₀ = 0 :=
      gradientFun_eq_zero_at_spatial_min (I := I) (G.metric t₀)
        hspace_max.neg hprod_sp.self_of_nhds.neg
    have hrw : gradientFun (I := I) (G.metric t₀)
        (fun y : M => -(low.phi t₀ y * F t₀ y)) x₀ =
        -gradientFun (I := I) (G.metric t₀)
          (fun y : M => low.phi t₀ y * F t₀ y) x₀ :=
      gradientFun_neg (I := I) (G.metric t₀) hprod_sp.self_of_nhds
    rw [hrw] at hneg
    exact neg_eq_zero.mp hneg
  have htime_diff : DifferentiableWithinAt Real
      (fun s : Real => low.phi s x₀ * F s x₀) (Set.Icc 0 T) t₀ :=
    low.time_diff.mul hF_time
  have hderiv_nonneg : 0 ≤ derivWithin
      (fun s : Real => low.phi s x₀ * F s x₀) (Set.Icc 0 T) t₀ :=
    derivWithin_nonneg_at_Icc_max_of_pos htime_max ht₀ ht₀pos
  have hpara_nonneg : 0 ≤ parabolicOperatorWithDrift (I := I) G T
      (fun _ y => (0 : TangentSpace I y))
      (fun s y => low.phi s y * F s y) t₀ x₀ := by
    have hheat : heatOperatorWithDrift (I := I) G t₀
        (fun y : M => (0 : TangentSpace I y))
        (fun y : M => low.phi t₀ y * F t₀ y) x₀ =
          laplacianAt (I := I) G t₀
            (fun y : M => low.phi t₀ y * F t₀ y) x₀ := by
      unfold heatOperatorWithDrift
      rw [driftTerm_zero_drift]
      ring
    rw [parabolicOperatorWithDrift_eq, hheat]
    linarith
  have hprod_rule := parabolic_mul_nhds (I := I) (G := G) T
    (fun _ y => (0 : TangentSpace I y)) low.phi F t₀ x₀
    low.time_diff hF_time hphi_sp hF_space low.grad_diff hF_grad
  rw [hprod_rule] at hpara_nonneg
  simp only [gradientAt_eq] at hpara_nonneg
  have hpF : low.phi t₀ x₀ • gradientFun (I := I) (G.metric t₀) (F t₀) x₀ =
      -(F t₀ x₀ • gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀) := by
    rw [eq_neg_iff_add_eq_zero, ← gradientFun_mul (I := I) (G.metric t₀)
      hphi_sp.self_of_nhds hF_space.self_of_nhds]
    exact hgrad_zero
  have hinner_eq : low.phi t₀ x₀ * (G.metric t₀).inner x₀
        (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀)
        (gradientFun (I := I) (G.metric t₀) (F t₀) x₀) =
      -(F t₀ x₀ * (G.metric t₀).inner x₀
        (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀)
        (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀)) := by
    calc low.phi t₀ x₀ * (G.metric t₀).inner x₀
            (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀)
            (gradientFun (I := I) (G.metric t₀) (F t₀) x₀)
        = ((G.metric t₀).inner x₀
            (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀))
            (low.phi t₀ x₀ •
              gradientFun (I := I) (G.metric t₀) (F t₀) x₀) := by
          rw [map_smul]
          simp
      _ = ((G.metric t₀).inner x₀
            (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀))
            (-(F t₀ x₀ •
              gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀)) := by
          rw [hpF]
      _ = -(F t₀ x₀ * (G.metric t₀).inner x₀
            (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀)
            (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀)) := by
          rw [map_neg, map_smul]
          simp
  have hFnn : 0 ≤ F t₀ x₀ := hF_nonneg t₀ ht₀ x₀
  have hz0 : 0 ≤ χ t₀ x₀ * F t₀ x₀ := mul_nonneg hchi0 hFnn
  have hp2 : χ t₀ x₀ ^ 2 ≤ 1 := by nlinarith
  have hphi_eq : low.phi t₀ x₀ = χ t₀ x₀ := low.eq_at
  rw [hphi_eq] at hpara_nonneg hinner_eq
  have hPF' : t₀ * parabolicOperatorWithDrift (I := I) G T
      (fun _ y => (0 : TangentSpace I y)) F t₀ x₀ ≤
        -(c * F t₀ x₀ ^ 2) + C := by
    have h := mul_le_mul_of_nonneg_left hF_evol ht₀pos.le
    have e1 : t₀ * (-(c / t₀) * F t₀ x₀ ^ 2 + C / t₀) =
        -(c * F t₀ x₀ ^ 2) + C := by
      field_simp
    rw [e1] at h
    exact h
  have hmul : 0 ≤ χ t₀ x₀ ^ 2 * parabolicOperatorWithDrift (I := I) G T
        (fun _ y => (0 : TangentSpace I y)) F t₀ x₀ +
      χ t₀ x₀ * F t₀ x₀ * parabolicOperatorWithDrift (I := I) G T
        (fun _ y => (0 : TangentSpace I y)) low.phi t₀ x₀ +
      2 * (F t₀ x₀ * (G.metric t₀).inner x₀
        (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀)
        (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀)) := by
    nlinarith [mul_nonneg hchi0 hpara_nonneg, hinner_eq]
  have hgradsq : (G.metric t₀).inner x₀
      (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀)
      (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀) ≤
        A * χ t₀ x₀ := by
    have h := low.grad_sq_le
    rw [hphi_eq] at h
    exact h
  have t1 : χ t₀ x₀ ^ 2 * (t₀ * parabolicOperatorWithDrift (I := I) G T
        (fun _ y => (0 : TangentSpace I y)) F t₀ x₀) ≤
      χ t₀ x₀ ^ 2 * (-(c * F t₀ x₀ ^ 2) + C) :=
    mul_le_mul_of_nonneg_left hPF' (sq_nonneg _)
  have t2 : (t₀ * (χ t₀ x₀ * F t₀ x₀)) *
        parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y)) low.phi t₀ x₀ ≤
      (t₀ * (χ t₀ x₀ * F t₀ x₀)) * Λ t₀ x₀ :=
    mul_le_mul_of_nonneg_left low.parabolic_le (mul_nonneg ht₀pos.le hz0)
  have t3 : (2 * (t₀ * F t₀ x₀)) * (G.metric t₀).inner x₀
        (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀)
        (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀) ≤
      (2 * (t₀ * F t₀ x₀)) * (A * χ t₀ x₀) :=
    mul_le_mul_of_nonneg_left hgradsq (by positivity)
  have t4 : 0 ≤ t₀ * (χ t₀ x₀ ^ 2 * parabolicOperatorWithDrift (I := I) G T
        (fun _ y => (0 : TangentSpace I y)) F t₀ x₀ +
      χ t₀ x₀ * F t₀ x₀ * parabolicOperatorWithDrift (I := I) G T
        (fun _ y => (0 : TangentSpace I y)) low.phi t₀ x₀ +
      2 * (F t₀ x₀ * (G.metric t₀).inner x₀
        (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀)
        (gradientFun (I := I) (G.metric t₀) (low.phi t₀) x₀))) :=
    mul_nonneg ht₀pos.le hmul
  nlinarith [t1, t2, t3, t4, mul_nonneg hC (sub_nonneg.mpr hp2)]

theorem bernstein_maximum_of_selfCoupled_cutoff
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {T A B Dcoef kappa c C : Real} {Theta : Real → M → Real}
    (cut : ShiSelfCoupledCutoff (I := I) G T A B Dcoef Theta)
    (F : Real → M → Real)
    (hT : 0 < T) (hc : 0 < c) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ Dcoef) (hkappa : 0 ≤ kappa)
    (hF_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ F t x)
    (hF_init : ∀ x : M, F 0 x = 0)
    (hF_cont : ContinuousOn (fun q : Real × M => F q.1 q.2)
      (spacetimeSlab (M := M) T))
    (hF_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => F s x) (Set.Icc 0 T) t)
    (hF_space : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (F t) x)
    (hF_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (F t) y) x)
    (hF_evol : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M, 0 < cut.chi x →
      parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y)) F t x ≤
        -(c / t) * F t x ^ 2 + C / t)
    (hTheta : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M, 0 < cut.chi x →
      ∃ s ∈ Set.Icc (0 : Real) t, Theta t x ≤ kappa * Real.sqrt (F s x)) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      cut.chi x * F t x ≤ bernsteinSelfCoupledBound c C A B Dcoef kappa T := by
  classical
  have hZ1 : (1 : Real) ≤ bernsteinSelfCoupledBound c C A B Dcoef kappa T :=
    one_le_bernsteinSelfCoupledBound c C A B Dcoef kappa T
  have hZ0 : (0 : Real) ≤ bernsteinSelfCoupledBound c C A B Dcoef kappa T :=
    le_trans zero_le_one hZ1
  by_cases hsupp : (cut.support).Nonempty
  · obtain ⟨x1, hx1⟩ := hsupp
    have hcompact : IsCompact (Set.Icc 0 T ×ˢ cut.support) :=
      isCompact_Icc.prod cut.support_compact
    have hne : (Set.Icc 0 T ×ˢ cut.support).Nonempty :=
      ⟨(0, x1), ⟨⟨le_rfl, hT.le⟩, hx1⟩⟩
    have hcont : ContinuousOn (fun q : Real × M => cut.chi q.2 * F q.1 q.2)
        (Set.Icc 0 T ×ˢ cut.support) :=
      ((cut.chi_continuous.comp continuous_snd).continuousOn).mul
        (hF_cont.mono (fun q hq => ⟨hq.1, Set.mem_univ _⟩))
    obtain ⟨⟨t0, x0⟩, hp0mem, hp0max⟩ := hcompact.exists_isMaxOn hne hcont
    have ht0 : t0 ∈ Set.Icc 0 T := hp0mem.1
    have hx0 : x0 ∈ cut.support := hp0mem.2
    have hmaxset : ∀ q ∈ Set.Icc 0 T ×ˢ cut.support,
        cut.chi q.2 * F q.1 q.2 ≤ cut.chi x0 * F t0 x0 :=
      fun q hq => hp0max hq
    have hkey : cut.chi x0 * F t0 x0 ≤
        bernsteinSelfCoupledBound c C A B Dcoef kappa T := by
      by_contra hbad
      push Not at hbad
      have hupos : 0 < cut.chi x0 * F t0 x0 := lt_of_lt_of_le
        (lt_of_lt_of_le zero_lt_one hZ1) hbad.le
      have hchi_range := cut.chi_mem_Icc x0
      have hfnn : 0 ≤ F t0 x0 := hF_nonneg t0 ht0 x0
      have hchipos : 0 < cut.chi x0 := by
        rcases lt_or_eq_of_le hchi_range.1 with h | h
        · exact h
        · exfalso
          rw [← h, zero_mul] at hupos
          exact lt_irrefl 0 hupos
      have ht0pos : 0 < t0 := by
        rcases lt_or_eq_of_le ht0.1 with h | h
        · exact h
        · exfalso
          rw [← h, hF_init x0, mul_zero] at hupos
          exact lt_irrefl 0 hupos
      have ht0Ioc : t0 ∈ Set.Ioc (0 : Real) T := ⟨ht0pos, ht0.2⟩
      have hmax_slab : ∀ q : Real × M, q ∈ spacetimeSlab (M := M) T →
          cut.chi q.2 * F q.1 q.2 ≤ cut.chi x0 * F t0 x0 := by
        intro q hq
        by_cases hqs : q.2 ∈ cut.support
        · exact hmaxset q ⟨hq.1, hqs⟩
        · rw [cut.support_zero q.2 hqs, zero_mul]
          exact hupos.le
      obtain ⟨low⟩ := cut.lower_support t0 ht0Ioc x0 hchipos
      have hcore : c * (cut.chi x0 * F t0 x0) ^ 2 ≤
          C + t0 * (cut.chi x0 * F t0 x0) *
              (B + Dcoef * Real.sqrt (cut.chi x0) * Theta t0 x0) +
            2 * A * t0 * (cut.chi x0 * F t0 x0) :=
        bernstein_quadratic_le_at_max_of_selfCoupled_lowerSupport low ht0 ht0pos
          hC hchi_range.1 hchi_range.2 hF_nonneg (hF_time t0 ht0 ht0pos x0)
          (Filter.Eventually.of_forall fun y => hF_space t0 ht0 ht0pos y)
          (hF_grad t0 ht0 ht0pos x0) hmax_slab
          (hF_evol t0 ht0 ht0pos x0 hchipos)
      have hz0 : 0 ≤ cut.chi x0 * F t0 x0 := hupos.le
      have hzpos : 0 < cut.chi x0 * F t0 x0 := hupos
      have hsc : Real.sqrt (cut.chi x0) * Theta t0 x0 ≤
          kappa * Real.sqrt (cut.chi x0 * F t0 x0) := by
        obtain ⟨s, hs, hsle⟩ := hTheta t0 ht0Ioc x0 hchipos
        have hsslab : s ∈ Set.Icc (0 : Real) T := ⟨hs.1, hs.2.trans ht0.2⟩
        have hZs : cut.chi x0 * F s x0 ≤ cut.chi x0 * F t0 x0 :=
          hmaxset (s, x0) ⟨hsslab, hx0⟩
        have hq0 : 0 ≤ Real.sqrt (cut.chi x0) := Real.sqrt_nonneg _
        have hstep1 : Real.sqrt (cut.chi x0) * Theta t0 x0 ≤
            Real.sqrt (cut.chi x0) * (kappa * Real.sqrt (F s x0)) :=
          mul_le_mul_of_nonneg_left hsle hq0
        have hstep2 : Real.sqrt (cut.chi x0) * (kappa * Real.sqrt (F s x0)) =
            kappa * Real.sqrt (cut.chi x0 * F s x0) := by
          rw [Real.sqrt_mul hchi_range.1]
          ring
        have hstep3 : kappa * Real.sqrt (cut.chi x0 * F s x0) ≤
            kappa * Real.sqrt (cut.chi x0 * F t0 x0) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hZs) hkappa
        rw [hstep2] at hstep1
        linarith
      have hpow : (cut.chi x0 * F t0 x0) ^ ((3 : Real) / 2) =
          (cut.chi x0 * F t0 x0) * Real.sqrt (cut.chi x0 * F t0 x0) := by
        have h1 : ((3 : Real) / 2) = 1 + 1 / 2 := by norm_num
        rw [h1, Real.rpow_add hzpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
      have hsq0 : 0 ≤ Real.sqrt (cut.chi x0 * F t0 x0) := Real.sqrt_nonneg _
      have hA1 : (t0 * (cut.chi x0 * F t0 x0) * Dcoef) *
            (Real.sqrt (cut.chi x0) * Theta t0 x0) ≤
          (t0 * (cut.chi x0 * F t0 x0) * Dcoef) *
            (kappa * Real.sqrt (cut.chi x0 * F t0 x0)) :=
        mul_le_mul_of_nonneg_left hsc (by positivity)
      have hA2 : t0 * (cut.chi x0 * F t0 x0) * B ≤
          T * B * (cut.chi x0 * F t0 x0) := by
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr ht0.2) hB) hz0]
      have hA3 : (t0 * (cut.chi x0 * F t0 x0) * Dcoef) *
            (kappa * Real.sqrt (cut.chi x0 * F t0 x0)) ≤
          (T * Dcoef * kappa) *
            ((cut.chi x0 * F t0 x0) * Real.sqrt (cut.chi x0 * F t0 x0)) := by
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
          (sub_nonneg.mpr ht0.2) hD) hkappa) hz0) hsq0]
      have hB1 : 2 * A * t0 * (cut.chi x0 * F t0 x0) ≤
          2 * A * T * (cut.chi x0 * F t0 x0) := by
        nlinarith [mul_nonneg (mul_nonneg hA (sub_nonneg.mpr ht0.2)) hz0]
      have hquad : c * (cut.chi x0 * F t0 x0) ^ 2 ≤
          (T * Dcoef * kappa) * (cut.chi x0 * F t0 x0) ^ ((3 : Real) / 2) +
            (T * (B + 2 * A)) * (cut.chi x0 * F t0 x0) + C := by
        rw [hpow]
        nlinarith [hcore, hA1, hA2, hA3, hB1]
      have habsorb := polynomial_absorption (a := T * Dcoef * kappa)
        (b := T * (B + 2 * A)) (c := c) (d := C)
        (z := cut.chi x0 * F t0 x0) hz0 hc hquad
      rw [bernsteinSelfCoupledBound] at hbad
      exact absurd habsorb (not_le.mpr hbad)
    intro t ht x
    by_cases hx : x ∈ cut.support
    · exact le_trans (hmaxset (t, x) ⟨ht, hx⟩) hkey
    · rw [cut.support_zero x hx, zero_mul]
      exact hZ0
  · intro t ht x
    have hx : x ∉ cut.support := by
      rw [Set.not_nonempty_iff_eq_empty] at hsupp
      simp [hsupp]
    rw [cut.support_zero x hx, zero_mul]
    exact hZ0


theorem bernstein_maximum_sq_of_selfCoupled_cutoff
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {T A B Dcoef kappa c C : Real} {Theta : Real → M → Real}
    (cut : ShiSelfCoupledCutoff (I := I) G T A B Dcoef Theta)
    (F : Real → M → Real)
    (hT : 0 < T) (hc : 0 < c) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ Dcoef) (hkappa : 0 ≤ kappa)
    (hF_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ F t x)
    (hF_init : ∀ x : M, F 0 x = 0)
    (hF_cont : ContinuousOn (fun q : Real × M => F q.1 q.2)
      (spacetimeSlab (M := M) T))
    (hF_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => F s x) (Set.Icc 0 T) t)
    (hF_space : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (F t) x)
    (hF_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (F t) y) x)
    (hF_evol : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M, 0 < cut.chi x →
      parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y)) F t x ≤
        -(c / t) * F t x ^ 2 + C / t)
    (hTheta : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M, 0 < cut.chi x →
      ∃ s ∈ Set.Icc (0 : Real) t, Theta t x ≤ kappa * Real.sqrt (F s x)) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      cut.chi x ^ 2 * F t x ≤
        bernsteinSelfCoupledBound c C A B Dcoef kappa T := by
  intro t ht x
  have hbase := bernstein_maximum_of_selfCoupled_cutoff (I := I) cut F hT hc hC
    hA hB hD hkappa hF_nonneg hF_init hF_cont hF_time hF_space hF_grad hF_evol
    hTheta t ht x
  have hrange := cut.chi_mem_Icc x
  have hFnn := hF_nonneg t ht x
  have hstep : cut.chi x ^ 2 * F t x ≤ cut.chi x * F t x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrange.2) (mul_nonneg hrange.1 hFnn)]
  linarith

end DifferentialGeometry.PDE.RicciFlow

end
