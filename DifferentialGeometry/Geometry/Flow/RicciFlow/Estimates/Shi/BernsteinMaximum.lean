import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Cutoff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

structure ShiFixedCutoff
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T eps : Real) where
  chi : Real → M → Real
  support : Set M
  err_nonneg : 0 ≤ eps
  support_compact : IsCompact support
  support_zero :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, x ∉ support → chi t x = 0
  range :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, chi t x ∈ Set.Icc (0 : Real) 1
  joint_cont :
    ContinuousOn (fun p : Real × M => chi p.1 p.2) (Set.Icc 0 T ×ˢ support)
  lower_support :
    ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M, 0 < chi t x →
      Nonempty (ShiCutoffLowerSupportAt (I := I) G T eps chi t x)

def polynomialAbsorptionBound (a b c d : Real) : Real :=
  max 1 (max (4 * a / c) (max (4 * b / c) (4 * d / c))) ^ 2

theorem one_le_polynomialAbsorptionBound (a b c d : Real) :
    1 ≤ polynomialAbsorptionBound a b c d := by
  have h1 : (1 : Real) ≤ max 1 (max (4 * a / c) (max (4 * b / c) (4 * d / c))) :=
    le_max_left _ _
  unfold polynomialAbsorptionBound
  nlinarith

theorem polynomial_absorption {a b c d z : Real}
    (hz : 0 ≤ z) (hc : 0 < c)
    (hineq : c * z ^ 2 ≤ a * z ^ ((3 : Real) / 2) + b * z + d) :
    z ≤ polynomialAbsorptionBound a b c d := by
  have hcne : c ≠ 0 := ne_of_gt hc
  set Z : Real := max 1 (max (4 * a / c) (max (4 * b / c) (4 * d / c))) with hZdef
  have hZ1 : (1 : Real) ≤ Z := le_max_left _ _
  have hZa : 4 * a / c ≤ Z := le_trans (le_max_left _ _) (le_max_right _ _)
  have hZb : 4 * b / c ≤ Z :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hZd : 4 * d / c ≤ Z :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have ha' : 4 * a ≤ Z * c := by
    have h1 : 4 * a / c * c ≤ Z * c := mul_le_mul_of_nonneg_right hZa hc.le
    rwa [div_mul_cancel₀ (4 * a) hcne] at h1
  have hb' : 4 * b ≤ Z * c := by
    have h1 : 4 * b / c * c ≤ Z * c := mul_le_mul_of_nonneg_right hZb hc.le
    rwa [div_mul_cancel₀ (4 * b) hcne] at h1
  have hd' : 4 * d ≤ Z * c := by
    have h1 : 4 * d / c * c ≤ Z * c := mul_le_mul_of_nonneg_right hZd hc.le
    rwa [div_mul_cancel₀ (4 * d) hcne] at h1
  have hgoal : z ≤ Z ^ 2 := by
    by_contra hcon
    push Not at hcon
    set s : Real := Real.sqrt z with hsdef
    have hs0 : 0 ≤ s := Real.sqrt_nonneg z
    have hs2 : s ^ 2 = z := Real.sq_sqrt hz
    have hpow : z ^ ((3 : Real) / 2) = s ^ 3 := by
      have h1 : z = s ^ (2 : Nat) := hs2.symm
      rw [h1, ← Real.rpow_natCast s 2, ← Real.rpow_mul hs0]
      norm_num
    have hZlt : Z ^ 2 < s ^ 2 := by rw [hs2]; exact hcon
    have hsZ : Z < s := by
      by_contra hcon2
      push Not at hcon2
      have hsq : s * s ≤ Z * Z := mul_self_le_mul_self hs0 hcon2
      nlinarith
    have hs1 : (1 : Real) ≤ s := le_trans hZ1 hsZ.le
    have hspos : (0 : Real) < s := lt_of_lt_of_le one_pos hs1
    have hsm1 : (0 : Real) ≤ s - 1 := sub_nonneg.mpr hs1
    have h12 : s ≤ s ^ 2 := by nlinarith [mul_nonneg hspos.le hsm1]
    have h23 : s ^ 2 ≤ s ^ 3 := by nlinarith [mul_nonneg (mul_nonneg hspos.le hspos.le) hsm1]
    have h34 : s ^ 3 ≤ s ^ 4 := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hspos.le hspos.le) hspos.le) hsm1]
    have hs4 : (1 : Real) ≤ s ^ 4 := by linarith
    have hs2nn : (0 : Real) ≤ s ^ 2 := sq_nonneg s
    have hs3nn : (0 : Real) ≤ s ^ 3 := le_trans hs2nn h23
    have hZs : Z * c ≤ s * c := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsZ.le) hc.le]
    have ha2 : a ≤ c * s / 4 := by linarith
    have hb2 : b ≤ c * s / 4 := by linarith
    have hd2 : d ≤ c * s / 4 := by linarith
    have e1 : a * s ^ 3 ≤ c / 4 * s ^ 4 := by
      linarith [mul_le_mul_of_nonneg_right ha2 hs3nn]
    have e2 : b * s ^ 2 ≤ c / 4 * s ^ 4 := by
      linarith [mul_le_mul_of_nonneg_right hb2 hs2nn,
        mul_nonneg hc.le (sub_nonneg.mpr h34)]
    have e3 : d ≤ c / 4 * s ^ 4 := by
      linarith [mul_nonneg hc.le
        (sub_nonneg.mpr (le_trans (le_trans h12 h23) h34))]
    have hineq' : c * s ^ 4 ≤ a * s ^ 3 + b * s ^ 2 + d := by
      have ea : c * s ^ 4 = c * z ^ 2 := by rw [← hs2]; ring
      have eb : b * s ^ 2 = b * z := by rw [hs2]
      rw [ea, eb, ← hpow]
      exact hineq
    linarith [hineq', e1, e2, e3,
      mul_pos hc (lt_of_lt_of_le zero_lt_one hs4)]
  calc z ≤ Z ^ 2 := hgoal
    _ = polynomialAbsorptionBound a b c d := by rw [hZdef, polynomialAbsorptionBound]

def bernsteinMaximumBound (c C eps T : Real) : Real :=
  polynomialAbsorptionBound 0 (3 * eps * T) c C

theorem one_le_bernsteinMaximumBound (c C eps T : Real) :
    1 ≤ bernsteinMaximumBound c C eps T :=
  one_le_polynomialAbsorptionBound _ _ _ _

variable [I.Boundaryless]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]

theorem bernstein_maximum_of_fixed_cutoff
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {T eps c C : Real}
    (cut : ShiFixedCutoff (I := I) G T eps)
    (F : Real → M → Real)
    (hT : 0 < T) (hc : 0 < c) (hC : 0 ≤ C)
    (hF_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ F t x)
    (hF_init : ∀ x : M, F 0 x = 0)
    (hF_cont : ContinuousOn (fun p : Real × M => F p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hF_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => F s x) (Set.Icc 0 T) t)
    (hF_space : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (F t) x)
    (hF_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (F t) y) x)
    (hF_evol : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M, 0 < cut.chi t x →
      parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y)) F t x ≤
        -(c / t) * F t x ^ 2 + C / t) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      cut.chi t x * F t x ≤ bernsteinMaximumBound c C eps T := by
  classical
  have hZ1 : (1 : Real) ≤ bernsteinMaximumBound c C eps T :=
    one_le_bernsteinMaximumBound c C eps T
  have hZ0 : (0 : Real) ≤ bernsteinMaximumBound c C eps T := le_trans zero_le_one hZ1
  have heps : 0 ≤ eps := cut.err_nonneg
  by_cases hsupp : (cut.support).Nonempty
  · obtain ⟨x1, hx1⟩ := hsupp
    have hcompact : IsCompact (Set.Icc 0 T ×ˢ cut.support) :=
      isCompact_Icc.prod cut.support_compact
    have hne : (Set.Icc 0 T ×ˢ cut.support).Nonempty :=
      ⟨(0, x1), ⟨⟨le_rfl, hT.le⟩, hx1⟩⟩
    have hcont : ContinuousOn (fun p : Real × M => cut.chi p.1 p.2 * F p.1 p.2)
        (Set.Icc 0 T ×ˢ cut.support) :=
      cut.joint_cont.mul (hF_cont.mono (fun p hp => ⟨hp.1, Set.mem_univ _⟩))
    obtain ⟨⟨t0, x0⟩, hp0mem, hp0max⟩ := hcompact.exists_isMaxOn hne hcont
    have ht0 : t0 ∈ Set.Icc 0 T := hp0mem.1
    have hmaxset : ∀ p ∈ Set.Icc 0 T ×ˢ cut.support,
        cut.chi p.1 p.2 * F p.1 p.2 ≤ cut.chi t0 x0 * F t0 x0 :=
      fun p hp => hp0max hp
    have hkey : cut.chi t0 x0 * F t0 x0 ≤ bernsteinMaximumBound c C eps T := by
      by_contra hbad
      push Not at hbad
      have hupos : 0 < cut.chi t0 x0 * F t0 x0 := lt_of_lt_of_le
        (lt_of_lt_of_le zero_lt_one hZ1) hbad.le
      have hchi_range := cut.range t0 ht0 x0
      have hfnn : 0 ≤ F t0 x0 := hF_nonneg t0 ht0 x0
      have hchipos : 0 < cut.chi t0 x0 := by
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
      have hmax_slab : ∀ p : Real × M, p ∈ spacetimeSlab (M := M) T →
          cut.chi p.1 p.2 * F p.1 p.2 ≤ cut.chi t0 x0 * F t0 x0 := by
        intro p hp
        by_cases hps : p.2 ∈ cut.support
        · exact hmaxset p ⟨hp.1, hps⟩
        · rw [cut.support_zero p.1 hp.1 p.2 hps, zero_mul]
          exact hupos.le
      obtain ⟨low⟩ := cut.lower_support t0 ht0 ht0pos x0 hchipos
      have hPhi_max : ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t0, x0),
          low.phi p.1 p.2 * F p.1 p.2 ≤ low.phi t0 x0 * F t0 x0 := by
        filter_upwards [low.lower_nhds, self_mem_nhdsWithin] with p hp hpslab
        have h1 : low.phi p.1 p.2 * F p.1 p.2 ≤ cut.chi p.1 p.2 * F p.1 p.2 :=
          mul_le_mul_of_nonneg_right hp.2 (hF_nonneg p.1 hpslab.1 p.2)
        have h2 := hmax_slab p hpslab
        rw [low.eq_at]
        linarith
      have htend_time : Filter.Tendsto (fun s : Real => (s, x0))
          (𝓝[Set.Icc 0 T] t0) (𝓝[spacetimeSlab (M := M) T] (t0, x0)) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · have hcontmap : Continuous (fun s : Real => (s, x0)) :=
            continuous_id.prodMk continuous_const
          exact (hcontmap.tendsto t0).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          exact ⟨hs, Set.mem_univ x0⟩
      have htend_space : Filter.Tendsto (fun y : M => (t0, y))
          (𝓝 x0) (𝓝[spacetimeSlab (M := M) T] (t0, x0)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨(continuous_const.prodMk continuous_id).tendsto x0, ?_⟩
        exact Filter.Eventually.of_forall fun y => ⟨ht0, Set.mem_univ y⟩
      have htime_max : IsLocalMaxOn (fun s : Real => low.phi s x0 * F s x0)
          (Set.Icc 0 T) t0 := htend_time.eventually hPhi_max
      have hspace_max : IsLocalMax (fun y : M => low.phi t0 y * F t0 y) x0 :=
        htend_space.eventually hPhi_max
      have hF_sp : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (F t0) y :=
        fun y => hF_space t0 ht0 ht0pos y
      have hphi_sp : ∀ᶠ y in 𝓝 x0,
          MDifferentiableAt I 𝓘(Real, Real) (low.phi t0) y := low.space_diff_nhds
      have hprod_sp : ∀ᶠ y in 𝓝 x0, MDifferentiableAt I 𝓘(Real, Real)
          (fun z : M => low.phi t0 z * F t0 z) y := by
        filter_upwards [hphi_sp] with y hy
        exact hy.mul (hF_sp y)
      have hprod_grad : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
          gradientFun (I := I) (G.metric t0)
            (fun y : M => low.phi t0 y * F t0 y) z) x0 := by
        have heq : (fun z : M => gradientFun (I := I) (G.metric t0)
              (fun y : M => low.phi t0 y * F t0 y) z) =ᶠ[𝓝 x0]
            (fun z : M => low.phi t0 z •
                gradientFun (I := I) (G.metric t0) (F t0) z +
              F t0 z • gradientFun (I := I) (G.metric t0) (low.phi t0) z) := by
          filter_upwards [hphi_sp] with z hz
          exact gradientFun_mul (I := I) (G.metric t0) hz (hF_sp z)
        have hsum : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
            low.phi t0 z • gradientFun (I := I) (G.metric t0) (F t0) z +
              F t0 z • gradientFun (I := I) (G.metric t0) (low.phi t0) z) x0 :=
          mdifferentiableAt_add_section
            (hphi_sp.self_of_nhds.smul_section (hF_grad t0 ht0 ht0pos x0))
            ((hF_sp x0).smul_section low.grad_diff)
        refine hsum.congr_of_eventuallyEq ?_
        filter_upwards [heq] with z hz
        exact congrArg (fun q =>
          (⟨z, q⟩ : TotalSpace E (TangentSpace I : M → Type _))) hz
      have hlap_nonpos : laplacianAt (I := I) G t0
          (fun y : M => low.phi t0 y * F t0 y) x0 ≤ 0 :=
        laplacianAt_nonpos_at_spatial_max_of_isInteriorPoint (I := I) G t0
          hspace_max BoundarylessManifold.isInteriorPoint
          hprod_sp.self_of_nhds hprod_sp hprod_grad
      have hgrad_zero : gradientFun (I := I) (G.metric t0)
          (fun y : M => low.phi t0 y * F t0 y) x0 = 0 := by
        have hneg : gradientFun (I := I) (G.metric t0)
            (fun y : M => -(low.phi t0 y * F t0 y)) x0 = 0 :=
          gradientFun_eq_zero_at_spatial_min (I := I) (G.metric t0)
            hspace_max.neg hprod_sp.self_of_nhds.neg
        have hrw : gradientFun (I := I) (G.metric t0)
            (fun y : M => -(low.phi t0 y * F t0 y)) x0 =
            -gradientFun (I := I) (G.metric t0)
              (fun y : M => low.phi t0 y * F t0 y) x0 :=
          gradientFun_neg (I := I) (G.metric t0) hprod_sp.self_of_nhds
        rw [hrw] at hneg
        exact neg_eq_zero.mp hneg
      have htime_diff : DifferentiableWithinAt Real
          (fun s : Real => low.phi s x0 * F s x0) (Set.Icc 0 T) t0 :=
        low.time_diff.mul (hF_time t0 ht0 ht0pos x0)
      have hderiv_nonneg : 0 ≤ derivWithin
          (fun s : Real => low.phi s x0 * F s x0) (Set.Icc 0 T) t0 :=
        derivWithin_nonneg_at_Icc_max_of_pos htime_max ht0 ht0pos
      have hpara_nonneg : 0 ≤ parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y))
          (fun s y => low.phi s y * F s y) t0 x0 := by
        have hheat : heatOperatorWithDrift (I := I) G t0
            (fun y : M => (0 : TangentSpace I y))
            (fun y : M => low.phi t0 y * F t0 y) x0 =
              laplacianAt (I := I) G t0
                (fun y : M => low.phi t0 y * F t0 y) x0 := by
          unfold heatOperatorWithDrift
          rw [driftTerm_zero_drift]
          ring
        rw [parabolicOperatorWithDrift_eq, hheat]
        linarith
      have hprod_rule := parabolic_mul_nhds (I := I) (G := G) T
        (fun _ y => (0 : TangentSpace I y)) low.phi F t0 x0
        low.time_diff (hF_time t0 ht0 ht0pos x0)
        hphi_sp (Filter.Eventually.of_forall hF_sp)
        low.grad_diff (hF_grad t0 ht0 ht0pos x0)
      rw [hprod_rule] at hpara_nonneg
      simp only [gradientAt_eq] at hpara_nonneg
      have hpF : low.phi t0 x0 • gradientFun (I := I) (G.metric t0) (F t0) x0 =
          -(F t0 x0 • gradientFun (I := I) (G.metric t0) (low.phi t0) x0) := by
        rw [eq_neg_iff_add_eq_zero, ← gradientFun_mul (I := I) (G.metric t0)
          hphi_sp.self_of_nhds (hF_sp x0)]
        exact hgrad_zero
      have hinner_eq : low.phi t0 x0 * (G.metric t0).inner x0
            (gradientFun (I := I) (G.metric t0) (low.phi t0) x0)
            (gradientFun (I := I) (G.metric t0) (F t0) x0) =
          -(F t0 x0 * (G.metric t0).inner x0
            (gradientFun (I := I) (G.metric t0) (low.phi t0) x0)
            (gradientFun (I := I) (G.metric t0) (low.phi t0) x0)) := by
        calc low.phi t0 x0 * (G.metric t0).inner x0
                (gradientFun (I := I) (G.metric t0) (low.phi t0) x0)
                (gradientFun (I := I) (G.metric t0) (F t0) x0)
            = ((G.metric t0).inner x0
                (gradientFun (I := I) (G.metric t0) (low.phi t0) x0))
                (low.phi t0 x0 •
                  gradientFun (I := I) (G.metric t0) (F t0) x0) := by
              rw [map_smul]
              simp
          _ = ((G.metric t0).inner x0
                (gradientFun (I := I) (G.metric t0) (low.phi t0) x0))
                (-(F t0 x0 •
                  gradientFun (I := I) (G.metric t0) (low.phi t0) x0)) := by
              rw [hpF]
          _ = -(F t0 x0 * (G.metric t0).inner x0
                (gradientFun (I := I) (G.metric t0) (low.phi t0) x0)
                (gradientFun (I := I) (G.metric t0) (low.phi t0) x0)) := by
              rw [map_neg, map_smul]
              simp
      have ht0ne : t0 ≠ 0 := ne_of_gt ht0pos
      have hPF' : t0 * parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y)) F t0 x0 ≤
            -(c * F t0 x0 ^ 2) + C := by
        have h := mul_le_mul_of_nonneg_left
          (hF_evol t0 ht0 ht0pos x0 hchipos) ht0pos.le
        have e1 : t0 * (-(c / t0) * F t0 x0 ^ 2 + C / t0) =
            -(c * F t0 x0 ^ 2) + C := by
          field_simp
        rw [e1] at h
        exact h
      have hz0 : 0 ≤ cut.chi t0 x0 * F t0 x0 := hupos.le
      have hp2 : cut.chi t0 x0 ^ 2 ≤ 1 := by nlinarith [hchi_range.1, hchi_range.2]
      have hphi_eq : low.phi t0 x0 = cut.chi t0 x0 := low.eq_at
      rw [hphi_eq] at hpara_nonneg hinner_eq hpF
      have hmul : 0 ≤ cut.chi t0 x0 ^ 2 * parabolicOperatorWithDrift (I := I) G T
            (fun _ y => (0 : TangentSpace I y)) F t0 x0 +
          cut.chi t0 x0 * F t0 x0 * parabolicOperatorWithDrift (I := I) G T
            (fun _ y => (0 : TangentSpace I y)) low.phi t0 x0 +
          2 * (F t0 x0 * (G.metric t0).inner x0
            (gradientFun (I := I) (G.metric t0) (low.phi t0) x0)
            (gradientFun (I := I) (G.metric t0) (low.phi t0) x0)) := by
        nlinarith [mul_nonneg hchipos.le hpara_nonneg, hinner_eq]
      have hgradsq : (G.metric t0).inner x0
          (gradientFun (I := I) (G.metric t0) (low.phi t0) x0)
          (gradientFun (I := I) (G.metric t0) (low.phi t0) x0) ≤
            eps * cut.chi t0 x0 := by
        have h := low.grad_sq_le
        rw [hphi_eq] at h
        exact h
      have t1 : cut.chi t0 x0 ^ 2 * (t0 * parabolicOperatorWithDrift (I := I) G T
            (fun _ y => (0 : TangentSpace I y)) F t0 x0) ≤
          cut.chi t0 x0 ^ 2 * (-(c * F t0 x0 ^ 2) + C) :=
        mul_le_mul_of_nonneg_left hPF' (sq_nonneg _)
      have t2 : (t0 * (cut.chi t0 x0 * F t0 x0)) *
            parabolicOperatorWithDrift (I := I) G T
              (fun _ y => (0 : TangentSpace I y)) low.phi t0 x0 ≤
          (t0 * (cut.chi t0 x0 * F t0 x0)) * eps :=
        mul_le_mul_of_nonneg_left low.parabolic_le (mul_nonneg ht0pos.le hz0)
      have t3 : (2 * (t0 * F t0 x0)) * (G.metric t0).inner x0
            (gradientFun (I := I) (G.metric t0) (low.phi t0) x0)
            (gradientFun (I := I) (G.metric t0) (low.phi t0) x0) ≤
          (2 * (t0 * F t0 x0)) * (eps * cut.chi t0 x0) :=
        mul_le_mul_of_nonneg_left hgradsq
          (by positivity)
      have t4 : 0 ≤ t0 * (cut.chi t0 x0 ^ 2 * parabolicOperatorWithDrift (I := I) G T
            (fun _ y => (0 : TangentSpace I y)) F t0 x0 +
          cut.chi t0 x0 * F t0 x0 * parabolicOperatorWithDrift (I := I) G T
            (fun _ y => (0 : TangentSpace I y)) low.phi t0 x0 +
          2 * (F t0 x0 * (G.metric t0).inner x0
            (gradientFun (I := I) (G.metric t0) (low.phi t0) x0)
            (gradientFun (I := I) (G.metric t0) (low.phi t0) x0))) :=
        mul_nonneg ht0pos.le hmul
      have hquad : c * (cut.chi t0 x0 * F t0 x0) ^ 2 ≤
          0 * (cut.chi t0 x0 * F t0 x0) ^ ((3 : Real) / 2) +
            (3 * eps * T) * (cut.chi t0 x0 * F t0 x0) + C := by
        rw [zero_mul, zero_add]
        nlinarith [t1, t2, t3, t4,
          mul_nonneg hC (sub_nonneg.mpr hp2),
          mul_nonneg (mul_nonneg heps (sub_nonneg.mpr ht0.2)) hz0]
      have habsorb := polynomial_absorption (a := 0) (b := 3 * eps * T)
        (c := c) (d := C) (z := cut.chi t0 x0 * F t0 x0) hz0 hc hquad
      rw [bernsteinMaximumBound] at hbad
      exact absurd habsorb (not_le.mpr hbad)
    intro t ht x
    by_cases hx : x ∈ cut.support
    · exact le_trans (hmaxset (t, x) ⟨ht, hx⟩) hkey
    · rw [cut.support_zero t ht x hx, zero_mul]
      exact hZ0
  · intro t ht x
    have hx : x ∉ cut.support := by
      rw [Set.not_nonempty_iff_eq_empty] at hsupp
      simp [hsupp]
    rw [cut.support_zero t ht x hx, zero_mul]
    exact hZ0

theorem bernstein_maximum_sq_of_fixed_cutoff
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {T eps c C : Real}
    (cut : ShiFixedCutoff (I := I) G T eps)
    (F : Real → M → Real)
    (hT : 0 < T) (hc : 0 < c) (hC : 0 ≤ C)
    (hF_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ F t x)
    (hF_init : ∀ x : M, F 0 x = 0)
    (hF_cont : ContinuousOn (fun p : Real × M => F p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hF_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => F s x) (Set.Icc 0 T) t)
    (hF_space : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (F t) x)
    (hF_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (F t) y) x)
    (hF_evol : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M, 0 < cut.chi t x →
      parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y)) F t x ≤
        -(c / t) * F t x ^ 2 + C / t) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      cut.chi t x ^ 2 * F t x ≤ bernsteinMaximumBound c C eps T := by
  intro t ht x
  have hbase := bernstein_maximum_of_fixed_cutoff (I := I) cut F hT hc hC
    hF_nonneg hF_init hF_cont hF_time hF_space hF_grad hF_evol t ht x
  have hrange := cut.range t ht x
  have hFnn := hF_nonneg t ht x
  have hstep : cut.chi t x ^ 2 * F t x ≤ cut.chi t x * F t x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrange.2) (mul_nonneg hrange.1 hFnn)]
  linarith

end DifferentialGeometry.PDE.RicciFlow
