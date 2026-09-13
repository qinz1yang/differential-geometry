import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.SourceGaussian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortTime.ReducedJacobianLimit
import DifferentialGeometry.Analysis.Calculus.Derivative.IntervalConstancy
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem continuousOn_lReducedJacobian
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau) :
    ContinuousOn (fun Z : E => lReducedJacobian S T x Z tau)
      (lInjDomain S T x tau) := by
  let U : Set E := lInjDomain S T x tau
  let Ψ := lExpPartial S hS T x tau htau
  have hsource : Ψ.source = U :=
    lExpPartial_source S hS T x tau htau
  have hden : ContinuousOn (fun Z : E => lExpDensity S T x Z tau) U := by
    have hpd : ContinuousOn
        (paramDensity (S.base.metric (T - tau)) Ψ) U := by
      simpa only [hsource] using
        (paramDensity_contOn (I := I) (S.base.metric (T - tau)) Ψ)
    apply hpd.congr
    intro Z hZ
    exact (lExpPartial_density S hS T x tau htau hZ).symm
  have hred : ContinuousOn
      (fun Z : E => redDensity S T x (lExp S T x Z tau) tau) U := by
    have hΨ : ContinuousOn (Ψ : E → M) U := by
      simpa only [← hsource] using Ψ.contMDiffOn_toFun.continuousOn
    have hl : ContinuousOn
        (fun Z : E => redLength S T x (Ψ Z) tau) U := by
      intro Z hZ
      have hZ' : Z ∈ lInjDomain (E := E) (I := I) S T x tau := hZ
      obtain ⟨V, hVopen, hΨV, hsmooth⟩ :=
        redLength_smooth S hS T x htau hZ'
      have hΨeq : Ψ Z = lExp S T x Z tau :=
        lExpPartial_apply S hS T x tau htau hZ'
      rw [← hΨeq] at hΨV
      exact (hsmooth.continuousOn.continuousAt
        (hVopen.mem_nhds hΨV)).comp_continuousWithinAt
        (hΨ Z hZ)
    have hcore : ContinuousOn
        (fun Z : E =>
          -redLength S T x (Ψ Z) tau -
            ((Module.finrank Real E : Real) / 2) * Real.log tau -
            ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi)) U :=
      (hl.neg.sub continuousOn_const).sub continuousOn_const
    have hexp : ContinuousOn
        (fun Z : E => redDensity S T x (Ψ Z) tau) U := by
      change ContinuousOn
        (Real.exp ∘ fun Z : E =>
          -redLength S T x (Ψ Z) tau -
            ((Module.finrank Real E : Real) / 2) * Real.log tau -
            ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi)) U
      exact Real.continuous_exp.comp_continuousOn hcore
    apply hexp.congr
    intro Z hZ
    dsimp only [Ψ]
    rw [lExpPartial_apply S hS T x tau htau hZ]
  let F : E -> Real := fun Z => lReducedJacobian S T x Z tau
  have hprod : ContinuousOn (fun Z : E => F Z * lSourceDensity S T x) U :=
    (hden.mul hred).congr fun Z hZ =>
      lReducedJacobian_mul_source S hS T x htau hZ
  refine (hprod.div_const (lSourceDensity S T x)).congr fun Z hZ => ?_
  simp only [mul_div_assoc, div_self (lSourceDensity_pos S T x).ne', mul_one]
  rfl

theorem aemeasurable_ofReal_lReducedJacobian_mul_source
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau) :
    AEMeasurable
      (fun Z : E =>
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x))
      ((modelHaar (E := E)).restrict (lInjDomain S T x tau)) := by
  have hcont : ContinuousOn
      (fun Z : E => lReducedJacobian S T x Z tau * lSourceDensity S T x)
      (lInjDomain S T x tau) :=
    (continuousOn_lReducedJacobian S hS T x tau htau).mul continuousOn_const
  have hmeas : AEMeasurable
      (fun Z : E => lReducedJacobian S T x Z tau * lSourceDensity S T x)
      ((modelHaar (E := E)).restrict (lInjDomain S T x tau)) :=
    hcont.aemeasurable (lInj_isOpen S hS T x tau).measurableSet
  exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable hmeas

theorem lReducedJacobian_deriv_eq_zero_iff_lRedLog_deriv_eq_zero
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    deriv (lReducedJacobian S T x Z) tau = 0 ↔ deriv (lRedLog S T x Z) tau = 0 := by
  rw [(lReducedJacobian_hasDeriv S hS T x htau hZ).deriv,
    (lRedLog_hasDeriv S hS T x htau hZ).deriv]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (Real.exp_ne_zero _)
  · intro h
    rw [h, mul_zero]

theorem lReducedJacobian_deriv_eq_zero_iff_laplacian_add_scalar_eq
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    deriv (lReducedJacobian S T x Z) tau = 0 ↔
      laplacian (I := I) (LeviCivita (I := I) (S.base.metric (T - tau)))
          (S.base.metric (T - tau))
          (fun y : M => redLength S T x y tau) (lExp S T x Z tau) +
        S.scalar (T - tau) (lExp S T x Z tau) +
        lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
          (2 * tau * Real.sqrt tau) -
        (Module.finrank Real E : Real) / (2 * tau) = 0 := by
  rw [lReducedJacobian_deriv_eq_zero_iff_lRedLog_deriv_eq_zero S hS T x htau hZ,
    (lRedLog_hasDeriv S hS T x htau hZ).deriv]

theorem lReducedJacobian_eq_on_Icc_of_deriv_eq_zero
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {a b : Real}
    (ha : 0 < a) (hab : a ≤ b)
    (hZb : Z ∈ lInjDomain S T x b)
    (hzero : ∀ tau ∈ Set.Ioo a b,
      deriv (lReducedJacobian S T x Z) tau = 0) :
    ∀ tau ∈ Set.Icc a b,
      lReducedJacobian S T x Z tau = lReducedJacobian S T x Z a := by
  have hmem : ∀ tau ∈ Set.Icc a b, Z ∈ lInjDomain S T x tau := by
    intro tau htau
    obtain ⟨sigma, hsigma, hmin⟩ := hZb
    exact ⟨sigma, lt_of_le_of_lt htau.2 hsigma, hmin⟩
  have hcont : ContinuousOn (lReducedJacobian S T x Z) (Set.Icc a b) := by
    intro tau htau
    exact (lReducedJacobian_hasDeriv S hS T x (ha.trans_le htau.1)
      (hmem tau htau)).continuousAt.continuousWithinAt
  have hgeom : ∀ tau ∈ Set.Ioo a b,
      HasDerivAt (lReducedJacobian S T x Z) 0 tau := by
    intro tau htau
    have htauI : tau ∈ Set.Icc a b := Set.Ioo_subset_Icc_self htau
    have h := (lReducedJacobian_hasDeriv S hS T x (ha.trans_le htauI.1)
      (hmem tau htauI)).differentiableAt.hasDerivAt
    rwa [hzero tau htau] at h
  exact DifferentialGeometry.eq_of_hasDerivAt_zero_on_Icc hab hcont hgeom

theorem lReducedJacobian_eq_on_Icc_of_laplacian_add_scalar_eq
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {a b : Real}
    (ha : 0 < a) (hab : a ≤ b)
    (hZb : Z ∈ lInjDomain S T x b)
    (hzero : ∀ tau ∈ Set.Ioo a b,
      laplacian (I := I) (LeviCivita (I := I) (S.base.metric (T - tau)))
          (S.base.metric (T - tau))
          (fun y : M => redLength S T x y tau) (lExp S T x Z tau) +
        S.scalar (T - tau) (lExp S T x Z tau) +
        lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
          (2 * tau * Real.sqrt tau) -
        (Module.finrank Real E : Real) / (2 * tau) = 0) :
    ∀ tau ∈ Set.Icc a b,
      lReducedJacobian S T x Z tau = lReducedJacobian S T x Z a := by
  refine lReducedJacobian_eq_on_Icc_of_deriv_eq_zero S hS T x ha hab hZb ?_
  intro tau htau
  exact (lReducedJacobian_deriv_eq_zero_iff_laplacian_add_scalar_eq S hS T x
    (ha.trans htau.1)
    (by
      obtain ⟨sigma, hsigma, hmin⟩ := hZb
      exact ⟨sigma, lt_of_le_of_lt (Set.Ioo_subset_Icc_self htau).2 hsigma,
        hmin⟩)).mpr (hzero tau htau)

theorem redVolume_ne_top
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {tau : Real} (htau : 0 < tau)
    (hslab : Set.Icc (T - tau) T ⊆ D.regular) :
    redVolume S T x tau ≠ ⊤ := by
  rw [redVolume_lint S hS T x tau htau hslab]
  have hle : (∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂(modelHaar (E := E))) ≤
      ∫⁻ Z : E, ENNReal.ofReal (lSourceGaussian S T x Z)
        ∂(modelHaar (E := E)) := by
    calc
      (∫⁻ Z in lInjDomain S T x tau,
          ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
          ∂(modelHaar (E := E))) ≤
          ∫⁻ Z in lInjDomain S T x tau,
            ENNReal.ofReal (lSourceGaussian S T x Z)
            ∂(modelHaar (E := E)) := by
        refine MeasureTheory.setLIntegral_mono'
          (lInj_isOpen S hS T x tau).measurableSet ?_
        intro Z hZ
        rw [lSourceGaussian_eq_metric_norm]
        exact ENNReal.ofReal_le_ofReal
          (calc
            lReducedJacobian S T x Z tau * lSourceDensity S T x
                ≤ ((Real.pi ^
                      ((Module.finrank Real E : Real) / 2))⁻¹ *
                    Real.exp (-(((S.base.metric T).inner x) Z) Z)) *
                  lSourceDensity S T x :=
                mul_le_mul_of_nonneg_right
                  (lReducedJacobian_le_gaussian S hS T x htau hZ)
                  (lSourceDensity_pos S T x).le
            _ = (Real.pi ^
                    ((Module.finrank Real E : Real) / 2))⁻¹ *
                  lSourceDensity S T x *
                  Real.exp (-(((S.base.metric T).inner x) Z) Z) := by
                ring)
      _ ≤ ∫⁻ Z : E, ENNReal.ofReal (lSourceGaussian S T x Z)
            ∂(modelHaar (E := E)) :=
        by
          simpa only [Measure.restrict_univ] using
            MeasureTheory.lintegral_mono_set
              (Set.subset_univ (lInjDomain S T x tau))
  rw [lSourceGaussian_mass S T x] at hle
  exact fun htop => ENNReal.one_ne_top (top_unique (htop ▸ hle))

private theorem ae_lReducedJacobian_eq_of_redVolume_eq_pair
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (hslab : Set.Icc (T - b) T ⊆ D.regular)
    (hconst : redVolume S T x b = redVolume S T x a) :
    ∀ᵐ (Z : E) ∂((modelHaar (E := E)).restrict (lInjDomain S T x b)),
      lReducedJacobian S T x Z b = lReducedJacobian S T x Z a := by
  have hbpos : 0 < b := ha.trans_le hab
  have hslab_a : Set.Icc (T - a) T ⊆ D.regular := fun r hr =>
    hslab ⟨(sub_le_sub_left hab T).trans hr.1, hr.2⟩
  have hsub : lInjDomain S T x b ⊆ lInjDomain S T x a := by
    rintro Z ⟨s, hs, hmin⟩
    exact ⟨s, lt_of_le_of_lt hab hs, hmin⟩
  have hUbm : MeasurableSet (lInjDomain S T x b) :=
    (lInj_isOpen S hS T x b).measurableSet
  have hpt : ∀ Z ∈ lInjDomain S T x b,
      ENNReal.ofReal (lReducedJacobian S T x Z b * lSourceDensity S T x) ≤
        ENNReal.ofReal (lReducedJacobian S T x Z a * lSourceDensity S T x) :=
    fun Z hZ =>
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (lReducedJacobian_anti S hS T x ha hab hZ) (lSourceDensity_pos S T x).le)
  have h1 : (∫⁻ Z in lInjDomain S T x b,
        ENNReal.ofReal (lReducedJacobian S T x Z b * lSourceDensity S T x)
        ∂(modelHaar (E := E))) ≤
      ∫⁻ Z in lInjDomain S T x b,
        ENNReal.ofReal (lReducedJacobian S T x Z a * lSourceDensity S T x)
        ∂(modelHaar (E := E)) :=
    MeasureTheory.setLIntegral_mono' hUbm hpt
  have h2 : (∫⁻ Z in lInjDomain S T x b,
        ENNReal.ofReal (lReducedJacobian S T x Z a * lSourceDensity S T x)
        ∂(modelHaar (E := E))) ≤
      ∫⁻ Z in lInjDomain S T x a,
        ENNReal.ofReal (lReducedJacobian S T x Z a * lSourceDensity S T x)
        ∂(modelHaar (E := E)) :=
    MeasureTheory.lintegral_mono_set hsub
  have heq : (∫⁻ Z in lInjDomain S T x b,
        ENNReal.ofReal (lReducedJacobian S T x Z a * lSourceDensity S T x)
        ∂(modelHaar (E := E))) =
      ∫⁻ Z in lInjDomain S T x b,
        ENNReal.ofReal (lReducedJacobian S T x Z b * lSourceDensity S T x)
        ∂(modelHaar (E := E)) := by
    refine le_antisymm ?_ h1
    calc
      (∫⁻ Z in lInjDomain S T x b,
          ENNReal.ofReal (lReducedJacobian S T x Z a * lSourceDensity S T x)
          ∂(modelHaar (E := E))) ≤
          ∫⁻ Z in lInjDomain S T x a,
            ENNReal.ofReal (lReducedJacobian S T x Z a * lSourceDensity S T x)
            ∂(modelHaar (E := E)) := h2
      _ = redVolume S T x a :=
        (redVolume_lint S hS T x a ha hslab_a).symm
      _ = redVolume S T x b := hconst.symm
      _ = ∫⁻ Z in lInjDomain S T x b,
            ENNReal.ofReal (lReducedJacobian S T x Z b * lSourceDensity S T x)
            ∂(modelHaar (E := E)) :=
        redVolume_lint S hS T x b hbpos hslab
  have hfin : (∫⁻ Z in lInjDomain S T x b,
      ENNReal.ofReal (lReducedJacobian S T x Z b * lSourceDensity S T x)
      ∂(modelHaar (E := E))) ≠ ⊤ := by
    rw [← redVolume_lint S hS T x b hbpos hslab]
    exact redVolume_ne_top S hS T x hbpos hslab
  have hfg : (fun Z : E =>
        ENNReal.ofReal (lReducedJacobian S T x Z b * lSourceDensity S T x))
      ≤ᵐ[(modelHaar (E := E)).restrict (lInjDomain S T x b)]
      fun Z : E =>
        ENNReal.ofReal (lReducedJacobian S T x Z a * lSourceDensity S T x) :=
    (MeasureTheory.ae_restrict_iff' hUbm).mpr
      (Filter.Eventually.of_forall fun Z hZ => hpt Z hZ)
  have hmeas : AEMeasurable
      (fun Z : E =>
        ENNReal.ofReal (lReducedJacobian S T x Z a * lSourceDensity S T x))
      ((modelHaar (E := E)).restrict (lInjDomain S T x b)) := by
    have hcont : ContinuousOn
        (fun Z : E => lReducedJacobian S T x Z a * lSourceDensity S T x)
        (lInjDomain S T x b) :=
      ((continuousOn_lReducedJacobian S hS T x a ha).mono hsub).mul
        continuousOn_const
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (hcont.aemeasurable hUbm)
  have hae := MeasureTheory.ae_eq_of_ae_le_of_lintegral_le hfg hfin hmeas heq.le
  filter_upwards [hae] with Z hZ
  have hb0 : 0 ≤ lReducedJacobian S T x Z b * lSourceDensity S T x :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (lSourceDensity_pos S T x).le
  have ha0 : 0 ≤ lReducedJacobian S T x Z a * lSourceDensity S T x :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (lSourceDensity_pos S T x).le
  exact (mul_right_cancel₀ (lSourceDensity_pos S T x).ne'
    ((ENNReal.ofReal_eq_ofReal_iff hb0 ha0).mp hZ))

theorem ae_lReducedJacobian_eq_on_Icc_of_redVolume_eq
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (hslab : Set.Icc (T - b) T ⊆ D.regular)
    (hconst : ∀ tau ∈ Set.Icc a b, redVolume S T x tau = redVolume S T x b) :
    ∀ᵐ (Z : E) ∂((modelHaar (E := E)).restrict (lInjDomain S T x b)),
      ∀ tau ∈ Set.Icc a b,
        lReducedJacobian S T x Z tau = lReducedJacobian S T x Z b := by
  classical
  have hbpos : 0 < b := ha.trans_le hab
  have hUbm : MeasurableSet (lInjDomain S T x b) :=
    (lInj_isOpen S hS T x b).measurableSet
  have hall : ∀ᵐ (Z : E) ∂((modelHaar (E := E)).restrict (lInjDomain S T x b)),
      ∀ q : {q : ℚ // (q : Real) ∈ Set.Icc a b},
        lReducedJacobian S T x Z b =
          lReducedJacobian S T x Z ((q : ℚ) : Real) := by
    rw [MeasureTheory.ae_all_iff]
    rintro ⟨q, hq⟩
    exact ae_lReducedJacobian_eq_of_redVolume_eq_pair (a := ((q : ℚ) : Real))
      S hS T x (ha.trans_le hq.1) hq.2 hslab (hconst q hq).symm
  filter_upwards [hall, MeasureTheory.ae_restrict_mem hUbm] with Z hZ hZb
  intro tau htau
  rcases lt_or_eq_of_le htau.2 with hltb | rfl
  · obtain ⟨u, _hanti, hux, hu⟩ := Real.exists_seq_rat_strictAnti_tendsto tau
    have hmem : Z ∈ lInjDomain S T x tau := by
      obtain ⟨s, hs, hmin⟩ := hZb
      exact ⟨s, lt_of_le_of_lt htau.2 hs, hmin⟩
    have hev : ∀ᶠ n : Nat in Filter.atTop,
        ((u n : ℚ) : Real) ∈ Set.Icc a b := by
      filter_upwards [hu (Iio_mem_nhds hltb)] with n hn
      exact ⟨htau.1.trans (hux n).le, hn.le⟩
    have hcont : Tendsto
        (fun n : Nat => lReducedJacobian S T x Z ((u n : ℚ) : Real))
        Filter.atTop (𝓝 (lReducedJacobian S T x Z tau)) :=
      ((lReducedJacobian_hasDeriv S hS T x (ha.trans_le htau.1)
        hmem).continuousAt).tendsto.comp hu
    have hlim : Tendsto
        (fun n : Nat => lReducedJacobian S T x Z ((u n : ℚ) : Real))
        Filter.atTop (𝓝 (lReducedJacobian S T x Z b)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      exact hZ ⟨u n, hn⟩
    exact tendsto_nhds_unique hcont hlim
  · rfl

theorem ae_deriv_lReducedJacobian_eq_zero_of_redVolume_eq
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (hslab : Set.Icc (T - b) T ⊆ D.regular)
    (hconst : ∀ tau ∈ Set.Icc a b, redVolume S T x tau = redVolume S T x b) :
    ∀ᵐ (Z : E) ∂((modelHaar (E := E)).restrict (lInjDomain S T x b)),
      ∀ tau ∈ Set.Ioo a b,
        deriv (lReducedJacobian S T x Z) tau = 0 := by
  filter_upwards [ae_lReducedJacobian_eq_on_Icc_of_redVolume_eq S hS T x
    ha hab hslab hconst] with Z hZ
  intro tau htau
  have hloc : (fun r : Real => lReducedJacobian S T x Z r) =ᶠ[𝓝 tau]
      fun _ => lReducedJacobian S T x Z b := by
    filter_upwards [isOpen_Ioo.mem_nhds htau] with r hr
    exact hZ r (Set.Ioo_subset_Icc_self hr)
  exact ((hasDerivAt_const tau (lReducedJacobian S T x Z b)).congr_of_eventuallyEq
    hloc).deriv

theorem ae_laplacian_add_scalar_eq_of_redVolume_eq
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (hslab : Set.Icc (T - b) T ⊆ D.regular)
    (hconst : ∀ tau ∈ Set.Icc a b, redVolume S T x tau = redVolume S T x b) :
    ∀ᵐ (Z : E) ∂((modelHaar (E := E)).restrict (lInjDomain S T x b)),
      ∀ tau ∈ Set.Ioo a b,
        laplacian (I := I) (LeviCivita (I := I) (S.base.metric (T - tau)))
            (S.base.metric (T - tau))
            (fun y : M => redLength S T x y tau) (lExp S T x Z tau) +
          S.scalar (T - tau) (lExp S T x Z tau) +
          lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
            (2 * tau * Real.sqrt tau) -
          (Module.finrank Real E : Real) / (2 * tau) = 0 := by
  have hUbm : MeasurableSet (lInjDomain S T x b) :=
    (lInj_isOpen S hS T x b).measurableSet
  filter_upwards [ae_deriv_lReducedJacobian_eq_zero_of_redVolume_eq S hS T x
    ha hab hslab hconst, MeasureTheory.ae_restrict_mem hUbm] with Z hZ hZb
  intro tau htau
  have hmem : Z ∈ lInjDomain S T x tau := by
    obtain ⟨s, hs, hmin⟩ := hZb
    exact ⟨s, lt_of_le_of_lt (Set.Ioo_subset_Icc_self htau).2 hs, hmin⟩
  exact (lReducedJacobian_deriv_eq_zero_iff_laplacian_add_scalar_eq S hS T x
    (ha.trans htau.1) hmem).mp (hZ tau htau)

end DifferentialGeometry.PDE.RicciFlow.Perelman
