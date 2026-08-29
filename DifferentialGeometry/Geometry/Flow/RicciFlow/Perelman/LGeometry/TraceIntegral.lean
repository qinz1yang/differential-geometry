import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.HamiltonH

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section normedSpaceCompatibility

attribute [-instance] InnerProductSpace.toNormedSpace

open Bundle Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open MeasureTheory
open Filter

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

noncomputable def lKTail
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (a b : Real) : Real :=
  2 * ∫ s in a..b, ((s - a) / s) ^ 2 * lHamSq S T alpha s

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
    [I.Boundaryless] [SigmaCompactSpace M] in
theorem lKTail_sq
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (a b : Real) (ha : 0 ≤ a) (hab : a ≤ b) :
    lKTail S T (sqReparam gamma) a b =
      ∫ rho in a ^ 2..b ^ 2,
        Real.sqrt rho * (Real.sqrt rho - a) ^ 2 *
          lHamilton S T rho (gamma rho) (lVelocity (I := I) gamma rho) := by
  let k : Real → Real := fun rho ↦
    Real.sqrt rho * (Real.sqrt rho - a) ^ 2 *
      lHamilton S T rho (gamma rho) (lVelocity (I := I) gamma rho)
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (g := k) (f := fun s : Real ↦ s ^ 2)
      (f' := fun s : Real ↦ 2 * s) (a := a) (b := b)
      (continuous_id.pow 2).continuousOn
      (by
        intro s _hs
        simpa using hasDerivAt_pow 2 s)
      (by
        intro s hs
        rw [min_eq_left hab, max_eq_right hab] at hs
        exact mul_nonneg (by norm_num) (ha.trans (le_of_lt hs.1)))
  have hpoint : ∀ s ∈ Set.uIcc a b,
      2 * (((s - a) / s) ^ 2 * lHamSq S T (sqReparam gamma) s) =
        (k ∘ fun r : Real ↦ r ^ 2) s * (2 * s) := by
    intro s hs
    have hsI : s ∈ Set.Icc a b := by
      simpa only [Set.uIcc_of_le hab] using hs
    have hsnonneg : 0 ≤ s := ha.trans hsI.1
    by_cases hs0 : s = 0
    · subst s
      have ha0 : a = 0 := le_antisymm hsI.1 ha
      subst a
      simp [lHamSq, k]
    · have hspos : 0 < s := lt_of_le_of_ne hsnonneg (Ne.symm hs0)
      rw [lHamSq_eq S T (sqReparam gamma) s
        (lVelocity (I := I) gamma (s ^ 2))
        (lVelocity_sq_pos (I := I) gamma s hspos)]
      simp only [k, Function.comp_apply, sqReparam, Real.sqrt_sq hspos.le]
      field_simp [hs0]
  rw [lKTail, ← intervalIntegral.integral_const_mul]
  calc
    (∫ s in a..b,
        2 * (((s - a) / s) ^ 2 * lHamSq S T (sqReparam gamma) s)) =
        ∫ s in a..b, (k ∘ fun r : Real ↦ r ^ 2) s * (2 * s) := by
      exact intervalIntegral.integral_congr hpoint
    _ = ∫ rho in a ^ 2..b ^ 2, k rho := by
      simpa [k] using hsub

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem lKTail_tendsto
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {b : Real}
    (hb : 0 < b) (hbdom : b ∈ lRegDomain S T x Z) :
    Tendsto
      (fun a ↦ lKTail S T (lRegCurve S T x Z) a b)
      (𝓝[>] 0)
      (𝓝 (lK S T (lRegCurve S T x Z) b)) := by
  let alpha : Real → M := lRegCurve S T x Z
  let H : Real → Real := fun s ↦ lHamSq S T alpha s
  let F : Real → Real → Real := fun a s ↦
    if a < s then ((s - a) / s) ^ 2 * H s else 0
  have hHint : IntervalIntegrable H volume 0 b := by
    simpa only [H, alpha] using lRayHam_int S hS T x Z hb hbdom
  have hFmeas (a : Real) :
      AEStronglyMeasurable (F a) (volume.restrict (Set.uIoc 0 b)) := by
    have hcoef : Measurable (fun s : Real ↦ ((s - a) / s) ^ 2) :=
      ((measurable_id.sub measurable_const).div measurable_id).pow_const 2
    have hprod : AEStronglyMeasurable
        (fun s : Real ↦ ((s - a) / s) ^ 2 * H s)
        (volume.restrict (Set.uIoc 0 b)) :=
      hcoef.aestronglyMeasurable.mul hHint.def'.aestronglyMeasurable
    change AEStronglyMeasurable
      ((Set.Ioi a).indicator (fun s : Real ↦ ((s - a) / s) ^ 2 * H s))
      (volume.restrict (Set.uIoc 0 b))
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi]
    exact hprod.mono_measure Measure.restrict_le_self
  have hFbound {a s : Real} (ha : 0 < a) (hs : s ∈ Set.uIoc 0 b) :
      ‖F a s‖ ≤ |H s| := by
    have hsI : s ∈ Set.Ioc (0 : Real) b := by
      simpa only [Set.uIoc_of_le hb.le] using hs
    simp only [F]
    split_ifs with has
    · have hq0 : 0 ≤ (s - a) / s :=
        div_nonneg (sub_nonneg.mpr has.le) hsI.1.le
      have hq1 : (s - a) / s ≤ 1 :=
        (div_le_one hsI.1).2 (by linarith)
      have hq2 : ((s - a) / s) ^ 2 ≤ 1 :=
        (sq_le_one_iff₀ hq0).2 hq1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hq2 (abs_nonneg (H s))
    · simpa only [norm_zero] using abs_nonneg (H s)
  have hfixed : Tendsto
      (fun a ↦ ∫ s in (0 : Real)..b, F a s)
      (𝓝[>] 0) (𝓝 (∫ s in (0 : Real)..b, H s)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (fun s : Real ↦ |H s|) ?_ ?_ hHint.abs ?_
    · filter_upwards with a
      exact hFmeas a
    · filter_upwards [Ioo_mem_nhdsGT hb] with a ha
      exact ae_of_all _ fun s hs ↦ hFbound ha.1 hs
    · exact ae_of_all _ fun s hs ↦ by
        have hsI : s ∈ Set.Ioc (0 : Real) b := by
          simpa only [Set.uIoc_of_le hb.le] using hs
        have ha0 : Tendsto (fun a : Real ↦ a) (𝓝[>] 0) (𝓝 0) :=
          tendsto_inf_left tendsto_id
        have hcoef : Tendsto (fun a : Real ↦ ((s - a) / s) ^ 2)
            (𝓝[>] 0) (𝓝 1) := by
          simpa only [sub_zero, div_self hsI.1.ne', one_pow] using
            (((tendsto_const_nhds (x := s)).sub ha0).div_const s).pow 2
        have hprod : Tendsto
            (fun a : Real ↦ ((s - a) / s) ^ 2 * H s)
            (𝓝[>] 0) (𝓝 (H s)) := by
          simpa only [one_mul] using hcoef.mul tendsto_const_nhds
        apply hprod.congr'
        filter_upwards [Ioo_mem_nhdsGT hsI.1] with a ha
        simp only [F, if_pos ha.2]
  have hEq :
      (fun a ↦ lKTail S T alpha a b) =ᶠ[𝓝[>] 0]
        (fun a ↦ 2 * ∫ s in (0 : Real)..b, F a s) := by
    filter_upwards [Ioo_mem_nhdsGT hb] with a ha
    have hFint : IntervalIntegrable (F a) volume 0 b := by
      apply hHint.mono_fun (hFmeas a)
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      exact ae_of_all _ fun s hs ↦ by
        simpa only [Real.norm_eq_abs] using hFbound ha.1 hs
    have haI : a ∈ Set.uIcc (0 : Real) b := by
      simpa only [Set.uIcc_of_le hb.le] using ⟨ha.1.le, ha.2.le⟩
    have hparts := (IntervalIntegrable.trans_iff (f := F a) haI).1 hFint
    have hzero : ∫ s in (0 : Real)..a, F a s = 0 := by
      calc
        (∫ s in (0 : Real)..a, F a s) = ∫ _s in (0 : Real)..a, 0 := by
          apply intervalIntegral.integral_congr
          intro s hs
          have hsI : s ∈ Set.Icc (0 : Real) a := by
            simpa only [Set.uIcc_of_le ha.1.le] using hs
          simp only [F, if_neg (not_lt.mpr hsI.2)]
        _ = 0 := intervalIntegral.integral_zero
    have htail :
        (∫ s in a..b, F a s) =
          ∫ s in a..b, ((s - a) / s) ^ 2 * H s := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hsI : s ∈ Set.Icc a b := by
        simpa only [Set.uIcc_of_le ha.2.le] using hs
      by_cases has : a < s
      · simp only [F, if_pos has]
      · have hsa : s = a := le_antisymm (not_lt.mp has) hsI.1
        subst s
        simp only [F, lt_self_iff_false, if_false, sub_self, zero_div]
        ring
    rw [lKTail]
    congr 1
    calc
      (∫ s in a..b, ((s - a) / s) ^ 2 * H s) =
          (∫ s in a..b, F a s) := htail.symm
      _ = (∫ s in (0 : Real)..a, F a s) + ∫ s in a..b, F a s := by
        rw [hzero, zero_add]
      _ = ∫ s in (0 : Real)..b, F a s :=
        intervalIntegral.integral_add_adjacent_intervals hparts.1 hparts.2
  have hscaled : Tendsto
      (fun a ↦ 2 * ∫ s in (0 : Real)..b, F a s)
      (𝓝[>] 0) (𝓝 (2 * ∫ s in (0 : Real)..b, H s)) :=
    tendsto_const_nhds.mul hfixed
  have htailLim := hscaled.congr' hEq.symm
  simpa only [alpha, H, lK] using htailLim

omit [InnerProductSpace Real E] in
omit [SigmaCompactSpace M] in
private theorem lTraceInt_data
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {b : Real}
    (hb : 0 < b) (hbdom : b ∈ lRegDomain S T x Z)
    (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegCurve S T x Z s))
    (hP : ∀ i s, s ∈ Set.Icc (0 : Real) b →
      DifferentiableAt Real
        (chartRepAt (I := I) (lRegCurve S T x Z) (P i) s) s)
    (hDP : ∀ i s, s ∈ Set.Icc (0 : Real) b →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z) (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z s) (P i s))
    (hON : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (lRegCurve S T x Z b)
          (P i b) (P j b) = if i = j then 1 else 0)
    (hIint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (s / b) ^ 2 *
        lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s)
      MeasureTheory.volume 0 b) :
    IntervalIntegrable
        (fun s ↦ lHamSq S T (lRegCurve S T x Z) s)
        MeasureTheory.volume 0 b ∧
      ∫ s in (0 : Real)..b,
          ((s / b) ^ 2 * ∑ i : Fin (Module.finrank Real E),
              lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s) -
            (2 * s ^ 2 / b ^ 2) *
              S.scalar (T - s ^ 2) (lRegCurve S T x Z s) =
        -b * S.scalar (T - b ^ 2) (lRegCurve S T x Z b) -
          lK S T (lRegCurve S T x Z) b / (2 * b ^ 2) := by
  classical
  let U : Set Real := lRegDomain S T x Z
  let alpha : Real → M := lRegCurve S T x Z
  let R : Real → Real := fun s ↦ S.scalar (T - s ^ 2) (alpha s)
  let F : Real → Real := fun s ↦ s ^ 3 * R s
  let Q : Real → Real := fun s ↦
    s ^ 2 * ∑ i : Fin (Module.finrank Real E),
      lRegIndexInt S T alpha (P i) (P i) s - 2 * s ^ 2 * R s
  have hgeo := lRegCurve_isReg (I := I) S hS T x Z hb hbdom
  have ht : ∀ s ∈ Set.Icc (0 : Real) b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact (hgeo.2.2 s (by
      simpa only [Set.uIcc_of_le hb.le] using hs)).1
  have halpha : ∀ s ∈ Set.Icc (0 : Real) b,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s := by
    intro s hs
    exact (hgeo.2.2 s (by
      simpa only [Set.uIcc_of_le hb.le] using hs)).2.1
  have hONs (s : Real) (hs : s ∈ Set.Icc (0 : Real) b)
      (i j : Fin (Module.finrank Real E)) :
      (S.base.metric (T - s ^ 2)).inner (alpha s) (P i s) (P j s) =
        if i = j then 1 else 0 := by
    rw [lAdapted_inner_eq (I := I) S hS T alpha (P i) (P j) hs.2
      (fun r hr ↦ ht r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ halpha r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hP i r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hP j r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hDP i r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hDP j r ⟨le_trans hs.1 hr.1, hr.2⟩)]
    simpa only [alpha] using hON i j
  have hUopen : IsOpen U := by
    simpa only [U] using lRegDomain_isOpen S T x Z
  let z : E := Z
  have hpair : ContMDiff (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real)) ∞
      (fun s : Real ↦ (z, s)) :=
    contMDiff_const.prodMk contMDiff_id
  have halphaInf : ContMDiffOn (modelWithCornersSelf Real Real) I ∞ alpha U := by
    change ContMDiffOn (modelWithCornersSelf Real Real) I ∞
      ((fun q : E × Real ↦ lRegCurve S T x q.1 q.2) ∘
        fun s : Real ↦ (z, s)) U
    exact (lRegCurve_smoothOn S hS T x).comp hpair.contMDiffOn
      (fun s (hs : s ∈ U) ↦ by
        change s ∈ lRegDomain S T x z
        change s ∈ lRegDomain S T x Z at hs
        exact hs)
  have htime : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞
      (fun s : Real ↦ T - s ^ 2) :=
    contMDiff_const.sub (contMDiff_id.pow 2)
  have harg : ContMDiffOn (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real Real).prod I) ∞
      (fun s : Real ↦ (T - s ^ 2, alpha s)) U :=
    htime.contMDiffOn.prodMk halphaInf
  have hRmd : ContMDiffOn (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ R U := by
    change ContMDiffOn (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞
      ((fun p : Real × M ↦ S.scalar p.1 p.2) ∘
        fun s : Real ↦ (T - s ^ 2, alpha s)) U
    exact (scalar_joint (I := I) S hS).comp harg
      (fun s (hs : s ∈ U) ↦
        ⟨lRegDomain_reg S T x Z (by simpa only [U] using hs),
          Set.mem_univ _⟩)
  have hR : ContDiffOn Real ∞ R U :=
    contMDiffOn_iff_contDiffOn.mp hRmd
  have hF : ContDiffOn Real ∞ F U := by
    simpa only [F, id_eq] using (contDiff_id.pow 3).contDiffOn.mul hR
  have hsegU : Set.Icc (0 : Real) b ⊆ U := by
    intro s hs
    simpa only [U] using lRegDomain_seg S T x Z hbdom hs.1 hs.2
  have hRcont : ContinuousOn R (Set.Icc (0 : Real) b) :=
    hR.continuousOn.mono hsegU
  have hFdcont : ContinuousOn (deriv F) (Set.Icc (0 : Real) b) :=
    (hF.continuousOn_deriv_of_isOpen hUopen (by simp)).mono hsegU
  have hFdint : IntervalIntegrable (deriv F) MeasureTheory.volume 0 b :=
    hFdcont.intervalIntegrable_of_Icc hb.le
  have hidxInt : IntervalIntegrable
      (fun s : Real ↦ (s / b) ^ 2 *
        ∑ i : Fin (Module.finrank Real E),
          lRegIndexInt S T alpha (P i) (P i) s)
      MeasureTheory.volume 0 b := by
    have hsum := IntervalIntegrable.sum
      (Finset.univ : Finset (Fin (Module.finrank Real E)))
      (fun i _ ↦ by simpa only [alpha] using hIint i)
    refine hsum.congr ?_
    intro s _hs
    simp only [alpha, Finset.sum_apply, Finset.mul_sum]
  have hRterm : IntervalIntegrable
      (fun s : Real ↦ (2 * s ^ 2 / b ^ 2) * R s)
      MeasureTheory.volume 0 b := by
    have hc : Continuous (fun s : Real ↦ 2 * s ^ 2 / b ^ 2) :=
      (continuous_const.mul (continuous_id.pow 2)).div_const _
    exact (hc.continuousOn.mul hRcont).intervalIntegrable_of_Icc hb.le
  have hscaled : IntervalIntegrable
      (fun s : Real ↦ (s / b) ^ 2 *
          ∑ i : Fin (Module.finrank Real E),
            lRegIndexInt S T alpha (P i) (P i) s -
        (2 * s ^ 2 / b ^ 2) * R s)
      MeasureTheory.volume 0 b := hidxInt.sub hRterm
  have hQint : IntervalIntegrable Q MeasureTheory.volume 0 b := by
    refine (hscaled.const_mul (b ^ 2)).congr ?_
    intro s _hs
    simp only [Q]
    field_simp [hb.ne']
  have htraceDeriv (s : Real) (hs : s ∈ Set.Icc (0 : Real) b) :
      HasDerivAt F (-lHamSq S T alpha s - Q s) s := by
    simpa only [F, Q] using
      lTrace_deriv S hS T alpha P s (ht s hs) (halpha s hs)
        (fun i ↦ hDP i s hs) (hONs s hs)
  have hderivEq : Set.EqOn (deriv F)
      (fun s : Real ↦ -lHamSq S T alpha s - Q s)
      (Set.Icc (0 : Real) b) := by
    intro s hs
    exact (htraceDeriv s hs).deriv
  have hderivInt : IntervalIntegrable
      (fun s : Real ↦ -lHamSq S T alpha s - Q s)
      MeasureTheory.volume 0 b := by
    refine hFdint.congr ?_
    intro s hs
    apply hderivEq
    have hs' : s ∈ Set.Ioc (0 : Real) b := by
      simpa only [Set.uIoc_of_le hb.le] using hs
    exact ⟨hs'.1.le, hs'.2⟩
  have hHamInt : IntervalIntegrable (fun s ↦ lHamSq S T alpha s)
      MeasureTheory.volume 0 b := by
    refine ((hderivInt.add hQint).neg).congr ?_
    intro s _hs
    simp
  have hFTC :
      (∫ s in (0 : Real)..b, -lHamSq S T alpha s - Q s) = F b - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs ↦ htraceDeriv s (by
        simpa only [Set.uIcc_of_le hb.le] using hs)) hderivInt
  have hQeq :
      (∫ s in (0 : Real)..b, Q s) =
        -b ^ 3 * R b - lK S T alpha b / 2 := by
    have hsplit := intervalIntegral.integral_sub
      (f := fun s : Real ↦ -lHamSq S T alpha s) (g := Q)
      hHamInt.neg hQint
    rw [hsplit, intervalIntegral.integral_neg] at hFTC
    simp only [F, R] at hFTC
    rw [lK]
    linarith
  have hscaleEq :
      (∫ s in (0 : Real)..b, Q s) =
        b ^ 2 * ∫ s in (0 : Real)..b,
          ((s / b) ^ 2 *
              ∑ i : Fin (Module.finrank Real E),
                lRegIndexInt S T alpha (P i) (P i) s -
            (2 * s ^ 2 / b ^ 2) * R s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _hs
    simp only [Q]
    field_simp [hb.ne']
  rw [hQeq] at hscaleEq
  have hfinal :
      (∫ s in (0 : Real)..b,
          ((s / b) ^ 2 *
              ∑ i : Fin (Module.finrank Real E),
                lRegIndexInt S T alpha (P i) (P i) s -
            (2 * s ^ 2 / b ^ 2) * R s)) =
        -b * R b - lK S T alpha b / (2 * b ^ 2) := by
    have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb.ne'
    have hdiv :
        (∫ s in (0 : Real)..b,
            ((s / b) ^ 2 *
                ∑ i : Fin (Module.finrank Real E),
                  lRegIndexInt S T alpha (P i) (P i) s -
              (2 * s ^ 2 / b ^ 2) * R s)) =
          (-b ^ 3 * R b - lK S T alpha b / 2) / b ^ 2 := by
      apply (eq_div_iff hb2).2
      nlinarith [hscaleEq]
    rw [hdiv]
    field_simp [hb.ne']
  exact ⟨by simpa only [alpha] using hHamInt,
    by simpa only [alpha, R] using hfinal⟩

omit [InnerProductSpace Real E] in
omit [SigmaCompactSpace M] in
private theorem lTracePos_data
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {a b : Real}
    (ha : 0 < a) (hab : a < b) (hbdom : b ∈ lRegDomain S T x Z)
    (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegCurve S T x Z s))
    (hP : ∀ i s, s ∈ Set.Icc a b →
      DifferentiableAt Real
        (chartRepAt (I := I) (lRegCurve S T x Z) (P i) s) s)
    (hDP : ∀ i s, s ∈ Set.Icc a b →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z) (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z s) (P i s))
    (hON : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (lRegCurve S T x Z b)
          (P i b) (P j b) = if i = j then 1 else 0)
    (hIint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ ((s - a) / (b - a)) ^ 2 *
        lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s)
      MeasureTheory.volume a b) :
    IntervalIntegrable
        (fun s ↦ ((s - a) / s) ^ 2 *
          lHamSq S T (lRegCurve S T x Z) s)
        MeasureTheory.volume a b ∧
      ∫ s in a..b,
          (((s - a) / (b - a)) ^ 2 *
              ∑ i : Fin (Module.finrank Real E),
                lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s -
            (2 * s * (s - a) / (b - a) ^ 2) *
              S.scalar (T - s ^ 2) (lRegCurve S T x Z s)) =
        -b * S.scalar (T - b ^ 2) (lRegCurve S T x Z b) -
          lKTail S T (lRegCurve S T x Z) a b /
            (2 * (b - a) ^ 2) := by
  classical
  let U : Set Real := lRegDomain S T x Z
  let alpha : Real → M := lRegCurve S T x Z
  let R : Real → Real := fun s ↦ S.scalar (T - s ^ 2) (alpha s)
  let F : Real → Real := fun s ↦ s ^ 3 * R s
  let c : Real → Real := fun s ↦ ((s - a) / s) ^ 2
  let G : Real → Real := fun s ↦ s * (s - a) ^ 2 * R s
  let Q : Real → Real := fun s ↦
    s ^ 2 * ∑ i : Fin (Module.finrank Real E),
      lRegIndexInt S T alpha (P i) (P i) s - 2 * s ^ 2 * R s
  let A : Real → Real := fun s ↦
    ((s - a) / (b - a)) ^ 2 *
        ∑ i : Fin (Module.finrank Real E),
          lRegIndexInt S T alpha (P i) (P i) s -
      (2 * s * (s - a) / (b - a) ^ 2) * R s
  let W : Real → Real := fun s ↦ c s * lHamSq S T alpha s
  have hb : 0 < b := lt_trans ha hab
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hgeo := lRegCurve_isReg (I := I) S hS T x Z hb hbdom
  have ht : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact (hgeo.2.2 s (by
      rw [Set.uIcc_of_le hb.le]
      exact ⟨ha.le.trans hs.1, hs.2⟩)).1
  have halpha : ∀ s ∈ Set.Icc a b,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s := by
    intro s hs
    exact (hgeo.2.2 s (by
      rw [Set.uIcc_of_le hb.le]
      exact ⟨ha.le.trans hs.1, hs.2⟩)).2.1
  have hONs (s : Real) (hs : s ∈ Set.Icc a b)
      (i j : Fin (Module.finrank Real E)) :
      (S.base.metric (T - s ^ 2)).inner (alpha s) (P i s) (P j s) =
        if i = j then 1 else 0 := by
    rw [lAdapted_inner_eq (I := I) S hS T alpha (P i) (P j) hs.2
      (fun r hr ↦ ht r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ halpha r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hP i r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hP j r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hDP i r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hDP j r ⟨le_trans hs.1 hr.1, hr.2⟩)]
    simpa only [alpha] using hON i j
  have hUopen : IsOpen U := by
    simpa only [U] using lRegDomain_isOpen S T x Z
  let z : E := Z
  have hpair : ContMDiff (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real)) ∞
      (fun s : Real ↦ (z, s)) :=
    contMDiff_const.prodMk contMDiff_id
  have halphaInf : ContMDiffOn (modelWithCornersSelf Real Real) I ∞ alpha U := by
    change ContMDiffOn (modelWithCornersSelf Real Real) I ∞
      ((fun q : E × Real ↦ lRegCurve S T x q.1 q.2) ∘
        fun s : Real ↦ (z, s)) U
    exact (lRegCurve_smoothOn S hS T x).comp hpair.contMDiffOn
      (fun s (hs : s ∈ U) ↦ by
        change s ∈ lRegDomain S T x z
        change s ∈ lRegDomain S T x Z at hs
        exact hs)
  have htime : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞
      (fun s : Real ↦ T - s ^ 2) :=
    contMDiff_const.sub (contMDiff_id.pow 2)
  have harg : ContMDiffOn (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real Real).prod I) ∞
      (fun s : Real ↦ (T - s ^ 2, alpha s)) U :=
    htime.contMDiffOn.prodMk halphaInf
  have hRmd : ContMDiffOn (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ R U := by
    change ContMDiffOn (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞
      ((fun p : Real × M ↦ S.scalar p.1 p.2) ∘
        fun s : Real ↦ (T - s ^ 2, alpha s)) U
    exact (scalar_joint (I := I) S hS).comp harg
      (fun s (hs : s ∈ U) ↦
        ⟨lRegDomain_reg S T x Z (by simpa only [U] using hs),
          Set.mem_univ _⟩)
  have hR : ContDiffOn Real ∞ R U :=
    contMDiffOn_iff_contDiffOn.mp hRmd
  have hG : ContDiffOn Real ∞ G U := by
    simpa only [G, id_eq] using
      (contDiff_id.mul ((contDiff_id.sub contDiff_const).pow 2)).contDiffOn.mul hR
  have hsegU : Set.Icc a b ⊆ U := by
    intro s hs
    simpa only [U] using
      lRegDomain_seg S T x Z hbdom (ha.le.trans hs.1) hs.2
  have hRcont : ContinuousOn R (Set.Icc a b) :=
    hR.continuousOn.mono hsegU
  have hGdcont : ContinuousOn (deriv G) (Set.Icc a b) :=
    (hG.continuousOn_deriv_of_isOpen hUopen (by simp)).mono hsegU
  have hGdint : IntervalIntegrable (deriv G) MeasureTheory.volume a b :=
    hGdcont.intervalIntegrable_of_Icc hab.le
  have hidxInt : IntervalIntegrable
      (fun s : Real ↦ ((s - a) / (b - a)) ^ 2 *
        ∑ i : Fin (Module.finrank Real E),
          lRegIndexInt S T alpha (P i) (P i) s)
      MeasureTheory.volume a b := by
    have hsum := IntervalIntegrable.sum
      (Finset.univ : Finset (Fin (Module.finrank Real E)))
      (fun i _ ↦ by simpa only [alpha] using hIint i)
    refine hsum.congr ?_
    intro s _hs
    simp only [alpha, Finset.sum_apply, Finset.mul_sum]
  have hRterm : IntervalIntegrable
      (fun s : Real ↦
        (2 * s * (s - a) / (b - a) ^ 2) * R s)
      MeasureTheory.volume a b := by
    have hc : Continuous
        (fun s : Real ↦ 2 * s * (s - a) / (b - a) ^ 2) :=
      ((continuous_const.mul continuous_id).mul
        (continuous_id.sub continuous_const)).div_const _
    exact (hc.continuousOn.mul hRcont).intervalIntegrable_of_Icc hab.le
  have hAint : IntervalIntegrable A MeasureTheory.volume a b := by
    simpa only [A] using hidxInt.sub hRterm
  have htraceDeriv (s : Real) (hs : s ∈ Set.Icc a b) :
      HasDerivAt G (-W s - (b - a) ^ 2 * A s) s := by
    have hs0 : s ≠ 0 := ne_of_gt (ha.trans_le hs.1)
    have hc0 := ((((hasDerivAt_id s).sub_const a).div
      (hasDerivAt_id s) hs0).pow 2)
    change HasDerivAt c _ s at hc0
    have hc : HasDerivAt c (2 * a * (s - a) / s ^ 3) s := by
      apply hc0.congr_deriv
      simp
      field_simp [hs0]
    have htrace := lTrace_deriv S hS T alpha P s (ht s hs) (halpha s hs)
      (fun i ↦ hDP i s hs) (hONs s hs)
    have hprod := hc.mul htrace
    have hfun : (fun r : Real ↦ c r * F r) = G := by
      funext r
      by_cases hr : r = 0
      · subst r
        simp [c, F, G]
      · dsimp only [c, F, G]
        field_simp [hr]
    change HasDerivAt (fun r : Real ↦ c r * F r) _ s at hprod
    rw [hfun] at hprod
    apply hprod.congr_deriv
    dsimp only [c, F, Q, A, W, R]
    field_simp [hs0, hba]
    ring
  have hderivEq : Set.EqOn (deriv G)
      (fun s : Real ↦ -W s - (b - a) ^ 2 * A s) (Set.Icc a b) := by
    intro s hs
    exact (htraceDeriv s hs).deriv
  have hderivInt : IntervalIntegrable
      (fun s : Real ↦ -W s - (b - a) ^ 2 * A s)
      MeasureTheory.volume a b := by
    refine hGdint.congr ?_
    intro s hs
    apply hderivEq
    have hs' : s ∈ Set.Ioc a b := by
      simpa only [Set.uIoc_of_le hab.le] using hs
    exact ⟨hs'.1.le, hs'.2⟩
  have hWint : IntervalIntegrable W MeasureTheory.volume a b := by
    refine ((hderivInt.add (hAint.const_mul ((b - a) ^ 2))).neg).congr ?_
    intro s _hs
    simp
  have hFTC :
      (∫ s in a..b, -W s - (b - a) ^ 2 * A s) = G b - G a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs ↦ htraceDeriv s (by
        simpa only [Set.uIcc_of_le hab.le] using hs)) hderivInt
  have hfund :
      -(∫ s in a..b, W s) -
          (b - a) ^ 2 * ∫ s in a..b, A s =
        b * (b - a) ^ 2 * R b := by
    have hWneg : IntervalIntegrable (fun s ↦ -W s)
        MeasureTheory.volume a b := by
      change IntervalIntegrable (-W) MeasureTheory.volume a b
      exact hWint.neg
    have hAc : IntervalIntegrable (fun s ↦ (b - a) ^ 2 * A s)
        MeasureTheory.volume a b := by
      simpa only using hAint.const_mul ((b - a) ^ 2)
    rw [intervalIntegral.integral_sub hWneg hAc,
      intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul] at hFTC
    simpa only [G, sub_self, pow_two, mul_zero, zero_mul, sub_zero] using hFTC
  have hfinal :
      (∫ s in a..b, A s) =
        -b * R b - (2 * ∫ s in a..b, W s) /
          (2 * (b - a) ^ 2) := by
    field_simp [hba]
    nlinarith [hfund]
  exact ⟨by simpa only [W, c, alpha] using hWint,
    by simpa only [A, R, W, c, alpha, lKTail] using hfinal⟩

omit [InnerProductSpace Real E] in
omit [SigmaCompactSpace M] in
theorem lHamSq_int
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {b : Real}
    (hb : 0 < b) (hbdom : b ∈ lRegDomain S T x Z)
    (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegCurve S T x Z s))
    (hP : ∀ i s, s ∈ Set.Icc (0 : Real) b →
      DifferentiableAt Real
        (chartRepAt (I := I) (lRegCurve S T x Z) (P i) s) s)
    (hDP : ∀ i s, s ∈ Set.Icc (0 : Real) b →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z) (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z s) (P i s))
    (hON : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (lRegCurve S T x Z b)
          (P i b) (P j b) = if i = j then 1 else 0)
    (hIint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (s / b) ^ 2 *
        lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s)
      MeasureTheory.volume 0 b) :
    IntervalIntegrable
      (fun s ↦ lHamSq S T (lRegCurve S T x Z) s)
      MeasureTheory.volume 0 b :=
  (lTraceInt_data S hS T x Z hb hbdom P hP hDP hON hIint).1

omit [InnerProductSpace Real E] in
omit [SigmaCompactSpace M] in
theorem lTraceInt_eq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {b : Real}
    (hb : 0 < b) (hbdom : b ∈ lRegDomain S T x Z)
    (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegCurve S T x Z s))
    (hP : ∀ i s, s ∈ Set.Icc (0 : Real) b →
      DifferentiableAt Real
        (chartRepAt (I := I) (lRegCurve S T x Z) (P i) s) s)
    (hDP : ∀ i s, s ∈ Set.Icc (0 : Real) b →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z) (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z s) (P i s))
    (hON : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (lRegCurve S T x Z b)
          (P i b) (P j b) = if i = j then 1 else 0)
    (hIint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (s / b) ^ 2 *
        lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s)
      MeasureTheory.volume 0 b) :
    ∫ s in (0 : Real)..b,
        ((s / b) ^ 2 * ∑ i : Fin (Module.finrank Real E),
            lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s) -
          (2 * s ^ 2 / b ^ 2) *
            S.scalar (T - s ^ 2) (lRegCurve S T x Z s) =
      -b * S.scalar (T - b ^ 2) (lRegCurve S T x Z b) -
        lK S T (lRegCurve S T x Z) b / (2 * b ^ 2) :=
  (lTraceInt_data S hS T x Z hb hbdom P hP hDP hON hIint).2

omit [InnerProductSpace Real E] in
omit [SigmaCompactSpace M] in
theorem lTraceInt_pos
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {a b : Real}
    (ha : 0 < a) (hab : a < b) (hbdom : b ∈ lRegDomain S T x Z)
    (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegCurve S T x Z s))
    (hP : ∀ i s, s ∈ Set.Icc a b →
      DifferentiableAt Real
        (chartRepAt (I := I) (lRegCurve S T x Z) (P i) s) s)
    (hDP : ∀ i s, s ∈ Set.Icc a b →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z) (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z s) (P i s))
    (hON : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (lRegCurve S T x Z b)
          (P i b) (P j b) = if i = j then 1 else 0)
    (hIint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ ((s - a) / (b - a)) ^ 2 *
        lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s)
      MeasureTheory.volume a b) :
    ∫ s in a..b,
        (((s - a) / (b - a)) ^ 2 *
            ∑ i : Fin (Module.finrank Real E),
              lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s -
          (2 * s * (s - a) / (b - a) ^ 2) *
            S.scalar (T - s ^ 2) (lRegCurve S T x Z s)) =
      -b * S.scalar (T - b ^ 2) (lRegCurve S T x Z b) -
        lKTail S T (lRegCurve S T x Z) a b /
          (2 * (b - a) ^ 2) :=
  (lTracePos_data S hS T x Z ha hab hbdom P hP hDP hON hIint).2

end normedSpaceCompatibility

end DifferentialGeometry.PDE.RicciFlow.Perelman
