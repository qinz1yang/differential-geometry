import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CostRampBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionLocalMin

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter MeasureTheory Set
open scoped ContDiff Manifold Topology NNReal

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

noncomputable def lChartRamp (y z : E) {L : Real} (hL : 0 ≤ L) : timeH1 E L :=
  timeH1.ofContDiffOn hL
    (fun r : Real ↦ y + (r / L) • (z - y))
    ((contDiff_const.add
      ((contDiff_id.div_const L).smul contDiff_const)).contDiffOn)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [CompactSpace M] in
theorem lRamp_apply (y z : E) {L r : Real} (hL : 0 ≤ L)
    (hr : r ∈ Icc (0 : Real) L) :
    (lChartRamp y z hL).toFun r = y + (r / L) • (z - y) := by
  exact timeH1.toFun_ofContDiffOn hL _ _ hr

omit [NeZero (Module.finrank Real E)] in
omit [FiniteDimensional ℝ E] in
theorem lRamp_deriv {y z : E} {L : Real} (hL : 0 < L) :
    (lChartRamp y z hL.le).deriv =ᵐ[timeMeasure L]
      fun _ ↦ (1 / L) • (z - y) := by
  filter_upwards [timeH1.deriv_ofContDiffOn hL.le
    (fun r : Real ↦ y + (r / L) • (z - y)) _] with r hr
  have hr' : (lChartRamp y z hL.le).deriv r =
      deriv (fun s : Real ↦ y + (s / L) • (z - y)) r := by
    simpa only [lChartRamp] using hr
  rw [hr']
  change deriv (fun s : Real ↦ y + (id s / L) • (z - y)) r =
    (1 / L) • (z - y)
  simpa only [one_div] using
    ((hasDerivAt_id r).div_const L |>.smul_const (z - y) |>.const_add y).deriv

omit [NeZero (Module.finrank Real E)] in
theorem lRamp_start {y z : E} {L : Real} (hL : 0 ≤ L) :
    (lChartRamp y z hL).toFun 0 = y := by
  rw [lRamp_apply (y := y) (z := z) hL ⟨le_rfl, hL⟩,
    zero_div, zero_smul, add_zero]

omit [NeZero (Module.finrank Real E)] in
theorem lRamp_end {y z : E} {L : Real} (hL : 0 < L) :
    (lChartRamp y z hL.le).toFun L = z := by
  rw [lRamp_apply (y := y) (z := z) hL.le ⟨hL.le, le_rfl⟩,
    div_self hL.ne', one_smul]
  abel

omit [NeZero (Module.finrank Real E)] in
theorem lRamp_mapsTo {K : Set E} (hK : Convex Real K) {y z : E}
    {L : Real} (hL : 0 ≤ L)
    (hy : y ∈ K) (hz : z ∈ K) :
    MapsTo (lChartRamp y z hL).toFun (Icc (0 : Real) L) K := by
  intro r hr
  by_cases hL0 : L = 0
  · subst L
    have hr0 : r = 0 := le_antisymm (by simpa using hr.2) hr.1
    rw [lRamp_apply (y := y) (z := z) (le_refl 0) hr,
      hr0, zero_div, zero_smul, add_zero]
    exact hy
  · rw [lRamp_apply (y := y) (z := z) hL hr]
    let t : Real := r / L
    have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    have ht : t ∈ Icc (0 : Real) 1 := by
      exact ⟨div_nonneg hr.1 hLpos.le, (div_le_one hLpos).2 hr.2⟩
    simpa only [t, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      add_comm] using hK.lineMap_mem hy hz ht

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [CompactSpace M] in
theorem lRampAct_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a : Real) (p : M) {y z : E} {L : Real} (hL : 0 < L)
    (hreg : ∀ r ∈ Icc (0 : Real) L,
      T - (a + r) ^ 2 ∈ D.regular)
    (htar : MapsTo (lChartRamp y z hL.le).toFun
      (Icc (0 : Real) L) (interior (extChartAt I p).target))
    (Cg Cs : Real)
    (hgram : ∀ r ∈ Icc (0 : Real) L,
      ‖chartGramOp (I := I) S.family p
        (T - (a + r) ^ 2, (lChartRamp y z hL.le).toFun r)‖ ≤ Cg)
    (hscalar : ∀ r ∈ Icc (0 : Real) L,
      |2 * (a + r) ^ 2 * S.scalar (T - (a + r) ^ 2)
        ((extChartAt I p).symm ((lChartRamp y z hL.le).toFun r))| ≤ Cs) :
    lChartAct S T a p (lChartRamp y z hL.le) ≤
      (Cg / 2) * (‖z - y‖ ^ 2 / L) + Cs * L := by
  let u : timeH1 E L := lChartRamp y z hL.le
  let v : E := (1 / L) • (z - y)
  let τ : Real → Real := fun r ↦ T - (a + r) ^ 2
  let A : Real → E →L[Real] E := fun r ↦
    chartGramOp (I := I) S.family p (τ r, u.toFun r)
  let kin : Real → Real := fun r ↦
    (1 / 2 : Real) * inner Real (A r v) v
  let pot : Real → Real := fun r ↦
    2 * (a + r) ^ 2 * S.scalar (τ r)
      ((extChartAt I p).symm (u.toFun r))
  have hvnorm : ‖v‖ = ‖z - y‖ / L := by
    rw [show v = (1 / L) • (z - y) by rfl, norm_smul,
      Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hL)]
    rw [one_div, inv_mul_eq_div]
  have huDer : u.deriv =ᵐ[timeMeasure L] fun _ ↦ v := by
    simpa only [u, v] using lRamp_deriv (y := y) (z := z) hL
  have hτc : ContinuousOn τ (Icc (0 : Real) L) := by
    exact continuousOn_const.sub
      ((continuousOn_const.add continuousOn_id).pow 2)
  let J : Set Real := τ '' Icc (0 : Real) L
  let K : Set E := u.toFun '' Icc (0 : Real) L
  have hJreg : J ⊆ D.regular := by
    rintro _ ⟨r, hr, rfl⟩
    exact hreg r hr
  have hKchart : K ⊆ interior (extChartAt I p).target := by
    rintro _ ⟨r, hr, rfl⟩
    exact htar (by simpa only [u] using hr)
  have hpair : ContinuousOn (fun r ↦ (τ r, u.toFun r))
      (Icc (0 : Real) L) := hτc.prodMk u.continuousOn_toFun
  have hAcont : ContinuousOn A (Icc (0 : Real) L) := by
    exact (chartGramOp_cont (I := I) hS.smoothMetric hJreg p hKchart).comp
      hpair (fun r hr ↦ ⟨⟨r, hr, rfl⟩, ⟨r, hr, rfl⟩⟩)
  have hkinCont : ContinuousOn kin (Icc (0 : Real) L) := by
    exact continuousOn_const.mul
      ((hAcont.clm_apply continuousOn_const).inner continuousOn_const)
  have hkinInt : IntervalIntegrable kin volume 0 L :=
    ContinuousOn.intervalIntegrable_of_Icc hL.le hkinCont
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hinv : ContinuousOn
      (fun r ↦ (extChartAt I p).symm (u.toFun r)) (Icc (0 : Real) L) :=
    (continuousOn_extChartAt_symm (I := I) p).comp
      u.continuousOn_toFun (fun r hr ↦
        (interior_subset (s := (extChartAt I p).target)) (hKchart ⟨r, hr, rfl⟩))
  have hscalarCont : ContinuousOn (fun r ↦
      S.scalar (τ r) ((extChartAt I p).symm (u.toFun r)))
      (Icc (0 : Real) L) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let τ' : Icc (0 : Real) L → {q : Real // q ∈ D.carrier} := fun r ↦
      ⟨τ r.1, D.regular_subset (hJreg ⟨r.1, r.2, rfl⟩)⟩
    have hτ' : Continuous τ' := continuous_induced_rng.mpr hτc.domRestrict
    have hc := hSc.continuous_subtype.comp (hτ'.prodMk hinv.domRestrict)
    change Continuous
      ((fun q : {t : Real // t ∈ D.carrier} × M ↦
        S.scalar q.1.1 q.2) ∘ fun r : Icc (0 : Real) L ↦
          (τ' r, (extChartAt I p).symm (u.toFun r)))
    exact hc
  have hpotCont : ContinuousOn pot (Icc (0 : Real) L) := by
    exact (continuous_const.mul
      ((continuous_const.add continuous_id).pow 2)).continuousOn.mul hscalarCont
  have hpotInt : IntervalIntegrable pot volume 0 L :=
    ContinuousOn.intervalIntegrable_of_Icc hL.le hpotCont
  have huDer' : u.deriv =ᵐ[volume.restrict (uIoc (0 : Real) L)]
      fun _ ↦ v := by
    have hm := huDer.filter_mono
      (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
    simpa only [timeMeasure, uIoc_of_le hL.le,
      restrict_Ioc_eq_restrict_Icc] using hm
  have hact : lChartAct S T a p u =
      (∫ r in (0 : Real)..L, kin r) + ∫ r in (0 : Real)..L, pot r := by
    unfold lChartAct lChartLag
    rw [intervalIntegral.integral_add]
    · congr 1
      · apply intervalIntegral.integral_congr_ae_restrict
        filter_upwards [huDer'] with r hr
        rw [hr]
        simp only [kin, A, τ, smul_apply,
          real_inner_smul_left]
    · exact hkinInt.congr_ae (by
        filter_upwards [huDer'] with r hr
        rw [hr]
        simp only [kin, A, τ, smul_apply,
          real_inner_smul_left])
    · exact hpotInt
  have hkinLe : ∀ r ∈ Icc (0 : Real) L,
      kin r ≤ Cg / 2 * (‖z - y‖ / L) ^ 2 := by
    intro r hr
    have hA := hgram r hr
    have hinner : inner Real (A r v) v ≤
        Cg * (‖z - y‖ / L) ^ 2 := by
      calc
        inner Real (A r v) v ≤ ‖A r v‖ * ‖v‖ := real_inner_le_norm _ _
        _ ≤ (‖A r‖ * ‖v‖) * ‖v‖ := by
          gcongr
          exact (A r).le_opNorm v
        _ ≤ Cg * (‖z - y‖ / L) ^ 2 := by
          rw [hvnorm]
          have hnorm : 0 ≤ ‖z - y‖ / L :=
            div_nonneg (norm_nonneg _) hL.le
          calc
            ‖A r‖ * (‖z - y‖ / L) * (‖z - y‖ / L) ≤
                Cg * (‖z - y‖ / L) * (‖z - y‖ / L) := by
              gcongr
            _ = Cg * (‖z - y‖ / L) ^ 2 := by ring
    dsimp only [kin]
    nlinarith
  have hpotLe : ∀ r ∈ Icc (0 : Real) L, pot r ≤ Cs := by
    intro r hr
    exact (le_abs_self (pot r)).trans
      (by simpa only [pot, τ, u] using hscalar r hr)
  have hkinBound : (∫ r in (0 : Real)..L, kin r) ≤
      (Cg / 2 * (‖z - y‖ / L) ^ 2) * L := by
    have hconst : IntervalIntegrable
        (fun _ : Real ↦ Cg / 2 * (‖z - y‖ / L) ^ 2) volume 0 L :=
      intervalIntegrable_const
    have hm := intervalIntegral.integral_mono_on hL.le hkinInt hconst hkinLe
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
      mul_comm L] using hm
  have hpotBound : (∫ r in (0 : Real)..L, pot r) ≤ Cs * L := by
    have hconst : IntervalIntegrable (fun _ : Real ↦ Cs) volume 0 L :=
      intervalIntegrable_const
    have hm := intervalIntegral.integral_mono_on hL.le hpotInt hconst hpotLe
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
      mul_comm L] using hm
  rw [show lChartAct S T a p (lChartRamp y z hL.le) = lChartAct S T a p u by rfl,
    hact]
  calc
    (∫ r in (0 : Real)..L, kin r) + ∫ r in (0 : Real)..L, pot r ≤
        (Cg / 2 * (‖z - y‖ / L) ^ 2) * L + Cs * L :=
      add_le_add hkinBound hpotBound
    _ = (Cg / 2) * (‖z - y‖ ^ 2 / L) + Cs * L := by
      field_simp

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [CompactSpace M] in
theorem lRampAct_linear
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a : Real) (p : M) {y z : E} {L : Real} (hL : 0 < L)
    (hreg : ∀ r ∈ Icc (0 : Real) L,
      T - (a + r) ^ 2 ∈ D.regular)
    (htar : MapsTo (lChartRamp y z hL.le).toFun
      (Icc (0 : Real) L) (interior (extChartAt I p).target))
    (Cg Cs V : Real) (hCg : 0 ≤ Cg) (hV : 0 ≤ V)
    (hdisp : ‖z - y‖ ≤ V * L)
    (hgram : ∀ r ∈ Icc (0 : Real) L,
      ‖chartGramOp (I := I) S.family p
        (T - (a + r) ^ 2, (lChartRamp y z hL.le).toFun r)‖ ≤ Cg)
    (hscalar : ∀ r ∈ Icc (0 : Real) L,
      |2 * (a + r) ^ 2 * S.scalar (T - (a + r) ^ 2)
        ((extChartAt I p).symm ((lChartRamp y z hL.le).toFun r))| ≤ Cs) :
    lChartAct S T a p (lChartRamp y z hL.le) ≤
      (Cg / 2 * V ^ 2 + Cs) * L := by
  have hbase := lRampAct_bound (I := I) S hS T a p hL hreg htar Cg Cs
    hgram hscalar
  have hratio0 : 0 ≤ ‖z - y‖ / L :=
    div_nonneg (norm_nonneg _) hL.le
  have hratio : ‖z - y‖ / L ≤ V := by
    exact (div_le_iff₀ hL).2 hdisp
  have hsq : (‖z - y‖ / L) ^ 2 ≤ V ^ 2 :=
    (sq_le_sq₀ hratio0 hV).2 hratio
  calc
    lChartAct S T a p (lChartRamp y z hL.le) ≤
        Cg / 2 * (‖z - y‖ ^ 2 / L) + Cs * L := hbase
    _ = (Cg / 2 * (‖z - y‖ / L) ^ 2 + Cs) * L := by
      field_simp
    _ ≤ (Cg / 2 * V ^ 2 + Cs) * L := by
      gcongr

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem lRampAct_slab
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (p : M) {A B : Real}
    (hreg : ∀ s ∈ Icc A B, T - s ^ 2 ∈ D.regular)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I p).target) :
    ∃ Cg Cs : Real, 0 ≤ Cg ∧ 0 ≤ Cs ∧
      ∀ {a L : Real} {y z : E} (hL : 0 < L),
        (∀ r ∈ Icc (0 : Real) L, a + r ∈ Icc A B) →
        MapsTo (lChartRamp y z hL.le).toFun (Icc (0 : Real) L) K →
        lChartAct S T a p (lChartRamp y z hL.le) ≤
          (Cg / 2) * (‖z - y‖ ^ 2 / L) + Cs * L := by
  let τ : Real → Real := fun s ↦ T - s ^ 2
  let J : Set Real := τ '' Icc A B
  have hτc : ContinuousOn τ (Icc A B) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn hτc
  have hJreg : J ⊆ D.regular := by
    rintro _ ⟨s, hs, rfl⟩
    exact hreg s hs
  obtain ⟨Cg, hCg⟩ := chartGramOp_bound (I := I) hS.smoothMetric hJreg hJc p
    hKchart hKc
  let P : Real → M → Real := fun s x ↦
    2 * s ^ 2 * S.scalar (T - s ^ 2) x
  have hpair : ContinuousOn
      (fun q : Real × M ↦ (T - q.1 ^ 2, q.2))
      (Icc A B ×ˢ (univ : Set M)) :=
    (continuous_const.sub (continuous_fst.pow 2)).continuousOn.prodMk
      continuous_snd.continuousOn
  have hmaps : MapsTo
      (fun q : Real × M ↦ (T - q.1 ^ 2, q.2))
      (Icc A B ×ˢ (univ : Set M)) (D.carrier ×ˢ (univ : Set M)) := by
    intro q hq
    exact ⟨D.regular_subset (hreg q.1 hq.1), mem_univ _⟩
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hscalar : ContinuousOn
      (fun q : Real × M ↦ S.scalar (T - q.1 ^ 2) q.2)
      (Icc A B ×ˢ (univ : Set M)) := by
    simpa only [Function.comp_def] using
      hSc.scalar_continuousOn.comp hpair hmaps
  have hP : ContinuousOn (fun q : Real × M ↦ P q.1 q.2)
      (Icc A B ×ˢ (univ : Set M)) := by
    exact ((continuous_const.mul (continuous_fst.pow 2)).continuousOn.mul hscalar)
  obtain ⟨Cs0, hCs0⟩ :=
    (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set M))).exists_bound_of_continuousOn hP
  let Cs : Real := max Cs0 0
  refine ⟨Cg, Cs, NNReal.coe_nonneg Cg, le_max_right _ _, ?_⟩
  intro a L y z hL htime hrange
  apply lRampAct_bound (I := I) S hS T a p hL
  · intro r hr
    exact hreg (a + r) (htime r hr)
  · intro r hr
    exact hKchart (hrange hr)
  · intro r hr
    exact hCg (T - (a + r) ^ 2, (lChartRamp y z hL.le).toFun r)
      ⟨⟨a + r, htime r hr, rfl⟩, hrange hr⟩
  · intro r hr
    have hb := hCs0
      (a + r, (extChartAt I p).symm ((lChartRamp y z hL.le).toFun r))
      ⟨htime r hr, mem_univ _⟩
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (le_max_left Cs0 0)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
