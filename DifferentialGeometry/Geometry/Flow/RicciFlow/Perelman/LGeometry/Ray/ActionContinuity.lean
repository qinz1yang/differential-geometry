import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
private theorem continuousOn_lRegLagrangian_variation
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) {x : M} {alpha : E × Real → M} {V : Set E} {K : Set Real}
    (hVopen : IsOpen V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hcurves : ∀ Z ∈ V,
      IsLRegCurveOn S T (fun s ↦ alpha (Z, s)) K x Z) :
    ContinuousOn
      (fun q : E × Real ↦ lRegLagrangian S T (fun s ↦ alpha (q.1, s)) q.2)
      (V ×ˢ K) := by
  let J := 𝓘(Real, E).prod 𝓘(Real, Real)
  let U := V ×ˢ K
  let F : E × Real → M := alpha
  have hUopen : IsOpen U := hVopen.prod hKopen
  have hF : ContMDiffOn J I ∞ F U := by
    simpa only [J, F, U] using halpha
  have htm :=
    hF.contMDiffOn_tangentMapWithin (m := ∞) le_rfl hUopen.uniqueMDiffOn
  have hunit : ContMDiff J J.tangent ∞
      (fun q : E × Real ↦
        (TotalSpace.mk' (E × Real) q ((0 : E), (1 : Real)) :
          TangentBundle J (E × Real))) := by
    have hE : ContMDiff 𝓘(Real, E) 𝓘(Real, E).tangent ∞
        (fun z : E ↦
          (TotalSpace.mk' E z (0 : E) : TangentBundle 𝓘(Real, E) E)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : E ↦ (0 : E))).mpr contDiff_const
    have hR : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real).tangent ∞
        (fun r : Real ↦
          (TotalSpace.mk' Real r (1 : Real) :
            TangentBundle 𝓘(Real, Real) Real)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : Real ↦ (1 : Real))).mpr contDiff_const
    have hpair := (hE.comp contMDiff_fst).prodMk (hR.comp contMDiff_snd)
    have hsymm : ContMDiff
        (𝓘(Real, E).tangent.prod 𝓘(Real, Real).tangent) J.tangent ∞
        ((equivTangentBundleProd 𝓘(Real, E) E
          𝓘(Real, Real) Real).symm) :=
      contMDiff_equivTangentBundleProd_symm
    with_unfolding_all exact hsymm.comp hpair
  have hvelSmooth : ContMDiffOn J I.tangent ∞
      (fun q : E × Real ↦
        (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (F q) (lVelocity (I := I) (fun s ↦ F (q.1, s)) q.2) :
            TangentBundle I M)) U := by
    have hcomp : ContMDiffOn J I.tangent ∞
        (fun q : E × Real ↦
          tangentMapWithin J I F U
            (TotalSpace.mk' (E × Real) q ((0 : E), (1 : Real)))) U :=
      htm.comp (hunit.contMDiffOn (s := U)) (fun _ hq ↦ hq)
    refine hcomp.congr ?_
    intro q hq
    have hwithin : mfderivWithin J I F U q = mfderiv J I F q :=
      mfderivWithin_of_isOpen hUopen hq
    have hdiff : MDifferentiableAt J I F q :=
      ((hF q hq).contMDiffAt (hUopen.mem_nhds hq)).mdifferentiableAt (by simp)
    have hsplit := mfderiv_prod_eq_add_apply
      (I := 𝓘(Real, E)) (I' := 𝓘(Real, Real)) (I'' := I)
      (f := F) (p := q) (v := ((0 : E), (1 : Real))) hdiff
    have hzero : mfderiv 𝓘(Real, E) I
        (fun z : E ↦ F (z, q.2)) q.1 (0 : E) = 0 := map_zero _
    rw [hzero, zero_add] at hsplit
    have hjoint : mfderiv J I F q ((0 : E), (1 : Real)) =
        lVelocity (I := I) (fun s ↦ F (q.1, s)) q.2 := by
      simpa only [lVelocity] using hsplit
    change TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
        (F q) (lVelocity (I := I) (fun s ↦ F (q.1, s)) q.2) =
      tangentMapWithin J I F U
        (TotalSpace.mk' (E × Real) q ((0 : E), (1 : Real)))
    simp only [tangentMapWithin, hwithin, hjoint]
  let P := {q : E × Real // q ∈ U}
  let timeLift : P → {t : Real // t ∈ D.carrier} := fun q ↦
    ⟨T - q.1.2 ^ 2, D.regular_subset ((hcurves q.1.1 q.2.1).2.2 q.1.2 q.2.2).1⟩
  let velLift : P → TangentBundle I M := fun q ↦
    ⟨F q.1, lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2⟩
  have htime : Continuous timeLift := by
    exact ((continuous_const.sub
      ((continuous_snd.comp continuous_subtype_val).pow 2)).subtype_mk _)
  have hvel : Continuous velLift := by
    have hvelOn := hvelSmooth.continuousOn
    rw [continuousOn_iff_continuous_domRestrict] at hvelOn
    change Continuous velLift at hvelOn
    exact hvelOn
  have hbase : Continuous (fun q : P ↦ F q.1) := by
    have hbaseOn := hF.continuousOn
    rw [continuousOn_iff_continuous_domRestrict] at hbaseOn
    change Continuous (fun q : P ↦ F q.1) at hbaseOn
    exact hbaseOn
  have hquad :=
    metricTimeBundleQuad_cont_of_metricFamilySmoothOn
      (I := I) (M := M) S.family.metric hS.smoothMetric
      (K := D.carrier) (fun _ ht ↦ ht)
  have hkin0 := hquad.comp (htime.prodMk hvel)
  have hkin : Continuous (fun q : P ↦
      (S.base.metric (T - q.1.2 ^ 2)).inner (F q.1)
        (lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2)
        (lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2)) := by
    change Continuous (fun q : P ↦
      (S.base.metric (T - q.1.2 ^ 2)).inner (F q.1)
        (lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2)
        (lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2)) at hkin0
    exact hkin0
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hscalar := hSc.continuous_subtype.comp (htime.prodMk hbase)
  have hlag : Continuous (fun q : P ↦
      (1 / 2 : Real) *
          (S.base.metric (T - q.1.2 ^ 2)).inner (F q.1)
            (lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2)
            (lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2) +
        2 * q.1.2 ^ 2 * S.scalar (T - q.1.2 ^ 2) (F q.1)) :=
    continuous_const.mul hkin |>.add
      ((continuous_const.mul
        ((continuous_snd.comp continuous_subtype_val).pow 2)).mul hscalar)
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous ((V ×ˢ K).domRestrict
    (fun q : E × Real ↦ lRegLagrangian S T (fun s ↦ alpha (q.1, s)) q.2)) at hlag
  exact hlag

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tendsto_lRegAction_lRegCurve_sequence
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : Nat → TangentSpace I x}
    {Z₀ : TangentSpace I x} {b : Nat → Real} {b₀ : Real}
    (hb₀ : 0 < b₀) (hdom : b₀ ∈ lRegDomain S T x Z₀)
    (hZ : Tendsto Z atTop (nhds Z₀))
    (hb : Tendsto b atTop (nhds b₀)) :
    Tendsto
      (fun n ↦ lRegAction S T (lRegCurve S T x (Z n)) 0 (b n))
      atTop
      (nhds (lRegAction S T (lRegCurve S T x Z₀) 0 b₀)) := by
  obtain ⟨J₀, hJ₀open, hJ₀conn, h0J₀, hb₀J₀, hchosen⟩ :=
    lRegChosen_spec S T x Z₀ hdom
  obtain ⟨V, hVopen, hZ₀V, K, hKopen, hKconn, h0K, hb₀K,
      alpha, halpha, hcurves⟩ :=
    lRegFamily_extend S hS T hJ₀open hJ₀conn h0J₀ hb₀J₀ hchosen
  have hlag := continuousOn_lRegLagrangian_variation (I := I) S hS T hVopen hKopen halpha hcurves
  obtain ⟨ε, hε, hεK⟩ := (Metric.isOpen_iff.1 hKopen) b₀ hb₀K
  let δ : Real := min (ε / 2) (b₀ / 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min (half_pos hε) (half_pos hb₀)
  have hδε : δ < ε := by
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hδb : δ < b₀ := by
    exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hb₀)
  have hZV : ∀ᶠ n in atTop, Z n ∈ V :=
    hZ.eventually (hVopen.mem_nhds hZ₀V)
  have hbδ : ∀ᶠ n in atTop, dist (b n) b₀ < δ :=
    hb.eventually (Metric.ball_mem_nhds b₀ hδ)
  have hgood : ∀ᶠ n in atTop,
      Z n ∈ V ∧ b₀ - δ < b n ∧ b n < b₀ + δ := by
    filter_upwards [hZV, hbδ] with n hnV hnδ
    rw [Real.dist_eq] at hnδ
    have hnlow := (abs_lt.mp hnδ).1
    have hnup := (abs_lt.mp hnδ).2
    exact ⟨hnV, by linarith, by linarith⟩
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hgood)
  let Zs : Nat → E := fun n ↦ Z (n + N)
  let bs : Nat → Real := fun n ↦ b (n + N)
  have htailGood (n : Nat) :
      Zs n ∈ V ∧ b₀ - δ < bs n ∧ bs n < b₀ + δ := by
    exact hN (n + N) (Nat.le_add_left N n)
  have hZs : Tendsto Zs atTop (nhds Z₀) := by
    exact (tendsto_add_atTop_iff_nat N).2 hZ
  have hbs : Tendsto bs atTop (nhds b₀) := by
    exact (tendsto_add_atTop_iff_nat N).2 hb
  have hbUpperK : b₀ + δ ∈ K := by
    apply hεK
    change dist (b₀ + δ) b₀ < ε
    rw [Real.dist_eq]
    simpa only [add_sub_cancel_left, abs_of_pos hδ] using hδε
  let Q : Set E := insert Z₀ (range Zs)
  let L : Set Real := Icc (0 : Real) (b₀ + δ)
  have hQcompact : IsCompact Q := by
    with_unfolding_all exact hZs.isCompact_insert_range
  have hLcompact : IsCompact L := by
    simpa only [L] using isCompact_Icc
  have hQV : Q ⊆ V := by
    intro z hz
    rcases hz with rfl | ⟨n, rfl⟩
    · exact hZ₀V
    · exact (htailGood n).1
  have hLK : L ⊆ K := by
    have hsub := hKconn.ordConnected.uIcc_subset h0K hbUpperK
    have hnonneg : 0 ≤ b₀ + δ := by linarith
    simpa only [L, uIcc_of_le hnonneg] using hsub
  have hcompact : IsCompact (Q ×ˢ L) := hQcompact.prod hLcompact
  have hsub : Q ×ˢ L ⊆ V ×ˢ K := prod_mono hQV hLK
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn (hlag.mono hsub)
  have hC0 : 0 ≤ C := by
    have hzeroL : (0 : Real) ∈ L := by
      exact ⟨le_rfl, by linarith⟩
    exact (norm_nonneg _).trans
      (hC (Z₀, 0) ⟨mem_insert _ _, hzeroL⟩)
  let F : E → Real → Real := fun z s ↦
    lRegLagrangian S T (fun r ↦ alpha (z, r)) s
  have hb₀L : b₀ ∈ L := by
    exact ⟨hb₀.le, by linarith⟩
  have hzeroL : (0 : Real) ∈ L := by
    exact ⟨le_rfl, by linarith⟩
  have h0bL : Set.uIcc (0 : Real) b₀ ⊆ L :=
    Set.uIcc_subset_Icc hzeroL hb₀L
  have hbsL (n : Nat) : bs n ∈ L := by
    exact ⟨by linarith [hδb, (htailGood n).2.1],
      (htailGood n).2.2.le⟩
  have hcont (z : E) (hz : z ∈ Q) :
      ContinuousOn (F z) L := by
    have hzV := hQV hz
    have hpair : ContinuousOn (fun s : Real ↦ (z, s)) L :=
      continuous_const.continuousOn.prodMk continuous_id.continuousOn
    have hc := hlag.comp hpair (fun s hs ↦ ⟨hzV, hLK hs⟩)
    simpa only [Function.comp_def, F] using hc
  have hfixed : Tendsto
      (fun n ↦ ∫ s in (0 : Real)..b₀, F (Zs n) s)
      atTop (nhds (∫ s in (0 : Real)..b₀, F Z₀ s)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (fun _ : Real ↦ C) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards with n
      have hzQ : Zs n ∈ Q := mem_insert_iff.mpr <| Or.inr ⟨n, rfl⟩
      exact ((hcont (Zs n) hzQ).mono
        (Set.uIoc_subset_uIcc.trans h0bL)).aestronglyMeasurable measurableSet_uIoc
    · filter_upwards with n
      exact ae_of_all _ fun s hs ↦ by
        have hsL : s ∈ L := h0bL (Set.uIoc_subset_uIcc hs)
        simpa only [Real.norm_eq_abs, F] using
          hC (Zs n, s)
            ⟨mem_insert_iff.mpr (Or.inr ⟨n, rfl⟩), hsL⟩
    · exact ae_of_all _ fun s hs ↦ by
        have hsL : s ∈ L := h0bL (Set.uIoc_subset_uIcc hs)
        have hpair : Tendsto (fun n ↦ (Zs n, s)) atTop
            (nhds (Z₀, s)) := hZs.prodMk_nhds tendsto_const_nhds
        have hAt : ContinuousAt
            (fun q : E × Real ↦
              lRegLagrangian S T (fun r ↦ alpha (q.1, r)) q.2) (Z₀, s) :=
          (hlag (Z₀, s) ⟨hZ₀V, hLK hsL⟩).continuousAt
            ((hVopen.prod hKopen).mem_nhds ⟨hZ₀V, hLK hsL⟩)
        have h := hAt.tendsto.comp hpair
        change Tendsto (fun n ↦ F (Zs n) s) atTop (nhds (F Z₀ s)) at h
        exact h
  have htailBound (n : Nat) :
      ‖∫ s in b₀..bs n, F (Zs n) s‖ ≤ C * |bs n - b₀| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    have hsL : s ∈ L :=
      Set.uIcc_subset_Icc hb₀L (hbsL n) (Set.uIoc_subset_uIcc hs)
    simpa only [Real.norm_eq_abs, F] using
      hC (Zs n, s) ⟨mem_insert_iff.mpr (Or.inr ⟨n, rfl⟩), hsL⟩
  have htailZero : Tendsto
      (fun n ↦ ∫ s in b₀..bs n, F (Zs n) s) atTop (nhds 0) := by
    apply squeeze_zero_norm htailBound
    have habs : Tendsto (fun n ↦ |bs n - b₀|) atTop (nhds 0) := by
      simpa only [sub_self, abs_zero] using (hbs.sub_const b₀).abs
    simpa only [mul_zero] using tendsto_const_nhds.mul habs
  have hsplit (n : Nat) :
      lRegAction S T (fun s ↦ alpha (Zs n, s)) 0 (bs n) =
        (∫ s in (0 : Real)..b₀, F (Zs n) s) +
          ∫ s in b₀..bs n, F (Zs n) s := by
    have hzQ : Zs n ∈ Q := mem_insert_iff.mpr <| Or.inr ⟨n, rfl⟩
    have h0b : IntervalIntegrable (F (Zs n)) volume 0 b₀ := by
      exact ((hcont (Zs n) hzQ).mono
        h0bL).intervalIntegrable
    have hbb : IntervalIntegrable (F (Zs n)) volume b₀ (bs n) := by
      exact ((hcont (Zs n) hzQ).mono
        (Set.uIcc_subset_Icc hb₀L (hbsL n))).intervalIntegrable
    simpa only [lRegAction, F] using
      (lRegAction_add (I := I) S T (fun s ↦ alpha (Zs n, s))
        0 b₀ (bs n) h0b hbb).symm
  have halphaLim : Tendsto
      (fun n ↦ lRegAction S T (fun s ↦ alpha (Zs n, s)) 0 (bs n))
      atTop
      (nhds (lRegAction S T (fun s ↦ alpha (Z₀, s)) 0 b₀)) := by
    have hadd := hfixed.add htailZero
    have hact' : Tendsto
        (fun n ↦ lRegAction S T (fun s ↦ alpha (Zs n, s)) 0 (bs n))
        atTop (nhds ((∫ s in (0 : Real)..b₀, F Z₀ s) + 0)) := by
      apply hadd.congr'
      filter_upwards with n
      exact (hsplit n).symm
    have hact : Tendsto
        (fun n ↦ lRegAction S T (fun s ↦ alpha (Zs n, s)) 0 (bs n))
        atTop (nhds (∫ s in (0 : Real)..b₀, F Z₀ s)) := by
      simpa only [add_zero] using hact'
    simpa only [lRegAction, F] using hact
  have hlimitEq :
      lRegAction S T (lRegCurve S T x Z₀) 0 b₀ =
        lRegAction S T (fun s ↦ alpha (Z₀, s)) 0 b₀ := by
    have heq := lRegCurve_eqOn S hS T hKopen hKconn h0K
      (hcurves Z₀ hZ₀V)
    exact lRegAction_congr (I := I) S T
      (lRegCurve S T x Z₀) (fun s ↦ alpha (Z₀, s)) 0 b₀
      (heq.mono (Set.uIoo_subset_uIcc_self.trans
        (hKconn.ordConnected.uIcc_subset h0K hb₀K)))
  have hrayShift : Tendsto
      (fun n ↦ lRegAction S T (lRegCurve S T x (Zs n)) 0 (bs n))
      atTop (nhds (lRegAction S T (lRegCurve S T x Z₀) 0 b₀)) := by
    rw [hlimitEq]
    apply halphaLim.congr'
    filter_upwards with n
    have heq := lRegCurve_eqOn S hS T hKopen hKconn h0K
      (hcurves (Zs n) (htailGood n).1)
    exact (lRegAction_congr (I := I) S T
      (lRegCurve S T x (Zs n)) (fun s ↦ alpha (Zs n, s)) 0 (bs n)
      (heq.mono (Set.uIoo_subset_uIcc_self.trans
        (hKconn.ordConnected.uIcc_subset h0K (hLK (hbsL n)))))).symm
  exact (tendsto_add_atTop_iff_nat N).1 (by
    simpa only [Zs, bs] using hrayShift)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem continuousAt_lRegAction_lRegCurve
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {b : Real}
    (hb : 0 < b) (hdom : b ∈ lRegDomain S T x Z) :
    ContinuousAt
      (fun p : E × Real ↦
        lRegAction S T (lRegCurve S T x p.1) 0 p.2)
      (Z, b) := by
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro p hp
  have hZ : Tendsto (fun n ↦ (p n).1) atTop (nhds Z) :=
    continuousAt_fst.tendsto.comp hp
  have hb' : Tendsto (fun n ↦ (p n).2) atTop (nhds b) :=
    continuousAt_snd.tendsto.comp hp
  simpa only [Function.comp_def] using
    tendsto_lRegAction_lRegCurve_sequence S hS T x hb hdom hZ hb'

end DifferentialGeometry.PDE.RicciFlow.Perelman
