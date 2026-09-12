import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Barrier
import DifferentialGeometry.Geometry.Boundary.SmoothAnnulus
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import DifferentialGeometry.Geometry.Metric.Family.Regularity.DifferentialOperator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set Filter
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance scalarZeroTopology : TopologicalSpace F.M := F.topology
local instance scalarZeroCharted : ChartedSpace H F.M := F.charted
local instance scalarZeroSmooth : IsManifold I ∞ F.M := F.smooth
local instance scalarZeroT2 : T2Space F.M := F.t2

theorem scalar_slice_zero_of_nonnegative_slab
    (hconnected : ConnectedSpace F.M) {a b t : ℝ}
    (hat : a < t) (htb : t < b) (hregular : Set.Icc a b ⊆ D.regular)
    (hnonnegative : ∀ s ∈ Set.Icc a b, ∀ y : F.M, 0 ≤ F.S.scalar s y)
    (x : F.M) (hzero : F.S.scalar t x = 0) :
    ∀ y : F.M, F.S.scalar t y = 0 := by
  let S' : SolutionOn (I := I) (M := F.M) (D.timeShift a) := F.S.timeShift a
  have hS' : IsSolutionOn (I := I) S' := isSolutionOn_timeShift (I := I) F.isSolution a
  let G : MetricConnectionFamily (I := I) (M := F.M) ℝ := flowG (I := I) S'
  let T : ℝ := t - a
  have hT : 0 < T := by
    dsimp only [T]
    linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ → F.M → ℝ, u = (fun s z => S'.scalar s z) :=
    ⟨_, rfl⟩
  have hslabreg : Set.Icc 0 T ⊆ (D.timeShift a).regular := by
    intro s hs
    have hsab : s + a ∈ Set.Icc a b := by
      refine ⟨by linarith [hs.1], ?_⟩
      dsimp only [T] at hs
      linarith [hs.2]
    exact hregular hsab
  have hslabcar : Set.Icc 0 T ⊆ (D.timeShift a).carrier :=
    fun s hs => (D.timeShift a).regular_subset (hslabreg hs)
  have hu_cont : ContinuousOn (fun p : ℝ × F.M => u p.1 p.2)
      (spacetimeSlab (M := F.M) T) := by
    have h := hS'.scalarCont.mono (Set.prod_mono hslabcar (Set.Subset.rfl))
    simpa only [hu, spacetimeSlab] using h
  have hu_nonneg : ∀ s ∈ Set.Icc 0 T, ∀ z : F.M, 0 ≤ u s z := by
    intro s hs z
    have hsab : s + a ∈ Set.Icc a b := by
      refine ⟨by linarith [hs.1], ?_⟩
      dsimp only [T] at hs
      linarith [hs.2]
    simpa only [hu, S', SolutionOn.timeShift_scalar] using hnonnegative (s + a) hsab z
  have hu_time : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ z : F.M,
      DifferentiableWithinAt ℝ (fun q => u q z) (Set.Icc 0 T) s := by
    intro s hs _ z
    simpa only [hu] using hS'.scalarTime hs hslabcar z
  have hreg' := scalarRegularityOfSolution (I := I) S' hS'
  have hu_mdiff : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ z : F.M,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (u s) z := by
    intro s hs _ z
    have h := hreg'.scalar_space s (hslabcar hs) z
    simpa only [hu] using h
  have hu_grad : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ z : F.M,
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun w : F.M => Bundle.TotalSpace.mk' E w
          (gradientFun (I := I) (G.metric s) (u s) w)) z := by
    intro s hs _ z
    simpa only [hu, G, flowG, SolutionOn.family_metric] using
      hreg'.scalar_grad s (hslabcar hs) z
  have hu_super : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ z : F.M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T
        (fun _ (y : F.M) => (0 : TangentSpace I y)) u s z := by
    intro s hs _ z
    have hsreg : s ∈ (D.timeShift a).regular := hslabreg hs
    have hderiv := scalarEvolution_of_isSolution (I := I) S' hS' G
      (fun _ => rfl) (fun _ => rfl) ⟨s, hsreg⟩ z
    have hderiv_eq : derivWithin (fun q => u q z) (Set.Icc 0 T) s =
        laplacianAt (I := I) G s (u s) z +
          2 * normSq0S (I := I) (S'.family.metric s) z 2 (S'.ricci s z) := by
      have h := hderiv.hasDerivAt ((D.timeShift a).regular_mem_nhds hsreg)
      have h2 := h.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt hs)
      simpa only [hu] using h2
    rw [parabolicOperatorWithDrift_eq, hderiv_eq]
    have hzero_drift : heatOperatorWithDrift (I := I) G s
        ((fun _ (y : F.M) => (0 : TangentSpace I y)) s) (u s) z =
        laplacianAt (I := I) G s (u s) z := by
      simp only [heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt]
    rw [hzero_drift]
    have hnorm : 0 ≤ 2 * normSq0S (I := I) (S'.family.metric s) z 2 (S'.ricci s z) :=
      mul_nonneg (by norm_num) (normSq0S_nonneg (I := I) _ z 2 _)
    linarith
  have huT : ∀ z : F.M, u T z = F.S.scalar t z := by
    intro z
    simp only [hu, S', T, SolutionOn.timeShift_scalar]
    congr 1
    ring
  have hmain : ∀ z : F.M, u T z = 0 := by
    let Q : Set F.M := {z | u T z = 0}
    have hTs : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
    have huT_cont : Continuous (u T) := by
      rw [← continuousOn_univ]
      have hmap : Set.MapsTo (fun z : F.M => (T, z)) Set.univ (spacetimeSlab (M := F.M) T) :=
        fun z _ => ⟨hTs, Set.mem_univ z⟩
      have h := hu_cont.comp (by fun_prop) hmap
      simpa only [Function.comp_def] using h
    have hQclosed : IsClosed Q := isClosed_eq huT_cont continuous_const
    have hQopen : IsOpen Q := by
      rw [isOpen_iff_mem_nhds]
      intro a haQ
      have haT0 : u T a = 0 := haQ
      by_contra ha
      let bmp : SmoothBumpFunction I a := Classical.choice inferInstance
      let Cchart : ℝ := ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ + 1
      have hCchart : 0 < Cchart := by
        dsimp only [Cchart]
        linarith [norm_nonneg (toEuclidean (E := E)).symm.toContinuousLinearMap]
      let Sset : Set E := Metric.ball (extChartAt I a a) (bmp.rIn / 2) ∩
        {z : E | ‖(toEuclidean (E := E)) (z - extChartAt I a a)‖ < bmp.rIn / (4 * Cchart)}
      have hSset_open : IsOpen Sset :=
        Metric.isOpen_ball.inter (isOpen_lt (by fun_prop) (by fun_prop))
      have haSset : extChartAt I a a ∈ Sset := by
        refine ⟨?_, ?_⟩
        · change dist (extChartAt I a a) (extChartAt I a a) < bmp.rIn / 2
          rw [dist_self]
          exact half_pos bmp.rIn_pos
        · change ‖(toEuclidean (E := E)) (extChartAt I a a - extChartAt I a a)‖ <
            bmp.rIn / (4 * Cchart)
          rw [sub_self, map_zero, norm_zero]
          exact div_pos bmp.rIn_pos (mul_pos (by norm_num) hCchart)
      let W : Set F.M := (chartAt H a).source ∩ extChartAt I a ⁻¹' Sset
      have hWopen : IsOpen W := isOpen_extChartAt_preimage a hSset_open
      have haW : a ∈ W := ⟨mem_chart_source H a, haSset⟩
      have hWnhds : W ∈ 𝓝 a := hWopen.mem_nhds haW
      have hne : ∃ c ∈ W, u T c ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact ha (Filter.mem_of_superset hWnhds hcon)
      obtain ⟨c, hcW, hcT⟩ := hne
      have hcsource : c ∈ (chartAt H a).source := hcW.1
      have hcpos : 0 < u T c :=
        lt_of_le_of_ne (hu_nonneg T hTs c) (Ne.symm hcT)
      have hc_dist_half : dist (extChartAt I a c) (extChartAt I a a) < bmp.rIn / 2 := hcW.2.1
      have hc_dist : dist (extChartAt I a c) (extChartAt I a a) < bmp.rIn := by
        linarith [bmp.rIn_pos]
      have hc_eucl_small : ‖(toEuclidean (E := E))
          (extChartAt I a c - extChartAt I a a)‖ < bmp.rIn / (4 * Cchart) := hcW.2.2
      let srad : ℝ := (bmp.rIn - dist (extChartAt I a c) (extChartAt I a a)) / (2 * Cchart)
      have hsrad : 0 < srad := by
        dsimp only [srad]
        exact div_pos (sub_pos.mpr hc_dist) (mul_pos (by norm_num) hCchart)
      have hsmall_lt_s : bmp.rIn / (4 * Cchart) < srad := by
        have hden : 0 < 4 * Cchart := mul_pos (by norm_num) hCchart
        calc
          bmp.rIn / (4 * Cchart) <
              (2 * (bmp.rIn - dist (extChartAt I a c) (extChartAt I a a))) /
                (4 * Cchart) := by
            apply (div_lt_div_iff₀ hden hden).mpr
            nlinarith [hc_dist_half]
          _ = srad := by
            dsimp only [srad]
            field_simp
            ring
      have hc_eucl : ‖(toEuclidean (E := E))
          (extChartAt I a c - extChartAt I a a)‖ < srad :=
        hc_eucl_small.trans hsmall_lt_s
      let Qc : ℝ := srad ^ 2
      have hQ : 0 < Qc := sq_pos_of_pos hsrad
      have hqaQ : SmoothBumpFunction.chartRadiusSq (I := I) a c a < Qc := by
        apply (sq_lt_sq₀ (norm_nonneg _) hsrad.le).mpr
        change ‖(toEuclidean (E := E)) (extChartAt I a a - extChartAt I a c)‖ < srad
        simpa only [map_sub, norm_sub_rev] using hc_eucl
      have hterminal : ∃ delta eta : ℝ, 0 < delta ∧ 0 < eta ∧ ∃ V ∈ 𝓝 c,
          ∀ s ∈ Set.Icc 0 T, T - delta < s → ∀ z ∈ V, eta ≤ u s z := by
        let eta : ℝ := u T c / 2
        have heta : 0 < eta := by
          dsimp only [eta]
          linarith [hcpos]
        have hpoint : (T, c) ∈ spacetimeSlab (M := F.M) T := ⟨hTs, Set.mem_univ c⟩
        have htarget : Set.Ioi eta ∈ 𝓝 (u T c) := Ioi_mem_nhds (by dsimp only [eta]; linarith)
        have hpre : (fun p : ℝ × F.M => u p.1 p.2) ⁻¹' Set.Ioi eta ∈
            nhdsWithin (T, c) (Set.Icc 0 T ×ˢ (Set.univ : Set F.M)) := by
          have h := (hu_cont (T, c) hpoint).preimage_mem_nhdsWithin htarget
          simpa only [spacetimeSlab] using h
        rcases mem_nhdsWithin_prod_iff.mp hpre with ⟨U, hU, V, hV, hUV⟩
        rcases Metric.mem_nhdsWithin_iff.mp hU with ⟨delta, hdelta, hball⟩
        have hV' : V ∈ 𝓝 c := by simpa using hV
        refine ⟨delta, eta, hdelta, heta, V, hV', ?_⟩
        intro s hs hsclose z hz
        have hsball : s ∈ Metric.ball T delta := by
          change dist s T < delta
          rw [Real.dist_eq]
          rw [abs_of_nonpos (sub_nonpos.mpr hs.2)]
          linarith
        have hUmem : s ∈ U := hball ⟨hsball, hs⟩
        have htx : (s, z) ∈ U ×ˢ V := ⟨hUmem, hz⟩
        exact le_of_lt (hUV htx)
      obtain ⟨delta, eta, hdelta, heta, V, hV, hlocalV⟩ := hterminal
      obtain ⟨r, hr, hrV⟩ :=
        SmoothBumpFunction.exists_cutoffChartRadiusSq_sublevel_subset (I := I) bmp hcsource hQ hV
      let rho : F.M → ℝ := SmoothBumpFunction.cutoffChartRadiusSq (I := I) bmp c Qc
      have hrho : ContMDiff I 𝓘(ℝ, ℝ) ∞ rho :=
        SmoothBumpFunction.cutoffChartRadiusSq_contMDiff (I := I) bmp Qc
      have hrho_nonneg : ∀ z : F.M, 0 ≤ rho z :=
        SmoothBumpFunction.cutoffChartRadiusSq_nonneg (I := I) bmp hQ.le
      have hbc : bmp c = 1 := bmp.one_of_dist_le hcsource hc_dist.le
      have hrhoc : rho c = 0 := by
        simp [rho, SmoothBumpFunction.cutoffChartRadiusSq, SmoothBumpFunction.chartRadiusSq,
          hbc]
      have hrhoa : rho a = SmoothBumpFunction.chartRadiusSq (I := I) a c a := by
        simp [rho, SmoothBumpFunction.cutoffChartRadiusSq]
      let R : ℝ := (rho a + Qc) / 2
      have hrhoaR : rho a < R := by
        dsimp only [R]
        rw [hrhoa]
        linarith
      have hRQ : R < Qc := by
        dsimp only [R]
        rw [hrhoa]
        linarith
      have hR : 0 < R := lt_of_le_of_lt (hrho_nonneg a) hrhoaR
      have hcompactK : IsCompact {z : F.M | rho z ≤ R} := by
        simpa only [rho] using
          SmoothBumpFunction.isCompact_sublevel_cutoffChartRadiusSq (I := I) bmp hRQ
      have hgrad_ne : ∀ s ∈ Set.Icc 0 T, ∀ z : F.M,
          r ≤ rho z → rho z ≤ R → gradientFun (I := I) (G.metric s) rho z ≠ 0 := by
        intro s _ z hzr hzR
        have hmidR : R < (R + Qc) / 2 := by linarith
        have hmidQ : (R + Qc) / 2 < Qc := by linarith
        have hltmid : rho z < (R + Qc) / 2 := hzR.trans_lt hmidR
        have hrad := SmoothBumpFunction.pos_and_chartRadiusSq_lt_of_cutoffChartRadiusSq_lt
          (I := I) bmp hmidQ hltmid
        have hbz : bmp z ≠ 0 := ne_of_gt hrad.1
        have hzsource : z ∈ (chartAt H a).source := by
          apply bmp.support_subset_source
          simpa [Function.mem_support] using hbz
        have hzcore : dist (extChartAt I a z) (extChartAt I a a) < bmp.rIn := by
          apply SmoothBumpFunction.dist_lt_rIn_of_chartRadiusSq_lt (I := I) bmp hc_dist
          simpa only [Qc, srad, Cchart] using hrad.2
        have hzc : z ≠ c := by
          intro heq
          subst heq
          rw [hrhoc] at hzr
          linarith
        exact SmoothBumpFunction.cutoffChartRadiusSq_gradient_ne_zero (I := I) (G.metric s)
          bmp hcsource hzsource hzcore hzc Qc
      have hlocal : ∀ s ∈ Set.Icc 0 T, T - delta < s → ∀ z : F.M,
          rho z < r → eta ≤ u s z := by
        intro s hs hsclose z hz
        exact hlocalV s hs hsclose z (hrV hz)
      let K : Set F.M := {z : F.M | r ≤ rho z ∧ rho z ≤ R}
      let Sslab : Set (ℝ × F.M) := Set.Icc 0 T ×ˢ K
      let qfun : ℝ × F.M → ℝ := fun p => (G.metric p.1).inner p.2
        (gradientFun (I := I) (G.metric p.1) rho p.2)
        (gradientFun (I := I) (G.metric p.1) rho p.2)
      let ell : ℝ × F.M → ℝ := fun p =>
        |heatOperatorWithDrift (I := I) G p.1
          (fun y : F.M => (0 : TangentSpace I y)) rho p.2|
      have hKcompact : IsCompact K := by
        apply hcompactK.of_isClosed_subset
          ((isClosed_le continuous_const hrho.continuous).inter
            (isClosed_le hrho.continuous continuous_const))
        intro z hz
        exact hz.2
      have hSslab : IsCompact Sslab := isCompact_Icc.prod hKcompact
      have hq_cont : ContinuousOn qfun Sslab := by
        have h := G.gradient_norm_sq_continuousOn hS'.smoothMetric hslabreg hrho
        exact h.mono (fun p hp => ⟨hp.1, Set.mem_univ p.2⟩)
      have hell_cont : ContinuousOn ell Sslab := by
        have hlap : ContinuousOn (fun p : ℝ × F.M =>
            heatOperatorWithDrift (I := I) G p.1
              (fun y : F.M => (0 : TangentSpace I y)) rho p.2)
            (Set.Icc 0 T ×ˢ (Set.univ : Set F.M)) := by
          simpa only [heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt] using
            G.laplacianAt_continuousOn hS'.smoothMetric hslabreg (uniqueDiffOn_Icc hT)
              (fun _ _ => rfl) hrho
        exact (hlap.abs).mono (fun p hp => ⟨hp.1, Set.mem_univ p.2⟩)
      obtain ⟨m, B, hm, hB, hgrad_lower, hheat_upper⟩ :
          ∃ m B : ℝ, 0 < m ∧ 0 ≤ B ∧
            (∀ p ∈ Sslab, m ≤ qfun p) ∧
            (∀ p ∈ Sslab,
              heatOperatorWithDrift (I := I) G p.1
                (fun y : F.M => (0 : TangentSpace I y)) rho p.2 ≤ B) := by
        by_cases hKne : K.Nonempty
        · have hSne : Sslab.Nonempty := by
            obtain ⟨z, hz⟩ := hKne
            exact ⟨(0, z), ⟨⟨le_rfl, hT.le⟩, hz⟩⟩
          obtain ⟨pm, hpm, hpmin⟩ := hSslab.exists_isMinOn hSne hq_cont
          obtain ⟨pB, hpB, hpBmax⟩ := hSslab.exists_isMaxOn hSne hell_cont
          have hqm : 0 < qfun pm :=
            (G.metric pm.1).pos pm.2 _ (hgrad_ne pm.1 hpm.1 pm.2 hpm.2.1 hpm.2.2)
          refine ⟨qfun pm, ell pB, hqm, by positivity, hpmin, ?_⟩
          intro p hp
          have habs := hpBmax hp
          have hself := le_abs_self
            (heatOperatorWithDrift (I := I) G p.1
              (fun y : F.M => (0 : TangentSpace I y)) rho p.2)
          change |heatOperatorWithDrift (I := I) G p.1
              (fun y : F.M => (0 : TangentSpace I y)) rho p.2| ≤ ell pB at habs
          exact hself.trans habs
        · refine ⟨1, 0, by positivity, le_rfl, ?_, ?_⟩
          · intro p hp
            exact (hKne ⟨p.2, hp.2⟩).elim
          · intro p hp
            exact (hKne ⟨p.2, hp.2⟩).elim
      let kappa : ℝ := max (R / T ^ 2) (R / delta ^ 2) + 1
      have hT_sq : 0 < T ^ 2 := sq_pos_of_pos hT
      have hdelta_sq : 0 < delta ^ 2 := sq_pos_of_pos hdelta
      have hkappa : 0 < kappa := by
        dsimp only [kappa]
        linarith [le_max_left (R / T ^ 2) (R / delta ^ 2), div_pos hR hT_sq]
      have hinit : R ≤ kappa * T ^ 2 := by
        apply le_of_lt ((div_lt_iff₀ hT_sq).mp ?_)
        dsimp only [kappa]
        linarith [le_max_left (R / T ^ 2) (R / delta ^ 2)]
      have htime : R ≤ kappa * delta ^ 2 := by
        apply le_of_lt ((div_lt_iff₀ hdelta_sq).mp ?_)
        dsimp only [kappa]
        linarith [le_max_right (R / T ^ 2) (R / delta ^ 2)]
      let alpha : ℝ := (2 * kappa * T + B) / m + 1
      have hnum : 0 ≤ 2 * kappa * T + B := by positivity
      have halpha : 0 < alpha := by
        dsimp only [alpha]
        have := div_nonneg hnum hm.le
        linarith
      have hdom : 2 * kappa * T + B ≤ alpha * m := by
        apply le_of_lt ((div_lt_iff₀ hm).mp ?_)
        dsimp only [alpha]
        linarith
      have hpos : 0 < u T a :=
        scalar_strong_maximum_principle_of_compact_sublevel_barrier (I := I) G hT
          (fun _ (y : F.M) => (0 : TangentSpace I y)) u hu_cont hu_nonneg hu_time hu_mdiff
          hu_grad hu_super
          hrho hrho_nonneg hR hdelta heta hlocal hcompactK
          (m := m) (B := B) (kappa := kappa) (alpha := alpha)
          (fun s hs hspos z hzr hzR => hgrad_lower (s, z) ⟨hs, hzr, hzR⟩)
          (fun s hs hspos z hzr hzR => hheat_upper (s, z) ⟨hs, hzr, hzR⟩)
          hkappa hinit htime halpha hdom hrhoaR
      exact absurd haT0 (ne_of_gt hpos)
    have hQuniv : Q = Set.univ :=
      IsClopen.eq_univ ⟨hQclosed, hQopen⟩
        ⟨x, by simp only [Q, Set.mem_ofPred_eq, huT x, hzero]⟩
    intro z
    have hzQ : z ∈ Q := by rw [hQuniv]; exact Set.mem_univ z
    simpa only [Q, Set.mem_ofPred_eq] using hzQ
  intro y
  rw [← huT y]
  exact hmain y

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
