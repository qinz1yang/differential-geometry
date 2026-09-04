import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.TimeParameter

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology Interval

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

omit [NeZero (Module.finrank Real E)] in
private theorem rampDown_add {L : Real} (hL : 0 < L) (z w : E) :
    timeH1.rampDown L (z + w) =
      timeH1.rampDown L z + timeH1.rampDown L w := by
  apply timeH1.ext
  · rw [← timeH1.toFun_zero (timeH1.rampDown L (z + w)),
      timeH1.init_add, ← timeH1.toFun_zero (timeH1.rampDown L z),
      ← timeH1.toFun_zero (timeH1.rampDown L w),
      timeH1.rampDown_zero hL, timeH1.rampDown_zero hL,
      timeH1.rampDown_zero hL]
  · rw [timeH1.deriv_add]
    apply Lp.ext
    filter_upwards [timeH1.rampDown_deriv hL (z + w),
      timeH1.rampDown_deriv hL z, timeH1.rampDown_deriv hL w,
      Lp.coeFn_add (timeH1.rampDown L z).deriv
        (timeH1.rampDown L w).deriv] with s hzw hz hw hadd
    rw [hzw, hadd, Pi.add_apply, hz, hw, smul_add]

private def rampDownLM (L : Real) (hL : 0 < L) :
    E →ₗ[Real] timeH1 E L where
  toFun := timeH1.rampDown L
  map_add' := rampDown_add hL
  map_smul' := timeH1.rampDown_smul hL

omit [NeZero (Module.finrank Real E)] in
omit [FiniteDimensional ℝ E] in
private theorem toFun_cast {a b : Real} (h : a = b) (v : timeH1 E b) :
    ((h.symm ▸ v : timeH1 E a).toFun) = v.toFun := by
  subst b
  rfl

omit [NeZero (Module.finrank Real E)] in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem tendsto_cast {a b : Real} (h : a = b)
    (v : Nat → timeH1 E b) (u : timeH1 E b)
    (hv : Tendsto v atTop (nhds u)) :
    Tendsto (fun n ↦ h.symm ▸ v n) atTop (nhds (h.symm ▸ u)) := by
  subst b
  exact hv

omit [NeZero (Module.finrank Real E)] in
private theorem rampDown_tendsto {L : Real} (hL : 0 < L)
    {z : Nat → E} {z₀ : E} (hz : Tendsto z atTop (nhds z₀)) :
    Tendsto (fun n ↦ timeH1.rampDown L (z n)) atTop
      (nhds (timeH1.rampDown L z₀)) := by
  exact (LinearMap.continuous_of_finiteDimensional
    (rampDownLM L hL)).continuousAt.tendsto.comp hz

omit [NeZero (Module.finrank Real E)] in
omit [FiniteDimensional ℝ E] in
private theorem h1_uniform
    {L : Real} (v : Nat → timeH1 E L) (u : timeH1 E L)
    (hv : Tendsto v atTop (nhds u)) :
    TendstoUniformly
      (fun n (r : Icc (0 : Real) L) ↦ (v n).toFun r.1)
      (fun r ↦ u.toFun r.1) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  let C : Real := 1 + Real.sqrt L
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hsub : Tendsto (fun n ↦ u - v n) atTop (nhds 0) := by
    simpa only [sub_self] using (tendsto_const_nhds.sub hv :
      Tendsto (fun n ↦ u - v n) atTop (nhds (u - u)))
  have hnorm : Tendsto (fun n ↦ ‖u - v n‖) atTop (nhds 0) := by
    change Tendsto (norm ∘ fun n ↦ u - v n) atTop (nhds 0)
    simpa only [norm_zero] using
      continuous_norm.tendsto (0 : timeH1 E L) |>.comp hsub
  have hsmall : ∀ᶠ n in atTop, ‖u - v n‖ < ε / C :=
    hnorm.eventually (Iio_mem_nhds (div_pos hε hC))
  filter_upwards [hsmall] with n hn
  intro r
  have hfun : (u - v n).toFun r.1 = u.toFun r.1 - (v n).toFun r.1 := by
    rw [sub_eq_add_neg, timeH1.toFun_add u (-v n) r.2]
    have hneg := timeH1.toFun_smul (-1 : Real) (v n) r.2
    simpa only [neg_one_smul, sub_eq_add_neg] using
      congrArg (u.toFun r.1 + ·) hneg
  rw [dist_eq_norm, ← hfun]
  calc
    ‖(u - v n).toFun r.1‖ ≤ C * ‖u - v n‖ :=
      (u - v n).norm_toFun_le_norm r.2
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hn hC
    _ = ε := by field_simp

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
private theorem eventually_mem_buf
    {A : Type*} (f : A → E) (v : Nat → A → E) (K : Set E)
    (hfc : IsCompact (range f)) (hfK : ∀ r, f r ∈ interior K)
    (hv : TendstoUniformly v f atTop) :
    ∀ᶠ n in atTop, ∀ r, v n r ∈ K := by
  obtain ⟨δ, hδ, hthick⟩ :=
    hfc.exists_thickening_subset_open isOpen_interior (by
      rintro _ ⟨r, rfl⟩
      exact hfK r)
  have hclose := (Metric.tendstoUniformly_iff.mp hv) δ hδ
  filter_upwards [hclose] with n hn
  intro r
  apply interior_subset
  apply hthick
  exact Metric.mem_thickening_iff.mpr
    ⟨f r, mem_range_self r, by simpa only [dist_comm] using hn r⟩

omit [NeZero (Module.finrank Real E)] [T2Space M] in
omit [CompactSpace M] in
theorem chart_head_act_lim
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a c : Real) (hac : a < c) (p : M) (gamma : Real → M)
    (u₀ : timeH1 E (c - a))
    (hsrc₀ : MapsTo gamma (Icc a c) (chartAt H p).source)
    (hrep₀ : EqOn u₀.toFun (fun r ↦ extChartAt I p (gamma (a + r)))
      (Icc (0 : Real) (c - a)))
    (z : Nat → E) (hz : Tendsto z atTop (nhds 0))
    (K : Set E) (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I p).target)
    (hK : ∀ n (r : Icc (0 : Real) (c - a)),
      (u₀ + timeH1.rampDown (c - a) (z n)).toFun r.1 ∈ K)
    (hK₀ : ∀ r : Icc (0 : Real) (c - a), u₀.toFun r.1 ∈ K)
    (hreg : ∀ s ∈ Icc a c, T - s ^ 2 ∈ D.regular) :
    Tendsto
      (fun n ↦ lRegAction S T
        (fun s ↦ (extChartAt I p).symm
          ((u₀ + timeH1.rampDown (c - a) (z n)).toFun (s - a))) a c)
      atTop (nhds (lRegAction S T gamma a c)) := by
  let v : Nat → timeH1 E (c - a) := fun n ↦
    u₀ + timeH1.rampDown (c - a) (z n)
  let beta : Nat → Real → M := fun n s ↦
    (extChartAt I p).symm ((v n).toFun (s - a))
  let beta₀ : Real → M := fun s ↦
    (extChartAt I p).symm (u₀.toFun (s - a))
  have hL : 0 < c - a := sub_pos.mpr hac
  have hv : Tendsto v atTop (nhds u₀) := by
    have hr := rampDown_tendsto (E := E) hL hz
    have hr₀ : timeH1.rampDown (c - a) (0 : E) = 0 := by
      simpa only [zero_smul] using
        timeH1.rampDown_smul hL (0 : Real) (0 : E)
    simpa only [v, hr₀, add_zero] using tendsto_const_nhds.add hr
  have hcoord := h1_uniform v u₀ hv
  have hsymm : UniformContinuousOn (extChartAt I p).symm K :=
    hKc.uniformContinuousOn_of_continuous <|
      (continuousOn_extChartAt_symm p).mono (hKchart.trans interior_subset)
  have hunif : TendstoUniformly
      (fun n (s : Icc a c) ↦ beta n s.1)
      (fun s ↦ beta₀ s.1) atTop := by
    have hshift : MapsTo (fun s : Icc a c ↦ s.1 - a)
        univ (Icc (0 : Real) (c - a)) := by
      intro s _
      exact ⟨sub_nonneg.mpr s.2.1, sub_le_sub_right s.2.2 a⟩
    have hc' := hcoord.comp (fun s : Icc a c ↦
      ⟨s.1 - a, hshift (mem_univ s)⟩)
    apply UniformContinuousOn.comp_tendstoUniformly
      (s := K) (F := fun n (s : Icc a c) ↦ (v n).toFun (s.1 - a))
      (f := fun s ↦ u₀.toFun (s.1 - a))
    · exact fun n s ↦ hK n ⟨s.1 - a, hshift (mem_univ s)⟩
    · exact fun s ↦ hK₀ ⟨s.1 - a, hshift (mem_univ s)⟩
    · exact hsymm
    · simpa only [beta, beta₀, Function.comp_def] using hc'
  have hcont (n : Nat) : ContinuousOn (beta n) (Icc a c) := by
    have hcoordCont : ContinuousOn (fun s ↦ (v n).toFun (s - a))
        (Icc a c) :=
      (v n).continuousOn_toFun.comp (continuous_sub_right a).continuousOn
        (fun s hs ↦ ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩)
    exact (continuousOn_extChartAt_symm p).comp hcoordCont
      (fun s hs ↦ interior_subset (hKchart (hK n ⟨s - a,
        ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩⟩)))
  have hsrc (n : Nat) : MapsTo (beta n) (Icc a c)
      (chartAt H p).source := by
    intro s hs
    rw [← extChartAt_source (I := I) p]
    exact (extChartAt I p).map_target
      (interior_subset (hKchart (hK n ⟨s - a,
        ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩⟩)))
  have hrep (n : Nat) : EqOn (v n).toFun
      (fun r ↦ extChartAt I p (beta n (a + r)))
      (Icc (0 : Real) (c - a)) := by
    intro r hr
    simp only [beta, add_sub_cancel_left]
    exact ((extChartAt I p).right_inv
      (interior_subset (hKchart (hK n ⟨r, hr⟩)))).symm
  have hsrcLim : MapsTo beta₀ (Icc a c)
      (chartAt H p).source := by
    intro s hs
    rw [← extChartAt_source (I := I) p]
    exact (extChartAt I p).map_target
      (interior_subset (hKchart (hK₀ ⟨s - a,
        ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩⟩)))
  have hrepLim : EqOn u₀.toFun
      (fun r ↦ extChartAt I p (beta₀ (a + r)))
      (Icc (0 : Real) (c - a)) := by
    intro r hr
    simp only [beta₀, add_sub_cancel_left]
    exact ((extChartAt I p).right_inv
      (interior_subset (hKchart (hK₀ ⟨r, hr⟩)))).symm
  let t : Fin 2 → Real := ![a, c]
  have ht0 : t 0 = a := rfl
  have ht1 : t (Fin.last 1) = c := rfl
  have htLen : partitionIntervalLength t 0 = c - a := by
    simp [partitionIntervalLength, t]
  let vt (n : Nat) : timeH1 E (partitionIntervalLength t 0) := htLen.symm ▸ v n
  let u₀t : timeH1 E (partitionIntervalLength t 0) := htLen.symm ▸ u₀
  let vtFin : (i : Fin 1) → Nat → timeH1 E (partitionIntervalLength t i) :=
    Fin.cases vt fun k ↦ Fin.elim0 k
  let u₀Fin : (i : Fin 1) → timeH1 E (partitionIntervalLength t i) :=
    Fin.cases u₀t fun k ↦ Fin.elim0 k
  have htmono : Monotone t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [t, hac.le]
  have hlim := lAction_h1_lim (I := I) S hMet hSc T a c t htmono
    ht0 ht1 (fun _ ↦ p) beta beta₀ vtFin u₀Fin
    (fun i n ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change MapsTo (beta n) (Icc a c) (chartAt H p).source
      exact hsrc n)
    (fun i n ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      intro r hr
      have hr' : r ∈ Icc (0 : Real) (c - a) := by
        rw [← htLen]
        exact hr
      change (vt n).toFun r = extChartAt I p (beta n (t 0 + r))
      rw [toFun_cast htLen (v n), ht0]
      exact hrep n hr')
    (fun i ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change MapsTo beta₀ (Icc a c) (chartAt H p).source
      exact hsrcLim)
    (fun i ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      intro r hr
      have hr' : r ∈ Icc (0 : Real) (c - a) := by
        rw [← htLen]
        exact hr
      change u₀t.toFun r = extChartAt I p (beta₀ (t 0 + r))
      rw [toFun_cast htLen u₀, ht0]
      exact hrepLim hr')
    (fun _ ↦ K) (fun _ ↦ hKc) (fun _ ↦ hKchart)
    (fun i n r ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hr' : r.val ∈ Icc (0 : Real) (c - a) := by
        rw [← htLen]
        exact r.property
      change (vt n).toFun r.1 ∈ K
      rw [toFun_cast htLen (v n)]
      exact hK n ⟨r.val, hr'⟩)
    (fun i r ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hr' : r.val ∈ Icc (0 : Real) (c - a) := by
        rw [← htLen]
        exact r.property
      change u₀t.toFun r.1 ∈ K
      rw [toFun_cast htLen u₀]
      exact hK₀ ⟨r.val, hr'⟩)
    (fun i ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change Tendsto vt atTop (nhds u₀t)
      exact tendsto_cast htLen v u₀ hv)
    hcont hunif hreg
  have heq : EqOn beta₀ gamma (Icc a c) := by
    intro s hs
    apply (extChartAt I p).injOn
    · simpa only [extChartAt_source] using hsrcLim hs
    · rw [extChartAt_source]
      exact hsrc₀ hs
    · calc
        extChartAt I p (beta₀ s) = u₀.toFun (s - a) :=
          (extChartAt I p).right_inv
            (interior_subset (hKchart (hK₀ ⟨s - a,
              ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩⟩)))
        _ = extChartAt I p (gamma (a + (s - a))) :=
          hrep₀ ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩
        _ = extChartAt I p (gamma s) := by
          congr 2
          ring
  have heqAct : lRegAction S T beta₀ a c = lRegAction S T gamma a c :=
    lRegAction_congr (I := I) S T beta₀ gamma a c (by
      have heq' : EqOn beta₀ gamma (uIcc a c) := by
        simpa only [uIcc_of_le hac.le] using heq
      exact heq'.mono uIoo_subset_uIcc_self)
  rw [heqAct] at hlim
  simpa only [beta, v] using hlim

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] in
theorem lCost_lt_x_event
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T t₀ t₁ tau : Real) (htau : 0 < tau)
    (htime : Icc t₀ t₁ ⊆ D.carrier)
    (hback : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ Icc t₀ t₁)
    (x y : M) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha)
    (hstart : alpha 0 = x) (hend : alpha (Real.sqrt tau) = y)
    (hreg : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ D.regular)
    (A : Real) (hA : lRegAction S T alpha 0 (Real.sqrt tau) < A)
    (q : Nat → M) (hq : Tendsto q atTop (nhds x)) :
    ∀ᶠ n in atTop, lCost S T (q n) y tau < A := by
  classical
  let b : Real := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hxSrc : alpha 0 ∈ (chartAt H x).source := by
    rw [hstart]
    exact mem_chart_source H x
  obtain ⟨c, hc, hcb₂, hsrcHead⟩ :=
    DifferentialGeometry.Geometry.exists_chart_initial_segment (H := H)
      (a := (0 : Real)) (b := b / 2) (half_pos hb)
      (halpha.continuous.continuousOn.mono (Icc_subset_Icc_right (half_le_self hb.le)))
      hxSrc
  have hcb : c < b := lt_of_le_of_lt hcb₂ (half_lt_self hb)
  let gamma : Real → M := fun r ↦ alpha r
  have hgamma : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc (0 : Real) c) := halpha.contMDiffOn
  have hgammaSrc : MapsTo gamma (Icc (0 : Real) c)
      (chartAt H x).source := hsrcHead
  let u₀ : timeH1 E c := chartTimeH1 I hc.le x gamma hgamma hgammaSrc
  have hrep₀ : EqOn u₀.toFun (fun r ↦ extChartAt I x (alpha r))
      (Icc (0 : Real) c) := by
    have hout := chartTimeH1_toFun I hc.le x gamma hgamma hgammaSrc
    change EqOn u₀.toFun (fun r ↦ extChartAt I x (alpha r))
      (Icc (0 : Real) c)
    with_unfolding_all exact hout
  have htar₀ (r : Icc (0 : Real) c) :
      u₀.toFun r.1 ∈ (extChartAt I x).target := by
    rw [hrep₀ r.2]
    exact (extChartAt I x).map_source (by
      rw [extChartAt_source]
      exact hgammaSrc r.2)
  obtain ⟨K, hKc, _hKclosed, hintoK, hKtar⟩ :=
    exists_compact_closed_between
      (isCompact_Icc.image_of_continuousOn u₀.continuousOn_toFun)
      (isOpen_extChartAt_target (I := I) x)
      (by rintro _ ⟨r, hr, rfl⟩; exact htar₀ ⟨r, hr⟩)
  have hKchart : K ⊆ interior (extChartAt I x).target := by
    simpa only [(isOpen_extChartAt_target (I := I) x).interior_eq] using hKtar
  have hK₀ (r : Icc (0 : Real) c) : u₀.toFun r.1 ∈ K :=
    interior_subset (hintoK ⟨r.1, r.2, rfl⟩)
  have hqSrc : ∀ᶠ n in atTop, q n ∈ (chartAt H x).source :=
    hq.eventually ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  let z : Nat → E := fun n ↦ extChartAt I x (q n) - extChartAt I x x
  have hz : Tendsto z atTop (nhds 0) := by
    have hcq := (continuousAt_extChartAt (I := I) x).tendsto.comp hq
    have hcst : Tendsto (fun _ : Nat ↦ extChartAt I x x) atTop
        (nhds (extChartAt I x x)) := tendsto_const_nhds
    simpa only [z, Function.comp_apply, sub_self] using hcq.sub hcst
  let v : Nat → timeH1 E c := fun n ↦ u₀ + timeH1.rampDown c (z n)
  have hv : Tendsto v atTop (nhds u₀) := by
    have hr := rampDown_tendsto (E := E) hc hz
    have hr₀ : timeH1.rampDown c (0 : E) = 0 := by
      simpa only [zero_smul] using timeH1.rampDown_smul hc (0 : Real) (0 : E)
    simpa only [v, hr₀, add_zero] using tendsto_const_nhds.add hr
  have hcoord := h1_uniform v u₀ hv
  have hu₀Range : IsCompact
      (range fun r : Icc (0 : Real) c ↦ u₀.toFun r.1) := by
    rw [← image_univ]
    exact isCompact_univ.image_of_continuousOn
      (u₀.continuousOn_toFun.comp continuous_subtype_val.continuousOn
        (fun _ _ ↦ Subtype.property _))
  have hvK : ∀ᶠ n in atTop, ∀ r : Icc (0 : Real) c, (v n).toFun r.1 ∈ K :=
    eventually_mem_buf (fun r : Icc (0 : Real) c ↦ u₀.toFun r.1)
      (fun n r ↦ (v n).toFun r.1) K hu₀Range
      (fun r ↦ hintoK ⟨r.1, r.2, rfl⟩) hcoord
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hqSrc.and hvK)
  let q' : Nat → M := fun n ↦ q (n + N)
  let z' : Nat → E := fun n ↦ z (n + N)
  have hq'Src (n : Nat) : q' n ∈ (chartAt H x).source :=
    (hN _ (Nat.le_add_left N n)).1
  have hz' : Tendsto z' atTop (nhds 0) := hz.comp (tendsto_add_atTop_nat N)
  have hv'K (n : Nat) (r : Icc (0 : Real) c) :
      (u₀ + timeH1.rampDown c (z' n)).toFun r.1 ∈ K := by
    simpa only [v, z'] using (hN _ (Nat.le_add_left N n)).2 r
  let beta : Nat → Real → M := fun n s ↦
    (extChartAt I x).symm ((u₀ + timeH1.rampDown c (z' n)).toFun s)
  have hheadLim : Tendsto (fun n ↦ lRegAction S T (beta n) 0 c) atTop
      (nhds (lRegAction S T alpha 0 c)) := by
    let u₀' : timeH1 E (c - 0) := (sub_zero c).symm ▸ u₀
    have hu₀' : u₀'.toFun = u₀.toFun := by
      exact toFun_cast (sub_zero c) u₀
    have hrep₀' : EqOn u₀'.toFun
        (fun r ↦ extChartAt I x (alpha (0 + r)))
        (Icc (0 : Real) (c - 0)) := by
      rw [hu₀']
      simpa only [sub_zero, zero_add] using hrep₀
    have hv'K' : ∀ n (r : Icc (0 : Real) (c - 0)),
        (u₀' + timeH1.rampDown (c - 0) (z' n)).toFun r.1 ∈ K := by
      intro n r
      have hr : r.1 ∈ Icc (0 : Real) c := by simpa only [sub_zero] using r.2
      have h := hv'K n ⟨r.1, hr⟩
      rw [timeH1.toFun_add _ _ r.2,
        timeH1.rampDown_apply (by simpa only [sub_zero] using hc.le) (z' n) r.2,
        hu₀']
      rw [timeH1.toFun_add _ _ hr, timeH1.rampDown_apply hc.le (z' n) hr] at h
      simpa only [sub_zero] using h
    have hK₀' : ∀ r : Icc (0 : Real) (c - 0), u₀'.toFun r.1 ∈ K := by
      intro r
      rw [hu₀']
      exact hK₀ ⟨r.1, by simpa only [sub_zero] using r.2⟩
    have hlim :=
      chart_head_act_lim (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
        T 0 c hc x alpha u₀' hsrcHead hrep₀' z' hz' K hKc hKchart
        hv'K' hK₀' (fun s hs ↦ hreg s ⟨hs.1, hs.2.trans hcb.le⟩)
    have hactEq (n : Nat) :
        lRegAction S T
          (fun s ↦ (extChartAt I x).symm
            ((u₀' + timeH1.rampDown (c - 0) (z' n)).toFun (s - 0))) 0 c =
          lRegAction S T (beta n) 0 c := by
      apply lRegAction_congr (I := I) S T _ _ 0 c
      intro s hs
      have hs' : s ∈ Ioo (0 : Real) c := by
        simpa only [uIoo_of_le hc.le] using hs
      have hsc : s ∈ Icc (0 : Real) c := ⟨hs'.1.le, hs'.2.le⟩
      have hsL : s - 0 ∈ Icc (0 : Real) (c - 0) := by
        simpa only [sub_zero] using hsc
      simp only [beta]
      congr 1
      rw [timeH1.toFun_add _ _ hsL,
        timeH1.rampDown_apply (by simpa only [sub_zero] using hc.le) (z' n) hsL,
        hu₀']
      rw [timeH1.toFun_add _ _ hsc, timeH1.rampDown_apply hc.le (z' n) hsc]
      simp only [sub_zero]
    have hfun : (fun n ↦ lRegAction S T
        (fun s ↦ (extChartAt I x).symm
          ((u₀' + timeH1.rampDown (c - 0) (z' n)).toFun (s - 0))) 0 c) =
        (fun n ↦ lRegAction S T (beta n) 0 c) := funext hactEq
    rw [hfun] at hlim
    exact hlim
  have hu₀c1 : ContDiffOn Real 1 u₀.toFun (Icc (0 : Real) c) := by
    exact (chartCoord_contDiff I x gamma hgamma hgammaSrc).congr
      (fun r hr ↦ by simpa only [gamma, Function.comp_apply] using hrep₀ hr)
  have hbetaC1 (n : Nat) : ContMDiffOn
      (modelWithCornersSelf Real Real) I 1 (beta n) (Icc (0 : Real) c) := by
    let w₀ : timeH1 E c := u₀ + timeH1.rampDown c (z' n)
    have hwC1 : ContDiffOn Real 1 w₀.toFun (Icc (0 : Real) c) := by
      have hrampC1 : ContDiffOn Real 1
          (fun r : Real ↦ ((c - r) / c) • z' n) (Icc (0 : Real) c) :=
        (((contDiff_const.sub contDiff_id).div_const c).smul_const
          (z' n)).contDiffOn
      apply (hu₀c1.add hrampC1).congr
      intro r hr
      rw [timeH1.toFun_add _ _ hr, timeH1.rampDown_apply hc.le (z' n) hr]
    let w : timeH1 E (c - 0) := (sub_zero c).symm ▸ w₀
    have hwfun : w.toFun = w₀.toFun := toFun_cast (sub_zero c) w₀
    apply curve_c1_local I x (beta n) w
    · intro s hs
      rw [← extChartAt_source (I := I) x]
      exact (extChartAt I x).map_target
        (interior_subset (hKchart (hv'K n ⟨s, hs⟩)))
    · intro r hr
      rw [hwfun]
      simp only [beta, zero_add]
      exact ((extChartAt I x).right_inv
        (interior_subset (hKchart (hv'K n
          ⟨r, by simpa only [sub_zero] using hr⟩)))).symm
    · rw [hwfun]
      simpa only [sub_zero] using hwC1
  have hbetaSrc (n : Nat) : MapsTo (beta n) (Icc (0 : Real) c)
      (chartAt H x).source := by
    intro s hs
    rw [← extChartAt_source (I := I) x]
    exact (extChartAt I x).map_target
      (interior_subset (hKchart (hv'K n ⟨s, hs⟩)))
  have hbeta₀ (n : Nat) : beta n 0 = q' n := by
    apply (extChartAt I x).injOn
    · simpa only [extChartAt_source] using hbetaSrc n ⟨le_rfl, hc.le⟩
    · rw [extChartAt_source]
      exact hq'Src n
    · have hright : extChartAt I x (beta n 0) =
          (u₀ + timeH1.rampDown c (z' n)).toFun 0 :=
        (extChartAt I x).right_inv
          (interior_subset (hKchart (hv'K n ⟨0, ⟨le_rfl, hc.le⟩⟩)))
      have hu₀0 : u₀.toFun 0 = extChartAt I x x := by
        calc
          u₀.toFun 0 = extChartAt I x (alpha 0) := by
            simpa only using hrep₀ ⟨le_rfl, hc.le⟩
          _ = extChartAt I x x := congrArg (extChartAt I x) hstart
      rw [hright, timeH1.toFun_add _ _ ⟨le_rfl, hc.le⟩,
        timeH1.rampDown_zero hc, hu₀0]
      simp only [z', z, q', add_sub_cancel]
  have hbetaC (n : Nat) : beta n c = alpha c := by
    apply (extChartAt I x).injOn
    · simpa only [extChartAt_source] using hbetaSrc n ⟨hc.le, le_rfl⟩
    · rw [extChartAt_source]
      exact hsrcHead ⟨hc.le, le_rfl⟩
    · have hright : extChartAt I x (beta n c) =
          (u₀ + timeH1.rampDown c (z' n)).toFun c :=
        (extChartAt I x).right_inv
          (interior_subset (hKchart (hv'K n ⟨c, ⟨hc.le, le_rfl⟩⟩)))
      rw [hright, timeH1.toFun_add _ _ ⟨hc.le, le_rfl⟩,
        timeH1.rampDown_end hc, add_zero, hrep₀ ⟨hc.le, le_rfl⟩]
  have hreg₀c : ∀ s ∈ Icc (0 : Real) c, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hs.1, hs.2.trans hcb.le⟩
  have hregcb : ∀ s ∈ Icc c b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hc.le.trans hs.1, by simpa only [b] using hs.2⟩
  have hheadInt := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
    T 0 c hc.le alpha halpha.contMDiffOn hreg₀c
  have htailInt := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
    T c b hcb.le alpha halpha.contMDiffOn hregcb
  have halphaAdd := lRegAction_add (I := I) S T alpha 0 c b hheadInt htailInt
  have hpiece : Tendsto
      (fun n ↦ lRegAction S T (beta n) 0 c + lRegAction S T alpha c b)
      atTop (nhds (lRegAction S T alpha 0 b)) := by
    have htailConst : Tendsto (fun _ : Nat ↦ lRegAction S T alpha c b)
        atTop (nhds (lRegAction S T alpha c b)) := tendsto_const_nhds
    have hsum := hheadLim.add htailConst
    rw [halphaAdd] at hsum
    exact hsum
  have hsmall : ∀ᶠ n in atTop,
      lRegAction S T (beta n) 0 c + lRegAction S T alpha c b < A :=
    hpiece.eventually (Iio_mem_nhds (by simpa only [b] using hA))
  have hcost' : ∀ᶠ n in atTop, lCost S T (q' n) y tau < A := by
    filter_upwards [hsmall] with n hn
    obtain ⟨eta, m, t, p, w, heta₀, heta₁, htmono, htfirst, htlast,
        _hcnode, hsrc, hrep⟩ :=
      exists_chartH1_join (I := I) 0 c b hc hcb (beta n) alpha
        (hbetaC1 n) halpha.contMDiffOn (hbetaC n)
    obtain ⟨delta, _u, hdelta, hdelta₀, hdeltab, _hsrcDelta, _hrepDelta,
        _hu, _hunif, hdeltaAct⟩ :=
      lAction_c1_dense (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
        T 0 b t htmono htfirst htlast p eta w hsrc hrep
        (fun s hs ↦ hreg s (by simpa only [b] using hs))
    have hetaHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1 eta
        (Icc (0 : Real) c) := (hbetaC1 n).congr fun s hs ↦ heta₀ hs
    have hetaTail : ContMDiffOn (modelWithCornersSelf Real Real) I 1 eta
        (Icc c b) := halpha.contMDiffOn.congr fun s hs ↦ heta₁ hs
    have hetaHeadInt := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
      ⟨hS.scalarCont⟩ T 0 c hc.le eta hetaHead hreg₀c
    have hetaTailInt := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
      ⟨hS.scalarCont⟩ T c b hcb.le eta hetaTail hregcb
    have hetaAdd := lRegAction_add (I := I) S T eta 0 c b
      hetaHeadInt hetaTailInt
    have hetaHeadAct : lRegAction S T eta 0 c = lRegAction S T (beta n) 0 c :=
      lRegAction_congr (I := I) S T eta (beta n) 0 c (by
        intro s hs
        have hs' : s ∈ Ioo (0 : Real) c := by
          simpa only [uIoo_of_le hc.le] using hs
        exact heta₀ ⟨hs'.1.le, hs'.2.le⟩)
    have hetaTailAct : lRegAction S T eta c b = lRegAction S T alpha c b :=
      lRegAction_congr (I := I) S T eta alpha c b (by
        intro s hs
        have hs' : s ∈ Ioo c b := by
          simpa only [uIoo_of_le hcb.le] using hs
        exact heta₁ ⟨hs'.1.le, hs'.2.le⟩)
    have hetaLt : lRegAction S T eta 0 b < A := by
      rw [← hetaAdd, hetaHeadAct, hetaTailAct]
      exact hn
    have hdeltaSmall : ∀ᶠ k in atTop, lRegAction S T (delta k) 0 b < A :=
      hdeltaAct.eventually (Iio_mem_nhds hetaLt)
    obtain ⟨k, hk⟩ := hdeltaSmall.exists
    rw [lCost_eq_reg (I := I) S T (q' n) y tau htau.le]
    exact lt_of_le_of_lt
      (lRegCostC1_le (I := I) S hS T t₀ t₁ 0 b hb.le
        htime (by simpa only [b] using hback) (q' n) y (delta k) (hdelta k)
        ((hdelta₀ k).trans ((heta₀ ⟨le_rfl, hc.le⟩).trans (hbeta₀ n)))
        ((hdeltab k).trans ((heta₁ ⟨hcb.le, le_rfl⟩).trans
          (by simpa only [b] using hend)))
        (by simpa only [b] using hreg)) hk
  rw [← map_add_atTop_eq_nat N]
  change ∀ᶠ n in atTop, lCost S T (q (n + N)) y tau < A
  simpa only [q'] using hcost'

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
