import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.TwoPieceSplicing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.RawMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.ActionContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Ramp

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
private theorem rampUp_add {L : Real} (hL : 0 < L) (z w : E) :
    timeH1.rampUp L (z + w) = timeH1.rampUp L z + timeH1.rampUp L w := by
  apply timeH1.ext
  · rw [← timeH1.toFun_zero (timeH1.rampUp L (z + w)),
      timeH1.init_add,
      ← timeH1.toFun_zero (timeH1.rampUp L z),
      ← timeH1.toFun_zero (timeH1.rampUp L w),
      timeH1.rampUp_zero hL, timeH1.rampUp_zero hL,
      timeH1.rampUp_zero hL, add_zero]
  · rw [timeH1.deriv_add]
    apply Lp.ext
    filter_upwards [timeH1.rampUp_deriv hL (z + w),
      timeH1.rampUp_deriv hL z, timeH1.rampUp_deriv hL w,
      Lp.coeFn_add (timeH1.rampUp L z).deriv
        (timeH1.rampUp L w).deriv] with s hzw hz hw hadd
    rw [hzw, hadd, Pi.add_apply, hz, hw, smul_add]

private def rampUpLM (L : Real) (hL : 0 < L) :
    E →ₗ[Real] timeH1 E L where
  toFun := timeH1.rampUp L
  map_add' := rampUp_add hL
  map_smul' := timeH1.rampUp_smul hL

omit [NeZero (Module.finrank Real E)] in
private theorem rampUp_tendsto {L : Real} (hL : 0 < L)
    {z : Nat → E} {z₀ : E} (hz : Tendsto z atTop (nhds z₀)) :
    Tendsto (fun n ↦ timeH1.rampUp L (z n)) atTop
      (nhds (timeH1.rampUp L z₀)) := by
  exact (LinearMap.continuous_of_finiteDimensional (rampUpLM L hL)).continuousAt.tendsto.comp hz

omit [NeZero (Module.finrank Real E)] in
omit [FiniteDimensional ℝ E] in
private theorem h1_uniform {L : Real}
    (v : Nat → timeH1 E L) (u : timeH1 E L)
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
    have hn := continuous_norm.tendsto (0 : timeH1 E L) |>.comp hsub
    convert hn using 1
    · rfl
    · simp only [norm_zero]
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

omit [NeZero (Module.finrank Real E)] in
omit [FiniteDimensional ℝ E] in
private theorem timeH1_toFun_cast {a b : Real} (h : a = b)
    (w : timeH1 E b) :
    (h.symm ▸ w : timeH1 E a).toFun = w.toFun := by
  subst b
  rfl

omit [NeZero (Module.finrank Real E)] in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem timeH1_tendsto_cast {a b : Real} (h : a = b)
    (w : Nat → timeH1 E b) (w0 : timeH1 E b)
    (hw : Tendsto w atTop (nhds w0)) :
    Tendsto (fun n ↦ h.symm ▸ w n) atTop (nhds (h.symm ▸ w0)) := by
  subst b
  exact hw

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
private theorem chart_tail_lim
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T c b : Real) (hcb : c < b) (p : M) (gamma : Real → M)
    (u0 : timeH1 E (b - c))
    (hsrc0 : MapsTo gamma (Icc c b) (chartAt H p).source)
    (hrep0 : EqOn u0.toFun
      (fun r ↦ extChartAt I p (gamma (c + r))) (Icc (0 : Real) (b - c)))
    (z : Nat → E) (hz : Tendsto z atTop (nhds 0))
    (K : Set E) (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I p).target)
    (hK : ∀ n (r : Icc (0 : Real) (b - c)),
      (u0 + timeH1.rampUp (b - c) (z n)).toFun r.1 ∈ K)
    (hK0 : ∀ r : Icc (0 : Real) (b - c), u0.toFun r.1 ∈ K)
    (hreg : ∀ s ∈ Icc c b, T - s ^ 2 ∈ D.regular) :
    Tendsto
      (fun n ↦ lRegAction S T
        (fun s ↦ (extChartAt I p).symm
          ((u0 + timeH1.rampUp (b - c) (z n)).toFun (s - c))) c b)
      atTop (nhds (lRegAction S T gamma c b)) := by
  let v : Nat → timeH1 E (b - c) := fun n ↦
    u0 + timeH1.rampUp (b - c) (z n)
  let beta : Nat → Real → M := fun n s ↦
    (extChartAt I p).symm ((v n).toFun (s - c))
  let beta0 : Real → M := fun s ↦ (extChartAt I p).symm (u0.toFun (s - c))
  have hL : 0 < b - c := sub_pos.mpr hcb
  have hv : Tendsto v atTop (nhds u0) := by
    have hr := rampUp_tendsto (E := E) hL hz
    have hr0 : timeH1.rampUp (b - c) (0 : E) = 0 := by
      simpa only [zero_smul] using
        timeH1.rampUp_smul hL (0 : Real) (0 : E)
    simpa only [v, hr0, add_zero] using
      tendsto_const_nhds.add hr
  have hcoord := h1_uniform v u0 hv
  have hsymm : UniformContinuousOn (extChartAt I p).symm K :=
    hKc.uniformContinuousOn_of_continuous <|
      (continuousOn_extChartAt_symm p).mono (hKchart.trans interior_subset)
  have hunif : TendstoUniformly
      (fun n (s : Icc c b) ↦ beta n s.1)
      (fun s ↦ beta0 s.1) atTop := by
    have hshift : MapsTo (fun s : Icc c b ↦ s.1 - c)
        univ (Icc (0 : Real) (b - c)) := by
      intro s _
      exact ⟨sub_nonneg.mpr s.2.1, sub_le_sub_right s.2.2 c⟩
    have hc := hcoord.comp (fun s : Icc c b ↦
      ⟨s.1 - c, hshift (mem_univ s)⟩)
    apply UniformContinuousOn.comp_tendstoUniformly
      (s := K) (F := fun n (s : Icc c b) ↦
        (v n).toFun (s.1 - c)) (f := fun s ↦ u0.toFun (s.1 - c))
    · exact fun n s ↦ hK n ⟨s.1 - c, hshift (mem_univ s)⟩
    · exact fun s ↦ hK0 ⟨s.1 - c, hshift (mem_univ s)⟩
    · exact hsymm
    · convert hc using 1 <;> rfl
  have hcont (n : Nat) : ContinuousOn (beta n) (Icc c b) := by
    have hcoordCont : ContinuousOn (fun s ↦ (v n).toFun (s - c))
        (Icc c b) :=
      (v n).continuousOn_toFun.comp (continuous_sub_right c).continuousOn
        (fun s hs ↦ ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩)
    exact (continuousOn_extChartAt_symm p).comp
      hcoordCont
      (fun s hs ↦ interior_subset (hKchart (hK n ⟨s - c,
        ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩⟩)))
  have hsrc (n : Nat) : MapsTo (beta n) (Icc c b) (chartAt H p).source := by
    intro s hs
    rw [← extChartAt_source (I := I) p]
    exact (extChartAt I p).map_target
      (interior_subset (hKchart (hK n ⟨s - c,
        ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩⟩)))
  have hrep (n : Nat) : EqOn (v n).toFun
      (fun r ↦ extChartAt I p (beta n (c + r)))
      (Icc (0 : Real) (b - c)) := by
    intro r hr
    simp only [beta, add_sub_cancel_left]
    exact ((extChartAt I p).right_inv
      (interior_subset (hKchart (hK n ⟨r, hr⟩)))).symm
  have hsrcLim : MapsTo beta0 (Icc c b) (chartAt H p).source := by
    intro s hs
    rw [← extChartAt_source (I := I) p]
    exact (extChartAt I p).map_target
      (interior_subset (hKchart (hK0 ⟨s - c,
        ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩⟩)))
  have hrepLim : EqOn u0.toFun
      (fun r ↦ extChartAt I p (beta0 (c + r)))
      (Icc (0 : Real) (b - c)) := by
    intro r hr
    simp only [beta0, add_sub_cancel_left]
    exact ((extChartAt I p).right_inv
      (interior_subset (hKchart (hK0 ⟨r, hr⟩)))).symm
  let t : Fin 2 → Real :=
    Fin.cases c (Fin.cases b fun k ↦ Fin.elim0 k)
  have ht0 : t 0 = c := rfl
  have ht1 : t (Fin.last 1) = b := rfl
  have htLen : partitionIntervalLength t 0 = b - c := rfl
  have htmono : Monotone t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [t, hcb.le]
  let vt (n : Nat) : timeH1 E (partitionIntervalLength t 0) := htLen.symm ▸ v n
  let u0t : timeH1 E (partitionIntervalLength t 0) := htLen.symm ▸ u0
  let vtFin : (i : Fin 1) → Nat → timeH1 E (partitionIntervalLength t i) :=
    Fin.cases vt fun k ↦ Fin.elim0 k
  let u0Fin : (i : Fin 1) → timeH1 E (partitionIntervalLength t i) :=
    Fin.cases u0t fun k ↦ Fin.elim0 k
  have hlim := lAction_h1_lim (I := I) S hMet hSc T c b t htmono
    ht0 ht1 (fun _ ↦ p) beta beta0
    vtFin u0Fin
    (fun i n ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change MapsTo (beta n) (Icc c b) (chartAt H p).source
      exact hsrc n)
    (fun i n ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      intro r hr
      have hr' : r ∈ Icc (0 : Real) (b - c) := by
        rw [← htLen]
        exact hr
      change (vt n).toFun r = extChartAt I p (beta n (t 0 + r))
      rw [timeH1_toFun_cast htLen (v n), ht0]
      exact hrep n hr')
    (fun i ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change MapsTo beta0 (Icc c b) (chartAt H p).source
      exact hsrcLim)
    (fun i ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      intro r hr
      have hr' : r ∈ Icc (0 : Real) (b - c) := by
        rw [← htLen]
        exact hr
      change u0t.toFun r = extChartAt I p (beta0 (t 0 + r))
      rw [timeH1_toFun_cast htLen u0, ht0]
      exact hrepLim hr')
    (fun _ ↦ K) (fun _ ↦ hKc) (fun _ ↦ hKchart)
    (fun i n r ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hrmem : r.val ∈ Icc (0 : Real) (b - c) := by
        rw [← htLen]
        exact r.property
      let r' : Icc (0 : Real) (b - c) := ⟨r.val, hrmem⟩
      change (vt n).toFun r.1 ∈ K
      rw [timeH1_toFun_cast htLen (v n)]
      have hk := hK n r'
      change (v n).toFun r'.1 ∈ K at hk
      have hrval : (r' : Real) = (r : Real) := by
        rfl
      rw [hrval] at hk
      exact hk)
    (fun i r ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hrmem : r.val ∈ Icc (0 : Real) (b - c) := by
        rw [← htLen]
        exact r.property
      let r' : Icc (0 : Real) (b - c) := ⟨r.val, hrmem⟩
      change u0t.toFun r.1 ∈ K
      rw [timeH1_toFun_cast htLen u0]
      have hk := hK0 r'
      have hrval : (r' : Real) = (r : Real) := by
        rfl
      rw [hrval] at hk
      exact hk)
    (fun i ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change Tendsto vt atTop (nhds u0t)
      exact timeH1_tendsto_cast htLen v u0 hv)
    hcont hunif hreg
  have heq : EqOn beta0 gamma (Icc c b) := by
    intro s hs
    apply (extChartAt I p).injOn
    · simpa only [extChartAt_source] using hsrcLim hs
    · rw [extChartAt_source]
      exact hsrc0 hs
    · calc
        extChartAt I p (beta0 s) = u0.toFun (s - c) :=
          (extChartAt I p).right_inv (interior_subset (hKchart
            (hK0 ⟨s - c,
              ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩⟩)))
        _ = extChartAt I p (gamma (c + (s - c))) :=
          hrep0 ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩
        _ = extChartAt I p (gamma s) := by
          congr 2
          ring
  have heqAct : lRegAction S T beta0 c b = lRegAction S T gamma c b :=
    lRegAction_congr (I := I) S T beta0 gamma c b
      (by
        have heq' : EqOn beta0 gamma (uIcc c b) := by
          simpa only [uIcc_of_le hcb.le] using heq
        exact heq'.mono uIoo_subset_uIcc_self)
  rw [heqAct] at hlim
  simpa only [beta, v] using hlim

omit [NeZero (Module.finrank Real E)] in
theorem lCost_lt_event
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T t0 t1 tau : Real) (htau : 0 < tau)
    (htime : Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ Icc t0 t1)
    (x y : M) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha)
    (h0 : alpha 0 = x) (hend : alpha (Real.sqrt tau) = y)
    (hreg : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ D.regular)
    (A : Real) (hA : lRegAction S T alpha 0 (Real.sqrt tau) < A)
    (q : Nat → M) (hq : Tendsto q atTop (nhds y)) :
    ∀ᶠ n in atTop, lCost S T x (q n) tau < A := by
  classical
  let b : Real := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hySrc : y ∈ (chartAt H y).source := mem_chart_source H y
  have hpre : alpha ⁻¹' (chartAt H y).source ∈ 𝓝[≤] b := by
    apply mem_nhdsWithin_of_mem_nhds
    apply halpha.continuous.continuousAt.preimage_mem_nhds
    exact (chartAt H y).open_source.mem_nhds (by simpa only [b, hend] using hySrc)
  obtain ⟨c0, hc0b, hc0src⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp hpre
  let c : Real := max c0 (b / 2)
  have hc : 0 < c := lt_of_lt_of_le (half_pos hb) (le_max_right _ _)
  have hcb : c < b := by
    exact max_lt hc0b (half_lt_self hb)
  have hsrcTail : MapsTo alpha (Icc c b) (chartAt H y).source := by
    intro s hs
    exact hc0src ⟨(le_max_left _ _).trans hs.1, hs.2⟩
  let gamma : Real → M := fun r ↦ alpha (c + r)
  have hshift : MapsTo (fun r : Real ↦ c + r) (Icc (0 : Real) (b - c))
      (Icc c b) := by
    intro r hr
    exact ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩
  have hgamma : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc (0 : Real) (b - c)) := by
    exact halpha.comp (contDiff_const.add contDiff_id).contMDiff |>.contMDiffOn
  have hgammaSrc : MapsTo gamma (Icc (0 : Real) (b - c))
      (chartAt H y).source := fun r hr ↦ hsrcTail (hshift hr)
  let u0 : timeH1 E (b - c) :=
    chartTimeH1 I (sub_nonneg.mpr hcb.le) y gamma hgamma hgammaSrc
  have hrep0 : EqOn u0.toFun
      (fun r ↦ extChartAt I y (alpha (c + r)))
      (Icc (0 : Real) (b - c)) := by
    intro r hr
    change u0.toFun r = ((extChartAt I y) ∘ gamma) r
    exact chartTimeH1_toFun I (sub_nonneg.mpr hcb.le) y gamma hgamma
      hgammaSrc hr
  have htar0 (r : Icc (0 : Real) (b - c)) :
      u0.toFun r.1 ∈ (extChartAt I y).target := by
    rw [hrep0 r.2]
    exact (extChartAt I y).map_source (by
      rw [extChartAt_source]
      exact hgammaSrc r.2)
  obtain ⟨K, hKc, _hKclosed, hintoK, hKtar⟩ :=
    exists_compact_closed_between
      (isCompact_Icc.image_of_continuousOn u0.continuousOn_toFun)
      (isOpen_extChartAt_target (I := I) y)
      (by rintro _ ⟨r, hr, rfl⟩; exact htar0 ⟨r, hr⟩)
  have hKchart : K ⊆ interior (extChartAt I y).target := by
    simpa only [(isOpen_extChartAt_target (I := I) y).interior_eq] using hKtar
  have hK0 (r : Icc (0 : Real) (b - c)) : u0.toFun r.1 ∈ K :=
    interior_subset (hintoK ⟨r.1, r.2, rfl⟩)
  have hqSrc : ∀ᶠ n in atTop, q n ∈ (chartAt H y).source :=
    hq.eventually ((chartAt H y).open_source.mem_nhds hySrc)
  let z : Nat → E := fun n ↦ extChartAt I y (q n) - extChartAt I y y
  have hz : Tendsto z atTop (nhds 0) := by
    have hcq := (continuousAt_extChartAt (I := I) y).tendsto.comp hq
    have hcst : Tendsto (fun _ : Nat ↦ extChartAt I y y) atTop
        (nhds (extChartAt I y y)) := tendsto_const_nhds
    simpa only [z, Function.comp_apply, sub_self] using hcq.sub hcst
  let v : Nat → timeH1 E (b - c) := fun n ↦
    u0 + timeH1.rampUp (b - c) (z n)
  have hv : Tendsto v atTop (nhds u0) := by
    have hr := rampUp_tendsto (E := E) (sub_pos.mpr hcb) hz
    have hr0 : timeH1.rampUp (b - c) (0 : E) = 0 := by
      simpa only [zero_smul] using
        timeH1.rampUp_smul (sub_pos.mpr hcb) (0 : Real) (0 : E)
    simpa only [v, hr0, add_zero] using tendsto_const_nhds.add hr
  have hcoord := h1_uniform v u0 hv
  have hu0Range : IsCompact
      (range fun r : Icc (0 : Real) (b - c) ↦ u0.toFun r.1) := by
    rw [← image_univ]
    exact isCompact_univ.image_of_continuousOn
      (u0.continuousOn_toFun.comp continuous_subtype_val.continuousOn
        (fun _ _ ↦ Subtype.property _))
  have hvK : ∀ᶠ n in atTop, ∀ r : Icc (0 : Real) (b - c),
      (v n).toFun r.1 ∈ K :=
    eventually_mem_buf (fun r : Icc (0 : Real) (b - c) ↦ u0.toFun r.1)
      (fun n r ↦ (v n).toFun r.1) K
      hu0Range
      (fun r ↦ hintoK ⟨r.1, r.2, rfl⟩) hcoord
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (hqSrc.and hvK))
  let q' : Nat → M := fun n ↦ q (n + N)
  let z' : Nat → E := fun n ↦ z (n + N)
  let v' : Nat → timeH1 E (b - c) := fun n ↦ v (n + N)
  have hq'Src (n : Nat) : q' n ∈ (chartAt H y).source := (hN _ (Nat.le_add_left N n)).1
  have hz' : Tendsto z' atTop (nhds 0) := hz.comp (tendsto_add_atTop_nat N)
  have hv' (n : Nat) : v' n = u0 + timeH1.rampUp (b - c) (z' n) := rfl
  have hv'K (n : Nat) (r : Icc (0 : Real) (b - c)) :
      (u0 + timeH1.rampUp (b - c) (z' n)).toFun r.1 ∈ K := by
    simpa only [v', v, z'] using (hN _ (Nat.le_add_left N n)).2 r
  let beta : Nat → Real → M := fun n s ↦
    (extChartAt I y).symm
      ((u0 + timeH1.rampUp (b - c) (z' n)).toFun (s - c))
  have htailLim : Tendsto (fun n ↦ lRegAction S T (beta n) c b) atTop
      (nhds (lRegAction S T alpha c b)) := by
    apply chart_tail_lim (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩ T c b hcb y
      alpha u0 hsrcTail hrep0 z' hz' K hKc hKchart hv'K hK0
    intro s hs
    exact hreg s ⟨hc.le.trans hs.1, by simpa only [b] using hs.2⟩
  have hu0c1 : ContDiffOn Real 1 u0.toFun (Icc (0 : Real) (b - c)) := by
    exact (chartCoord_contDiff I y gamma hgamma hgammaSrc).congr
      (fun r hr ↦ by simpa only [gamma, Function.comp_apply] using hrep0 hr)
  have hbetaC1 (n : Nat) : ContMDiffOn
      (modelWithCornersSelf Real Real) I 1 (beta n) (Icc c b) := by
    have hvC1 : ContDiffOn Real 1
        (u0 + timeH1.rampUp (b - c) (z' n)).toFun
        (Icc (0 : Real) (b - c)) := by
      apply (hu0c1.add
        (((contDiff_id.div_const (b - c)).smul_const (z' n)).contDiffOn)).congr
      intro r hr
      rw [timeH1.toFun_add _ _ hr,
        timeH1.rampUp_apply (sub_nonneg.mpr hcb.le) (z' n) hr]
      simp only [id_eq]
    apply curve_c1_local I y (beta n)
      (u0 + timeH1.rampUp (b - c) (z' n))
    · intro s hs
      rw [← extChartAt_source (I := I) y]
      exact (extChartAt I y).map_target
        (interior_subset (hKchart (hv'K n ⟨s - c,
          ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩⟩)))
    · intro r hr
      simp only [beta, add_sub_cancel_left]
      exact ((extChartAt I y).right_inv
        (interior_subset (hKchart (hv'K n ⟨r, hr⟩)))).symm
    · exact hvC1
  have hbetaSrc (n : Nat) : MapsTo (beta n) (Icc c b)
      (chartAt H y).source := by
    intro s hs
    rw [← extChartAt_source (I := I) y]
    exact (extChartAt I y).map_target
      (interior_subset (hKchart (hv'K n ⟨s - c,
        ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩⟩)))
  have hbetaC (n : Nat) : beta n c = alpha c := by
    apply (extChartAt I y).injOn
    · simpa only [extChartAt_source] using hbetaSrc n ⟨le_rfl, hcb.le⟩
    · rw [extChartAt_source]
      exact hsrcTail ⟨le_rfl, hcb.le⟩
    · simp only [beta, sub_self]
      have hv0 : (u0 + timeH1.rampUp (b - c) (z' n)).toFun 0 =
          u0.toFun 0 := by
        rw [timeH1.toFun_add _ _ ⟨le_rfl, sub_nonneg.mpr hcb.le⟩,
          timeH1.rampUp_zero (sub_pos.mpr hcb), add_zero]
      have hright0 : extChartAt I y ((extChartAt I y).symm (u0.toFun 0)) =
          u0.toFun 0 := (extChartAt I y).right_inv
        (interior_subset (hKchart (hK0
          ⟨0, ⟨le_rfl, sub_nonneg.mpr hcb.le⟩⟩)))
      rw [hv0, hright0]
      calc
        u0.toFun 0 = extChartAt I y (alpha (c + 0)) :=
          hrep0 ⟨le_rfl, sub_nonneg.mpr hcb.le⟩
        _ = extChartAt I y (alpha c) := by rw [add_zero]
  have hbetaB (n : Nat) : beta n b = q' n := by
    apply (extChartAt I y).injOn
    · rw [extChartAt_source]
      rw [← extChartAt_source (I := I) y]
      exact (extChartAt I y).map_target
        (interior_subset (hKchart (hv'K n ⟨b - c,
          ⟨sub_nonneg.mpr hcb.le, le_rfl⟩⟩)))
    · rw [extChartAt_source]
      exact hq'Src n
    · have hrightB : extChartAt I y (beta n b) =
          (u0 + timeH1.rampUp (b - c) (z' n)).toFun (b - c) := by
        exact (extChartAt I y).right_inv
          (interior_subset (hKchart (hv'K n ⟨b - c,
            ⟨sub_nonneg.mpr hcb.le, le_rfl⟩⟩)))
      have hu0b : u0.toFun (b - c) = extChartAt I y y := by
        calc
          u0.toFun (b - c) = extChartAt I y (alpha (c + (b - c))) :=
            hrep0 ⟨sub_nonneg.mpr hcb.le, le_rfl⟩
          _ = extChartAt I y y := by
            rw [show c + (b - c) = b by ring,
              show b = Real.sqrt tau by rfl, hend]
      rw [hrightB, timeH1.toFun_add _ _
          ⟨sub_nonneg.mpr hcb.le, le_rfl⟩,
        timeH1.rampUp_end (sub_pos.mpr hcb), hu0b]
      simp only [z', z, q', add_sub_cancel]
  have hreg0c : ∀ s ∈ Icc (0 : Real) c, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hs.1, hs.2.trans hcb.le⟩
  have hregcb : ∀ s ∈ Icc c b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hc.le.trans hs.1, by simpa only [b] using hs.2⟩
  have hheadInt := lRegLag_int_c1 (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
    T 0 c hc.le alpha halpha.contMDiffOn hreg0c
  have htailInt := lRegLag_int_c1 (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
    T c b hcb.le alpha halpha.contMDiffOn hregcb
  have halphaAdd := lRegAction_add (I := I) S T alpha 0 c b hheadInt htailInt
  have hpiece : Tendsto
      (fun n ↦ lRegAction S T alpha 0 c + lRegAction S T (beta n) c b)
      atTop (nhds (lRegAction S T alpha 0 b)) := by
    have hsum : Tendsto
        (fun n ↦ lRegAction S T alpha 0 c + lRegAction S T (beta n) c b)
        atTop (nhds
          (lRegAction S T alpha 0 c + lRegAction S T alpha c b)) :=
      tendsto_const_nhds.add htailLim
    rw [halphaAdd] at hsum
    exact hsum
  have hsmall : ∀ᶠ n in atTop,
      lRegAction S T alpha 0 c + lRegAction S T (beta n) c b < A :=
    hpiece.eventually (Iio_mem_nhds (by simpa only [b] using hA))
  have hcost' : ∀ᶠ n in atTop, lCost S T x (q' n) tau < A := by
    filter_upwards [hsmall] with n hn
    obtain ⟨eta, m, t, p, w, heta0, heta1, htmono, ht0, htlast,
        _hcnode, hsrc, hrep⟩ :=
      exists_chartH1_join (I := I) 0 c b hc hcb alpha (beta n)
        halpha.contMDiffOn (hbetaC1 n) (hbetaC n).symm
    obtain ⟨delta, _u, hdelta, hdelta0, hdeltab, _hsrcDelta, _hrepDelta,
        _hu, _hunif, hdeltaAct⟩ :=
      lAction_c1_dense (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
        T 0 b t htmono ht0 htlast p eta w hsrc hrep
        (fun s hs ↦ hreg s (by simpa only [b] using hs))
    have hetaHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1 eta
        (Icc (0 : Real) c) := halpha.contMDiffOn.congr fun s hs ↦ heta0 hs
    have hetaTail : ContMDiffOn (modelWithCornersSelf Real Real) I 1 eta
        (Icc c b) := (hbetaC1 n).congr fun s hs ↦ heta1 hs
    have hetaHeadInt := lRegLag_int_c1 (I := I) S hS.smoothMetric
      ⟨hS.scalarCont⟩ T 0 c hc.le eta hetaHead hreg0c
    have hetaTailInt := lRegLag_int_c1 (I := I) S hS.smoothMetric
      ⟨hS.scalarCont⟩ T c b hcb.le eta hetaTail hregcb
    have hetaAdd := lRegAction_add (I := I) S T eta 0 c b
      hetaHeadInt hetaTailInt
    have hetaHeadAct : lRegAction S T eta 0 c = lRegAction S T alpha 0 c :=
      lRegAction_congr (I := I) S T eta alpha 0 c (by
        intro s hs
        have hs' : s ∈ Ioo (0 : Real) c := by
          simpa only [uIoo_of_le hc.le] using hs
        exact heta0 ⟨hs'.1.le, hs'.2.le⟩)
    have hetaTailAct : lRegAction S T eta c b = lRegAction S T (beta n) c b :=
      lRegAction_congr (I := I) S T eta (beta n) c b (by
        intro s hs
        have hs' : s ∈ Ioo c b := by
          simpa only [uIoo_of_le hcb.le] using hs
        exact heta1 ⟨hs'.1.le, hs'.2.le⟩)
    have hetaLt : lRegAction S T eta 0 b < A := by
      rw [← hetaAdd, hetaHeadAct, hetaTailAct]
      exact hn
    have hdeltaSmall : ∀ᶠ k in atTop, lRegAction S T (delta k) 0 b < A :=
      hdeltaAct.eventually (Iio_mem_nhds hetaLt)
    obtain ⟨k, hk⟩ := hdeltaSmall.exists
    rw [lCost_eq_reg (I := I) S T x (q' n) tau htau.le]
    exact lt_of_le_of_lt
      (lRegCostC1_le (I := I) S hS T t0 t1 0 b hb.le
        htime (by simpa only [b] using hback) x (q' n) (delta k) (hdelta k)
        ((hdelta0 k).trans ((heta0 ⟨le_rfl, hc.le⟩).trans h0))
        ((hdeltab k).trans
          ((heta1 ⟨hcb.le, le_rfl⟩).trans (hbetaB n)))
        (by simpa only [b] using hreg)) hk
  rw [← map_add_atTop_eq_nat N]
  change ∀ᶠ n in atTop, lCost S T x (q (n + N)) tau < A
  exact hcost'

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lCost_le_ray
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (b : Real)
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z) :
    lCost S T x (lRegCurve S T x Z b) (b ^ 2) ≤
      lRegAction S T (lRegCurve S T x Z) 0 b := by
  obtain ⟨rho, hrho, hrho_id, _hrho_deriv, hrho_range⟩ :=
    exists_lReg_clamp S T x Z hb0 hb
  let z : E := Z
  let gamma : Real → M := fun s ↦ lRegCurve S T x Z (rho s)
  have hrhoM : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ rho :=
    contMDiff_iff_contDiff.mpr hrho
  have hpair : ContMDiff (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real)) ∞
      (fun s : Real ↦ (z, rho s)) :=
    contMDiff_const.prodMk hrhoM
  have hgammaInf : ContMDiff (modelWithCornersSelf Real Real) I ∞ gamma := by
    rw [← contMDiffOn_univ]
    change ContMDiffOn (modelWithCornersSelf Real Real) I ∞
      (fun s ↦ lRegCurve S T x Z (rho s)) univ
    exact (lRegCurve_smoothOn S hS T x).comp hpair.contMDiffOn
      (fun s _hs ↦ by
        change rho s ∈ lRegDomain S T x Z
        exact hrho_range s)
  have hgamma : ContMDiff (modelWithCornersSelf Real Real) I 1 gamma :=
    hgammaInf.of_le (by norm_num)
  have heq : Set.EqOn gamma (lRegCurve S T x Z) (Icc (0 : Real) b) := by
    intro s hs
    exact congrArg (lRegCurve S T x Z) (hrho_id hs)
  have hreg : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact lRegDomain_reg S T x Z
      (lRegDomain_seg S T x Z hb hs.1 hs.2)
  have htime : Icc (T - b ^ 2) T ⊆ D.carrier := by
    intro r hr
    have hnonneg : 0 ≤ T - r := by linarith [hr.2]
    have hle : T - r ≤ b ^ 2 := by linarith [hr.1]
    have hsqrt : Real.sqrt (T - r) ∈ Icc (0 : Real) b := by
      refine ⟨Real.sqrt_nonneg _, ?_⟩
      calc
        Real.sqrt (T - r) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hle
        _ = b := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hb0]
    have hregR := hreg (Real.sqrt (T - r)) hsqrt
    have heqR : T - (Real.sqrt (T - r)) ^ 2 = r := by
      rw [Real.sq_sqrt hnonneg]
      ring
    exact D.regular_subset (by simpa only [heqR] using hregR)
  have hback : ∀ s ∈ Icc (0 : Real) b,
      T - s ^ 2 ∈ Icc (T - b ^ 2) T := by
    intro s hs
    have hsq : s ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hs.1 hb0.le).2 hs.2
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  have hact : lRegAction S T gamma 0 b =
      lRegAction S T (lRegCurve S T x Z) 0 b := by
    apply lRegAction_congr (I := I) S T gamma (lRegCurve S T x Z) 0 b
    intro s hs
    apply heq
    have hs' : s ∈ Ioo (0 : Real) b := by
      simpa only [uIoo_of_le hb0.le] using hs
    exact ⟨hs'.1.le, hs'.2.le⟩
  have hrho0 : rho 0 = 0 := by
    simpa only [id_eq] using hrho_id ⟨le_rfl, hb0.le⟩
  have hrhob : rho b = b := by
    simpa only [id_eq] using hrho_id ⟨hb0.le, le_rfl⟩
  rw [lCost_eq_reg (I := I) S T x (lRegCurve S T x Z b)
      (b ^ 2) (sq_nonneg b), Real.sqrt_sq_eq_abs, abs_of_pos hb0]
  calc
    lRegCostC1 S T 0 b x (lRegCurve S T x Z b) ≤
        lRegAction S T gamma 0 b :=
      lRegCostC1_le (I := I) S hS T (T - b ^ 2) T 0 b hb0.le
        htime hback x (lRegCurve S T x Z b) gamma hgamma
        (by simp only [gamma, hrho0, lRegCurve_zero])
        (by simp only [gamma, hrhob]) hreg
    _ = lRegAction S T (lRegCurve S T x Z) 0 b := hact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lCost_ray_event
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : Nat → TangentSpace I x}
    {Z₀ : TangentSpace I x} {tau : Nat → Real} {tau₀ : Real}
    (htau₀ : 0 < tau₀)
    (hdom : Real.sqrt tau₀ ∈ lRegDomain S T x Z₀)
    (hZ : Tendsto Z atTop (nhds Z₀))
    (htau : Tendsto tau atTop (nhds tau₀))
    (A : Real)
    (hA : lRegAction S T (lRegCurve S T x Z₀) 0
      (Real.sqrt tau₀) < A) :
    ∀ᶠ n in atTop, lCost S T x (lExp S T x (Z n) (tau n)) (tau n) < A := by
  have hsqrt : Tendsto (fun n ↦ Real.sqrt (tau n)) atTop
      (nhds (Real.sqrt tau₀)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp htau
  have hsqrt0 : 0 < Real.sqrt tau₀ := Real.sqrt_pos.2 htau₀
  have hjoint : Tendsto (fun n ↦ ((Z n : E), Real.sqrt (tau n))) atTop
      (nhds ((Z₀ : E), Real.sqrt tau₀)) := hZ.prodMk_nhds hsqrt
  have hmem : ∀ᶠ n in atTop,
      Real.sqrt (tau n) ∈ lRegDomain S T x (Z n) := by
    exact hjoint.eventually
      ((lRegJointDom_open S hS T x).mem_nhds (by
        change Real.sqrt tau₀ ∈ lRegDomain S T x Z₀
        exact hdom))
  have hpos : ∀ᶠ n in atTop, 0 < tau n :=
    htau.eventually (Ioi_mem_nhds htau₀)
  have hact := lRayAct_tendsto (I := I) S hS T x hsqrt0 hdom hZ hsqrt
  have hactLt : ∀ᶠ n in atTop,
      lRegAction S T (lRegCurve S T x (Z n)) 0
        (Real.sqrt (tau n)) < A :=
    hact.eventually (Iio_mem_nhds hA)
  filter_upwards [hmem, hpos, hactLt] with n hnDom hnPos hnAct
  have hle := lCost_le_ray (I := I) S hS T x (Z n)
    (Real.sqrt (tau n)) (Real.sqrt_pos.2 hnPos) hnDom
  have hle' : lCost S T x (lExp S T x (Z n) (tau n)) (tau n) ≤
      lRegAction S T (lRegCurve S T x (Z n)) 0
        (Real.sqrt (tau n)) := by
    simpa only [lExp, Real.sq_sqrt hnPos.le] using hle
  exact hle'.trans_lt hnAct

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
