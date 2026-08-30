import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LowerSemicontinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.GeometricDensity
import DifferentialGeometry.Geometry.Operator.MetricFamilyGramStrong
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Density

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [UniformSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [IsManifold I ∞ M] [CompactSpace M] in
private theorem exists_chart_buf
    {m : Nat} (p : Fin m → M) (L : Fin m → Real)
    (u : (i : Fin m) → timeH1 E (L i))
    (htar : ∀ i (r : Icc (0 : Real) (L i)),
      (u i).toFun r.1 ∈ (extChartAt I (p i)).target) :
    ∃ K : Fin m → Set E,
      (∀ i, IsCompact (K i)) ∧
      (∀ i, K i ⊆ (extChartAt I (p i)).target) ∧
      (∀ i (r : Icc (0 : Real) (L i)),
        (u i).toFun r.1 ∈ interior (K i)) := by
  classical
  have hchoice (i : Fin m) : ∃ K : Set E,
      IsCompact K ∧ IsClosed K ∧
      (u i).toFun '' Icc (0 : Real) (L i) ⊆ interior K ∧
      K ⊆ (extChartAt I (p i)).target := by
    apply exists_compact_closed_between
    · exact isCompact_Icc.image_of_continuousOn (u i).continuousOn_toFun
    · exact isOpen_extChartAt_target (I := I) (p i)
    · rintro _ ⟨r, hr, rfl⟩
      exact htar i ⟨r, hr⟩
  choose K hKc _ hinto hKtar using hchoice
  refine ⟨K, hKc, hKtar, ?_⟩
  intro i r
  exact hinto i ⟨r.1, r.2, rfl⟩

omit [InnerProductSpace Real E] [FiniteDimensional Real E] in
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

omit [FiniteDimensional ℝ E] in
private theorem timeH1_uniform
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
  have hsub : Tendsto (fun n ↦ u - v n) atTop (nhds 0) :=
    by simpa only [sub_self] using (tendsto_const_nhds.sub hv :
      Tendsto (fun n ↦ u - v n) atTop (nhds (u - u)))
  have hnorm : Tendsto (fun n ↦ ‖u - v n‖) atTop (nhds 0) := by
    have h := continuous_norm.tendsto (0 : timeH1 E L) |>.comp hsub
    rw [norm_zero] at h
    exact h.congr' (Eventually.of_forall fun _ ↦ rfl)
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

omit [FiniteDimensional ℝ E] in
private theorem timeH1_deriv_lim
    {L : Real} (v : Nat → timeH1 E L) (u : timeH1 E L)
    (hv : Tendsto v atTop (nhds u)) :
    Tendsto (fun n ↦ (v n).deriv) atTop (nhds u.deriv) := by
  exact (((timeH1.timeDeriv E L).continuous.tendsto u).comp hv).congr'
    (Eventually.of_forall fun _ ↦ rfl)

private theorem exists_flat_nonneg
    {L : Real} (hL : 0 ≤ L) (u : timeH1 E L) :
    ∃ w : Nat → timeH1 E L, ∃ f : Nat → Real → E,
      (∀ n, ContDiff Real 1 (f n)) ∧
        (∀ n, EqOn (w n).toFun (f n) (Icc (0 : Real) L)) ∧
        (∀ n, f n 0 = u.toFun 0) ∧ (∀ n, f n L = u.toFun L) ∧
        (∀ n, f n =ᶠ[nhds (0 : Real)] fun _ ↦ u.toFun 0) ∧
        (∀ n, f n =ᶠ[nhds L] fun _ ↦ u.toFun L) ∧
        Tendsto w atTop (nhds u) := by
  rcases hL.eq_or_lt with hL0 | hLpos
  · subst L
    refine ⟨fun _ ↦ u, fun _ _ ↦ u.toFun 0, fun _ ↦ contDiff_const, ?_,
      fun _ ↦ rfl, fun _ ↦ rfl, ?_, ?_, tendsto_const_nhds⟩
    · intro n r hr
      have hr0 : r = 0 := le_antisymm hr.2 hr.1
      subst r
      rfl
    · exact fun _ ↦ Eventually.of_forall fun _ ↦ rfl
    · exact fun _ ↦ Eventually.of_forall fun _ ↦ rfl
  · obtain ⟨w, f, hf, hwf, hf0, hfL, hfg0, hfgL, hw, _⟩ :=
      exists_flat_dense hLpos u
    exact ⟨w, f, hf, hwf, hf0, hfL, hfg0, hfgL, hw⟩

omit [CompactSpace M] in
theorem lAction_chart_lim
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (alpha : Nat → Real → M) (gamma : Real → M)
    (u : (i : Fin m) → Nat → timeH1 E (lSegLen t i))
    (uLim : (i : Fin m) → timeH1 E (lSegLen t i))
    (hsrc : ∀ i n, MapsTo (alpha n)
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i n, EqOn (u i n).toFun
      (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
      (Icc (0 : Real) (lSegLen t i)))
    (hsrcLim : ∀ i, MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrepLim : ∀ i, EqOn (uLim i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (lSegLen t i)))
    (K : Fin m → Set E) (hKc : ∀ i, IsCompact (K i))
    (hKchart : ∀ i, K i ⊆ interior (extChartAt I (p i)).target)
    (huK : ∀ i n (r : Icc (0 : Real) (lSegLen t i)),
      (u i n).toFun r.1 ∈ K i)
    (huLimK : ∀ i (r : Icc (0 : Real) (lSegLen t i)),
      (uLim i).toFun r.1 ∈ K i)
    (hu : ∀ i, TendstoUniformly
      (fun n (r : Icc (0 : Real) (lSegLen t i)) ↦ (u i n).toFun r.1)
      (fun r ↦ (uLim i).toFun r.1) atTop)
    (hdu : ∀ i, Tendsto (fun n ↦ (u i n).deriv) atTop
      (nhds (uLim i).deriv))
    (halpha : ∀ n, ContinuousOn (alpha n) (Icc a b))
    (hunif : TendstoUniformly
      (fun n (s : Icc a b) ↦ alpha n s.1)
      (fun s ↦ gamma s.1) atTop)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    Tendsto (fun n ↦ lRegAction S T (alpha n) a b) atTop
      (nhds (lRegAction S T gamma a b)) := by
  classical
  have hab : a ≤ b := by
    rw [← ht0, ← htlast]
    exact htmono (Fin.zero_le _)
  have hleft (i : Fin m) : a ≤ t i.castSucc := by
    rw [← ht0]
    exact htmono (Fin.zero_le _)
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ :=
    htmono Fin.castSucc_lt_succ.le
  have hright (i : Fin m) : t i.succ ≤ b := by
    rw [← htlast]
    exact htmono (Fin.le_last _)
  have hpieceSub (i : Fin m) :
      Icc (t i.castSucc) (t i.succ) ⊆ Icc a b :=
    Icc_subset_Icc (hleft i) (hright i)
  let kin : Fin m → Nat → Real := fun i n ↦
    ∫ r in (0 : Real)..lSegLen t i, (1 / 2 : Real) * inner Real
      (chartGramOp (I := I) S.family (p i)
        (T - (t i.castSucc + r) ^ 2, (u i n).toFun r) ((u i n).deriv r))
      ((u i n).deriv r)
  let kinLim : Fin m → Real := fun i ↦
    ∫ r in (0 : Real)..lSegLen t i, (1 / 2 : Real) * inner Real
      (chartGramOp (I := I) S.family (p i)
        (T - (t i.castSucc + r) ^ 2, (uLim i).toFun r) ((uLim i).deriv r))
      ((uLim i).deriv r)
  let pot : Fin m → Nat → Real := fun i n ↦
    ∫ s in (t i.castSucc)..(t i.succ),
      2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s)
  let potLim : Fin m → Real := fun i ↦
    ∫ s in (t i.castSucc)..(t i.succ),
      2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s)
  have hkin (i : Fin m) : Tendsto (kin i) atTop (nhds (kinLim i)) := by
    have hL : 0 ≤ lSegLen t i := sub_nonneg.mpr (hseg i)
    have htc : ContinuousOn
        (fun r : Real ↦ T - (t i.castSucc + r) ^ 2)
        (Icc (0 : Real) (lSegLen t i)) :=
      (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
    have htreg : MapsTo (fun r : Real ↦ T - (t i.castSucc + r) ^ 2)
        (Icc (0 : Real) (lSegLen t i)) D.regular := by
      intro r hr
      apply hreg (t i.castSucc + r)
      have hr2 : r ≤ t i.succ - t i.castSucc := by
        simpa only [lSegLen] using hr.2
      exact ⟨by linarith [hleft i, hr.1], by
        linarith [hr2, hright i]⟩
    simpa only [kin, kinLim] using
      chartKin_tendsto (I := I) hMet (p i) hL
        (fun r : Real ↦ T - (t i.castSucc + r) ^ 2) htc htreg
        (hKc i) (hKchart i) (u i) (uLim i) (huK i) (huLimK i)
        (hu i) (hdu i)
  have hpot (i : Fin m) : Tendsto (pot i) atTop (nhds (potLim i)) := by
    have hcarrier : ∀ s ∈ Icc (t i.castSucc) (t i.succ),
        T - s ^ 2 ∈ D.carrier := fun s hs ↦
      D.regular_subset (hreg s (hpieceSub i hs))
    have hconv : TendstoUniformly
        (fun n (s : Icc (t i.castSucc) (t i.succ)) ↦ alpha n s.1)
        (fun s ↦ gamma s.1) atTop := by
      let incl : Icc (t i.castSucc) (t i.succ) → Icc a b :=
        fun s ↦ ⟨s.1, hpieceSub i s.2⟩
      convert hunif.comp incl using 1
      · funext n s
        rfl
      · funext s
        rfl
    let Q : Set M := (extChartAt I (p i)).symm '' K i
    have hQc : IsCompact Q :=
      (hKc i).image_of_continuousOn
        ((continuousOn_extChartAt_symm (I := I) (p i)).mono
          (fun z hz ↦ interior_subset (hKchart i hz)))
    have hval : ∀ n s, s ∈ Icc (t i.castSucc) (t i.succ) → alpha n s ∈ Q := by
      intro n s hs
      have hr : s - t i.castSucc ∈ Icc (0 : Real) (lSegLen t i) := by
        constructor
        · linarith [hs.1]
        · simp only [lSegLen]
          linarith [hs.2]
      refine ⟨extChartAt I (p i) (alpha n s), ?_, ?_⟩
      · have hcoord := huK i n ⟨s - t i.castSucc, hr⟩
        rw [hrep i n hr] at hcoord
        have hshift : t i.castSucc + (s - t i.castSucc) = s := by ring
        simpa only [hshift] using hcoord
      · apply (extChartAt I (p i)).left_inv
        rw [extChartAt_source]
        exact hsrc i n hs
    simpa only [pot, potLim] using
      lScalar_tendsto_cpt (I := I) S hSc T (t i.castSucc) (t i.succ)
        (hseg i) hcarrier Q hQc alpha gamma
        (fun n ↦ (halpha n).mono (hpieceSub i)) hval hconv
  have hsum : Tendsto
      (fun n ↦ ∑ i : Fin m, (kin i n + pot i n)) atTop
      (nhds (∑ i : Fin m, (kinLim i + potLim i))) := by
    exact tendsto_finsetSum Finset.univ fun i _ ↦ (hkin i).add (hpot i)
  have hact (n : Nat) : lRegAction S T (alpha n) a b =
      ∑ i : Fin m, (kin i n + pot i n) := by
    simpa only [kin, pot] using
      lRegAction_chart S hMet hSc T a b t htmono ht0 htlast p (alpha n)
        (fun i ↦ u i n) (fun i ↦ hsrc i n) (fun i ↦ hrep i n) hreg
  have hlim : lRegAction S T gamma a b =
      ∑ i : Fin m, (kinLim i + potLim i) := by
    simpa only [kinLim, potLim] using
      lRegAction_chart S hMet hSc T a b t htmono ht0 htlast p gamma uLim
        hsrcLim hrepLim hreg
  rw [show (fun n ↦ lRegAction S T (alpha n) a b) =
      (fun n ↦ ∑ i : Fin m, (kin i n + pot i n)) by
        funext n
        exact hact n,
    hlim]
  exact hsum

omit [CompactSpace M] in
theorem lAction_h1_lim
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (alpha : Nat → Real → M) (gamma : Real → M)
    (u : (i : Fin m) → Nat → timeH1 E (lSegLen t i))
    (uLim : (i : Fin m) → timeH1 E (lSegLen t i))
    (hsrc : ∀ i n, MapsTo (alpha n)
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i n, EqOn (u i n).toFun
      (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
      (Icc (0 : Real) (lSegLen t i)))
    (hsrcLim : ∀ i, MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrepLim : ∀ i, EqOn (uLim i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (lSegLen t i)))
    (K : Fin m → Set E) (hKc : ∀ i, IsCompact (K i))
    (hKchart : ∀ i, K i ⊆ interior (extChartAt I (p i)).target)
    (huK : ∀ i n (r : Icc (0 : Real) (lSegLen t i)),
      (u i n).toFun r.1 ∈ K i)
    (huLimK : ∀ i (r : Icc (0 : Real) (lSegLen t i)),
      (uLim i).toFun r.1 ∈ K i)
    (hu : ∀ i, Tendsto (u i) atTop (nhds (uLim i)))
    (halpha : ∀ n, ContinuousOn (alpha n) (Icc a b))
    (hunif : TendstoUniformly
      (fun n (s : Icc a b) ↦ alpha n s.1)
      (fun s ↦ gamma s.1) atTop)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    Tendsto (fun n ↦ lRegAction S T (alpha n) a b) atTop
      (nhds (lRegAction S T gamma a b)) := by
  exact lAction_chart_lim S hMet hSc T a b t htmono ht0 htlast p alpha gamma
    u uLim hsrc hrep hsrcLim hrepLim K hKc hKchart huK huLimK
    (fun i ↦ timeH1_uniform (u i) (uLim i) (hu i))
    (fun i ↦ timeH1_deriv_lim (u i) (uLim i) (hu i))
    halpha hunif hreg

omit [CompactSpace M] in
theorem lAction_c1_dense
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : Real → M)
    (uLim : (i : Fin m) → timeH1 E (lSegLen t i))
    (hsrcLim : ∀ i, MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrepLim : ∀ i, EqOn (uLim i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (lSegLen t i)))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    ∃ alpha : Nat → Real → M,
      ∃ u : (i : Fin m) → Nat → timeH1 E (lSegLen t i),
        (∀ n, ContMDiff (modelWithCornersSelf Real Real) I 1 (alpha n)) ∧
          (∀ n, alpha n a = gamma a) ∧
          (∀ n, alpha n b = gamma b) ∧
          (∀ i n, MapsTo (alpha n)
            (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source) ∧
          (∀ i n, EqOn (u i n).toFun
            (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
            (Icc (0 : Real) (lSegLen t i))) ∧
          (∀ i, Tendsto (u i) atTop (nhds (uLim i))) ∧
          TendstoUniformly
            (fun n (s : Icc a b) ↦ alpha n s.1)
            (fun s ↦ gamma s.1) atTop ∧
          Tendsto (fun n ↦ lRegAction S T (alpha n) a b) atTop
            (nhds (lRegAction S T gamma a b)) := by
  classical
  have hseg (i : Fin m) : 0 ≤ lSegLen t i :=
    sub_nonneg.mpr (htmono Fin.castSucc_lt_succ.le)
  have hshift (i : Fin m) : MapsTo (fun r : Real ↦ t i.castSucc + r)
      (Icc (0 : Real) (lSegLen t i))
      (Icc (t i.castSucc) (t i.succ)) := by
    intro r hr
    change r ∈ Icc (0 : Real) (t i.succ - t i.castSucc) at hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have htar (i : Fin m) (r : Icc (0 : Real) (lSegLen t i)) :
      (uLim i).toFun r.1 ∈ (extChartAt I (p i)).target := by
    rw [hrepLim i r.2]
    exact (extChartAt I (p i)).map_source (by
      simpa only [extChartAt_source] using hsrcLim i (hshift i r.2))
  obtain ⟨K, hKc, hKtar, huLimInt⟩ :=
    exists_chart_buf p (fun i ↦ lSegLen t i) uLim htar
  have hKchart (i : Fin m) :
      K i ⊆ interior (extChartAt I (p i)).target := by
    rw [(isOpen_extChartAt_target (I := I) (p i)).interior_eq]
    exact hKtar i
  have huLimK (i : Fin m) (r : Icc (0 : Real) (lSegLen t i)) :
      (uLim i).toFun r.1 ∈ K i :=
    interior_subset (huLimInt i r)
  choose w v hvC1 hwv hv0 hvL hvg0 hvgL hw using fun i ↦
    exists_flat_nonneg (hseg i) (uLim i)
  have hvlim (i : Fin m) : TendstoUniformly
      (fun n (r : Icc (0 : Real) (lSegLen t i)) ↦ v i n r.1)
      (fun r ↦ (uLim i).toFun r.1) atTop := by
    exact (tendstoUniformly_congr
      (F := fun n (r : Icc (0 : Real) (lSegLen t i)) ↦ (w i n).toFun r.1)
      (F' := fun n r ↦ v i n r.1)
      (Eventually.of_forall fun n ↦ funext fun r ↦ hwv i n r.2)).mp
        (timeH1_uniform (w i) (uLim i) (hw i))
  have hfc (i : Fin m) : IsCompact
      (range fun r : Icc (0 : Real) (lSegLen t i) ↦ (uLim i).toFun r.1) :=
    isCompact_range (uLim i).continuousOn_toFun.domRestrict
  have hev (i : Fin m) : ∀ᶠ n in atTop,
      ∀ r : Icc (0 : Real) (lSegLen t i), v i n r.1 ∈ K i :=
    eventually_mem_buf
      (fun r : Icc (0 : Real) (lSegLen t i) ↦ (uLim i).toFun r.1)
      (fun n r ↦ v i n r.1) (K i) (hfc i) (huLimInt i) (hvlim i)
  have hall : ∀ᶠ n in atTop, ∀ i,
      ∀ r : Icc (0 : Real) (lSegLen t i), v i n r.1 ∈ K i :=
    Filter.eventually_all.mpr hev
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  have hvK (i : Fin m) (n : Nat)
      (r : Icc (0 : Real) (lSegLen t i)) : v i (n + N) r.1 ∈ K i :=
    hN (n + N) (Nat.le_add_left N n) i r
  have hvlimTail (i : Fin m) : TendstoUniformly
      (fun n (r : Icc (0 : Real) (lSegLen t i)) ↦ v i (n + N) r.1)
      (fun r ↦ (uLim i).toFun r.1) atTop := by
    intro U hU
    exact (tendsto_add_atTop_nat N).eventually (hvlim i U hU)
  obtain ⟨alpha, halpha, halpha0, halphaL, hrepV, hsrc, hunif⟩ :=
    exists_c1_of_flat a b t htmono ht0 htlast p gamma uLim hsrcLim hrepLim
      K hKc hKtar (fun i n ↦ v i (n + N))
      (fun i n ↦ hvC1 i (n + N))
      (fun i n ↦ (hvg0 i (n + N)).trans
        (Eventually.of_forall fun _ ↦ (hv0 i (n + N)).symm))
      (fun i n ↦ (hvgL i (n + N)).trans
        (Eventually.of_forall fun _ ↦ (hvL i (n + N)).symm))
      (fun i n ↦ hv0 i (n + N))
      (fun i n ↦ hvL i (n + N)) hvK huLimK hvlimTail
  let u : (i : Fin m) → Nat → timeH1 E (lSegLen t i) :=
    fun i n ↦ w i (n + N)
  have hrep (i : Fin m) (n : Nat) : EqOn (u i n).toFun
      (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
      (Icc (0 : Real) (lSegLen t i)) :=
    (hwv i (n + N)).trans (hrepV i n)
  have huK (i : Fin m) (n : Nat)
      (r : Icc (0 : Real) (lSegLen t i)) : (u i n).toFun r.1 ∈ K i := by
    rw [hwv i (n + N) r.2]
    exact hvK i n r
  have hulim (i : Fin m) : Tendsto (u i) atTop (nhds (uLim i)) := by
    exact (hw i).comp (tendsto_add_atTop_nat N)
  have hact : Tendsto (fun n ↦ lRegAction S T (alpha n) a b) atTop
      (nhds (lRegAction S T gamma a b)) :=
    lAction_h1_lim S hMet hSc T a b t htmono ht0 htlast p alpha gamma
      u uLim hsrc hrep hsrcLim hrepLim K hKc hKchart huK huLimK hulim
      (fun n ↦ (halpha n).continuous.continuousOn) hunif hreg
  exact ⟨alpha, u, halpha, halpha0, halphaL, hsrc, hrep, hulim, hunif, hact⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
