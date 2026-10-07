import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.GlobalSurgeryPath_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TerminalPath_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RmSurvivor_S56
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SmoothFirstExit_CX2

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- P1: a globally `C^1`, clipped path of length `< r` from `d(x,y) < r`
(copy of `exists_global_seed_path_CX2` with `exists_lt_of_edistOf_lt`). -/
theorem exists_clipped_path_S147 (P : OrientedThreeStage.{u}) (g : P.Metric)
    {x y : P.Carrier} {r : ℝ≥0∞} (h : riemannianEDistOf g x y < r) :
    ∃ γ : ℝ → P.Carrier, γ 0 = x ∧ γ 1 = y ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ ∧
      (∀ s, γ s = γ (projIcc (0 : ℝ) 1 zero_le_one s)) ∧
      metricPathELength g γ 0 1 < r := by
  obtain ⟨β, hβ0, hβ1, hβ, hlen⟩ := exists_lt_of_edistOf_lt g h
  let γ := β ∘ Real.smoothTransition
  have hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ := by
    rw [← contMDiffOn_univ]
    apply hβ.comp
    · rw [contMDiffOn_univ, contMDiff_iff_contDiff]
      fun_prop
    · intro s _
      exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  refine ⟨γ, by simpa [γ] using hβ0, by simpa [γ] using hβ1, hγ, ?_, ?_⟩
  · intro s
    simp only [γ, Function.comp_apply, Real.smoothTransition.projIcc]
  · have heq : metricPathELength g γ 0 1 = metricPathELength g β 0 1 := by
      let : RiemannianBundle (TangentSpace ThreeModel : P.Carrier → Type _) := ⟨g.toRiemannianMetric⟩
      change pathELength ThreeModel (β ∘ Real.smoothTransition) 0 1 = pathELength ThreeModel β 0 1
      rw [pathELength_comp_of_monotoneOn zero_le_one (Real.smoothTransition.monotone.monotoneOn _)]
      · simp only [Real.smoothTransition.zero, Real.smoothTransition.one]
      · exact (Real.smoothTransition.contDiff : ContDiff ℝ 1 Real.smoothTransition).contDiffOn.differentiableOn (by norm_num)
      · simpa only [Real.smoothTransition.zero, Real.smoothTransition.one] using
          hβ.mdifferentiableOn (by norm_num)
    exact heq.trans_lt hlen

/-- Forward dual of `compact_backward_first_exit_CX2`: take the least time of the compact
set `{R ≤ f}`; if control on `[a,v)` improves `f v` to `L < R`, the set is empty. -/
theorem compact_forward_first_exit_S147 {a b : ℝ} {f : ℝ → ℝ≥0∞} {L R : ℝ≥0∞}
    (hcont : ContinuousOn f (Icc a b)) (hLR : L < R) (hinit : f a < R)
    (hboost : ∀ v ∈ Icc a b, (∀ w ∈ Ico a v, f w < R) → f v ≤ L) :
    ∀ v ∈ Icc a b, f v < R := by
  by_contra hfail
  push Not at hfail
  obtain ⟨v, hv, hfv⟩ := hfail
  have hAc : IsCompact {t | t ∈ Icc a b ∧ R ≤ f t} :=
    isCompact_Icc.of_isClosed_subset (isClosed_Icc.isClosed_le continuousOn_const hcont)
      (fun q hq => hq.1)
  obtain ⟨t, ht, hmin⟩ := hAc.exists_isLeast ⟨v, hv, hfv⟩
  have hta : a < t := lt_of_le_of_ne ht.1.1 (by
    intro h
    exact (not_le_of_gt hinit) (h ▸ ht.2))
  have hbefore : ∀ w ∈ Ico a t, f w < R := by
    intro w hw
    by_contra hbad
    exact (not_le_of_gt hw.2) (hmin ⟨⟨hw.1, hw.2.le.trans ht.1.2⟩, le_of_not_gt hbad⟩)
  exact (not_le_of_gt hLR) (ht.2.trans (hboost t ht.1 hbefore))

/-- A `C^1` path of length `< R` stays in the `R`-ball around its initial point. -/
theorem path_mem_ball_S147 {P : OrientedThreeStage.{u}} (g : P.Metric) {γ : ℝ → P.Carrier}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ) {R : ℝ}
    (hshort : metricPathELength g γ 0 1 < ENNReal.ofReal R) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    γ z ∈ riemannianBallOf g (γ 0) R := by
  have hd := edistOf_le_metricPathELength g hz.1
    (hγ.contMDiffOn.mono (Icc_subset_Icc le_rfl hz.2))
  exact (hd.trans (metricPathELength_mono _ γ le_rfl hz.2)).trans_lt hshort

/-- A path of `R`-ball-controlled curvature along the incoming slab: the flow length stays
`≤ e^{9Kb(s-a)} ℓ` for all `t ∈ [a,s)` (forward first exit + `pathLength_exp_CX2`). -/
theorem slab_path_length_S147 {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
    {Kb ℓ R : ℝ} (hK : 0 ≤ Kb) (hℓ : 0 ≤ ℓ)
    (hroom : Real.exp (9 * Kb * (s - a)) * ℓ < R)
    {γ : ℝ → P.Carrier} (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hRm : ∀ t ∈ Ico a s, ∀ x ∈ riemannianBallOf (G.flow.base.metric t) (γ 0) R,
      Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (G.flow.base.rm04 t x)) ≤ Kb)
    (h0 : metricPathELength (G.flow.base.metric a) γ 0 1 ≤ ENNReal.ofReal ℓ) :
    ∀ t ∈ Ico a s, metricPathELength (G.flow.base.metric t) γ 0 1 ≤
      ENNReal.ofReal (Real.exp (9 * Kb * (s - a)) * ℓ) := by
  have hB1 : 1 ≤ Real.exp (9 * Kb * (s - a)) :=
    Real.one_le_exp (mul_nonneg (by positivity) (sub_nonneg.mpr G.lt.le))
  have hℓR : ℓ < R := (le_mul_of_one_le_left hℓ hB1).trans_lt hroom
  have hR : 0 < R := hℓ.trans_lt hℓR
  let f : ℝ → ℝ≥0∞ := fun t => metricPathELength (G.flow.base.metric t) γ 0 1
  have hmem : ∀ t, f t < ENNReal.ofReal R → ∀ z ∈ Icc (0 : ℝ) 1,
      γ z ∈ riemannianBallOf (G.flow.base.metric t) (γ 0) R :=
    fun t hshort z hz => path_mem_ball_S147 (G.flow.base.metric t) hγ hshort hz
  intro t ht
  have hcarr : ∀ b ∈ Ico a s, Icc a b ⊆ (RealTimeInterval.closedOpen a s G.lt).carrier :=
    fun b hb x hx => ⟨hx.1, hx.2.trans_lt hb.2⟩
  have hreg : ∀ b ∈ Ico a s, Ioo a b ⊆ (RealTimeInterval.closedOpen a s G.lt).regular :=
    fun b hb x hx => ⟨hx.1, hx.2.trans_le hb.2.le⟩
  have hc : ContinuousOn f (Icc a t) :=
    continuousOn_pathLength_CX2 G.flow G.equation (hcarr t ht) hγ
  have hboost : ∀ v ∈ Icc a t, (∀ w ∈ Ico a v, f w < ENNReal.ofReal R) →
      f v ≤ ENNReal.ofReal (Real.exp (9 * Kb * (s - a)) * ℓ) := by
    intro v hv hstay
    have hvs : v < s := hv.2.trans_lt ht.2
    have hle : ∀ w ∈ Ico a v, f w ≤ ENNReal.ofReal (Real.exp (9 * Kb * (v - a)) * ℓ) := by
      intro w hw
      have hws : w ∈ Ico a s := ⟨hw.1, hw.2.trans hvs⟩
      have hb := pathLength_exp_CX2 G.flow G.equation hK (hcarr w hws) (hreg w hws) γ
        (fun t' ht' z hz => hRm t' ⟨ht'.1, ht'.2.trans_lt hws.2⟩ (γ z)
          (hmem t' (hstay t' ⟨ht'.1, ht'.2.trans_lt hw.2⟩) z hz))
        ⟨hw.1, le_rfl⟩ ⟨le_rfl, hw.1⟩
      have he : Real.exp (9 * Kb * |w - a|) ≤ Real.exp (9 * Kb * (v - a)) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hw.1)]
        exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hK (sub_nonneg.mpr hw.2.le)])
      have h1 := mul_le_mul' (ENNReal.ofReal_le_ofReal he) h0
      exact (hb.trans h1).trans_eq (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    have hcl : f v ≤ ENNReal.ofReal (Real.exp (9 * Kb * (v - a)) * ℓ) := by
      rcases eq_or_lt_of_le hv.1 with hva | hva
      · subst hva
        simpa [f] using h0
      · have hcv : ContinuousOn f (closure (Ico a v)) := by
          rw [closure_Ico hva.ne]
          exact hc.mono (Icc_subset_Icc le_rfl hv.2)
        exact le_on_closure hle hcv continuousOn_const (by
          rw [closure_Ico hva.ne]
          exact ⟨hva.le, le_rfl⟩)
    refine hcl.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hK (sub_nonneg.mpr hvs.le)])) hℓ
  have hinit : f a < ENNReal.ofReal R := h0.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hℓR)
  have hLR : ENNReal.ofReal (Real.exp (9 * Kb * (s - a)) * ℓ) < ENNReal.ofReal R :=
    (ENNReal.ofReal_lt_ofReal_iff hR).mpr hroom
  exact hboost t ⟨ht.1, le_rfl⟩ (fun w hw =>
    compact_forward_first_exit_S147 hc hLR hinit hboost w ⟨hw.1, hw.2.le⟩)

/-- G1 (frozen `[FROZEN] CH12-S137 slab_forward`, = S140 G1b): forward slab length lemma.
A point `w` within `ℓ` of `u` at time `a`, with a curvature tube `Kb` on the moving `R`-balls
around `u`, is terminal regular, and `d_term(u,w) ≤ e^{9Kb(s-a)} ℓ`. -/
theorem slab_forward_ball_S147 {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
    (L : G.TerminalLimitMetric) {u w : P.Carrier} {Kb ℓ R : ℝ} (hK : 0 ≤ Kb) (hℓ : 0 ≤ ℓ)
    (hroom : Real.exp (9 * Kb * (s - a)) * ℓ < R)
    (hRm : ∀ t ∈ Ico a s, ∀ x ∈ riemannianBallOf (G.flow.base.metric t) u R,
      Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (G.flow.base.rm04 t x)) ≤ Kb)
    (hw : riemannianEDistOf (G.flow.base.metric a) u w < ENNReal.ofReal ℓ) :
    ∃ u' w' : G.terminalRegularOpen, u'.val = u ∧ w'.val = w ∧
      riemannianEDistOf L.metric u' w' ≤
        ENNReal.ofReal (Real.exp (9 * Kb * (s - a)) * ℓ) := by
  have hcpos : 0 < Real.exp (9 * Kb * (s - a)) := Real.exp_pos _
  have hℓR : ℓ < R / Real.exp (9 * Kb * (s - a)) := by
    rw [lt_div_iff₀ hcpos]
    simpa only [mul_comm] using hroom
  obtain ⟨ρ, hℓρ, hρR⟩ := exists_between hℓR
  have hρ0 : 0 ≤ ρ := hℓ.trans hℓρ.le
  have hρroom : Real.exp (9 * Kb * (s - a)) * ρ < R := by
    rw [lt_div_iff₀ hcpos] at hρR
    simpa only [mul_comm] using hρR
  have hR : 0 < R := (mul_nonneg hcpos.le hρ0).trans_lt hρroom
  -- every point of `U = B_a(u, ρ)` has controlled curvature up to time `s`
  have key : ∀ y ∈ riemannianBallOf (G.flow.base.metric a) u ρ, ∀ t ∈ Ico a s,
      Real.sqrt (normSq0S (G.flow.base.metric t) y 4 (G.flow.base.rm04 t y)) ≤ Kb := by
    intro y hy t ht
    obtain ⟨γ, h0, h1, hγ, -, hlen⟩ := exists_clipped_path_S147 P (G.flow.base.metric a) hy
    have hbound := slab_path_length_S147 G hK hρ0 hρroom hγ (by rw [h0]; exact hRm) hlen.le t ht
    have hmem := path_mem_ball_S147 (G.flow.base.metric t) hγ (z := 1) (R := R)
      (hbound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hρroom))
      ⟨zero_le_one, le_rfl⟩
    rw [h0, h1] at hmem
    exact hRm t ht y hmem
  have hUreg : ∀ y ∈ riemannianBallOf (G.flow.base.metric a) u ρ, y ∈ G.terminalRegularRegion :=
    fun y hy => mem_terminalRegularRegion_of_bound_S56 G
      (isOpen_riemannianBallOf (G.flow.base.metric a) u ρ) hy ⟨le_rfl, G.lt⟩
      (fun y' hy' t ht => key y' hy' t ht)
  obtain ⟨γ, h0, h1, hγ, hclip, hlen⟩ := exists_clipped_path_S147 P (G.flow.base.metric a) hw
  have hγU : ∀ z, γ z ∈ riemannianBallOf (G.flow.base.metric a) u ρ := by
    intro z
    have hmem := path_mem_ball_S147 (G.flow.base.metric a) hγ
      (hlen.trans_le (ENNReal.ofReal_le_ofReal hℓρ.le))
      (projIcc (0 : ℝ) 1 zero_le_one z).2
    rw [hclip z, ← h0]
    exact hmem
  let η : ℝ → G.terminalRegularOpen := fun z => ⟨γ z, hUreg _ (hγU z)⟩
  have hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η :=
    (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff G.terminalRegularOpen η).mp hγ
  let S := terminalPathSolution_CX2 L
  have hS := terminalPathSolution_isSolution_CX2 L
  have hcont : ContinuousOn (fun t => metricPathELength (S.base.metric t) η 0 1) (Icc a s) :=
    continuousOn_pathLength_CX2 S hS (fun t ht => ht) hη
  have hbefore : ∀ t ∈ Ico a s, metricPathELength (S.base.metric t) η 0 1 ≤
      ENNReal.ofReal (Real.exp (9 * Kb * (s - a)) * ℓ) := by
    intro t ht
    change metricPathELength (L.extendedMetric t) η 0 1 ≤ _
    rw [L.extendedMetric_before ht.2, pathLength_restrictOpen_CX2 _ _ _ hη]
    exact slab_path_length_S147 G hK hℓ hroom hγ (by rw [h0]; exact hRm) hlen.le t ht
  have hterm : metricPathELength (S.base.metric s) η 0 1 ≤
      ENNReal.ofReal (Real.exp (9 * Kb * (s - a)) * ℓ) := by
    have hcl : closure (Ico a s) = Icc a s := closure_Ico G.lt.ne
    exact le_on_closure hbefore (hcl ▸ hcont) continuousOn_const
      (by rw [hcl]; exact ⟨G.lt.le, le_rfl⟩)
  refine ⟨η 0, η 1, h0, h1, ?_⟩
  calc riemannianEDistOf L.metric (η 0) (η 1)
      ≤ metricPathELength L.metric η 0 1 :=
        edistOf_le_metricPathELength L.metric zero_le_one hη.contMDiffOn
    _ = metricPathELength (S.base.metric s) η 0 1 := by
        change _ = metricPathELength (L.extendedMetric s) η 0 1
        rw [L.extendedMetric_terminal]
    _ ≤ _ := hterm

end GC.LongTime.Ch12
