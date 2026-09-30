import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Truncation

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

variable {H : ObservedHistory.{u}}

private theorem mem_stageDomain_of_le_of_lt' {j : Fin (H.eventCount + 1)} {t : ℝ}
    (h₁ : H.time j ≤ t) (h₂ : t < H.stageEndTime j) : t ∈ H.stageDomain j := by
  cases j using Fin.lastCases with
  | last =>
    rw [stageEndTime_last] at h₂
    simp only [stageDomain, Fin.lastCases_last, mem_Icc]
    exact ⟨h₁, h₂.le⟩
  | cast m =>
    rw [stageEndTime_castSucc] at h₂
    simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico]
    exact ⟨h₁, h₂⟩

private theorem bounds_of_regularizedCost_eq' {first last : Fin (H.eventCount + 1)}
    {hle : first ≤ last} {T B v : ℝ}
    {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    (hmin : H.regularizedExtendedAction first last T B 0 v α =
      H.regularizedCost first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0)
        (α ⟨first, le_rfl, hle⟩ v))
    (hfin : H.regularizedExtendedAction first last T B 0 v α ≠ ⊤) :
    T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) ∧ T - v ^ 2 ∈ H.stageDomain first := by
  have hne : (H.regularizedActionValues first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0)
      (α ⟨first, le_rfl, hle⟩ v)).Nonempty := by
    by_contra h
    exact hfin (hmin.trans (H.regularizedCost_eq_top_of_no_competitor first last hle T B 0 v _ _
      (not_nonempty_iff_eq_empty.1 h)))
  obtain ⟨A, -, -, hupper, hlower, -⟩ := hne
  exact ⟨hupper, hlower⟩

section SeamBase

variable {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) {T B v : ℝ}
  {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}

variable
  (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
    -B ≤ metricScalarAt (H.stageMetric j t) x)
  (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
    (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
  (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
    (H.event i).RegularCrossing
      (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
      (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
  (hmin : H.regularizedExtendedAction first last T B 0 v α =
    H.regularizedCost first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0)
      (α ⟨first, le_rfl, hle⟩ v))
  (hfin : H.regularizedExtendedAction first last T B 0 v α ≠ ⊤)
include hfloor hα hcross hmin hfin

private theorem exists_hasHistoryLInitialVector_of_eq_time (hv : 0 < v)
    (hT : H.time last = T) (hTe : T < H.stageEndTime last) :
    ∃ Z : TangentSpace ThreeModel (α ⟨last, hle, le_rfl⟩ 0),
      H.HasHistoryLInitialVector T α (α ⟨last, hle, le_rfl⟩ 0) Z := by
  classical
  obtain ⟨hupper, hlower⟩ := bounds_of_regularizedCost_eq' hmin hfin
  have hfl : first < last := by
    refine lt_of_le_of_ne hle fun h => ?_
    subst h
    have := H.time_le_of_mem_stageDomain hlower
    nlinarith [pow_pos hv 2]
  obtain ⟨i, rfl⟩ : ∃ i : Fin H.eventCount, i.succ = last :=
    Fin.exists_succ_eq.2 (ne_of_gt ((Fin.zero_le first).trans_lt hfl))
  have hf : first ≤ i.castSucc := Fin.le_castSucc_iff.2 hfl
  have hnode : ∀ (i' : Fin H.eventCount) (hf' : first ≤ i'.castSucc) (hl' : i'.succ ≤ i.succ),
      ∃ z : (H.event i').old,
        z.val.val = α ⟨i'.castSucc, hf', i'.castSucc_lt_succ.le.trans hl'⟩
          (Real.sqrt (T - H.time i'.succ)) ∧
        (H.event i').oldOutput z = α ⟨i'.succ, hf'.trans i'.castSucc_lt_succ.le, hl'⟩
          (Real.sqrt (T - H.time i'.succ)) := fun i' hf' hl' =>
    let ⟨z, _, h1, h2⟩ := hcross i' hf' hl'
    ⟨z, h1, h2⟩
  have hs0 : Real.sqrt (T - H.time i.succ) = 0 := by rw [hT, sub_self, Real.sqrt_zero]
  have hcs : H.time i.castSucc < T := hT ▸ H.time_strictMono i.castSucc_lt_succ
  have hvT : T - v ^ 2 < T := by nlinarith [pow_pos hv 2]
  have hso : H.regularizedStageStart T 0 i.castSucc = 0 := by
    simp only [regularizedStageStart, stageEndTime_castSucc, hT]
    norm_num
  have hen : H.regularizedStageEnd T v i.succ = 0 := by
    simp only [regularizedStageEnd, hT, max_eq_right hvT.le, sub_self, Real.sqrt_zero]
  have hmax : max (T - v ^ 2) (H.time i.castSucc) < T := max_lt hvT hcs
  have hvo : 0 < H.regularizedStageEnd T v i.castSucc :=
    Real.sqrt_pos.2 (by simp only [regularizedStageEnd] at *; linarith)
  have hve2 : H.regularizedStageEnd T v i.castSucc ^ 2 =
      T - max (T - v ^ 2) (H.time i.castSucc) := Real.sq_sqrt (by linarith)
  have hbo := (H.regularizedStage_bounds le_rfl hv.le hupper hlower
    ⟨i.castSucc, hf, i.castSucc_lt_succ.le⟩).2.2
  have hco : ContinuousOn (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le⟩)
      (Icc 0 (H.regularizedStageEnd T v i.castSucc)) := by
    have h : ContinuousOn (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le⟩)
        (uIcc (H.regularizedStageStart T 0 i.castSucc) (H.regularizedStageEnd T v i.castSucc)) :=
      (hα _).1
    rwa [hso, uIcc_of_le hvo.le] at h
  have hcr := hcross i hf le_rfl
  rw [hs0] at hcr
  obtain ⟨x, -, hx1, -⟩ := hcr
  let p₀ : (H.event i).incoming.terminalRegularOpen := (H.event i).oldTerminal x
  have hp₀ : p₀.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le⟩ 0 :=
    ((H.event i).oldTerminal_eq x).trans hx1
  have hcr' := hcross i hf le_rfl
  rw [hs0] at hcr'
  obtain ⟨F, hsource, hpF, -, hFt, hFcross, -⟩ :=
    MetricCutCapEvent.RegularCrossing.exists_survivor_partialDiffeomorph (H.event i) (p := p₀)
      (by rw [hp₀]; exact hcr')
  let Wo : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen :=
    ⟨F.source, F.open_source⟩
  have hW : ∀ y ∈ Wo, y.val ∈ interior (Subtype.val '' (H.event i).old) := by
    intro y hy
    change y ∈ F.source at hy
    rw [hsource] at hy
    exact hy
  have hUo : IsOpen (Subtype.val '' (Wo : Set (H.event i).incoming.terminalRegularOpen)) :=
    (H.event i).incoming.terminalRegularOpen.isOpen.isOpenMap_subtype_val _ F.open_source
  obtain ⟨b, hb0, hbv', hbmaps⟩ : ∃ b, 0 < b ∧ b < H.regularizedStageEnd T v i.castSucc ∧
      MapsTo (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le⟩) (Icc 0 b)
        (Subtype.val '' (Wo : Set (H.event i).incoming.terminalRegularOpen)) := by
    have hmem : α ⟨i.castSucc, hf, i.castSucc_lt_succ.le⟩ ⁻¹'
        (Subtype.val '' (Wo : Set (H.event i).incoming.terminalRegularOpen)) ∈ 𝓝[≥] 0 := by
      rw [← nhdsWithin_Icc_eq_nhdsGE hvo]
      exact (hco _ ⟨le_rfl, hvo.le⟩).preimage_mem_nhdsWithin (hUo.mem_nhds ⟨p₀, hpF, hp₀⟩)
    obtain ⟨b₀, hb₀, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 hmem
    exact ⟨min b₀ (H.regularizedStageEnd T v i.castSucc / 2), lt_min hb₀ (by linarith),
      (min_le_right _ _).trans_lt (by linarith),
      fun s hs => hsub ⟨hs.1, hs.2.trans (min_le_left _ _)⟩⟩
  have hbw2 : b ^ 2 < H.regularizedStageEnd T v i.castSucc ^ 2 :=
    pow_lt_pow_left₀ hbv' hb0.le two_ne_zero
  have hse : H.time i.succ < H.stageEndTime i.succ := hT ▸ hTe
  have hup : T - (0 : ℝ) ^ 2 ∈ H.stageDomain i.succ :=
    mem_stageDomain_of_le_of_lt' (by rw [hT]; norm_num) (by simpa using hTe)
  have hdown₀ : H.time i.castSucc < T - b ^ 2 := by
    have := le_max_right (T - v ^ 2) (H.time i.castSucc)
    linarith
  have hdown₁ : T - b ^ 2 < H.time i.succ := by
    rw [hT]
    nlinarith [pow_pos hb0 2]
  obtain ⟨G, hG0, hGstage⟩ := H.exists_incomingSlab_stageMetric i.succ hse
  obtain ⟨Wn, hWa, hWb, hrange⟩ := LWindow.exists_seam i G (hG0.trans (H.event_output i).symm)
    hGstage Wo ⟨p₀, hpF⟩ hW le_rfl hb0 hup (by simpa using hTe) hdown₀ hdown₁
  have htarget : F.target ⊆ range (Wn.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩) := by
    intro q hq
    have hy : F.toPartialEquiv.symm q ∈ F.source := F.toPartialEquiv.map_target hq
    obtain ⟨z, hz⟩ : (F.toPartialEquiv.symm q).val ∈
        range (Wn.f ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩) := by
      rw [hrange]
      exact ⟨_, hy, rfl⟩
    refine ⟨z, ?_⟩
    have h1 := Wn.crossing i le_rfl le_rfl z
    rw [hz] at h1
    have h2 := hFcross _ hy
    have h3 : F (F.toPartialEquiv.symm q) = q := F.toPartialEquiv.right_inv hq
    rw [h3] at h2
    exact (H.event i).regularCrossing_right_unique h1 h2
  have hcases : ∀ k : Fin (H.eventCount + 1), i.castSucc ≤ k → k ≤ i.succ →
      k = i.castSucc ∨ k = i.succ := by
    intro k h1 h2
    rcases h1.lt_or_eq with h | h
    · exact Or.inr (le_antisymm h2 (Fin.castSucc_lt_iff_succ_le.1 h))
    · exact Or.inl h.symm
  have hrange' : ∀ j : H.StageInterval i.castSucc i.succ,
      MapsTo (α ⟨j.val, hf.trans j.property.1, j.property.2.trans le_rfl⟩)
        (Icc (H.regularizedStageStart T Wn.a j.val) (H.regularizedStageEnd T Wn.b j.val))
        (range (Wn.f j)) := by
    rintro ⟨k, h1, h2⟩
    rcases hcases k h1 h2 with rfl | rfl
    · dsimp only
      rw [Wn.regularizedStageStart_castSucc_eq, Wn.regularizedStageEnd_castSucc_eq, hWb, hs0]
      intro s hs
      change _ ∈ range (Wn.f ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩)
      rw [hrange]
      exact hbmaps hs
    · dsimp only
      rw [Wn.regularizedStageStart_succ_eq, Wn.regularizedStageEnd_succ_eq, hWa, hs0]
      intro s hs
      obtain rfl : s = 0 := le_antisymm hs.2 hs.1
      exact htarget hFt
  have hbv : Wn.b ≤ v := by rw [hWb]; linarith
  obtain ⟨γ, hγc, hγ, heq, -⟩ := Wn.exists_lift_isLRegularizedGeodesicOn_of_regularizedCost_eq
    hle hf le_rfl le_rfl hWa.ge hbv hupper hlower hfloor α hα hnode hmin hfin hrange'
  obtain ⟨Zx, ⟨hdom, hZeq⟩, -⟩ := Wn.existsUnique_eqOn_lRegularizedCurve_of_regularizedCost_eq
    hle hf le_rfl hWa hbv hupper hlower hfloor α hα hnode hmin hfin γ hγc hγ heq
  have hp : Wn.f ⟨i.succ, Wn.le, le_rfl⟩ (γ 0) = α ⟨i.succ, hle, le_rfl⟩ 0 := by
    have h := heq ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩
    rw [Wn.regularizedStageStart_succ_eq, Wn.regularizedStageEnd_succ_eq, hWa, hs0] at h
    exact h ⟨le_rfl, le_rfl⟩
  refine ⟨mfderiv ThreeModel ThreeModel (Wn.f ⟨i.succ, Wn.le, le_rfl⟩) (γ 0) Zx, i.castSucc, hf,
    Wn, γ 0, Zx, hWa, hp, rfl, hdom, fun j r hr => ?_⟩
  have hr' : r ∈ Icc (H.regularizedStageStart T Wn.a j.val)
      (H.regularizedStageEnd T Wn.b j.val) := by rwa [hWa]
  have hsub := Wn.piece_subset j hr'
  rw [hWa] at hsub
  simp only [Function.comp_apply]
  rw [hZeq hsub]
  exact heq j hr'

theorem exists_hasHistoryLInitialVector_of_regularizedCost_eq_of_mem_Ico (hv : 0 < v)
    (hT : T ∈ Ico (H.time last) (H.stageEndTime last)) :
    ∃ Z : TangentSpace ThreeModel (α ⟨last, hle, le_rfl⟩ 0),
      H.HasHistoryLInitialVector T α (α ⟨last, hle, le_rfl⟩ 0) Z := by
  rcases hT.1.lt_or_eq with hlt | heq
  · exact exists_hasHistoryLInitialVector_of_regularizedCost_eq hle hfloor hα hcross hmin hfin hv
      ⟨hlt, hT.2⟩
  · exact exists_hasHistoryLInitialVector_of_eq_time hle hfloor hα hcross hmin hfin hv heq hT.2

end SeamBase

section MinDomain

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T B v : ℝ}
  {p : (H.stage last).Carrier}

private theorem setLIntegral_eq_zero_of_forall_mem' {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {s : Set X} {f : X → ℝ≥0∞} (hf : ∀ x ∈ s, f x = 0) :
    ∫⁻ x in s, f x ∂μ = 0 := by
  rw [lintegral_def, ← le_zero_iff]
  refine iSup₂_le fun g hg => ?_
  rw [SimpleFunc.lintegral, le_zero_iff]
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases eq_or_ne c 0 with rfl | hc
  · exact zero_mul _
  rw [Measure.restrict_apply (g.measurableSet_preimage _)]
  have hempty : g ⁻¹' {c} ∩ s = ∅ := by
    refine eq_empty_of_forall_notMem fun x hx => hc ?_
    have hgx : g x ≤ f x := hg x
    rw [hf x hx.2, le_zero_iff] at hgx
    exact (mem_singleton_iff.mp hx.1).symm.trans hgx
  rw [hempty, measure_empty, mul_zero]

variable (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
  -B ≤ metricScalarAt (H.stageMetric j t) x)
include hfloor

theorem exists_historyLExp_eq_of_mem_regularMinimizerEndpoints_of_mem_Ico (hv : 0 < v)
    (hT : T ∈ Ico (H.time last) (H.stageEndTime last)) {q : (H.stage first).Carrier}
    (hq : q ∈ H.regularMinimizerEndpoints first last hle T B v p)
    (hfin : H.regularizedCost first last hle T B 0 v p q ≠ ⊤) :
    ∃ Z : H.historyLExpDomain hle T v p,
      Z.1 ∈ H.historyMinDomain hle T B v p ∧ H.historyLExp hle T v p Z = q := by
  obtain ⟨α, hac, hp, hq, hcross, hmin⟩ := hq
  subst hp hq
  have hfin' : H.regularizedExtendedAction first last T B 0 v α ≠ ⊤ := by
    rw [hmin]
    exact hfin
  have hgeo := isHistoryLGeodesicOn_of_regularizedCost_eq hle hfloor hac hcross hmin hfin' hv
  obtain ⟨Z, hZ⟩ := exists_hasHistoryLInitialVector_of_regularizedCost_eq_of_mem_Ico hle hfloor
    hac hcross hmin hfin' hv hT
  exact ⟨⟨Z, α, hgeo, hZ⟩, ⟨α, hgeo, hZ, hac, rfl, hmin, hfin'⟩, historyLExp_eq hv _ hgeo hZ⟩

theorem image_historyMinDomain_of_mem_Ico (hv : 0 < v)
    (hT : T ∈ Ico (H.time last) (H.stageEndTime last)) :
    H.historyLExp hle T v p '' (Subtype.val ⁻¹' H.historyMinDomain hle T B v p) =
      H.regularMinimizerEndpoints first last hle T B v p ∩
        {q | H.regularizedCost first last hle T B 0 v p q ≠ ⊤} := by
  refine (image_historyMinDomain_subset hv).antisymm fun q ⟨hq, hfin⟩ => ?_
  obtain ⟨Z, hZ, rfl⟩ :=
    exists_historyLExp_eq_of_mem_regularMinimizerEndpoints_of_mem_Ico hfloor hv hT hq hfin
  exact ⟨Z, hZ, rfl⟩

theorem setLIntegral_regularMinimizerEndpoints_eq_of_mem_Ico (hv : 0 < v)
    (hT : T ∈ Ico (H.time last) (H.stageEndTime last))
    [MeasurableSpace (H.stage first).Carrier] (μ : Measure (H.stage first).Carrier) :
    ∫⁻ q in H.regularMinimizerEndpoints first last hle T B v p,
      H.regularizedDensity first last hle T B v p q ∂μ =
    ∫⁻ q in H.historyLExp hle T v p '' (Subtype.val ⁻¹' H.historyMinDomain hle T B v p),
      H.regularizedDensity first last hle T B v p q ∂μ := by
  set E := H.regularMinimizerEndpoints first last hle T B v p
  set I := H.historyLExp hle T v p '' (Subtype.val ⁻¹' H.historyMinDomain hle T B v p)
  have hIE : I ⊆ E := (image_historyMinDomain_subset hv).trans inter_subset_left
  refine le_antisymm ?_ (lintegral_mono_set hIE)
  have hEI : E ⊆ I ∪ E \ I := fun q hq => by
    by_cases h : q ∈ I
    exacts [Or.inl h, Or.inr ⟨hq, h⟩]
  have hzero : ∀ q ∈ E \ I, H.regularizedDensity first last hle T B v p q = 0 := by
    intro q hq
    have hI : I = H.regularMinimizerEndpoints first last hle T B v p ∩
        {q | H.regularizedCost first last hle T B 0 v p q ≠ ⊤} :=
      image_historyMinDomain_of_mem_Ico hfloor hv hT
    rw [hI] at hq
    apply regularizedDensity_eq_zero_of_regularizedCost_eq_top
    by_contra hne
    exact hq.2 ⟨hq.1, hne⟩
  calc ∫⁻ q in E, H.regularizedDensity first last hle T B v p q ∂μ
      ≤ ∫⁻ q in I ∪ E \ I, H.regularizedDensity first last hle T B v p q ∂μ :=
        lintegral_mono_set hEI
    _ ≤ ∫⁻ q in I, H.regularizedDensity first last hle T B v p q ∂μ +
        ∫⁻ q in E \ I, H.regularizedDensity first last hle T B v p q ∂μ :=
        lintegral_union_le _ _ _
    _ = ∫⁻ q in I, H.regularizedDensity first last hle T B v p q ∂μ := by
        rw [setLIntegral_eq_zero_of_forall_mem' μ hzero, add_zero]

end MinDomain

section InitialVector

private theorem exists_mfderivWithin_castSucc_eq {first : Fin (H.eventCount + 1)}
    {i : Fin H.eventCount} {T : ℝ} (hT : H.time i.succ = T)
    {α : (j : H.StageInterval first i.succ) → ℝ → (H.stage j.val).Carrier}
    {lo : Fin (H.eventCount + 1)} (hlo : first ≤ lo) (W : H.LWindow lo i.succ T)
    (hl : lo ≤ i.castSucc) (x : W.X) (Zx : TangentSpace ThreeModel x) (ha : W.a = 0)
    (heq : ∀ j : H.StageInterval lo i.succ,
      EqOn (W.f j ∘ lRegularizedCurve W.S T x Zx) (α ⟨j.val, hlo.trans j.property.1, j.property.2⟩)
        (Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T W.b j.val))) :
    W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le⟩ x =
        α ⟨i.castSucc, hlo.trans hl, i.castSucc_lt_succ.le⟩ 0 ∧
      ∃ e > 0, ∀ e' ∈ Ioc 0 e, mfderivWithin 𝓘(ℝ, ℝ) ThreeModel
        (α ⟨i.castSucc, hlo.trans hl, i.castSucc_lt_succ.le⟩) (Icc 0 e') 0 1 =
          (2 : ℝ) • mfderiv ThreeModel ThreeModel
            (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le⟩) x Zx := by
  have hb : 0 < W.b := ha ▸ W.lt
  have hTreg : T ∈ W.D.regular := by simpa [ha] using W.regular W.a ⟨le_rfl, W.lt.le⟩
  have hcs : H.time i.castSucc < T := hT ▸ H.time_strictMono i.castSucc_lt_succ
  have hstart : H.regularizedStageStart T 0 i.castSucc = 0 := by
    simp only [regularizedStageStart, stageEndTime_castSucc, hT]
    norm_num
  have hepos : 0 < H.regularizedStageEnd T W.b i.castSucc := by
    apply Real.sqrt_pos.2
    have := max_lt (show T - W.b ^ 2 < T by nlinarith) hcs
    linarith
  have hEq : EqOn (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le⟩ ∘ lRegularizedCurve W.S T x Zx)
      (α ⟨i.castSucc, hlo.trans hl, i.castSucc_lt_succ.le⟩)
      (Icc 0 (H.regularizedStageEnd T W.b i.castSucc)) := by
    have := heq ⟨i.castSucc, hl, i.castSucc_lt_succ.le⟩
    rw [hstart] at this
    exact this
  have hcd : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel (lRegularizedCurve W.S T x Zx) 0 := by
    have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ∞
        (fun r : ℝ => ((Zx, r) : ThreeSpace × ℝ)) 0 :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact ((lRegularizedCurve_smoothAt W.S W.solution T x Zx hTreg).comp 0 hpair).mdifferentiableAt
      (by simp)
  have hfd : MDifferentiableAt ThreeModel ThreeModel (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le⟩)
      (lRegularizedCurve W.S T x Zx 0) :=
    (W.localDiffeomorph _ _).mdifferentiableAt (by simp)
  refine ⟨?_, _, hepos, fun e' he' => ?_⟩
  · have h0 := hEq ⟨le_rfl, hepos.le⟩
    simp only [Function.comp_apply, lRegularizedCurve_zero] at h0
    exact h0
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (0 : ℝ) e') 0 :=
    uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_Icc he'.1 0 ⟨le_rfl, he'.1.le⟩)
  have hEq' := hEq.mono (Icc_subset_Icc le_rfl he'.2)
  have key : mfderivWithin 𝓘(ℝ, ℝ) ThreeModel
      (α ⟨i.castSucc, hlo.trans hl, i.castSucc_lt_succ.le⟩) (Icc 0 e') 0 =
      mfderivWithin 𝓘(ℝ, ℝ) ThreeModel
        (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le⟩ ∘ lRegularizedCurve W.S T x Zx)
        (Icc 0 e') 0 :=
    (mfderivWithin_congr hEq' (hEq' ⟨le_rfl, he'.1.le⟩)).symm
  rw [key, mfderivWithin_eq_mfderiv hu (hfd.comp 0 hcd), mfderiv_comp 0 hfd hcd]
  change mfderiv ThreeModel ThreeModel (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le⟩)
    (lRegularizedCurve W.S T x Zx 0)
    (lVelocity (I := ThreeModel) (lRegularizedCurve W.S T x Zx) 0) = _
  rw [lRegularizedCurve_velocity_zero W.S W.solution T x Zx hTreg]
  have key₂ : ∀ y : W.X, y = x →
      mfderiv ThreeModel ThreeModel (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le⟩) y
        ((2 : ℝ) • Zx) =
      (2 : ℝ) • mfderiv ThreeModel ThreeModel
        (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le⟩) x Zx := by
    rintro y rfl
    rw [map_smul]
  exact key₂ _ (lRegularizedCurve_zero _ _ _ _)

private theorem lo_le_castSucc {lo : Fin (H.eventCount + 1)} {i : Fin H.eventCount} {T : ℝ}
    (hT : H.time i.succ = T) (W : H.LWindow lo i.succ T) (ha : W.a = 0) : lo ≤ i.castSucc := by
  refine Fin.le_castSucc_iff.2 (lt_of_le_of_ne W.le fun h => ?_)
  have hlow : T - W.b ^ 2 ∈ H.stageDomain i.succ := h ▸ W.lower
  have := H.time_le_of_mem_stageDomain hlow
  have hb : 0 < W.b := ha ▸ W.lt
  nlinarith [pow_pos hb 2]

theorem HasHistoryLInitialVector.eq_of_eqOn_of_time_succ_eq {first : Fin (H.eventCount + 1)}
    {i : Fin H.eventCount} (hf : first ≤ i.castSucc) {T : ℝ} (hT : H.time i.succ = T)
    {α β : (j : H.StageInterval first i.succ) → ℝ → (H.stage j.val).Carrier}
    {p : (H.stage i.succ).Carrier} {Z Z' : TangentSpace ThreeModel p}
    (hα : H.HasHistoryLInitialVector T α p Z) (hβ : H.HasHistoryLInitialVector T β p Z')
    {η : ℝ} (hη : 0 < η)
    (h : EqOn (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le⟩)
      (β ⟨i.castSucc, hf, i.castSucc_lt_succ.le⟩)
      (Icc 0 η)) : Z = Z' := by
  classical
  obtain ⟨lo₁, hlo₁, W₁, x₁, Zx₁, ha₁, -, hZ₁, -, heq₁⟩ := hα
  obtain ⟨lo₂, hlo₂, W₂, x₂, Zx₂, ha₂, -, hZ₂, -, heq₂⟩ := hβ
  have hl₁ := lo_le_castSucc hT W₁ ha₁
  have hl₂ := lo_le_castSucc hT W₂ ha₂
  obtain ⟨hx₁, e₁, he₁, hd₁⟩ := exists_mfderivWithin_castSucc_eq hT hlo₁ W₁ hl₁ x₁ Zx₁ ha₁ heq₁
  obtain ⟨hx₂, e₂, he₂, hd₂⟩ := exists_mfderivWithin_castSucc_eq hT hlo₂ W₂ hl₂ x₂ Zx₂ ha₂ heq₂
  have hy : W₂.f ⟨i.castSucc, hl₂, i.castSucc_lt_succ.le⟩ x₂ =
      W₁.f ⟨i.castSucc, hl₁, i.castSucc_lt_succ.le⟩ x₁ :=
    hx₂.trans ((h ⟨le_rfl, hη.le⟩).symm.trans hx₁.symm)
  have he : 0 < min η (min e₁ e₂) := lt_min hη (lt_min he₁ he₂)
  have hc := mfderivWithin_congr (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    (h.mono (Icc_subset_Icc le_rfl (min_le_left η (min e₁ e₂)))) (h ⟨le_rfl, hη.le⟩)
  have k₁ := hd₁ _ ⟨he, (min_le_right _ _).trans (min_le_left _ _)⟩
  have k₂ := hd₂ _ ⟨he, (min_le_right _ _).trans (min_le_right _ _)⟩
  rw [hc] at k₁
  have hV : mfderiv ThreeModel ThreeModel (W₁.f ⟨i.castSucc, hl₁, i.castSucc_lt_succ.le⟩) x₁ Zx₁ =
      mfderiv ThreeModel ThreeModel (W₂.f ⟨i.castSucc, hl₂, i.castSucc_lt_succ.le⟩) x₂ Zx₂ :=
    smul_right_injective ThreeSpace (two_ne_zero : (2 : ℝ) ≠ 0) (k₁.symm.trans k₂)
  have : Nonempty W₁.X := ⟨x₁⟩
  have hψ₁ := W₁.eventually_regularCrossing_invFun i hl₁ le_rfl x₁
  set ψ : (H.stage i.castSucc).Carrier → (H.stage i.succ).Carrier := fun q =>
    W₁.f ⟨i.succ, hl₁.trans i.castSucc_lt_succ.le, le_rfl⟩
      (Function.invFun (W₁.f ⟨i.castSucc, hl₁, i.castSucc_lt_succ.le.trans le_rfl⟩) q) with hψdef
  have hψ₂ : ∀ᶠ q in 𝓝 (W₂.f ⟨i.castSucc, hl₂, i.castSucc_lt_succ.le.trans le_rfl⟩ x₂),
      (H.event i).RegularCrossing q (ψ q) := by
    change ∀ᶠ q in 𝓝 (W₂.f ⟨i.castSucc, hl₂, i.castSucc_lt_succ.le⟩ x₂), _
    rw [hy]
    exact hψ₁
  have m₁ := W₁.mfderiv_apply_mfderiv_eq_of_regularCrossing i hl₁ le_rfl x₁ hψ₁ Zx₁
  have m₂ := W₂.mfderiv_apply_mfderiv_eq_of_regularCrossing i hl₂ le_rfl x₂ hψ₂ Zx₂
  rw [← hZ₁, ← hZ₂]
  change mfderiv ThreeModel ThreeModel
      (W₁.f ⟨i.succ, hl₁.trans i.castSucc_lt_succ.le, le_rfl⟩) x₁ Zx₁ =
    mfderiv ThreeModel ThreeModel (W₂.f ⟨i.succ, hl₂.trans i.castSucc_lt_succ.le, le_rfl⟩) x₂ Zx₂
  rw [← m₁, ← m₂]
  change mfderiv ThreeModel ThreeModel ψ (W₁.f ⟨i.castSucc, hl₁, i.castSucc_lt_succ.le⟩ x₁)
      (mfderiv ThreeModel ThreeModel (W₁.f ⟨i.castSucc, hl₁, i.castSucc_lt_succ.le⟩) x₁ Zx₁) =
    mfderiv ThreeModel ThreeModel ψ (W₂.f ⟨i.castSucc, hl₂, i.castSucc_lt_succ.le⟩ x₂)
      (mfderiv ThreeModel ThreeModel (W₂.f ⟨i.castSucc, hl₂, i.castSucc_lt_succ.le⟩) x₂ Zx₂)
  rw [hV, hy]

end InitialVector

section Injective

variable {first last k : Fin (H.eventCount + 1)} {hle : first ≤ last} {T B v₁ v₂ : ℝ}
  {p : (H.stage last).Carrier}

private theorem lt_stageEndTime_of_lt'' {j k : Fin (H.eventCount + 1)} {t : ℝ}
    (ht : t ∈ H.stageDomain j) (hjk : j < k) : t < H.stageEndTime j := by
  cases j using Fin.lastCases with
  | last => exact absurd hjk (not_lt.2 (Fin.le_last k))
  | cast i =>
    simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at ht
    rw [stageEndTime_castSucc]
    exact ht.2

private theorem eqOn_of_truncate_eq (hkl : k ≤ last)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hv₁ : 0 < v₁) (h12 : v₁ < v₂) (hk : T - v₁ ^ 2 ∈ H.stageDomain k)
    {α β : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    (hαg : H.IsHistoryLGeodesicOn hle T v₂ α)
    (hαac : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v₂ j.val))
    (hαp : α ⟨last, hle, le_rfl⟩ 0 = p)
    (hαmin : H.regularizedExtendedAction first last T B 0 v₂ α =
      H.regularizedCost first last hle T B 0 v₂ (α ⟨last, hle, le_rfl⟩ 0)
        (α ⟨first, le_rfl, hle⟩ v₂))
    (hαfin : H.regularizedExtendedAction first last T B 0 v₂ α ≠ ⊤)
    (hβg : H.IsHistoryLGeodesicOn hle T v₂ β)
    (hβac : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (β j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v₂ j.val))
    (hβp : β ⟨last, hle, le_rfl⟩ 0 = p)
    (hβmin : H.regularizedExtendedAction first last T B 0 v₂ β =
      H.regularizedCost first last hle T B 0 v₂ (β ⟨last, hle, le_rfl⟩ 0)
        (β ⟨first, le_rfl, hle⟩ v₂))
    (hβfin : H.regularizedExtendedAction first last T B 0 v₂ β ≠ ⊤)
    (hfk : first ≤ k) (hx : α ⟨k, hfk, hkl⟩ v₁ = β ⟨k, hfk, hkl⟩ v₁)
    (j : H.StageInterval first last) (hkj : k ≤ j.val) {r : ℝ}
    (hr : r ∈ Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v₂ j.val))
    (hrv : r ≤ v₁) : α j r = β j r := by
  classical
  obtain ⟨hupper, hlower⟩ := bounds_of_regularizedCost_eq' hαmin hαfin
  have hv₂ : 0 < v₂ := hv₁.trans h12
  have hkI : T - v₁ ^ 2 ∈ Icc (H.time k) (H.stageEndTime k) :=
    ⟨H.time_le_of_mem_stageDomain hk, H.le_stageEndTime_of_mem_stageDomain hk⟩
  have hnode : ∀ {γ : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier},
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        (H.event i).RegularCrossing
          (γ ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
          (γ ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)))) →
      ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = γ ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = γ ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ)) := fun hc i hf hl =>
    let ⟨z, _, h1, h2⟩ := hc i hf hl
    ⟨z, h1, h2⟩
  have hcα := regularizedExtendedAction_truncate_eq_regularizedCost hle hfk hkl hv₁.le h12.le hk
    hfloor α hαac (hnode hαg.2.1) hαmin hαfin
  have hcβ := regularizedExtendedAction_truncate_eq_regularizedCost hle hfk hkl hv₁.le h12.le hk
    hfloor β hβac (hnode hβg.2.1) hβmin hβfin
  have hU : H.regularizedExtendedAction k last T B 0 v₁
        (fun j => α ⟨j.val, hfk.trans j.property.1, j.property.2⟩) =
      H.regularizedExtendedAction k last T B 0 v₁
        (fun j => β ⟨j.val, hfk.trans j.property.1, j.property.2⟩) := by
    rw [hcα.1, hcβ.1, hαp, hβp, hx]
  let γ : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier := fun j =>
    if k < j.val then β j else if j.val < k then α j else piecewise (Iic v₁) (β j) (α j)
  have hγgt : ∀ j : H.StageInterval first last, k < j.val → γ j = β j := fun j h => by
    simp only [γ, ite_eq_left h]
  have hγlt : ∀ j : H.StageInterval first last, j.val < k → γ j = α j := fun j h => by
    simp only [γ, ite_eq_right (not_lt.2 h.le), ite_eq_left h]
  have hγeq : ∀ j : H.StageInterval first last, j.val = k →
      γ j = piecewise (Iic v₁) (β j) (α j) := fun j h => by
    simp only [γ, h, lt_irrefl, ite_false]
  have hγle : ∀ (j : H.StageInterval first last) (r : ℝ), k ≤ j.val → r ≤ v₁ → γ j r = β j r := by
    intro j r hj hr
    rcases hj.lt_or_eq with h | h
    · rw [hγgt j h]
    · rw [hγeq j h.symm, piecewise_eq_of_mem _ _ _ (mem_Iic.2 hr)]
  have hγge : ∀ (j : H.StageInterval first last) (r : ℝ), j.val ≤ k → v₁ ≤ r → γ j r = α j r := by
    intro j r hj hr
    rcases hj.lt_or_eq with h | h
    · rw [hγlt j h]
    rcases hr.lt_or_eq with h' | h'
    · rw [hγeq j h, piecewise_eq_of_notMem _ _ _ fun hm => absurd (mem_Iic.1 hm) (not_le.2 h')]
    · subst h'
      obtain rfl : j = ⟨k, hfk, hkl⟩ := Subtype.ext h
      rw [hγeq _ rfl, piecewise_eq_of_mem _ _ _ (mem_Iic.2 le_rfl)]
      exact hx.symm
  have hγac : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (γ j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v₂ j.val) := by
    intro j
    rcases lt_trichotomy j.val k with h | h | h
    · rw [hγlt j h]
      exact hαac j
    · obtain rfl : j = ⟨k, hfk, hkl⟩ := Subtype.ext h
      rw [hγeq _ rfl]
      have hs : H.regularizedStageStart T 0 k ≤ v₁ :=
        (regularizedStageStart_le_of_le le_rfl hv₁.le k).trans
          (H.regularizedStageStart_eq_of_mem_Icc hv₁.le hkI).le
      have he : v₁ ≤ H.regularizedStageEnd T v₂ k :=
        (H.regularizedStageEnd_eq_of_mem_stageDomain hv₁.le hk).symm.le.trans
          (regularizedStageEnd_le_of_le hv₁.le h12.le k)
      have hb := (H.regularizedStage_bounds le_rfl hv₂.le hupper hlower ⟨k, hfk, hkl⟩).2.1
      dsimp only at hb ⊢
      refine Manifold.absolutelyContinuousOnInterval_piecewise_Iic ?_ ?_ hs he hx.symm
      · apply Manifold.absolutelyContinuousOnInterval_mono (hβac _)
        rw [uIcc_of_le hs, uIcc_of_le hb]
        exact Icc_subset_Icc le_rfl he
      · apply Manifold.absolutelyContinuousOnInterval_mono (hαac _)
        rw [uIcc_of_le he, uIcc_of_le hb]
        exact Icc_subset_Icc hs le_rfl
    · rw [hγgt j h]
      exact hβac j
  have hγp : γ ⟨last, hle, le_rfl⟩ 0 = p := (hγle _ 0 hkl hv₁.le).trans hβp
  have hγq : γ ⟨first, le_rfl, hle⟩ v₂ = α ⟨first, le_rfl, hle⟩ v₂ := hγge _ v₂ hfk h12.le
  have hγcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (γ ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (γ ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))) := by
    intro i hf hl
    rcases le_or_gt k i.castSucc with hki | hik
    · have hks := hki.trans_lt i.castSucc_lt_succ
      have hw : Real.sqrt (T - H.time i.succ) ≤ v₁ := by
        have h1 := lt_stageEndTime_of_lt'' hk hks
        have h2 := stageEndTime_le_time_of_lt hks
        exact ((Real.sqrt_lt' hv₁).2 (by linarith)).le
      rw [hγle ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ _ hki hw,
        hγle ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ _ hks.le hw]
      exact hβg.2.1 i hf hl
    · have hsk : i.succ ≤ k := Fin.castSucc_lt_iff_succ_le.1 hik
      have hw : v₁ ≤ Real.sqrt (T - H.time i.succ) := by
        apply Real.le_sqrt_of_sq_le
        have := (H.time_strictMono.monotone hsk).trans (H.time_le_of_mem_stageDomain hk)
        linarith
      rw [hγge ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ _ hik.le hw,
        hγge ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ _ hsk hw]
      exact hαg.2.1 i hf hl
  have hsc : ∀ t ∈ Ioo (H.regularizedStageStart T 0 k) (H.regularizedStageEnd T v₂ k),
      ∀ x : (H.stage k).Carrier, -B ≤ metricScalarAt (H.stageMetric k (T - t ^ 2)) x :=
    fun t ht x => hfloor k _ (H.mapsTo_regularizedStage_Ioo T 0 v₂ k ht) x
  have hsplitγ := regularizedExtendedAction_eq_add_at_parameter k hfk hkl le_rfl hv₁.le h12.le hk
    hsc γ hγac
  have hsplitα := regularizedExtendedAction_eq_add_at_parameter k hfk hkl le_rfl hv₁.le h12.le hk
    hsc α hαac
  have hUγ : H.regularizedExtendedAction k last T B 0 v₁
        (fun j => γ ⟨j.val, hfk.trans j.property.1, j.property.2⟩) =
      H.regularizedExtendedAction k last T B 0 v₁
        (fun j => β ⟨j.val, hfk.trans j.property.1, j.property.2⟩) := by
    unfold regularizedExtendedAction
    refine Finset.sum_congr rfl fun j _ =>
      H.stageRegularizedExtendedAction_congr j.val T B _ _ _ _ fun r hr => ?_
    have hb := (H.regularizedStage_bounds le_rfl hv₁.le hupper hk j).2.2
    exact hγle _ r j.property.1 (hr.2.le.trans hb)
  have hLγ : H.regularizedExtendedAction first k T B v₁ v₂
        (fun j => γ ⟨j.val, j.property.1, j.property.2.trans hkl⟩) =
      H.regularizedExtendedAction first k T B v₁ v₂
        (fun j => α ⟨j.val, j.property.1, j.property.2.trans hkl⟩) := by
    unfold regularizedExtendedAction
    refine Finset.sum_congr rfl fun j _ =>
      H.stageRegularizedExtendedAction_congr j.val T B _ _ _ _ fun r hr => ?_
    have hb := (H.regularizedStage_bounds hv₁.le h12.le hkI hlower j).1
    exact hγge _ r j.property.2 (hb.trans hr.1.le)
  have hγact : H.regularizedExtendedAction first last T B 0 v₂ γ =
      H.regularizedExtendedAction first last T B 0 v₂ α := by
    rw [hsplitγ, hsplitα, hUγ, hLγ, ← hU]
  have hγmin : H.regularizedExtendedAction first last T B 0 v₂ γ =
      H.regularizedCost first last hle T B 0 v₂ (γ ⟨last, hle, le_rfl⟩ 0)
        (γ ⟨first, le_rfl, hle⟩ v₂) := by
    rw [hγact, hγp, hγq, hαmin, hαp]
  have hγfin : H.regularizedExtendedAction first last T B 0 v₂ γ ≠ ⊤ := by
    rw [hγact]
    exact hαfin
  have hagree := IsHistoryLGeodesicOn.eqOn_of_eqOn_Ioi hfloor hαg hαac hγac hγcross hγmin hγfin
    hv₂ h12 fun j r hr hvr => by
      rcases le_or_gt j.val k with hjk | hkj
      · exact (hγge j r hjk hvr.le).symm
      · have he := H.regularizedStageEnd_eq_of_lt hk hkj (pow_le_pow_left₀ hv₁.le h12.le 2)
        have hb := (H.regularizedStage_bounds le_rfl hv₁.le hupper hk
          ⟨j.val, hkj.le, j.property.2⟩).2.2
        dsimp only at hb
        linarith [hr.2]
  exact (hagree j hr).trans (hγle j r hkj hrv)

theorem injOn_historyLExp_of_lt_of_mem_Ico (hkl : k ≤ last)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hT : T ∈ Ico (H.time last) (H.stageEndTime last)) (hv₁ : 0 < v₁) (h12 : v₁ < v₂)
    (hk : T - v₁ ^ 2 ∈ H.stageDomain k) :
    InjOn (H.historyLExp hkl T v₁ p) (Subtype.val ⁻¹' H.historyMinDomain hle T B v₂ p) := by
  classical
  intro Z₁ hZ₁ Z₂ hZ₂ hE
  apply Subtype.ext
  obtain ⟨α, hαg, hαi, hαac, hαp, hαmin, hαfin⟩ := hZ₁
  obtain ⟨β, hβg, hβi, hβac, hβp, hβmin, hβfin⟩ := hZ₂
  rw [← hαp] at hαmin
  rw [← hβp] at hβmin
  obtain ⟨hupper, hlower⟩ := bounds_of_regularizedCost_eq' hαmin hαfin
  have hv₂ : 0 < v₂ := hv₁.trans h12
  have hfk := first_le_of_mem_stageDomain hv₁.le h12.le hlower hk
  have hxα : H.historyLExp hkl T v₁ p Z₁ = α ⟨k, hfk, hkl⟩ v₁ :=
    historyLExp_eq hv₁ Z₁ (isHistoryLGeodesicOn_truncate hfloor hfk hkl hv₁ h12.le hk hαg hαac
      hαmin hαfin) (hαi.truncate hv₁ hfk hk)
  have hxβ : H.historyLExp hkl T v₁ p Z₂ = β ⟨k, hfk, hkl⟩ v₁ :=
    historyLExp_eq hv₁ Z₂ (isHistoryLGeodesicOn_truncate hfloor hfk hkl hv₁ h12.le hk hβg hβac
      hβmin hβfin) (hβi.truncate hv₁ hfk hk)
  have hx : α ⟨k, hfk, hkl⟩ v₁ = β ⟨k, hfk, hkl⟩ v₁ := hxα.symm.trans (hE.trans hxβ)
  have hagree := eqOn_of_truncate_eq hkl hfloor hv₁ h12 hk hαg hαac hαp hαmin hαfin hβg hβac hβp
    hβmin hβfin hfk hx
  rcases hT.1.lt_or_eq with hlt | heq
  · have hstart : H.regularizedStageStart T 0 last = 0 :=
      H.regularizedStageStart_eq_of_mem_Icc le_rfl hupper
    have hη : 0 < min v₁ (H.regularizedStageEnd T v₂ last) := by
      refine lt_min hv₁ (Real.sqrt_pos.2 ?_)
      have := max_lt (show T - v₂ ^ 2 < T by nlinarith) hlt
      linarith
    refine HasHistoryLInitialVector.eq_of_eqOn hle hlt hαi hβi hη fun r hr => ?_
    exact hagree ⟨last, hle, le_rfl⟩ hkl
      ⟨hstart.le.trans hr.1, hr.2.trans (min_le_right _ _)⟩ (hr.2.trans (min_le_left _ _))
  · have hfl : first < last := by
      refine lt_of_le_of_ne hle fun h => ?_
      subst h
      have := H.time_le_of_mem_stageDomain hlower
      nlinarith [pow_pos hv₂ 2]
    obtain ⟨i, rfl⟩ : ∃ i : Fin H.eventCount, i.succ = last :=
      Fin.exists_succ_eq.2 (ne_of_gt ((Fin.zero_le first).trans_lt hfl))
    have hf : first ≤ i.castSucc := Fin.le_castSucc_iff.2 hfl
    have hks : k ≤ i.castSucc := by
      refine Fin.le_castSucc_iff.2 (lt_of_le_of_ne hkl fun h => ?_)
      subst h
      have := H.time_le_of_mem_stageDomain hk
      nlinarith [pow_pos hv₁ 2]
    have hcs : H.time i.castSucc < T := heq ▸ H.time_strictMono i.castSucc_lt_succ
    have hstart : H.regularizedStageStart T 0 i.castSucc = 0 := by
      simp only [regularizedStageStart, stageEndTime_castSucc, ← heq]
      norm_num
    have hη : 0 < min v₁ (H.regularizedStageEnd T v₂ i.castSucc) := by
      refine lt_min hv₁ (Real.sqrt_pos.2 ?_)
      have := max_lt (show T - v₂ ^ 2 < T by nlinarith) hcs
      linarith
    refine HasHistoryLInitialVector.eq_of_eqOn_of_time_succ_eq hf heq hαi hβi hη fun r hr => ?_
    exact hagree ⟨i.castSucc, hf, i.castSucc_lt_succ.le⟩ hks
      ⟨hstart.le.trans hr.1, hr.2.trans (min_le_right _ _)⟩ (hr.2.trans (min_le_left _ _))

end Injective

end ObservedHistory

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

theorem exists_reducedVolume_eq_lintegral_image_historyMinDomain_of_mem_Ico :
    ∃ b : ℝ, ∀ B₀ : ℝ, b ≤ B₀ → ∀ (k : Fin (H.eventCount + 1)) (p : (H.stage k).Carrier)
      (T v : ℝ)
      (hle : H.toHistory.activeStage (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)) ≤ k),
      0 < v → T ∈ Ico (H.toHistory.time k) (H.toHistory.stageEndTime k) →
      H.reducedVolume k p T v =
        ∫⁻ q in H.toHistory.historyLExp hle T v p ''
            (Subtype.val ⁻¹' H.toHistory.historyMinDomain hle T B₀ v p),
          H.toHistory.regularizedDensity _ k hle T B₀ v p q
          ∂riemannianVolumeMeasure ThreeModel
            (H.stage (H.toHistory.activeStage
              (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)))).Carrier
            (H.toHistory.stageMetric _ (T - v ^ 2)) := by
  obtain ⟨b, hb⟩ := H.exists_reducedVolume_eq_lintegral
  obtain ⟨b', -, hfloor⟩ := H.exists_stageMetric_scalar_lower_bound
  refine ⟨max b b', fun B₀ hB₀ k p T v hle hv hT => ?_⟩
  refine (hb B₀ (le_of_max_le_left hB₀) k p T v hle).trans ?_
  exact ObservedHistory.setLIntegral_regularMinimizerEndpoints_eq_of_mem_Ico (H := H.toHistory)
    (first := H.toHistory.activeStage (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)))
    (last := k) (hle := hle) (T := T) (B := B₀) (v := v) (p := p)
    (fun j t ht x => (neg_le_neg (le_of_max_le_right hB₀)).trans (hfloor j t ht x)) hv hT _

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
