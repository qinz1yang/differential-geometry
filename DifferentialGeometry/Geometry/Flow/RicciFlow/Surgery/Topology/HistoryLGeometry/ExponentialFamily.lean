import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.ExponentialSmooth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.Truncation

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

open private mem_regularizedStage_Icc eq_of_mem_Ioo_of_mem_Icc exists_mem_Ioo_not_mem_range
  exists_stage_nhds LWindow.mem_range_of_mem_Icc exists_transfer_family IsHistoryLGeodesicPrefix
  HasPrefixFamily isHistoryLGeodesicPrefix_congr hasPrefixFamily_step lo_le_of_lt_b from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.ExponentialSmooth
open private le_of_mem_stageDomain exists_mem_stageDomain from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.Truncation

universe u
variable {H : ObservedHistory.{u}}

section Truncate

variable {first last k : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v₁ v₂ : ℝ}

theorem IsHistoryLGeodesicOn.truncate (hfk : first ≤ k) (hkl : k ≤ last) (hv₁ : 0 < v₁)
    (h12 : v₁ ≤ v₂) (hk : T - v₁ ^ 2 ∈ H.stageDomain k)
    {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    (hgeo : H.IsHistoryLGeodesicOn hle T v₂ α) :
    H.IsHistoryLGeodesicOn hkl T v₁
      (fun j : H.StageInterval k last => α ⟨j.val, hfk.trans j.property.1, j.property.2⟩) := by
  obtain ⟨hlower, hcross, hwin, hcont⟩ := hgeo
  refine ⟨hk, fun i hf hl => hcross i (hfk.trans hf) hl, fun s hs => ?_, ?_⟩
  · obtain ⟨lo, hi, hlo, hhi, W, hsW, -, γ, hγ, heq⟩ := hwin s ⟨hs.1, hs.2.trans_le h12⟩
    set b' := min W.b v₁ with hb'
    have hab : W.a < b' := lt_min (hsW.1.trans hsW.2) (hsW.1.trans hs.2)
    have hb'0 : 0 ≤ b' := W.nonneg.trans hab.le
    have hb'b : b' ≤ W.b := min_le_left _ _
    have hlowb : T - W.b ^ 2 ≤ T - b' ^ 2 := sub_le_sub_left (pow_le_pow_left₀ hb'0 hb'b 2) T
    have hbv : T - v₁ ^ 2 ≤ T - b' ^ 2 :=
      sub_le_sub_left (pow_le_pow_left₀ hb'0 (min_le_right _ _) 2) T
    have hba : T - b' ^ 2 ≤ T - W.a ^ 2 :=
      sub_le_sub_left (pow_le_pow_left₀ W.nonneg hab.le 2) T
    have h0 : 0 ≤ T - b' ^ 2 :=
      (H.time_nonneg k).trans ((H.time_le_of_mem_stageDomain hk).trans hbv)
    have hH : T - b' ^ 2 ≤ H.horizon := hba.trans
      ((H.le_stageEndTime_of_mem_stageDomain W.upper).trans (H.stageEndTime_le_horizon _))
    obtain ⟨lo', hlo'⟩ := exists_mem_stageDomain (H := H) h0 hH
    have h1 : lo ≤ lo' := le_of_mem_stageDomain W.lower hlo' hlowb
    have h2 : k ≤ lo' := le_of_mem_stageDomain hk hlo' hbv
    have h3 : lo' ≤ hi := le_of_mem_stageDomain hlo' W.upper hba
    refine ⟨lo', hi, h2, hhi, W.restrict h1 le_rfl h3 le_rfl hab hb'b W.upper hlo',
      show W.a < s ∧ s < b' from ⟨hsW.1, lt_min hsW.2 hs.2⟩, min_le_right _ _, γ,
      fun r (hr : r ∈ Ioo W.a b') => hγ r ⟨hr.1, hr.2.trans_le hb'b⟩, fun j r hr => ?_⟩
    exact heq ⟨j.val, h1.trans j.property.1, j.property.2⟩
      ⟨hr.1, hr.2.trans (regularizedStageEnd_le_of_le hb'0 hb'b j.val)⟩
  · rcases eq_or_lt_of_le h12 with h | h
    · subst h
      obtain rfl : k = first := le_antisymm (le_of_mem_stageDomain hk hlower le_rfl)
        (le_of_mem_stageDomain hlower hk le_rfl)
      exact hcont
    · obtain ⟨lo, hi, hlo, hhi, W, hvW, -, γ, hγ, heq⟩ := hwin v₁ ⟨hv₁, h⟩
      have hkI : T - v₁ ^ 2 ∈ Icc (H.time k) (H.stageEndTime k) :=
        ⟨H.time_le_of_mem_stageDomain hk, H.le_stageEndTime_of_mem_stageDomain hk⟩
      have hkW := LWindow.mem_range_of_mem_Icc W hvW hkI
      have hlt : T - v₁ ^ 2 < H.stageEndTime k := by
        cases k using Fin.lastCases with
        | last =>
          rw [stageEndTime_last]
          have h1 := (H.le_stageEndTime_of_mem_stageDomain W.upper).trans
            (H.stageEndTime_le_horizon hi)
          have h2 : W.a ^ 2 < v₁ ^ 2 := pow_lt_pow_left₀ hvW.1 W.nonneg two_ne_zero
          linarith
        | cast i =>
          simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at hk
          rw [stageEndTime_castSucc]
          exact hk.2
      have hc : ContinuousAt (fun r : ℝ => T - r ^ 2) v₁ := by fun_prop
      have hev : ∀ᶠ r in 𝓝[<] v₁, r ∈ Ioc W.a v₁ ∧ T - r ^ 2 ≤ H.stageEndTime k := by
        filter_upwards [Ioo_mem_nhdsLT hvW.1, nhdsWithin_le_nhds
          (hc.eventually_lt continuousAt_const hlt), self_mem_nhdsWithin] with r h1 h2 h3
        exact ⟨⟨h1.1, h1.2.le⟩, h2.le⟩
      have hrep : ∀ r, r ∈ Ioc W.a v₁ → T - r ^ 2 ≤ H.stageEndTime k →
          α ⟨k, hfk.trans le_rfl, hkl⟩ r = W.f ⟨k, hkW⟩ (γ r) := by
        intro r hr hre
        have hr2 : r ^ 2 ≤ v₁ ^ 2 := pow_le_pow_left₀ (W.nonneg.trans hr.1.le) hr.2 2
        have hpiece := mem_regularizedStage_Icc W.nonneg ⟨hr.1.le, hr.2.trans hvW.2.le⟩
          (show T - r ^ 2 ∈ Icc (H.time k) (H.stageEndTime k) from ⟨by linarith [hkI.1], hre⟩)
        exact (heq ⟨k, hkW⟩ hpiece).symm
      have hg : ContinuousAt (fun r => W.f ⟨k, hkW⟩ (γ r)) v₁ :=
        (W.localDiffeomorph _).contMDiff.continuous.continuousAt.comp (hγ v₁ hvW).2.1.continuousAt
      exact hg.continuousWithinAt.congr_of_eventuallyEq (hev.mono fun r hr => hrep r hr.1 hr.2)
        (hrep v₁ ⟨hvW.1, le_rfl⟩ hkI.2)

variable {p : (H.stage last).Carrier}

theorem mem_historyLExpDomain_of_le (hfk : first ≤ k) (hkl : k ≤ last) (hv₁ : 0 < v₁)
    (h12 : v₁ ≤ v₂) (hk : T - v₁ ^ 2 ∈ H.stageDomain k) {Z : TangentSpace ThreeModel p}
    (hZ : Z ∈ H.historyLExpDomain hle T v₂ p) : Z ∈ H.historyLExpDomain hkl T v₁ p := by
  obtain ⟨α, hα, hinit⟩ := hZ
  exact ⟨_, hα.truncate hfk hkl hv₁ h12 hk, hinit.truncate hv₁ hfk hk⟩

theorem historyLExp_eq_historyLCurve_of_mem_historyLExpDomain (hfk : first ≤ k) (hkl : k ≤ last)
    (hv₁ : 0 < v₁) (h12 : v₁ ≤ v₂) (hk : T - v₁ ^ 2 ∈ H.stageDomain k)
    (Z : H.historyLExpDomain hle T v₂ p) :
    H.historyLExp hkl T v₁ p ⟨Z.1, mem_historyLExpDomain_of_le hfk hkl hv₁ h12 hk Z.2⟩ =
      H.historyLCurve hle T v₂ p Z ⟨k, hfk, hkl⟩ v₁ :=
  historyLExp_eq hv₁ _ ((isHistoryLGeodesicOn_historyLCurve Z).truncate hfk hkl hv₁ h12 hk)
    ((hasHistoryLInitialVector_historyLCurve Z).truncate hv₁ hfk hk)

end Truncate

section BaseBound

variable {first last : Fin (H.eventCount + 1)} {T v : ℝ} {p : (H.stage last).Carrier}
  {α₀ : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_hasPrefixFamily_base_lt {Z₀ : ThreeSpace} {m : ℝ} (hv : 0 < v) (hm : 0 < m)
    (hlower : T - v ^ 2 ∈ H.stageDomain first) (hZ₀ : H.HasHistoryLInitialVector T α₀ p Z₀) :
    ∃ c₁, 0 < c₁ ∧ c₁ < m ∧ HasPrefixFamily H T v p α₀ Z₀ c₁ := by
  classical
  obtain ⟨lo₀, hlo₀, W₀, x, Zx₀, ha₀, hx, hZx₀, hdom, heq₀⟩ := hZ₀
  have hb₀ : 0 < W₀.b := ha₀ ▸ W₀.lt
  obtain ⟨α, J, hJo, hJc, h0J, hbJ, hcurve⟩ := hdom
  obtain ⟨V', hV', hZV', K, hK, hKc, h0K, hbK, fam, hfam, hfamc⟩ :=
    lRegularizedFamily_extend W₀.S W₀.solution T hJo hJc h0J hbJ hcurve
  have hIcc : Icc 0 W₀.b ⊆ K := hKc.Icc_subset h0K hbK
  obtain ⟨c₁, hc₁, hne⟩ := exists_mem_Ioo_not_mem_range (H := H) (T := T)
    (lt_min (lt_min hb₀ hv) hm) le_rfl
  have hc₁b : c₁ < W₀.b := hc₁.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hc₁v : c₁ < v := hc₁.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hc₁m : c₁ < m := hc₁.2.trans_le (min_le_right _ _)
  have hTup : T - 0 ^ 2 ∈ H.stageDomain last := by
    have h := W₀.upper
    rwa [ha₀] at h
  have hT0 : T ∈ H.stageDomain last := by simpa using hTup
  have hc₁0 : 0 ≤ T - c₁ ^ 2 := by
    have := H.time_le_of_mem_stageDomain hlower
    have h2 : c₁ ^ 2 < v ^ 2 := pow_lt_pow_left₀ hc₁v hc₁.1.le two_ne_zero
    linarith [H.time_nonneg first]
  have hc₁h : T - c₁ ^ 2 < H.horizon := by
    have := (H.le_stageEndTime_of_mem_stageDomain hT0).trans (H.stageEndTime_le_horizon last)
    have : 0 < c₁ ^ 2 := pow_pos hc₁.1 2
    linarith
  obtain ⟨k₀, η, hη, hηc, hηk⟩ := exists_stage_nhds hc₁.1 hc₁0 hc₁h hne
  have hkc := hηk c₁ ⟨by linarith, by linarith⟩
  have hc₁a : W₀.a < c₁ := by rw [ha₀]; exact hc₁.1
  have hk₀ : lo₀ ≤ k₀ ∧ k₀ ≤ last :=
    LWindow.mem_range_of_mem_Icc W₀ ⟨hc₁a, hc₁b⟩ ⟨hkc.1.le, hkc.2.le⟩
  set η₀ := min η (W₀.b - c₁) with hη₀def
  have hη₀ : 0 < η₀ := lt_min hη (by linarith)
  have hη₀η : η₀ ≤ η := min_le_left _ _
  have hη₀b : η₀ ≤ W₀.b - c₁ := min_le_right _ _
  have hsub : Ioo (c₁ - η₀) (c₁ + η₀) ⊆ Ioo W₀.a W₀.b := fun s hs => by
    rw [ha₀]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsubK : Ioo (c₁ - η₀) (c₁ + η₀) ⊆ K := fun s hs => hIcc ⟨by linarith [hs.1], by
    linarith [hs.2]⟩
  let e := (W₀.localDiffeomorph ⟨last, W₀.le, le_rfl⟩).mfderivToContinuousLinearEquiv
    (by simp) x
  let L : ThreeSpace →L[ℝ] ThreeSpace :=
    (e.symm : TangentSpace ThreeModel (W₀.f ⟨last, W₀.le, le_rfl⟩ x) →L[ℝ]
      TangentSpace ThreeModel x)
  have hLe : ∀ Z : ThreeSpace, mfderiv ThreeModel ThreeModel (W₀.f ⟨last, W₀.le, le_rfl⟩) x
      (L Z) = Z := fun Z => e.apply_symm_apply Z
  have hLZ₀ : L Z₀ = Zx₀ := by
    have h : e Zx₀ = Z₀ := hZx₀
    have h2 : e.symm (e Zx₀) = Zx₀ := e.symm_apply_apply Zx₀
    rw [h] at h2
    exact h2
  let V : Set ThreeSpace := L ⁻¹' V'
  have hV : IsOpen V := hV'.preimage L.continuous
  have hZ₀V : Z₀ ∈ V := by
    change L Z₀ ∈ V'
    rw [hLZ₀]
    exact hZV'
  let β₀ : ThreeSpace × ℝ → W₀.X := fun q => fam (L q.1, q.2)
  have hβ₀ : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β₀ (V ×ˢ K) := by
    have hmap : ContMDiff (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : ThreeSpace × ℝ => (L q.1, q.2)) :=
      (L.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    exact hfam.comp hmap.contMDiffOn fun q hq => ⟨hq.1, hq.2⟩
  have hcurveZ : ∀ Z ∈ V, IsLRegularizedCurveOn W₀.S T (fun s => β₀ (Z, s)) K x (L Z) :=
    fun Z hZ => hfamc (L Z) hZ
  let A : ThreeSpace → (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier :=
    fun Z j r => if h : r ≤ c₁ ∧ lo₀ ≤ j.val then W₀.f ⟨j.val, h.2, j.property.2⟩ (β₀ (Z, r))
      else α₀ j r
  have hA : ∀ Z (j : H.StageInterval first last) r (h : r ≤ c₁ ∧ lo₀ ≤ j.val),
      A Z j r = W₀.f ⟨j.val, h.2, j.property.2⟩ (β₀ (Z, r)) := fun Z j r h => dif_pos h
  have hup0 : T - (0 : ℝ) ^ 2 ∈ H.stageDomain last := hTup
  have hdown : T - c₁ ^ 2 ∈ H.stageDomain k₀ := H.mem_stageDomain_of_mem_Ioo hkc
  have hTlast : H.time last ≤ T := H.time_le_of_mem_stageDomain hT0
  refine ⟨c₁, hc₁.1, hc₁m, V, hV, hZ₀V, A, fun Z hZ => ?_, lo₀, last, hlo₀, le_rfl, W₀,
    lRegularizedCurve W₀.S T x Zx₀, ⟨hc₁a, hc₁b⟩, ?_, ?_, k₀, hk₀, η₀, hη₀, hsub,
    fun r hr => hηk r ⟨by linarith [hr.1], by linarith [hr.2]⟩, β₀,
    hβ₀.mono (prod_mono subset_rfl hsubK), fun Z hZ s hs => (hcurveZ Z hZ).2.2 s (hsubK hs),
    fun s hs => ?_, fun Z hZ r hr => hA Z _ r ⟨hr.2, hk₀.1⟩⟩
  · let W'' := W₀.restrict hk₀.1 le_rfl hk₀.2 (by rw [ha₀]) hc₁.1 hc₁b.le hup0 hdown
    refine ⟨fun i hf hl hw => ?_, fun s hs => ?_, k₀, hlo₀.trans hk₀.1, W'', x, L Z, rfl,
      le_rfl, hx, hLe Z, ⟨fun s => β₀ (Z, s), K, hK, hKc, h0K, hIcc ⟨hc₁.1.le, hc₁b.le⟩,
        hcurveZ Z hZ⟩, fun j r hr => ?_⟩
    · have hsq : T - Real.sqrt (T - H.time i.succ) ^ 2 = H.time i.succ := by
        rw [Real.sq_sqrt (by linarith [H.time_strictMono.monotone hl])]
        ring
      have hold : lo₀ ≤ i.castSucc := lo_le_of_lt_b W₀ (Real.sqrt_nonneg _) (hw.trans hc₁b)
        (by rw [hsq, stageEndTime_castSucc])
      have hnew : lo₀ ≤ i.succ := hold.trans i.castSucc_lt_succ.le
      rw [hA Z _ _ ⟨hw.le, hold⟩, hA Z _ _ ⟨hw.le, hnew⟩]
      exact W₀.crossing i hold hl _
    · refine ⟨k₀, last, hlo₀.trans hk₀.1, le_rfl, W'', hs, le_rfl, fun r => β₀ (Z, r),
        fun r hr => (hcurveZ Z hZ).2.2 r (hIcc ⟨hr.1.le, hr.2.le.trans hc₁b.le⟩),
        fun j r hr => ?_⟩
      have hrI : r ∈ Icc 0 c₁ := LWindow.piece_subset _ j hr
      change W₀.f ⟨j.val, hk₀.1.trans j.property.1, j.property.2⟩ (β₀ (Z, r)) = _
      rw [hA Z _ r ⟨hrI.2, hk₀.1.trans j.property.1⟩]
    · have hrI : r ∈ Icc 0 c₁ := LWindow.piece_subset W'' j hr
      have hcur := lRegularizedCurve_eqOn W₀.S W₀.solution T hK hKc h0K (hcurveZ Z hZ)
        (hIcc ⟨hrI.1, hrI.2.trans hc₁b.le⟩)
      change W₀.f ⟨j.val, hk₀.1.trans j.property.1, j.property.2⟩
        (lRegularizedCurve W₀.S T x (L Z) r) = _
      rw [hcur, hA Z _ r ⟨hrI.2, hk₀.1.trans j.property.1⟩]
  · intro s hs
    rw [ha₀] at hs
    have hsJ : s ∈ J := hJc.Icc_subset h0J hbJ (Ioo_subset_Icc_self hs)
    exact isLRegularizedGeodesicOn_lRegularizedCurve W₀.S W₀.solution T x Zx₀ s
      ⟨α, J, hJo, hJc, h0J, hsJ, hcurve⟩
  · intro j r hr hrv ht
    have hr' : r ∈ Icc (H.regularizedStageStart T 0 j.val)
        (H.regularizedStageEnd T W₀.b j.val) := by
      rw [ha₀] at hr
      exact mem_regularizedStage_Icc le_rfl ⟨hr.1.le, hr.2.le⟩ ht
    exact heq₀ j hr'
  · change fam (L Z₀, s) = lRegularizedCurve W₀.S T x Zx₀ s
    rw [hLZ₀]
    exact (lRegularizedCurve_eqOn W₀.S W₀.solution T hK hKc h0K (hfamc Zx₀ hZV')
      (hsubK hs)).symm

end BaseBound

section Target

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
  {p : (H.stage last).Carrier}
  {α₀ : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}

private theorem hasPrefixFamily_of_window (hv : 0 < v) {Z₀ : ThreeSpace}
    (hα₀ : H.IsHistoryLGeodesicOn hle T v α₀) (hZ₀ : H.HasHistoryLInitialVector T α₀ p Z₀)
    {c : ℝ} (hc : 0 < c) (hcv : c ≤ v) (hne : T - c ^ 2 ∉ range H.time)
    {lo hi : Fin (H.eventCount + 1)} (hlo : first ≤ lo) (hhi : hi ≤ last)
    (W : H.LWindow lo hi T) (hcW : c ∈ Ioo W.a W.b) (γ : ℝ → W.X)
    (hγ : IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b))
    (href : ∀ j : H.StageInterval lo hi, ∀ r ∈ Ioo W.a W.b, r ≤ v →
      T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) →
      W.f j (γ r) = α₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r) :
    HasPrefixFamily H T v p α₀ Z₀ c := by
  obtain ⟨c₁, hc₁, hc₁c, hP₁⟩ := exists_hasPrefixFamily_base_lt hv hc hα₀.1 hZ₀
  set S : Set ℝ := {c' | c' ≤ c ∧ HasPrefixFamily H T v p α₀ Z₀ c'} with hSdef
  have hSne : S.Nonempty := ⟨c₁, hc₁c.le, hP₁⟩
  have hSbdd : BddAbove S := ⟨c, fun c' hc' => hc'.1⟩
  have hsc : sSup S ≤ c := csSup_le hSne fun c' hc' => hc'.1
  have hc₁s : c₁ ≤ sSup S := le_csSup hSbdd ⟨hc₁c.le, hP₁⟩
  have hsEq : sSup S = c := by
    by_contra hne'
    have hlt : sSup S < c := lt_of_le_of_ne hsc hne'
    have hs0 : 0 < sSup S := hc₁.trans_le hc₁s
    obtain ⟨lo', hi', hlo', hhi', W', hsW', hbv, γ', hγ', heq'⟩ :=
      hα₀.2.2.1 (sSup S) ⟨hs0, hlt.trans_le hcv⟩
    obtain ⟨c', hc', hne''⟩ := exists_mem_Ioo_not_mem_range (H := H) (T := T)
      (lt_min hsW'.2 hlt) hs0.le
    have hc'b : c' < W'.b := hc'.2.trans_le (min_le_left _ _)
    have hc'c : c' ≤ c := (hc'.2.trans_le (min_le_right _ _)).le
    obtain ⟨c'', hc''S, hac''⟩ := exists_lt_of_lt_csSup hSne hsW'.1
    have hP := hasPrefixFamily_step hc''S.2 hlo' hhi' W' γ' hγ'
      (fun j r hr _ ht => heq' j (mem_regularizedStage_Icc W'.nonneg ⟨hr.1.le, hr.2.le⟩ ht))
      hac'' ((le_csSup hSbdd hc''S).trans_lt hc'.1) hc'b (hc'c.trans hcv) hne''
    exact absurd (le_csSup hSbdd ⟨hc'c, hP⟩) (not_le.2 hc'.1)
  have haS : W.a < sSup S := by rw [hsEq]; exact hcW.1
  obtain ⟨c'', hc''S, hac''⟩ := exists_lt_of_lt_csSup hSne haS
  rcases eq_or_lt_of_le hc''S.1 with h | h
  · have hP := hc''S.2
    rwa [h] at hP
  · exact hasPrefixFamily_step hc''S.2 hlo hhi W γ hγ href hac'' h hcW.2 hcv hne

private theorem isHistoryLGeodesicOn_of_prefix
    {A : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier} {Z : ThreeSpace}
    {c : ℝ} (hc : 0 < c) {k : Fin (H.eventCount + 1)} (hfk : first ≤ k) (hkl : k ≤ last)
    (hk : T - c ^ 2 ∈ Ioo (H.time k) (H.stageEndTime k))
    (hP : IsHistoryLGeodesicPrefix H T p A Z c)
    (hcont : ContinuousWithinAt (A ⟨k, hfk, hkl⟩) (Iio c) c) :
    H.IsHistoryLGeodesicOn hkl T c
        (fun j : H.StageInterval k last => A ⟨j.val, hfk.trans j.property.1, j.property.2⟩) ∧
      H.HasHistoryLInitialVector T
        (fun j : H.StageInterval k last => A ⟨j.val, hfk.trans j.property.1, j.property.2⟩) p
        Z := by
  obtain ⟨hcross, hwin, lo₀, hlo₀, W₀, x, Zx, ha₀, hb₀, hx, hZx, hdom, hbase⟩ := hP
  have hkd : T - c ^ 2 ∈ H.stageDomain k := H.mem_stageDomain_of_mem_Ioo hk
  have key : ∀ {lo hi : Fin (H.eventCount + 1)} (W : H.LWindow lo hi T), W.b ≤ c → k ≤ lo :=
    fun W hb => le_of_mem_stageDomain hkd W.lower
      (sub_le_sub_left (pow_le_pow_left₀ (W.nonneg.trans W.lt.le) hb 2) T)
  refine ⟨⟨hkd, fun i hf hl => hcross i (hfk.trans hf) hl ?_, fun s hs => ?_, hcont⟩,
    lo₀, key W₀ hb₀, W₀, x, Zx, ha₀, hx, hZx, hdom, fun j r hr => hbase j hr⟩
  · have h1 : H.stageEndTime k ≤ H.time i.succ := by
      rw [← stageEndTime_castSucc]
      exact H.stageEndTime_mono hf
    exact (Real.sqrt_lt' hc).2 (by linarith [hk.2])
  · obtain ⟨lo, hi, hlo, hhi, W, hsW, hb, γ, hγ, heq⟩ := hwin s hs
    exact ⟨lo, hi, key W hb, hhi, W, hsW, hb, γ, hγ, fun j r hr => heq j hr⟩

end Target

section StepExposed

variable {first last : Fin (H.eventCount + 1)} {T v : ℝ} {p : (H.stage last).Carrier}
  {α₀ : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_window_family_step {Z₀ : ThreeSpace} {c c' : ℝ}
    (hP : HasPrefixFamily H T v p α₀ Z₀ c) {lo' hi' : Fin (H.eventCount + 1)} (hlo' : first ≤ lo')
    (hhi' : hi' ≤ last) (W' : H.LWindow lo' hi' T) (γ' : ℝ → W'.X)
    (hγ' : IsLRegularizedGeodesicOn W'.S T γ' (Ioo W'.a W'.b))
    (href' : ∀ j : H.StageInterval lo' hi', ∀ r ∈ Ioo W'.a W'.b, r ≤ v →
      T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) →
      W'.f j (γ' r) = α₀ ⟨j.val, hlo'.trans j.property.1, j.property.2.trans hhi'⟩ r)
    (hc : W'.a < c) (hcc' : c < c') (hc'b : c' < W'.b) (hc'v : c' ≤ v)
    (hne : T - c' ^ 2 ∉ range H.time) :
    ∃ V₂ : Set ThreeSpace, IsOpen V₂ ∧ Z₀ ∈ V₂ ∧ ∃ K : Set ℝ, IsOpen K ∧ IsPreconnected K ∧
      c ∈ K ∧ c' ∈ K ∧ K ⊆ Ioo W'.a W'.b ∧ ∃ β₂ : ThreeSpace × ℝ → W'.X,
        ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β₂ (V₂ ×ˢ K) ∧
        (∀ Z ∈ V₂, IsLRegularizedGeodesicOn W'.S T (fun s => β₂ (Z, s)) K) ∧
        ∃ A' : ThreeSpace → (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
          (∀ Z ∈ V₂, IsHistoryLGeodesicPrefix H T p (A' Z) Z c') ∧
          ∀ Z ∈ V₂, ∀ (j : H.StageInterval first last) (h : lo' ≤ j.val ∧ j.val ≤ hi') (r : ℝ),
            c < r → A' Z j r = W'.f ⟨j.val, h⟩ (β₂ (Z, r)) := by
  classical
  obtain ⟨V, hV, hZ₀V, A, hA, lo, hi, hlo, hhi, W, γ, hcW, hγ, href, k, hk, η, hη, hηW, hηk, β,
    hβ, hgeo, hβγ, hAβ⟩ := hP
  have hcpos : 0 < c := W'.nonneg.trans_lt hc
  have hkc := hηk c ⟨by linarith, by linarith⟩
  have hk' : lo' ≤ k ∧ k ≤ hi' :=
    LWindow.mem_range_of_mem_Icc W' ⟨hc, hcc'.trans hc'b⟩ ⟨hkc.1.le, hkc.2.le⟩
  set η₀ := min η (min (c - W'.a) (min (W'.b - c) (v - c))) with hη₀
  have hη₀pos : 0 < η₀ := lt_min hη (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hη₀le : η₀ ≤ η := min_le_left _ _
  have hη₀a : η₀ ≤ c - W'.a := (min_le_right _ _).trans (min_le_left _ _)
  have hη₀b : η₀ ≤ W'.b - c :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη₀v : η₀ ≤ v - c :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsubη : Ioo (c - η₀) (c + η₀) ⊆ Ioo (c - η) (c + η) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hagree : ∀ s ∈ Ioo (c - η₀) (c + η₀),
      W.f ⟨k, hk⟩ (β (Z₀, s)) = W'.f ⟨k, hk'⟩ (γ' s) := by
    intro s hs
    have hs' := hsubη hs
    have hks := hηk s hs'
    rw [hβγ s hs', href ⟨k, hk⟩ s (hηW hs') (by linarith [hs.2]) ⟨hks.1.le, hks.2.le⟩,
      href' ⟨k, hk'⟩ s ⟨by linarith [hs.1], by linarith [hs.2]⟩ (by linarith [hs.2])
        ⟨hks.1.le, hks.2.le⟩]
  obtain ⟨V₁, hV₁, hZ₀V₁, hV₁V, η₁, hη₁, hη₁le, hη₁W', β₁, hβ₁, hgeo₁, hβ₁γ', hβ₁f⟩ :=
    exists_transfer_family W W' hk hk' hη₀pos (fun s hs => hηW (hsubη hs))
      ⟨hc, hcc'.trans hc'b⟩ (fun r hr => hηk r (hsubη hr)) hV hZ₀V
      (hβ.mono (prod_mono subset_rfl hsubη)) (fun Z hZ s hs => hgeo Z hZ s (hsubη hs)) hagree
  have hcK₀ : c ∈ Ioo (c - η₁) (c + η₁) := ⟨by linarith, by linarith⟩
  have hcb : uIcc c c' ⊆ Ioo W'.a W'.b := by
    rw [uIcc_of_le hcc'.le]
    exact fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨V₂, hV₂, hZ₀V₂, hV₂V₁, K, hK, hKc, hK₀K, hc'K, hKJ, β₂, hβ₂, hgeo₂, hβ₂γ', hβ₂β₁⟩ :=
    exists_lRegularizedGeodesicFamily_along W'.S W'.solution T isOpen_Ioo hγ' hV₁ hZ₀V₁
      isOpen_Ioo isPreconnected_Ioo hη₁W' hβ₁ hgeo₁ hβ₁γ' hcK₀ hcb
  have hc'pos : 0 < c' := hcpos.trans hcc'
  have hc'0 : 0 ≤ T - c' ^ 2 := by
    have h1 := H.time_le_of_mem_stageDomain W'.lower
    have h2 : c' ^ 2 < W'.b ^ 2 := pow_lt_pow_left₀ hc'b hc'pos.le two_ne_zero
    linarith [H.time_nonneg lo']
  have hc'h : T - c' ^ 2 < H.horizon := by
    have h1 := (H.le_stageEndTime_of_mem_stageDomain W'.upper).trans
      (H.stageEndTime_le_horizon hi')
    have h2 : W'.a ^ 2 < c' ^ 2 := pow_lt_pow_left₀ (hc.trans hcc') W'.nonneg two_ne_zero
    linarith
  obtain ⟨k', η₂, hη₂, -, hη₂k'⟩ := exists_stage_nhds hc'pos hc'0 hc'h hne
  have hkc' := hη₂k' c' ⟨by linarith, by linarith⟩
  have hk'' : lo' ≤ k' ∧ k' ≤ hi' :=
    LWindow.mem_range_of_mem_Icc W' ⟨hc.trans hcc', hc'b⟩ ⟨hkc'.1.le, hkc'.2.le⟩
  have hk'k : k' ≤ k := by
    by_contra h
    have h1 := stageEndTime_le_time_of_lt (not_le.1 h)
    have h2 : c ^ 2 < c' ^ 2 := pow_lt_pow_left₀ hcc' hcpos.le two_ne_zero
    linarith [hkc.2, hkc'.1]
  let A' : ThreeSpace → (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier :=
    fun Z j r => if r ≤ c then A Z j r else
      if h : lo' ≤ j.val ∧ j.val ≤ hi' then W'.f ⟨j.val, h⟩ (β₂ (Z, r)) else A Z j r
  have hA'le : ∀ Z j r, r ≤ c → A' Z j r = A Z j r := fun Z j r h => if_pos h
  have hA'gt : ∀ Z (j : H.StageInterval first last) r (h : lo' ≤ j.val ∧ j.val ≤ hi'), c < r →
      A' Z j r = W'.f ⟨j.val, h⟩ (β₂ (Z, r)) := fun Z j r h hr => by
    change (if r ≤ c then A Z j r else
      if h : lo' ≤ j.val ∧ j.val ≤ hi' then W'.f ⟨j.val, h⟩ (β₂ (Z, r)) else A Z j r) = _
    rw [if_neg (not_le.2 hr), dif_pos h]
  have hcore : ∀ Z ∈ V₂, ∀ r ∈ Ioc (c - η₁) c,
      A Z ⟨k, hlo.trans hk.1, hk.2.trans hhi⟩ r = W'.f ⟨k, hk'⟩ (β₂ (Z, r)) := by
    intro Z hZ r hr
    have hr₁ : r ∈ Ioo (c - η₁) (c + η₁) := ⟨hr.1, by linarith [hr.2]⟩
    have hrη : r ∈ Ioc (c - η) c := ⟨by linarith [hr.1], hr.2⟩
    rw [hAβ Z (hV₁V (hV₂V₁ hZ)) r hrη, hβ₂β₁ Z hZ r hr₁, hβ₁f Z (hV₂V₁ hZ) r hr₁]
  refine ⟨V₂, hV₂, hZ₀V₂, K, hK, hKc, hK₀K hcK₀, hc'K, hKJ, β₂, hβ₂, hgeo₂, A',
    fun Z hZ => ?_, fun Z _ j h r hr => hA'gt Z j r h hr⟩
  have hZV : Z ∈ V := hV₁V (hV₂V₁ hZ)
  refine isHistoryLGeodesicPrefix_congr hcc'.le (hA Z hZV) (fun i hf hl h1 h2 => ?_)
    (fun s hs => ?_) (fun j r hr => hA'le Z j r hr)
  · rcases eq_or_lt_of_le h1 with h | h
    · exfalso
      have hwpos : 0 < Real.sqrt (T - H.time i.succ) := h ▸ hcpos
      have hT : T - c ^ 2 = H.time i.succ := by
        rw [h, Real.sq_sqrt (Real.sqrt_pos.1 hwpos).le]
        ring
      have hik := eq_of_mem_Ioo_of_mem_Icc hkc
        (show T - c ^ 2 ∈ Icc (H.time i.succ) (H.stageEndTime i.succ) from
          by rw [hT]; exact ⟨le_rfl, H.time_le_stageEndTime _⟩)
      rw [hT, hik] at hkc
      exact lt_irrefl _ hkc.1
    · have hwpos : 0 < Real.sqrt (T - H.time i.succ) := hcpos.trans h
      have hT : T - Real.sqrt (T - H.time i.succ) ^ 2 = H.time i.succ := by
        rw [Real.sq_sqrt (Real.sqrt_pos.1 hwpos).le]
        ring
      have hwW : Real.sqrt (T - H.time i.succ) ∈ Ioo W'.a W'.b := ⟨hc.trans h, h2.trans hc'b⟩
      have hold := LWindow.mem_range_of_mem_Icc W' hwW (j := i.castSucc) (by
        rw [hT, stageEndTime_castSucc]
        exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩)
      have hnew := LWindow.mem_range_of_mem_Icc W' hwW (j := i.succ) (by
        rw [hT]
        exact ⟨le_rfl, H.time_le_stageEndTime _⟩)
      rw [hA'gt Z _ _ hold h, hA'gt Z _ _ hnew h]
      exact W'.crossing i hold.1 hnew.2 _
  · have hlow : c - η₁ / 2 ∈ Ioo (c - η₁) (c + η₁) := ⟨by linarith, by linarith⟩
    have hlowη : c - η₁ / 2 ∈ Ioo (c - η) (c + η) :=
      ⟨by linarith [hη₁le, hη₀le], by linarith⟩
    have hup : T - (c - η₁ / 2) ^ 2 ∈ H.stageDomain k :=
      H.mem_stageDomain_of_mem_Ioo (hηk _ hlowη)
    have hdown : T - c' ^ 2 ∈ H.stageDomain k' := H.mem_stageDomain_of_mem_Ioo hkc'
    refine ⟨k', k, hlo'.trans hk''.1, hk'.2.trans hhi',
      W'.restrict hk''.1 hk'.2 hk'k (hη₁W' hlow).1.le (show c - η₁ / 2 < c' by linarith)
        hc'b.le hup hdown, ⟨show c - η₁ / 2 < s by linarith [hs.1], hs.2⟩, le_rfl,
      fun r => β₂ (Z, r),
      fun r hr => hgeo₂ Z hZ r (hKc.Icc_subset (hK₀K hlow) hc'K (Ioo_subset_Icc_self hr)),
      fun j r hr => ?_⟩
    have hrI : r ∈ Icc (c - η₁ / 2) c' := LWindow.piece_subset _ j hr
    have hrt : T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) :=
      LWindow.mem_Icc_of_mem_piece _ j hr
    have hj' : lo' ≤ j.val ∧ j.val ≤ hi' :=
      ⟨hk''.1.trans j.property.1, j.property.2.trans hk'.2⟩
    change W'.f ⟨j.val, hj'⟩ (β₂ (Z, r)) = _
    rcases le_or_gt r c with hrc | hrc
    · have hrη : r ∈ Ioo (c - η) (c + η) := ⟨by linarith [hrI.1, hη₁le, hη₀le], by linarith⟩
      obtain ⟨jv, hj1, hj2⟩ := j
      have hjk : jv = k := eq_of_mem_Ioo_of_mem_Icc (hηk r hrη) hrt
      subst hjk
      rw [hA'le Z _ r hrc]
      exact (hcore Z hZ r ⟨by linarith [hrI.1], hrc⟩).symm
    · rw [hA'gt Z _ r hj' hrc]

end StepExposed

section Export

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
  {p : (H.stage last).Carrier}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiffOn_window_family_historyLCurve (hv : 0 < v)
    {Z₀ : TangentSpace ThreeModel p} (hZ₀ : Z₀ ∈ H.historyLExpOpenDomain hle T v p)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo 0 v) :
    ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧ V ⊆ H.historyLExpOpenDomain hle T v p ∧
      ∃ hVdom : (∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p),
      ∃ (lo hi : Fin (H.eventCount + 1)) (hlo : first ≤ lo) (hhi : hi ≤ last)
        (W : H.LWindow lo hi T) (K : Set ℝ), IsOpen K ∧ s₀ ∈ K ∧ K ⊆ Ioo W.a W.b ∧
        ∃ β : ThreeSpace × ℝ → W.X,
          ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (V ×ˢ K) ∧
          (∀ Z ∈ V, IsLRegularizedGeodesicOn W.S T (fun r => β (Z, r)) K) ∧
          ∀ Z (hZ : Z ∈ V) (j : H.StageInterval lo hi),
            ∀ r ∈ K ∩ Ioo (H.regularizedStageStart T W.a j.val)
              (H.regularizedStageEnd T W.b j.val),
              H.historyLCurve hle T v p ⟨Z, hVdom Z hZ⟩
                ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r = W.f j (β (Z, r)) := by
  obtain ⟨V₃, hV₃, hZ₀V₃, hV₃sub, -⟩ := exists_nhds_contMDiffOn_historyLExp hv hZ₀
  obtain ⟨α₀, hα₀, hinit, -⟩ := hZ₀
  obtain ⟨lo, hi, hlo, hhi, W, hsW, hbv, γ, hγ, heq⟩ := hα₀.2.2.1 s₀ hs₀
  have href : ∀ j : H.StageInterval lo hi, ∀ r ∈ Ioo W.a W.b, r ≤ v →
      T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) →
      W.f j (γ r) = α₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r :=
    fun j r hr _ ht => heq j (mem_regularizedStage_Icc W.nonneg ⟨hr.1.le, hr.2.le⟩ ht)
  obtain ⟨c₁, hc₁, hne₁⟩ := exists_mem_Ioo_not_mem_range (H := H) (T := T) hsW.1 W.nonneg
  obtain ⟨c', hc', hne'⟩ := exists_mem_Ioo_not_mem_range (H := H) (T := T) hsW.2 hs₀.1.le
  have hc₁pos : 0 < c₁ := W.nonneg.trans_lt hc₁.1
  have hc'pos : 0 < c' := hs₀.1.trans hc'.1
  have hc'v : c' ≤ v := hc'.2.le.trans hbv
  have hP := hasPrefixFamily_of_window hv hα₀ hinit hc₁pos (hc₁.2.trans hs₀.2).le hne₁ hlo hhi W
    ⟨hc₁.1, hc₁.2.trans hsW.2⟩ γ hγ href
  obtain ⟨V₂, hV₂, hZ₀V₂, K, hK, hKc, hc₁K, hc'K, hKW, β, hβ, hgeo, A', hA', hrep⟩ :=
    exists_window_family_step hP hlo hhi W γ hγ href hc₁.1 (hc₁.2.trans hc'.1) hc'.2 hc'v hne'
  have hc'0 : 0 ≤ T - c' ^ 2 := by
    have h1 := H.time_le_of_mem_stageDomain W.lower
    have h2 : c' ^ 2 < W.b ^ 2 := pow_lt_pow_left₀ hc'.2 hc'pos.le two_ne_zero
    linarith [H.time_nonneg lo]
  have hc'h : T - c' ^ 2 < H.horizon := by
    have h1 := (H.le_stageEndTime_of_mem_stageDomain W.upper).trans
      (H.stageEndTime_le_horizon hi)
    have h2 : W.a ^ 2 < c' ^ 2 := pow_lt_pow_left₀ (hsW.1.trans hc'.1) W.nonneg two_ne_zero
    linarith
  obtain ⟨k', η₂, hη₂, -, hη₂k'⟩ := exists_stage_nhds hc'pos hc'0 hc'h hne'
  have hk'I := hη₂k' c' ⟨by linarith, by linarith⟩
  have hk'W : lo ≤ k' ∧ k' ≤ hi := LWindow.mem_range_of_mem_Icc W ⟨hsW.1.trans hc'.1, hc'.2⟩
    ⟨hk'I.1.le, hk'I.2.le⟩
  have hfk' : first ≤ k' := hlo.trans hk'W.1
  have hk'l : k' ≤ last := hk'W.2.trans hhi
  have hk'd : T - c' ^ 2 ∈ H.stageDomain k' := H.mem_stageDomain_of_mem_Ioo hk'I
  have hopen : IsOpen (V₂ ×ˢ K) := hV₂.prod hK
  have hcont : ∀ Z ∈ V₂, ContinuousWithinAt (A' Z ⟨k', hfk', hk'l⟩) (Iio c') c' := by
    intro Z hZ
    have hg : ContinuousAt (fun r => W.f ⟨k', hk'W⟩ (β (Z, r))) c' :=
      (W.localDiffeomorph _).contMDiff.continuous.continuousAt.comp
        (((hβ (Z, c') ⟨hZ, hc'K⟩).contMDiffAt (hopen.mem_nhds ⟨hZ, hc'K⟩)).comp c'
          (contMDiffAt_const.prodMk contMDiffAt_id)).continuousAt
    refine hg.continuousWithinAt.congr_of_eventuallyEq ?_
      (hrep Z hZ ⟨k', hfk', hk'l⟩ hk'W c' (hc₁.2.trans hc'.1))
    filter_upwards [Ioo_mem_nhdsLT (hc₁.2.trans hc'.1)] with r hr
    exact hrep Z hZ ⟨k', hfk', hk'l⟩ hk'W r hr.1
  have hdom : ∀ Z ∈ V₂ ∩ V₃, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p :=
    fun Z hZ => historyLExpOpenDomain_subset_historyLExpDomain (hV₃sub hZ.2)
  refine ⟨V₂ ∩ V₃, hV₂.inter hV₃, ⟨hZ₀V₂, hZ₀V₃⟩, fun Z hZ => hV₃sub hZ.2, hdom, lo, hi, hlo,
    hhi, W, K ∩ Ioo c₁ c', hK.inter isOpen_Ioo,
    ⟨hKc.Icc_subset hc₁K hc'K ⟨hc₁.2.le, hc'.1.le⟩, hc₁.2, hc'.1⟩, fun r hr => hKW hr.1, β,
    hβ.mono (prod_mono inter_subset_left inter_subset_left),
    fun Z hZ r hr => hgeo Z hZ.1 r hr.1, fun Z hZ j r hr => ?_⟩
  obtain ⟨hgeoA, hinitA⟩ := isHistoryLGeodesicOn_of_prefix hc'pos hfk' hk'l hk'I (hA' Z hZ.1)
    (hcont Z hZ.1)
  have hαZ := (isHistoryLGeodesicOn_historyLCurve (⟨Z, hdom Z hZ⟩ :
    H.historyLExpDomain hle T v p)).truncate hfk' hk'l hc'pos hc'v hk'd
  have hinitZ := (hasHistoryLInitialVector_historyLCurve (⟨Z, hdom Z hZ⟩ :
    H.historyLExpDomain hle T v p)).truncate hc'pos hfk' hk'd
  have ht : T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) :=
    W.mem_Icc_of_mem_piece j (Ioo_subset_Icc_self hr.2)
  have hr0 : 0 ≤ r := W.nonneg.trans (hKW hr.1.1).1.le
  have hrc' : r < c' := hr.1.2.2
  have hk'j : k' ≤ j.val := by
    by_contra h
    have h1 := stageEndTime_le_time_of_lt (not_le.1 h)
    have h2 : r ^ 2 < c' ^ 2 := pow_lt_pow_left₀ hrc' hr0 two_ne_zero
    linarith [hk'I.1, ht.2]
  have hpiece : r ∈ Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T c' j.val) :=
    mem_regularizedStage_Icc le_rfl ⟨hr0, hrc'.le⟩ ht
  have e := IsHistoryLGeodesicOn.eqOn_of_hasHistoryLInitialVector hc'pos hgeoA hαZ hinitA hinitZ
    ⟨j.val, hk'j, j.property.2.trans hhi⟩ hpiece
  exact e.symm.trans (hrep Z hZ.1 ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩
    j.property r hr.1.2.1)

end Export

section SeamExport

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
  {p : (H.stage last).Carrier}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiffOn_seam_window_family_historyLCurve (hv : 0 < v)
    {Z₀ : TangentSpace ThreeModel p} (hZ₀ : Z₀ ∈ H.historyLExpOpenDomain hle T v p)
    (i : Fin H.eventCount) (hlo : first ≤ i.castSucc) (hhi : i.succ ≤ last)
    (hw : Real.sqrt (T - H.time i.succ) ∈ Ioo 0 v) :
    ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧ V ⊆ H.historyLExpOpenDomain hle T v p ∧
      ∃ hVdom : (∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p),
      ∃ (W : H.LWindow i.castSucc i.succ T) (K : Set ℝ), IsOpen K ∧
        Real.sqrt (T - H.time i.succ) ∈ K ∧ K ⊆ Ioo W.a W.b ∧
        ∃ β : ThreeSpace × ℝ → W.X,
          ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (V ×ˢ K) ∧
          (∀ Z ∈ V, IsLRegularizedGeodesicOn W.S T (fun r => β (Z, r)) K) ∧
          ∀ Z (hZ : Z ∈ V) (j : H.StageInterval i.castSucc i.succ),
            ∀ r ∈ K ∩ Ioo (H.regularizedStageStart T W.a j.val)
              (H.regularizedStageEnd T W.b j.val),
              H.historyLCurve hle T v p ⟨Z, hVdom Z hZ⟩
                ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r = W.f j (β (Z, r)) := by
  set w := Real.sqrt (T - H.time i.succ) with hwdef
  obtain ⟨V, hV, hZ₀V, hVsub, hVdom, lo, hi, hlo', hhi', W, K, hK, hwK, hKW, β, hβ, hgeo, hrep⟩ :=
    exists_contMDiffOn_window_family_historyLCurve hv hZ₀ hw
  have hwW := hKW hwK
  have hT : T - w ^ 2 = H.time i.succ := by
    rw [hwdef, Real.sq_sqrt (Real.sqrt_pos.1 hw.1).le]
    ring
  have hold := LWindow.mem_range_of_mem_Icc W hwW (j := i.castSucc) (by
    rw [hT, stageEndTime_castSucc]
    exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩)
  have hnew := LWindow.mem_range_of_mem_Icc W hwW (j := i.succ) (by
    rw [hT]
    exact ⟨le_rfl, H.time_le_stageEndTime _⟩)
  have hend : H.time i.succ < H.stageEndTime i.succ := by
    have h1 := (H.le_stageEndTime_of_mem_stageDomain W.upper).trans
      (H.stageEndTime_le_horizon hi)
    have h2 : W.a ^ 2 < w ^ 2 := pow_lt_pow_left₀ hwW.1 W.nonneg two_ne_zero
    cases h : i.succ using Fin.lastCases with
    | last =>
      rw [stageEndTime_last]
      rw [h] at hT
      linarith
    | cast m =>
      rw [stageEndTime_castSucc]
      exact H.time_strictMono m.castSucc_lt_succ
  have hopen : IsOpen ((fun r : ℝ => T - r ^ 2) ⁻¹'
      Ioo (H.time i.castSucc) (H.stageEndTime i.succ) ∩ (K ∩ Ioo W.a W.b)) :=
    (isOpen_Ioo.preimage (by fun_prop)).inter (hK.inter isOpen_Ioo)
  have hwO : w ∈ (fun r : ℝ => T - r ^ 2) ⁻¹'
      Ioo (H.time i.castSucc) (H.stageEndTime i.succ) ∩ (K ∩ Ioo W.a W.b) :=
    ⟨show T - w ^ 2 ∈ Ioo (H.time i.castSucc) (H.stageEndTime i.succ) by
      rw [hT]
      exact ⟨H.time_strictMono i.castSucc_lt_succ, hend⟩, hwK, hwW⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen w hwO
  have hmem : ∀ r, w - ε / 2 ≤ r → r ≤ w + ε / 2 →
      r ∈ (fun r : ℝ => T - r ^ 2) ⁻¹' Ioo (H.time i.castSucc) (H.stageEndTime i.succ) ∩
        (K ∩ Ioo W.a W.b) := fun r h1 h2 => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith)
  have hl := hmem (w - ε / 2) le_rfl (by linarith)
  have hu := hmem (w + ε / 2) (by linarith) le_rfl
  have hwpos : 0 < w := hw.1
  have hup : T - (w - ε / 2) ^ 2 ∈ H.stageDomain i.succ := by
    refine H.mem_stageDomain_of_mem_Ioo ⟨?_, hl.1.2⟩
    have h0 : 0 ≤ w - ε / 2 := W.nonneg.trans hl.2.2.1.le
    have : (w - ε / 2) ^ 2 < w ^ 2 := pow_lt_pow_left₀ (by linarith) h0 two_ne_zero
    linarith
  have hdown : T - (w + ε / 2) ^ 2 ∈ H.stageDomain i.castSucc := by
    refine H.mem_stageDomain_of_mem_Ioo ⟨hu.1.1, ?_⟩
    rw [stageEndTime_castSucc]
    have : w ^ 2 < (w + ε / 2) ^ 2 := pow_lt_pow_left₀ (by linarith) hwpos.le two_ne_zero
    linarith
  refine ⟨V, hV, hZ₀V, hVsub, hVdom,
    W.restrict hold.1 hnew.2 i.castSucc_lt_succ.le hl.2.2.1.le (by linarith) hu.2.2.2.le hup
      hdown, K ∩ Ioo (w - ε / 2) (w + ε / 2), hK.inter isOpen_Ioo,
    ⟨hwK, by linarith, by linarith⟩, fun r hr => ⟨hr.2.1, hr.2.2⟩, β,
    hβ.mono (prod_mono subset_rfl inter_subset_left),
    fun Z hZ r hr => hgeo Z hZ r hr.1, fun Z hZ j r hr => ?_⟩
  have ha' : W.a ≤ w - ε / 2 := hl.2.2.1.le
  have hb' : w + ε / 2 ≤ W.b := hu.2.2.2.le
  exact hrep Z hZ ⟨j.val, hold.1.trans j.property.1, j.property.2.trans hnew.2⟩ r
    ⟨hr.1.1, (regularizedStageStart_le_of_le W.nonneg ha' j.val).trans_lt hr.2.1,
      hr.2.2.trans_le (regularizedStageEnd_le_of_le (by linarith) hb' j.val)⟩

end SeamExport

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
