import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.FamilyChainClosure

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

open private mem_regularizedStage_Icc exists_mem_Ioo_not_mem_range exists_stage_nhds
  LWindow.mem_range_of_mem_Icc from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.ExponentialSmooth
open private le_of_mem_stageDomain from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.Truncation
open private exists_stage_of_le LWindowChain.exists_contMDiff_eqOn
  LWindowChain.exists_partition_of_cover LWindowChain.le_of_mem_stageDomain'
  LWindowChain.mem_regularizedStage_Ioo' mem_Ioo_of_mem_stageDomain from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.IndexChain

universe u

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {T w : ℝ} {p : (H.stage last).Carrier}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_base_family (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZo : Z₀.1 ∈ H.historyLExpOpenDomain hle T w p) {m : ℝ} (hm : 0 < m) :
    ∃ (lo₀ : Fin (H.eventCount + 1)) (_ : first ≤ lo₀) (W₀ : H.LWindow lo₀ last T) (x : W₀.X)
      (L : ThreeSpace →L[ℝ] ThreeSpace) (V : Set ThreeSpace) (K : Set ℝ)
      (β₀ : ThreeSpace × ℝ → W₀.X) (c₁ : ℝ),
      W₀.a = 0 ∧ Function.Injective L ∧ 0 < c₁ ∧ c₁ < m ∧ c₁ < W₀.b ∧ c₁ < w ∧ IsOpen V ∧
      Z₀.1 ∈ V ∧ IsOpen K ∧ Icc 0 W₀.b ⊆ K ∧
      ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β₀ (V ×ˢ K) ∧
      (∀ Z ∈ V, IsLRegularizedGeodesicOn W₀.S T (fun r => β₀ (Z, r)) K) ∧
      (∀ Z ∈ V, ∀ s ∈ K, s ∈ lRegularizedDomain W₀.S T x (L Z) ∧
        β₀ (Z, s) = lRegularizedCurve W₀.S T x (L Z) s) ∧
      ∃ hVdom : (∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T w p),
      ∀ Z (hZ : Z ∈ V) (j : H.StageInterval first last) (hj : lo₀ ≤ j.val), ∀ r ∈ Icc 0 c₁,
        T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) →
        H.historyLCurve hle T w p ⟨Z, hVdom Z hZ⟩ j r =
          W₀.f ⟨j.val, hj, j.property.2⟩ (β₀ (Z, r)) := by
  classical
  have hgeo₀ := isHistoryLGeodesicOn_historyLCurve Z₀
  obtain ⟨lo₀, hlo₀, W₀, x, Zx₀, ha₀, hx, hZx₀, hdom, heq₀⟩ :=
    hasHistoryLInitialVector_historyLCurve Z₀
  have hb₀ : 0 < W₀.b := ha₀ ▸ W₀.lt
  obtain ⟨α, J, hJo, hJc, h0J, hbJ, hcurve⟩ := hdom
  obtain ⟨V', hV', hZV', K, hK, hKc, h0K, hbK, fam, hfam, hfamc⟩ :=
    lRegularizedFamily_extend W₀.S W₀.solution T hJo hJc h0J hbJ hcurve
  have hIcc : Icc 0 W₀.b ⊆ K := hKc.Icc_subset h0K hbK
  obtain ⟨c₁, hc₁, hne⟩ := exists_mem_Ioo_not_mem_range (H := H) (T := T)
    (lt_min (lt_min hb₀ hw) hm) le_rfl
  have hc₁b : c₁ < W₀.b := hc₁.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hc₁w : c₁ < w := hc₁.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hc₁m : c₁ < m := hc₁.2.trans_le (min_le_right _ _)
  have hT0 : T ∈ H.stageDomain last := by
    have h := W₀.upper
    rw [ha₀] at h
    simpa using h
  have hc₁0 : 0 ≤ T - c₁ ^ 2 := by
    have := H.time_le_of_mem_stageDomain hgeo₀.1
    have h2 : c₁ ^ 2 < w ^ 2 := pow_lt_pow_left₀ hc₁w hc₁.1.le two_ne_zero
    linarith [H.time_nonneg first]
  have hc₁h : T - c₁ ^ 2 < H.horizon := by
    have := (H.le_stageEndTime_of_mem_stageDomain hT0).trans (H.stageEndTime_le_horizon last)
    have : 0 < c₁ ^ 2 := pow_pos hc₁.1 2
    linarith
  obtain ⟨k₀, η, hη, -, hηk⟩ := exists_stage_nhds hc₁.1 hc₁0 hc₁h hne
  have hkc := hηk c₁ ⟨by linarith, by linarith⟩
  have hk₀d : T - c₁ ^ 2 ∈ H.stageDomain k₀ := H.mem_stageDomain_of_mem_Ioo hkc
  have hlo₀k₀ : lo₀ ≤ k₀ := le_of_mem_stageDomain W₀.lower hk₀d
    (sub_le_sub_left (pow_le_pow_left₀ hc₁.1.le hc₁b.le 2) T)
  have hfk₀ : first ≤ k₀ := first_le_of_mem_stageDomain hc₁.1.le hc₁w.le hgeo₀.1 hk₀d
  have hk₀l : k₀ ≤ last := le_of_mem_stageDomain hk₀d hT0 (by nlinarith)
  let e := (W₀.localDiffeomorph ⟨last, W₀.le, le_rfl⟩).mfderivToContinuousLinearEquiv
    (by simp) x
  let L : ThreeSpace →L[ℝ] ThreeSpace :=
    (e.symm : TangentSpace ThreeModel (W₀.f ⟨last, W₀.le, le_rfl⟩ x) →L[ℝ]
      TangentSpace ThreeModel x)
  have hLe : ∀ Z : ThreeSpace, mfderiv ThreeModel ThreeModel (W₀.f ⟨last, W₀.le, le_rfl⟩) x
      (L Z) = Z := fun Z => e.apply_symm_apply Z
  have hLinj : Function.Injective L := e.symm.injective
  have hLZ₀ : L Z₀.1 = Zx₀ := by
    have h : e Zx₀ = Z₀.1 := hZx₀
    have h2 : e.symm (e Zx₀) = Zx₀ := e.symm_apply_apply Zx₀
    rw [h] at h2
    exact h2
  set V : Set ThreeSpace := L ⁻¹' V' ∩ H.historyLExpOpenDomain hle T w p with hVdef
  have hV : IsOpen V := (hV'.preimage L.continuous).inter (isOpen_historyLExpOpenDomain hw)
  have hZ₀V : Z₀.1 ∈ V := ⟨by change L Z₀.1 ∈ V'; rw [hLZ₀]; exact hZV', hZo⟩
  have hVdom : ∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T w p :=
    fun Z hZ => historyLExpOpenDomain_subset_historyLExpDomain hZ.2
  let β₀ : ThreeSpace × ℝ → W₀.X := fun q => fam (L q.1, q.2)
  have hβ₀ : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β₀ (V ×ˢ K) := by
    have hmap : ContMDiff (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : ThreeSpace × ℝ => (L q.1, q.2)) :=
      (L.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    exact hfam.comp hmap.contMDiffOn fun q hq => ⟨hq.1.1, hq.2⟩
  have hcurveZ : ∀ Z ∈ V, IsLRegularizedCurveOn W₀.S T (fun s => β₀ (Z, s)) K x (L Z) :=
    fun Z hZ => hfamc (L Z) hZ.1
  have hlreg : ∀ Z ∈ V, ∀ s ∈ K, s ∈ lRegularizedDomain W₀.S T x (L Z) ∧
      β₀ (Z, s) = lRegularizedCurve W₀.S T x (L Z) s := fun Z hZ s hs =>
    ⟨⟨fun r => β₀ (Z, r), K, hK, hKc, h0K, hs, hcurveZ Z hZ⟩,
      (lRegularizedCurve_eqOn W₀.S W₀.solution T hK hKc h0K (hcurveZ Z hZ) hs).symm⟩
  refine ⟨lo₀, hlo₀, W₀, x, L, V, K, β₀, c₁, ha₀, hLinj, hc₁.1, hc₁m, hc₁b, hc₁w, hV, hZ₀V, hK,
    hIcc, hβ₀, fun Z hZ => (hcurveZ Z hZ).2.2, hlreg, hVdom, fun Z hZ j hj r hr ht => ?_⟩
  have hk₀j : k₀ ≤ j.val := by
    by_contra h
    have h1 := stageEndTime_le_time_of_lt (not_le.1 h)
    have h2 : r ^ 2 ≤ c₁ ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
    linarith [ht.2, hkc.1]
  let B : (j : H.StageInterval k₀ last) → ℝ → (H.stage j.val).Carrier :=
    fun j r => W₀.f ⟨j.val, hlo₀k₀.trans j.property.1, j.property.2⟩ (β₀ (Z, r))
  have hsub : ∀ s ∈ Icc (0 : ℝ) c₁, s ∈ K := fun s hs => hIcc ⟨hs.1, hs.2.trans hc₁b.le⟩
  let W' := W₀.restrict hlo₀k₀ le_rfl hk₀l (by rw [ha₀]) hc₁.1 hc₁b.le (by simpa using hT0) hk₀d
  have hW'a : W'.a = 0 := rfl
  have hB : H.IsHistoryLGeodesicOn hk₀l T c₁ B := by
    refine ⟨hk₀d, fun i hf hl => W₀.crossing i (hlo₀k₀.trans hf) hl _, fun s hs => ?_, ?_⟩
    · refine ⟨k₀, last, le_rfl, le_rfl, W', hs, le_rfl, fun r => β₀ (Z, r),
        fun r hr => (hcurveZ Z hZ).2.2 r (hsub r ⟨hr.1.le, hr.2.le⟩), fun j r hr => rfl⟩
    · exact ((W₀.localDiffeomorph _).contMDiff.continuous.continuousAt.comp
        ((hcurveZ Z hZ).2.2 c₁ (hsub c₁ ⟨hc₁.1.le, le_rfl⟩)).2.1.continuousAt).continuousWithinAt
  have hB₀ : H.HasHistoryLInitialVector T B p Z := by
    refine ⟨k₀, le_rfl, W', x, L Z, hW'a, hx, hLe Z, ?_, fun j r hr => ?_⟩
    · exact (hlreg Z hZ c₁ (hsub c₁ ⟨hc₁.1.le, le_rfl⟩)).1
    · have hr' : r ∈ Icc (0 : ℝ) c₁ := W'.piece_subset j hr
      change W₀.f _ (lRegularizedCurve W₀.S T x (L Z) r) = W₀.f _ (β₀ (Z, r))
      rw [(hlreg Z hZ r (hsub r hr')).2]
  have hA := (isHistoryLGeodesicOn_historyLCurve ⟨Z, hVdom Z hZ⟩).truncate hfk₀ hk₀l hc₁.1
    hc₁w.le hk₀d
  have hA₀ := (hasHistoryLInitialVector_historyLCurve ⟨Z, hVdom Z hZ⟩).truncate hc₁.1 hfk₀ hk₀d
  have heq := IsHistoryLGeodesicOn.eqOn_of_hasHistoryLInitialVector hc₁.1 hA hB hA₀ hB₀
    ⟨j.val, hk₀j, j.property.2⟩ (mem_regularizedStage_Icc le_rfl hr ht)
  exact heq

variable (hle) in
def FamilyPiece {fst : Fin (H.eventCount + 1)} (hfst : first ≤ fst) (T w v : ℝ)
    (p : (H.stage last).Carrier) (Z₀ : H.historyLExpDomain hle T w p) (x y : ℝ) : Prop :=
  ∃ (lo hi : Fin (H.eventCount + 1)) (hlo : fst ≤ lo) (hhi : hi ≤ last) (W : H.LWindow lo hi T)
    (γ : ℝ → W.X) (V : Set ThreeSpace) (K : Set ℝ) (β : ThreeSpace × ℝ → W.X),
    ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
    (∃ a b, a < x ∧ y < b ∧ IsLRegularizedGeodesicOn W.S T γ (Ioo a b)) ∧
    Icc x y ⊆ Icc W.a W.b ∧ (0 < x → W.a < x) ∧ (y < v → y < W.b) ∧
    (∀ j : H.StageInterval lo hi, EqOn (W.f j ∘ γ)
      (H.historyLCurve hle T w p Z₀
        ⟨j.val, (hfst.trans hlo).trans j.property.1, j.property.2.trans hhi⟩)
      (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))) ∧
    (∀ j, T - y ^ 2 ∈ H.stageDomain j → lo ≤ j) ∧ (∀ j, T - x ^ 2 ∈ H.stageDomain j → j ≤ hi) ∧
    IsOpen V ∧ Z₀.1 ∈ V ∧ IsOpen K ∧ Icc x y ⊆ K ∧ K ∩ Ioi 0 ⊆ Ioo W.a W.b ∧
    ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (V ×ˢ K) ∧
    (∀ Z ∈ V, IsLRegularizedGeodesicOn W.S T (fun r => β (Z, r)) K) ∧
    (∀ s ∈ K, β (Z₀.1, s) = γ s) ∧
    (∃ hVdom : (∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T w p),
      ∀ Z (hZ : Z ∈ V) (j : H.StageInterval lo hi),
        ∀ r ∈ K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val),
          H.historyLCurve hle T w p ⟨Z, hVdom Z hZ⟩
            ⟨j.val, (hfst.trans hlo).trans j.property.1, j.property.2.trans hhi⟩ r =
            W.f j (β (Z, r))) ∧
    (x = 0 → ∃ (xb : W.X) (L : ThreeSpace →L[ℝ] ThreeSpace), Function.Injective L ∧
      ∀ Z ∈ V, ∀ s ∈ K, s ∈ lRegularizedDomain W.S T xb (L Z) ∧
        β (Z, s) = lRegularizedCurve W.S T xb (L Z) s)

theorem familyPiece_of_window {fst : Fin (H.eventCount + 1)} (hfst : first ≤ fst)
    (Z₀ : H.historyLExpDomain hle T w p) {v : ℝ} (hv : 0 < v) (hvw : v < w)
    (hvf : H.time fst < T - v ^ 2) (hT : T ∈ H.stageDomain last)
    {lo hi : Fin (H.eventCount + 1)} (hlo : first ≤ lo) (hhi : hi ≤ last) (W : H.LWindow lo hi T)
    {V : Set ThreeSpace} {K : Set ℝ} {β : ThreeSpace × ℝ → W.X} (hV : IsOpen V)
    (hZ₀V : Z₀.1 ∈ V)
    (hVdom : ∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T w p)
    (hK : IsOpen K) (hKW : K ⊆ Ioo W.a W.b)
    (hβ : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (V ×ˢ K))
    (hgeo : ∀ Z ∈ V, IsLRegularizedGeodesicOn W.S T (fun r => β (Z, r)) K)
    (hrep : ∀ Z (hZ : Z ∈ V) (j : H.StageInterval lo hi),
      ∀ r ∈ K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val),
        H.historyLCurve hle T w p ⟨Z, hVdom Z hZ⟩
          ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r = W.f j (β (Z, r)))
    {x y : ℝ} (hxy : x < y) (hx0 : 0 < x) (hsub : Icc x y ⊆ K) (hyv : y ≤ v) :
    FamilyPiece hle hfst T w v p Z₀ x y := by
  obtain ⟨-, δ, hδ, -, -, -, hIoo⟩ := exists_bump_eq_one hK hxy.le hsub
  set ε := min δ x with hε
  have hε0 : 0 < ε := lt_min hδ hx0
  set e := min (min δ (w - v)) (min v ((T - v ^ 2 - H.time fst) / (4 * v))) / 2 with he
  have he0 : 0 < e := by
    have : 0 < (T - v ^ 2 - H.time fst) / (4 * v) := div_pos (by linarith) (by positivity)
    have h1 : 0 < min δ (w - v) := lt_min hδ (by linarith)
    have h2 : 0 < min v ((T - v ^ 2 - H.time fst) / (4 * v)) := lt_min hv this
    positivity
  have heδ : e < δ := by
    have := min_le_left (min δ (w - v)) (min v ((T - v ^ 2 - H.time fst) / (4 * v)))
    have := min_le_left δ (w - v)
    linarith
  have he2 : e ≤ δ / 2 := by
    have := min_le_left (min δ (w - v)) (min v ((T - v ^ 2 - H.time fst) / (4 * v)))
    have := min_le_left δ (w - v)
    linarith
  have hew : e < w - v := by
    have := min_le_left (min δ (w - v)) (min v ((T - v ^ 2 - H.time fst) / (4 * v)))
    have := min_le_right δ (w - v)
    linarith
  have hest : e ≤ min v ((T - v ^ 2 - H.time fst) / (4 * v)) := by
    have := min_le_right (min δ (w - v)) (min v ((T - v ^ 2 - H.time fst) / (4 * v)))
    have : 0 ≤ min v ((T - v ^ 2 - H.time fst) / (4 * v)) := (lt_min hv (div_pos (by linarith)
      (by positivity))).le
    linarith
  set a' := x - ε / 2 with ha'
  set b' := y + e with hb'
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεx : ε ≤ x := min_le_right _ _
  have ha'K : a' ∈ K := hIoo ⟨by linarith, by linarith⟩
  have hb'K : b' ∈ K := hIoo ⟨by linarith, by linarith⟩
  have ha'0 : 0 < a' := by linarith
  have hWa : W.a < a' := (hKW ha'K).1
  have hWb : b' < W.b := (hKW hb'K).2
  have hab' : a' < b' := by linarith
  have hTh : T ≤ H.horizon := (H.le_stageEndTime_of_mem_stageDomain hT).trans
    (H.stageEndTime_le_horizon last)
  obtain ⟨lo', hlo'm, hfst'⟩ := exists_stage_of_le (b := b') hT hvf (by linarith) (by linarith) hv
  have hmem : T - a' ^ 2 ∈ Icc (0 : ℝ) H.horizon := by
    have hvT : 0 ≤ T - v ^ 2 := (H.time_nonneg fst).trans hvf.le
    have : a' ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ ha'0.le (by linarith) 2
    constructor <;> nlinarith
  have hhi'm := H.activeStage_mem ⟨_, hmem⟩
  have hW0 := W.nonneg
  have h1 : lo ≤ lo' := LWindowChain.le_of_mem_stageDomain' W.lower hlo'm (by nlinarith)
  have h2 : H.activeStage ⟨_, hmem⟩ ≤ hi :=
    LWindowChain.le_of_mem_stageDomain' hhi'm W.upper (by nlinarith)
  have h3 : lo' ≤ H.activeStage ⟨_, hmem⟩ :=
    LWindowChain.le_of_mem_stageDomain' hlo'm hhi'm (by nlinarith)
  let W' := W.restrict h1 h2 h3 hWa.le hab' hWb.le hhi'm hlo'm
  set r := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hsubK : Ioo (a' - r) (b' + r) ⊆ K := fun s hs => hIoo ⟨by linarith [hs.1], by
    linarith [hs.2]⟩
  have hβZ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (fun s => β (Z₀.1, s)) K :=
    hβ.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn fun s hs => ⟨hZ₀V, hs⟩
  obtain ⟨γ, hγ, hγeq⟩ := LWindowChain.exists_contMDiff_eqOn hab'.le hr0 (hβZ.mono hsubK)
  have hcont : ∀ s ∈ K, ContinuousAt (fun s => β (Z₀.1, s)) s := fun s hs =>
    (hβZ s hs).continuousWithinAt.continuousAt (hK.mem_nhds hs)
  refine ⟨lo', H.activeStage ⟨_, hmem⟩, hfst', h2.trans hhi, W', γ, V, K ∩ Ioo a' b', β, hγ,
    ⟨a' - r / 2, b' + r / 2, by linarith, by linarith, ?_⟩,
    Icc_subset_Icc (by change a' ≤ x; linarith) (by change y ≤ b'; linarith),
    fun _ => by change a' < x; linarith, fun _ => by change y < b'; linarith, ?_, ?_, ?_, hV,
    hZ₀V, hK.inter isOpen_Ioo, fun s hs => ⟨hsub hs, by linarith [hs.1], by linarith [hs.2]⟩,
    fun s hs => hs.1.2, hβ.mono (prod_mono subset_rfl inter_subset_left),
    fun Z hZ s hs => hgeo Z hZ s hs.1, fun s hs => (hγeq ⟨by linarith [hs.2.1],
      by linarith [hs.2.2]⟩).symm, ⟨hVdom, fun Z hZ j s hs => ?_⟩, fun h => absurd h hx0.ne'⟩
  · have hg : IsLRegularizedGeodesicOn W.S T (fun s => β (Z₀.1, s))
        (Ioo (a' - r / 2) (b' + r / 2)) := fun s hs =>
      hgeo Z₀.1 hZ₀V s (hsubK ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    exact hg.congr_of_eventuallyEq fun s hs =>
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) fun t ht => hγeq ht
  · intro j t ht
    have htab : t ∈ Icc a' b' := W'.piece_subset j ht
    have htK : t ∈ K := hIoo ⟨by linarith [htab.1], by linarith [htab.2]⟩
    have hγt : γ t = β (Z₀.1, t) := hγeq ⟨by linarith [htab.1], by linarith [htab.2]⟩
    change W.f ⟨j.val, h1.trans j.property.1, j.property.2.trans h2⟩ (γ t) = _
    rw [hγt]
    refine (historyLCurve_eq_of_family Z₀ hlo hhi W hK hcont (hrep Z₀.1 hZ₀V)
      ⟨j.val, h1.trans j.property.1, j.property.2.trans h2⟩ htK (hKW htK) (by linarith [htab.2])
      ⟨(regularizedStageStart_le_of_le W.nonneg hWa.le j.val).trans ht.1,
        ht.2.trans (regularizedStageEnd_le_of_le (by linarith) hWb.le j.val)⟩).symm
  · intro j hj
    exact LWindowChain.le_of_mem_stageDomain' hlo'm hj (by nlinarith)
  · intro j hj
    exact LWindowChain.le_of_mem_stageDomain' hj hhi'm (by nlinarith)
  · exact hrep Z hZ ⟨j.val, h1.trans j.property.1, j.property.2.trans h2⟩ s ⟨hs.1.1,
      (regularizedStageStart_le_of_le W.nonneg hWa.le j.val).trans_lt hs.2.1,
      hs.2.2.trans_le (regularizedStageEnd_le_of_le (by linarith) hWb.le j.val)⟩

theorem exists_base_cover {fst : Fin (H.eventCount + 1)} (hfst : first ≤ fst)
    (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZo : Z₀.1 ∈ H.historyLExpOpenDomain hle T w p) {v : ℝ} (hv : 0 < v)
    (hvf : H.time fst < T - v ^ 2) (hT : T ∈ H.stageDomain last) :
    ∃ O : Set ℝ, IsOpen O ∧ (0 : ℝ) ∈ O ∧ ∀ x y, x < y → Icc x y ⊆ O → Icc x y ⊆ Icc 0 v →
      FamilyPiece hle hfst T w v p Z₀ x y := by
  obtain ⟨lo₀, hlo₀, W₀, xb, L, V, K, β₀, c₁, ha₀, hL, hc₁, hc₁v, hc₁b, -, hV, hZ₀V, hK, hIccK,
    hβ₀, hgeo, hlreg, hVdom, hrep⟩ := exists_base_family hw Z₀ hZo hv
  have hb₀ : 0 < W₀.b := ha₀ ▸ W₀.lt
  refine ⟨K ∩ Iio c₁, hK.inter isOpen_Iio, ⟨hIccK ⟨le_rfl, hb₀.le⟩, hc₁⟩,
    fun x y hxy hO hI => ?_⟩
  have hx0 : 0 ≤ x := (hI (left_mem_Icc.2 hxy.le)).1
  have hyv : y ≤ v := (hI (right_mem_Icc.2 hxy.le)).2
  have hyc : y < c₁ := (hO (right_mem_Icc.2 hxy.le)).2
  set e := min (c₁ - y) (min v ((T - v ^ 2 - H.time fst) / (4 * v))) / 2 with he
  have hst0 : 0 < min v ((T - v ^ 2 - H.time fst) / (4 * v)) :=
    lt_min hv (div_pos (by linarith) (by positivity))
  have he0 : 0 < e := by
    have : 0 < min (c₁ - y) (min v ((T - v ^ 2 - H.time fst) / (4 * v))) :=
      lt_min (by linarith) hst0
    positivity
  have hec : e < c₁ - y := by
    have := min_le_left (c₁ - y) (min v ((T - v ^ 2 - H.time fst) / (4 * v)))
    linarith
  have hest : e ≤ min v ((T - v ^ 2 - H.time fst) / (4 * v)) := by
    have := min_le_right (c₁ - y) (min v ((T - v ^ 2 - H.time fst) / (4 * v)))
    linarith
  set b' := y + e with hb'
  have hb'0 : 0 < b' := by linarith
  have hb'c : b' < c₁ := by linarith
  obtain ⟨lo', hlo'm, hfst'⟩ := exists_stage_of_le (b := b') hT hvf hb'0.le (by linarith) hv
  have h1 : lo₀ ≤ lo' := LWindowChain.le_of_mem_stageDomain' W₀.lower hlo'm (by nlinarith)
  have h3 : lo' ≤ last := LWindowChain.le_of_mem_stageDomain' hlo'm hT (by nlinarith)
  let W' := W₀.restrict h1 le_rfl h3 ha₀.le hb'0 (hb'c.trans hc₁b).le (by simpa using hT) hlo'm
  obtain ⟨-, δ, hδ, -, -, -, hIoo⟩ := exists_bump_eq_one hK hb'0.le
    (fun s hs => hIccK ⟨hs.1, hs.2.trans (hb'c.trans hc₁b).le⟩)
  have hβZ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (fun s => β₀ (Z₀.1, s)) K :=
    hβ₀.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn fun s hs => ⟨hZ₀V, hs⟩
  obtain ⟨γ, hγ, hγeq⟩ := LWindowChain.exists_contMDiff_eqOn hb'0.le hδ (hβZ.mono hIoo)
  have hsub' : Icc (0 : ℝ) b' ⊆ Icc 0 c₁ := Icc_subset_Icc le_rfl hb'c.le
  refine ⟨lo', last, hfst', le_rfl, W', γ, V, K ∩ Ioo (0 - δ / 2) b', β₀, hγ,
    ⟨0 - δ / 2, b' + δ / 2, by linarith, by linarith, ?_⟩,
    Icc_subset_Icc (by change 0 ≤ x; linarith) (by change y ≤ b'; linarith),
    fun h => by change 0 < x; exact h, fun _ => by change y < b'; linarith, ?_,
    fun j hj => LWindowChain.le_of_mem_stageDomain' hlo'm hj (by nlinarith),
    fun j hj => LWindowChain.le_of_mem_stageDomain' hj hT (by nlinarith), hV, hZ₀V,
    hK.inter isOpen_Ioo,
    fun s hs => ⟨hIccK ⟨hx0.trans hs.1, hs.2.trans (by linarith [hb'c, hc₁b])⟩,
      by linarith [hs.1], by linarith [hs.2]⟩,
    fun s hs => ⟨hs.2, hs.1.2.2⟩, hβ₀.mono (prod_mono subset_rfl inter_subset_left),
    fun Z hZ s hs => hgeo Z hZ s hs.1,
    fun s hs => (hγeq ⟨by linarith [hs.2.1], by linarith [hs.2.2]⟩).symm, ⟨hVdom, ?_⟩,
    fun _ => ⟨xb, L, hL, fun Z hZ s hs => hlreg Z hZ s hs.1⟩⟩
  · have hg : IsLRegularizedGeodesicOn W₀.S T (fun s => β₀ (Z₀.1, s))
        (Ioo (0 - δ / 2) (b' + δ / 2)) := fun s hs =>
      hgeo Z₀.1 hZ₀V s (hIoo ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    exact hg.congr_of_eventuallyEq fun s hs =>
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) fun t ht => hγeq ht
  · intro j t ht
    have htab : t ∈ Icc (0 : ℝ) b' := W'.piece_subset j ht
    have hγt : γ t = β₀ (Z₀.1, t) := hγeq ⟨by linarith [htab.1], by linarith [htab.2]⟩
    change W₀.f ⟨j.val, h1.trans j.property.1, j.property.2⟩ (γ t) = _
    rw [hγt]
    exact (hrep Z₀.1 hZ₀V ⟨j.val, hlo₀.trans (h1.trans j.property.1), j.property.2⟩
      (h1.trans j.property.1) t (hsub' htab) (W'.mem_Icc_of_mem_piece j ht)).symm
  · intro Z hZ j t ht
    have ht' := H.mapsTo_regularizedStage_Ioo T 0 b' j.val ht.2
    have htab : t ∈ Icc (0 : ℝ) b' := W'.piece_subset j (Ioo_subset_Icc_self ht.2)
    exact hrep Z hZ ⟨j.val, hlo₀.trans (h1.trans j.property.1), j.property.2⟩
      (h1.trans j.property.1) t (hsub' htab)
      ⟨H.time_le_of_mem_stageDomain ht', H.le_stageEndTime_of_mem_stageDomain ht'⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
