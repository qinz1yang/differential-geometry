import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.JacobiField.FamilyChain.LocalFamilies

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

open private exists_stage_of_le LWindowChain.exists_contMDiff_eqOn
  LWindowChain.exists_partition_of_cover LWindowChain.le_of_mem_stageDomain'
  LWindowChain.mem_regularizedStage_Ioo' mem_Ioo_of_mem_stageDomain from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.IndexForm.WindowChain

universe u

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {T w : ℝ} {p : (H.stage last).Carrier}

theorem exists_lFamilyChain (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZo : Z₀.1 ∈ H.historyLExpOpenDomain hle T w p) (hT : T ∈ H.stageDomain last) {v : ℝ}
    (hv : 0 < v) (hvw : v < w) {fst : Fin (H.eventCount + 1)} (hfst : first ≤ fst)
    (hvf : T - v ^ 2 ∈ Ioo (H.time fst) (H.stageEndTime fst)) {w' : ℝ} (hw' : 0 < w')
    (hw'v : w' < v) (hw'F : T - w' ^ 2 ∉ range H.time) :
    ∃ ch : H.LFamilyChain hle hfst T w v p Z₀, ∃ m, 0 < m ∧ m < ch.n ∧ ch.c m = w' := by
  classical
  have hcov : ∀ s ∈ Icc 0 v, ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧ ∀ x y, x < y → Icc x y ⊆ U →
      Icc x y ⊆ Icc 0 v → FamilyPiece hle hfst T w v p Z₀ x y := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · subst hs0
      exact exists_base_cover hfst hw Z₀ hZo hv hvf.1 hT
    · obtain ⟨V, hV, hZ₀V, -, hVdom, lo, hi, hlo, hhi, W, K, hK, hsK, hKW, β, hβ, hgeo, hrep⟩ :=
        exists_contMDiffOn_window_family_historyLCurve hw hZo ⟨hs0, hs.2.trans_lt hvw⟩
      refine ⟨K, hK, hsK, fun x y hxy hU hI => ?_⟩
      have hx0 : 0 < x := W.nonneg.trans_lt (hKW (hU (left_mem_Icc.2 hxy.le))).1
      exact familyPiece_of_window hfst Z₀ hv hvw hvf.1 hT hlo hhi W hV hZ₀V hVdom hK hKW hβ hgeo
        hrep hxy hx0 hU (hI (right_mem_Icc.2 hxy.le)).2
  let O : ℝ → Set ℝ := fun s => if hs : s ∈ Icc 0 v then Classical.choose (hcov s hs) else univ
  have hO : ∀ s ∈ Icc 0 v, IsOpen (O s) ∧ s ∈ O s := fun s hs => by
    simp only [O, dite_eq_left hs]
    exact ⟨(Classical.choose_spec (hcov s hs)).1, (Classical.choose_spec (hcov s hs)).2.1⟩
  have hOP : ∀ s ∈ Icc 0 v, ∀ x y, x < y → Icc x y ⊆ O s → Icc x y ⊆ Icc 0 v →
      FamilyPiece hle hfst T w v p Z₀ x y := fun s hs => by
    simp only [O, dite_eq_left hs]
    exact (Classical.choose_spec (hcov s hs)).2.2
  have hwF' : w' ∉ range (fun i => Real.sqrt (T - H.time i)) := by
    rintro ⟨i, hi⟩
    replace hi : Real.sqrt (T - H.time i) = w' := hi
    apply hw'F
    refine ⟨i, ?_⟩
    have hpos : 0 ≤ T - H.time i := by
      by_contra h
      rw [Real.sqrt_eq_zero'.2 (not_le.1 h).le] at hi
      linarith
    rw [← hi, Real.sq_sqrt hpos]
    ring
  obtain ⟨n, c, hc0, hcn, hlt, hcF, ⟨m, hm0, hmn, hcm⟩, hcI, hcO⟩ :=
    LWindowChain.exists_partition_of_cover hw' hw'v (Set.finite_range _) hwF' O hO
  have hpd : ∀ k, FamilyPiece hle hfst T w v p Z₀ (c (min k (n - 1))) (c (min k (n - 1) + 1)) := by
    intro k
    have hk : min k (n - 1) < n := (min_le_right _ _).trans_lt (by omega)
    obtain ⟨s, hs, hsub⟩ := hcO _ hk
    exact hOP s hs _ _ (hlt _ hk) hsub (Icc_subset_Icc (hcI _ hk.le).1 (hcI _ hk).2)
  choose lo hi hlo hhi W γ V K β hγ hgeo' hpiece hxa hyb heq hstlo hsthi hVo hZV hKo hpK hKW hβ
    hfam hcurve hVR hbase using hpd
  choose hVdom hrep using hVR
  have hmin : ∀ k < n, min k (n - 1) = k := fun k hk => min_eq_left (by omega)
  have hTh : T ≤ H.horizon := (H.le_stageEndTime_of_mem_stageDomain hT).trans
    (H.stageEndTime_le_horizon last)
  have hvT : 0 ≤ T - v ^ 2 := (H.time_nonneg fst).trans hvf.1.le
  have hmemI : ∀ j ≤ n, T - c j ^ 2 ∈ Icc (0 : ℝ) H.horizon := fun j hj => by
    have h := hcI j hj
    constructor <;> nlinarith [h.1, h.2]
  let stg : ℕ → Fin (H.eventCount + 1) := fun j =>
    if j = 0 then last else if j = n then fst else
      if h : T - c j ^ 2 ∈ Icc (0 : ℝ) H.horizon then H.activeStage ⟨_, h⟩ else last
  have hstg : ∀ j (hj : 0 < j) (hjn : j < n), stg j = H.activeStage ⟨_, hmemI j hjn.le⟩ := by
    intro j hj hjn
    simp only [stg, ite_eq_right hj.ne', ite_eq_right hjn.ne, dite_eq_left (hmemI j hjn.le)]
  have hstgmem : ∀ j ≤ n, T - c j ^ 2 ∈ H.stageDomain (stg j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp only [stg, ite_eq_left rfl, hc0]
      simpa using hT
    rcases eq_or_lt_of_le hj with rfl | hjn
    · simp only [stg, ite_eq_right hpos.ne', hcn]
      exact H.mem_stageDomain_of_mem_Ioo hvf
    · rw [hstg j hpos hjn]
      exact H.activeStage_mem _
  refine ⟨
    { n := n, c := c, c_zero := hc0, c_n := hcn, lt := hlt, lo := lo, hi := hi
      first_le := hlo, le_last := hhi, W := W, γ := γ, geodesic := ?_, piece := ?_
      eqOn := ?_, contMDiff := hγ, stage := stg, stage_zero := (by simp [stg])
      stage_n := ?_, mem_stageDomain := hstgmem, lo_le_stage := ?_, stage_le_hi := ?_
      node := ?_, V := V, K := K, β := β, isOpen_V := hVo, mem_V := hZV, V_sub := hVdom
      isOpen_K := hKo, piece_K := ?_, K_W := hKW, smooth := hβ, family := hfam, curve := hcurve
      rep := hrep, base := ?_ },
    m, hm0, hmn, hcm⟩
  · intro k hk
    have h := hgeo' k
    rw [hmin k hk] at h
    exact h
  · intro k hk
    have h := hpiece k
    rw [hmin k hk] at h
    exact h
  · intro k _ j
    exact heq k j
  · show stg n = fst
    simp [stg, show n ≠ 0 by omega]
  · intro k hk
    have h := hstlo k
    rw [hmin k hk] at h
    exact h _ (hstgmem (k + 1) hk)
  · intro k hk
    have h := hsthi k
    rw [hmin k hk] at h
    exact h _ (hstgmem k hk.le)
  · intro k hk
    have hk' : k < n := by omega
    have hmono : ∀ i j, i < j → j ≤ n → c i < c j := by
      intro i j hij hjn
      induction j with
      | zero => omega
      | succ j ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
        · exact (ih h (by omega)).trans (hlt j (by omega))
        · exact hlt i (by omega)
    have hpos : 0 < c (k + 1) := hc0 ▸ hmono 0 (k + 1) (by omega) hk.le
    have hcv : c (k + 1) < v := hcn ▸ hmono (k + 1) n hk le_rfl
    have hT' : T - c (k + 1) ^ 2 < H.horizon := by nlinarith
    have hne : T - c (k + 1) ^ 2 ∉ range H.time := by
      rintro ⟨i, hi⟩
      apply hcF (k + 1) (by omega) hk
      refine ⟨i, ?_⟩
      change Real.sqrt (T - H.time i) = c (k + 1)
      rw [hi, show T - (T - c (k + 1) ^ 2) = c (k + 1) ^ 2 by ring, Real.sqrt_sq hpos.le]
    have hIoo := mem_Ioo_of_mem_stageDomain (hstgmem (k + 1) hk.le) hne hT'
    have p₁ := hpiece k
    have p₂ := hpiece (k + 1)
    have y₁ := hyb k
    have x₂ := hxa (k + 1)
    rw [hmin k hk'] at p₁ y₁
    rw [hmin (k + 1) hk] at p₂ x₂
    refine ⟨LWindowChain.mem_regularizedStage_Ioo' (W k).nonneg ⟨?_, y₁ hcv⟩ hIoo,
      LWindowChain.mem_regularizedStage_Ioo' (W (k + 1)).nonneg ⟨x₂ hpos, ?_⟩ hIoo⟩
    · exact (p₁ (left_mem_Icc.2 (hlt k hk').le)).1.trans_lt (hlt k hk')
    · exact (hlt (k + 1) hk).trans_le (p₂ (right_mem_Icc.2 (hlt (k + 1) hk).le)).2
  · intro k hk
    have h := hpK k
    rw [hmin k hk] at h
    exact h
  · have h0 : min 0 (n - 1) = 0 := Nat.zero_min _
    have h := hbase 0
    rw [h0] at h
    exact h hc0


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
