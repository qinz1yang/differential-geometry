import DifferentialGeometry.Topology.PiecewiseLinear.ConeLayers

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def stdCone : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}

def stdConeLayer (σ' σ : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ σ' ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ σ}

def stdConeLayerLow (σ' σ : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ σ' ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ σ ∧
    σ' * z.1 + σ * z.2 ≤ σ' * σ}

def stdConeLayerHigh (σ' σ : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ σ' ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ σ ∧
    σ' * σ ≤ σ' * z.1 + σ * z.2}

theorem stdConeLayer_union_split (σ' σ : ℝ) :
    stdConeLayerLow σ' σ ∪ stdConeLayerHigh σ' σ = stdConeLayer σ' σ := by
  ext z
  constructor
  · rintro (⟨h1, h2, h3, h4, -⟩ | ⟨h1, h2, h3, h4, -⟩) <;> exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    rcases le_total (σ' * z.1 + σ * z.2) (σ' * σ) with h | h
    · exact Or.inl ⟨h1, h2, h3, h4, h⟩
    · exact Or.inr ⟨h1, h2, h3, h4, h⟩

theorem stdConeLayer_union (σ : ℕ → ℝ) (N : ℕ) (hmono : ∀ k ≤ N, σ k ≤ σ (k + 1))
    (h0 : σ 0 = 0) (hN : σ (N + 1) = 1) :
    ⋃ k ∈ Finset.range (N + 1), stdConeLayer (σ k) (σ (k + 1)) = stdCone := by
  have hchain := le_of_chain hmono
  ext z
  simp only [mem_iUnion₂, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, h1, h2, h3, h4⟩
    exact ⟨h1, h2, h4.trans (by rw [← hN]; exact hchain (N + 1) le_rfl (k + 1) (by omega))⟩
  · rintro ⟨h1, h2, h3⟩
    have hex : ∃ k, k < N + 1 ∧ σ k ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ σ (k + 1) := by
      classical
      have hP0 : (fun k => σ k ≤ z.1 + z.2) 0 := by
        change σ 0 ≤ z.1 + z.2
        rw [h0]
        linarith
      have hPlam : (fun k => σ k ≤ z.1 + z.2)
          (Nat.findGreatest (fun k => σ k ≤ z.1 + z.2) N) :=
        Nat.findGreatest_spec (P := fun k => σ k ≤ z.1 + z.2) (Nat.zero_le N) hP0
      have hPk : σ (Nat.findGreatest (fun k => σ k ≤ z.1 + z.2) N) ≤ z.1 + z.2 := hPlam
      have hkle : Nat.findGreatest (fun k => σ k ≤ z.1 + z.2) N ≤ N := Nat.findGreatest_le N
      rcases eq_or_lt_of_le hkle with heq | hlt
      · refine ⟨N, by omega, heq ▸ hPk, ?_⟩
        rw [hN]
        exact h3
      · have hnotlam : ¬ (fun k => σ k ≤ z.1 + z.2)
            (Nat.findGreatest (fun k => σ k ≤ z.1 + z.2) N + 1) :=
          Nat.findGreatest_is_greatest (P := fun k => σ k ≤ z.1 + z.2) (Nat.lt_succ_self _)
            (Nat.succ_le_of_lt hlt)
        have hnot : ¬ (σ (Nat.findGreatest (fun k => σ k ≤ z.1 + z.2) N + 1) ≤ z.1 + z.2) :=
          hnotlam
        exact ⟨_, by omega, hPk, (lt_of_not_ge hnot).le⟩
    obtain ⟨k, hk, hk1, hk2⟩ := hex
    exact ⟨k, hk, h1, h2, hk1, hk2⟩

theorem stdConeLayerLow_subset {σ' σ : ℝ} (hσ1 : σ ≤ 1) :
    stdConeLayerLow σ' σ ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  rintro ⟨x, y⟩ ⟨h1, h2, h3, h4, -⟩
  exact ⟨⟨h1, by simp only at *; linarith⟩, ⟨h2, by simp only at *; linarith⟩⟩

theorem stdConeLayerHigh_subset {σ' σ : ℝ} (hσ1 : σ ≤ 1) :
    stdConeLayerHigh σ' σ ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  rintro ⟨x, y⟩ ⟨h1, h2, h3, h4, -⟩
  exact ⟨⟨h1, by simp only at *; linarith⟩, ⟨h2, by simp only at *; linarith⟩⟩

theorem isHPolytope_stdConeLayerLow {σ' σ : ℝ} (hσ1 : σ ≤ 1) :
    IsHPolytope (stdConeLayerLow σ' σ) := by
  refine ⟨?_, Fin 5, inferInstance,
    ![-(LinearMap.fst ℝ ℝ ℝ), -(LinearMap.snd ℝ ℝ ℝ),
      -(LinearMap.fst ℝ ℝ ℝ) - LinearMap.snd ℝ ℝ ℝ,
      LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ,
      σ' • LinearMap.fst ℝ ℝ ℝ + σ • LinearMap.snd ℝ ℝ ℝ],
    ![0, 0, -σ', σ, σ' * σ], ?_⟩
  · refine IsCompact.of_isClosed_subset (isCompact_Icc.prod isCompact_Icc) ?_
      (stdConeLayerLow_subset hσ1)
    have hrw : stdConeLayerLow σ' σ = ({z : ℝ × ℝ | 0 ≤ z.1} ∩ {z : ℝ × ℝ | 0 ≤ z.2}) ∩
        (({z : ℝ × ℝ | σ' ≤ z.1 + z.2} ∩ {z : ℝ × ℝ | z.1 + z.2 ≤ σ}) ∩
          {z : ℝ × ℝ | σ' * z.1 + σ * z.2 ≤ σ' * σ}) := by
      ext z
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, ⟨⟨h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩⟩,
        fun h => ⟨h.1.1, h.1.2, h.2.1.1, h.2.1.2, h.2.2⟩⟩
    rw [hrw]
    refine (((isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)).inter
      (((isClosed_le continuous_const (continuous_fst.add continuous_snd)).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const)).inter
        (isClosed_le ((continuous_const.mul continuous_fst).add
          (continuous_const.mul continuous_snd)) continuous_const)))
  · ext z
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩ i
      fin_cases i <;> simp <;> linarith
    · intro h
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      have h3 := h 3
      have h4 := h 4
      simp at h0 h1 h2 h3 h4
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem isHPolytope_stdConeLayerHigh {σ' σ : ℝ} (hσ1 : σ ≤ 1) :
    IsHPolytope (stdConeLayerHigh σ' σ) := by
  refine ⟨?_, Fin 5, inferInstance,
    ![-(LinearMap.fst ℝ ℝ ℝ), -(LinearMap.snd ℝ ℝ ℝ),
      -(LinearMap.fst ℝ ℝ ℝ) - LinearMap.snd ℝ ℝ ℝ,
      LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ,
      -(σ' • LinearMap.fst ℝ ℝ ℝ) - σ • LinearMap.snd ℝ ℝ ℝ],
    ![0, 0, -σ', σ, -(σ' * σ)], ?_⟩
  · refine IsCompact.of_isClosed_subset (isCompact_Icc.prod isCompact_Icc) ?_
      (stdConeLayerHigh_subset hσ1)
    have hrw : stdConeLayerHigh σ' σ = ({z : ℝ × ℝ | 0 ≤ z.1} ∩ {z : ℝ × ℝ | 0 ≤ z.2}) ∩
        (({z : ℝ × ℝ | σ' ≤ z.1 + z.2} ∩ {z : ℝ × ℝ | z.1 + z.2 ≤ σ}) ∩
          {z : ℝ × ℝ | σ' * σ ≤ σ' * z.1 + σ * z.2}) := by
      ext z
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, ⟨⟨h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩⟩,
        fun h => ⟨h.1.1, h.1.2, h.2.1.1, h.2.1.2, h.2.2⟩⟩
    rw [hrw]
    refine (((isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)).inter
      (((isClosed_le continuous_const (continuous_fst.add continuous_snd)).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const)).inter
        (isClosed_le continuous_const ((continuous_const.mul continuous_fst).add
          (continuous_const.mul continuous_snd)))))
  · ext z
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩ i
      fin_cases i <;> simp <;> linarith
    · intro h
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      have h3 := h 3
      have h4 := h 4
      simp at h0 h1 h2 h3 h4
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

end DifferentialGeometry.Topology.PiecewiseLinear
