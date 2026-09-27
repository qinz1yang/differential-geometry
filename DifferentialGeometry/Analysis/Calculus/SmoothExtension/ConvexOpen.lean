import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

open scoped ContDiff

namespace DifferentialGeometry.Analysis

open Set

theorem exists_contDiff_range_subset_eqOn_eqOn_compl
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {K U : Set V} (hK : IsCompact K) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hKU : K ⊆ U) {z : V} (hz : z ∈ U) :
    ∃ r : V → V, ContDiff ℝ ∞ r ∧ range r ⊆ U ∧ EqOn r id K ∧
      EqOn r (fun _ => z) Uᶜ := by
  obtain ⟨χ, hχ, -, hχone, hχsupp, hχrange⟩ := exists_bump_compact hK hU hKU
  refine ⟨fun x => χ x • x + (1 - χ x) • z,
    (hχ.smul contDiff_id).add ((contDiff_const.sub hχ).smul contDiff_const), ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    by_cases hx : χ x = 0
    · simpa only [hx, zero_smul, sub_zero, one_smul, zero_add] using hz
    · have hχx : χ x ∈ Icc (0 : ℝ) 1 := hχrange ⟨x, rfl⟩
      exact hconv (hχsupp (subset_tsupport χ hx)) hz hχx.1
        (sub_nonneg.mpr hχx.2) (by ring)
  · intro x hx
    simp only [hχone.self_of_nhdsSet hx, Pi.one_apply, one_smul, sub_self,
      zero_smul, add_zero, id_eq]
  · intro x hx
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hχsupp h))
    simp only [hχx, zero_smul, sub_zero, one_smul, zero_add]

theorem exists_contDiff_range_subset_eqOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {K U : Set V} (hK : IsCompact K) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hKU : K ⊆ U) (hne : U.Nonempty) :
    ∃ r : V → V, ContDiff ℝ ∞ r ∧ range r ⊆ U ∧ EqOn r id K := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r, hr, hrU, hrK, -⟩ :=
    exists_contDiff_range_subset_eqOn_eqOn_compl hK hU hconv hKU hz
  exact ⟨r, hr, hrU, hrK⟩

theorem exists_contDiff_range_subset_eqOn_nhds_Ioo
    {a b c : ℝ} (hac : a < c) (hcb : c < b) :
    ∃ ψ : ℝ → ℝ, ∃ ε > 0, ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Ioo a b ∧
      Ioo (c - ε) (c + ε) ⊆ Ioo a b ∧
      EqOn ψ id (Ioo (c - ε) (c + ε)) ∧ EqOn ψ (fun _ => c) (Ioo a b)ᶜ := by
  let ε := min (c - a) (b - c) / 2
  have hε : 0 < ε := half_pos (lt_min (sub_pos.mpr hac) (sub_pos.mpr hcb))
  have hsub : Icc (c - ε) (c + ε) ⊆ Ioo a b := by
    intro t ht
    dsimp [ε] at *
    constructor <;> linarith [ht.1, ht.2, min_le_left (c - a) (b - c), min_le_right (c - a) (b - c)]
  obtain ⟨ψ, hψ, hψrange, hψid, hψout⟩ :=
    exists_contDiff_range_subset_eqOn_eqOn_compl isCompact_Icc isOpen_Ioo
      (convex_Ioo a b) hsub ⟨hac, hcb⟩
  have hεsub : Ioo (c - ε) (c + ε) ⊆ Icc (c - ε) (c + ε) := Ioo_subset_Icc_self
  exact ⟨ψ, ε, hε, hψ, hψrange, hεsub.trans hsub, hψid.mono hεsub, hψout⟩

end DifferentialGeometry.Analysis
