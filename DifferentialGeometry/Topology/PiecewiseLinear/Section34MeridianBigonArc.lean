import DifferentialGeometry.Topology.PiecewiseLinear.ExistsAnnulusParametrizationOfProductCircleCut
import DifferentialGeometry.Topology.PiecewiseLinear.CircleIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLSphere.exists_returning_arc_of_integer_height_marks {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} (hQ : IsPLSphere 1 Q) {n : ℕ} (hn : 0 < n)
    (q : Fin n → E) (hq : ∀ i, q i ∈ Q) (hinj : Function.Injective q)
    {g : E → ℝ} (hg : ContinuousOn g Q)
    (hmarks : ∀ x ∈ Q, (∃ m : ℤ, g x = m) ↔ ∃ i, q i = x)
    (hcross : ∀ i, (∃ a ∈ Q, g a < g (q i)) ∧ ∃ b ∈ Q, g (q i) < g b) :
    ∃ (i j : Fin n) (m : ℤ) (β : ℝ → E), i ≠ j ∧
      IsPLHomeomorphOn β (Icc 0 1) (β '' Icc 0 1) ∧ β 0 = q i ∧ β 1 = q j ∧
      β '' Icc 0 1 ⊆ Q ∧ (∀ k, q k ∉ β '' Ioo 0 1) ∧
      g (q i) = m ∧ g (q j) = m ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, (m : ℝ) < g (β t) ∧ g (β t) < m + 1) ∧
      IsClosed (Q \ β '' Ioo 0 1) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        ∀ t ∈ Icc (0 : ℝ) 1, (m : ℝ) ≤ g (β t) ∧ g (β t) ≤ m + δ := by
  classical
  have htwo : 1 < n := by
    by_contra hnot
    have hn1 : n = 1 := by omega
    let i : Fin n := ⟨0, hn⟩
    obtain ⟨⟨a, ha, halt⟩, b, hb, hblt⟩ := hcross i
    have hane : a ≠ q i := fun heq => halt.ne (congrArg g heq)
    have hbne : b ≠ q i := fun heq => hblt.ne' (congrArg g heq)
    have hconn := (hQ.isConnected_sdiff_singleton_one (q i)).isPreconnected
    obtain ⟨x, hx, hgx⟩ := hconn.intermediate_value ⟨ha, hane⟩ ⟨hb, hbne⟩
      (hg.mono sdiff_subset) ⟨halt.le, hblt.le⟩
    obtain ⟨m, hm⟩ := (hmarks (q i) (hq i)).mpr ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := (hmarks x hx.1).mp ⟨m, hgx.trans hm⟩
    have hji : j = i := Fin.ext (by have := j.isLt; have := i.isLt; omega)
    exact hx.2 (hj.symm.trans (congrArg q hji))
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => g (q i))
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨m, hm⟩ := (hmarks (q i₀) (hq i₀)).mpr ⟨i₀, rfl⟩
  have hmax' (i : Fin n) : g (q i) ≤ (m : ℝ) := hm ▸ hmax i (Finset.mem_univ i)
  obtain ⟨b, hbQ, hbg⟩ := (hcross i₀).2
  rw [hm] at hbg
  obtain ⟨r, hmr, hr⟩ := exists_between (lt_min hbg (by linarith : (m : ℝ) < m + 1))
  obtain ⟨s, hsQ, hgs⟩ := hQ.isConnected_one.isPreconnected.intermediate_value
    (hq i₀) hbQ hg ⟨hm ▸ hmr.le, (hr.trans_le (min_le_left _ _)).le⟩
  have hsr : (m : ℝ) < g s ∧ g s < m + 1 := by
    rw [hgs]
    exact ⟨hmr, hr.trans_le (min_le_right _ _)⟩
  have hsq : ∀ i, q i ≠ s := fun i heq =>
    (not_le_of_gt hsr.1) (heq ▸ hmax' i)
  obtain ⟨i, j, β, hij, hβ, hzero, hone, hβQ, hsβ, hno, hclosed⟩ :=
    hQ.exists_arc_between_adjacent_marks htwo q hq hinj hsQ hsq
  have hcont : ContinuousOn (g ∘ β) (Icc (0 : ℝ) 1) := hg.comp
    hβ.isPiecewiseAffineOn.continuousOn (fun t ht => hβQ ⟨t, ht, rfl⟩)
  have havoid (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (z : ℤ) : g (β t) ≠ z := by
    intro heq
    obtain ⟨k, hk⟩ := (hmarks (β t) (hβQ ⟨t, Ioo_subset_Icc_self ht, rfl⟩)).mp ⟨z, heq⟩
    exact hno k ⟨t, ht, hk.symm⟩
  have hpre : IsPreconnected ((g ∘ β) '' Ioo (0 : ℝ) 1) :=
    isPreconnected_Ioo.image (g ∘ β) (hcont.mono Ioo_subset_Icc_self)
  have hfront : Disjoint ((g ∘ β) '' Ioo (0 : ℝ) 1)
      (frontier (Ioo (m : ℝ) (m + 1))) := by
    rw [frontier_Ioo (by linarith : (m : ℝ) < m + 1)]
    refine disjoint_left.mpr ?_
    rintro y ⟨t, ht, rfl⟩ (heq | heq)
    · exact havoid t ht m heq
    · apply havoid t ht (m + 1)
      simpa only [Int.cast_add, Int.cast_one, mem_singleton_iff, Function.comp_apply] using heq
  have hsub : (g ∘ β) '' Ioo (0 : ℝ) 1 ⊆ Ioo (m : ℝ) (m + 1) := by
    obtain ⟨t, ht, hts⟩ := hsβ
    exact IsPreconnected.subset_of_disjoint_frontier hpre
      ⟨g s, ⟨t, ht, congrArg g hts⟩, hsr⟩ hfront
  have hcontcl : ContinuousOn (g ∘ β) (closure (Ioo (0 : ℝ) 1)) := by
    rw [closure_Ioo zero_ne_one]
    exact hcont
  have hcl := (show MapsTo (g ∘ β) (Ioo (0 : ℝ) 1) (Ioo (m : ℝ) (m + 1)) from
    fun t ht => hsub ⟨t, ht, rfl⟩).closure_of_continuousOn hcontcl
  rw [closure_Ioo zero_ne_one, closure_Ioo (by linarith : (m : ℝ) ≠ m + 1)] at hcl
  have hzero' : (m : ℝ) ≤ g (q i) := by
    simpa only [Function.comp_apply, hzero] using (hcl ⟨le_rfl, zero_le_one⟩).1
  have hone' : (m : ℝ) ≤ g (q j) := by
    simpa only [Function.comp_apply, hone] using (hcl ⟨zero_le_one, le_rfl⟩).1
  have hzeroeq := le_antisymm (hmax' i) hzero'
  have honeeq := le_antisymm (hmax' j) hone'
  obtain ⟨t₀, ht₀, hmaxβ⟩ := isCompact_Icc.exists_isMaxOn
    ⟨(0 : ℝ), le_rfl, zero_le_one⟩ hcont
  have hmaxlt : g (β t₀) < (m : ℝ) + 1 := by
    rcases ht₀.1.eq_or_lt with ht | ht
    · rw [← ht, hzero, hzeroeq]
      linarith
    · rcases ht₀.2.eq_or_lt with ht' | ht'
      · rw [ht', hone, honeeq]
        linarith
      · exact (hsub ⟨t₀, ⟨ht, ht'⟩, rfl⟩).2
  have hmaxgt : (m : ℝ) < g (β t₀) :=
    lt_of_lt_of_le (hsub ⟨1 / 2, by norm_num, rfl⟩).1
      (hmaxβ (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1))
  exact ⟨i, j, m, β, hij, hβ, hzero, hone, hβQ, hno, le_antisymm (hmax' i) hzero',
    le_antisymm (hmax' j) hone', fun t ht => hsub ⟨t, ht, rfl⟩, hclosed,
    g (β t₀) - m, sub_pos.mpr hmaxgt, by linarith,
    fun t ht => ⟨(hcl ht).1, by
      have hh : g (β t) ≤ g (β t₀) := hmaxβ ht
      linarith⟩⟩

theorem IsPLSphere.exists_upper_returning_arc_of_integer_height_marks {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} (hQ : IsPLSphere 1 Q) {n : ℕ} (hn : 0 < n)
    (q : Fin n → E) (hq : ∀ i, q i ∈ Q) (hinj : Function.Injective q)
    {g : E → ℝ} (hg : ContinuousOn g Q)
    (hmarks : ∀ x ∈ Q, (∃ m : ℤ, g x = m) ↔ ∃ i, q i = x)
    (hcross : ∀ i, (∃ a ∈ Q, g a < g (q i)) ∧ ∃ b ∈ Q, g (q i) < g b) :
    ∃ (i j : Fin n) (m : ℤ) (β : ℝ → E), i ≠ j ∧
      IsPLHomeomorphOn β (Icc 0 1) (β '' Icc 0 1) ∧ β 0 = q i ∧ β 1 = q j ∧
      β '' Icc 0 1 ⊆ Q ∧ (∀ k, q k ∉ β '' Ioo 0 1) ∧
      g (q i) = m ∧ g (q j) = m ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, (m : ℝ) - 1 < g (β t) ∧ g (β t) < m) ∧
      IsClosed (Q \ β '' Ioo 0 1) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        ∀ t ∈ Icc (0 : ℝ) 1, (m : ℝ) - δ ≤ g (β t) ∧ g (β t) ≤ m := by
  have hmarks' : ∀ x ∈ Q, (∃ m : ℤ, -g x = m) ↔ ∃ i, q i = x := by
    intro x hx
    rw [← hmarks x hx]
    constructor <;> rintro ⟨m, hm⟩ <;> refine ⟨-m, ?_⟩ <;> push_cast <;> linarith
  have hcross' : ∀ i, (∃ a ∈ Q, -g a < -g (q i)) ∧ ∃ b ∈ Q, -g (q i) < -g b := by
    intro i
    obtain ⟨⟨a, ha, halt⟩, b, hb, hblt⟩ := hcross i
    exact ⟨⟨b, hb, neg_lt_neg hblt⟩, a, ha, neg_lt_neg halt⟩
  obtain ⟨i, j, m, β, hij, hβ, hzero, hone, hβQ, hno, hmi, hmj, hheight,
    hclosed, δ, hδ, hδ1, hbound⟩ :=
    hQ.exists_returning_arc_of_integer_height_marks hn q hq hinj hg.neg hmarks' hcross'
  simp only [Pi.neg_apply] at hmi hmj hheight hbound
  refine ⟨i, j, -m, β, hij, hβ, hzero, hone, hβQ, hno, ?_, ?_, ?_, hclosed,
    δ, hδ, hδ1, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith
  · intro t ht
    obtain ⟨hl, hu⟩ := hheight t ht
    push_cast
    constructor <;> linarith
  · intro t ht
    obtain ⟨hl, hu⟩ := hbound t ht
    push_cast
    constructor <;> linarith

end DifferentialGeometry.Topology.PiecewiseLinear
