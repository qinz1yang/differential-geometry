import DifferentialGeometry.Geometry.Comparison.PairedPacketLocalization

set_option autoImplicit false

open Set Metric Real
open scoped Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι : Type*} [MetricSpace X]

theorem PairedComparisonPacket.injective_anchors
    {δ : ℝ} {q : X} {a b : ι → X} (hpacket : PairedComparisonPacket δ {q} a b)
    (hδ : δ < Real.pi / 2) : Function.Injective (Sum.elim a b) := by
  have hne := hpacket.not_mem_anchors (q := q) (by simp) hδ
  have hqa (i : ι) : q ≠ a i := fun h => hne (Or.inl ⟨i, h.symm⟩)
  have hab (i : ι) : a i ≠ b i := by
    intro h
    have hh := hpacket.opposite q (by simp) i
    rw [← h, dist_self, comparisonAngleNegCurvature_self (by norm_num) (dist_pos.mpr (hqa i))] at hh
    linarith [Real.pi_pos]
  have hcross (i j : ι) (hij : i ≠ j) (u v : X)
      (hu : u ∈ ({a i, b i} : Set X)) (hv : v ∈ ({a j, b j} : Set X)) : u ≠ v := by
    intro h
    have hqu : q ≠ u := by
      intro he
      rcases (by simpa only [mem_insert_iff, mem_singleton_iff] using hu : u = a i ∨ u = b i) with hh | hh
      · exact hne (Or.inl ⟨i, (he.trans hh).symm⟩)
      · exact hne (Or.inr ⟨i, (he.trans hh).symm⟩)
    have hh := hpacket.cross q (by simp) i j hij u hu v hv
    rw [← h, dist_self, comparisonAngleNegCurvature_self (by norm_num) (dist_pos.mpr hqu)] at hh
    linarith
  rintro (i | i) (j | j) h
  · have hij : i = j := by
      by_contra hn
      exact hcross i j hn (a i) (a j) (by simp) (by simp) h
    exact congrArg Sum.inl hij
  · by_cases hij : i = j
    · subst j
      exact (hab i h).elim
    · exact (hcross i j hij (a i) (b j) (by simp) (by simp) h).elim
  · by_cases hij : i = j
    · subst j
      exact (hab i h.symm).elim
    · exact (hcross i j hij (b i) (a j) (by simp) (by simp) h).elim
  · have hij : i = j := by
      by_contra hn
      exact hcross i j hn (b i) (b j) (by simp) (by simp) h
    exact congrArg Sum.inr hij

theorem PairedComparisonPacket.exists_positive_anchor_bounds [Finite ι]
    {δ : ℝ} {q : X} {a b : ι → X} (hpacket : PairedComparisonPacket δ {q} a b)
    (hδ : 0 < δ) (hδpi : δ < Real.pi / 2) :
    ∃ a₀ A : ℝ, 0 < a₀ ∧ a₀ ≤ A ∧
      ∀ j : ι ⊕ ι, dist q (Sum.elim a b j) ∈ Icc a₀ A := by
  obtain ⟨V, _, hq, _, _, a₀, A, ha₀, haA, hb⟩ :=
    (hpacket.weaken (by linarith : δ ≤ (2 * δ) / 2)).exists_uniform_nhds
      (by positivity : 0 < 2 * δ) (hpacket.not_mem_anchors (by simp) hδpi)
      (Filter.univ_mem : (univ : Set X) ∈ 𝓝 q)
  refine ⟨a₀, A, ha₀, haA, ?_⟩
  rintro (i | i)
  · exact hb q hq (a i) (Or.inl ⟨i, rfl⟩)
  · exact hb q hq (b i) (Or.inr ⟨i, rfl⟩)

end DifferentialGeometry.Geometry.Comparison.Toponogov
