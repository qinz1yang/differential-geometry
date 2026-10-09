import DifferentialGeometry.Geometry.Comparison.PairedDistanceOpenness

set_option autoImplicit false

open Set Metric Filter Real
open scoped Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι : Type*} [MetricSpace X]

theorem continuousAt_comparisonAngleNegCurvature_one_dist {q a b : X}
    (ha : q ≠ a) (hb : q ≠ b) :
    ContinuousAt (fun z => comparisonAngleNegCurvature 1 (dist z a) (dist z b) (dist a b)) q := by
  simp only [comparisonAngleNegCurvature, one_ne_zero, sqrt_one, one_mul]
  apply ContinuousAt.arccos
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact (mul_pos (sinh_pos_iff.mpr (dist_pos.mpr ha))
      (sinh_pos_iff.mpr (dist_pos.mpr hb))).ne'

theorem PairedComparisonPacket.exists_uniform_nhds [Finite ι]
    {δ : ℝ} {q : X} {Ω : Set X} {a b : ι → X}
    (hpacket : PairedComparisonPacket (δ / 2) {q} a b) (hδ : 0 < δ)
    (hne : q ∉ range a ∪ range b) (hΩ : Ω ∈ 𝓝 q) :
    ∃ V : Set X, IsOpen V ∧ q ∈ V ∧ V ⊆ Ω ∧ PairedComparisonPacket δ V a b ∧
      ∃ a₀ A : ℝ, 0 < a₀ ∧ a₀ ≤ A ∧
        ∀ z ∈ V, ∀ c ∈ range a ∪ range b, dist z c ∈ Icc a₀ A := by
  let := Fintype.ofFinite ι
  let S := range a ∪ range b
  have hS : S.Finite := (finite_range a).union (finite_range b)
  have hqS : q ∈ Sᶜ := hne
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp hS.isClosed.isOpen_compl q hqS
  obtain ⟨M, hM⟩ := (hS.image (fun c => dist q c)).bddAbove
  have hdistlo (c : X) (hc : c ∈ S) : ε ≤ dist q c := by
    by_contra h
    exact hεS (by rw [mem_ball, dist_comm]; exact lt_of_not_ge h) hc
  have hdisthi (c : X) (hc : c ∈ S) : dist q c ≤ M := hM ⟨c, hc, rfl⟩
  have hne' (c : X) (hc : c ∈ S) : q ≠ c := by rintro rfl; exact hne hc
  have haS (i : ι) : a i ∈ S := Or.inl ⟨i, rfl⟩
  have hbS (i : ι) : b i ∈ S := Or.inr ⟨i, rfl⟩
  have hpairS (i : ι) (u : X) (hu : u ∈ ({a i, b i} : Set X)) : u ∈ S := by
    rcases (by simpa only [mem_insert_iff, mem_singleton_iff] using hu : u = a i ∨ u = b i) with rfl | rfl
    · exact haS i
    · exact hbS i
  have hopp : ∀ᶠ z in 𝓝 q, ∀ i, Real.pi - δ <
      comparisonAngleNegCurvature 1 (dist z (a i)) (dist z (b i)) (dist (a i) (b i)) := by
    apply eventually_all.mpr
    intro i
    exact (tendsto_order.mp (continuousAt_comparisonAngleNegCurvature_one_dist
      (hne' _ (haS i)) (hne' _ (hbS i)))).1 _
      (by linarith [hpacket.opposite q (by simp) i])
  have hcross : ∀ᶠ z in 𝓝 q, ∀ i j, ∀ u ∈ ({a i, b i} : Set X),
      ∀ v ∈ ({a j, b j} : Set X), i ≠ j → Real.pi / 2 - δ <
        comparisonAngleNegCurvature 1 (dist z u) (dist z v) (dist u v) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    apply (eventually_all_finite ((finite_singleton (b i)).insert (a i))).mpr
    intro u hu
    apply (eventually_all_finite ((finite_singleton (b j)).insert (a j))).mpr
    intro v hv
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => False.elim (h hij))
    have hh := (tendsto_order.mp (continuousAt_comparisonAngleNegCurvature_one_dist
      (hne' _ (hpairS i u hu)) (hne' _ (hpairS j v hv)))).1 (Real.pi / 2 - δ)
      (by linarith [hpacket.cross q (by simp) i j hij u hu v hv])
    filter_upwards [hh] with z hz
    exact fun _ => hz
  have hgood : {z | z ∈ Ω ∧ dist z q < ε / 2 ∧ dist z q < 1 ∧
      PairedComparisonPacket δ {z} a b} ∈ 𝓝 q := by
    filter_upwards [hΩ, ball_mem_nhds q (half_pos hε), ball_mem_nhds q zero_lt_one,
      hopp, hcross] with z hzΩ hzε hz1 hzo hzc
    refine ⟨hzΩ, hzε, hz1, ?_⟩
    constructor
    · intro z' hz' i
      have heq : z' = z := mem_singleton_iff.mp hz'
      subst z'
      exact hzo i
    · intro z' hz' i j hij u hu v hv
      have heq : z' = z := mem_singleton_iff.mp hz'
      subst z'
      exact hzc i j u hu v hv hij
  obtain ⟨ρ, hρ, hρgood⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨ball q ρ, isOpen_ball, mem_ball_self hρ, fun z hz => (hρgood hz).1, ?_,
    ε / 2, max (ε / 2) (M + 1), half_pos hε, le_max_left _ _, ?_⟩
  · constructor
    · intro z hz i
      exact (hρgood hz).2.2.2.opposite z (by simp) i
    · intro z hz i j hij u hu v hv
      exact (hρgood hz).2.2.2.cross z (by simp) i j hij u hu v hv
  · intro z hz c hc
    have hzε := (hρgood hz).2.1
    have hz1 := (hρgood hz).2.2.1
    constructor
    · have htri := dist_triangle q z c
      rw [dist_comm q z] at htri
      linarith [hdistlo c hc]
    · apply le_trans _ (le_max_right _ _)
      linarith [dist_triangle z q c, hdisthi c hc]

theorem PairedComparisonPacket.not_mem_anchors {δ : ℝ} {V : Set X} {a b : ι → X}
    (hpacket : PairedComparisonPacket δ V a b) {q : X} (hq : q ∈ V)
    (hδ : δ < Real.pi / 2) : q ∉ range a ∪ range b := by
  rintro (⟨i, hi⟩ | ⟨i, hi⟩)
  · have h := hpacket.opposite q hq i
    simp only [hi, dist_self, comparisonAngleNegCurvature, one_ne_zero, sqrt_one,
      one_mul, sinh_zero, zero_mul, div_zero, arccos_zero, ite_false] at h
    linarith
  · have h := hpacket.opposite q hq i
    simp only [hi, dist_self, comparisonAngleNegCurvature, one_ne_zero, sqrt_one,
      one_mul, sinh_zero, mul_zero, div_zero, arccos_zero, ite_false] at h
    linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
