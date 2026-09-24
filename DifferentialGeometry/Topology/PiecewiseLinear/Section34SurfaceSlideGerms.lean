import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem image_sdiff_eq_of_mapsTo_of_eqOn {X : Type*} {S N J : Set X} {H : X → X}
    (hJ : J ⊆ S) (hN : MapsTo H N N) (hfix : EqOn H id (S \ N)) :
    (H '' J) \ N = J \ N := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hxN⟩
    have hyN : y ∉ N := fun h => hxN (hN h)
    rw [hfix ⟨hJ hy, hyN⟩]
    exact ⟨hy, hyN⟩
  · rintro ⟨hx, hxN⟩
    exact ⟨⟨x, hx, hfix ⟨hJ hx, hxN⟩⟩, hxN⟩

theorem eventually_mem_image_iff_of_closed_support
    {X : Type*} [TopologicalSpace X] {S N J : Set X} {H : X → X}
    (hJ : J ⊆ S) (hN : IsClosed N) (hHN : MapsTo H N N)
    (hfix : EqOn H id (closure (S \ N))) {x : X} (hxN : x ∉ N) :
    ∀ᶠ y in 𝓝 x, y ∈ H '' J ↔ y ∈ J := by
  have heq := image_sdiff_eq_of_mapsTo_of_eqOn hJ hHN (hfix.mono subset_closure)
  filter_upwards [hN.isOpen_compl.mem_nhds hxN] with y hyN
  exact ⟨fun hy => (heq.subset ⟨hy, hyN⟩).1,
    fun hy => (heq.symm.subset ⟨hy, hyN⟩).1⟩

theorem eventually_mem_image_iff_at_remaining_trace
    {X : Type*} [TopologicalSpace X] {S N J L R : Set X} {H : X → X}
    (hJ : J ⊆ S) (hN : IsClosed N) (hHN : MapsTo H N N)
    (hfix : EqOn H id (closure (S \ N)))
    (hNR : N ∩ (J ∩ L) ⊆ R) (htrace : H '' J ∩ L = (J ∩ L) \ R)
    {x : X} (hx : x ∈ H '' J ∩ L) : ∀ᶠ y in 𝓝 x, y ∈ H '' J ↔ y ∈ J := by
  have hxold := htrace.subset hx
  exact eventually_mem_image_iff_of_closed_support hJ hN hHN hfix
    (fun hxN => hxold.2 (hNR ⟨hxN, hxold.1⟩))

theorem eventually_mem_pullback_image_iff_of_closed_support
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S N J : Set X} {H : X → X} (hJ : J ⊆ S) (hN : IsClosed N)
    (hHN : MapsTo H N N) (hfix : EqOn H id (closure (S \ N)))
    {f : Y → X} {x : Y} (A : Set Y) (hf : ContinuousWithinAt f A x)
    (hxN : f x ∉ N) :
    ∀ᶠ y in 𝓝 x, y ∈ A ∩ f ⁻¹' (H '' J) ↔ y ∈ A ∩ f ⁻¹' J := by
  have heq := hf.tendsto.eventually
    (eventually_mem_image_iff_of_closed_support hJ hN hHN hfix hxN)
  filter_upwards [eventually_nhdsWithin_iff.mp heq] with y hy
  exact and_congr_right fun hyA => hy hyA

theorem mem_closure_inter_pullback_image_iff_of_closed_support
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S N J : Set X} {H : X → X} (hJ : J ⊆ S) (hN : IsClosed N)
    (hHN : MapsTo H N N) (hfix : EqOn H id (closure (S \ N)))
    {f : Y → X} {x : Y} (A : Set Y) (hf : ContinuousWithinAt f A x)
    (hxN : f x ∉ N) :
    x ∈ closure (A ∩ f ⁻¹' (H '' J)) ↔ x ∈ closure (A ∩ f ⁻¹' J) := by
  rw [mem_closure_iff_frequently, mem_closure_iff_frequently]
  have hgerm :=
    eventually_mem_pullback_image_iff_of_closed_support hJ hN hHN hfix A hf hxN
  constructor
  · intro h
    exact (h.and_eventually hgerm).mono fun _ hy => hy.2.mp hy.1
  · intro h
    exact (h.and_eventually hgerm).mono fun _ hy => hy.2.mpr hy.1

theorem OpenPartialHomeomorph.exists_smaller_axis_chart_of_curve_germ
    {X : Type*} [TopologicalSpace X] {S J J' L : Set X}
    (e : OpenPartialHomeomorph (ℝ × ℝ) S) {ε : ℝ} (hε : 0 < ε)
    (hsource : Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source)
    (hfirst : ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε, (e p : X) ∈ J ↔ p.1 = 0)
    (hsecond : ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε, (e p : X) ∈ L ↔ p.2 = 0)
    (hgerm : ∀ᶠ y in 𝓝 (e (0, 0) : X), y ∈ J' ↔ y ∈ J) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ Ioo (-η) η ×ˢ Ioo (-η) η ⊆ e.source ∧
      ∀ p ∈ Ioo (-η) η ×ˢ Ioo (-η) η,
        ((e p : X) ∈ J' ↔ p.1 = 0) ∧ ((e p : X) ∈ L ↔ p.2 = 0) := by
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hezero : (0, 0) ∈ e.source := hsource ⟨hzero, hzero⟩
  have he : ContinuousAt (fun p => (e p : X)) (0, 0) :=
    continuous_subtype_val.continuousAt.comp
      (e.continuousOn.continuousAt (e.open_source.mem_nhds hezero))
  obtain ⟨ρ, hρ, hρgerm⟩ := Metric.mem_nhds_iff.mp (he.tendsto.eventually hgerm)
  let η := min ε ρ
  have hη : 0 < η := lt_min hε hρ
  have hηε : η ≤ ε := min_le_left _ _
  have hηρ : η ≤ ρ := min_le_right _ _
  have hsub : Ioo (-η) η ×ˢ Ioo (-η) η ⊆ Ioo (-ε) ε ×ˢ Ioo (-ε) ε := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], lt_of_lt_of_le hp.1.2 hηε⟩,
      ⟨by linarith [hp.2.1], lt_of_lt_of_le hp.2.2 hηε⟩⟩
  refine ⟨η, hη, hηε, hsub.trans hsource, ?_⟩
  intro p hp
  have hpg : (e p : X) ∈ J' ↔ (e p : X) ∈ J := by
    apply hρgerm
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff, abs_lt]
    exact ⟨⟨by linarith [hp.1.1], lt_of_lt_of_le hp.1.2 hηρ⟩,
      ⟨by linarith [hp.2.1], lt_of_lt_of_le hp.2.2 hηρ⟩⟩
  exact ⟨hpg.trans (hfirst p (hsub hp)), hsecond p (hsub hp)⟩

theorem OpenPartialHomeomorph.exists_remaining_axis_chart_of_supported_slide
    {X : Type*} [TopologicalSpace X] {S N J L R : Set X} {H : X → X}
    (hJ : J ⊆ S) (hN : IsClosed N) (hHN : MapsTo H N N)
    (hfix : EqOn H id (closure (S \ N)))
    (hNR : N ∩ (J ∩ L) ⊆ R) (htrace : H '' J ∩ L = (J ∩ L) \ R)
    (e : OpenPartialHomeomorph (ℝ × ℝ) S) {ε : ℝ} (hε : 0 < ε)
    (hsource : Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source)
    (hfirst : ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε, (e p : X) ∈ J ↔ p.1 = 0)
    (hsecond : ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε, (e p : X) ∈ L ↔ p.2 = 0)
    (hremain : (e (0, 0) : X) ∈ H '' J ∩ L) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ Ioo (-η) η ×ˢ Ioo (-η) η ⊆ e.source ∧
      ∀ p ∈ Ioo (-η) η ×ˢ Ioo (-η) η,
        ((e p : X) ∈ H '' J ↔ p.1 = 0) ∧ ((e p : X) ∈ L ↔ p.2 = 0) := by
  exact OpenPartialHomeomorph.exists_smaller_axis_chart_of_curve_germ e
    hε hsource hfirst hsecond
    (eventually_mem_image_iff_at_remaining_trace hJ hN hHN hfix hNR htrace hremain)

end DifferentialGeometry.Topology.PiecewiseLinear
