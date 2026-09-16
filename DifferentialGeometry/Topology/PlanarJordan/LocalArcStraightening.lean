import DifferentialGeometry.Topology.PlanarJordan.VertexFan
import DifferentialGeometry.Topology.Homeomorph.UniformGluing
import DifferentialGeometry.Topology.DiscreteNeighborhoods
import DifferentialGeometry.Topology.Embedding.RealParameter
import DifferentialGeometry.Topology.Order.DiscreteRange
import Mathlib.Analysis.SpecificLimits.Basic

open Set Topology

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies

theorem exists_homeomorph_polygonal_subarcs_at_interior
    {f : ℝ → Plane} (hf : ContinuousOn f unitInterval) (hi : InjOn f unitInterval)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {N : Set Plane} (hN : N ∈ 𝓝 (f t)) :
    ∃ (r a b : ℝ) (e : Plane ≃ₜ Plane), 0 < r ∧ Plane.closedSquare (f t) r ⊆ N ∧
      0 < a ∧ a < t ∧ t < b ∧ b < 1 ∧
      f '' Icc a b ⊆ Plane.closedSquare (f t) r ∧
      IsPolygonal (e '' (f '' Icc a t)) ∧ IsPolygonal (e '' (f '' Icc t b)) ∧
      e (f t) = f t ∧ EqOn e id (Plane.openSquare (f t) r)ᶜ ∧
      ∀ x, dist (e x) x ≤ Metric.diam (Plane.closedSquare (f t) r) := by
  have htI : t ∈ unitInterval := ⟨ht.1.le, ht.2.le⟩
  have hleft : IsArcBetween (f '' Icc 0 t) (f 0) (f t) := by
    simpa only [uIcc_of_le ht.1.le] using
      isArcBetween_subarc_of_injOn_I hf hi zero_mem_I htI ht.1.ne
  have hright : IsArcBetween (f '' Icc t 1) (f t) (f 1) := by
    simpa only [uIcc_of_le ht.2.le] using
      isArcBetween_subarc_of_injOn_I hf hi htI one_mem_I ht.2.ne
  have hZ : IsClosed ({f 0, f 1} : Set Plane) :=
    ((finite_singleton (f 1)).insert (f 0)).isClosed
  have htZ : f t ∉ ({f 0, f 1} : Set Plane) := by
    rintro (h0 | h1)
    · exact ht.1.ne' (hi htI zero_mem_I h0)
    · exact ht.2.ne (hi htI one_mem_I h1)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem hN (hZ.isOpen_compl.mem_nhds htZ))
  let r := ρ / 2
  have hr : 0 < r := half_pos hρ
  have hsub : Plane.closedSquare (f t) r ⊆ N \ {f 0, f 1} :=
    (Plane.closedSquare_subset_ball hρ).trans hball
  have hcenter : f t ∈ Plane.openSquare (f t) r := by
    change Plane.supDist (f t) (f t) < r
    simpa only [Plane.supDist_self] using hr
  have h0 : f 0 ∉ Plane.openSquare (f t) r := fun hx =>
    (hsub (Plane.openSquare_subset_closedSquare _ _ hx)).2 (Or.inl rfl)
  have h1 : f 1 ∉ Plane.openSquare (f t) r := fun hx =>
    (hsub (Plane.openSquare_subset_closedSquare _ _ hx)).2 (Or.inr rfl)
  obtain ⟨A, hAsub, p, hp, hA, hAI⟩ := exists_initial_arc_to_frontier hleft.reverse
    (Plane.isOpen_openSquare _ _) hcenter h0
  obtain ⟨B, hBsub, q, hq, hB, hBI⟩ := exists_initial_arc_to_frontier hright
    (Plane.isOpen_openSquare _ _) hcenter h1
  have hmeet : ∀ x ∈ A, x ∈ B → x = f t := by
    intro x hx hy
    obtain ⟨u, hu, rfl⟩ := hAsub hx
    obtain ⟨v, hv, heq⟩ := hBsub hy
    have huv := hi ⟨hu.1, hu.2.trans ht.2.le⟩ ⟨ht.1.le.trans hv.1, hv.2⟩ heq.symm
    exact congrArg f (le_antisymm hu.2 (huv.symm ▸ hv.1))
  have hpC := Plane.frontier_openSquare_subset _ _ hp
  have hqC := Plane.frontier_openSquare_subset _ _ hq
  obtain ⟨e, heA, heB, het, hefix, hedist⟩ :=
    exists_homeomorph_image_two_vertex_arcs_radial hr hpC hqC hA hB hmeet hAI hBI
  obtain ⟨a, ha, hfa⟩ := hAsub hA.right_mem
  obtain ⟨b, hb, hfb⟩ := hBsub hB.right_mem
  have hpnot : p ∉ Plane.openSquare (f t) r := by
    simpa only [(Plane.isOpen_openSquare _ _).interior_eq] using hp.2
  have hqnot : q ∉ Plane.openSquare (f t) r := by
    simpa only [(Plane.isOpen_openSquare _ _).interior_eq] using hq.2
  have hat : a < t := lt_of_le_of_ne ha.2 fun h => hpnot ((hfa.symm.trans (congrArg f h)).symm ▸ hcenter)
  have htb : t < b := lt_of_le_of_ne hb.1 fun h => hqnot ((hfb.symm.trans (congrArg f h.symm)).symm ▸ hcenter)
  have ha0 : 0 < a := lt_of_le_of_ne ha.1 fun h =>
    (hsub ((Plane.isClosed_closedSquare _ _).frontier_subset hpC)).2 (Or.inl (hfa.symm.trans (congrArg f h.symm)))
  have hb1 : b < 1 := lt_of_le_of_ne hb.2 fun h =>
    (hsub ((Plane.isClosed_closedSquare _ _).frontier_subset hqC)).2 (Or.inr (hfb.symm.trans (congrArg f h)))
  have hAsmall : IsArcBetween (f '' Icc a t) p (f t) := by
    simpa only [uIcc_of_le hat.le, hfa] using
      isArcBetween_subarc_of_injOn_I hf hi ⟨ha.1, ha.2.trans ht.2.le⟩ htI hat.ne
  have hBsmall : IsArcBetween (f '' Icc t b) (f t) q := by
    simpa only [uIcc_of_le htb.le, hfb] using
      isArcBetween_subarc_of_injOn_I hf hi htI ⟨ht.1.le.trans hb.1, hb.2⟩ htb.ne
  have hAeq : A = f '' Icc a t := hA.reverse.eq_of_subset_arc hAsmall hleft hAsub
    (image_mono (Icc_subset_Icc_left ha.1))
  have hBeq : B = f '' Icc t b := hB.eq_of_subset_arc hBsmall hright hBsub
    (image_mono (Icc_subset_Icc_right hb.2))
  have hAC : A ⊆ Plane.closedSquare (f t) r := by
    intro x hx
    by_cases hxp : x = p
    · exact hxp ▸ (Plane.isClosed_closedSquare _ _).frontier_subset hpC
    · exact Plane.openSquare_subset_closedSquare _ _ (hAI ⟨hx, hxp⟩)
  have hBC : B ⊆ Plane.closedSquare (f t) r := by
    intro x hx
    by_cases hxq : x = q
    · exact hxq ▸ (Plane.isClosed_closedSquare _ _).frontier_subset hqC
    · exact Plane.openSquare_subset_closedSquare _ _ (hBI ⟨hx, hxq⟩)
  refine ⟨r, a, b, e, hr, hsub.trans inter_subset_left, ha0, hat, htb, hb1, ?_, ?_, ?_, het, hefix, hedist⟩
  · rw [← Icc_union_Icc_eq_Icc hat.le htb.le, image_union, ← hAeq, ← hBeq]
    exact union_subset hAC hBC
  · rw [← hAeq, heA]
    exact isPolygonal_segment _ _
  · rw [← hBeq, heB]
    exact isPolygonal_segment _ _


theorem exists_homeomorph_polygonal_subarcs_of_isDiscrete
    {ι : Type*} {f : ℝ → Plane} (hf : ContinuousOn f unitInterval) (hi : InjOn f unitInterval)
    {t : ι → ℝ} (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) (hinj : Function.Injective t)
    (hdiscrete : IsDiscrete (range fun i => f (t i)))
    {N : ι → Set Plane} (hN : ∀ i, N i ∈ 𝓝 (f (t i)))
    {δ : ι → ℝ} (hδ : ∀ i, 0 < δ i) (hδlim : Filter.Tendsto δ Filter.cofinite (𝓝 0)) :
    ∃ (r a b : ι → ℝ) (e : Plane ≃ₜ Plane),
      (∀ i, 0 < r i ∧ Plane.closedSquare (f (t i)) (r i) ⊆ N i ∧
        0 < a i ∧ a i < t i ∧ t i < b i ∧ b i < 1 ∧
        f '' Icc (a i) (b i) ⊆ Plane.closedSquare (f (t i)) (r i) ∧
        IsPolygonal (e '' (f '' Icc (a i) (t i))) ∧
        IsPolygonal (e '' (f '' Icc (t i) (b i))) ∧ e (f (t i)) = f (t i)) ∧
      (Pairwise fun i j => Disjoint (Plane.closedSquare (f (t i)) (r i))
        (Plane.closedSquare (f (t j)) (r j))) ∧
      Filter.Tendsto (fun i => Metric.diam (Plane.closedSquare (f (t i)) (r i)))
        Filter.cofinite (𝓝 0) ∧
      EqOn e id (⋃ i, Plane.openSquare (f (t i)) (r i))ᶜ ∧
      ∀ i x, x ∈ Plane.closedSquare (f (t i)) (r i) →
        dist (e x) x ≤ Metric.diam (Plane.closedSquare (f (t i)) (r i)) := by
  have hp : Function.Injective fun i => f (t i) := fun i j hij =>
    hinj (hi ⟨(ht i).1.le, (ht i).2.le⟩ ⟨(ht j).1.le, (ht j).2.le⟩ hij)
  obtain ⟨R, hR, hRdis⟩ := Metric.exists_pairwise_disjoint_closedBall_of_isDiscrete hp hdiscrete hN hδ
  choose r a b g hr hsub ha hat htb hb hAB hpolyA hpolyB hcenter hfix hdist using fun i =>
    exists_homeomorph_polygonal_subarcs_at_interior hf hi (ht i)
      (Metric.ball_mem_nhds (f (t i)) (hR i).1)
  let C (i : ι) := Plane.closedSquare (f (t i)) (r i)
  have hCB (i : ι) : C i ⊆ Metric.closedBall (f (t i)) (R i) :=
    (hsub i).trans Metric.ball_subset_closedBall
  have hCN (i : ι) : C i ⊆ N i := (hCB i).trans (hR i).2.2
  have hdis : Pairwise fun i j => Disjoint (C i) (C j) :=
    fun i j hij => (hRdis hij).mono (hCB i) (hCB j)
  have hdiam (i : ι) : Metric.diam (C i) ≤ 2 * δ i :=
    (Metric.diam_le_of_subset_closedBall (hR i).1.le (hCB i)).trans
      (mul_le_mul_of_nonneg_left (hR i).2.1.le (by norm_num))
  have hcontract : Filter.Tendsto (fun i => Metric.diam (C i)) Filter.cofinite (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using hδlim.const_mul 2) (fun _ => Metric.diam_nonneg) hdiam
  have hgfix (i : ι) : EqOn (g i) id (C i)ᶜ :=
    (hfix i).mono (compl_subset_compl.mpr (Plane.openSquare_subset_closedSquare _ _))
  obtain ⟨e, he, hefix⟩ := Homeomorph.exists_gluing_of_pairwise_disjoint_of_tendsto_diam g C
    hgfix hdis (fun i => Plane.isBounded_closedSquare _ _) hcontract
  refine ⟨r, a, b, e, ?_, hdis, hcontract, ?_, ?_⟩
  · intro i
    refine ⟨hr i, hCN i, ha i, hat i, htb i, hb i, hAB i, ?_, ?_, ?_⟩
    · rw [((he i).mono ((image_mono (Icc_subset_Icc_right (htb i).le)).trans (hAB i))).image_eq]
      exact hpolyA i
    · rw [((he i).mono ((image_mono (Icc_subset_Icc_left (hat i).le)).trans (hAB i))).image_eq]
      exact hpolyB i
    · rw [he i (Plane.mem_closedSquare_self _ (hr i).le)]
      exact hcenter i
  · intro x hx
    by_cases hxC : x ∈ ⋃ i, C i
    · obtain ⟨i, hiC⟩ := mem_iUnion.mp hxC
      rw [he i hiC]
      exact hfix i (fun h => hx (mem_iUnion.mpr ⟨i, h⟩))
    · exact hefix hxC
  · intro i x hx
    rw [he i hx]
    exact hdist i x


theorem exists_homeomorph_polygonal_subarcs_of_strictAnti
    {f : ℝ → Plane} (hf : ContinuousOn f unitInterval) (hi : InjOn f unitInterval)
    {t : ℕ → ℝ} (ht : ∀ n, t n ∈ Ioo (0 : ℝ) 1) (hanti : StrictAnti t)
    {N : ℕ → Set Plane} (hN : ∀ n, N n ∈ 𝓝 (f (t n))) :
    ∃ (a b : ℕ → ℝ) (e : Plane ≃ₜ Plane),
      (∀ n, 0 < a n ∧ a n < t n ∧ t n < b n ∧ b n < 1 ∧
        IsPolygonal (e '' (f '' Icc (a n) (t n))) ∧
        IsPolygonal (e '' (f '' Icc (t n) (b n))) ∧ e (f (t n)) = f (t n)) ∧
      e (f 0) = f 0 ∧ e (f 1) = f 1 ∧ EqOn e id (⋃ n, N n)ᶜ := by
  obtain ⟨g, hg, hgf⟩ := isCompact_I.exists_continuous_leftInvOn hf hi
  have htI (n : ℕ) : t n ∈ unitInterval := ⟨(ht n).1.le, (ht n).2.le⟩
  have hd : IsDiscrete (range fun n => f (t n)) := by
    apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
    rintro x ⟨n, rfl⟩
    obtain ⟨V, hV, hVt⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
      hanti.isDiscrete_range_nat (t n) (mem_range_self n)
    refine ⟨g ⁻¹' V, hV.preimage hg, Subset.antisymm ?_ ?_⟩
    · rintro x ⟨hx, m, rfl⟩
      have htm : t m ∈ V := hgf (htI m) ▸ hx
      have heq : t m = t n := hVt.subset ⟨htm, mem_range_self m⟩
      exact congrArg f heq
    · apply singleton_subset_iff.mpr
      refine ⟨?_, mem_range_self n⟩
      change g (f (t n)) ∈ V
      rw [hgf (htI n)]
      exact (hVt.symm.subset rfl).1
  let Z : Set Plane := {f 0, f 1}
  have hZ : IsClosed Z := ((finite_singleton (f 1)).insert (f 0)).isClosed
  have htZ (n : ℕ) : f (t n) ∉ Z := by
    rintro (h0 | h1)
    · exact (ht n).1.ne' (hi (htI n) zero_mem_I h0)
    · exact (ht n).2.ne (hi (htI n) one_mem_I h1)
  have hN' (n : ℕ) : N n ∩ Zᶜ ∈ 𝓝 (f (t n)) :=
    Filter.inter_mem (hN n) (hZ.isOpen_compl.mem_nhds (htZ n))
  have hδ : ∀ n : ℕ, 0 < (1 / 2 : ℝ) ^ n := fun n => pow_pos (by norm_num) n
  have hδlim : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.cofinite (𝓝 0) := by
    rw [Nat.cofinite_eq_atTop]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨r, a, b, e, hdata, _, _, hfix, _⟩ :=
    exists_homeomorph_polygonal_subarcs_of_isDiscrete hf hi ht hanti.injective hd hN' hδ hδlim
  have houtside : EqOn e id (⋃ n, N n ∩ Zᶜ)ᶜ := hfix.mono (compl_subset_compl.mpr
    (iUnion_mono fun n => (Plane.openSquare_subset_closedSquare _ _).trans (hdata n).2.1))
  have hfixZ : EqOn e id Z := by
    intro x hx
    apply houtside
    intro hmem
    obtain ⟨n, hn⟩ := mem_iUnion.mp hmem
    exact hn.2 hx
  refine ⟨a, b, e, ?_, hfixZ (Or.inl rfl), hfixZ (Or.inr rfl), ?_⟩
  · intro n
    obtain ⟨_, _, ha, hat, htb, hb, _, hpolyA, hpolyB, he⟩ := hdata n
    exact ⟨ha, hat, htb, hb, hpolyA, hpolyB, he⟩
  · exact houtside.mono (compl_subset_compl.mpr (iUnion_mono fun _ => inter_subset_left))

end DifferentialGeometry.Topology.PlanarJordan
