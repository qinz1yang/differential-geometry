/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeTraces
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleBicollar

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLCrossingAt.mem_closure_sides {A X : Set E} {x : E}
    (hcross : HasPLCrossingAt A (frontier X) x)
    (hA : ∀ N ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (A ∩ N) ∧ g c = x)
    (hXc : IsClosed X) (hX : x ∈ closure (interior X)) :
    x ∈ closure (A ∩ interior X) ∧ x ∈ closure (A \ X) := by
  obtain ⟨U, φ, ρ, hU, hxU, -, hφ, hφx, hloc⟩ := hcross.exists_sideChart hA hXc hX
  have hpoints : ∀ V, IsOpen V → x ∈ V →
      (V ∩ (A ∩ interior X)).Nonempty ∧ (V ∩ (A \ X)).Nonempty := by
    intro V hV hxV
    have himage : IsOpen (φ '' (U ∩ V)) :=
      hφ.isOpen_image_of_isOpen Metric.isOpen_ball (hU.inter hV) inter_subset_left
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp himage 0 ⟨x, ⟨hxU, hxV⟩, hφx⟩
    have hpt : ∀ t : ℝ, |t| < r → ∃ y ∈ U ∩ V, φ y = (0, t, 0) := by
      intro t ht
      apply hball
      rw [mem_ball_zero_iff, Prod.norm_def, Prod.norm_def]
      simpa using max_lt hr (max_lt ht hr)
    obtain ⟨a, ha, hφa⟩ := hpt (r / 2) (by rw [abs_of_pos (by positivity)]; linarith)
    obtain ⟨b, hb, hφb⟩ := hpt (-(r / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
    have haA : a ∈ A := (hloc a ha.1).1.mpr (by rw [hφa])
    have hbA : b ∈ A := (hloc b hb.1).1.mpr (by rw [hφb])
    have haX : a ∈ X := (hloc a ha.1).2.2.mpr (by rw [hφa]; positivity)
    have haI : a ∈ interior X := (mem_interior_iff_notMem_frontier haX).mpr (by
      intro haf
      have hz := (hloc a ha.1).2.1.mp haf
      rw [hφa] at hz
      change r / 2 = 0 at hz
      linarith)
    have hbX : b ∉ X := by
      intro hbX
      have hz := (hloc b hb.1).2.2.mp hbX
      rw [hφb] at hz
      change 0 ≤ -(r / 2) at hz
      linarith
    exact ⟨⟨a, ha.2, haA, haI⟩, ⟨b, hb.2, hbA, hbX⟩⟩
  exact ⟨mem_closure_iff.mpr fun V hV hxV => (hpoints V hV hxV).1,
    mem_closure_iff.mpr fun V hV hxV => (hpoints V hV hxV).2⟩

theorem IsPLHomeomorphOn.exists_half_collar_of_closed_cover {J W A B : Set E}
    {ρ : E × ℝ → E} (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W)
    (hJ : IsPLSphere 1 J) (hfix : ∀ x ∈ J, ρ (x, 0) = x)
    (hA : IsClosed A) (hB : IsClosed B) (hcoverAB : W ⊆ A ∪ B)
    (hmeet : W ∩ (A ∩ B) = J) (ha : (W \ B).Nonempty) (hb : (W \ A).Nonempty) :
    ∃ σ : E × ℝ → E, IsPLHomeomorphOn σ (J ×ˢ Icc (0 : ℝ) 1) (W ∩ B) ∧
      ∀ x ∈ J, σ (x, 0) = x := by
  have hJA : J ⊆ A := hmeet.symm.subset.trans (inter_subset_right.trans inter_subset_left)
  have hJB : J ⊆ B := hmeet.symm.subset.trans (inter_subset_right.trans inter_subset_right)
  have hJW : J ⊆ W := hmeet.symm.subset.trans inter_subset_left
  have hcoord : ∀ z ∈ J ×ˢ Icc (-1 : ℝ) 1, ρ z ∈ J ↔ z.2 = 0 := by
    intro z hz
    constructor
    · intro hJρ
      have heq : z = (ρ z, 0) := hρ.bijOn.injOn hz ⟨hJρ, by norm_num⟩
        (hfix _ hJρ).symm
      exact congrArg Prod.snd heq
    · intro hz0
      rcases z with ⟨z, t⟩
      change t = 0 at hz0
      subst t
      rw [hfix z hz.1]
      exact hz.1
  let P : Set E := ρ '' (J ×ˢ Ioc (0 : ℝ) 1)
  let N : Set E := ρ '' (J ×ˢ Ico (-1 : ℝ) 0)
  have hpos : J ×ˢ Ioc (0 : ℝ) 1 ⊆ J ×ˢ Icc (-1 : ℝ) 1 :=
    fun z hz => ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
  have hneg : J ×ˢ Ico (-1 : ℝ) 0 ⊆ J ×ˢ Icc (-1 : ℝ) 1 :=
    fun z hz => ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
  have hPW : P ⊆ W := (image_mono hpos).trans hρ.image_eq.subset
  have hNW : N ⊆ W := (image_mono hneg).trans hρ.image_eq.subset
  have hPc : IsPreconnected P := (hJ.isConnected.isPreconnected.prod isPreconnected_Ioc).image
    ρ (hρ.isPiecewiseAffineOn.continuousOn.mono hpos)
  have hNc : IsPreconnected N := (hJ.isConnected.isPreconnected.prod isPreconnected_Ico).image
    ρ (hρ.isPiecewiseAffineOn.continuousOn.mono hneg)
  have hPJ : Disjoint P J := by
    apply disjoint_left.mpr
    rintro _ ⟨z, hz, rfl⟩ hJρ
    exact (ne_of_gt hz.2.1) ((hcoord z (hpos hz)).mp hJρ)
  have hNJ : Disjoint N J := by
    apply disjoint_left.mpr
    rintro _ ⟨z, hz, rfl⟩ hJρ
    exact (ne_of_lt hz.2.2) ((hcoord z (hneg hz)).mp hJρ)
  have hside : ∀ Y : Set E, Y ⊆ W → IsPreconnected Y → Disjoint Y J → Y ⊆ A ∨ Y ⊆ B := by
    intro Y hYW hY hYJ
    apply isPreconnected_iff_subset_of_disjoint_closed.mp hY A B hA hB
      (hYW.trans hcoverAB)
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyY, hyAB⟩
    exact disjoint_left.mp hYJ hyY (hmeet.subset ⟨hYW hyY, hyAB⟩)
  have hcover : ∀ y ∈ W, y ∈ J ∨ y ∈ P ∨ y ∈ N := by
    intro y hy
    obtain ⟨⟨z, t⟩, hzt, rfl⟩ := hρ.image_eq.symm.subset hy
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · exact Or.inr (Or.inr ⟨(z, t), ⟨hzt.1, hzt.2.1, ht⟩, rfl⟩)
    · exact Or.inl ((hfix z hzt.1).symm ▸ hzt.1)
    · exact Or.inr (Or.inl ⟨(z, t), ⟨hzt.1, ht, hzt.2.2⟩, rfl⟩)
  have hcases : (P ⊆ B ∧ N ⊆ A) ∨ (N ⊆ B ∧ P ⊆ A) := by
    rcases hside P hPW hPc hPJ with hp | hp <;>
      rcases hside N hNW hNc hNJ with hn | hn
    · obtain ⟨y, hyW, hyA⟩ := hb
      rcases hcover y hyW with hy | hy | hy
      · exact (hyA (hJA hy)).elim
      · exact (hyA (hp hy)).elim
      · exact (hyA (hn hy)).elim
    · exact Or.inr ⟨hn, hp⟩
    · exact Or.inl ⟨hp, hn⟩
    · obtain ⟨y, hyW, hyB⟩ := ha
      rcases hcover y hyW with hy | hy | hy
      · exact (hyB (hJB hy)).elim
      · exact (hyB (hp hy)).elim
      · exact (hyB (hn hy)).elim
  have hclip : ∀ Y Z : Set E, Y ⊆ W → Y ⊆ B → Z ⊆ A → Disjoint Z J →
      (∀ y ∈ W, y ∈ J ∨ y ∈ Y ∨ y ∈ Z) → W ∩ B = J ∪ Y := by
    intro Y Z hYW hY hZ hZJ hcov
    refine Subset.antisymm ?_ ?_
    · rintro y ⟨hyW, hyB⟩
      rcases hcov y hyW with hy | hy | hy
      · exact Or.inl hy
      · exact Or.inr hy
      · exact (disjoint_left.mp hZJ hy (hmeet.subset ⟨hyW, hZ hy, hyB⟩)).elim
    · rintro y (hy | hy)
      · exact ⟨hJW hy, hJB hy⟩
      · exact ⟨hYW hy, hY hy⟩
  have hposimage : ρ '' (J ×ˢ Icc (0 : ℝ) 1) = J ∪ P := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      rcases eq_or_lt_of_le ht.1 with ht0 | ht0
      · change 0 = t at ht0
        subst t
        exact Or.inl ((hfix z hz).symm ▸ hz)
      · exact Or.inr ⟨(z, t), ⟨hz, ht0, ht.2⟩, rfl⟩
    · rintro y (hy | ⟨z, hz, rfl⟩)
      · exact ⟨(y, 0), ⟨hy, le_rfl, zero_le_one⟩, hfix y hy⟩
      · exact ⟨z, ⟨hz.1, hz.2.1.le, hz.2.2⟩, rfl⟩
  have hnegimage : ρ '' (J ×ˢ Icc (-1 : ℝ) 0) = J ∪ N := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      rcases lt_or_eq_of_le ht.2 with ht0 | rfl
      · exact Or.inr ⟨(z, t), ⟨hz, ht.1, ht0⟩, rfl⟩
      · exact Or.inl ((hfix z hz).symm ▸ hz)
    · rintro y (hy | ⟨z, hz, rfl⟩)
      · exact ⟨(y, 0), ⟨hy, by norm_num⟩, hfix y hy⟩
      · exact ⟨z, ⟨hz.1, hz.2.1, hz.2.2.le⟩, rfl⟩
  rcases hcases with ⟨hPB, hNA⟩ | ⟨hNB, hPA⟩
  · refine ⟨ρ, ?_, hfix⟩
    rw [hclip P N hPW hPB hNA hNJ hcover, ← hposimage]
    exact hρ.restrict (hJ.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)
      (prod_mono subset_rfl (Icc_subset_Icc (by norm_num) le_rfl))
  · have hswap : ∀ y ∈ W, y ∈ J ∨ y ∈ N ∨ y ∈ P := by
      intro y hy
      rcases hcover y hy with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    have hreflect : IsPLHomeomorphOn (fun t : ℝ => -t) (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 0) := by
      apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
        (isPiecewiseAffineOn_of_affine_of_isHPolytope
          (-LinearMap.id : ℝ →ₗ[ℝ] ℝ).toAffineMap isHPolytope_Icc)
      refine ⟨?_, fun _ _ _ _ h => neg_injective h, ?_⟩
      · intro t ht
        change -1 ≤ -t ∧ -t ≤ 0
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      · intro t ht
        exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, neg_neg t⟩
    let σ := ρ ∘ Prod.map (id : E → E) (fun t : ℝ => -t)
    refine ⟨σ, ?_, fun x hx => by simpa [σ] using hfix x hx⟩
    rw [hclip N P hNW hNB hPA hPJ hswap, ← hnegimage]
    exact (hJ.isPolyhedron.isPLHomeomorphOn_id.prodMap hreflect).trans
      (hρ.restrict (hJ.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)
        (prod_mono subset_rfl (Icc_subset_Icc le_rfl (by norm_num))))

theorem IsPLHomeomorphOn.exists_half_collar_of_frontier {J W X : Set E}
    {ρ : E × ℝ → E} (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W)
    (hJ : IsPLSphere 1 J) (hfix : ∀ x ∈ J, ρ (x, 0) = x)
    (hX : IsClosed X) (hfront : W ∩ frontier X = J)
    (hint : (W ∩ interior X).Nonempty) (hext : (W \ X).Nonempty) :
    ∃ σ : E × ℝ → E, IsPLHomeomorphOn σ (J ×ˢ Icc (0 : ℝ) 1) (W \ interior X) ∧
      ∀ x ∈ J, σ (x, 0) = x := by
  have hcover : W ⊆ X ∪ (interior X)ᶜ := fun y _ => by
    by_cases hy : y ∈ X
    · exact Or.inl hy
    · exact Or.inr fun hyI => hy (interior_subset hyI)
  have hmeet : W ∩ (X ∩ (interior X)ᶜ) = J := by
    simpa only [hX.frontier_eq, sdiff_eq] using hfront
  obtain ⟨σ, hσ, hσ0⟩ := hρ.exists_half_collar_of_closed_cover hJ hfix hX
    isOpen_interior.isClosed_compl hcover hmeet (by simpa only [sdiff_compl] using hint) hext
  exact ⟨σ, hσ, hσ0⟩

end DifferentialGeometry.Topology.PiecewiseLinear
