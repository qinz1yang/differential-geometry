import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalLocalChart
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingRibbonAnnuli

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.image_base_arc_sides_of_signed_seam_formulas
    {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : V × ℝ → E} {Q A₀ A₁ : Set V} {R P C : Set E}
    (hg : IsCylindricalDiagram g Q R) (hends : ∀ p ∈ Q, g (p, 0) = g (p, 1))
    {u : E → M} (hu : InjOn u P) (hRP : R ⊆ P) (hA₀ : A₀ ⊆ Q) (hA₁ : A₁ ⊆ Q)
    {As Bs F D : Set M}
    (hface₀ : (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F)
    (hface₁ : (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D)
    (hcontact₀ : As ∩ u '' R = F) (hcontact₁ : Bs ∩ u '' R = D)
    {f : (ℝ × ℝ) × ℝ → E}
    (hfirst : u '' (f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) = u '' C ∩ As)
    (hsecond : u '' (f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) = u '' C ∩ Bs)
    {γ : ℝ → V} {e : ℝ} (he : e ≤ 1) (hγ : MapsTo γ (Icc (-e) e) Q)
    {ν : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hν : MapsTo ν (stdSimplexBoundary 2) (stdSimplexBoundary 2)) {a b : Bool}
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      ν (stdTriangleLoop s) = stdTriangleLoop q → ∀ t ∈ Icc (0 : ℝ) e,
        g (γ t, s) = f (t • fourSpokeModelLeaf (if a then 0 else 2), q))
    (hneg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      ν (stdTriangleLoop s) = stdTriangleLoop q → ∀ t ∈ Icc (-e) 0,
        g (γ t, s) = f ((-t) • fourSpokeModelLeaf (if b then 1 else 3), q)) :
    γ '' Icc 0 e ⊆ A₀ ∧ γ '' Icc (-e) 0 ⊆ A₁ := by
  have hbase (A : Set V) (S T : Set M) (hAQ : A ⊆ Q)
      (hface : (u ∘ g) '' (A ×ˢ Icc (0 : ℝ) 1) = T) (hcontact : S ∩ u '' R = T)
      {x : V} (hx : x ∈ Q) (hS : u (g (x, 0)) ∈ S) : x ∈ A := by
    have hxR : g (x, 0) ∈ R := hg.image_eq.subset
      (mem_image_of_mem g ⟨hx, by norm_num⟩)
    obtain ⟨⟨y, t⟩, ⟨hy, ht⟩, heq⟩ := hface.symm.subset
      (hcontact.subset ⟨hS, mem_image_of_mem u hxR⟩)
    have hyR : g (y, t) ∈ R := hg.image_eq.subset
      (mem_image_of_mem g ⟨hAQ hy, ht⟩)
    have hxy := hg.fst_eq_of_eq_of_equal_ends hends ⟨hAQ hy, ht⟩ ⟨hx, by norm_num⟩
      (hu (hRP hyR) (hRP hxR) heq)
    change y = x at hxy
    exact hxy ▸ hy
  obtain ⟨q, hq, heq⟩ := stdTriangleLoop_image.symm.subset
    (hν (stdTriangleLoop_image.subset (mem_image_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by norm_num))))
  have hribbon (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (i : Fin 4) :
      (r • fourSpokeModelLeaf i, q) ∈ section34MarkedRibbon i := by
    refine ⟨?_, hq⟩
    rw [segment_eq_image]
    exact ⟨r, hr, by simp⟩
  constructor
  · rintro _ ⟨t, ht, rfl⟩
    have ht' : t ∈ Icc (-e) e := ⟨by linarith [ht.1, ht.2], ht.2⟩
    apply hbase A₀ As F hA₀ hface₀ hcontact₀ (hγ ht')
    rw [hpos 0 (by norm_num) q hq heq.symm t ht]
    apply (hfirst.subset ?_).2
    apply mem_image_of_mem u
    apply mem_image_of_mem f
    have hm := hribbon t ⟨ht.1, ht.2.trans he⟩ (if a then 0 else 2)
    cases a
    · exact Or.inr hm
    · exact Or.inl hm
  · rintro _ ⟨t, ht, rfl⟩
    have ht' : t ∈ Icc (-e) e := ⟨ht.1, by linarith [ht.1, ht.2]⟩
    apply hbase A₁ Bs D hA₁ hface₁ hcontact₁ (hγ ht')
    rw [hneg 0 (by norm_num) q hq heq.symm t ht]
    apply (hsecond.subset ?_).2
    apply mem_image_of_mem u
    apply mem_image_of_mem f
    have hm := hribbon (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ (if b then 1 else 3)
    cases b
    · exact Or.inr hm
    · exact Or.inl hm

end DifferentialGeometry.Topology.PiecewiseLinear
