import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingRibbonAnnuli
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalCancellation
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarGluing
import DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_signed_crossing_ribbon_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C : Set E} (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ x ∈ spliceSquare, f (x, 0) = f (x, 1))
    (i j : Fin 4) (hij : i ≠ j) :
    ∃ ρ : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn ρ (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1)
        (f '' section34MarkedRibbon j ∪ f '' section34MarkedRibbon i) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        ρ (stdTriangleLoop s, t) = f (t • fourSpokeModelLeaf i, s)) ∧
      (∀ t ∈ Icc (-1 : ℝ) 0, ∀ s ∈ Icc (0 : ℝ) 1,
        ρ (stdTriangleLoop s, t) = f ((-t) • fourSpokeModelLeaf j, s)) ∧
      (∀ Q ⊆ Icc (0 : ℝ) 1, ρ '' (stdSimplexBoundary 2 ×ˢ Q) =
        f '' (((fun t : ℝ => t • fourSpokeModelLeaf i) '' Q) ×ˢ Icc (0 : ℝ) 1)) ∧
      ∀ Q ⊆ Icc (-1 : ℝ) 0, ρ '' (stdSimplexBoundary 2 ×ˢ Q) =
        f '' (((fun t : ℝ => (-t) • fourSpokeModelLeaf j) '' Q) ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨τ, hτ, hτf, hτcore, hτzero, -, -⟩ :=
    hf.exists_crossing_ribbon_annulus_charts hends
  have hS := isPolyhedron_stdSimplexBoundary_two
  have hn : IsPLHomeomorphOn (fun t : ℝ => -t) (Icc (-1 : ℝ) 0) (Icc (0 : ℝ) 1) := by
    simpa only [neg_one_mul, add_zero] using
      isPLHomeomorphOn_mul_add_Icc_of_neg (m := (-1 : ℝ)) (c := 0)
        (a := -1) (b := 0) (a' := 0) (b' := 1) (by norm_num) (by norm_num) (by norm_num)
  have hleft := (hS.isPLHomeomorphOn_id.prodMap hn).trans (hτ j)
  have hinter : f '' section34MarkedRibbon j ∩ f '' section34MarkedRibbon i =
      f '' section34MarkedAxis := by
    rw [section34MarkedRibbon, section34MarkedRibbon,
      hf.inter_images_base_regions hends (segment_zero_fourSpokeModelLeaf_subset j)
        (segment_zero_fourSpokeModelLeaf_subset i), segment_zero_fourSpokeModelLeaf_inter hij.symm]
    rfl
  have hagree : EqOn (τ j ∘ Prod.map id (fun t : ℝ => -t)) (τ i)
      ((stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 0) ∩
        (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) := by
    rintro ⟨z, t⟩ ht
    have ht0 : t = 0 := le_antisymm ht.1.2.2 ht.2.2.1
    subst t
    simpa using hτcore j i z ht.1.1
  have hsurj : SurjOn (τ j ∘ Prod.map id (fun t : ℝ => -t))
      ((stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 0) ∩
        (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
      (f '' section34MarkedRibbon j ∩ f '' section34MarkedRibbon i) := by
    intro y hy
    obtain ⟨⟨z, t⟩, ⟨hz, ht⟩, heq⟩ := (hτzero j).symm.subset (hinter.subset hy)
    have ht0 : t = 0 := ht
    subst t
    exact ⟨(z, 0), ⟨⟨hz, by norm_num⟩, ⟨hz, by norm_num⟩⟩, by simpa using heq⟩
  obtain ⟨ρ, hρ, hρneg, hρpos⟩ := exists_isPLHomeomorphOn_union
    (hS.prod isHPolytope_Icc.isPolyhedron) (hS.prod isHPolytope_Icc.isPolyhedron)
    hleft (hτ i) hagree hsurj
  have hunion : (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 0) ∪
      (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
      stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1 := by
    rw [← prod_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
  rw [hunion] at hρ
  have hp (t) (ht : t ∈ Icc (0 : ℝ) 1) (s) (hs : s ∈ Icc (0 : ℝ) 1) :
      ρ (stdTriangleLoop s, t) = f (t • fourSpokeModelLeaf i, s) :=
    (hρpos ⟨stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop hs), ht⟩).trans
      (hτf i t ht s hs)
  have hm (t) (ht : t ∈ Icc (-1 : ℝ) 0) (s) (hs : s ∈ Icc (0 : ℝ) 1) :
      ρ (stdTriangleLoop s, t) = f ((-t) • fourSpokeModelLeaf j, s) :=
    (hρneg ⟨stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop hs), ht⟩).trans
      (hτf j (-t) (hn.bijOn.mapsTo ht) s hs)
  have hlevels {V : Set ℝ} {γ : ℝ → ℝ × ℝ}
      (hγ : ∀ t ∈ V, ∀ s ∈ Icc (0 : ℝ) 1, ρ (stdTriangleLoop s, t) = f (γ t, s)) :
      ρ '' (stdSimplexBoundary 2 ×ˢ V) = f '' ((γ '' V) ×ˢ Icc (0 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro y ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      obtain ⟨s, hs, rfl⟩ := stdTriangleLoop_image.symm.subset hz
      exact ⟨(γ t, s), ⟨mem_image_of_mem γ ht, hs⟩, (hγ t ht s hs).symm⟩
    · rintro y ⟨⟨p, s⟩, ⟨⟨t, ht, rfl⟩, hs⟩, rfl⟩
      exact ⟨(stdTriangleLoop s, t),
        ⟨stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop hs), ht⟩, hγ t ht s hs⟩
  exact ⟨ρ, hρ, hp, hm, fun Q hQ => hlevels (fun t ht => hp t (hQ ht)),
    fun Q hQ => hlevels (fun t ht => hm t (hQ ht))⟩

end DifferentialGeometry.Topology.PiecewiseLinear
