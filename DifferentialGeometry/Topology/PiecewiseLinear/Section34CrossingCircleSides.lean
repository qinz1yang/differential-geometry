import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCircleCore
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularSideAlternation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem HasPLCrossingAt.opposite_bicollar_sides
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S X J W : Set E} [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {ρ : E × ℝ → E} {x : E} (hcross : HasPLCrossingAt S (frontier X) x)
    (hJ : IsPreconnected J) (hxJ : x ∈ J) (hWS : W ⊆ S)
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W)
    (hρ₀ : ∀ y ∈ J, ρ (y, 0) = y) (hW : W ∈ 𝓝[S] x)
    (htrace : W ∩ frontier X = J) (hX : IsClosed X) (hreg : closure (interior X) = X) :
    (ρ '' (J ×ˢ Ico (-1 : ℝ) 0) ⊆ interior X ∧
      ρ '' (J ×ˢ Ioc (0 : ℝ) 1) ⊆ Xᶜ) ∨
    (ρ '' (J ×ˢ Ico (-1 : ℝ) 0) ⊆ Xᶜ ∧
      ρ '' (J ×ˢ Ioc (0 : ℝ) 1) ⊆ interior X) := by
  have hneg : J ×ˢ Ico (-1 : ℝ) 0 ⊆ J ×ˢ Icc (-1 : ℝ) 1 :=
    fun _ hy => ⟨hy.1, hy.2.1, hy.2.2.le.trans zero_le_one⟩
  have hpos : J ×ˢ Ioc (0 : ℝ) 1 ⊆ J ×ˢ Icc (-1 : ℝ) 1 :=
    fun _ hy => ⟨hy.1, (by norm_num : (-1 : ℝ) ≤ 0).trans hy.2.1.le, hy.2.2⟩
  have hnegc : IsPreconnected (ρ '' (J ×ˢ Ico (-1 : ℝ) 0)) :=
    (hJ.prod (convex_Ico (-1 : ℝ) 0).isPreconnected).image ρ
      (hρ.isPiecewiseAffineOn.continuousOn.mono hneg)
  have hposc : IsPreconnected (ρ '' (J ×ˢ Ioc (0 : ℝ) 1)) :=
    (hJ.prod (convex_Ioc (0 : ℝ) 1).isPreconnected).image ρ
      (hρ.isPiecewiseAffineOn.continuousOn.mono hpos)
  have hdis (I : Set ℝ) (hI : I ⊆ Icc (-1 : ℝ) 1) (hzero : 0 ∉ I) :
      Disjoint (ρ '' (J ×ˢ I)) (frontier X) := by
    refine disjoint_left.mpr ?_
    rintro z ⟨y, hy, rfl⟩ hz
    have hyJ := htrace.subset ⟨hρ.bijOn.mapsTo ⟨hy.1, hI hy.2⟩, hz⟩
    have heq := hρ.bijOn.injOn ⟨hy.1, hI hy.2⟩
      ⟨hyJ, by norm_num⟩ (hρ₀ _ hyJ).symm
    have ht : y.2 = 0 := congrArg Prod.snd heq
    exact hzero (ht ▸ hy.2)
  have hdneg := hdis (Ico (-1 : ℝ) 0)
    (fun _ hy => ⟨hy.1, hy.2.le.trans zero_le_one⟩) (by simp)
  have hdpos := hdis (Ioc (0 : ℝ) 1)
    (fun _ hy => ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans hy.1.le, hy.2⟩) (by simp)
  have hxS := hWS (htrace.symm.subset hxJ).1
  have hball := fun N hN => exists_ball_chart_of_mem_nhdsWithin_surface
    hxS (self_mem_nhdsWithin : S ∈ 𝓝[S] x) (N := N) hN
  have hxfront := (htrace.symm.subset hxJ).2
  have hxreg : x ∈ closure (interior X) := hreg.symm ▸ hX.frontier_subset hxfront
  obtain ⟨V₀, -, -, -, hin⟩ := hcross.exists_connected_inside_slice hball hX hxreg
  let Y := (interior X)ᶜ
  have hY : IsClosed Y := isOpen_interior.isClosed_compl
  have hYi : interior Y = Xᶜ := by
    change interior (interior X)ᶜ = Xᶜ
    rw [interior_compl, hreg]
  have hYf : frontier Y = frontier X := by
    change frontier (interior X)ᶜ = frontier X
    rw [frontier_compl, frontier, hreg, interior_interior, frontier, hX.closure_eq]
  have hxY : x ∈ closure (interior Y) := by
    rw [hYi, closure_compl]
    exact hxfront.2
  obtain ⟨V₁, -, -, -, hout⟩ :=
    (hYf.symm ▸ hcross).exists_connected_inside_slice hball hY hxY
  have hout' : x ∈ closure (S \ X) := by
    simpa only [hYi, Set.sdiff_eq] using (closure_mono inter_subset_left hout)
  obtain ⟨V, hV, hVW⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hW
  apply DifferentialGeometry.Topology.opposite_sides_of_local_two_set_cover
    hX hnegc hposc hdneg hdpos (closure_mono inter_subset_left hin) hout' hV
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hρ.bijOn.surjOn (hVW hy)
  rcases lt_trichotomy z.2 0 with ht | ht | ht
  · exact Or.inl (Or.inl ⟨z, ⟨hz.1, hz.2.1, ht⟩, rfl⟩)
  · apply Or.inr
    have heq : ρ z = z.1 := by
      have hz0 : z = (z.1, (0 : ℝ)) := Prod.ext rfl ht
      rw [hz0, hρ₀ z.1 hz.1]
    exact heq.symm ▸ (htrace.symm.subset hz.1).2
  · exact Or.inl (Or.inr ⟨z, ⟨hz.1, ht, hz.2.2⟩, rfl⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
