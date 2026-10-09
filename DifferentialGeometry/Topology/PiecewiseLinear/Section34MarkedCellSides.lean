import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCircleSides
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeChain

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def section34MarkedRibbon (i : Fin 4) : Set ((ℝ × ℝ) × ℝ) :=
  segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1

def section34MarkedRibbonCore (i : Fin 4) : Set ((ℝ × ℝ) × ℝ) :=
  (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) \ {0}) ×ˢ Icc (0 : ℝ) 1

def section34MarkedAxis : Set ((ℝ × ℝ) × ℝ) := {0} ×ˢ Icc (0 : ℝ) 1

theorem section34_marked_ribbon_subset_cylinder (i : Fin 4) :
    section34MarkedRibbon i ⊆ spliceCylinder :=
  prod_mono (segment_zero_fourSpokeModelLeaf_subset i) subset_rfl

theorem section34_marked_ribbon_core_subset (i : Fin 4) :
    section34MarkedRibbonCore i ⊆ section34MarkedRibbon i := prod_mono sdiff_subset subset_rfl

theorem section34_marked_axis_subset_ribbon (i : Fin 4) :
    section34MarkedAxis ⊆ section34MarkedRibbon i :=
  prod_mono (singleton_subset_iff.mpr (left_mem_segment ℝ _ _)) subset_rfl

theorem section34_marked_ribbon_inter {i j : Fin 4} (hij : i ≠ j) :
    section34MarkedRibbon i ∩ section34MarkedRibbon j = section34MarkedAxis := by
  rw [section34MarkedRibbon, section34MarkedRibbon, prod_inter_prod,
    segment_zero_fourSpokeModelLeaf_inter hij, inter_self]
  rfl

theorem section34_marked_ribbon_core_disjoint {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (section34MarkedRibbonCore i) (section34MarkedRibbon j) := by
  refine disjoint_left.mpr fun x hx hy => ?_
  have h := section34_marked_ribbon_inter hij ▸
    (show x ∈ section34MarkedRibbon i ∩ section34MarkedRibbon j from
      ⟨section34_marked_ribbon_core_subset i hx, hy⟩)
  exact hx.1.2 h.1

theorem isPreconnected_section34_marked_ribbon_core (i : Fin 4) :
    IsPreconnected (section34MarkedRibbonCore i) := by
  let f : ℝ × ℝ → (ℝ × ℝ) × ℝ := fun p => (p.1 • fourSpokeModelLeaf i, p.2)
  have hf : Continuous f := by fun_prop
  have heq : f '' (Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) =
      section34MarkedRibbonCore i := by
    apply Subset.antisymm
    · rintro x ⟨p, hp, rfl⟩
      refine ⟨⟨?_, ?_⟩, hp.2⟩
      · rw [segment_eq_image]
        exact ⟨p.1, ⟨hp.1.1.le, hp.1.2⟩, by simp [f]⟩
      · exact fun h => (smul_ne_zero hp.1.1.ne' (fourSpokeModelLeaf_ne_zero i)) h
    · rintro ⟨v, t⟩ ⟨⟨hv, hv0⟩, ht⟩
      rw [segment_eq_image] at hv
      obtain ⟨r, hr, rfl⟩ := hv
      simp only [smul_zero, zero_add] at hv0 ⊢
      refine ⟨(r, t), ⟨⟨lt_of_le_of_ne hr.1 ?_, hr.2⟩, ht⟩, rfl⟩
      intro h
      change 0 = r at h
      exact hv0 (by rw [← h, zero_smul]; rfl)
  rw [← heq]
  exact (isPreconnected_Ioc.prod isPreconnected_Icc).image f hf.continuousOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLCrossingAt.opposite_marked_cell_ribbon_sides
    {S X C : Set E}
    {G : (ℝ × ℝ) × ℝ → E} (hG : IsPLHomeomorphOn G spliceCylinder C) (i : Fin 4)
    (hS : G '' (section34MarkedRibbon i ∪ section34MarkedRibbon (i + 2)) = C ∩ S)
    (hF : G '' (section34MarkedRibbon (i + 1) ∪ section34MarkedRibbon (i + 3)) =
      C ∩ frontier X)
    (hc : G (0, 1 / 2) ∈ interior C)
    (hcross : HasPLCrossingAt S (frontier X) (G (0, 1 / 2)))
    (hball : ∀ N ∈ 𝓝 (G (0, 1 / 2)),
      ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
        0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ InjOn g (Metric.ball c r) ∧
          MapsTo g (Metric.ball c r) (S ∩ N) ∧ g c = G (0, 1 / 2))
    (hX : IsClosed X) (hreg : closure (interior X) = X) :
    (G '' section34MarkedRibbonCore i ⊆ interior X ∧
      G '' section34MarkedRibbonCore (i + 2) ⊆ Xᶜ) ∨
    (G '' section34MarkedRibbonCore i ⊆ Xᶜ ∧
      G '' section34MarkedRibbonCore (i + 2) ⊆ interior X) := by
  have hcore (j : Fin 4) : section34MarkedRibbonCore j ⊆ spliceCylinder :=
    (section34_marked_ribbon_core_subset j).trans (section34_marked_ribbon_subset_cylinder j)
  have hconn (j : Fin 4) : IsPreconnected (G '' section34MarkedRibbonCore j) :=
    (isPreconnected_section34_marked_ribbon_core j).image G
      (hG.isPiecewiseAffineOn.continuousOn.mono (hcore j))
  have hdis (j : Fin 4) (hj₁ : j ≠ i + 1) (hj₃ : j ≠ i + 3) :
      Disjoint (G '' section34MarkedRibbonCore j) (frontier X) := by
    refine disjoint_left.mpr ?_
    rintro x ⟨p, hp, rfl⟩ hx
    obtain ⟨q, hq, heq⟩ := hF.symm.subset ⟨hG.bijOn.mapsTo (hcore j hp), hx⟩
    have hqC : q ∈ spliceCylinder := (union_subset
      (section34_marked_ribbon_subset_cylinder _) (section34_marked_ribbon_subset_cylinder _)) hq
    have hqp := hG.bijOn.injOn hqC (hcore j hp) heq
    subst q
    rcases hq with hq | hq
    · exact disjoint_left.mp (section34_marked_ribbon_core_disjoint hj₁) hp hq
    · exact disjoint_left.mp (section34_marked_ribbon_core_disjoint hj₃) hp hq
  have h0axis : ((0 : ℝ × ℝ), (1 / 2 : ℝ)) ∈ section34MarkedAxis := by
    exact ⟨rfl, by norm_num, by norm_num⟩
  have hcF : G (0, 1 / 2) ∈ frontier X := (hF ▸ mem_image_of_mem G
    (Or.inl (section34_marked_axis_subset_ribbon (i + 1) h0axis))).2
  obtain ⟨V₀, -, -, -, hin⟩ := hcross.exists_connected_inside_slice hball hX
    (hreg.symm ▸ hX.frontier_subset hcF)
  let Y := (interior X)ᶜ
  have hY : IsClosed Y := isOpen_interior.isClosed_compl
  have hYi : interior Y = Xᶜ := by rw [interior_compl, hreg]
  have hYf : frontier Y = frontier X := by
    rw [frontier_compl, frontier, hreg, interior_interior, frontier, hX.closure_eq]
  have hcY : G (0, 1 / 2) ∈ closure (interior Y) := by
    rw [hYi, closure_compl]
    exact hcF.2
  obtain ⟨V₁, -, -, -, hout⟩ :=
    (hYf.symm ▸ hcross).exists_connected_inside_slice hball hY hcY
  have hout' : G (0, 1 / 2) ∈ closure (S \ X) := by
    simpa only [hYi, Set.sdiff_eq] using (closure_mono inter_subset_left hout)
  apply DifferentialGeometry.Topology.opposite_sides_of_local_two_set_cover hX
    (hconn i) (hconn (i + 2))
    (hdis i (by fin_cases i <;> decide) (by fin_cases i <;> decide))
    (hdis (i + 2) (by fin_cases i <;> decide) (by fin_cases i <;> decide))
    (closure_mono inter_subset_left hin) hout' (isOpen_interior.mem_nhds hc)
  intro x hx
  obtain ⟨p, hp, rfl⟩ := hS.symm.subset ⟨interior_subset hx.1, hx.2⟩
  by_cases hp0 : p.1 = 0
  · apply Or.inr
    have hpI : p.2 ∈ Icc (0 : ℝ) 1 := hp.elim (fun h => h.2) (fun h => h.2)
    exact (hF ▸ mem_image_of_mem G
      (Or.inl (section34_marked_axis_subset_ribbon (i + 1) ⟨hp0, hpI⟩))).2
  · rcases hp with hp | hp
    · exact Or.inl (Or.inl ⟨p, ⟨⟨hp.1, hp0⟩, hp.2⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨p, ⟨⟨hp.1, hp0⟩, hp.2⟩, rfl⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
