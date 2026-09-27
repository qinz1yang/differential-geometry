/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TetraHoles

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

open Classical in
theorem Section34CutFrame.clawBall_holes
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) {a b c d : Ea} (htabcd : t = {a, b, c, d})
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {ea eb ec ed : Section34EdgeIndex 𝒦 𝒦'}
    (hea₁ : a ∈ ea.1) (hea₂ : convexHull ℝ (ea.1 : Set Ea) ⊆ segment ℝ a d)
    (hea : ∀ e : Section34EdgeIndex 𝒦 𝒦', a ∈ e.1 →
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ a d → e = ea)
    (heb₁ : b ∈ eb.1) (heb₂ : convexHull ℝ (eb.1 : Set Ea) ⊆ segment ℝ b c)
    (heb : ∀ e : Section34EdgeIndex 𝒦 𝒦', b ∈ e.1 →
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ b c → e = eb)
    (hec₁ : c ∈ ec.1) (hec₂ : convexHull ℝ (ec.1 : Set Ea) ⊆ segment ℝ c a)
    (hec : ∀ e : Section34EdgeIndex 𝒦 𝒦', c ∈ e.1 →
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ c a → e = ec)
    (hed₁ : d ∈ ed.1) (hed₂ : convexHull ℝ (ed.1 : Set Ea) ⊆ segment ℝ d b)
    (hed : ∀ e : Section34EdgeIndex 𝒦 𝒦', d ∈ e.1 →
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ d b → e = ed)
    {chart : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
    (hchart : chart ∈ (plGroupoid 3).maximalAtlas M₂)
    (hVc : ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 t →
      section34VertexBallImage src f₁ w ⊆ chart.source) :
    (∀ k l : Fin 4, k ≠ l → ![ec, eb, ed, ea] k ≠ ![ec, eb, ed, ea] l) ∧
      section34ClawBall (section34VertexBallImage src f₁) a b c d ∩
          section34ClawBall (section34VertexBallImage src f₁) d c a b =
        ⋃ k, section34SplitDiskImage src f₁ (![ec, eb, ed, ea] k) ∧
      (∀ k, section34SplitDiskImage src f₁ (![ec, eb, ed, ea] k) ⊆
        frontier (section34ClawBall (section34VertexBallImage src f₁) a b c d)) ∧
      (∀ k, section34SplitDiskImage src f₁ (![ec, eb, ed, ea] k) ⊆
        frontier (section34ClawBall (section34VertexBallImage src f₁) d c a b)) ∧
      ∀ k, section34SplitDiskImage src f₁ (![ec, eb, ed, ea] k) \
          section34SplitDiskImage srcBd f₁ (![ec, eb, ed, ea] k) ⊆
        interior (section34ClawBall (section34VertexBallImage src f₁) a b c d ∪
          section34ClawBall (section34VertexBallImage src f₁) d c a b) := by
  have ha : a ∈ t := by rw [htabcd]; simp
  have hb : b ∈ t := by rw [htabcd]; simp
  have hc : c ∈ t := by rw [htabcd]; simp
  have hd : d ∈ t := by rw [htabcd]; simp
  have hVce : ∀ {e : Section34EdgeIndex 𝒦 𝒦'} {u v : Ea}, u ∈ t → v ∈ t →
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ u v →
      ∀ w : Section34VertexIndex 𝒦 𝒦', w.1 ⊆ e.1 →
        section34VertexBallImage src f₁ w ⊆ chart.source := by
    intro e u v hu hv he w hw
    apply hVc w
    intro z hz
    exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ hu)
      (subset_convexHull ℝ _ hv) (he (subset_convexHull ℝ _ (hw hz)))
  have hseg : ∀ {e : Section34EdgeIndex 𝒦 𝒦'} {u v x : Ea},
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ u v → x ∈ e.1 → x ∈ segment ℝ u v :=
    fun he hx => he (subset_convexHull ℝ _ hx)
  have hsymm : ∀ {u v x : Ea}, x ∈ segment ℝ u v → x ∈ segment ℝ v u := fun h => by
    rwa [segment_symm]
  obtain ⟨wa, wa', pa, hwa, hwa', hpae, hpaa, hwae, hwa'e⟩ :=
    exists_section34VertexIndex_pair_of_mem_edgeIndex ea hea₁
  obtain ⟨wb, wb', pb, hwb, hwb', hpbe, hpbb, hwbe, hwb'e⟩ :=
    exists_section34VertexIndex_pair_of_mem_edgeIndex eb heb₁
  obtain ⟨wc, wc', pc, hwc, hwc', hpce, hpcc, hwce, hwc'e⟩ :=
    exists_section34VertexIndex_pair_of_mem_edgeIndex ec hec₁
  obtain ⟨wd, wd', pd, hwd, hwd', hpde, hpdd, hwde, hwd'e⟩ :=
    exists_section34VertexIndex_pair_of_mem_edgeIndex ed hed₁
  have hA := hcut.splitDiskImage_subset_frontier_clawBall hf₁ ht ha hb hc hd hab hac had hbc
    hbd hcd hwa hwa' (Or.inl (left_mem_segment ℝ a b))
    (Or.inr (Or.inl ⟨hsymm (hseg hea₂ hpae), hpaa⟩)) hwae hwa'e hchart (hVce ha hd hea₂)
  have hB := hcut.splitDiskImage_subset_frontier_clawBall hf₁ ht ha hb hc hd hab hac had hbc
    hbd hcd hwb hwb' (Or.inl (right_mem_segment ℝ a b))
    (Or.inr (Or.inr ⟨hsymm (hseg heb₂ hpbe), hpbb⟩)) hwbe hwb'e hchart (hVce hb hc heb₂)
  have hC := hcut.splitDiskImage_subset_frontier_clawBall hf₁ ht ha hb hc hd hab hac had hbc
    hbd hcd hwc' hwc (Or.inr (Or.inl ⟨hsymm (hseg hec₂ hpce), hpcc⟩))
    (Or.inl (right_mem_segment ℝ d c)) hwc'e hwce hchart (hVce hc ha hec₂)
  have hD := hcut.splitDiskImage_subset_frontier_clawBall hf₁ ht ha hb hc hd hab hac had hbc
    hbd hcd hwd' hwd (Or.inr (Or.inr ⟨hsymm (hseg hed₂ hpde), hpdd⟩))
    (Or.inl (left_mem_segment ℝ d c)) hwd'e hwde hchart (hVce hd hb hed₂)
  have hone : ∀ {u v w x : Ea}, u ∈ t → v ∈ t → w ∈ t → v ≠ w → x ∈ segment ℝ u v →
      x ∈ segment ℝ u w → x = u := fun hu hv hw hvw h h' =>
    mem_singleton_iff.mp (SimplicialComplex.segment_inter_segment_subset_singleton ht hu hv hw hvw
      ⟨h, h'⟩)
  have hab' : ea ≠ eb := by
    intro h
    have h1 : a ∈ segment ℝ b c := hseg heb₂ (by rw [← h]; exact hea₁)
    exact Set.disjoint_left.mp (SimplicialComplex.disjoint_segment_segment ht ha hd hb hc hab hac
      hbd.symm hcd.symm) (left_mem_segment ℝ a d) h1
  have hac' : ea ≠ ec := by
    intro h
    have h1 : c ∈ segment ℝ a d := hseg hea₂ (by rw [h]; exact hec₁)
    exact hac (hone ha hd hc hcd.symm h1 (right_mem_segment ℝ a c)).symm
  have had' : ea ≠ ed := by
    intro h
    have h1 : a ∈ segment ℝ d b := hseg hed₂ (by rw [← h]; exact hea₁)
    exact had (hone hd hb ha hab.symm h1 (right_mem_segment ℝ d a))
  have hbc' : eb ≠ ec := by
    intro h
    have h1 : b ∈ segment ℝ c a := hseg hec₂ (by rw [← h]; exact heb₁)
    exact hbc (hone hc ha hb hab h1 (right_mem_segment ℝ c b))
  have hbd' : eb ≠ ed := by
    intro h
    have h1 : d ∈ segment ℝ b c := hseg heb₂ (by rw [h]; exact hed₁)
    exact hbd (hone hb hc hd hcd h1 (right_mem_segment ℝ b d)).symm
  have hcd' : ec ≠ ed := by
    intro h
    have h1 : c ∈ segment ℝ d b := hseg hed₂ (by rw [← h]; exact hec₁)
    exact Set.disjoint_left.mp (SimplicialComplex.disjoint_segment_segment ht hc ha hd hb hcd
      hbc.symm had hab) (left_mem_segment ℝ c a) h1
  have hsubU := hcut.clawBall_inter_clawBall hf₁ ht htabcd hab hac had hbc hbd hcd hea heb hec hed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k l hkl
    fin_cases k <;> fin_cases l
    all_goals first
      | exact absurd rfl hkl
      | exact hbc' | exact hbc'.symm | exact hcd' | exact hcd'.symm | exact hac' | exact hac'.symm
      | exact hbd' | exact hbd'.symm | exact hab' | exact hab'.symm | exact had' | exact had'.symm
  · apply Subset.antisymm
    · intro z hz
      rcases hsubU hz with ((h | h) | h) | h
      · exact mem_iUnion.mpr ⟨3, h⟩
      · exact mem_iUnion.mpr ⟨1, h⟩
      · exact mem_iUnion.mpr ⟨0, h⟩
      · exact mem_iUnion.mpr ⟨2, h⟩
    · refine iUnion_subset fun k => ?_
      fin_cases k
      exacts [hC.1, hB.1, hD.1, hA.1]
  · intro k
    fin_cases k
    exacts [hC.2.1, hB.2.1, hD.2.1, hA.2.1]
  · intro k
    fin_cases k
    exacts [hC.2.2.1, hB.2.2.1, hD.2.2.1, hA.2.2.1]
  · intro k
    fin_cases k
    exacts [hC.2.2.2, hB.2.2.2, hD.2.2.2, hA.2.2.2]

end DifferentialGeometry.Topology.PiecewiseLinear
