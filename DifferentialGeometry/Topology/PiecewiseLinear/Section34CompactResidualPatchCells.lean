/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactPatchEnumeration
import DifferentialGeometry.Topology.PiecewiseLinear.CircleClosedCover

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}
  {fblBd tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set E3}
  {tgtA tgtABd : Section34CompactArcIndex K K' → Set E3}
  {tgtP : Section34CompactMarkIndex K K' → Set E3}

theorem Section34CompactCutFrame.exists_residualPatch_boundary
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34CompactSimplexIndex K 4} {R : Set E3} (hR : IsPLBall 3 R)
    (hDR : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
      tgtD s ⊆ frontier R)
    (hfr : frontier R ⊆ (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34CompactVertexIndex K K')
      (_ : Section34Incident w.1 t.1), section34CompactVertexBallImage src f₁ w))
    (hio : ∀ a : Section34CompactArcIndex K K', Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34CompactEdgeIndex K K', y ∉ section34CompactSplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∈ R ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∉ R)
    (h7 : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 t.1 →
      R ∩ section34CompactVertexBallImage src f₁ w = ∅)
    {w : Section34CompactVertexIndex K K'} (hw : Section34Incident w.1 t.1) :
    ∃ q : (Fin 3 → ℝ) → E3, IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        (R ∩ section34CompactVertexBallImage src f₁ w) ∧
      q '' stdSimplexBoundary 2 =
        (⋃ (a : Section34CompactArcIndex K K')
          (_ : a.1.2 = w ∧ Section34Incident a.1.1.1 t.1), tgtA a) ∪
        ⋃ (i : Section34CompactEdgeArcIndex K K') (_ : i.1.1 = t ∧ w.1 ⊆ i.1.2.1),
          R ∩ section34CompactSplitDiskImage src f₁ i.1.2 := by
  obtain ⟨m, sK, eK, hsK, hwsK, hweK, hsinj, heinj, hinc, hscomp, hecomp⟩ :=
    hcut.exists_patchEnum t hw
  obtain ⟨⟨q, hq, hqb⟩, -⟩ := hcut.exists_residualPatch hf₁ hdisk hR hDR hfr hint hio h7 hsK hwsK
    hweK hsinj heinj hinc hscomp hecomp
  have heKt : ∀ k, Section34Incident (eK k).1 t.1 := fun k z hz =>
    convexHull_min (hsK k) (convex_convexHull ℝ _) (((hinc k k).mpr (Or.inl rfl)) hz)
  refine ⟨q, hq, ?_⟩
  rw [hqb]
  congr 1
  · ext y
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨k, hy⟩
      exact ⟨⟨(sK k, w), hwsK k⟩, ⟨rfl, hsK k⟩, hy⟩
    · rintro ⟨a, ⟨haw, hat⟩, hy⟩
      have hwa : Section34Incident w.1 a.1.1.1 := by
        rw [← haw]
        exact a.2
      obtain ⟨k, hk⟩ := hscomp a.1.1 hat hwa
      have ha : a = ⟨(sK k, w), hwsK k⟩ := Subtype.ext (Prod.ext hk haw)
      rw [ha] at hy
      exact ⟨k, hy⟩
  · ext y
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨k, hy⟩
      exact ⟨⟨(t, eK k), heKt k⟩, ⟨rfl, hweK k⟩, hy⟩
    · rintro ⟨i, ⟨hit, hwi⟩, hy⟩
      have hie : Section34Incident i.1.2.1 t.1 := by
        rw [← hit]
        exact i.2
      obtain ⟨k, hk⟩ := hecomp i.1.2 hie hwi
      rw [hk] at hy
      exact ⟨k, hy⟩

theorem Section34CompactCutFrame.exists_residualEdgeArc
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34CompactSimplexIndex K 4} {R : Set E3} (hR : IsPLBall 3 R)
    (hDR : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
      tgtD s ⊆ frontier R)
    (hfr : frontier R ⊆ (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34CompactVertexIndex K K')
      (_ : Section34Incident w.1 t.1), section34CompactVertexBallImage src f₁ w))
    (hio : ∀ a : Section34CompactArcIndex K K', Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34CompactEdgeIndex K K', y ∉ section34CompactSplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∈ R ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∉ R)
    (h7 : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 t.1 →
      R ∩ section34CompactVertexBallImage src f₁ w = ∅)
    {e : Section34CompactEdgeIndex K K'} (he : Section34Incident e.1 t.1) :
    ∃ γ : ℝ → E3,
      IsPLHomeomorphOn γ (Icc 0 1) (R ∩ section34CompactSplitDiskImage src f₁ e) ∧
      ({γ 0, γ 1} : Set E3) = ⋃ (p : Section34CompactMarkIndex K K')
        (_ : p.1.2 = e ∧ Section34Incident p.1.1.1 t.1), tgtP p := by
  obtain ⟨w, w', -, hew, -⟩ := hcut.splitDiskImage_eq_inter hf₁ e
  have hwe : w.1 ⊆ e.1 := by
    have h : (w.1 : Set E3) ⊆ e.1 := by
      rw [hew]
      exact subset_union_left
    exact Finset.coe_subset.mp h
  have hw : Section34Incident w.1 t.1 := fun z hz => he (hwe hz)
  obtain ⟨m, sK, eK, hsK, hwsK, hweK, hsinj, heinj, hinc, hscomp, hecomp⟩ :=
    hcut.exists_patchEnum t hw
  obtain ⟨-, hI⟩ := hcut.exists_residualPatch hf₁ hdisk hR hDR hfr hint hio h7 hsK hwsK
    hweK hsinj heinj hinc hscomp hecomp
  obtain ⟨k, rfl⟩ := hecomp e he hwe
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := hI k
  refine ⟨γ, hγ, ?_⟩
  have hmark := hdisk.faceDisk_inter_splitDiskImage_eq hcut hf₁
  apply Subset.antisymm
  · rintro y (hy | hy)
    · refine mem_iUnion₂.mpr ⟨⟨(sK k, eK k), (hinc k k).mpr (Or.inl rfl)⟩, ⟨rfl, hsK k⟩,
        (hmark _).subset ?_⟩
      change y ∈ tgtD (sK k) ∩ section34CompactSplitDiskImage src f₁ (eK k)
      rw [hγ0, hy]
      exact mem_singleton _
    · refine mem_iUnion₂.mpr ⟨⟨(sK (k + 1), eK k), (hinc (k + 1) k).mpr (Or.inr rfl)⟩,
        ⟨rfl, hsK (k + 1)⟩, (hmark _).subset ?_⟩
      change y ∈ tgtD (sK (k + 1)) ∩ section34CompactSplitDiskImage src f₁ (eK k)
      rw [hγ1, mem_singleton_iff.mp hy]
      exact mem_singleton _
  · intro y hy
    obtain ⟨p, ⟨hpe, hpt⟩, hy⟩ := mem_iUnion₂.mp hy
    rw [← hmark] at hy
    have hps : Section34Incident (eK k).1 p.1.1.1 := by
      rw [← hpe]
      exact p.2
    have hwp : Section34Incident w.1 p.1.1.1 := fun z hz => hps (hweK k hz)
    obtain ⟨j, hj⟩ := hscomp p.1.1 hpt hwp
    rw [hj] at hps hy
    rw [hpe] at hy
    rcases (hinc j k).mp hps with h | h
    · rw [← h, hγ0] at hy
      exact Or.inl hy
    · rw [← h, hγ1] at hy
      exact Or.inr hy

end DifferentialGeometry.Topology.PiecewiseLinear
