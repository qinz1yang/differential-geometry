/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualPatch
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PatchEnumeration

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}
  {fbl fblBd tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂}
  {tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂}
  {tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂}

theorem Section34NormalPlus.isPLCellOn_residualPatch_boundary
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34SimplexIndex 𝒦 4} {R : Set M₂} (hR : IsPLCellOn 3 R (frontier R))
    (hDR : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      tgtD s ⊆ frontier R)
    (hfr : frontier R ⊆ (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w) ∪
      ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34VertexIndex 𝒦 𝒦')
      (_ : Section34Incident w.1 t.1), section34VertexBallImage src f₁ w))
    (hio : ∀ a : Section34ArcIndex 𝒦 𝒦', Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34EdgeIndex 𝒦 𝒦', y ∉ section34SplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∈ R ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∉ R)
    (h7 : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 t.1 →
      R ∩ section34VertexBallImage src f₁ w = ∅)
    {w : Section34VertexIndex 𝒦 𝒦'} (hw : Section34Incident w.1 t.1) :
    IsPLCellOn 2 (R ∩ section34VertexBallImage src f₁ w)
      ((⋃ (a : Section34ArcIndex 𝒦 𝒦')
          (_ : a.1.2 = w ∧ Section34Incident a.1.1.1 t.1), tgtA a) ∪
        ⋃ (i : Section34EdgeArcIndex 𝒦 𝒦') (_ : i.1.1 = t ∧ w.1 ⊆ i.1.2.1),
          R ∩ section34SplitDiskImage src f₁ i.1.2) := by
  have hcut := hdata.1
  obtain ⟨m, sK, eK, hsK, hwsK, hweK, hsinj, heinj, hinc, hscomp, hecomp⟩ :=
    hcut.exists_patchEnum t hw
  obtain ⟨hcell, -⟩ := hdata.isPLCellOn_residualPatch hdisk hR hDR hfr hint hio h7 hsK hwsK
    hweK hsinj heinj hinc hscomp hecomp
  have heKt : ∀ k, Section34Incident (eK k).1 t.1 := fun k z hz =>
    convexHull_min (hsK k) (convex_convexHull ℝ _) (((hinc k k).mpr (Or.inl rfl)) hz)
  convert hcell using 1
  congr 1
  · symm
    ext y
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
  · symm
    ext y
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

theorem Section34NormalPlus.isPLCellOn_residualEdgeArc
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34SimplexIndex 𝒦 4} {R : Set M₂} (hR : IsPLCellOn 3 R (frontier R))
    (hDR : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      tgtD s ⊆ frontier R)
    (hfr : frontier R ⊆ (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w) ∪
      ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34VertexIndex 𝒦 𝒦')
      (_ : Section34Incident w.1 t.1), section34VertexBallImage src f₁ w))
    (hio : ∀ a : Section34ArcIndex 𝒦 𝒦', Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34EdgeIndex 𝒦 𝒦', y ∉ section34SplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∈ R ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∉ R)
    (h7 : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 t.1 →
      R ∩ section34VertexBallImage src f₁ w = ∅)
    {e : Section34EdgeIndex 𝒦 𝒦'} (he : Section34Incident e.1 t.1) :
    IsPLCellOn 1 (R ∩ section34SplitDiskImage src f₁ e)
      (⋃ (p : Section34MarkIndex 𝒦 𝒦')
        (_ : p.1.2 = e ∧ Section34Incident p.1.1.1 t.1), tgtP p) := by
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  obtain ⟨w, w', -, hew, -⟩ := hcut.splitDiskImage_eq_inter hf₁.injOn e
  have hwe : w.1 ⊆ e.1 := by
    have h : (w.1 : Set Ea) ⊆ e.1 := by
      rw [hew]
      exact subset_union_left
    exact Finset.coe_subset.mp h
  have hw : Section34Incident w.1 t.1 := fun z hz => he (hwe hz)
  obtain ⟨m, sK, eK, hsK, hwsK, hweK, hsinj, heinj, hinc, hscomp, hecomp⟩ :=
    hcut.exists_patchEnum t hw
  obtain ⟨-, hI⟩ := hdata.isPLCellOn_residualPatch hdisk hR hDR hfr hint hio h7 hsK hwsK
    hweK hsinj heinj hinc hscomp hecomp
  obtain ⟨k, rfl⟩ := hecomp e he hwe
  have hmark := hdisk.faceDisk_inter_splitDisk_eq hdata
  have hbd : (tgtD (sK k) ∩ section34SplitDiskImage src f₁ (eK k)) ∪
      tgtD (sK (k + 1)) ∩ section34SplitDiskImage src f₁ (eK k) =
      ⋃ (p : Section34MarkIndex 𝒦 𝒦')
        (_ : p.1.2 = eK k ∧ Section34Incident p.1.1.1 t.1), tgtP p := by
    apply Subset.antisymm
    · rintro y (hy | hy)
      · exact mem_iUnion₂.mpr
          ⟨⟨(sK k, eK k), (hinc k k).mpr (Or.inl rfl)⟩, ⟨rfl, hsK k⟩, (hmark _).subset hy⟩
      · exact mem_iUnion₂.mpr
          ⟨⟨(sK (k + 1), eK k), (hinc (k + 1) k).mpr (Or.inr rfl)⟩,
            ⟨rfl, hsK (k + 1)⟩, (hmark _).subset hy⟩
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
      · rw [← h] at hy
        exact Or.inl hy
      · rw [← h] at hy
        exact Or.inr hy
  exact hbd ▸ hI k

end DifferentialGeometry.Topology.PiecewiseLinear
