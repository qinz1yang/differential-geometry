/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ClawHoles
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceRuns
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TetraFaces

open Set

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

open Classical in
theorem Section34FaceDiskFamily.exists_faceRuns_of_tetra
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) {a b c d : Ea} (htabcd : t = {a, b, c, d})
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {ea eb ec ed : Section34EdgeIndex 𝒦 𝒦'}
    (hea₁ : a ∈ ea.1) (hea₂ : convexHull ℝ (ea.1 : Set Ea) ⊆ segment ℝ a d)
    (heb₁ : b ∈ eb.1) (heb₂ : convexHull ℝ (eb.1 : Set Ea) ⊆ segment ℝ b c)
    (hec₁ : c ∈ ec.1) (hec₂ : convexHull ℝ (ec.1 : Set Ea) ⊆ segment ℝ c a)
    (hed₁ : d ∈ ed.1) (hed₂ : convexHull ℝ (ed.1 : Set Ea) ⊆ segment ℝ d b)
    (hinj : ∀ k l : Fin 4, k ≠ l → ![ec, eb, ed, ea] k ≠ ![ec, eb, ed, ea] l)
    (h12 : section34ClawBall (section34VertexBallImage src f₁) a b c d ∩
        section34ClawBall (section34VertexBallImage src f₁) d c a b =
      ⋃ k, section34SplitDiskImage src f₁ (![ec, eb, ed, ea] k))
    {sacd sabc sbcd sabd : Section34SimplexIndex 𝒦 3} (hsacd : sacd.1 = {a, c, d})
    (hsabc : sabc.1 = {a, b, c}) (hsbcd : sbcd.1 = {b, c, d}) (hsabd : sabd.1 = {a, b, d})
    {chart : OpenPartialHomeomorph M₂ E3}
    (hchart : chart ∈ (plGroupoid 3).maximalAtlas M₂)
    (hVchart : ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 t →
      section34VertexBallImage src f₁ w ⊆ chart.source)
    (hDchart : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t →
      tgtD s ⊆ chart.source) :
    ∃ (pin pout : Fin 4 → M₂) (γ₁ γ₂ : Fin 4 → ℝ → E3),
      (∀ k, pin k ∈ section34SplitDiskImage srcBd f₁ (![ec, eb, ed, ea] (k - 1))) ∧
      (∀ k, pout k ∈ section34SplitDiskImage srcBd f₁ (![ec, eb, ed, ea] k)) ∧
      (∀ k, tgtD (![sacd, sabc, sbcd, sabd] k) ∩
        section34SplitDiskImage src f₁ (![ec, eb, ed, ea] (k - 1)) = {pin k}) ∧
      (∀ k, tgtD (![sacd, sabc, sbcd, sabd] k) ∩
        section34SplitDiskImage src f₁ (![ec, eb, ed, ea] k) = {pout k}) ∧
      (∀ k l, l ≠ k - 1 → l ≠ k → tgtD (![sacd, sabc, sbcd, sabd] k) ∩
        section34SplitDiskImage src f₁ (![ec, eb, ed, ea] l) = ∅) ∧
      (∀ k, tgtDBd (![sacd, sabc, sbcd, sabd] k) =
        tgtD (![sacd, sabc, sbcd, sabd] k) ∩
            section34ClawBall (section34VertexBallImage src f₁) a b c d ∪
          tgtD (![sacd, sabc, sbcd, sabd] k) ∩
            section34ClawBall (section34VertexBallImage src f₁) d c a b) ∧
      (∀ k, tgtD (![sacd, sabc, sbcd, sabd] k) ∩
          section34ClawBall (section34VertexBallImage src f₁) a b c d ∩
        (tgtD (![sacd, sabc, sbcd, sabd] k) ∩
          section34ClawBall (section34VertexBallImage src f₁) d c a b) =
        {pin k, pout k}) ∧
      (∀ k, IsPLHomeomorphOn (γ₁ k) (Icc 0 1)
        (chart '' (tgtD (![sacd, sabc, sbcd, sabd] k) ∩
          section34ClawBall (section34VertexBallImage src f₁) a b c d)) ∧
        γ₁ k 0 = chart (pin k) ∧ γ₁ k 1 = chart (pout k)) ∧
      ∀ k, IsPLHomeomorphOn (γ₂ k) (Icc 0 1)
        (chart '' (tgtD (![sacd, sabc, sbcd, sabd] k) ∩
          section34ClawBall (section34VertexBallImage src f₁) d c a b)) ∧
        γ₂ k 0 = chart (pin k) ∧ γ₂ k 1 = chart (pout k) := by
  classical
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  have hmap := hcut.2.2.1
  set V := section34VertexBallImage src f₁
  set B₁ := section34ClawBall V a b c d
  set B₂ := section34ClawBall V d c a b
  have ha : a ∈ t := by rw [htabcd]; simp
  have hb : b ∈ t := by rw [htabcd]; simp
  have hc : c ∈ t := by rw [htabcd]; simp
  have hd : d ∈ t := by rw [htabcd]; simp
  have hvK : ∀ {u : Ea}, u ∈ t → ({u} : Finset Ea) ∈ 𝒦.complex.faces := fun hu =>
    𝒦.complex.down_closed ht (Finset.singleton_subset_iff.mpr hu) (Finset.singleton_nonempty _)
  have hpK : ∀ {u v : Ea}, u ∈ t → v ∈ t → ({u, v} : Finset Ea) ∈ 𝒦.complex.faces := fun hu hv =>
    𝒦.complex.down_closed ht (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv))
      (Finset.insert_nonempty _ _)
  have hB₁c : IsClosed B₁ :=
    (hcut.isPLCellOn_section34ClawBall hf₁ ht ha hb hc hd hab hac hbd had hbc
      hcd hchart hVchart).isCompact.isClosed
  have hB₂c : IsClosed B₂ :=
    (hcut.isPLCellOn_section34ClawBall hf₁ ht hd hc ha hb hcd.symm had.symm hbc.symm
      hbd.symm hac.symm hab hchart hVchart).isCompact.isClosed
  have hsub : B₁ ∪ B₂ ⊆ ⋃ w, V w := by
    refine union_subset (iUnion₂_subset fun w _ => subset_iUnion V w)
      (iUnion₂_subset fun w _ => subset_iUnion V w)
  have hst : ∀ {s : Section34SimplexIndex 𝒦 3}, (s.1 : Set Ea) ⊆ t →
      ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 → V w ⊆ B₁ ∪ B₂ :=
    fun hs w hw => section34VertexBallImage_subset_clawBall_union hmap ht htabcd
      (hw.trans (convexHull_min (hs.trans (subset_convexHull ℝ _)) (convex_convexHull ℝ _)))
  have hsubt : ∀ {s : Finset Ea} {x y z : Ea}, s = {x, y, z} → x ∈ t → y ∈ t → z ∈ t →
      (s : Set Ea) ⊆ t := by
    intro s x y z hs hx hy hz u hu
    rw [hs] at hu
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  obtain ⟨wa, wa', pa, hwa, -, hpae, hpaa, -, -⟩ :=
    exists_section34VertexIndex_pair_of_mem_edgeIndex ea hea₁
  obtain ⟨wb, wb', pb, hwb, -, hpbe, hpbb, -, -⟩ :=
    exists_section34VertexIndex_pair_of_mem_edgeIndex eb heb₁
  obtain ⟨wc, wc', pc, hwc, -, hpce, hpcc, -, -⟩ :=
    exists_section34VertexIndex_pair_of_mem_edgeIndex ec hec₁
  obtain ⟨wd, wd', pd, hwd, -, hpde, hpdd, -, -⟩ :=
    exists_section34VertexIndex_pair_of_mem_edgeIndex ed hed₁
  have hVa : V wa ⊆ B₁ := fun z hz =>
    mem_iUnion₂.mpr ⟨wa, ⟨a, hwa, Or.inl (left_mem_segment ℝ a b)⟩, hz⟩
  have hVb : V wb ⊆ B₁ := fun z hz =>
    mem_iUnion₂.mpr ⟨wb, ⟨b, hwb, Or.inl (right_mem_segment ℝ a b)⟩, hz⟩
  have hVc : V wc ⊆ B₂ := fun z hz =>
    mem_iUnion₂.mpr ⟨wc, ⟨c, hwc, Or.inl (right_mem_segment ℝ d c)⟩, hz⟩
  have hVd : V wd ⊆ B₂ := fun z hz =>
    mem_iUnion₂.mpr ⟨wd, ⟨d, hwd, Or.inl (left_mem_segment ℝ d c)⟩, hz⟩
  have hwinc : ∀ {w : Section34VertexIndex 𝒦 𝒦'} {u : Ea} {s : Finset Ea}, w.1 = {u} →
      u ∈ s → Section34Incident w.1 s := by
    intro w u s hw hu z hz
    rw [hw, Finset.coe_singleton] at hz
    rw [mem_singleton_iff.mp hz]
    exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hu)
  have hseg : ∀ {e : Section34EdgeIndex 𝒦 𝒦'} {u v x : Ea},
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ u v → x ∈ e.1 → x ∈ segment ℝ u v :=
    fun he hx => he (subset_convexHull ℝ _ hx)
  have hmem : ∀ {s : Finset Ea} {x y z u : Ea}, s = {x, y, z} → (u = x ∨ u = y ∨ u = z) →
      u ∈ s := by
    intro s x y z u hs hu
    rw [hs]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hu
  have hnmem : ∀ {s : Finset Ea} {x y z u : Ea}, s = {x, y, z} → u ≠ x → u ≠ y → u ≠ z →
      u ∉ s := by
    intro s x y z u hs hx hy hz hu
    rw [hs] at hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with h | h | h
    · exact hx h
    · exact hy h
    · exact hz h
  have hDc : ∀ {s : Section34SimplexIndex 𝒦 3}, (s.1 : Set Ea) ⊆ t →
      tgtD s ⊆ chart.source := fun hs =>
    hDchart _ (hs.trans (subset_convexHull ℝ _))
  have hface : ∀ k : Fin 4, ∃ (p q : M₂) (g₁ g₂ : ℝ → E3),
      p ∈ section34SplitDiskImage srcBd f₁ (![ec, eb, ed, ea] (k - 1)) ∧
      q ∈ section34SplitDiskImage srcBd f₁ (![ec, eb, ed, ea] k) ∧
      tgtD (![sacd, sabc, sbcd, sabd] k) ∩
        section34SplitDiskImage src f₁ (![ec, eb, ed, ea] (k - 1)) = {p} ∧
      tgtD (![sacd, sabc, sbcd, sabd] k) ∩
        section34SplitDiskImage src f₁ (![ec, eb, ed, ea] k) = {q} ∧
      (∀ l, l ≠ k - 1 → l ≠ k → tgtD (![sacd, sabc, sbcd, sabd] k) ∩
        section34SplitDiskImage src f₁ (![ec, eb, ed, ea] l) = ∅) ∧
      tgtDBd (![sacd, sabc, sbcd, sabd] k) =
        tgtD (![sacd, sabc, sbcd, sabd] k) ∩ B₁ ∪ tgtD (![sacd, sabc, sbcd, sabd] k) ∩ B₂ ∧
      tgtD (![sacd, sabc, sbcd, sabd] k) ∩ B₁ ∩ (tgtD (![sacd, sabc, sbcd, sabd] k) ∩ B₂) =
        {p, q} ∧
      (IsPLHomeomorphOn g₁ (Icc 0 1)
        (chart '' (tgtD (![sacd, sabc, sbcd, sabd] k) ∩ B₁)) ∧
        g₁ 0 = chart p ∧ g₁ 1 = chart q) ∧
      (IsPLHomeomorphOn g₂ (Icc 0 1)
        (chart '' (tgtD (![sacd, sabc, sbcd, sabd] k) ∩ B₂)) ∧
        g₂ 0 = chart p ∧ g₂ 1 = chart q) := by
    intro k
    fin_cases k
    · obtain ⟨p, q, hp, hq, hDi, hDj, hDo, hDb, hint, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ :=
        hdisk.exists_runs_of_face hdata hB₁c hB₂c hsub h12 sacd
          (hst (hsubt hsacd ha hc hd)) (i := 3) (j := 0) (hinj 3 0 (by decide))
          (SimplicialComplex.section34Incident_of_subset_segment hea₂
            (hmem hsacd (Or.inl rfl))
            (hmem hsacd (Or.inr (Or.inr rfl))))
          (SimplicialComplex.section34Incident_of_subset_segment hec₂
            (hmem hsacd (Or.inr (Or.inl rfl)))
            (hmem hsacd (Or.inl rfl)))
          (fun l h1 h2 => by
            fin_cases l
            · exact absurd rfl h2
            · exact SimplicialComplex.not_section34Incident_of_notMem_left sacd.2.1 (hvK hb) heb₁
                (hnmem hsacd hab.symm hbc hbd)
            · exact SimplicialComplex.not_section34Incident_of_notMem_right
                sacd.2.1 (hpK hd hb) hpde
                (hseg hed₂ hpde) hpdd (hnmem hsacd hab.symm hbc hbd)
            · exact absurd rfl h1)
          (hwinc hwa (hmem hsacd (Or.inl rfl))) (hwinc hwd (hmem hsacd (Or.inr (Or.inr rfl))))
          hVa hVd hchart (hDc (hsubt hsacd ha hc hd))
      exact ⟨p, q, g₁, g₂, hp, hq, hDi, hDj, hDo, hDb, hint, hg₁, hg₂⟩
    · obtain ⟨p, q, hp, hq, hDi, hDj, hDo, hDb, hint, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ :=
        hdisk.exists_runs_of_face hdata hB₁c hB₂c hsub h12 sabc
          (hst (hsubt hsabc ha hb hc)) (i := 0) (j := 1) (hinj 0 1 (by decide))
          (SimplicialComplex.section34Incident_of_subset_segment hec₂
            (hmem hsabc (Or.inr (Or.inr rfl)))
            (hmem hsabc (Or.inl rfl)))
          (SimplicialComplex.section34Incident_of_subset_segment heb₂
            (hmem hsabc (Or.inr (Or.inl rfl)))
            (hmem hsabc (Or.inr (Or.inr rfl))))
          (fun l h1 h2 => by
            fin_cases l
            · exact absurd rfl h1
            · exact absurd rfl h2
            · exact SimplicialComplex.not_section34Incident_of_notMem_left sabc.2.1 (hvK hd) hed₁
                (hnmem hsabc had.symm hbd.symm hcd.symm)
            · exact SimplicialComplex.not_section34Incident_of_notMem_right
                sabc.2.1 (hpK ha hd) hpae
                (hseg hea₂ hpae) hpaa (hnmem hsabc had.symm hbd.symm hcd.symm))
          (hwinc hwa (hmem hsabc (Or.inl rfl))) (hwinc hwc (hmem hsabc (Or.inr (Or.inr rfl))))
          hVa hVc hchart (hDc (hsubt hsabc ha hb hc))
      exact ⟨p, q, g₁, g₂, hp, hq, hDi, hDj, hDo, hDb, hint, hg₁, hg₂⟩
    · obtain ⟨p, q, hp, hq, hDi, hDj, hDo, hDb, hint, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ :=
        hdisk.exists_runs_of_face hdata hB₁c hB₂c hsub h12 sbcd
          (hst (hsubt hsbcd hb hc hd)) (i := 1) (j := 2) (hinj 1 2 (by decide))
          (SimplicialComplex.section34Incident_of_subset_segment heb₂
            (hmem hsbcd (Or.inl rfl))
            (hmem hsbcd (Or.inr (Or.inl rfl))))
          (SimplicialComplex.section34Incident_of_subset_segment hed₂
            (hmem hsbcd (Or.inr (Or.inr rfl)))
            (hmem hsbcd (Or.inl rfl)))
          (fun l h1 h2 => by
            fin_cases l
            · exact SimplicialComplex.not_section34Incident_of_notMem_right
                sbcd.2.1 (hpK hc ha) hpce
                (hseg hec₂ hpce) hpcc (hnmem hsbcd hab hac had)
            · exact absurd rfl h1
            · exact absurd rfl h2
            · exact SimplicialComplex.not_section34Incident_of_notMem_left sbcd.2.1 (hvK ha) hea₁
                (hnmem hsbcd hab hac had))
          (hwinc hwb (hmem hsbcd (Or.inl rfl))) (hwinc hwc (hmem hsbcd (Or.inr (Or.inl rfl))))
          hVb hVc hchart (hDc (hsubt hsbcd hb hc hd))
      exact ⟨p, q, g₁, g₂, hp, hq, hDi, hDj, hDo, hDb, hint, hg₁, hg₂⟩
    · obtain ⟨p, q, hp, hq, hDi, hDj, hDo, hDb, hint, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ :=
        hdisk.exists_runs_of_face hdata hB₁c hB₂c hsub h12 sabd
          (hst (hsubt hsabd ha hb hd)) (i := 2) (j := 3) (hinj 2 3 (by decide))
          (SimplicialComplex.section34Incident_of_subset_segment hed₂
            (hmem hsabd (Or.inr (Or.inr rfl)))
            (hmem hsabd (Or.inr (Or.inl rfl))))
          (SimplicialComplex.section34Incident_of_subset_segment hea₂
            (hmem hsabd (Or.inl rfl))
            (hmem hsabd (Or.inr (Or.inr rfl))))
          (fun l h1 h2 => by
            fin_cases l
            · exact SimplicialComplex.not_section34Incident_of_notMem_left sabd.2.1 (hvK hc) hec₁
                (hnmem hsabd hac.symm hbc.symm hcd)
            · exact SimplicialComplex.not_section34Incident_of_notMem_right
                sabd.2.1 (hpK hb hc) hpbe
                (hseg heb₂ hpbe) hpbb (hnmem hsabd hac.symm hbc.symm hcd)
            · exact absurd rfl h1
            · exact absurd rfl h2)
          (hwinc hwa (hmem hsabd (Or.inl rfl))) (hwinc hwd (hmem hsabd (Or.inr (Or.inr rfl))))
          hVa hVd hchart (hDc (hsubt hsabd ha hb hd))
      exact ⟨p, q, g₁, g₂, hp, hq, hDi, hDj, hDo, hDb, hint, hg₁, hg₂⟩
  choose pin pout γ₁ γ₂ hp hq hDi hDj hDo hDb hint hg₁ hg₂ using hface
  exact ⟨pin, pout, γ₁, γ₂, hp, hq, hDi, hDj, hDo, hDb, hint, hg₁, hg₂⟩

end DifferentialGeometry.Topology.PiecewiseLinear
