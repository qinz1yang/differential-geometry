/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleClosedCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

theorem Section34CutFrame.isPLCellOn_inter_vertexBallImage_of_chart
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    {s : Section34SimplexIndex 𝒦 3} {c : OpenPartialHomeomorph M₂ E3}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M₂)
    (hTc : section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.source)
    {J F : Set M₂} (hJ : IsPLSphere 1 (c '' J)) (hJF : J ⊆ F)
    (hF : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 s.1 →
      F ∩ section34VertexBallImage src f₁ w = ∅)
    (hJT : J ⊆ frontier (section34FaceTorus (section34VertexBallImage src f₁) s))
    (hJE : ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 →
      ∃ p, J ∩ section34SplitDiskImage srcBd f₁ e = {p})
    {w : Section34VertexIndex 𝒦 𝒦'} (hw : Section34Incident w.1 s.1) :
    IsPLCellOn 1 (J ∩ section34VertexBallImage src f₁ w)
        (J ∩ section34VertexBallImage src f₁ w ∩ ⋃ e, section34SplitDiskImage src f₁ e) ∧
      IsPreconnected (J ∩ ⋃ (u : Section34VertexIndex 𝒦 𝒦')
        (_ : Section34Incident u.1 s.1 ∧ u ≠ w), section34VertexBallImage src f₁ u) := by
  classical
  obtain ⟨-, hsub, hmap, -⟩ := id hcut
  have hinj : InjOn f₁ (section34CutNeighborhood src) := hf₁.injOn
  have hVcell := hcut.isPLCellOn_vertexBallImage hf₁
  have hVc : ∀ u : Section34VertexIndex 𝒦 𝒦', IsClosed (section34VertexBallImage src f₁ u) :=
    fun u => (hVcell u).isCompact.isClosed
  have hJTs : J ⊆ section34FaceTorus (section34VertexBallImage src f₁) s :=
    hJT.trans (isClosed_section34FaceTorus hsub hVc s).frontier_subset
  have hJc : J ⊆ c.source := hJTs.trans hTc
  have hVsrc : ∀ u : Section34VertexIndex 𝒦 𝒦', Section34Incident u.1 s.1 →
      section34VertexBallImage src f₁ u ⊆ c.source := fun u hu x hx =>
    hTc (mem_section34FaceTorus_iff.mpr ⟨u, hu, hx⟩)
  have hinc : ∀ (u : Section34VertexIndex 𝒦 𝒦') (x : M₂), x ∈ J →
      x ∈ section34VertexBallImage src f₁ u → Section34Incident u.1 s.1 := by
    intro u x hxJ hxu
    by_contra hn
    have hx : x ∈ F ∩ section34VertexBallImage src f₁ u := ⟨hJF hxJ, hxu⟩
    rw [hF u hn] at hx
    exact hx
  have hsubinc : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (u : Section34VertexIndex 𝒦 𝒦'),
      Section34Incident e.1 s.1 → u.1 ⊆ e.1 → Section34Incident u.1 s.1 :=
    fun _ _ he hu => (Finset.coe_subset.mpr hu).trans he
  have hEinc : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (x : M₂), x ∈ J →
      x ∈ section34SplitDiskImage src f₁ e → Section34Incident e.1 s.1 := by
    intro e x hxJ hxe
    obtain ⟨u, u', -, heu, hEeq⟩ := hcut.splitDiskImage_eq_inter hinj e
    rw [hEeq] at hxe
    change (e.1 : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea)
    rw [heu]
    exact union_subset (hinc u x hxJ hxe.1) (hinc u' x hxJ hxe.2)
  have hJEbd : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (x : M₂), x ∈ J →
      x ∈ section34SplitDiskImage src f₁ e → x ∈ section34SplitDiskImage srcBd f₁ e := by
    intro e x hxJ hxe
    by_contra hxb
    have he := hEinc e x hxJ hxe
    have hint := hcut.splitDiskImage_sdiff_subset_interior hf₁ e hc
      (fun u hu => hVsrc u (hsubinc e u he hu)) ⟨hxe, hxb⟩
    have hsubT : (⋃ (u : Section34VertexIndex 𝒦 𝒦') (_ : u.1 ⊆ e.1),
        section34VertexBallImage src f₁ u) ⊆
          section34FaceTorus (section34VertexBallImage src f₁) s :=
      iUnion₂_subset fun u hu y hy => mem_section34FaceTorus_iff.mpr ⟨u, hsubinc e u he hu, hy⟩
    exact Set.disjoint_left.mp disjoint_interior_frontier (interior_mono hsubT hint) (hJT hxJ)
  have hEbdE : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      section34SplitDiskImage srcBd f₁ e ⊆ section34SplitDiskImage src f₁ e :=
    fun e => (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset
  choose pt hpt using fun e : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1} =>
    hJE e.1 e.2
  have hptJ : ∀ e, pt e ∈ J ∧ pt e ∈ section34SplitDiskImage srcBd f₁ e.1 := by
    intro e
    have h : pt e ∈ J ∩ section34SplitDiskImage srcBd f₁ e.1 := by
      rw [hpt e]
      exact mem_singleton _
    exact h
  have hmemE : ∀ (e : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1}) (x : M₂),
      x ∈ J → x ∈ section34SplitDiskImage src f₁ e.1 → x = pt e := by
    intro e x hxJ hxe
    have hx : x ∈ J ∩ section34SplitDiskImage srcBd f₁ e.1 := ⟨hxJ, hJEbd e.1 x hxJ hxe⟩
    rw [hpt e] at hx
    exact hx
  have hptV : ∀ (e : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1})
      (u : Section34VertexIndex 𝒦 𝒦'), u.1 ⊆ e.1.1 → pt e ∈ section34VertexBallImage src f₁ u := by
    intro e u hu
    obtain ⟨a, b, -, hab, hEeq⟩ := hcut.splitDiskImage_eq_inter hinj e.1
    have hpe := hEbdE e.1 (hptJ e).2
    rw [hEeq] at hpe
    rcases eq_or_eq_of_section34VertexIndex_subset e.1 hab hu with h | h
    · rw [h]
      exact hpe.1
    · rw [h]
      exact hpe.2
  have hpig : ∀ {β : Type} (a b x y z : β), (x = a ∨ x = b) → (y = a ∨ y = b) →
      (z = a ∨ z = b) → x = y ∨ x = z ∨ y = z := by
    intro β a b x y z hx hy hz
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;>
      first
        | exact Or.inl (hx.trans hy.symm)
        | exact Or.inr (Or.inl (hx.trans hz.symm))
        | exact Or.inr (Or.inr (hy.trans hz.symm))
  have _ : Finite {u : Section34VertexIndex 𝒦 𝒦' // Section34Incident u.1 s.1} :=
    (finite_setOf_section34Incident_graphIndex hsub (graphSkeletonSpace 𝒦) 1 s.2.1).to_subtype
  have hcJ : IsClosed (c '' J) := hJ.isPolyhedron.isClosed
  let X : {u : Section34VertexIndex 𝒦 𝒦' // Section34Incident u.1 s.1} → Set E3 :=
    fun u => c '' J ∩ c '' section34VertexBallImage src f₁ u.1
  have hX : ∀ u, IsClosed (X u) := fun u => hcJ.inter
    ((hVcell u.1).isCompact.image_of_continuousOn (c.continuousOn.mono (hVsrc u.1 u.2))).isClosed
  have hXJ : ∀ u, X u ⊆ c '' J := fun _ => inter_subset_left
  have hback : ∀ (u : Section34VertexIndex 𝒦 𝒦'), Section34Incident u.1 s.1 → ∀ y ∈ J,
      c y ∈ c '' section34VertexBallImage src f₁ u → y ∈ section34VertexBallImage src f₁ u := by
    intro u hu y hy hcy
    obtain ⟨z, hz, hzy⟩ := hcy
    have hzy' : z = y := c.injOn (hVsrc u hu hz) (hJc hy) hzy
    exact hzy' ▸ hz
  have hcover : c '' J ⊆ ⋃ u, X u := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, hxu⟩ := mem_section34FaceTorus_iff.mp (hJTs hx)
    exact mem_iUnion.mpr ⟨⟨u, hu⟩, mem_image_of_mem c hx, mem_image_of_mem c hxu⟩
  have hXne : ∀ u, X u ≠ c '' J := by
    intro u h
    obtain ⟨e, he, hne⟩ := exists_section34EdgeIndex_incident_not_subset hsub hmap s u.1 u.2
    have hpX : c (pt ⟨e, he⟩) ∈ X u := by
      rw [h]
      exact mem_image_of_mem c (hptJ ⟨e, he⟩).1
    have hpu := hback u.1 u.2 _ (hptJ ⟨e, he⟩).1 hpX.2
    exact hne (hcut.subset_of_mem_splitDiskImage hinj (hEbdE e (hptJ ⟨e, he⟩).2) hpu)
  let p : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1} → E3 := fun e => c (pt e)
  have hp : Function.Injective p := by
    intro e e' h
    have h' : pt e = pt e' := c.injOn (hJc (hptJ e).1) (hJc (hptJ e').1) h
    by_contra hee
    have hne : e.1 ≠ e'.1 := fun h'' => hee (Subtype.ext h'')
    exact Set.disjoint_left.mp (hcut.disjoint_splitDiskImage hinj hne) (hEbdE e.1 (hptJ e).2)
      (h' ▸ hEbdE e'.1 (hptJ e').2)
  have hpX : ∀ (u : {u : Section34VertexIndex 𝒦 𝒦' // Section34Incident u.1 s.1})
      (e : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1}),
      p e ∈ X u ↔ u.1.1 ⊆ e.1.1 := by
    intro u e
    constructor
    · intro h
      exact hcut.subset_of_mem_splitDiskImage hinj (hEbdE e.1 (hptJ e).2)
        (hback u.1 u.2 _ (hptJ e).1 h.2)
    · intro h
      exact ⟨mem_image_of_mem c (hptJ e).1, mem_image_of_mem c (hptV e u.1 h)⟩
  have hmeet : ∀ u u' : {u : Section34VertexIndex 𝒦 𝒦' // Section34Incident u.1 s.1},
      u ≠ u' → ∀ x ∈ X u ∩ X u',
      ∃ e : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1},
        u.1.1 ⊆ e.1.1 ∧ u'.1.1 ⊆ e.1.1 ∧ x = p e := by
    intro u u' huu x hx
    obtain ⟨y, hyJ, rfl⟩ := hx.1.1
    have hyu := hback u.1 u.2 y hyJ hx.1.2
    have hyu' := hback u'.1 u'.2 y hyJ hx.2.2
    have hne : u.1 ≠ u'.1 := fun h => huu (Subtype.ext h)
    obtain ⟨e, hye⟩ := hcut.exists_mem_splitDiskImage_of_ne hinj hne hyu hyu'
    have he := hEinc e y hyJ hye
    exact ⟨⟨e, he⟩, hcut.subset_of_mem_splitDiskImage hinj hye hyu,
      hcut.subset_of_mem_splitDiskImage hinj hye hyu', by rw [hmemE ⟨e, he⟩ y hyJ hye]⟩
  have hdeg : ∀ u : {u : Section34VertexIndex 𝒦 𝒦' // Section34Incident u.1 s.1},
      ∃ e₁ e₂ : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1},
        e₁ ≠ e₂ ∧ u.1.1 ⊆ e₁.1.1 ∧ u.1.1 ⊆ e₂.1.1 := by
    intro u
    obtain ⟨e₁, e₂, hne, hi₁, hi₂, hw₁, hw₂, -⟩ :=
      exists_section34EdgeIndex_pair_of_incident hsub hmap s u.1 u.2
    exact ⟨⟨e₁, hi₁⟩, ⟨e₂, hi₂⟩, fun h => hne (congrArg Subtype.val h), hw₁, hw₂⟩
  have hdeg₃ : ∀ (u : {u : Section34VertexIndex 𝒦 𝒦' // Section34Incident u.1 s.1})
      (g₁ g₂ g₃ : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1}),
      u.1.1 ⊆ g₁.1.1 → u.1.1 ⊆ g₂.1.1 → u.1.1 ⊆ g₃.1.1 → g₁ = g₂ ∨ g₁ = g₃ ∨ g₂ = g₃ := by
    intro u g₁ g₂ g₃ h₁ h₂ h₃
    obtain ⟨e₁, e₂, -, -, -, -, -, huniq⟩ :=
      exists_section34EdgeIndex_pair_of_incident hsub hmap s u.1 u.2
    rcases hpig e₁ e₂ g₁.1 g₂.1 g₃.1 (huniq g₁.1 g₁.2 h₁) (huniq g₂.1 g₂.2 h₂)
      (huniq g₃.1 g₃.2 h₃) with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  have hend : ∀ e : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1},
      ∃ u u' : {u : Section34VertexIndex 𝒦 𝒦' // Section34Incident u.1 s.1},
        u ≠ u' ∧ u.1.1 ⊆ e.1.1 ∧ u'.1.1 ⊆ e.1.1 := by
    intro e
    obtain ⟨a, b, hab, heab, -⟩ := hcut.splitDiskImage_eq_inter hinj e.1
    have ha : (a.1 : Set Ea) ⊆ e.1.1 := heab ▸ subset_union_left
    have hb : (b.1 : Set Ea) ⊆ e.1.1 := heab ▸ subset_union_right
    exact ⟨⟨a, ha.trans e.2⟩, ⟨b, hb.trans e.2⟩, fun h => hab (congrArg Subtype.val h),
      Finset.coe_subset.mp ha, Finset.coe_subset.mp hb⟩
  have hend₃ : ∀ (e : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1})
      (u₁ u₂ u₃ : {u : Section34VertexIndex 𝒦 𝒦' // Section34Incident u.1 s.1}),
      u₁.1.1 ⊆ e.1.1 → u₂.1.1 ⊆ e.1.1 → u₃.1.1 ⊆ e.1.1 → u₁ = u₂ ∨ u₁ = u₃ ∨ u₂ = u₃ := by
    intro e u₁ u₂ u₃ h₁ h₂ h₃
    obtain ⟨a, b, -, hab, -⟩ := hcut.splitDiskImage_eq_inter hinj e.1
    rcases hpig a b u₁.1 u₂.1 u₃.1 (eq_or_eq_of_section34VertexIndex_subset e.1 hab h₁)
      (eq_or_eq_of_section34VertexIndex_subset e.1 hab h₂)
      (eq_or_eq_of_section34VertexIndex_subset e.1 hab h₃) with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  obtain ⟨e₁, e₂, hne, hi₁, hi₂, hw₁, hw₂, huniq⟩ :=
    exists_section34EdgeIndex_pair_of_incident hsub hmap s w hw
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := hJ.exists_isPLHomeomorphOn_Icc_of_cycle
    (X := X) (inc := fun u e => u.1.1 ⊆ e.1.1) hX hXJ hcover hXne hp hpX hmeet hdeg hdeg₃ hend
    hend₃ (u := ⟨w, hw⟩) (e₁ := ⟨e₁, hi₁⟩) (e₂ := ⟨e₂, hi₂⟩)
    (fun h => hne (congrArg Subtype.val h)) hw₁ hw₂
  have hXw : X ⟨w, hw⟩ = c '' (J ∩ section34VertexBallImage src f₁ w) :=
    (c.injOn.image_inter hJc (hVsrc w hw)).symm
  have hXt : X ⟨w, hw⟩ ⊆ c.target := by
    rw [hXw]
    rintro _ ⟨x, hx, rfl⟩
    exact c.map_source (hJc hx.1)
  have hcell := (isPLCellOn_one_of_isPLHomeomorphOn_Icc hγ).image_chart_symm hc hXt
  have hsymmX : c.symm '' X ⟨w, hw⟩ = J ∩ section34VertexBallImage src f₁ w := by
    rw [hXw]
    exact c.symm_image_image_of_subset_source (inter_subset_left.trans hJc)
  have hsymmB : c.symm '' {γ 0, γ 1} = {pt ⟨e₁, hi₁⟩, pt ⟨e₂, hi₂⟩} := by
    rw [hγ0, hγ1, image_pair]
    change {c.symm (c (pt ⟨e₁, hi₁⟩)), c.symm (c (pt ⟨e₂, hi₂⟩))} = _
    rw [c.left_inv (hJc (hptJ _).1), c.left_inv (hJc (hptJ _).1)]
  have hbd : J ∩ section34VertexBallImage src f₁ w ∩ ⋃ e, section34SplitDiskImage src f₁ e =
      {pt ⟨e₁, hi₁⟩, pt ⟨e₂, hi₂⟩} := by
    apply Subset.antisymm
    · rintro x ⟨⟨hxJ, hxw⟩, hxE⟩
      obtain ⟨e, hxe⟩ := mem_iUnion.mp hxE
      have he := hEinc e x hxJ hxe
      have hx := hmemE ⟨e, he⟩ x hxJ hxe
      rcases huniq e he (hcut.subset_of_mem_splitDiskImage hinj hxe hxw) with h | h
      · subst h
        exact Or.inl hx
      · subst h
        exact Or.inr hx
    · rintro x (rfl | rfl)
      · exact ⟨⟨(hptJ ⟨e₁, hi₁⟩).1, hptV ⟨e₁, hi₁⟩ w hw₁⟩,
          mem_iUnion.mpr ⟨e₁, hEbdE e₁ (hptJ ⟨e₁, hi₁⟩).2⟩⟩
      · exact ⟨⟨(hptJ ⟨e₂, hi₂⟩).1, hptV ⟨e₂, hi₂⟩ w hw₂⟩,
          mem_iUnion.mpr ⟨e₂, hEbdE e₂ (hptJ ⟨e₂, hi₂⟩).2⟩⟩
  refine ⟨by rw [hbd, ← hsymmX, ← hsymmB]; exact hcell, ?_⟩
  have hXwmeet : ∀ (u : {u : Section34VertexIndex 𝒦 𝒦' // Section34Incident u.1 s.1}),
      u ≠ ⟨w, hw⟩ → ∀ x ∈ X ⟨w, hw⟩ ∩ X u, x = p ⟨e₁, hi₁⟩ ∨ x = p ⟨e₂, hi₂⟩ := by
    intro u hu x hx
    obtain ⟨e, hwe, -, rfl⟩ := hmeet ⟨w, hw⟩ u (Ne.symm hu) x hx
    rcases huniq e.1 e.2 hwe with h | h
    · left
      rw [show e = ⟨e₁, hi₁⟩ from Subtype.ext h]
    · right
      rw [show e = ⟨e₂, hi₂⟩ from Subtype.ext h]
  let F' : Set E3 := ⋃ (u : {u : Section34VertexIndex 𝒦 𝒦' // Section34Incident u.1 s.1})
    (_ : u ≠ ⟨w, hw⟩), X u
  have hF'c : IsClosed F' := isClosed_iUnion_of_finite fun u => isClosed_iUnion_of_finite
    fun _ => hX u
  have hF'J : F' ⊆ c '' J := iUnion₂_subset fun u _ => hXJ u
  have hother : ∀ e : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1},
      w.1 ⊆ e.1.1 → p e ∈ F' := by
    intro e hwe
    obtain ⟨u, u', huu, hu, hu'⟩ := hend e
    have hwu : ∃ v : {u : Section34VertexIndex 𝒦 𝒦' // Section34Incident u.1 s.1},
        v ≠ ⟨w, hw⟩ ∧ v.1.1 ⊆ e.1.1 := by
      by_cases h : u = ⟨w, hw⟩
      · exact ⟨u', fun h' => huu (h.trans h'.symm), hu'⟩
      · exact ⟨u, h, hu⟩
    obtain ⟨v, hv, hve⟩ := hwu
    exact mem_iUnion₂.mpr ⟨v, hv, (hpX v e).mpr hve⟩
  have hpe : p ⟨e₁, hi₁⟩ ≠ p ⟨e₂, hi₂⟩ := fun h => hne (congrArg Subtype.val (hp h))
  have hloc : ∀ x ∈ F', x ≠ p ⟨e₁, hi₁⟩ → x ≠ p ⟨e₂, hi₂⟩ → F' ∈ 𝓝[c '' J] x := by
    intro x hx hx₁ hx₂
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
    have hxw : x ∉ X ⟨w, hw⟩ := fun hxw => by
      rcases hXwmeet u hu x ⟨hxw, hxu⟩ with h | h
      · exact hx₁ h
      · exact hx₂ h
    refine mem_nhdsWithin.mpr ⟨(X ⟨w, hw⟩)ᶜ, (hX _).isOpen_compl, hxw, fun y hy => ?_⟩
    obtain ⟨v, hyv⟩ := mem_iUnion.mp (hcover hy.2)
    have hv : v ≠ ⟨w, hw⟩ := fun h => hy.1 (h ▸ hyv)
    exact mem_iUnion₂.mpr ⟨v, hv, hyv⟩
  have hF'pre : IsPreconnected F' := by
    rcases hJ.eq_pair_or_eq_or_exists_arc_of_mem_nhdsWithin hF'c hF'J (hother _ hw₁)
      (hother _ hw₂) hpe hloc with hpair | hall | ⟨γ', hγ', -, -⟩
    · exfalso
      refine hXne ⟨w, hw⟩ (Subset.antisymm (hXJ _) fun y hy => ?_)
      obtain ⟨v, hyv⟩ := mem_iUnion.mp (hcover hy)
      by_cases hv : v = ⟨w, hw⟩
      · exact hv ▸ hyv
      · have hyF : y ∈ F' := mem_iUnion₂.mpr ⟨v, hv, hyv⟩
        rw [hpair] at hyF
        rcases hyF with h | h
        · rw [h, ← hγ0]
          exact hγ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
        · rw [mem_singleton_iff.mp h, ← hγ1]
          exact hγ.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
    · exfalso
      have hmid : γ (1 / 2) ∈ X ⟨w, hw⟩ := hγ.bijOn.mapsTo ⟨by norm_num, by norm_num⟩
      have hmidF : γ (1 / 2) ∈ F' := by
        rw [hall]
        exact hXJ _ hmid
      obtain ⟨u, hu, hmu⟩ := mem_iUnion₂.mp hmidF
      rcases hXwmeet u hu _ ⟨hmid, hmu⟩ with h | h
      · rw [← hγ0] at h
        have := hγ.bijOn.injOn ⟨by norm_num, by norm_num⟩ ⟨le_rfl, zero_le_one⟩ h
        norm_num at this
      · rw [← hγ1] at h
        have := hγ.bijOn.injOn ⟨by norm_num, by norm_num⟩ ⟨zero_le_one, le_rfl⟩ h
        norm_num at this
    · rw [← hγ'.image_eq]
      exact isPreconnected_Icc.image γ' hγ'.isPiecewiseAffineOn.continuousOn
  have hF't : F' ⊆ c.target := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hF'J hy
    exact c.map_source (hJc hx)
  have hrest : c.symm '' F' = J ∩ ⋃ (u : Section34VertexIndex 𝒦 𝒦')
      (_ : Section34Incident u.1 s.1 ∧ u ≠ w), section34VertexBallImage src f₁ u := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.mp hz
      obtain ⟨y, hyJ, rfl⟩ := hzu.1
      rw [c.left_inv (hJc hyJ)]
      exact ⟨hyJ, mem_iUnion₂.mpr ⟨u.1, ⟨u.2, fun h => hu (Subtype.ext h)⟩,
        hback u.1 u.2 y hyJ hzu.2⟩⟩
    · rintro y ⟨hyJ, hyU⟩
      obtain ⟨u, ⟨hu, huw⟩, hyu⟩ := mem_iUnion₂.mp hyU
      refine ⟨c y, mem_iUnion₂.mpr ⟨⟨u, hu⟩, fun h => huw (congrArg Subtype.val h),
        mem_image_of_mem c hyJ, mem_image_of_mem c hyu⟩, c.left_inv (hJc hyJ)⟩
  rw [← hrest]
  exact hF'pre.image c.symm (c.continuousOn_symm.mono hF't)

end DifferentialGeometry.Topology.PiecewiseLinear
