/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolution

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem doublePointSet_congr {X Y : Type*} {f g : X → Y} {P : Set X} (h : EqOn f g P) :
    doublePointSet f P = doublePointSet g P := by
  ext y
  constructor
  · rintro ⟨x, hx, z, hz, hxz, hfx, hfz⟩
    exact ⟨x, hx, z, hz, hxz, (h hx).symm.trans hfx, (h hz).symm.trans hfz⟩
  · rintro ⟨x, hx, z, hz, hxz, hfx, hfz⟩
    exact ⟨x, hx, z, hz, hxz, (h hx).trans hfx, (h hz).trans hfz⟩

theorem doublePointSet_comp_of_bijOn {X Y Z : Type*} {e : X → Y} {f : Y → Z} {P : Set X}
    {Q : Set Y} (he : BijOn e P Q) : doublePointSet (f ∘ e) P = doublePointSet f Q := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, z, hz, hxz, hfx, hfz⟩
    exact ⟨e x, he.mapsTo hx, e z, he.mapsTo hz, fun h => hxz (he.injOn hx hz h), hfx, hfz⟩
  · rintro y ⟨a, ha, b, hb, hab, hfa, hfb⟩
    obtain ⟨x, hx, rfl⟩ := he.surjOn ha
    obtain ⟨z, hz, rfl⟩ := he.surjOn hb
    exact ⟨x, hx, z, hz, fun h => hab (congrArg e h), hfa, hfb⟩

theorem image_doublePointSet_of_injOn {X Y Z : Type*} {f : X → Y} {g : Y → Z} {P : Set X}
    (hg : InjOn g (f '' P)) : doublePointSet (g ∘ f) P = g '' doublePointSet f P := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, z, hz, hxz, hfx, hfz⟩
    have h : f x = f z := hg ⟨x, hx, rfl⟩ ⟨z, hz, rfl⟩ (hfx.trans hfz.symm)
    exact ⟨f x, ⟨x, hx, z, hz, hxz, rfl, h.symm⟩, hfx⟩
  · rintro _ ⟨w, ⟨x, hx, z, hz, hxz, hfx, hfz⟩, rfl⟩
    exact ⟨x, hx, z, hz, hxz, congrArg g hfx, congrArg g hfz⟩

theorem spliceCore_subset_spliceCylinder : spliceCore ⊆ spliceCylinder := by
  intro p hp
  refine ⟨?_, hp.2⟩
  have h : p.1 = ((0 : ℝ), (0 : ℝ)) := hp.1
  rw [h, mem_spliceSquare]
  norm_num

theorem crossingFigure_subset_spliceCylinder : crossingFigure ⊆ spliceCylinder := by
  rintro p ⟨h | h, ht⟩
  · exact ⟨h.1, ht⟩
  · exact ⟨h.1, ht⟩

theorem spliceFigure_subset_spliceCylinder : spliceFigure ⊆ spliceCylinder := by
  rintro p ⟨h | h, ht⟩
  · exact ⟨h.1, ht⟩
  · exact ⟨h.1, ht⟩

theorem bentFigure_subset_spliceCylinder : bentFigure ⊆ spliceCylinder := by
  rintro p ⟨h | h, ht⟩
  · exact ⟨bentArcPos_subset_spliceSquare h, ht⟩
  · exact ⟨bentArcNeg_subset_spliceSquare h, ht⟩

theorem spliceSquareBoundary_prod_subset_spliceCylinder :
    spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1 ⊆ spliceCylinder := by
  rintro p ⟨h, ht⟩
  exact ⟨h.1, ht⟩

def spliceEndDisks : Set ((ℝ × ℝ) × ℝ) := spliceSquare ×ˢ ({0, 1} : Set ℝ)

theorem spliceEndDisks_subset_spliceCylinder : spliceEndDisks ⊆ spliceCylinder := by
  rintro p ⟨hp, ht⟩
  refine ⟨hp, ?_⟩
  rcases ht with h | h
  · rw [h]
    exact ⟨le_refl (0 : ℝ), zero_le_one⟩
  · rw [Set.mem_singleton_iff.mp h]
    exact ⟨zero_le_one, le_refl (1 : ℝ)⟩

theorem crossSeamResolve_snd (q : Bool × ((ℝ × ℝ) × ℝ)) : (crossSeamResolve q).2 = q.2.2 := by
  obtain ⟨b, x⟩ := q
  cases b
  · exact crossSeamResolveNeg_snd x
  · exact crossSeamResolvePos_snd x

theorem crossSeamResolve_mem_spliceEndDisks {q : Bool × ((ℝ × ℝ) × ℝ)} (hq : q ∈ bentSource)
    (hend : q.2.2 = 0 ∨ q.2.2 = 1) : crossSeamResolve q ∈ spliceEndDisks := by
  have hfig : crossSeamResolve q ∈ spliceFigure := by
    rw [← image_crossSeamResolve]
    exact ⟨q, hq, rfl⟩
  refine ⟨(spliceFigure_subset_spliceCylinder hfig).1, ?_⟩
  rw [crossSeamResolve_snd]
  rcases hend with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_singleton_iff.mpr h)

structure CrossSeamTubeCore {M : Type u} [TopologicalSpace M] (chart : (ℝ × ℝ) × ℝ → M)
    (figure double branch tube : Set M) : Prop where
  isOpen_tube : IsOpen tube
  continuousOn_chart : ContinuousOn chart spliceCylinder
  injOn_chart : InjOn chart spliceCylinder
  image_subset_tube : chart '' spliceCylinder ⊆ tube
  image_spliceCore : chart '' spliceCore = branch
  image_crossingFigure : chart '' crossingFigure = figure ∩ chart '' spliceCylinder
  double_inter_tube : double ∩ tube = branch

noncomputable def spliceEmbedding : ((ℝ × ℝ) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

def tubeWitnessSheetX : Set ((ℝ × ℝ) × ℝ) := crossingArcX ×ˢ Icc (0 : ℝ) 2

def tubeWitnessFarArcX : Set (ℝ × ℝ) := ({(4 : ℝ)} : Set ℝ) ×ˢ Icc (3 : ℝ) 5

def tubeWitnessFarArcY : Set (ℝ × ℝ) := Icc (3 : ℝ) 5 ×ˢ ({(4 : ℝ)} : Set ℝ)

def tubeWitnessFarSheetX : Set ((ℝ × ℝ) × ℝ) := tubeWitnessFarArcX ×ˢ Icc (0 : ℝ) 1

def tubeWitnessFarSheetY : Set ((ℝ × ℝ) × ℝ) := tubeWitnessFarArcY ×ˢ Icc (0 : ℝ) 1

def tubeWitnessFarCore : Set ((ℝ × ℝ) × ℝ) :=
  ({((4 : ℝ), (4 : ℝ))} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1

def tubeWitnessSurface : Set ((ℝ × ℝ) × ℝ) :=
  tubeWitnessSheetX ∪ crossingSheetY ∪ tubeWitnessFarSheetX ∪ tubeWitnessFarSheetY

def tubeWitnessDouble : Set ((ℝ × ℝ) × ℝ) := spliceCore ∪ tubeWitnessFarCore

def tubeWitnessTube : Set ((ℝ × ℝ) × ℝ) :=
  (Ioo (-2 : ℝ) 2 ×ˢ Ioo (-2 : ℝ) 2) ×ˢ Ioo (-1 : ℝ) 2

theorem tubeWitnessFarArcX_inter_tubeWitnessFarArcY :
    tubeWitnessFarArcX ∩ tubeWitnessFarArcY = {((4 : ℝ), (4 : ℝ))} := by
  ext p
  simp only [tubeWitnessFarArcX, tubeWitnessFarArcY, Set.mem_inter_iff, Set.mem_prod,
    Set.mem_singleton_iff, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, -, h2⟩
    exact Prod.ext h1 h2
  · rintro rfl
    norm_num

theorem tubeWitnessFarSheetX_inter_tubeWitnessFarSheetY :
    tubeWitnessFarSheetX ∩ tubeWitnessFarSheetY = tubeWitnessFarCore := by
  rw [tubeWitnessFarSheetX, tubeWitnessFarSheetY, Set.prod_inter_prod, Set.inter_self,
    tubeWitnessFarArcX_inter_tubeWitnessFarArcY, tubeWitnessFarCore]

theorem tubeWitnessSheetX_inter_crossingSheetY :
    tubeWitnessSheetX ∩ crossingSheetY = spliceCore := by
  have h : Icc (0 : ℝ) 2 ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 :=
    Set.inter_eq_right.mpr (Set.Icc_subset_Icc le_rfl (by norm_num))
  rw [tubeWitnessSheetX, crossingSheetY, Set.prod_inter_prod, crossingArcX_inter_crossingArcY,
    h, spliceCore]

theorem disjoint_tubeWitnessFarArc_spliceSquare :
    Disjoint (tubeWitnessFarArcX ∪ tubeWitnessFarArcY) spliceSquare := by
  rw [Set.disjoint_left]
  rintro q (h | h) hq
  · rw [mem_spliceSquare] at hq
    have h4 : q.1 = 4 := h.1
    linarith [hq.1.2]
  · rw [mem_spliceSquare] at hq
    have h4 : q.2 = 4 := h.2
    linarith [hq.2.2]

theorem disjoint_tubeWitnessNear_tubeWitnessFar :
    Disjoint (tubeWitnessSheetX ∪ crossingSheetY)
      (tubeWitnessFarSheetX ∪ tubeWitnessFarSheetY) := by
  rw [Set.disjoint_left]
  intro p hnear hfar
  have hsq : p.1 ∈ spliceSquare := by
    rcases hnear with h | h
    · exact h.1.1
    · exact h.1.1
  have hfarArc : p.1 ∈ tubeWitnessFarArcX ∪ tubeWitnessFarArcY := by
    rcases hfar with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  exact Set.disjoint_left.mp disjoint_tubeWitnessFarArc_spliceSquare hfarArc hsq

theorem tubeWitnessSurface_inter_spliceCylinder :
    tubeWitnessSurface ∩ spliceCylinder = crossingFigure := by
  ext p
  constructor
  · rintro ⟨((h | h) | h) | h, hcyl⟩
    · exact ⟨Or.inl h.1, hcyl.2⟩
    · exact ⟨Or.inr h.1, h.2⟩
    · exact absurd hcyl.1
        (Set.disjoint_left.mp disjoint_tubeWitnessFarArc_spliceSquare (Or.inl h.1))
    · exact absurd hcyl.1
        (Set.disjoint_left.mp disjoint_tubeWitnessFarArc_spliceSquare (Or.inr h.1))
  · rintro ⟨h | h, ht⟩
    · exact ⟨Or.inl (Or.inl (Or.inl ⟨h, Set.Icc_subset_Icc le_rfl (by norm_num) ht⟩)), h.1, ht⟩
    · exact ⟨Or.inl (Or.inl (Or.inr ⟨h, ht⟩)), h.1, ht⟩

theorem crossingFigure_subset_tubeWitnessSurface : crossingFigure ⊆ tubeWitnessSurface := by
  rintro p ⟨h | h, ht⟩
  · exact Or.inl (Or.inl (Or.inl ⟨h, Set.Icc_subset_Icc le_rfl (by norm_num) ht⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨h, ht⟩))

theorem spliceCore_subset_tubeWitnessDouble : spliceCore ⊆ tubeWitnessDouble :=
  Set.subset_union_left

theorem spliceCylinder_subset_tubeWitnessTube : spliceCylinder ⊆ tubeWitnessTube := by
  rintro p ⟨hsq, ht⟩
  rw [mem_spliceSquare] at hsq
  rw [Set.mem_Icc] at ht
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> constructor <;>
    linarith [hsq.1.1, hsq.1.2, hsq.2.1, hsq.2.2, ht.1, ht.2]

theorem isOpen_tubeWitnessTube : IsOpen tubeWitnessTube :=
  (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioo

theorem tubeWitnessDouble_inter_tubeWitnessTube :
    tubeWitnessDouble ∩ tubeWitnessTube = spliceCore := by
  apply Subset.antisymm
  · rintro p ⟨hd | hd, hu⟩
    · exact hd
    · exfalso
      have h4 : p.1 = ((4 : ℝ), (4 : ℝ)) := hd.1
      have hlt : p.1.1 < 2 := hu.1.1.2
      rw [h4] at hlt
      norm_num at hlt
  · intro p hp
    exact ⟨Or.inl hp,
      spliceCylinder_subset_tubeWitnessTube (spliceCore_subset_spliceCylinder hp)⟩

theorem tubeWitnessTop_mem_surface :
    (((0 : ℝ), (0 : ℝ)), (2 : ℝ)) ∈ tubeWitnessSurface := by
  refine Or.inl (Or.inl (Or.inl ⟨⟨?_, rfl⟩, ?_⟩))
  · rw [mem_spliceSquare]
    norm_num
  · rw [Set.mem_Icc]
    norm_num

theorem tubeWitnessTop_notMem_crossingFigure :
    (((0 : ℝ), (0 : ℝ)), (2 : ℝ)) ∉ crossingFigure := by
  rintro ⟨-, ht⟩
  rw [Set.mem_Icc] at ht
  norm_num at ht

theorem tubeWitnessTop_notMem_tube :
    (((0 : ℝ), (0 : ℝ)), (2 : ℝ)) ∉ tubeWitnessTube := by
  intro h
  have h2 : (((0 : ℝ), (0 : ℝ)), (2 : ℝ)).2 < 2 := h.2.2
  norm_num at h2

theorem tubeWitnessFar_mem_double :
    (((4 : ℝ), (4 : ℝ)), (0 : ℝ)) ∈ tubeWitnessDouble := by
  refine Or.inr ⟨rfl, ?_⟩
  rw [Set.mem_Icc]
  norm_num

theorem tubeWitnessFar_notMem_spliceCore :
    (((4 : ℝ), (4 : ℝ)), (0 : ℝ)) ∉ spliceCore := by
  rintro ⟨h, -⟩
  have h4 : ((4 : ℝ), (4 : ℝ)) = ((0 : ℝ), (0 : ℝ)) := h
  rw [Prod.mk.injEq] at h4
  norm_num at h4

theorem spliceEmbedding_image_ssubset {s t : Set ((ℝ × ℝ) × ℝ)} (hst : s ⊆ t)
    {p : (ℝ × ℝ) × ℝ} (hpt : p ∈ t) (hps : p ∉ s) :
    ⇑spliceEmbedding '' s ⊂ ⇑spliceEmbedding '' t := by
  rw [Set.ssubset_iff_of_subset (Set.image_mono hst)]
  refine ⟨spliceEmbedding p, ⟨p, hpt, rfl⟩, ?_⟩
  rintro ⟨q, hq, hqe⟩
  have hqp : q = p := spliceEmbedding.injective hqe
  rw [hqp] at hq
  exact hps hq

theorem spliceEmbedding_image_spliceCore_eq_inter :
    ⇑spliceEmbedding '' spliceCore =
      ⇑spliceEmbedding '' tubeWitnessSheetX ∩ ⇑spliceEmbedding '' crossingSheetY := by
  rw [← tubeWitnessSheetX_inter_crossingSheetY,
    Set.InjOn.image_inter spliceEmbedding.injective.injOn (subset_univ _) (subset_univ _)]

theorem crossSeamTubeCore_spliceEmbedding :
    CrossSeamTubeCore (M := EuclideanSpace ℝ (Fin 3)) ⇑spliceEmbedding
      (⇑spliceEmbedding '' tubeWitnessSurface) (⇑spliceEmbedding '' tubeWitnessDouble)
      (⇑spliceEmbedding '' spliceCore) (⇑spliceEmbedding '' tubeWitnessTube) where
  isOpen_tube := by
    have h : IsOpen (⇑spliceEmbedding.toHomeomorph '' tubeWitnessTube) :=
      spliceEmbedding.toHomeomorph.isOpenMap _ isOpen_tubeWitnessTube
    exact h
  continuousOn_chart := spliceEmbedding.continuous.continuousOn
  injOn_chart := spliceEmbedding.injective.injOn
  image_subset_tube := Set.image_mono spliceCylinder_subset_tubeWitnessTube
  image_spliceCore := rfl
  image_crossingFigure := by
    rw [← Set.InjOn.image_inter spliceEmbedding.injective.injOn (subset_univ _)
      (subset_univ _), tubeWitnessSurface_inter_spliceCylinder]
  double_inter_tube := by
    rw [← Set.InjOn.image_inter spliceEmbedding.injective.injOn (subset_univ _)
      (subset_univ _), tubeWitnessDouble_inter_tubeWitnessTube]

theorem spliceEmbedding_image_crossingFigure_ssubset_surface :
    ⇑spliceEmbedding '' crossingFigure ⊂ ⇑spliceEmbedding '' tubeWitnessSurface :=
  spliceEmbedding_image_ssubset crossingFigure_subset_tubeWitnessSurface
    tubeWitnessTop_mem_surface tubeWitnessTop_notMem_crossingFigure

theorem spliceEmbedding_surface_not_subset_tube :
    ¬⇑spliceEmbedding '' tubeWitnessSurface ⊆ ⇑spliceEmbedding '' tubeWitnessTube := by
  intro h
  obtain ⟨q, hq, hqe⟩ := h ⟨_, tubeWitnessTop_mem_surface, rfl⟩
  have hqp : q = (((0 : ℝ), (0 : ℝ)), (2 : ℝ)) := spliceEmbedding.injective hqe
  rw [hqp] at hq
  exact tubeWitnessTop_notMem_tube hq

theorem spliceEmbedding_image_spliceCore_ssubset_double :
    ⇑spliceEmbedding '' spliceCore ⊂ ⇑spliceEmbedding '' tubeWitnessDouble :=
  spliceEmbedding_image_ssubset spliceCore_subset_tubeWitnessDouble
    tubeWitnessFar_mem_double tubeWitnessFar_notMem_spliceCore

structure CrossSeamTubeData {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) (U : Set M) where
  chart : (ℝ × ℝ) × ℝ → M
  isTube : CrossSeamTubeCore chart (D '' D.domain) (doublePointSet D D.domain)
    (hD.singularSet.branchCarrier c) U

namespace CrossSeamTubeData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch}

theorem branchCarrier_subset_image_spliceCylinder (T : CrossSeamTubeData hD c U) :
    hD.singularSet.branchCarrier c ⊆ T.chart '' spliceCylinder := by
  rw [← T.isTube.image_spliceCore]
  exact Set.image_mono spliceCore_subset_spliceCylinder

theorem branchCarrier_subset_tube (T : CrossSeamTubeData hD c U) :
    hD.singularSet.branchCarrier c ⊆ U :=
  T.branchCarrier_subset_image_spliceCylinder.trans T.isTube.image_subset_tube

theorem branchCarrier_subset_interior_tube (T : CrossSeamTubeData hD c U) :
    hD.singularSet.branchCarrier c ⊆ interior U := by
  rw [T.isTube.isOpen_tube.interior_eq]
  exact T.branchCarrier_subset_tube

theorem isCompact_image_spliceCylinder (T : CrossSeamTubeData hD c U) :
    IsCompact (T.chart '' spliceCylinder) :=
  isHPolytope_spliceCylinder.isPolyhedron.isCompact.image_of_continuousOn
    T.isTube.continuousOn_chart

theorem doublePointSet_sdiff_branchCarrier (T : CrossSeamTubeData hD c U) :
    doublePointSet D D.domain \ hD.singularSet.branchCarrier c =
      doublePointSet D D.domain \ U := by
  apply Subset.antisymm
  · rintro y ⟨hy, hyb⟩
    refine ⟨hy, fun hyU => hyb ?_⟩
    rw [← T.isTube.double_inter_tube]
    exact ⟨hy, hyU⟩
  · rintro y ⟨hy, hyU⟩
    exact ⟨hy, fun hyb => hyU (T.branchCarrier_subset_tube hyb)⟩

theorem doublePointSet_inter_image_spliceCylinder (T : CrossSeamTubeData hD c U) :
    doublePointSet D D.domain ∩ T.chart '' spliceCylinder =
      hD.singularSet.branchCarrier c := by
  apply Subset.antisymm
  · rintro y ⟨hy, hcyl⟩
    rw [← T.isTube.double_inter_tube]
    exact ⟨hy, T.isTube.image_subset_tube hcyl⟩
  · intro y hy
    refine ⟨?_, T.branchCarrier_subset_image_spliceCylinder hy⟩
    rw [← T.isTube.double_inter_tube] at hy
    exact hy.1

theorem doublePointSet_sdiff_image_spliceCylinder (T : CrossSeamTubeData hD c U) :
    doublePointSet D D.domain \ hD.singularSet.branchCarrier c =
      doublePointSet D D.domain \ T.chart '' spliceCylinder := by
  apply Subset.antisymm
  · rintro y ⟨hy, hyb⟩
    refine ⟨hy, fun hcyl => hyb ?_⟩
    rw [← T.doublePointSet_inter_image_spliceCylinder]
    exact ⟨hy, hcyl⟩
  · rintro y ⟨hy, hcyl⟩
    exact ⟨hy, fun hyb => hcyl (T.branchCarrier_subset_image_spliceCylinder hyb)⟩

end CrossSeamTubeData

structure CrossSeamRegluedData {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B U : Set M}
    {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) (G : SingularTwoCell M) where
  cell : SingularTwoCell M
  domain_eq : cell.domain = G.domain
  coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)
  bijOn_coord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource
  reglued_eq : EqOn G (T.chart ∘ crossSeamInclude ∘ coord)
    (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
  resolved_eq : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
    (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
  eqOn_compl : EqOn cell G (G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder))

namespace CrossSeamRegluedData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D G : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch} {T : CrossSeamTubeData hD c U}

theorem image_cell_tube (R : CrossSeamRegluedData T G) :
    R.cell '' (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) = T.chart '' spliceFigure := by
  have h : R.cell '' (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
      = (T.chart ∘ crossSeamResolve ∘ R.coord) ''
        (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) :=
    Set.image_congr fun x hx => R.resolved_eq hx
  rw [h, Set.image_comp, Set.image_comp, R.bijOn_coord.image_eq, image_crossSeamResolve]

theorem mapsTo_cell_tube (R : CrossSeamRegluedData T G) :
    MapsTo R.cell (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
      (T.chart '' spliceCylinder) := by
  intro x hx
  have h : R.cell x ∈ R.cell '' (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) := ⟨x, hx, rfl⟩
  rw [R.image_cell_tube] at h
  exact Set.image_mono spliceFigure_subset_spliceCylinder h

theorem injOn_cell_tube (R : CrossSeamRegluedData T G) :
    InjOn R.cell (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) := by
  intro x hx z hz hxz
  have hxm : R.coord x ∈ bentSource := R.bijOn_coord.mapsTo hx
  have hzm : R.coord z ∈ bentSource := R.bijOn_coord.mapsTo hz
  have hxs : crossSeamResolve (R.coord x) ∈ spliceFigure := by
    rw [← image_crossSeamResolve]
    exact ⟨_, hxm, rfl⟩
  have hzs : crossSeamResolve (R.coord z) ∈ spliceFigure := by
    rw [← image_crossSeamResolve]
    exact ⟨_, hzm, rfl⟩
  rw [R.resolved_eq hx, R.resolved_eq hz] at hxz
  simp only [Function.comp_apply] at hxz
  have hmodel : crossSeamResolve (R.coord x) = crossSeamResolve (R.coord z) :=
    T.isTube.injOn_chart (spliceFigure_subset_spliceCylinder hxs)
      (spliceFigure_subset_spliceCylinder hzs) hxz
  exact R.bijOn_coord.injOn hx hz (injOn_crossSeamResolve hxm hzm hmodel)

theorem doublePointSet_cell_tube (R : CrossSeamRegluedData T G) :
    doublePointSet R.cell (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) = ∅ :=
  (doublePointSet_eq_empty_iff_injOn _ _).mpr R.injOn_cell_tube

theorem doublePointSet_reglued_tube (R : CrossSeamRegluedData T G) :
    doublePointSet G (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) =
      hD.singularSet.branchCarrier c := by
  have hinj : InjOn T.chart (crossSeamInclude '' bentSource) := by
    rw [image_crossSeamInclude]
    exact T.isTube.injOn_chart.mono bentFigure_subset_spliceCylinder
  have hcongr : doublePointSet G (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
      = doublePointSet ((T.chart ∘ crossSeamInclude) ∘ R.coord)
        (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) :=
    doublePointSet_congr R.reglued_eq
  rw [hcongr, doublePointSet_comp_of_bijOn R.bijOn_coord,
    image_doublePointSet_of_injOn hinj, doublePointSet_crossSeamInclude,
    T.isTube.image_spliceCore]

theorem cell_notMem_tube (R : CrossSeamRegluedData T G) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder)) :
    R.cell x ∉ T.chart '' spliceCylinder := by
  rw [R.eqOn_compl hx]
  exact hx.2

theorem mem_tube_or_notMem_tube (G : SingularTwoCell M) (U : Set M)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ G.domain) :
    x ∈ G.domain ∩ ⇑G ⁻¹' U ∨ x ∈ G.domain \ ⇑G ⁻¹' U := by
  by_cases h : G x ∈ U
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr ⟨hx, h⟩

theorem doublePointSet_cell_eq (R : CrossSeamRegluedData T G)
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder) :
    doublePointSet R.cell R.cell.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c := by
  rw [T.doublePointSet_sdiff_image_spliceCylinder, ← hGD, R.domain_eq]
  apply Subset.antisymm
  · rintro y ⟨x, hx, z, hz, hxz, hyx, hyz⟩
    rcases mem_tube_or_notMem_tube G (T.chart '' spliceCylinder) hx with hxV | hxW <;>
      rcases mem_tube_or_notMem_tube G (T.chart '' spliceCylinder) hz with hzV | hzW
    · exact absurd (R.injOn_cell_tube hxV hzV (hyx.trans hyz.symm)) hxz
    · exfalso
      have h1 : y ∈ T.chart '' spliceCylinder := by
        rw [← hyx]; exact R.mapsTo_cell_tube hxV
      have h2 : y ∉ T.chart '' spliceCylinder := by
        rw [← hyz]; exact R.cell_notMem_tube hzW
      exact h2 h1
    · exfalso
      have h1 : y ∈ T.chart '' spliceCylinder := by
        rw [← hyz]; exact R.mapsTo_cell_tube hzV
      have h2 : y ∉ T.chart '' spliceCylinder := by
        rw [← hyx]; exact R.cell_notMem_tube hxW
      exact h2 h1
    · refine ⟨⟨x, hx, z, hz, hxz, ?_, ?_⟩, ?_⟩
      · rw [← R.eqOn_compl hxW]; exact hyx
      · rw [← R.eqOn_compl hzW]; exact hyz
      · rw [← hyx]; exact R.cell_notMem_tube hxW
  · rintro y ⟨⟨x, hx, z, hz, hxz, hyx, hyz⟩, hyU⟩
    have hxU : G x ∉ T.chart '' spliceCylinder := by rw [hyx]; exact hyU
    have hzU : G z ∉ T.chart '' spliceCylinder := by rw [hyz]; exact hyU
    exact ⟨x, hx, z, hz, hxz, (R.eqOn_compl ⟨hx, hxU⟩).trans hyx,
      (R.eqOn_compl ⟨hz, hzU⟩).trans hyz⟩

theorem image_cell_subset (R : CrossSeamRegluedData T G)
    (hGim : G '' G.domain ⊆ D '' D.domain) :
    R.cell '' R.cell.domain ⊆ D '' D.domain ∪ U := by
  rw [R.domain_eq]
  rintro _ ⟨x, hx, rfl⟩
  rcases mem_tube_or_notMem_tube G (T.chart '' spliceCylinder) hx with hxV | hxW
  · exact Or.inr (T.isTube.image_subset_tube (R.mapsTo_cell_tube hxV))
  · exact Or.inl (hGim ⟨x, hx, (R.eqOn_compl hxW).symm⟩)

theorem image_cell_inter_lateral (R : CrossSeamRegluedData T G) :
    R.cell '' R.cell.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) =
      D '' D.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) := by
  have hlat : T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) ⊆ T.chart '' spliceCylinder :=
    Set.image_mono spliceSquareBoundary_prod_subset_spliceCylinder
  have hleft : R.cell '' R.cell.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1)
      = T.chart '' spliceFigure ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
      rw [R.domain_eq] at hx
      rcases mem_tube_or_notMem_tube G (T.chart '' spliceCylinder) hx with hxV | hxW
      · refine ⟨?_, hy⟩
        rw [← R.image_cell_tube]
        exact ⟨x, hxV, rfl⟩
      · exact absurd (hlat hy) (R.cell_notMem_tube hxW)
    · rintro y ⟨hy1, hy2⟩
      rw [← R.image_cell_tube] at hy1
      obtain ⟨x, hx, rfl⟩ := hy1
      exact ⟨⟨x, by rw [R.domain_eq]; exact hx.1, rfl⟩, hy2⟩
  have hright : D '' D.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1)
      = T.chart '' crossingFigure ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) := by
    rw [T.isTube.image_crossingFigure, Set.inter_assoc, Set.inter_eq_right.mpr hlat]
  rw [hleft, hright,
    ← Set.InjOn.image_inter T.isTube.injOn_chart spliceFigure_subset_spliceCylinder
      spliceSquareBoundary_prod_subset_spliceCylinder,
    ← Set.InjOn.image_inter T.isTube.injOn_chart crossingFigure_subset_spliceCylinder
      spliceSquareBoundary_prod_subset_spliceCylinder,
    crossingFigure_inter_lateral_eq_spliceFigure_inter_lateral]

end CrossSeamRegluedData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D G : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch} {T : CrossSeamTubeData hD c U}

theorem exists_resolved_cell_of_tube (R : CrossSeamRegluedData T G)
    (hnormal : NormalSingularCellData R.cell BdM B)
    (hGim : G '' G.domain ⊆ D '' D.domain)
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder) :
    ∃ (cell : SingularTwoCell M) (_hcell : NormalSingularCellData cell BdM B),
      doublePointSet cell cell.domain =
          doublePointSet D D.domain \ hD.singularSet.branchCarrier c ∧
        cell '' cell.domain ⊆ D '' D.domain ∪ U :=
  ⟨R.cell, hnormal, R.doublePointSet_cell_eq hGD, R.image_cell_subset hGim⟩

def crossSeamResolutionDataOfTube (R : CrossSeamRegluedData T G)
    (hnormal : NormalSingularCellData R.cell BdM B)
    (hGim : G '' G.domain ⊆ D '' D.domain)
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder)
    (e : hnormal.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c})
    (he : ∀ b, hnormal.singularSet.branchCarrier b =
      hD.singularSet.branchCarrier (e b).1) :
    CrossSeamResolutionData hD c U where
  cell := R.cell
  normal := hnormal
  doublePointSet_eq := R.doublePointSet_cell_eq hGD
  branchEquiv := e
  branchCarrier_eq := he
  image_subset := R.image_cell_subset hGim

theorem complexity_lt_of_tube (R : CrossSeamRegluedData T G)
    (hnormal : NormalSingularCellData R.cell BdM B)
    (hGim : G '' G.domain ⊆ D '' D.domain)
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder)
    (e : hnormal.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c})
    (he : ∀ b, hnormal.singularSet.branchCarrier b =
      hD.singularSet.branchCarrier (e b).1) :
    hnormal.singularSet.complexity < hD.singularSet.complexity :=
  (crossSeamResolutionDataOfTube R hnormal hGim hGD e he).complexity_lt

def IsCrossSeamTubeProducer (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  ∀ (D : SingularTwoCell M) (BdM B : Set M) (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch), hD.singularSet.IsBoundaryBranch c →
    ∃ U : Set M, Nonempty (CrossSeamTubeData hD c U)

end DifferentialGeometry.Topology.PiecewiseLinear
