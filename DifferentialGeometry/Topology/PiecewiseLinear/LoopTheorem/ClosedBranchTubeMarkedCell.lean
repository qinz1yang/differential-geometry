/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeCapFix

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_tubeCellSphere_of_marked {S D₀ D₁ : Set E} {y₀ y₁ : E}
    {T : Fin 4 → Set E} {γ : Fin 4 → ℝ → E} {q₀ q₁ : (Fin 3 → ℝ) → E} (hS : IsPLSphere 2 S)
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (T i)) (hγzero : ∀ i, γ i 0 = y₀)
    (hγone : ∀ i, γ i 1 = y₁) (hTS : ∀ i, T i ⊆ S)
    (hTT : ∀ i j, i ≠ j → T i ∩ T j = {y₀, y₁})
    (hsep : ∀ i : Fin 4, ∀ U ⊆ S \ (T i ∪ T (i + 2)), IsPreconnected U →
      (U ∩ T (i + 1)).Nonempty → (U ∩ T (i + 3)).Nonempty → False)
    (hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hq₁ : IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁) (hD₀S : D₀ ⊆ S) (hD₁S : D₁ ⊆ S)
    (hdis : Disjoint D₀ D₁) (hb₀ : ∀ i, q₀ '' stdSimplexBoundary 2 ∩ T i = {γ i (1 / 4)})
    (hb₁ : ∀ i, q₁ '' stdSimplexBoundary 2 ∩ T i = {γ i (3 / 4)}) (hy₀ : y₀ ∈ D₀)
    (hy₁ : y₁ ∈ D₁) :
    ∃ g : E → (ℝ × ℝ) × ℝ, IsPLHomeomorphOn g S tubeCellSphere ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) 1, g (γ i t) = tubeMeridianParam (fourSpokeModelLeaf i) t) ∧
        g '' D₀ = spliceSquare ×ˢ ({0} : Set ℝ) ∧ g '' D₁ = spliceSquare ×ˢ ({1} : Set ℝ) := by
  have hinv : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, Function.invFunOn (γ i) (Icc 0 1) (γ i t) = t :=
    fun i t ht => (hγ i).bijOn.invOn_invFunOn.1 ht
  obtain ⟨g₁, hg₁, -, -, hg₁t, hg₁T⟩ := exists_isPLHomeomorphOn_of_fourArcSphere hS
    isPLSphere_tubeCellSphere hγ hγzero hγone hTS tubeCellArc_subset_tubeCellSphere hTT
    (fun i j hij => tubeCellArc_inter hij) hsep tubeCellArc_sep (π := Equiv.refl (Fin 4))
    (fun _ => rfl)
    (t := fun i => tubeMeridianParam (fourSpokeModelLeaf i) ∘ Function.invFunOn (γ i) (Icc 0 1))
    (fun i => (hγ i).symm.trans (isPLHomeomorphOn_tubeCellArc i))
    (fun i => by
      rw [← hγzero i, Function.comp_apply, hinv i 0 ⟨le_rfl, zero_le_one⟩,
        tubeMeridianParam_zero])
    (fun i => by
      rw [← hγone i, Function.comp_apply, hinv i 1 ⟨zero_le_one, le_rfl⟩,
        tubeMeridianParam_one])
  have hg₁T' : ∀ k, g₁ '' T k = tubeCellArc k := hg₁T
  have hg₁γ : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
      g₁ (γ i t) = tubeMeridianParam (fourSpokeModelLeaf i) t := by
    intro i t ht
    rw [hg₁t i ((hγ i).bijOn.mapsTo ht)]
    simp only [Function.comp_apply, hinv i t ht]
  have hpolyD : ∀ {q : (Fin 3 → ℝ) → E} {D : Set E},
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D → D ⊆ S →
        IsPLHomeomorphOn (g₁ ∘ q) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (g₁ '' D) := fun hq hD =>
    hq.trans (hg₁.restrict (IsPLBall.isPolyhedron ⟨_, hq⟩) hD)
  have hbd : ∀ {q : (Fin 3 → ℝ) → E} {D : Set E},
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D → D ⊆ S → ∀ s ∈ Icc (0 : ℝ) 1,
        (∀ i, q '' stdSimplexBoundary 2 ∩ T i = {γ i s}) → ∀ k,
          (g₁ ∘ q) '' stdSimplexBoundary 2 ∩ tubeCellArc k =
            {tubeMeridianParam (fourSpokeModelLeaf k) s} := by
    intro q D hq hD s hs hb k
    have hsub : q '' stdSimplexBoundary 2 ⊆ S := by
      refine subset_trans ?_ hD
      rw [← hq.image_eq]
      exact image_mono fun x hx => hx.1
    rw [image_comp, ← hg₁T' k, ← hg₁.bijOn.injOn.image_inter hsub (hTS k), hb k,
      image_singleton, hg₁γ k s hs]
  have hΔdis : Disjoint (g₁ '' D₀) (g₁ '' D₁) := by
    rw [disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hyx' := hg₁.bijOn.injOn (hD₁S hy) (hD₀S hx) hyx
    rw [hyx'] at hy
    exact disjoint_left.mp hdis hx hy
  have hy₀' : g₁ y₀ = ((0 : ℝ × ℝ), (0 : ℝ)) := by
    rw [← hγzero 0, hg₁γ 0 0 ⟨le_rfl, zero_le_one⟩, tubeMeridianParam_zero]
  have hy₁' : g₁ y₁ = ((0 : ℝ × ℝ), (1 : ℝ)) := by
    rw [← hγone 0, hg₁γ 0 1 ⟨zero_le_one, le_rfl⟩, tubeMeridianParam_one]
  obtain ⟨h, hh, hhid, hh₀, hh₁⟩ := exists_tubeCellSphere_capFix (hpolyD hq₀ hD₀S)
    (hpolyD hq₁ hD₁S) ((image_mono hD₀S).trans hg₁.image_eq.subset)
    ((image_mono hD₁S).trans hg₁.image_eq.subset) hΔdis
    (fun k => by
      rw [hbd hq₀ hD₀S (1 / 4) ⟨by norm_num, by norm_num⟩ hb₀ k, tubeMeridianParam_quarter])
    (fun k => by
      rw [hbd hq₁ hD₁S (3 / 4) ⟨by norm_num, by norm_num⟩ hb₁ k,
        tubeMeridianParam_threeQuarter])
    ⟨y₀, hy₀, hy₀'⟩ ⟨y₁, hy₁, hy₁'⟩
  refine ⟨h ∘ g₁, hg₁.trans hh, ?_, ?_, ?_⟩
  · intro i t ht
    change h (g₁ (γ i t)) = _
    rw [hg₁γ i t ht]
    exact hhid i ⟨t, ht, rfl⟩
  · rw [image_comp, hh₀]
  · rw [image_comp, hh₁]

theorem exists_isPLHomeomorphOn_spliceCylinder_of_marked {c : E}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (hK : IsConeBase c K)
    {D₀ D₁ : Set E} {y₀ y₁ : E} {T : Fin 4 → Set E} {γ : Fin 4 → ℝ → E}
    {q₀ q₁ : (Fin 3 → ℝ) → E} (hS : IsPLSphere 2 K.space)
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (T i)) (hγzero : ∀ i, γ i 0 = y₀)
    (hγone : ∀ i, γ i 1 = y₁) (hTS : ∀ i, T i ⊆ K.space)
    (hTT : ∀ i j, i ≠ j → T i ∩ T j = {y₀, y₁})
    (hsep : ∀ i : Fin 4, ∀ U ⊆ K.space \ (T i ∪ T (i + 2)), IsPreconnected U →
      (U ∩ T (i + 1)).Nonempty → (U ∩ T (i + 3)).Nonempty → False)
    (hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hq₁ : IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁) (hD₀S : D₀ ⊆ K.space)
    (hD₁S : D₁ ⊆ K.space) (hdis : Disjoint D₀ D₁)
    (hb₀ : ∀ i, q₀ '' stdSimplexBoundary 2 ∩ T i = {γ i (1 / 4)})
    (hb₁ : ∀ i, q₁ '' stdSimplexBoundary 2 ∩ T i = {γ i (3 / 4)}) (hy₀ : y₀ ∈ D₀)
    (hy₁ : y₁ ∈ D₁) :
    ∃ G : (ℝ × ℝ) × ℝ → E, IsPLHomeomorphOn G spliceCylinder (coneSet c K.space) ∧
      G ((0 : ℝ × ℝ), (1 / 2 : ℝ)) = c ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) 1, G (tubeMeridianParam (fourSpokeModelLeaf i) t) = γ i t) ∧
      (∀ i, G '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1) =
        coneSet c (T i)) ∧
      G '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) = coneSet c {y₀, y₁} ∧
      G '' (spliceSquare ×ˢ ({0} : Set ℝ)) = D₀ ∧
      G '' (spliceSquare ×ˢ ({1} : Set ℝ)) = D₁ ∧ G '' tubeCellSphere = K.space := by
  classical
  obtain ⟨g, hg, hgγ, hg₀, hg₁⟩ := exists_isPLHomeomorphOn_tubeCellSphere_of_marked hS hγ
    hγzero hγone hTS hTT hsep hq₀ hq₁ hD₀S hD₁S hdis hb₀ hb₁ hy₀ hy₁
  obtain ⟨K₀, hK₀fin, hK₀S, hK₀, hK₀C⟩ := exists_tubeCellSphere_coneBase
  have : Finite K₀.faces := hK₀fin.to_subtype
  have hginv : IsPLHomeomorphOn (Function.invFunOn g K.space) K₀.space K.space := by
    rw [hK₀S]
    exact hg.symm
  obtain ⟨G, hG, hGg, hGc, -, hGcone⟩ := exists_isPLHomeomorphOn_coneComplex_pair hK₀ hK hginv
  rw [hK₀C, coneComplex_space_eq_coneSet] at hG
  have hleft : LeftInvOn (Function.invFunOn g K.space) g K.space :=
    hg.bijOn.invOn_invFunOn.1
  have hgT : ∀ i, g '' T i = tubeCellArc i := by
    intro i
    rw [← (hγ i).image_eq, image_image]
    exact image_congr (hgγ i)
  have hginvT : ∀ i, Function.invFunOn g K.space '' tubeCellArc i = T i := by
    intro i
    rw [← hgT i]
    exact (hleft.mono (hTS i)).image_image
  have hsphere : ∀ {X : Set ((ℝ × ℝ) × ℝ)}, X ⊆ tubeCellSphere → X ⊆ K₀.space := by
    intro X hX
    rw [hK₀S]
    exact hX
  have hgy₀ : g y₀ = ((0 : ℝ × ℝ), (0 : ℝ)) := by
    rw [← hγzero 0, hgγ 0 0 ⟨le_rfl, zero_le_one⟩, tubeMeridianParam_zero]
  have hgy₁ : g y₁ = ((0 : ℝ × ℝ), (1 : ℝ)) := by
    rw [← hγone 0, hgγ 0 1 ⟨zero_le_one, le_rfl⟩, tubeMeridianParam_one]
  have hy₀S : y₀ ∈ K.space := hγzero 0 ▸ hTS 0 ((hγ 0).bijOn.mapsTo ⟨le_rfl, zero_le_one⟩)
  have hy₁S : y₁ ∈ K.space := hγone 0 ▸ hTS 0 ((hγ 0).bijOn.mapsTo ⟨zero_le_one, le_rfl⟩)
  have hface : ∀ {z : ℝ}, z = 0 ∨ z = 1 → spliceSquare ×ˢ ({z} : Set ℝ) ⊆ K₀.space :=
    fun hz => hsphere fun p hp => mem_tubeCellSphere_iff.mpr (Or.inl ⟨hp.1, by
      rcases hz with rfl | rfl
      · exact Or.inl hp.2
      · exact Or.inr hp.2⟩)
  refine ⟨G, hG, hGc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i t ht
    rw [hGg (hsphere (tubeCellArc_subset_tubeCellSphere i) ⟨t, ht, rfl⟩), ← hgγ i t ht,
      hleft ((hTS i) ((hγ i).bijOn.mapsTo ht))]
  · intro i
    rw [← coneSet_tubeMeridian]
    exact (hGcone (tubeCellArc i) (hsphere (tubeCellArc_subset_tubeCellSphere i))).trans
      (congrArg (coneSet c) (hginvT i))
  · rw [← coneSet_tubeCellPoles, hGcone _ (hsphere fun p hp => by
      rcases hp with rfl | rfl
      · exact tubeCellPole_mem_tubeCellSphere (Or.inl rfl)
      · exact tubeCellPole_mem_tubeCellSphere (Or.inr rfl)), image_pair, ← hgy₀, ← hgy₁,
      hleft hy₀S, hleft hy₁S]
  · rw [(hGg.mono (hface (Or.inl rfl))).image_eq, ← hg₀, (hleft.mono hD₀S).image_image]
  · rw [(hGg.mono (hface (Or.inr rfl))).image_eq, ← hg₁, (hleft.mono hD₁S).image_image]
  · rw [← hK₀S, hGg.image_eq, hginv.image_eq]

end DifferentialGeometry.Topology.PiecewiseLinear
