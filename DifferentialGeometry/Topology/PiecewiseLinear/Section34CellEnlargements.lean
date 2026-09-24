/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.Connected.TwoSided
import DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphIntoMonoOfIsPLCellOn
import DifferentialGeometry.Topology.PiecewiseLinear.StageTransport
import DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Section34Cell Enlargements -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem PLPieceIn.isPLOn_conjugate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {W : Set X} (T : PLPieceIn E n X W) {τ : E → E}
    (hτ : IsPiecewiseAffineOn τ T.complex.space) (hmap : MapsTo τ T.complex.space T.complex.space) :
    IsPLOn n n (T.map ∘ τ ∘ Function.invFunOn T.map T.complex.space) W := by
  obtain ⟨R⟩ := T.exists_pLPiece
  let q := Function.invFunOn T.map T.complex.space ∘ R.piece.map
  have hq : IsPLHomeomorphOn q R.piece.complex.space T.complex.space :=
    R.piece.isPLHomeomorphOn_transition T
  have hpa : IsPiecewiseAffineOn (τ ∘ q) R.piece.complex.space := by
    have hp := hτ.comp hq.isPiecewiseAffineOn
    have hs : R.piece.complex.space ⊆ q ⁻¹' T.complex.space := hq.bijOn.mapsTo
    rwa [inter_eq_left.mpr hs] at hp
  have hpl := T.isPLOn_comp hpa (hmap.comp hq.bijOn.mapsTo)
  apply R.piece.isPLOn_of_eqOn_comp_invFunOn hpl
  intro x hx
  dsimp [q, Function.comp_def]
  rw [R.piece.bijOn.invOn_invFunOn.2 hx]

theorem bicollar_sides_of_regular_closed {X : Type*} [TopologicalSpace X]
    {C W : Set X} {ρ : X × ℝ → X} (hC : IsClosed C)
    (hregular : closure (interior C) = C) (hS : IsConnected (frontier C))
    (hW : W ∈ 𝓝ˢ (frontier C))
    (hρ : ContinuousOn ρ (frontier C ×ˢ Icc (-1 : ℝ) 1))
    (hbij : BijOn ρ (frontier C ×ˢ Icc (-1 : ℝ) 1) W)
    (hzero : ∀ x ∈ frontier C, ρ (x, 0) = x) :
    (ρ '' (frontier C ×ˢ Ico (-1 : ℝ) 0) ⊆ interior C ∧
      ρ '' (frontier C ×ˢ Ioc (0 : ℝ) 1) ⊆ Cᶜ) ∨
    (ρ '' (frontier C ×ˢ Ico (-1 : ℝ) 0) ⊆ Cᶜ ∧
      ρ '' (frontier C ×ˢ Ioc (0 : ℝ) 1) ⊆ interior C) := by
  let P := ρ '' (frontier C ×ˢ Ico (-1 : ℝ) 0)
  let Q := ρ '' (frontier C ×ˢ Ioc (0 : ℝ) 1)
  have hneg : frontier C ×ˢ Ico (-1 : ℝ) 0 ⊆ frontier C ×ˢ Icc (-1 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.le.trans zero_le_one⟩
  have hpos : frontier C ×ˢ Ioc (0 : ℝ) 1 ⊆ frontier C ×ˢ Icc (-1 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, (by norm_num : (-1 : ℝ) ≤ 0).trans hx.2.1.le, hx.2.2⟩
  have havoid (z : X × ℝ) (hz : z ∈ frontier C ×ˢ Icc (-1 : ℝ) 1)
      (ht : z.2 ≠ 0) : ρ z ∉ frontier C := by
    intro hzC
    have heq := hbij.injOn hz ⟨hzC, by norm_num, by norm_num⟩ (hzero _ hzC).symm
    exact ht (congrArg Prod.snd heq)
  have hcover : P ∪ Q = W \ frontier C := by
    apply Subset.antisymm
    · rintro y (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact ⟨hbij.mapsTo (hneg hz), havoid z (hneg hz) hz.2.2.ne⟩
      · exact ⟨hbij.mapsTo (hpos hz), havoid z (hpos hz) hz.2.1.ne'⟩
    · rintro y ⟨hyW, hyC⟩
      obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ := hbij.surjOn hyW
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [hzero x hx] at hyC
        exact hyC hx
      rcases lt_or_gt_of_ne ht0 with h | h
      · exact Or.inl ⟨(x, t), ⟨hx, ht.1, h⟩, rfl⟩
      · exact Or.inr ⟨(x, t), ⟨hx, h, ht.2⟩, rfl⟩
  have hside {A : Set X} (hA : IsPreconnected A) (hAS : A ⊆ (frontier C)ᶜ) :
      A ⊆ interior C ∨ A ⊆ Cᶜ := by
    apply hA.subset_or_subset isOpen_interior hC.isOpen_compl
      (Set.disjoint_left.mpr fun x hx hn => hn (interior_subset hx))
    intro x hx
    by_cases hxC : x ∈ C
    · left
      by_contra hxI
      exact hAS hx ⟨subset_closure hxC, hxI⟩
    · exact Or.inr hxC
  have hP := hside ((hS.prod (isConnected_Ico (by norm_num : (-1 : ℝ) < 0))).image
    ρ (hρ.mono hneg)).isPreconnected
    (fun x hx => (hcover.subset (Or.inl hx)).2)
  have hQ := hside ((hS.prod (isConnected_Ioc zero_lt_one)).image
    ρ (hρ.mono hpos)).isPreconnected
    (fun x hx => (hcover.subset (Or.inr hx)).2)
  obtain ⟨x, hx⟩ := hS.nonempty
  have hxW := mem_nhdsSet_iff_forall.mp hW x hx
  have hinside : (W ∩ interior C).Nonempty := by
    apply mem_closure_iff_nhds.mp (hregular.symm ▸ hC.frontier_subset hx) W hxW
  have houtside : (W ∩ Cᶜ).Nonempty := by
    have hxout : x ∈ closure Cᶜ := by
      rw [frontier_eq_closure_inter_closure] at hx
      exact hx.2
    exact mem_closure_iff_nhds.mp hxout W hxW
  rcases hP with hP | hP <;> rcases hQ with hQ | hQ
  · obtain ⟨y, hyW, hyC⟩ := houtside
    have hy : y ∈ P ∪ Q := hcover.symm.subset ⟨hyW, fun hy => hyC (hC.frontier_subset hy)⟩
    exact (hyC (interior_subset (hy.elim (fun hp => hP hp) (fun hq => hQ hq)))).elim
  · exact Or.inl ⟨hP, hQ⟩
  · exact Or.inr ⟨hP, hQ⟩
  · obtain ⟨y, hyW, hyC⟩ := hinside
    have hy : y ∈ P ∪ Q := hcover.symm.subset ⟨hyW, fun hy => hy.2 hyC⟩
    exact (hy.elim (fun hp => hP hp) (fun hq => hQ hq) (interior_subset hyC)).elim

theorem subset_interior_image_of_bicollar_shift {X : Type*} [TopologicalSpace X]
    {C W : Set X} {ρ : X × ℝ → X} {β : ℝ → ℝ} (f : X ≃ₜ X)
    (hW : frontier C ⊆ W) (hbij : BijOn ρ (frontier C ×ˢ Icc (-1 : ℝ) 1) W)
    (hnegative : ρ '' (frontier C ×ˢ Ico (-1 : ℝ) 0) ⊆ interior C)
    (hpositive : ρ '' (frontier C ×ˢ Ioc (0 : ℝ) 1) ⊆ Cᶜ)
    (hβ : StrictMono β) (hβzero : 0 < β 0)
    (hβsurj : SurjOn β (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1))
    (hmove : ∀ x ∈ frontier C, ∀ t ∈ Icc (-1 : ℝ) 1, f (ρ (x, t)) = ρ (x, β t))
    (hfix : EqOn f id Wᶜ) : C ⊆ interior (f '' C) := by
  have himage : f '' interior C ⊆ interior (f '' C) :=
    interior_maximal (image_mono interior_subset) (f.isOpenMap _ isOpen_interior)
  intro y hy
  apply himage
  by_cases hyW : y ∈ W
  · obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ := hbij.surjOn hyW
    have ht0 : t ≤ 0 := le_of_not_gt fun h =>
      hpositive ⟨(x, t), ⟨hx, h, ht.2⟩, rfl⟩ hy
    obtain ⟨s, hs, hst⟩ := hβsurj ht
    have hs0 : s < 0 := by
      by_contra hnot
      have hle := hβ.monotone (le_of_not_gt hnot)
      linarith
    refine ⟨ρ (x, s), hnegative ⟨(x, s), ⟨hx, hs.1, hs0⟩, rfl⟩, ?_⟩
    rw [hmove x hx s hs, hst]
  · refine ⟨y, ?_, hfix hyW⟩
    by_contra hyI
    exact hyW (hW ⟨subset_closure hy, hyI⟩)

theorem IsPLCellOn.enlargement_of_bicollar_shift
    {X : Type*} [MetricSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {C B W O : Set X} {ρ : X × ℝ → X} {β : ℝ → ℝ}
    (hC : IsPLCellOn 3 C B) (f : X ≃ₜ X) (hf : IsPL 3 3 f) (hfi : IsPL 3 3 f.symm)
    (hCO : C ⊆ O) (hWO : W ⊆ O) (hW : frontier C ⊆ W)
    (hbij : BijOn ρ (frontier C ×ˢ Icc (-1 : ℝ) 1) W)
    (hnegative : ρ '' (frontier C ×ˢ Ico (-1 : ℝ) 0) ⊆ interior C)
    (hpositive : ρ '' (frontier C ×ˢ Ioc (0 : ℝ) 1) ⊆ Cᶜ)
    (hβ : StrictMono β) (hβzero : 0 < β 0)
    (hβsurj : SurjOn β (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1))
    (hmove : ∀ x ∈ frontier C, ∀ t ∈ Icc (-1 : ℝ) 1, f (ρ (x, t)) = ρ (x, β t))
    (hfix : EqOn f id Wᶜ) :
    IsPLCellOn 3 (f '' C) (frontier (f '' C)) ∧ C ⊆ interior (f '' C) ∧ f '' C ⊆ O := by
  have hfu : IsPLHomeomorphInto 3 f univ := by
    refine ⟨fun x _ => hf x, f.injective.injOn, fun y _ => ⟨f.symm, ?_, ?_⟩⟩
    · rw [image_univ, f.surjective.range_eq]
      exact hfi y
    · exact fun x _ => f.symm_apply_apply x
  have hcell := hC.image (hfu.mono_of_isPLCellOn hC (subset_univ _))
  refine ⟨hcell.boundary_eq_frontier ▸ hcell,
    subset_interior_image_of_bicollar_shift f hW hbij hnegative hpositive hβ hβzero
      hβsurj hmove hfix, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  by_cases hxW : x ∈ W
  · apply hWO
    by_contra hnot
    have heq : f x = x := f.injective (hfix hnot)
    exact hnot (heq.symm ▸ hxW)
  · simpa only [hfix hxW, id_eq] using hCO hx

end DifferentialGeometry.Topology.PiecewiseLinear
