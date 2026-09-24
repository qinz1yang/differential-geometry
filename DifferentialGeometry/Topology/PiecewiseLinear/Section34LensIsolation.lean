/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.LocallyFiniteSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexScales
import Mathlib.Topology.MetricSpace.Thickening

/-! # Section34Lens Isolation -/

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_pos_cthickening_inter_cthickening_subset {X : Type*}
    [PseudoEMetricSpace X] {A B O : Set X} (hA : IsCompact A) (hB : IsClosed B)
    (hO : IsOpen O) (hAB : A ∩ B ⊆ O) :
    ∃ δ : ℝ, 0 < δ ∧ cthickening δ A ∩ cthickening δ B ⊆ O := by
  have hd : Disjoint (A \ O) B := by
    rw [Set.disjoint_left]
    exact fun x hxA hxB => hxA.2 (hAB ⟨hxA.1, hxB⟩)
  obtain ⟨r, hr, hdr⟩ := hd.exists_cthickenings (hA.diff hO) hB
  have hAO : A ⊆ O ∪ (cthickening r B)ᶜ := by
    intro x hxA
    by_cases hxO : x ∈ O
    · exact Or.inl hxO
    · exact Or.inr (Set.disjoint_left.mp hdr
        (self_subset_cthickening (A \ O) ⟨hxA, hxO⟩))
  obtain ⟨s, hs, hAs⟩ := hA.exists_cthickening_subset_open
    (hO.union isClosed_cthickening.isOpen_compl) hAO
  refine ⟨min s r, lt_min hs hr, ?_⟩
  intro x hx
  rcases hAs (cthickening_mono (min_le_left s r) A hx.1) with hxO | hxB
  · exact hxO
  · exact (hxB (cthickening_mono (min_le_right s r) B hx.2)).elim

theorem exists_locallyFinite_disjoint_cthickening_intersections {X V E : Type*} [MetricSpace X]
    (A : V → Set X) (ends : E → V × V) (hA : ∀ v, IsCompact (A v))
    {Ω : Set X} (hΩ : IsOpen Ω) (hAΩ : ∀ v, A v ⊆ Ω)
    (hlf : LocallyFinite fun e =>
      (Subtype.val : Ω → X) ⁻¹' (A (ends e).1 ∩ A (ends e).2))
    (hdisj : ∀ e d, e ≠ d →
      Disjoint (A (ends e).1 ∩ A (ends e).2) (A (ends d).1 ∩ A (ends d).2)) :
    ∃ (O : E → Set X) (δ : E → ℝ),
      (∀ e, IsOpen (O e)) ∧
      LocallyFinite (fun e => (Subtype.val : Ω → X) ⁻¹' O e) ∧
      (∀ e, A (ends e).1 ∩ A (ends e).2 ⊆ O e) ∧
      (∀ e, O e ⊆ Ω) ∧
      (∀ e d, e ≠ d → Disjoint (O e) (O d)) ∧
      (∀ e, 0 < δ e) ∧
      ∀ e, cthickening (δ e) (A (ends e).1) ∩
        cthickening (δ e) (A (ends e).2) ⊆ O e := by
  let L : E → Set Ω := fun e =>
    (Subtype.val : Ω → X) ⁻¹' (A (ends e).1 ∩ A (ends e).2)
  have hcl : ∀ e, IsClosed (L e) := fun e =>
    ((hA (ends e).1).isClosed.inter (hA (ends e).2).isClosed).preimage
      continuous_subtype_val
  have hLd : Pairwise (fun e d => Disjoint (L e) (L d)) := fun e d hed =>
    (hdisj e d hed).preimage Subtype.val
  obtain ⟨V, hVo, hLV, -, hVlf, hVd⟩ :=
    DifferentialGeometry.Topology.exists_locallyFinite_pairwise_disjoint_open_supersets
      L hcl hlf hLd isOpen_univ (fun _ => subset_univ _)
  let O : E → Set X := fun e => Subtype.val '' V e
  have hOo : ∀ e, IsOpen (O e) := fun e => hΩ.isOpenMap_subtype_val _ (hVo e)
  have hAO : ∀ e, A (ends e).1 ∩ A (ends e).2 ⊆ O e := by
    intro e x hx
    exact ⟨⟨x, hAΩ (ends e).1 hx.1⟩, hLV e hx, rfl⟩
  have hOlf : LocallyFinite fun e => (Subtype.val : Ω → X) ⁻¹' O e := by
    simpa only [O, preimage_image_eq _ Subtype.val_injective] using hVlf
  have hOd : ∀ e d, e ≠ d → Disjoint (O e) (O d) := fun e d hed =>
    (Set.disjoint_image_iff Subtype.val_injective).mpr (hVd hed)
  choose δ hδ hδO using fun e => exists_pos_cthickening_inter_cthickening_subset
    (hA (ends e).1) (hA (ends e).2).isClosed (hOo e) (hAO e)
  refine ⟨O, δ, hOo, hOlf, hAO, ?_, hOd, hδ, hδO⟩
  rintro e x ⟨y, -, rfl⟩
  exact y.property

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  {M₂ : Type u} [MetricSpace M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}

theorem exists_section34_vertex_scales_with_isolated_overlaps
    (h : M₁ → M₂) (Cp : Section34VertexIndex 𝒦 𝒦' → Set M₁)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (hends : ∀ e, (e.1 : Set Ea) =
      ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (hA : ∀ w, IsCompact (h '' Cp w)) {Ω : Set M₂} (hΩ : IsOpen Ω)
    (hAΩ : ∀ w, h '' Cp w ⊆ Ω)
    (hlf : LocallyFinite fun e => (Subtype.val : Ω → M₂) ⁻¹'
      ((h '' Cp (ends e).1) ∩ (h '' Cp (ends e).2)))
    (hdisj : ∀ e d, e ≠ d →
      Disjoint ((h '' Cp (ends e).1) ∩ (h '' Cp (ends e).2))
        ((h '' Cp (ends d).1) ∩ (h '' Cp (ends d).2)))
    (cap : Section34VertexIndex 𝒦 𝒦' → ℝ) (hcap : ∀ w, 0 < cap w)
    (margin : Section34EdgeIndex 𝒦 𝒦' → ℝ) (hmargin : ∀ e, 0 < margin e) :
    ∃ ε : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < ε w) ∧ (∀ w, ε w < cap w) ∧
      (∀ e, ε (ends e).1 + ε (ends e).2 < margin e) ∧
      ∀ e d, e ≠ d →
        Disjoint (section34CellThickening h Cp ε (ends e).1 ∩
          section34CellThickening h Cp ε (ends e).2)
        (section34CellThickening h Cp ε (ends d).1 ∩
          section34CellThickening h Cp ε (ends d).2) := by
  obtain ⟨O, δ, -, -, -, -, hOd, hδ, hδO⟩ :=
    exists_locallyFinite_disjoint_cthickening_intersections
      (fun w => h '' Cp w) ends hA hΩ hAΩ hlf hdisj
  obtain ⟨ε, hε, hεcap, hεsum⟩ := exists_section34_vertex_scales_with_sum_margins
    hends cap hcap (fun e => min (margin e) (δ e))
    (fun e => lt_min (hmargin e) (hδ e))
  have hthick (w : Section34VertexIndex 𝒦 𝒦') (r : ℝ) (hr : ε w ≤ r) :
      section34CellThickening h Cp ε w ⊆ cthickening r (h '' Cp w) := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp hy
    exact thickening_subset_cthickening r _
      (thickening_mono hr _ (ball_subset_thickening (mem_image_of_mem h hx) _ hxy))
  have hinside (e : Section34EdgeIndex 𝒦 𝒦') :
      section34CellThickening h Cp ε (ends e).1 ∩
        section34CellThickening h Cp ε (ends e).2 ⊆ O e := by
    have hsum : ε (ends e).1 + ε (ends e).2 < δ e :=
      (hεsum e).trans_le (min_le_right _ _)
    apply (inter_subset_inter (hthick (ends e).1 (δ e) ?_)
      (hthick (ends e).2 (δ e) ?_)).trans (hδO e)
    · exact le_of_lt ((lt_add_of_pos_right _ (hε (ends e).2)).trans hsum)
    · exact le_of_lt ((lt_add_of_pos_left _ (hε (ends e).1)).trans hsum)
  exact ⟨ε, hε, hεcap, fun e => (hεsum e).trans_le (min_le_left _ _),
    fun e d hed => (hOd e d hed).mono (hinside e) (hinside d)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
