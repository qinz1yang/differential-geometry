/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskMove
import DifferentialGeometry.Topology.PiecewiseLinear.SmoothBoundaryPlane
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryIsotopyExtension
import DifferentialGeometry.Topology.PiecewiseLinear.PrismAnnulusChart

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

universe u

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_homeomorph_smooth_disks_of_isClosedEmbedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    (ψ : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} → M)
    (hψ : IsClosedEmbedding ψ) (hψbd : range ψ ⊆ (𝓡∂ 3).boundary M) :
    ∃ θ : M ≃ₜ M, θ '' (𝓡∂ 3).boundary M = (𝓡∂ 3).boundary M ∧
      ∃ f : Fin 2 → EuclideanSpace ℝ (Fin 2) → M,
        (∀ j, IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (f j)) ∧
        (∀ j, range (f j) ⊆ (𝓡∂ 3).boundary M) ∧
        Disjoint (range (f 0)) (range (f 1)) ∧
        θ '' range ψ = ⋃ j, f j '' Metric.closedBall 0 1 := by
  classical
  have hBc : CompactSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (BoundaryManifold (𝓡∂ 3) M) :=
    BoundaryManifold.chartedSpace (I := 𝓡∂ 3)
  have hdisk : ∀ c : ℝ, (c = 0 ∨ c = 1) →
      ∃ d : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 → M,
        Continuous d ∧ Function.Injective d ∧ range d = ψ '' {z | z.val.val.2 = c} := by
    intro c hc
    have hcI : c ∈ Icc (0 : ℝ) 1 := by
      rcases hc with rfl | rfl
      · exact ⟨le_rfl, zero_le_one⟩
      · exact ⟨zero_le_one, le_rfl⟩
    have hc2 : c ∈ ({0, 1} : Set ℝ) := by
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hp2 : ∀ w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
        (prismBallHomeomorph.symm (w, ⟨c, hcI⟩)).val.2 = c := fun w =>
      congrArg (fun x => (x.2 : ℝ)) (prismBallHomeomorph.apply_symm_apply (w, ⟨c, hcI⟩))
    let z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 →
        {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
          z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} := fun w =>
      ⟨prismBallHomeomorph.symm (w, ⟨c, hcI⟩),
        (prismBallHomeomorph.symm (w, ⟨c, hcI⟩)).2.1, by rw [hp2 w]; exact hc2⟩
    have hzc : Continuous z :=
      (prismBallHomeomorph.symm.continuous.comp
        (continuous_id.prodMk continuous_const)).subtype_mk _
    refine ⟨fun w => ψ (z w), hψ.continuous.comp hzc, fun w w' h => ?_, ?_⟩
    · have h1 : z w = z w' := hψ.injective h
      have h2 := congrArg (fun q : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
          z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} => (prismBallHomeomorph q.val).1) h1
      simpa only [z, Homeomorph.apply_symm_apply] using h2
    · ext y
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨z w, hp2 w, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        refine ⟨(prismBallHomeomorph q.val).1, congrArg ψ (Subtype.ext ?_)⟩
        change prismBallHomeomorph.symm ((prismBallHomeomorph q.val).1, ⟨c, hcI⟩) = q.val
        have hpq : prismBallHomeomorph q.val = ((prismBallHomeomorph q.val).1, ⟨c, hcI⟩) :=
          Prod.ext rfl (Subtype.ext hq)
        rw [← hpq, Homeomorph.symm_apply_apply]
  obtain ⟨d₀, hd₀c, hd₀i, hd₀r⟩ := hdisk 0 (Or.inl rfl)
  obtain ⟨d₁, hd₁c, hd₁i, hd₁r⟩ := hdisk 1 (Or.inr rfl)
  have hrange : range ψ = range d₀ ∪ range d₁ := by
    rw [hd₀r, hd₁r, ← image_union, ← image_univ]
    congr 1
    ext z
    simp only [mem_univ, mem_union, Set.mem_ofPred_eq, true_iff]
    exact z.2.2
  have hdisj : Disjoint (range d₀) (range d₁) := by
    rw [hd₀r, hd₁r, disjoint_image_iff hψ.injective, Set.disjoint_left]
    intro z h0 h1
    have h0' : z.val.val.2 = 0 := h0
    have h1' : z.val.val.2 = 1 := h1
    rw [h0'] at h1'
    exact zero_ne_one h1'
  have hmem₀ : ∀ w, d₀ w ∈ (𝓡∂ 3).boundary M := fun w =>
    hψbd (by rw [hrange]; exact Or.inl ⟨w, rfl⟩)
  have hmem₁ : ∀ w, d₁ w ∈ (𝓡∂ 3).boundary M := fun w =>
    hψbd (by rw [hrange]; exact Or.inr ⟨w, rfl⟩)
  let e₀ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 → BoundaryManifold (𝓡∂ 3) M :=
    fun w => ⟨d₀ w, hmem₀ w⟩
  let e₁ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 → BoundaryManifold (𝓡∂ 3) M :=
    fun w => ⟨d₁ w, hmem₁ w⟩
  have he₀c : Continuous e₀ := hd₀c.subtype_mk _
  have he₁c : Continuous e₁ := hd₁c.subtype_mk _
  have he₀i : Function.Injective e₀ := fun w w' h => hd₀i (congrArg Subtype.val h)
  have he₁i : Function.Injective e₁ := fun w w' h => hd₁i (congrArg Subtype.val h)
  have hdisjB : Disjoint (range e₀) (range e₁) := by
    rw [Set.disjoint_left]
    rintro _ ⟨w, rfl⟩ ⟨w', hw'⟩
    exact Set.disjoint_left.mp hdisj ⟨w, rfl⟩ ⟨w', congrArg Subtype.val hw'⟩
  obtain ⟨W₀, W₁, hW₀, hW₁, hK₀W, hK₁W, hWW⟩ :=
    SeparatedNhds.of_isCompact_isCompact (isCompact_range he₀c) (isCompact_range he₁c) hdisjB
  obtain ⟨O₀, hO₀, hO₀ne, hO₀W, hmove₀⟩ :=
    exists_isotopy_closedBall_embedding_onto e₀ he₀c he₀i hW₀ hK₀W
  obtain ⟨O₁, hO₁, hO₁ne, hO₁W, hmove₁⟩ :=
    exists_isotopy_closedBall_embedding_onto e₁ he₁c he₁i hW₁ hK₁W
  have hsmooth : ∀ O : Set (BoundaryManifold (𝓡∂ 3) M), IsOpen O → O.Nonempty →
      ∃ f : EuclideanSpace ℝ (Fin 2) → M, IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ f ∧
        range f ⊆ (𝓡∂ 3).boundary M ∧
        ∀ w (h : f w ∈ (𝓡∂ 3).boundary M), (⟨f w, h⟩ : BoundaryManifold (𝓡∂ 3) M) ∈ O := by
    rintro O hO ⟨b, hb⟩
    obtain ⟨t, ht, hOt⟩ := isOpen_induced_iff.mp hO
    rw [← hOt] at hb
    obtain ⟨f, hf, hfbd, hft⟩ := exists_isSmoothEmbedding_plane_boundary_subset ht b.2 hb
    refine ⟨f, hf, hfbd, fun w h => ?_⟩
    rw [← hOt]
    exact hft ⟨w, rfl⟩
  obtain ⟨f₀, hf₀, hf₀bd, hf₀O⟩ := hsmooth O₀ hO₀ hO₀ne
  obtain ⟨f₁, hf₁, hf₁bd, hf₁O⟩ := hsmooth O₁ hO₁ hO₁ne
  let g₀ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 → BoundaryManifold (𝓡∂ 3) M :=
    fun w => ⟨f₀ w.val, hf₀bd ⟨w.val, rfl⟩⟩
  let g₁ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 → BoundaryManifold (𝓡∂ 3) M :=
    fun w => ⟨f₁ w.val, hf₁bd ⟨w.val, rfl⟩⟩
  have hg₀c : Continuous g₀ :=
    (hf₀.contMDiff.continuous.comp continuous_subtype_val).subtype_mk _
  have hg₁c : Continuous g₁ :=
    (hf₁.contMDiff.continuous.comp continuous_subtype_val).subtype_mk _
  have hg₀i : Function.Injective g₀ := fun w w' h =>
    Subtype.ext (hf₀.isEmbedding.injective (congrArg Subtype.val h))
  have hg₁i : Function.Injective g₁ := fun w w' h =>
    Subtype.ext (hf₁.isEmbedding.injective (congrArg Subtype.val h))
  have hg₀O : range g₀ ⊆ O₀ := by
    rintro _ ⟨w, rfl⟩
    exact hf₀O w.val _
  have hg₁O : range g₁ ⊆ O₁ := by
    rintro _ ⟨w, rfl⟩
    exact hf₁O w.val _
  obtain ⟨G₀, hG₀c, hG₀ci, hG₀0, ⟨K₀, -, hK₀W₀, hK₀fix⟩, hG₀img⟩ := hmove₀ g₀ hg₀c hg₀i hg₀O
  obtain ⟨G₁, hG₁c, hG₁ci, hG₁0, ⟨K₁, -, hK₁W₁, hK₁fix⟩, hG₁img⟩ := hmove₁ g₁ hg₁c hg₁i hg₁O
  let G : ℝ → BoundaryManifold (𝓡∂ 3) M ≃ₜ BoundaryManifold (𝓡∂ 3) M :=
    fun t => (G₀ t).trans (G₁ t)
  have hGc : Continuous (fun p : ℝ × BoundaryManifold (𝓡∂ 3) M => G p.1 p.2) :=
    hG₁c.comp (continuous_fst.prodMk hG₀c)
  have hGci : Continuous (fun p : ℝ × BoundaryManifold (𝓡∂ 3) M => (G p.1).symm p.2) :=
    hG₀ci.comp (continuous_fst.prodMk hG₁ci)
  have hG0 : G 0 = Homeomorph.refl _ := by
    refine Homeomorph.ext fun y => ?_
    change G₁ 0 (G₀ 0 y) = y
    rw [hG₀0, hG₁0]
    rfl
  obtain ⟨θ, hθbd, hθ⟩ := exists_homeomorph_of_boundary_isotopy G hGc hGci hG0
  have hGimg : ∀ s : Set (BoundaryManifold (𝓡∂ 3) M), G 1 '' s = G₁ 1 '' (G₀ 1 '' s) := by
    intro s
    rw [← image_comp]
    rfl
  have hG1₀ : G 1 '' range e₀ = range g₀ := by
    rw [hGimg, hG₀img]
    refine EqOn.image_eq_self fun y hy => hK₁fix 1 fun hyK => ?_
    exact Set.disjoint_left.mp hWW (hO₀W (hg₀O hy)) (hK₁W₁ hyK)
  have hG1₁ : G 1 '' range e₁ = range g₁ := by
    have hfix : EqOn (G₀ 1) id (range e₁) := fun y hy => hK₀fix 1 fun hyK =>
      Set.disjoint_left.mp hWW (hK₀W₀ hyK) (hK₁W hy)
    rw [hGimg, hfix.image_eq_self, hG₁img]
  let ι : BoundaryManifold (𝓡∂ 3) M → M := fun b => b.val
  have hθimg : ∀ s : Set (BoundaryManifold (𝓡∂ 3) M),
      θ '' (ι '' s) = ι '' (G 1 '' s) := by
    intro s
    rw [← image_comp, ← image_comp]
    exact image_congr fun b _ => hθ b
  have hrange' : range ψ = ι '' (range e₀ ∪ range e₁) := by
    rw [hrange, image_union, ← range_comp, ← range_comp]
    rfl
  have hgv : ∀ (f : EuclideanSpace ℝ (Fin 2) → M)
      (g : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 → BoundaryManifold (𝓡∂ 3) M),
      (∀ w, ι (g w) = f w.val) → ι '' range g = f '' Metric.closedBall 0 1 := by
    intro f g hg
    rw [← range_comp]
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.val, w.2, (hg w).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, hg ⟨x, hx⟩⟩
  refine ⟨θ, hθbd, ![f₀, f₁], Fin.forall_fin_two.mpr ⟨hf₀, hf₁⟩,
    Fin.forall_fin_two.mpr ⟨hf₀bd, hf₁bd⟩, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨w, rfl⟩ ⟨w', hw'⟩
    have h0 : (⟨f₀ w, hf₀bd ⟨w, rfl⟩⟩ : BoundaryManifold (𝓡∂ 3) M) ∈ O₀ := hf₀O w _
    have h1 : (⟨f₁ w', hf₁bd ⟨w', rfl⟩⟩ : BoundaryManifold (𝓡∂ 3) M) ∈ O₁ := hf₁O w' _
    have heq : (⟨f₁ w', hf₁bd ⟨w', rfl⟩⟩ : BoundaryManifold (𝓡∂ 3) M) =
        ⟨f₀ w, hf₀bd ⟨w, rfl⟩⟩ := Subtype.ext hw'
    rw [heq] at h1
    exact Set.disjoint_left.mp hWW (hO₀W h0) (hO₁W h1)
  · rw [hrange', hθimg, image_union, hG1₀, hG1₁, image_union,
      hgv f₀ g₀ (fun _ => rfl), hgv f₁ g₁ (fun _ => rfl)]
    ext y
    simp only [mem_union, mem_iUnion, Fin.exists_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]

end DifferentialGeometry.Topology.PiecewiseLinear
