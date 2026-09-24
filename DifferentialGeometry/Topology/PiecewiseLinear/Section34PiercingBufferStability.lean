/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingRegionStability
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingComponentStability

/-! # Section34Piercing Buffer Stability -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}

theorem exists_section34_component_stability_scales_of_connected_buffers
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    {K₀ K₁ R : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
    (hK₀ : ∀ e, IsCompact (K₀ e) ∧ IsConnected (K₀ e))
    (hK₁ : ∀ e, IsCompact (K₁ e) ∧ IsConnected (K₁ e))
    (hR : ∀ e, IsCompact (R e))
    (hK₀B : ∀ e, K₀ e ⊆ Bb e) (hK₁B : ∀ e, K₁ e ⊆ Bb e)
    (hRb : ∀ e, R e ⊆ Cc (ends e).2)
    (hcover : ∀ e, Bb e ⊆ K₀ e ∪ K₁ e ∪ R e)
    (hinside : ∀ e, K₀ e ⊆ interior (Cp (ends e).1))
    (houtside : ∀ e, Disjoint (K₁ e) (Cp (ends e).1))
    (hRT : ∀ e, R e ⊆ interior (Tn e)) :
    ∃ δ : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < δ w) ∧ (∀ w, δ w < ε w) ∧
      ∀ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
        (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) →
        (∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < δ w) →
        (∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
          ∀ z ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
            z ∉ G (ends e).1 '' Tn e →
            z ∈ connectedComponentIn
              (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y₀) ∧
        (∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
          ∀ z ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
            z ∉ G (ends e).1 '' Tn e →
            z ∈ connectedComponentIn
              (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y₀) := by
  obtain ⟨hε, hCc, hsubs, -, hCp, -, -, -, hends, -, -, hTS, hSn, -, -, hBb, -, hBbSn, -⟩ :=
    id hprep
  have hBbb : ∀ e, Bb e ⊆ Cc (ends e).2 := fun e =>
    (hBb e).1.trans ((hCp _).boundary_subset.trans (hsubs _).2.1)
  obtain ⟨d₀, hd₀, hd₀ε, hstable₀⟩ := exists_section34_region_image_stability_scales hh hCc
    (fun w => (hsubs w).2.2) (fun e => (hends e).2.1) hε (fun e => (hK₀ e).1)
    (fun e => (hK₀B e).trans (hBbb e)) (fun _ => (hsubs _).2.1) hinside
  obtain ⟨dR, hdR, -, hstableR⟩ := exists_section34_region_image_stability_scales hh hCc
    (fun w => (hsubs w).2.2) (fun e => (hends e).2.1) hε hR hRb
    (fun e => (hTS e).1.trans (interior_subset.trans (hSn e _ (Or.inl rfl)))) hRT
  have hK₁region : ∀ e, K₁ e ⊆ interior (Cc (ends e).1 \ Cp (ends e).1) := by
    intro e x hx
    apply interior_maximal (sdiff_subset_sdiff_left interior_subset)
      (isOpen_interior.sdiff (hCp _).isCompact.isClosed)
    exact ⟨interior_mono (hSn e _ (Or.inl rfl)) ((hBbSn e).1 (hK₁B e hx)),
      Set.disjoint_left.mp (houtside e) hx⟩
  obtain ⟨d₁, hd₁, -, hstable₁⟩ := exists_section34_region_image_stability_scales hh hCc
    (fun w => (hsubs w).2.2) (fun e => (hends e).2.1) hε (fun e => (hK₁ e).1)
    (fun e => (hK₁B e).trans (hBbb e)) (fun _ => sdiff_subset) hK₁region
  refine ⟨fun w => min (d₀ w) (min (dR w) (d₁ w)),
    fun w => lt_min (hd₀ w) (lt_min (hdR w) (hd₁ w)),
    fun w => (min_le_left _ _).trans_lt (hd₀ε w), fun G hG hclose => ?_⟩
  have hclose₀ : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < d₀ w :=
    fun w x hx => (hclose w x hx).trans_le (min_le_left _ _)
  have hcloseR : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < dR w :=
    fun w x hx => (hclose w x hx).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hclose₁ : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < d₁ w :=
    fun w x hx => (hclose w x hx).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  have hcomponents (e : Section34EdgeIndex 𝒦 𝒦') :=
    piercing_components_of_connected_buffers (hK₀ e).2 (hK₁ e).2 (hK₀B e) (hK₁B e)
      (hcover e) ((hG _).continuousOn.mono (hBbb e))
      ((hstable₀ G hG hclose₀ e).trans interior_subset) (show
        Disjoint (G (ends e).2 '' K₁ e) (G (ends e).1 '' Cp (ends e).1) from by
          refine Set.disjoint_left.mpr ?_
          intro y hy hyCp
          obtain ⟨x, hx, hxy⟩ := interior_subset (hstable₁ G hG hclose₁ e hy)
          obtain ⟨z, hz, hzy⟩ := hyCp
          have hxz := (hG _).injOn hx.1 ((hsubs _).2.1 hz) (hxy.trans hzy.symm)
          exact hx.2 (hxz ▸ hz))
      ((hstableR G hG hcloseR e).trans interior_subset)
  exact ⟨fun e => (hcomponents e).1, fun e => (hcomponents e).2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
