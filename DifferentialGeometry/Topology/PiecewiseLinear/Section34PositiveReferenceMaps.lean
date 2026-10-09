/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ConfinedTubePiercingConditions
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RelativeEdgeCharacter
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ReferenceBallMaps
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedCellOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.CellDiskOrientationCorrection

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
  {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ E3}
  {Sd : Section34SimplexIndex 𝒦 3 → Set E3}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}

theorem exists_section34_positive_reference_maps
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends
      Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34ConfinedTubePiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Sp Tp cnt Pg G)
    (hDvdef : ∀ w, Dv w = G w '' Cp w \
      ⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : (ends e).2 = w),
        interior (G (ends e).1 '' Cp (ends e).1))
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDmeet : ∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = Dd e)
    (hDdBd : ∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2)
    (hDddisj : ∀ e d, e ≠ d → Disjoint (Dd e) (Dd d))
    (hDvQ : ∀ w, Dv w ⊆ Q w)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (hDnbhd : (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦)) :
    ∃ (R : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂)
      (δ : Section34EdgeIndex 𝒦 𝒦' → M₂ → M₂),
      (∀ w, IsPLHomeomorphInto 3 (R w) (src (.vertexBall w))) ∧
      (∀ w, R w '' src (.vertexBall w) = Dv w) ∧
      (∀ w e, (w = (ends e).1 ∨ w = (ends e).2) → R w '' src (.splitDisk e) = Dd e) ∧
      ∀ e, IsPLHomeomorphInto 3 (δ e) (Dd e) ∧ δ e '' Dd e = Dd e ∧
        EqOn (δ e ∘ R (ends e).2) (R (ends e).1) (src (.splitDisk e)) ∧
        ∀ c : OpenPartialHomeomorph M₂ E3, DdBd e ⊆ c.source →
          IsPLCirclePositive (c '' DdBd e) (c ∘ δ e ∘ c.symm) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsep⟩ := id hpack
  have hDvsub (w : Section34VertexIndex 𝒦 𝒦') : Dv w ⊆ G w '' Cp w := by
    rw [hDvdef w]
    exact sdiff_subset
  obtain ⟨R, hR, hRim, -, hRD⟩ :=
    exists_section34_reference_ball_maps hframe hprep hDv hDd hDdBd hDddisj
  obtain ⟨σ, s, K, hKdata⟩ := exists_section34_relative_edge_character
    hU hh hframe htor hprep hsep hDvsub hDv hDd hDmeet hDdBd hDvQ hQlf hDnbhd hR hRim hRD
  obtain ⟨-, -, -, -, -, -, -, -, hends, -⟩ := id hprep
  choose b hb hbQ using exists_section34_vertex_chart hframe htor
  have hNpoint (w : Section34VertexIndex 𝒦 𝒦') :
      ∃ N : M₂ → M₂, IsPLHomeomorphInto 3 N (Dv w) ∧ N '' Dv w = Dv w ∧
        ∀ e, (w = (ends e).1 ∨ w = (ends e).2) → N '' Dd e = Dd e ∧
          ∀ c : OpenPartialHomeomorph M₂ E3, DdBd e ⊆ c.source →
            circleOrientationParity (c '' DdBd e) (c ∘ N ∘ c.symm) = σ w := by
    let I := {e : Section34EdgeIndex 𝒦 𝒦' // w = (ends e).1 ∨ w = (ends e).2}
    have _ : Finite I := section34_incident_edges_finite (fun e => (hends e).2.1) w
    obtain ⟨hDi, hDBi, hdisi⟩ := section34_target_vertex_boundary_disks hDd hDdBd hDddisj w
    obtain ⟨N, hN, hNim, hND, -, hNσ⟩ :=
      (hDv w).exists_disk_family_map_with_circle_parity
        (fun i : I => hDi i) (fun i : I => hDBi i) (fun i j hij => hdisi hij)
        (hb w) ((hDvQ w).trans (hbQ w)) (σ w)
    exact ⟨N, hN, hNim, fun e he => ⟨hND ⟨e, he⟩, hNσ ⟨e, he⟩⟩⟩
  choose N hN hNim hND using hNpoint
  let R' := fun w => N w ∘ R w
  have hR' (w : Section34VertexIndex 𝒦 𝒦') :
      IsPLHomeomorphInto 3 (R' w) (src (.vertexBall w)) :=
    (hR w).comp_of_image_eq (by rw [hRim w]; exact hN w)
  have hR'im (w : Section34VertexIndex 𝒦 𝒦') : R' w '' src (.vertexBall w) = Dv w := by
    change (N w ∘ R w) '' src (.vertexBall w) = _
    rw [image_comp, hRim w, hNim w]
  have hR'D (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦')
      (he : w = (ends e).1 ∨ w = (ends e).2) : R' w '' src (.splitDisk e) = Dd e := by
    change (N w ∘ R w) '' src (.splitDisk e) = _
    rw [image_comp, hRD w e he, (hND w e he).1]
  have hδpoint (e : Section34EdgeIndex 𝒦 𝒦') :
      ∃ δ : M₂ → M₂, IsPLHomeomorphInto 3 δ (Dd e) ∧ δ '' Dd e = Dd e ∧
        EqOn (δ ∘ R' (ends e).2) (R' (ends e).1) (src (.splitDisk e)) ∧
        ∀ c : OpenPartialHomeomorph M₂ E3, DdBd e ⊆ c.source →
          IsPLCirclePositive (c '' DdBd e) (c ∘ δ ∘ c.symm) := by
    obtain ⟨hc, hcs, hK, -, hKP, hKQ, hKgf, hKσ⟩ := hKdata e
    have hD₁ : Dd e ⊆ Dv (ends e).1 :=
      ((hDdBd e).trans inter_subset_left).trans (hDv (ends e).1).boundary_subset
    have hD₂ : Dd e ⊆ Dv (ends e).2 :=
      ((hDdBd e).trans inter_subset_right).trans (hDv (ends e).2).boundary_subset
    have hDc : Dd e ⊆ (ct (s e)).source :=
      (hD₁.trans (hDvQ _)).trans (subset_union_left.trans hcs)
    have hJc := (hDd e).boundary_subset.trans hDc
    have hKD : K e '' Dd e = Dd e := by
      rw [← hDmeet e, hK.injOn.image_inter subset_union_left subset_union_right, hKP, hKQ]
    have hpar : circleOrientationParity (ct (s e) '' DdBd e)
        (ct (s e) ∘ K e ∘ (ct (s e)).symm) =
        circleOrientationParity (ct (s e) '' DdBd e)
          (ct (s e) ∘ N (ends e).1 ∘ (ct (s e)).symm) +
        circleOrientationParity (ct (s e) '' DdBd e)
          (ct (s e) ∘ N (ends e).2 ∘ (ct (s e)).symm) := by
      rw [(hND (ends e).1 e (Or.inl rfl)).2 _ hJc,
        (hND (ends e).2 e (Or.inr rfl)).2 _ hJc]
      exact hKσ
    obtain ⟨δ, hδ, hδim, hδN, hpos⟩ := exists_positive_disk_correction_of_vertex_parities
      (hDd e) ((hN (ends e).1).mono_of_isPLCellOn (hDd e) hD₁)
      ((hN (ends e).2).mono_of_isPLCellOn (hDd e) hD₂)
      (hK.mono_of_isPLCellOn (hDd e) (hD₁.trans subset_union_left))
      (hND (ends e).1 e (Or.inl rfl)).1 (hND (ends e).2 e (Or.inr rfl)).1 hKD hc hDc hpar
    refine ⟨δ, hδ, hδim, ?_, ?_⟩
    · intro x hx
      have hxD : R (ends e).2 x ∈ Dd e :=
        hRD (ends e).2 e (Or.inr rfl) ▸ mem_image_of_mem (R (ends e).2) hx
      exact (hδN hxD).trans (congrArg (N (ends e).1) (hKgf hx))
    · intro c' hJc'
      have hDδ := (hDd e).image hδ
      rw [hδim] at hDδ
      have hJδ := hDδ.boundary_eq (hDd e)
      have hchange := circleOrientationParity_chart_eq (ct (s e)) c' hJc hJc'
        (fun x hx => hJδ ▸ mem_image_of_mem δ hx)
      apply circleOrientationParity_eq_zero_iff.mp
      rw [← hchange]
      exact circleOrientationParity_eq_zero_iff.mpr hpos
  choose δ hδ hδim hδR hδpos using hδpoint
  exact ⟨R', δ, hR', hR'im, hR'D, fun e => ⟨hδ e, hδim e, hδR e, hδpos e⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
