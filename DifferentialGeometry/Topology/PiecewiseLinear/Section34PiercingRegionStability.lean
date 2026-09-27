/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnInteriorRegionStability
import DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOnCompact
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdgeFinite

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁]
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

theorem exists_section34_region_image_stability_scales
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hCc : ∀ w, IsPLCellOn 3 (Cc w) (CcBd w)) (hCcU : ∀ w, Cc w ⊆ U)
    (hends : ∀ e, (e.1 : Set Ea) =
      ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (hε : ∀ w, 0 < ε w) {R K : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
    (hK : ∀ e, IsCompact (K e)) (hKb : ∀ e, K e ⊆ Cc (ends e).2)
    (hRa : ∀ e, R e ⊆ Cc (ends e).1) (hKR : ∀ e, K e ⊆ interior (R e)) :
    ∃ δ : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < δ w) ∧ (∀ w, δ w < ε w) ∧
      ∀ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
        (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) →
        (∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < δ w) →
        ∀ e, G (ends e).2 '' K e ⊆ interior (G (ends e).1 '' R e) := by
  classical
  have hcont : ContinuousOn h U :=
    continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinj : InjOn h U := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hh.injective (show
      U.domRestrict h ⟨x, hx⟩ = U.domRestrict h ⟨y, hy⟩ from hxy))
  have hedge (e : Section34EdgeIndex 𝒦 𝒦') :
      ∃ d > 0, ∀ F : M₁ → M₂, IsPLHomeomorphInto 3 F (Cc (ends e).1) →
        (∀ z ∈ Cc (ends e).1, dist (h z) (F z) < d) →
        Metric.cthickening d (h '' K e) ⊆ interior (F '' R e) := by
    exact exists_cthickening_subset_image_interior_stable_of_subset_isPLCellOn
      (hCc _) (hcont.mono (hCcU _)) (hinj.mono (hCcU _)) (hRa e) (hK e) (hKR e)
  choose d hd hstable using hedge
  have hw (w : Section34VertexIndex 𝒦 𝒦') :
      ∃ r : ℝ, 0 < r ∧ r < ε w ∧
        ∀ e, w = (ends e).1 ∨ w = (ends e).2 → r < d e := by
    let I := {e : Section34EdgeIndex 𝒦 𝒦' // w = (ends e).1 ∨ w = (ends e).2}
    let _ : Finite I := section34_incident_edges_finite hends w
    let b : Option I → ℝ := fun i => i.elim (ε w) (fun e => d e.1)
    have hb : ∀ i, 0 < b i := by
      intro i
      cases i with
      | none => exact hε w
      | some e => exact hd e.1
    obtain ⟨i, hi⟩ := Finite.exists_min b
    refine ⟨b i / 2, half_pos (hb i), ?_, ?_⟩
    · exact (half_lt_self (hb i)).trans_le (hi none)
    · intro e he
      exact (half_lt_self (hb i)).trans_le (hi (some ⟨e, he⟩))
  choose δ hδ hδε hδd using hw
  refine ⟨δ, hδ, hδε, fun G hG hclose e y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hy
  apply hstable e (G (ends e).1) (hG _)
    (fun z hz => by
      rw [dist_comm]
      exact (hclose _ z hz).trans (hδd _ e (Or.inl rfl)))
  apply Metric.thickening_subset_cthickening
  exact Metric.mem_thickening_iff.mpr ⟨h x, mem_image_of_mem h hx,
    (hclose _ x (hKb e hx)).trans (hδd _ e (Or.inr rfl))⟩

theorem exists_section34_outer_annulus_stability_scales
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε) :
    ∃ δ : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < δ w) ∧ (∀ w, δ w < ε w) ∧
      ∀ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
        (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) →
        (∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < δ w) →
        ∀ e, G (ends e).2 '' Bb e ⊆ interior (G (ends e).1 '' Sn e) := by
  obtain ⟨hε, hCc, hsubs, -, hCp, -, -, -, hends, -, -, -, hSn, -, -, hBb, -, hBbSn, -⟩ :=
    id hprep
  exact exists_section34_region_image_stability_scales hh hCc (fun w => (hsubs w).2.2)
    (fun e => (hends e).2.1) hε (fun e => (hBb e).2.isCompact)
    (fun e => (hBb e).1.trans ((hCp _).boundary_subset.trans (hsubs _).2.1))
    (fun e => hSn e _ (Or.inl rfl)) (fun e => (hBbSn e).1)

end DifferentialGeometry.Topology.PiecewiseLinear
