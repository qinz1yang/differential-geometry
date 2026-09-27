/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnThickeningStability
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnInteriorRegionStability
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOnCompact
import DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphIntoMonoOfIsPLCellOn
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

private theorem exists_vertex_scales_below_edge_bounds
    (hends : ∀ e, (e.1 : Set Ea) =
      ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (cap : Section34VertexIndex 𝒦 𝒦' → ℝ) (hcap : ∀ w, 0 < cap w)
    (d : Section34EdgeIndex 𝒦 𝒦' → ℝ) (hd : ∀ e, 0 < d e) :
    ∃ δ : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < δ w) ∧ (∀ w, δ w < cap w) ∧
      ∀ w e, w = (ends e).1 ∨ w = (ends e).2 → δ w < d e := by
  classical
  have hw (w : Section34VertexIndex 𝒦 𝒦') :
      ∃ r : ℝ, 0 < r ∧ r < cap w ∧
        ∀ e, w = (ends e).1 ∨ w = (ends e).2 → r < d e := by
    let I := {e : Section34EdgeIndex 𝒦 𝒦' // w = (ends e).1 ∨ w = (ends e).2}
    let _ : Finite I := section34_incident_edges_finite hends w
    let b : Option I → ℝ := fun i => i.elim (cap w) (fun e => d e.1)
    have hb : ∀ i, 0 < b i := by
      intro i
      cases i with
      | none => exact hcap w
      | some e => exact hd e.1
    obtain ⟨i, hi⟩ := Finite.exists_min b
    refine ⟨b i / 2, half_pos (hb i), ?_, ?_⟩
    · exact (half_lt_self (hb i)).trans_le (hi none)
    · intro e he
      exact (half_lt_self (hb i)).trans_le (hi (some ⟨e, he⟩))
  choose δ hδ hcapδ hδd using hw
  exact ⟨δ, hδ, hcapδ, hδd⟩

private theorem isCompact_cell_boundary {S B : Set M₁} (hS : IsPLCellOn 3 S B) :
    IsCompact B := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := hS
  rw [hB]
  apply hr.isPLSphere_image_stdSimplexBoundary.isPolyhedron.isCompact.image_of_continuousOn
  apply hu.continuousOn.mono
  rintro _ ⟨x, hx, rfl⟩
  exact hr.bijOn.mapsTo hx.1

private theorem exists_pos_cthickening_inter_cthickening_subset {X : Type*}
    [PseudoEMetricSpace X] {A B O : Set X} (hA : IsCompact A) (hB : IsClosed B)
    (hO : IsOpen O) (hAB : A ∩ B ⊆ O) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ A ∩ Metric.cthickening δ B ⊆ O := by
  have hd : Disjoint (A \ O) B := by
    rw [Set.disjoint_left]
    exact fun x hxA hxB => hxA.2 (hAB ⟨hxA.1, hxB⟩)
  obtain ⟨r, hr, hdr⟩ := hd.exists_cthickenings (hA.diff hO) hB
  have hAO : A ⊆ O ∪ (Metric.cthickening r B)ᶜ := by
    intro x hxA
    by_cases hxO : x ∈ O
    · exact Or.inl hxO
    · exact Or.inr (Set.disjoint_left.mp hdr
        (Metric.self_subset_cthickening (A \ O) ⟨hxA, hxO⟩))
  obtain ⟨s, hs, hAs⟩ := hA.exists_cthickening_subset_open
    (hO.union Metric.isClosed_cthickening.isOpen_compl) hAO
  refine ⟨min s r, lt_min hs hr, ?_⟩
  intro x hx
  rcases hAs (Metric.cthickening_mono (min_le_left s r) A hx.1) with hxO | hxB
  · exact hxO
  · exact (hxB (Metric.cthickening_mono (min_le_right s r) B hx.2)).elim

theorem exists_section34_inner_end_stability_scales
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε) :
    ∃ δ : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < δ w) ∧ (∀ w, δ w < ε w) ∧
      ∀ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
        (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) →
        (∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < δ w) →
        ∀ e, G (ends e).1 '' Ab₀ e ⊆ interior (G (ends e).2 '' Cp (ends e).2) := by
  classical
  obtain ⟨hε, -, hsubs, -, hcp, -, -, -, hends, -, -, -, -, -, haa, -, -, -, -, -, hab, -⟩ :=
    id hprep
  have hCpCc : ∀ w, Cp w ⊆ Cc w := fun w => (hsubs w).2.1
  have hCpU : ∀ w, Cp w ⊆ U := fun w => (hCpCc w).trans (hsubs w).2.2
  have hcontU : ContinuousOn h U :=
    continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinjU : InjOn h U := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hh.injective (show
      U.domRestrict h ⟨x, hx⟩ = U.domRestrict h ⟨y, hy⟩ from hxy))
  have hedge (e : Section34EdgeIndex 𝒦 𝒦') :
      ∃ d > 0, ∀ F : M₁ → M₂, IsPLHomeomorphInto 3 F (Cp (ends e).2) →
        (∀ z ∈ Cp (ends e).2, dist (h z) (F z) < d) →
        Metric.cthickening d (h '' Ab₀ e) ⊆ interior (F '' Cp (ends e).2) := by
    apply exists_cthickening_subset_image_interior_stable_of_isPLCellOn
      (hcp (ends e).2) (hcontU.mono (hCpU _)) (hinjU.mono (hCpU _))
      (haa e).2.isCompact_first
    rw [(hcp (ends e).2).sdiff_boundary_eq_interior]
    exact (hab e).1
  choose d hd hstable using hedge
  obtain ⟨δ, hδ, hδε, hδd⟩ :=
    exists_vertex_scales_below_edge_bounds (fun e => (hends e).2.1) ε hε d hd
  refine ⟨δ, hδ, hδε, fun G hG hGdist e => ?_⟩
  have hGb : IsPLHomeomorphInto 3 (G (ends e).2) (Cp (ends e).2) :=
    (hG (ends e).2).mono_of_isPLCellOn (hcp (ends e).2) (hCpCc _)
  have hclose : ∀ z ∈ Cp (ends e).2, dist (h z) (G (ends e).2 z) < d e := by
    intro z hz
    rw [dist_comm]
    exact (hGdist (ends e).2 z (hCpCc _ hz)).trans (hδd _ e (Or.inr rfl))
  rintro y ⟨x, hx, rfl⟩
  apply hstable e (G (ends e).2) hGb hclose
  apply Metric.thickening_subset_cthickening
  have hAaBd : Aa e ⊆ CpBd (ends e).1 := by
    rw [(haa e).1]
    exact inter_subset_left
  have hxCc : x ∈ Cc (ends e).1 :=
    hCpCc _ ((hcp _).boundary_subset (hAaBd ((haa e).2.first_subset hx)))
  apply Metric.mem_thickening_iff.mpr
  exact ⟨h x, mem_image_of_mem h hx,
    (hGdist (ends e).1 x hxCc).trans (hδd _ e (Or.inl rfl))⟩

private theorem exists_trace_interior_stability_scales_at_endpoint
    (v : Section34EdgeIndex 𝒦 𝒦' → Section34VertexIndex 𝒦 𝒦')
    (hv : ∀ e, v e = (ends e).1 ∨ v e = (ends e).2)
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε) :
    ∃ δ : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < δ w) ∧ (∀ w, δ w < ε w) ∧
      ∀ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
        (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) →
        (∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < δ w) →
        ∀ e, G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
          interior (G (v e) '' Tn e) := by
  classical
  obtain ⟨hε, hcc, hsubs, -, hcp, -, -, -, hends, -, -, htn, hsn, -, -, -, -, -, hbc,
    hcross, -⟩ := id hprep
  have hcontU : ContinuousOn h U :=
    continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinjU : InjOn h U := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hh.injective (show
      U.domRestrict h ⟨x, hx⟩ = U.domRestrict h ⟨y, hy⟩ from hxy))
  have hBdCc : ∀ w, CpBd w ⊆ Cc w := fun w =>
    (hcp w).boundary_subset.trans (hsubs w).2.1
  have hBdU : ∀ w, CpBd w ⊆ U := fun w => (hBdCc w).trans (hsubs w).2.2
  have hBdCompact : ∀ w, IsCompact (h '' CpBd w) := fun w =>
    (isCompact_cell_boundary (hcp w)).image_of_continuousOn (hcontU.mono (hBdU w))
  have hedge (e : Section34EdgeIndex 𝒦 𝒦') :
      ∃ d > 0, ∀ F Ga Gb : M₁ → M₂, IsPLHomeomorphInto 3 F (Cc (v e)) →
        (∀ x ∈ Cc (v e), dist (F x) (h x) < d) →
        (∀ x ∈ Cc (ends e).1, dist (Ga x) (h x) < d) →
        (∀ x ∈ Cc (ends e).2, dist (Gb x) (h x) < d) →
        Ga '' CpBd (ends e).1 ∩ Gb '' CpBd (ends e).2 ⊆ interior (F '' Tn e) := by
    have hTC : Tn e ⊆ Cc (v e) :=
      ((htn e).1.trans interior_subset).trans (hsn e _ (hv e))
    obtain ⟨r, hr, hrstable⟩ :=
      exists_cthickening_subset_image_interior_stable_of_subset_isPLCellOn
        (hcc (v e)) (hcontU.mono (hsubs _).2.2) (hinjU.mono (hsubs _).2.2)
        hTC (hbc e).1.isCompact ((hbc e).2.trans inter_subset_right)
    have hbase : (h '' CpBd (ends e).1) ∩ (h '' CpBd (ends e).2) ⊆
        Metric.thickening r (h '' Bc e) := by
      rintro y ⟨⟨x, hx, hxy⟩, z, hz, hzy⟩
      have hxz : x = z := hinjU (hBdU _ hx) (hBdU _ hz) (hxy.trans hzy.symm)
      have hxBc : x ∈ Bc e := (hcross e ⟨hx, hxz.symm ▸ hz⟩).1
      exact Metric.self_subset_thickening hr _ ⟨x, hxBc, hxy⟩
    obtain ⟨s, hs, hsinter⟩ := exists_pos_cthickening_inter_cthickening_subset
      (hBdCompact (ends e).1) (hBdCompact (ends e).2).isClosed
      Metric.isOpen_thickening hbase
    refine ⟨min r s, lt_min hr hs, fun F Ga Gb hF hFClose hGaClose hGbClose => ?_⟩
    have himage (w : Section34VertexIndex 𝒦 𝒦') (F : M₁ → M₂)
        (hF : ∀ x ∈ Cc w, dist (F x) (h x) < min r s) :
        F '' CpBd w ⊆ Metric.cthickening s (h '' CpBd w) := by
      rintro y ⟨x, hx, rfl⟩
      apply Metric.thickening_subset_cthickening
      apply Metric.mem_thickening_iff.mpr
      exact ⟨h x, mem_image_of_mem h hx, (hF x (hBdCc w hx)).trans_le (min_le_right r s)⟩
    intro y hy
    apply hrstable F hF (fun z hz => ?_)
      (Metric.thickening_subset_cthickening r _ (hsinter
        ⟨himage _ Ga hGaClose hy.1, himage _ Gb hGbClose hy.2⟩))
    rw [dist_comm]
    exact (hFClose z hz).trans_le (min_le_left r s)
  choose d hd hstable using hedge
  obtain ⟨δ, hδ, hδε, hδd⟩ :=
    exists_vertex_scales_below_edge_bounds (fun e => (hends e).2.1) ε hε d hd
  refine ⟨δ, hδ, hδε, fun G hG hGdist e => ?_⟩
  exact hstable e (G (v e)) (G (ends e).1) (G (ends e).2) (hG (v e))
    (fun x hx => (hGdist _ x hx).trans (hδd _ e (hv e)))
    (fun x hx => (hGdist _ x hx).trans (hδd _ e (Or.inl rfl)))
    (fun x hx => (hGdist _ x hx).trans (hδd _ e (Or.inr rfl)))

theorem exists_section34_trace_interior_stability_scales
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε) :
    ∃ δ : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < δ w) ∧ (∀ w, δ w < ε w) ∧
      ∀ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
        (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) →
        (∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < δ w) →
        ∀ e, G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
          interior (G (ends e).1 '' Tn e) := by
  exact exists_trace_interior_stability_scales_at_endpoint (fun e => (ends e).1)
    (fun _ => Or.inl rfl) hh hprep

theorem exists_section34_second_trace_interior_stability_scales
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε) :
    ∃ δ : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < δ w) ∧ (∀ w, δ w < ε w) ∧
      ∀ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
        (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) →
        (∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < δ w) →
        ∀ e, G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
          interior (G (ends e).2 '' Tn e) := by
  exact exists_trace_interior_stability_scales_at_endpoint (fun e => (ends e).2)
    (fun _ => Or.inr rfl) hh hprep

end DifferentialGeometry.Topology.PiecewiseLinear
