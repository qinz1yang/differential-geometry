import DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphIntoMonoOfIsPLCellOn
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingReindex
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingTraceNonempty
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ProtectedBoundaryPreservation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U W : Set M₁} {h : M₁ → M₂}
  {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
  {Sd : Section34SimplexIndex 𝒦 3 → Set (EuclideanSpace ℝ (Fin 3))}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem piercing_conditions_after_cancellation
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (n : ℕ) (C : Fin n → Set M₂) (hnlt : n < cnt e₀)
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀))
    (htube : Sp e₀ = G' (ends e₀).1 '' Sn e₀ ∧ Tp e₀ = G' (ends e₀).1 '' Tn e₀)
    (hG' : ∀ w, IsPLHomeomorphInto 3 (G' w) (Cc w))
    (hQ' : ∀ w, G' w '' Cc w ⊆ Q w)
    (hSn' : ∀ e, G' (ends e).2 '' Sn e ⊆ Q (ends e).1 ∧
      G' (ends e).1 '' Sn e ⊆ Q (ends e).2)
    (hmeet : G' (ends e₀).1 '' CpBd (ends e₀).1 ∩ G' (ends e₀).2 '' CpBd (ends e₀).2 ⊆
      G' (ends e₀).1 '' (Aa e₀ \ (Ab₀ e₀ ∪ Ab₁ e₀)) ∩
        G' (ends e₀).2 '' (Bb e₀ \ (Bb₀ e₀ ∪ Bb₁ e₀)) ∩ interior (Tp e₀))
    (hside : G' (ends e₀).1 '' Ab₀ e₀ ⊆ interior (G' (ends e₀).2 '' Cp (ends e₀).2) ∧
      Disjoint (G' (ends e₀).1 '' Ab₁ e₀) (G' (ends e₀).2 '' Cp (ends e₀).2))
    (hBb : Disjoint (G' (ends e₀).2 '' (Bb₀ e₀ ∪ Bb₁ e₀)) (Tp e₀))
    (hcompIn : ∃ y₀ ∈ G' (ends e₀).2 '' Bb e₀ ∩ G' (ends e₀).1 '' Cp (ends e₀).1,
      ∀ z ∈ G' (ends e₀).2 '' Bb e₀ ∩ G' (ends e₀).1 '' Cp (ends e₀).1, z ∉ Tp e₀ →
        z ∈ connectedComponentIn
          (G' (ends e₀).2 '' Bb e₀ ∩ G' (ends e₀).1 '' Cp (ends e₀).1) y₀)
    (hcompOut : ∃ y₀ ∈ G' (ends e₀).2 '' Bb e₀ \ G' (ends e₀).1 '' Cp (ends e₀).1,
      ∀ z ∈ G' (ends e₀).2 '' Bb e₀ \ G' (ends e₀).1 '' Cp (ends e₀).1, z ∉ Tp e₀ →
        z ∈ connectedComponentIn
          (G' (ends e₀).2 '' Bb e₀ \ G' (ends e₀).1 '' Cp (ends e₀).1) y₀)
    (hCtrace : G' (ends e₀).1 '' Aa e₀ ∩ G' (ends e₀).2 '' Bb e₀ = ⋃ i, C i)
    (hCsphere : ∀ i, IsPolyhedralSphere (n := 3) 1 (C i))
    (hCdisj : Pairwise fun i j => Disjoint (C i) (C j))
    (hCcross : ∀ y ∈ G' (ends e₀).1 '' Aa e₀ ∩ G' (ends e₀).2 '' Bb e₀,
      ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
        HasPLCrossingAt (c '' (G' (ends e₀).1 '' Aa e₀ ∩ c.source))
          (c '' (G' (ends e₀).2 '' Bb e₀ ∩ c.source)) (c y)) :
    ∃ (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ) (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
          Sp Tp cnt' Pg' G' ∧
        cnt' e₀ < cnt e₀ ∧
        (∀ e, e ≠ e₀ → cnt' e = cnt e) ∧
        ∀ e, e ≠ e₀ → G' (ends e).1 '' Aa e = G (ends e).1 '' Aa e ∧
          G' (ends e).2 '' Bb e = G (ends e).2 '' Bb e := by
  obtain ⟨-, -, hsub, -, hCp, -, -, -, -, -, -, -, -, -, hAaSource, hBbSource, -⟩ := id hprep
  have hGp' : ∀ w, IsPLHomeomorphInto 3 (G' w) (Cp w) :=
    fun w => (hG' w).mono_of_isPLCellOn (hCp w) (hsub w).2.1
  have hnonempty := section34_piercing_trace_nonempty_of_sides hprep hGp' e₀
    (fun _ hx => image_mono sdiff_subset (hmeet hx).1.2)
    ⟨fun _ hx => interior_subset (hside.1 hx), hside.2⟩
  rw [hCtrace] at hnonempty
  obtain ⟨y, hy⟩ := hnonempty
  obtain ⟨i, -⟩ := mem_iUnion.mp hy
  have : NeZero n := ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i) i.2)⟩
  have hAsub : Aa e₀ ⊆ CpBd (ends e₀).1 := (hAaSource e₀).1 ▸ inter_subset_left
  have hCsphereLocal : ∀ i, IsPolyhedralSphere (n := 3) 1 (C i) ∧
      C i ⊆ G' (ends e₀).1 '' (Aa e₀ \ (Ab₀ e₀ ∪ Ab₁ e₀)) ∩
        G' (ends e₀).2 '' (Bb e₀ \ (Bb₀ e₀ ∪ Bb₁ e₀)) := by
    refine fun i => ⟨hCsphere i, fun x hx => ?_⟩
    have htrace : x ∈ G' (ends e₀).1 '' Aa e₀ ∩ G' (ends e₀).2 '' Bb e₀ :=
      hCtrace ▸ mem_iUnion_of_mem i hx
    exact (hmeet ⟨image_mono hAsub htrace.1, image_mono (hBbSource e₀).1 htrace.2⟩).1
  have hforeign := section34Step_other_annulus_images hprep hpack G' e₀ hoff
  have hforeignInterior : ∀ e, e ≠ e₀ →
      G' (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
          G' (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e)) =
        G (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
          G (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e)) := by
    intro e he
    obtain ⟨hA, hB⟩ := section34Step_eqOn_other_annuli hprep hpack G' e₀ hoff e he
    rw [(hA.mono sdiff_subset).image_eq, (hB.mono sdiff_subset).image_eq]
  obtain ⟨-, -, -, -, hlf, hdisj, -, -, -, hgraph, -, hmark, -, -, -, -, htrace,
    hsphere, hdisjtrace, hcross, -⟩ := id hpack
  obtain ⟨cnt', Pg', -, hlt', hother, htrace', hsphere', hdisjtrace', hcross'⟩ :=
    exists_reindexed_piercing_family_of_strict_decrease
      (A := fun e => G (ends e).1 '' Aa e) (B := fun e => G (ends e).2 '' Bb e)
      (D := fun e => G (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
        G (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e)))
      (A' := fun e => G' (ends e).1 '' Aa e) (B' := fun e => G' (ends e).2 '' Bb e)
      (D' := fun e => G' (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
        G' (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e)))
      e₀ C htrace hsphere hdisjtrace hcross
      (fun e he => ⟨(hforeign e he).1, (hforeign e he).2, hforeignInterior e he⟩)
      hCtrace hCsphereLocal hCdisj hCcross (by simpa only [Nat.card_fin] using hnlt)
  have htubes : ∀ e, Sp e = G' (ends e).1 '' Sn e ∧ Tp e = G' (ends e).1 '' Tn e := by
    intro e
    by_cases he : e = e₀
    · exact he ▸ htube
    · exact section34Step_other_tube_images hprep hpack G' e₀ hoff e he
  have hmarkers := (section34Step_eqOn_marker_and_boundary hprep hpack G' e₀ hoff).1
  have hmark' : ∀ w e, Disjoint (G' w '' simplexBody 𝒦' w.1) (Sp e) := by
    intro w e
    rw [(hmarkers w).image_eq]
    exact hmark w e
  obtain ⟨-, -, -, -, -, -, -, -, hBbOld, -, -, -, -, -, hcompInOld,
    hcompOutOld, -⟩ := id hpack
  refine ⟨cnt', Pg', ?_, hlt', fun e he => (hother e he).1, hforeign⟩
  refine ⟨hG', hQ', hSn', htubes, hlf, hdisj, ?_, ?_, ?_, hgraph, hGp', hmark',
    section34Step_support_disjoint_other_boundaries hprep hpack G' e₀ hoff hin,
    section34Step_disjoint_cells hprep hpack G' e₀ hoff hin, ?_, ?_, htrace', hsphere',
    hdisjtrace', hcross', section34Step_lenses_disjoint hprep hpack G' e₀ hoff hin,
    section34Step_marker_exclusion hprep hpack G' e₀ hoff hin⟩
  · intro e
    by_cases he : e = e₀
    · exact he ▸ hmeet
    · exact section34Step_other_boundary_containment hprep hpack G' e₀ hoff hin e he
  · intro e
    by_cases he : e = e₀
    · exact he ▸ hside
    · exact section34Step_other_piercing_sides hprep hpack G' e₀ hoff hin hGp' e he
  · intro e
    by_cases he : e = e₀
    · subst e
      refine ⟨?_, hBb⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hin _ x ((hCp _).boundary_subset ((hBbSource e₀).1 hx))
        ((hBbOld e₀).1 ⟨x, hx, rfl⟩)
    · have hB := (section34Step_eqOn_other_annuli hprep hpack G' e₀ hoff e he).2
      rw [hB.image_eq, (hB.mono (union_subset (hBbSource e).2.first_subset
        (hBbSource e).2.second_subset)).image_eq]
      exact hBbOld e
  · intro e
    by_cases he : e = e₀
    · exact he ▸ hcompIn
    · rw [(section34Step_other_component_sets hprep hpack G' e₀ hoff hin e he).1]
      exact hcompInOld e
  · intro e
    by_cases he : e = e₀
    · exact he ▸ hcompOut
    · rw [(section34Step_other_component_sets hprep hpack G' e₀ hoff hin e he).2]
      exact hcompOutOld e

end DifferentialGeometry.Topology.PiecewiseLinear
