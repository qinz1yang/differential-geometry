import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingSideConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingComponentClosure
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ProtectedCellMotion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusLocalConnectivity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}


theorem section34_first_annulus_eq_boundary_inter_tube
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    G (ends e).1 '' Aa e = G (ends e).1 '' CpBd (ends e).1 ∩ Tp e := by
  obtain ⟨-, -, hsub, -, hCp, -, -, -, -, -, -, htor, hSnCc, -, hAa, -⟩ := hprep
  obtain ⟨hG, -, -, htube, -⟩ := hpack
  rw [(hAa e).1, (hG (ends e).1).injOn.image_inter
    ((hCp _).boundary_subset.trans (hsub _).2.1)
    (((htor e).1.trans interior_subset).trans (hSnCc e _ (Or.inl rfl))), ← (htube e).2]

theorem section34_crossing_inside_slice
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {x : M₂}
    (hx : x ∈ G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' Bb e) :
    ∃ V : Set M₂, IsOpen V ∧ x ∈ V ∧
      IsPreconnected (G (ends e).2 '' Bb e ∩
        interior (G (ends e).1 '' Cp (ends e).1) ∩ V) ∧
      x ∈ closure (G (ends e).2 '' Bb e ∩
        interior (G (ends e).1 '' Cp (ends e).1) ∩ V) := by
  have hAeq := section34_first_annulus_eq_boundary_inter_tube hprep hpack e
  have hann := (section34_piercing_annuli hprep hpack e).2
  obtain ⟨-, -, hsub, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := id hprep
  obtain ⟨hG, -, -, -, -, -, hmeet, -, hBdis, -, hGp, -, -, -, -, -, -, -, -, hcross, -⟩ :=
    id hpack
  have hcellA := (hCp (ends e).1).image (hGp (ends e).1)
  have hcellB := (hCp (ends e).2).image (hGp (ends e).2)
  have hxmeet := hmeet e ⟨hx.1, image_mono (hBb e).1 hx.2⟩
  have hxtrace : x ∈ G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e :=
    ⟨image_mono sdiff_subset hxmeet.1.1, hx.2⟩
  obtain ⟨c, -, hxc, hcross⟩ := hcross e x hxtrace
  have hcongr : ∀ᶠ z in 𝓝 (c x),
      z ∈ c '' (G (ends e).1 '' Aa e ∩ c.source) ↔
        z ∈ c '' (frontier (G (ends e).1 '' Cp (ends e).1) ∩ c.source) := by
    filter_upwards [(c.isOpen_image_source_inter isOpen_interior).mem_nhds
      ⟨x, ⟨hxc, hxmeet.2⟩, rfl⟩] with z hz
    obtain ⟨y, ⟨hys, hyT⟩, rfl⟩ := hz
    have hmem (S : Set M₂) : c y ∈ c '' (S ∩ c.source) ↔ y ∈ S := by
      constructor
      · rintro ⟨w, ⟨hw, hws⟩, hwy⟩
        exact c.injOn hws hys hwy ▸ hw
      · exact fun hy => ⟨y, ⟨hy, hys⟩, rfl⟩
    rw [hmem, hmem, hAeq, ← hcellA.boundary_eq_frontier]
    exact and_iff_left (interior_subset hyT)
  have hcross' := hcross.symm.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) hcongr
  refine exists_connected_inside_slice_of_chart_crossing hcellA.isCompact.isClosed
    (X := G (ends e).1 '' Cp (ends e).1) ?_ c hxc hcross' ?_
  · have hcl : closure (interior (G (ends e).1 '' Cp (ends e).1)) =
        G (ends e).1 '' Cp (ends e).1 := by
      rw [← hcellA.sdiff_boundary_eq_interior]
      exact hcellA.closure_sdiff_boundary
    rw [hcl]
    exact hcellA.boundary_subset hx.1
  · intro N hN
    apply hcellB.exists_ball_chart_in_annulus hann (image_mono (hBb e).1) hx.2 ?_ hN
    intro hxends
    rw [← image_union] at hxends
    exact disjoint_left.mp (hBdis e).2 hxends (interior_subset hxmeet.2)

theorem section34_inside_local_sides
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∀ x ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
      ∃ V : Set M₂, IsOpen V ∧ x ∈ V ∧
        IsPreconnected (G (ends e).2 '' Bb e ∩
          interior (G (ends e).1 '' Cp (ends e).1) ∩ V) ∧
        x ∈ closure (G (ends e).2 '' Bb e ∩
          interior (G (ends e).1 '' Cp (ends e).1) ∩ V) := by
  intro x hx
  by_cases hxi : x ∈ interior (G (ends e).1 '' Cp (ends e).1)
  · let _ := (section34_piercing_annuli hprep hpack e).2.locallyConnectedSpace
    obtain ⟨V, hV, hxV, hVA, hconn⟩ :=
      exists_open_connected_inter_of_locallyConnectedSpace isOpen_interior hx.1 hxi
    have heq : G (ends e).2 '' Bb e ∩ interior (G (ends e).1 '' Cp (ends e).1) ∩ V =
        G (ends e).2 '' Bb e ∩ V := by
      ext y
      exact ⟨fun hy => ⟨hy.1.1, hy.2⟩, fun hy => ⟨⟨hy.1, hVA hy.2⟩, hy.2⟩⟩
    exact ⟨V, hV, hxV, heq ▸ hconn.isPreconnected, subset_closure ⟨⟨hx.1, hxi⟩, hxV⟩⟩
  · have hfront : G (ends e).1 '' CpBd (ends e).1 =
        frontier (G (ends e).1 '' Cp (ends e).1) := by
      obtain ⟨-, -, -, -, hCp, -⟩ := hprep
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := hpack
      exact ((hCp _).image_boundary_interior (hG _)).1
    exact section34_crossing_inside_slice hprep hpack e
      ⟨hfront.symm ▸ And.intro (subset_closure hx.2) hxi, hx.1⟩

theorem section34_inside_component_closure_eq
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (y : M₂)
    (hy : y ∈ G (ends e).2 '' Bb e ∩ interior (G (ends e).1 '' Cp (ends e).1)) :
    closure (connectedComponentIn
      (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) y) =
      connectedComponentIn (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y := by
  have hlocal := section34_inside_local_sides hprep hpack e
  apply section34_inside_component_closure_eq_of_local_sides hprep hpack e ?_ ?_ y hy
  · intro x hx
    obtain ⟨V, -, -, -, hxV⟩ := hlocal x hx
    exact closure_mono inter_subset_left hxV
  · intro x hx
    obtain ⟨V, hV, hxV, hc, -⟩ := hlocal x hx
    exact ⟨V, hV, hxV, hc⟩

end DifferentialGeometry.Topology.PiecewiseLinear
