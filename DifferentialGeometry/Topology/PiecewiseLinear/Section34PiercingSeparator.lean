import DifferentialGeometry.Topology.Connected.SeparatingComponent
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryGeneration
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusDiskLocalization
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.boundary_simplyConnectedSpace {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B : Set M}
    (hS : IsPLCellOn 3 S B) : SimplyConnectedSpace B := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hfront : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  let f : frontier P → M := fun x => u x.val
  have hf : Continuous f := (hu.continuousOn.mono hfront).domRestrict
  have hi : Function.Injective f := fun x y hxy =>
    Subtype.ext (hu.injOn (hfront x.property) (hfront y.property) hxy)
  let _ : CompactSpace (frontier P) :=
    isCompact_iff_compactSpace.mp hP.isPLSphere_frontier.isPolyhedron.isCompact
  have hfemb := (hf.isClosedEmbedding hi).isEmbedding
  have hrange : range f = B := by
    rw [hB]
    exact range_comp u Subtype.val |>.trans (by rw [Subtype.range_coe])
  let _ := hP.isPLSphere_frontier.twoSimplyConnectedSpace
  exact (hfemb.toHomeomorph.trans (Homeomorph.setCongr hrange)).symm.toHomotopyEquiv
    |>.simplyConnectedSpace

theorem IsPLCellOn.exists_separating_member_on_boundary {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B V H K : Set M} (hS : IsPLCellOn 3 S B) (hV : IsClosed V)
    {ι : Type*} [Finite ι] (C : ι → Set M) (hC : ∀ i, IsClosed (C i))
    (hd : Pairwise fun i j => Disjoint (C i) (C j))
    (htrace : B ∩ frontier V = ⋃ i, C i) (hH : IsConnected H) (hK : IsConnected K)
    (hHB : H ⊆ B) (hKB : K ⊆ B) (hHV : H ⊆ interior V) (hKV : Disjoint K V) :
    ∃ i, DifferentialGeometry.Topology.Separates
      ((Subtype.val : B → M) ⁻¹' C i) (Subtype.val ⁻¹' H) (Subtype.val ⁻¹' K) := by
  obtain ⟨hchart⟩ := hS.nonempty_chartedSpace_boundary
  let _ := hchart
  let _ := hS.boundary_simplyConnectedSpace
  let _ : LocallyPathConnectedSpace B :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) B
  have hconn {A : Set M} (hA : IsConnected A) (hAB : A ⊆ B) :
      IsConnected ((Subtype.val : B → M) ⁻¹' A) := by
    have himage : Subtype.val '' ((Subtype.val : B → M) ⁻¹' A) = A := by
      rw [Subtype.image_preimage_coe]
      exact inter_eq_right.mpr hAB
    refine ⟨?_, Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
    · obtain ⟨x, hx⟩ := hA.nonempty
      exact ⟨⟨x, hAB hx⟩, hx⟩
    · simpa only [himage] using hA.isPreconnected
  apply DifferentialGeometry.Topology.exists_separates_of_finite_iUnion
    (fun W hW hc => hW.isConnected_iff_isPathConnected.mp hc)
    (fun i => (Subtype.val : B → M) ⁻¹' C i)
    (fun i => (hC i).preimage continuous_subtype_val)
    (fun i j hij => (hd hij).preimage Subtype.val) (hconn hH hHB) (hconn hK hKB)
  refine ⟨Subtype.val ⁻¹' interior V, Subtype.val ⁻¹' Vᶜ,
    isOpen_interior.preimage continuous_subtype_val,
    hV.isOpen_compl.preimage continuous_subtype_val, ?_, ?_, fun _ hx => hHV hx, ?_⟩
  · exact disjoint_left.mpr fun x hx hy => hy (interior_subset hx)
  · ext x
    simp only [mem_union, mem_preimage, mem_compl_iff,
      mem_iUnion]
    have ht : (∃ i, ↑x ∈ C i) ↔ ↑x ∈ frontier V := by
      rw [← mem_iUnion, ← htrace]
      exact and_iff_right x.property
    rw [ht, hV.frontier_eq]
    simp only [mem_sdiff]
    tauto
  · exact fun x hx => disjoint_left.mp hKV hx

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

theorem exists_section34_piercing_circle_separating_first_ends
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ i < cnt e, DifferentialGeometry.Topology.Separates
      ((Subtype.val : (G (ends e).1 '' CpBd (ends e).1) → M₂) ⁻¹' Pg e i)
      (Subtype.val ⁻¹' (G (ends e).1 '' Ab₀ e))
      (Subtype.val ⁻¹' (G (ends e).1 '' Ab₁ e)) := by
  have hann := (section34_piercing_annuli hprep hpack e).1
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, hbound, hside, -, -, hG, -, -, -, -, -, htrace, hPg,
    hdisj, -⟩ := hpack
  have hAS : G (ends e).1 '' Aa e ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    image_mono ((hAa e).1 ▸ inter_subset_left)
  have hBS : G (ends e).2 '' Bb e ⊆ G (ends e).2 '' CpBd (ends e).2 :=
    image_mono (hBb e).1
  have htrace' : G (ends e).1 '' CpBd (ends e).1 ∩
      frontier (G (ends e).2 '' Cp (ends e).2) = ⋃ i : Fin (cnt e), Pg e i := by
    rw [← ((hCp (ends e).2).image_boundary_interior (hG (ends e).2)).1]
    ext x
    constructor
    · intro hx
      have hx' := (hbound e hx).1
      have hxA : x ∈ G (ends e).1 '' Aa e := image_mono sdiff_subset hx'.1
      have hxB : x ∈ G (ends e).2 '' Bb e := image_mono sdiff_subset hx'.2
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp ((htrace e).2.subset ⟨hxA, hxB⟩)
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      have hx' := (hPg e i i.isLt).2 hxi
      exact ⟨hAS (image_mono sdiff_subset hx'.1), hBS (image_mono sdiff_subset hx'.2)⟩
  have hclosed (i : Fin (cnt e)) : IsClosed (Pg e i) := by
    obtain ⟨P, -⟩ := (hPg e i i.isLt).1
    exact P.piece.isCompact.isClosed
  have hconn₀ : IsConnected (G (ends e).1 '' Ab₀ e) :=
    ⟨hann.ends_nonempty.1, hann.isPreconnected_ends.1⟩
  have hconn₁ : IsConnected (G (ends e).1 '' Ab₁ e) :=
    ⟨hann.ends_nonempty.2, hann.isPreconnected_ends.2⟩
  obtain ⟨i, hi⟩ := IsPLCellOn.exists_separating_member_on_boundary
      ((hCp (ends e).1).image (hG (ends e).1))
      ((hCp (ends e).2).isCompact.image_of_continuousOn (hG (ends e).2).continuousOn).isClosed
      (fun i : Fin (cnt e) => Pg e i) hclosed
      (fun i j hij => hdisj e i i.isLt j j.isLt (fun h => hij (Fin.ext h)))
      htrace' hconn₀ hconn₁ (hann.first_subset.trans hAS) (hann.second_subset.trans hAS)
      (hside e).1 (hside e).2
  exact ⟨i, i.isLt, hi⟩

end DifferentialGeometry.Topology.PiecewiseLinear
