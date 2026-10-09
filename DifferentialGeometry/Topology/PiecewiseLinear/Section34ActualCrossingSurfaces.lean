import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualCrossingSurfacesTransport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandNeighborhood

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


theorem section34_piercing_circle_annulus_neighborhood
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e) :
    G (ends e).2 '' Bb e ∈ 𝓝ˢ[G (ends e).2 '' CpBd (ends e).2] (Pg e i) ∧
      G (ends e).2 '' Bb e ⊆ interior (G (ends e).1 '' Cc (ends e).1) ∧
      Pg e i ⊆ G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 := by
  have hann := (section34_piercing_annuli hprep hpack e).2
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, hSnCc, -, hAa, hBb, -⟩ := hprep
  obtain ⟨-, -, -, hEq, -, -, -, -, hBB, -, hGcp, -, -, -, -, -, -, hPg, -⟩ := hpack
  have hBCp := (hBb e).1.trans (hCp (ends e).2).boundary_subset
  have hBends := union_subset (hBb e).2.first_subset (hBb e).2.second_subset
  have hJminus : Pg e i ⊆ G (ends e).2 '' Bb e \
      (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) := by
    have ht := ((hPg e i hi).2).trans inter_subset_right
    rwa [((hGcp (ends e).2).injOn.mono hBCp).image_sdiff_subset hBends, image_union] at ht
  have hBS : G (ends e).2 '' Bb e ⊆ G (ends e).2 '' CpBd (ends e).2 :=
    image_mono (hBb e).1
  have hJS := (hJminus.trans sdiff_subset).trans hBS
  have hcell := (hCp (ends e).2).image (hGcp (ends e).2)
  have hpoint (x : M₂) (hx : x ∈ Pg e i) :
      G (ends e).2 '' Bb e ∈ 𝓝[G (ends e).2 '' CpBd (ends e).2] x :=
    hcell.annulus_mem_nhdsWithin_of_not_mem_ends hann hBS (hJminus hx).1 (hJminus hx).2
  have hnear : G (ends e).2 '' Bb e ∈
      𝓝ˢ[G (ends e).2 '' CpBd (ends e).2] (Pg e i) := by
    have hpre : (Subtype.val : (G (ends e).2 '' CpBd (ends e).2) → M₂) ⁻¹'
        (G (ends e).2 '' Bb e) ∈ 𝓝ˢ (Subtype.val ⁻¹' Pg e i) :=
      mem_nhdsSet_iff_forall.mpr fun x hx =>
        preimage_coe_mem_nhds_subtype.mpr (hpoint x hx)
    have ht := mem_nhdsSet_subtype_iff_nhdsSetWithin.mp hpre
    rwa [Subtype.image_preimage_coe, Subtype.image_preimage_coe,
      inter_eq_right.mpr hBS, inter_eq_right.mpr hJS] at ht
  have hSpCc : Sp e ⊆ G (ends e).1 '' Cc (ends e).1 := by
    rw [(hEq e).1]
    exact image_mono (hSnCc e _ (Or.inl rfl))
  refine ⟨hnear, (hBB e).1.trans (interior_mono hSpCc), ?_⟩
  intro x hx
  exact ⟨image_mono (sdiff_subset.trans ((hAa e).1 ▸ inter_subset_left))
    ((hPg e i hi).2 hx).1, hJS hx⟩

open Classical in
theorem exists_section34_actual_crossing_surfaces_in_model
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P) (hmodel : u '' P = G (ends e).1 '' Cc (ends e).1) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
    ∃ (K₀ K₁ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (N : Set (EuclideanSpace ℝ (Fin 3))), ∃ hfin₀ : K₀.faces.Finite,
      ∃ hfin₁ : K₁.faces.Finite,
      let _ : Finite K₀.faces := hfin₀.to_subtype
      let _ : Finite K₁.faces := hfin₁.to_subtype
      IsCombinatorialManifold 2 K₀ ∧ IsCombinatorialManifoldWithBoundary 2 K₁ ∧
      IsOrientable 2 K₀ ∧ IsOrientable 2 K₁ ∧ K₀.space ⊆ P ∧ K₁.space ⊆ interior P ∧
      K₀.space = Function.invFunOn u P '' (G (ends e).1 '' CpBd (ends e).1) ∧
      u '' K₁.space ⊆ G (ends e).2 '' CpBd (ends e).2 ∩ G (ends e).2 '' Bb e ∧
      IsPLSphere 1 (Function.invFunOn u P '' Pg e i) ∧
      Function.invFunOn u P '' Pg e i ⊆ K₀.space ∩ K₁.space ∧
      Disjoint (Function.invFunOn u P '' Pg e i) (boundaryComplex 2 K₀).space ∧
      Disjoint (Function.invFunOn u P '' Pg e i) (boundaryComplex 2 K₁).space ∧
      IsOpen N ∧ Function.invFunOn u P '' Pg e i ⊆ N ∧ N ⊆ interior P ∧
      N ∩ K₀.space = N ∩ u ⁻¹' (G (ends e).1 '' CpBd (ends e).1) ∧
      N ∩ K₁.space = N ∩ u ⁻¹' (G (ends e).2 '' CpBd (ends e).2) ∧
      (K₀.space ∩ K₁.space) ∩ N ⊆ Function.invFunOn u P '' Pg e i := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨hnear, hBint, hJboth⟩ :=
    section34_piercing_circle_annulus_neighborhood hprep hpack e hi
  obtain ⟨-, -, hsub, -, hCp, -, -, -, -, -, -, -, -, -, hAa, hBb, -⟩ := hprep
  obtain ⟨hG, -, -, -, -, -, hbound, -, -, -, hGcp, -, -, -, -, -, htrace, hPg,
    hdisj, -⟩ := hpack
  have hmodel : G (ends e).1 '' Cc (ends e).1 = u '' P := hmodel.symm
  have hfirst := (hCp (ends e).1).image (hGcp (ends e).1)
  have hsecond := (hCp (ends e).2).image (hGcp (ends e).2)
  have hfirstP : G (ends e).1 '' Cp (ends e).1 ⊆ u '' P :=
    hmodel ▸ image_mono (hsub (ends e).1).2.1
  obtain ⟨K₀, hfin₀, -, hK₀, hor₀, hK₀space, hK₀P, hK₀image, hK₀bd⟩ :=
    hu.exists_spherical_surface_complex_in_model hfirst hfirstP
  let _ : Finite K₀.faces := hfin₀.to_subtype
  have hBP : G (ends e).2 '' Bb e ⊆ interior (u '' P) := hmodel ▸ hBint
  have hJP : Pg e i ⊆ interior (u '' P) :=
    fun _ hx => hBP (image_mono sdiff_subset ((hPg e i hi).2 hx).2)
  obtain ⟨K₁, N₁, hfin₁, hK₁, hor₁, hK₁P, hK₁image, hJ, hJK₁, hJbd₁,
    hN₁, hJN₁, hN₁P, hN₁trace⟩ :=
    hu.exists_annular_surface_complex_in_model hsecond (hPg e i hi).1
      (hJboth.trans inter_subset_right) hJP hnear hBP
  let _ : Finite K₁.faces := hfin₁.to_subtype
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hJK₀ : τ '' Pg e i ⊆ K₀.space :=
    hK₀space.symm ▸ image_mono (hJboth.trans inter_subset_left)
  let I := {j : Fin (cnt e) // j.val ≠ i}
  let Z : Set M₂ := ⋃ j : I, Pg e j.val.val
  have hZclosed : IsClosed Z := by
    apply isClosed_iUnion_of_finite
    intro j
    obtain ⟨T, -⟩ := (hPg e j.val.val j.val.isLt).1
    exact T.piece.isCompact.isClosed
  have hJZ : Pg e i ⊆ Zᶜ := by
    intro x hx hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    exact disjoint_left.mp (hdisj e i hi j.val.val j.val.isLt j.property.symm) hx hj
  let N := N₁ ∩ u ⁻¹' Zᶜ
  have hN : IsOpen N :=
    (hu.continuousOn.mono (hN₁P.trans interior_subset)).isOpen_inter_preimage
      hN₁ hZclosed.isOpen_compl
  have hJN : τ '' Pg e i ⊆ N := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hJN₁ ⟨x, hx, rfl⟩, ?_⟩
    change u (τ x) ∉ Z
    rw [hright (interior_subset (hJP hx))]
    exact hJZ hx
  have hNP : N ⊆ interior P := inter_subset_left.trans hN₁P
  have hNfirst : N ∩ K₀.space = N ∩ u ⁻¹' (G (ends e).1 '' CpBd (ends e).1) := by
    apply Subset.antisymm
    · rintro x ⟨hxN, hxK⟩
      exact ⟨hxN, hK₀image ▸ mem_image_of_mem u hxK⟩
    · rintro x ⟨hxN, hxB⟩
      refine ⟨hxN, ?_⟩
      rw [hK₀space]
      exact ⟨u x, hxB, hleft (interior_subset (hNP hxN))⟩
  have hNsecond : N ∩ K₁.space = N ∩ u ⁻¹' (G (ends e).2 '' CpBd (ends e).2) := by
    ext x
    constructor
    · rintro ⟨hxN, hxK⟩
      exact ⟨hxN, (hN₁trace.subset ⟨hxN.1, hxK⟩).2⟩
    · rintro ⟨hxN, hxB⟩
      exact ⟨hxN, (hN₁trace.symm.subset ⟨hxN.1, hxB⟩).2⟩
  refine ⟨K₀, K₁, N, hfin₀, hfin₁, hK₀, hK₁,
    hor₀, hor₁, hK₀P, hK₁P, hK₀space, hK₁image, hJ,
    subset_inter hJK₀ hJK₁, ?_, hJbd₁, hN, hJN, hNP, hNfirst, hNsecond, ?_⟩
  · rw [hK₀bd]
    simp
  · rintro x ⟨⟨hx₀, hx₁⟩, hxN⟩
    have hwhole := (hbound e ⟨(hNfirst.subset ⟨hxN, hx₀⟩).2,
      (hNsecond.subset ⟨hxN, hx₁⟩).2⟩).1
    have huxtrace : u x ∈ G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e :=
      ⟨image_mono sdiff_subset hwhole.1, image_mono sdiff_subset hwhole.2⟩
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp ((htrace e).2.subset huxtrace)
    have hji : j = i := by
      by_contra hne
      exact hxN.2 (mem_iUnion.mpr ⟨⟨⟨j, hj⟩, hne⟩, hxj⟩)
    exact ⟨u x, hji ▸ hxj, hleft (interior_subset (hNP hxN))⟩

open Classical in
theorem exists_section34_actual_crossing_surfaces
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
      (K₀ K₁ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (N : Set (EuclideanSpace ℝ (Fin 3))), ∃ hfin₀ : K₀.faces.Finite,
      ∃ hfin₁ : K₁.faces.Finite,
      let _ : Finite K₀.faces := hfin₀.to_subtype
      let _ : Finite K₁.faces := hfin₁.to_subtype
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).1 '' Cc (ends e).1 ∧
      IsCombinatorialManifold 2 K₀ ∧ IsCombinatorialManifoldWithBoundary 2 K₁ ∧
      IsOrientable 2 K₀ ∧ IsOrientable 2 K₁ ∧ K₀.space ⊆ P ∧ K₁.space ⊆ interior P ∧
      K₀.space = Function.invFunOn u P '' (G (ends e).1 '' CpBd (ends e).1) ∧
      u '' K₁.space ⊆ G (ends e).2 '' CpBd (ends e).2 ∩ G (ends e).2 '' Bb e ∧
      IsPLSphere 1 (Function.invFunOn u P '' Pg e i) ∧
      Function.invFunOn u P '' Pg e i ⊆ K₀.space ∩ K₁.space ∧
      Disjoint (Function.invFunOn u P '' Pg e i) (boundaryComplex 2 K₀).space ∧
      Disjoint (Function.invFunOn u P '' Pg e i) (boundaryComplex 2 K₁).space ∧
      IsOpen N ∧ Function.invFunOn u P '' Pg e i ⊆ N ∧ N ⊆ interior P ∧
      N ∩ K₀.space = N ∩ u ⁻¹' (G (ends e).1 '' CpBd (ends e).1) ∧
      N ∩ K₁.space = N ∩ u ⁻¹' (G (ends e).2 '' CpBd (ends e).2) ∧
      (K₀.space ∩ K₁.space) ∩ N ⊆ Function.invFunOn u P '' Pg e i := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨-, hCc, -⟩ := id hprep
  obtain ⟨hG, -⟩ := id hpack
  obtain ⟨P, r, u, hr, hu, hmodel, -⟩ := (hCc (ends e).1).image (hG (ends e).1)
  obtain ⟨K₀, K₁, N, hfin₀, hfin₁, hK⟩ :=
    exists_section34_actual_crossing_surfaces_in_model hprep hpack e hi hu hmodel.symm
  exact ⟨P, u, K₀, K₁, N, hfin₀, hfin₁, ⟨r, hr⟩, hu, hmodel.symm, hK⟩

end DifferentialGeometry.Topology.PiecewiseLinear
