import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentEmptyBands
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentBoundaryCrossings
import DifferentialGeometry.Topology.PiecewiseLinear.Section34OuterFaceAlignedFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierCancellationDescent

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

theorem exists_section34_current_carrier_band_filling
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (I : Set (Fin (cnt e)))
    (hlt : 1 < Nat.card I) (Ψ : M₂ ≃ₜ M₂) {K : Set M₂}
    (hK : IsCompact K) (hKS : K ⊆ interior (Sp e)) (hfix : EqOn Ψ id Kᶜ)
    (hΨ : IsPLOn 3 3 Ψ (interior (G (ends e).1 '' Cc (ends e).1)))
    (hrim : Disjoint K (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)))
    (hkeep : ∀ i : I, Disjoint K (Pg e i.1.val))
    (hcarry : ∀ i : I, CarriesFundamentalGroupOnto (Pg e i.1.val) (Sp e))
    (htrace : G (ends e).1 '' CpBd (ends e).1 ∩ Ψ '' (G (ends e).2 '' CpBd (ends e).2) =
      ⋃ i : I, Pg e i.1.val) :
    ∃ i j : I, i ≠ j ∧ ∃ D F : Set M₂,
      F ⊆ G (ends e).1 '' Aa e ∧ D ⊆ Ψ '' (G (ends e).2 '' Bb e) ∧
      Section34FaceAlignedBandFilling
        (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
        (G (ends e).1 '' CpBd (ends e).1) (Ψ '' (G (ends e).2 '' CpBd (ends e).2))
        (interior (Sp e)) D F (Pg e i.1.val) (Pg e j.1.val) := by
  classical
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, hSnCc, -, hAa, hBb, -⟩ := id hprep
  obtain ⟨-, -, -, htube, -, -, -, -, hBaS, -, hGp, -, -, -, -, -, -, hPg, hdis, -⟩ :=
    id hpack
  have hcellA := (hCp (ends e).1).image (hGp (ends e).1)
  have hcellB := (hCp (ends e).2).image (hGp (ends e).2)
  have hAB : Aa e ⊆ CpBd (ends e).1 := (hAa e).1 ▸ inter_subset_left
  have hBB := (hBb e).1
  have hAaB := image_mono (f := G (ends e).1) hAB
  have hBaB := image_mono (f := G (ends e).2) hBB
  have hSpCc : Sp e ⊆ G (ends e).1 '' Cc (ends e).1 := by
    rw [(htube e).1]
    exact image_mono (hSnCc e _ (Or.inl rfl))
  have hKP := hKS.trans (interior_mono hSpCc)
  have hcellB' := hcellB.image_of_supported_isPLOn Ψ hΨ isOpen_interior
    hK.isClosed hKP hfix
  have hAT : G (ends e).1 '' Aa e ⊆ interior (Sp e) := by
    apply Subset.trans _ (section34_inner_tube_subset_interior_outer hprep hpack e)
    rw [(htube e).2]
    exact image_mono ((hAa e).1 ▸ inter_subset_right)
  have himageS : Ψ '' interior (Sp e) = interior (Sp e) :=
    image_eq_of_homeomorph_eqOn_compl_of_subset Ψ hfix hKS
  have hBT : Ψ '' (G (ends e).2 '' Bb e) ⊆ interior (Sp e) :=
    himageS ▸ image_mono (hBaS e).1
  obtain ⟨hannA, hannB⟩ := section34_piercing_annuli hprep hpack e
  have hfixB : EqOn Ψ id (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) :=
    fun _ hx => hfix (disjoint_right.mp hrim hx)
  have hB₀ : Ψ '' (G (ends e).2 '' Bb₀ e) = G (ends e).2 '' Bb₀ e :=
    (image_congr (hfixB.mono (image_mono subset_union_left))).trans (image_id' _)
  have hB₁ : Ψ '' (G (ends e).2 '' Bb₁ e) = G (ends e).2 '' Bb₁ e :=
    (image_congr (hfixB.mono (image_mono subset_union_right))).trans (image_id' _)
  have hannB' := hannB.image_of_continuousOn_injOn Ψ.continuous.continuousOn Ψ.injective.injOn
  rw [hB₀, hB₁] at hannB'
  have hJA (j : Fin (cnt e)) : Pg e j.val ⊆ G (ends e).1 '' Aa e :=
    fun _ hx => image_mono sdiff_subset ((hPg e j.val j.isLt).2 hx).1
  have hJB (j : Fin (cnt e)) : Pg e j.val ⊆ G (ends e).2 '' Bb e :=
    fun _ hx => image_mono sdiff_subset ((hPg e j.val j.isLt).2 hx).2
  have hArim (j : Fin (cnt e)) : Disjoint (Pg e j.val)
      (G (ends e).1 '' Ab₀ e ∪ G (ends e).1 '' Ab₁ e) := by
    rw [← image_union]
    have hsub : Pg e j.val ⊆
        G (ends e).1 '' Aa e \ G (ends e).1 '' (Ab₀ e ∪ Ab₁ e) := by
      rw [← ((hGp _).injOn.mono (hAB.trans (hCp _).boundary_subset)).image_sdiff_subset
        (union_subset (hAa e).2.first_subset (hAa e).2.second_subset)]
      exact fun _ hx => ((hPg e j.val j.isLt).2 hx).1
    exact disjoint_left.mpr fun _ hx hy => (hsub hx).2 hy
  have hBrim (j : Fin (cnt e)) : Disjoint (Pg e j.val)
      (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) := by
    rw [← image_union]
    have hsub : Pg e j.val ⊆
        G (ends e).2 '' Bb e \ G (ends e).2 '' (Bb₀ e ∪ Bb₁ e) := by
      rw [← ((hGp _).injOn.mono (hBB.trans (hCp _).boundary_subset)).image_sdiff_subset
        (union_subset (hBb e).2.first_subset (hBb e).2.second_subset)]
      exact fun _ hx => ((hPg e j.val j.isLt).2 hx).2
    exact disjoint_left.mpr fun _ hx hy => (hsub hx).2 hy
  have hpair : Pairwise fun j l : Fin (cnt e) => Disjoint (Pg e j.val) (Pg e l.val) :=
    fun j l hjl => hdis e j.val j.isLt l.val l.isLt (fun heq => hjl (Fin.ext heq))
  have hJB' (i : I) : Pg e i.1.val ⊆ Ψ '' (G (ends e).2 '' Bb e) :=
    fun x hx => ⟨x, hJB i.1 hx, hfix (disjoint_right.mp (hkeep i) hx)⟩
  have hcross : ∀ x ∈ G (ends e).1 '' CpBd (ends e).1 ∩
      Ψ '' (G (ends e).2 '' CpBd (ends e).2),
      ∃ c : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3)), x ∈ c.source ∧
        HasPLCrossingAt
          (c '' (Ψ '' (G (ends e).2 '' CpBd (ends e).2) ∩ c.source))
          (c '' (G (ends e).1 '' CpBd (ends e).1 ∩ c.source)) (c x) := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (htrace.subset hx)
    have hnear : Ψ =ᶠ[𝓝 x] id := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds
        (disjoint_right.mp (hkeep i) hxi)] with y hy
      exact hfix hy
    obtain ⟨c, -, hxc, hc⟩ := section34_current_boundary_chart_crossing hprep hpack e Ψ
      ⟨hAaB (hJA i.1 hxi), hBaB (hJB i.1 hxi)⟩ hnear
    exact ⟨c, hxc, hc⟩
  let r : I ≃ Fin (Nat.card I) := Nat.equivFinOfCardPos (by omega)
  let Γ : Fin (Nat.card I) → Set M₂ := fun k => Pg e (r.symm k).1.val
  have hΓtrace : G (ends e).1 '' CpBd (ends e).1 ∩
      Ψ '' (G (ends e).2 '' CpBd (ends e).2) = ⋃ k, Γ k :=
    htrace.trans (r.symm.surjective.iUnion_comp (fun i : I => Pg e i.1.val)).symm
  obtain ⟨i, j, hij, P, Q', u, v, f, g, -, hu, -, hf, hfP, hFA, hf₀, hf₁, hFempty,
      -, hv, -, hg, hgQ, hDB, hg₀, hg₁, hDempty⟩ :=
    exists_section34_current_simultaneous_empty_bands hprep hpack e hcellA hcellB'
      hannA hannB' hAaB (image_mono hBaB) hAT hBT hlt Γ
      (fun k => (hPg e (r.symm k).1.val (r.symm k).1.isLt).1)
      (fun k => hJA (r.symm k).1) (fun k => hJB' (r.symm k))
      (fun k => hArim (r.symm k).1) (fun k => hBrim (r.symm k).1)
      (fun k l hkl => hpair (fun heq => hkl (r.symm.injective (Subtype.ext heq))))
      (fun k => hcarry (r.symm k)) hΓtrace hcross
  have hfp := hf.isPiecewiseAffineOn.isPolyhedron_image
    (isPolyhedron_stdSimplexBoundary_two.prod isHPolytope_Icc.isPolyhedron)
  have hgp := hg.isPiecewiseAffineOn.isPolyhedron_image
    (isPolyhedron_stdSimplexBoundary_two.prod isHPolytope_Icc.isPolyhedron)
  have huf := (hu.isPLOn.mono_of_isPolyhedron hfp hfP).isPLHomeomorphInto_model
    hfp.isCompact (hu.injOn.mono hfP)
  have hvg := (hv.isPLOn.mono_of_isPolyhedron hgp hgQ).isPLHomeomorphInto_model
    hgp.isCompact (hv.injOn.mono hgQ)
  have hFA' : u '' (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ⊆
      G (ends e).1 '' Aa e := by rwa [← image_comp]
  have hDB' : v '' (g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ⊆
      Ψ '' (G (ends e).2 '' Bb e) := by rwa [← image_comp]
  have hfill := exists_section34_outer_face_aligned_filling_of_empty_bands hprep hpack e
    hcellA hannA hAaB hAT hcellB' hannB' (image_mono hBaB) hBT
    ((hPg e (r.symm i).1.val (r.symm i).1.isLt).1)
    ((hPg e (r.symm j).1.val (r.symm j).1.isLt).1)
    (hpair (fun heq => hij (r.symm.injective (Subtype.ext heq))))
    (hArim (r.symm i).1) (hArim (r.symm j).1)
    (hBrim (r.symm i).1) (hBrim (r.symm j).1)
    (hcarry (r.symm i)) (hcarry (r.symm j)) hvg huf hg hf hDB' hFA'
    hg₀ hg₁ hf₀ hf₁ hDempty hFempty
  exact ⟨r.symm i, r.symm j, fun heq => hij (r.symm.injective heq), _, _, hFA', hDB', hfill⟩

end DifferentialGeometry.Topology.PiecewiseLinear
