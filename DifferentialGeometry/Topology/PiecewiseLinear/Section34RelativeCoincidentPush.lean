import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellDiskPatchPush

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPseudoCell.exists_relative_surface_push_of_ball_frontier
    {Ec Eint Ebd C Z O A : Set (EuclideanSpace ℝ (Fin 3))}
    {P : EuclideanSpace ℝ (Fin 3)} (hpc : IsPseudoCell Ec Eint Ebd P)
    (hC : IsPLBall 3 C) (hZ : IsCompact Z) (hZE : Z ⊆ Eint \ {P})
    (hO : IsOpen O) (hZO : Z ⊆ O) (hfront : O ∩ Ec = O ∩ frontier C)
    (hAC : A ∩ O ⊆ C) (hAZ : A ∩ O ∩ Ec ⊆ Z) :
    ∃ Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn Φ univ univ ∧ EqOn Φ id Oᶜ ∧
      Φ '' A ⊆ A ∪ O ∧ Φ '' A ∩ Ec = (A \ O) ∩ Ec := by
  obtain ⟨Φ, hΦ, hfix, hΦC⟩ := hpc.exists_push_of_ball_frontier hC hZ hZE hO hZO hfront
  have hmap : MapsTo Φ O O := by
    intro y hy
    by_contra hn
    have hyy := hΦ.bijOn.injOn (mem_univ y) (mem_univ (Φ y)) (hfix (Φ y) hn).symm
    exact hn (hyy ▸ hy)
  refine ⟨Φ, hΦ, fun x hx => hfix x hx, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    by_cases hxO : x ∈ O
    · exact Or.inr (hmap hxO)
    · rw [hfix x hxO]
      exact Or.inl hx
  · ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hxE⟩
      by_cases hxO : x ∈ O
      · obtain ⟨hxZ, hfixx⟩ := (hΦC x (hAC ⟨hx, hxO⟩)).2 hxE
        rw [hfixx] at hxE
        exact (hxZ (hAZ ⟨⟨hx, hxO⟩, hxE⟩)).elim
      · rw [hfix x hxO] at hxE ⊢
        exact ⟨⟨hx, hxO⟩, hxE⟩
    · rintro ⟨⟨hy, hyO⟩, hyE⟩
      exact ⟨⟨y, hy, hfix y hyO⟩, hyE⟩

theorem IsPseudoCell.exists_relative_push_of_coincident_patch_neighborhood
    {Ec Eint Ebd Γ D T Ω : Set (EuclideanSpace ℝ (Fin 3))}
    {P : EuclideanSpace ℝ (Fin 3)} (hpc : IsPseudoCell Ec Eint Ebd P)
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Γ)
    (hD : IsPLBall 2 D) (hDΓ : D ⊆ r '' openSimplex (stdVertices 1))
    (hDE : D ⊆ Eint \ {P}) (hT : IsClosed T) (hDT : Disjoint D T)
    (hΓE : Γ ∩ Ec ⊆ D ∪ T) (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn Φ univ univ ∧ EqOn Φ id Ωᶜ ∧ EqOn Φ id T ∧
      EqOn Φ id (r '' stdSimplexBoundary 2) ∧
      Φ '' Γ ⊆ Γ ∪ Ω ∧ Φ '' Γ ∩ Ec = (Γ \ D) ∩ Ec := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := fun a b => Classical.propDecidable (a = b)
  have hΓ : IsPLBall 2 Γ := ⟨r, hr⟩
  let J := r '' stdSimplexBoundary 2
  have hJ : IsClosed J := hr.isPLSphere_image_stdSimplexBoundary.isPolyhedron.isClosed
  have hDsub : D ⊆ Γ := hDΓ.trans ((image_mono
    (openSimplex_stdVertices_subset_stdSimplex (n := 1))).trans hr.image_eq.subset)
  have hDJ : Disjoint D J := by
    apply disjoint_left.mpr
    intro x hx hxJ
    have := hDΓ hx
    rw [hr.image_openSimplex_stdVertices] at this
    exact this.2 hxJ
  let W := (Ω ∩ Tᶜ) ∩ Jᶜ
  have hW : IsOpen W := (hΩ.inter hT.isOpen_compl).inter hJ.isOpen_compl
  have hDW : D ⊆ W := fun x hx =>
    ⟨⟨hDΩ hx, disjoint_left.mp hDT hx⟩, disjoint_left.mp hDJ hx⟩
  obtain ⟨M, s, hs, hME, hMW, hDM, hag⟩ :=
    hpc.exists_disk_neighborhood hD hDE hW hDW
  have hM : IsPLBall 2 M := ⟨s, hs⟩
  have hDsubM : D ⊆ M := hDM.trans ((image_mono
    (openSimplex_stdVertices_subset_stdSimplex (n := 1))).trans hs.image_eq.subset)
  have hMEc : M ⊆ Ec := fun x hx => hpc.carrierEq.symm ▸ Or.inl (hME hx).1
  have hΓM : Γ ∩ M = D := by
    apply Subset.antisymm
    · intro x hx
      exact (hΓE ⟨hx.1, hMEc hx.2⟩).resolve_right (hMW hx.2).1.2
    · exact subset_inter hDsub hDsubM
  let V := {x | ∀ᶠ y in 𝓝 x, y ∈ M ↔ y ∈ Ec} ∩ W
  have hV : IsOpen V := isOpen_setOfPred_eventually_nhds.inter hW
  have hDV : D ⊆ V := fun x hx => ⟨hag x hx, hDW hx⟩
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  obtain ⟨F, hF, hFcard, hFM⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    (hΓ.isPolyhedron.isCompact.union hM.isPolyhedron.isCompact).isBounded
  let K := simplexComplex F hF
  let _ : Finite K.faces := (simplexComplex_faces_finite F hF).to_subtype
  have hKspace : K.space = convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin 3))) :=
    simplexComplex_space F hF (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKspace.symm ▸
    isPLBall_convexHull_of_affineIndependent F hF hFcard
  have hK := hKball.isCombinatorialManifoldWithBoundary
  have hint : interior K.space = openSimplex F := by
    rw [hKspace, interior_convexHull_eq_openSimplex hF (by omega)]
  have hΓint : Γ ⊆ interior K.space :=
    (subset_union_left.trans hFM).trans hint.symm.subset
  have hMint : M ⊆ interior K.space :=
    (subset_union_right.trans hFM).trans hint.symm.subset
  have hDint : D ⊆ interior K.space := hDsub.trans hΓint
  have hUnhds : V ∩ interior K.space ∈ 𝓝ˢ[K.space] D :=
    mem_nhdsSetWithin.mpr ⟨V ∩ interior K.space, hV.inter isOpen_interior,
      subset_inter hDV hDint, inter_subset_left⟩
  have hUdis : Disjoint (V ∩ interior K.space) (boundaryComplex 3 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK]
    exact disjoint_interior_frontier.mono_left inter_subset_right
  have hlocal : Γ ∪ M ∈ 𝓝ˢ[Γ ∪ M] D :=
    mem_nhdsSetWithin.mpr ⟨univ, isOpen_univ, subset_univ D, inter_subset_right⟩
  obtain ⟨N, B, g, q₁, A₁, Δ₁, C', hBfin, -, hB, hDN, -, -,
      hNnhds, -, hg, -, -, -, hΔ₁, -, hfront, hinter, -, -, -, -, -, hΓB, -, -, -, -, -⟩ :=
    hK.exists_surface_split_local_traces_with_side_trace hD hr hs hDΓ hDM
      hDsub hDsubM hΓM (hΓint.trans interior_subset) (hMint.trans interior_subset)
      subset_union_left subset_union_right hlocal hUnhds hUdis
  let _ : Finite B.faces := hBfin.to_subtype
  have hNnhds' : ∀ x ∈ D, N ∈ 𝓝 x := by
    intro x hx
    have h := hNnhds x hx
    rwa [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp (hDint hx))] at h
  have hDΔ₁ : Disjoint D Δ₁ := by
    apply disjoint_left.mpr
    intro x hx hxΔ₁
    have hxg : x ∈ g '' stdSimplexBoundary 2 :=
      hinter.subset ⟨⟨hDsubM hx, hDN hx⟩, hxΔ₁⟩
    apply hg.notMem_image_stdSimplexBoundary_of_mem_nhdsWithin hpc.isOpenCell
      (hDE hx).1 ?_ hxg
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨N ∩ {y | y ∈ M ↔ y ∈ Ec}, Filter.inter_mem (hNnhds' x hx) (hag x hx), ?_⟩
    rintro y ⟨⟨hyN, hy⟩, hyE⟩
    exact ⟨hy.mpr (hpc.carrierEq.symm ▸ Or.inl hyE), hyN⟩
  let O := (interior N ∩ V) \ Δ₁
  have hO : IsOpen O := (isOpen_interior.inter hV).sdiff hΔ₁.isPolyhedron.isClosed
  have hDO : D ⊆ O := fun x hx =>
    ⟨⟨mem_interior_iff_mem_nhds.mpr (hNnhds' x hx), hDV hx⟩,
      disjoint_left.mp hDΔ₁ hx⟩
  have hOV : O ⊆ V := inter_subset_left.trans inter_subset_right
  have hON : O ⊆ N := (inter_subset_left.trans inter_subset_left).trans interior_subset
  have hfrontO : O ∩ Ec = O ∩ frontier B.space := by
    rw [frontier_space_eq_boundaryComplex_space_of_finrank hdim B
      hB.isCombinatorialManifoldWithBoundary, hfront]
    ext x
    constructor
    · rintro ⟨hxO, hxE⟩
      exact ⟨hxO, Or.inl ⟨(hOV hxO).1.self_of_nhds.mpr hxE, hON hxO⟩⟩
    · rintro ⟨hxO, hx | hx⟩
      · exact ⟨hxO, hMEc hx.1⟩
      · exact (hxO.2 hx).elim
  have hΓC : Γ ∩ O ⊆ B.space := fun x hx =>
    (hΓB.symm.subset ⟨hx.1, hON hx.2⟩).2
  have hΓD : Γ ∩ O ∩ Ec ⊆ D := fun x hx =>
    (hΓE ⟨hx.1.1, hx.2⟩).resolve_right (hOV hx.1.2).2.1.2
  have hJO : Disjoint (r '' stdSimplexBoundary 2) O :=
    disjoint_left.mpr fun x hxJ hxO => (hOV hxO).2.2 hxJ
  obtain ⟨Φ, hΦ, hfix, hΓ'sub, htrace⟩ :=
    hpc.exists_relative_surface_push_of_ball_frontier hB hD.isPolyhedron.isCompact hDE
      hO hDO hfrontO hΓC hΓD
  have hOΩ : O ⊆ Ω := hOV.trans (fun _ hx => hx.2.1.1)
  refine ⟨Φ, hΦ, hfix.mono (compl_subset_compl.mpr hOΩ), ?_, ?_,
    hΓ'sub.trans (union_subset subset_union_left (hOΩ.trans subset_union_right)), ?_⟩
  · exact fun x hxT => hfix (fun hxO => (hOV hxO).2.1.2 hxT)
  · exact fun x hxBd => hfix (disjoint_left.mp hJO hxBd)
  · rw [htrace]
    ext x
    constructor
    · rintro ⟨⟨hxΓ, hxO⟩, hxE⟩
      exact ⟨⟨hxΓ, fun hxD => hxO (hDO hxD)⟩, hxE⟩
    · rintro ⟨⟨hxΓ, hxD⟩, hxE⟩
      exact ⟨⟨hxΓ, fun hxO => hxD (hΓD ⟨⟨hxΓ, hxO⟩, hxE⟩)⟩, hxE⟩

theorem IsPseudoCell.exists_relative_push_of_coincident_patch
    {Ec Eint Ebd Γ D T Ω : Set (EuclideanSpace ℝ (Fin 3))}
    {P : EuclideanSpace ℝ (Fin 3)} (hpc : IsPseudoCell Ec Eint Ebd P)
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Γ)
    (hD : IsPLBall 2 D) (hDΓ : D ⊆ r '' openSimplex (stdVertices 1))
    (hDE : D ⊆ Eint \ {P}) (hT : IsClosed T) (hDT : Disjoint D T)
    (hΓE : Γ ∩ Ec ⊆ D ∪ T) (hΩ : IsOpen Ω) (hΓΩ : Γ ⊆ Ω) :
    ∃ Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn Φ univ univ ∧ EqOn Φ id Ωᶜ ∧ EqOn Φ id T ∧
      EqOn Φ id (r '' stdSimplexBoundary 2) ∧
      Φ '' Γ ⊆ Ω ∧ Φ '' Γ ∩ Ec = (Γ \ D) ∩ Ec := by
  have hDsub : D ⊆ Γ := hDΓ.trans ((image_mono
    (openSimplex_stdVertices_subset_stdSimplex (n := 1))).trans hr.image_eq.subset)
  obtain ⟨Φ, hΦ, hfix, hfixT, hfixBd, hsub, htrace⟩ :=
    hpc.exists_relative_push_of_coincident_patch_neighborhood hr hD hDΓ hDE hT hDT hΓE hΩ
      (hDsub.trans hΓΩ)
  exact ⟨Φ, hΦ, hfix, hfixT, hfixBd, hsub.trans (union_subset hΓΩ Subset.rfl), htrace⟩

end DifferentialGeometry.Topology.PiecewiseLinear
