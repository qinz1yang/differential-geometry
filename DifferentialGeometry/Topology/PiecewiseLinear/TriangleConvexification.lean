import DifferentialGeometry.Topology.PiecewiseLinear.LevelConvexification

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_triangle_image_strict_separation
    {D : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsPLBall 2 D)
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∉ interior D)
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2))
      (T : Finset (EuclideanSpace ℝ (Fin 2)))
      (ℓ : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ),
      T.card = 3 ∧ AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 2)) ∧
      IsPLHomeomorphOn h univ univ ∧ EqOn h id Uᶜ ∧
      h '' D = convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2))) ∧
      ℓ ≠ 0 ∧ ∀ x ∈ convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2))) \ {h p},
        ℓ (h p) < ℓ x := by
  classical
  obtain ⟨g, C, hC, hg, hgD, hgfront, hgfix⟩ :=
    exists_isPLHomeomorphOn_straighten_of_isPLBall_two hD hU hDU
  have hCtriangle := hC
  obtain ⟨v, hv, hCv⟩ := hC
  let T : Finset (EuclideanSpace ℝ (Fin 2)) := Finset.univ.image v
  have hTrange : (T : Set (EuclideanSpace ℝ (Fin 2))) = Set.range v := by simp [T]
  have hT : AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 2)) :=
    AffineIndependent.mono (t := Set.range v) hv.range (by rw [hTrange])
  have hcard : T.card = 3 := by
    rw [Finset.card_image_of_injective _ hv.injective]
    simp
  have hCT : C = convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [hCv, hTrange]
  have hCU : C ⊆ U := by
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := hgD.symm ▸ hy
    by_contra hxU
    have hgg : g (g x) = g x := hgfix hxU
    have heq : g x = x := g.injective hgg
    exact hxU (heq.symm ▸ hDU hx)
  by_cases hpD : p ∈ D
  · have hpfront : p ∈ frontier D := by
      rw [hD.isPolyhedron.isCompact.isClosed.frontier_eq]
      exact ⟨hpD, hp⟩
    have hgp : g p ∈ frontier C := hgfront ▸ mem_image_of_mem g hpfront
    have hspan : affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin 2))) = ⊤ := by
      have h := hT.affineSpan_eq_top_iff_card_eq_finrank_add_one
      rw [Subtype.range_coe] at h
      exact h.mpr (by simpa using hcard)
    have hboundary : (simplexBoundary T hT).space =
        frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2)))) := by
      rw [simplexBoundary_space T hT (by omega),
        frontier_convexHull_eq_biUnion_erase T hT hspan]
    obtain ⟨k, hk, hkC, hkp, hkfix⟩ :=
      exists_isPLHomeomorphOn_simplex_boundary_mem_vertices T hT (by omega) hspan
        (by rwa [hboundary, ← hCT]) hU (by rwa [← hCT])
    obtain ⟨ℓ, hℓ, hsep⟩ :=
      exists_linearMap_lt_on_convexHull_sdiff_singleton T hT (by omega) hkp
    have himage : (g.trans k) '' D = convexHull ℝ (T : Set _) := by
      change (k ∘ g) '' D = _
      rw [image_comp, hgD, hCT, hkC]
    refine ⟨g.trans k, T, ℓ, hcard, hT, hg.trans hk, ?_, himage, hℓ, hsep⟩
    intro x hx
    change k (g x) = x
    rw [hgfix hx, id_eq, hkfix hx, id_eq]
  · have hgp : g p ∉ C := by
      rw [← hgD]
      exact fun ⟨x, hx, hxp⟩ => hpD (g.injective hxp ▸ hx)
    obtain ⟨ℓ, u, hpu, hu⟩ := geometric_hahn_banach_point_closed hCtriangle.convex
      hCtriangle.isCompact.isClosed hgp
    have hCne : C.Nonempty := by
      rw [hCv]
      exact ⟨v 0, subset_convexHull ℝ _ (mem_range_self 0)⟩
    have hℓ : ℓ.toLinearMap ≠ 0 := by
      intro h
      obtain ⟨y, hy⟩ := hCne
      have hlt := hpu.trans (hu y hy)
      change ℓ.toLinearMap (g p) < ℓ.toLinearMap y at hlt
      simp only [h, LinearMap.zero_apply, lt_self_iff_false] at hlt
    refine ⟨g, T, ℓ.toLinearMap, hcard, hT, hg, hgfix, ?_, hℓ, ?_⟩
    · exact hgD.trans hCT
    · intro x hx
      apply hpu.trans
      apply hu x
      exact hCT ▸ hx.1

theorem exists_isPLHomeomorphOn_triangle_image_strict_separation_of_subset_fiber
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {D : Set E} (hD : IsPLBall 2 D) {r : ℝ} (hDr : D ⊆ {x | ℓ x = r})
    {p : E} (hpr : ℓ p = r) (hp : D ∉ 𝓝[{x | ℓ x = r}] p)
    {W : Set E} (hW : Convex ℝ W) (hWopen : IsOpen W) (hDW : D ⊆ W) :
    ∃ (h : E ≃ₜ E) (m : E →ₗ[ℝ] ℝ)
      (e : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] E)
      (T : Finset (EuclideanSpace ℝ (Fin 2))),
      IsPLHomeomorphOn h univ univ ∧ EqOn h id Wᶜ ∧
      (∀ x, ℓ (h x) = ℓ x) ∧ T.card = 3 ∧
      AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 2)) ∧
      Function.Injective e ∧ h '' D = e '' convexHull ℝ (T : Set _) ∧
      m ≠ 0 ∧ (∀ x ∈ h '' D \ {h p}, m (h p) < m x) ∧
      ∀ S : Set E, heightIndex (h '' S) ℓ = heightIndex S ℓ := by
  classical
  obtain ⟨e, π, hleft, hfixed, -⟩ :=
    exists_affine_coordinates_of_linear_fiber hdimE ℓ hℓ r
  obtain ⟨Q, hQ, hQcard, hDpQ, hQr, hQspan⟩ :=
    exists_affineIndependent_openSimplex_superset_of_subset_fiber hdimE ℓ hℓ
      (hD.isPolyhedron.isCompact.insert p).isBounded (by
        rintro x (rfl | hx)
        · exact hpr
        · exact hDr hx)
  have hDQ : D ⊆ openSimplex Q := fun x hx => hDpQ (mem_insert_of_mem p hx)
  have hpQ : p ∈ openSimplex Q := hDpQ (mem_insert p D)
  let P : Set E := convexHull ℝ (Q : Set E)
  let R : Finset (EuclideanSpace ℝ (Fin 2)) := Q.image π
  let C₀ : Set (EuclideanSpace ℝ (Fin 2)) := convexHull ℝ (R : Set _)
  have hP : IsPolyhedron P := isPolyhedron_convexHull_of_affineIndependent Q hQ
  have hDP : D ⊆ P := hDQ.trans (openSimplex_subset_convexHull Q)
  have hπinj : InjOn π P := by
    intro x hx y hy hxy
    exact ((hfixed x).mpr (hQr hx)).symm.trans
      ((congrArg e hxy).trans ((hfixed y).mpr (hQr hy)))
  have hR : AffineIndependent ℝ ((↑) : R → EuclideanSpace ℝ (Fin 2)) :=
    affineIndependent_image_of_injOn_convexHull π.toAffineMap hQ hπinj
  have hRcard : R.card = 3 := by
    rw [Finset.card_image_of_injOn (hπinj.mono (subset_convexHull ℝ _)), hQcard]
  have hRint : interior C₀ = openSimplex R := interior_convexHull_eq_openSimplex hR (by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using hRcard)
  have hC₀ : IsPolyhedron C₀ := isPolyhedron_convexHull_of_affineIndependent R hR
  have hπP : π '' P = C₀ := by
    change π.toAffineMap '' convexHull ℝ (Q : Set E) =
      convexHull ℝ ((Q.image π : Finset _) : Set _)
    rw [AffineMap.image_convexHull, Finset.coe_image]
    rfl
  have hπpl : IsPLHomeomorphOn π P C₀ :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP
      ((isPiecewiseAffineOn_of_affine π.toAffineMap isOpen_univ).mono_of_isPolyhedron
        hP (subset_univ _))
      ⟨fun x hx => hπP ▸ mem_image_of_mem π hx, hπinj,
        fun y hy => hπP.symm ▸ hy⟩
  have hepl : IsPLHomeomorphOn e C₀ P := hπpl.symm.congr (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hπpl.bijOn.surjOn hy
    exact ((hfixed x).mpr (hQr hx)).trans
      (hπpl.bijOn.invOn_invFunOn.1 hx).symm)
  have hπopen : π '' openSimplex Q = openSimplex R := by
    have h := image_openSimplex_affineMap π.toAffineMap Q
      (hπinj.mono (subset_convexHull ℝ _))
    simp only [LinearMap.coe_toAffineMap] at h
    convert h using 1
    congr 1
    ext y
    simp only [R, Finset.mem_image]
  have hDπ : IsPLBall 2 (π '' D) :=
    hD.of_isPLHomeomorphOn (hπpl.restrict hD.isPolyhedron hDP)
  let U := interior C₀ ∩ e ⁻¹' W
  have hU : IsOpen U := isOpen_interior.inter
    (hWopen.preimage e.continuous_of_finiteDimensional)
  have hDU : π '' D ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hRint, ← hπopen]
      exact mem_image_of_mem π (hDQ hx)
    · change e (π x) ∈ W
      rw [(hfixed x).mpr (hDr hx)]
      exact hDW hx
  have hπp : π p ∉ interior (π '' D) := by
    intro hπp
    apply hp
    have hcont : Filter.Tendsto π (𝓝[{x | ℓ x = r}] p) (𝓝 (π p)) :=
      π.continuous_of_finiteDimensional.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    filter_upwards [hcont (mem_interior_iff_mem_nhds.mp hπp), self_mem_nhdsWithin]
      with y hy hyr
    obtain ⟨x, hx, hxy⟩ := hy
    have heq := congrArg e hxy
    rw [(hfixed x).mpr (hDr hx), (hfixed y).mpr hyr] at heq
    exact heq ▸ hx
  obtain ⟨g, T, m, hTcard, hT, hg, hgfix, hgD, hm, hsep⟩ :=
    exists_isPLHomeomorphOn_triangle_image_strict_separation hDπ hπp hU hDU
  have hgfixC : EqOn g id C₀ᶜ := hgfix.mono
    (compl_subset_compl.mpr (inter_subset_left.trans interior_subset))
  have hgCbij : BijOn g C₀ C₀ := by
    simpa only [compl_compl] using
      ((bijOn_id C₀ᶜ).congr hgfixC.symm).compl g.bijective
  have hgC : IsPLHomeomorphOn g C₀ C₀ := by
    have h := hg.restrict hC₀ (subset_univ _)
    rwa [hgCbij.image_eq] at h
  let f : E → E := fun x => e (g (π x))
  have hf : IsPLHomeomorphOn f P P := hπpl.trans (hgC.trans hepl)
  have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
  let L := simplexComplex Q hQ
  let B := simplexBoundary Q hQ
  have hLspace : L.space = P := simplexComplex_space Q hQ hQne
  let _ : Finite L.faces := (simplexComplex_faces_finite Q hQ).to_subtype
  have hB : B.faces ⊆ L.faces := simplexBoundary_faces_subset_simplexComplex Q hQ
  have hBP : B.space ⊆ P := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := B.mem_space_iff.mp hx
    exact convexHull_mono (Finset.coe_subset.mpr hs.1) hxs
  have hfix : EqOn f id B.space := by
    intro x hx
    have hxP := hBP hx
    have hxU : π x ∉ U := by
      rintro ⟨hxint, -⟩
      rw [hRint, ← hπopen] at hxint
      obtain ⟨y, hy, hyx⟩ := hxint
      have heq := hπinj (openSimplex_subset_convexHull Q hy) hxP hyx
      have hxopen : x ∈ openSimplex Q := heq ▸ hy
      rw [openSimplex_eq_sdiff_simplexBoundary Q hQ] at hxopen
      exact hxopen.2 hx
    change e (g (π x)) = x
    rw [hgfix hxU, id_eq]
    exact (hfixed x).mpr (hQr hxP)
  have hfW : EqOn f id (L.space \ W) := by
    rintro x ⟨hx, hxW⟩
    have hxP : x ∈ P := hLspace ▸ hx
    have hxU : π x ∉ U := by
      rintro ⟨-, hyW⟩
      apply hxW
      change e (π x) ∈ W at hyW
      rwa [(hfixed x).mpr (hQr hxP)] at hyW
    change e (g (π x)) = x
    rw [hgfix hxU, id_eq]
    exact (hfixed x).mpr (hQr hxP)
  have hbase : ∀ x ∈ L.space, x ∉ B.space →
      L.space ∈ 𝓝[{y | ℓ y = r}] x := by
    intro x hx hxB
    have hxP : x ∈ P := hLspace ▸ hx
    have hxopen : x ∈ openSimplex Q := by
      rw [openSimplex_eq_sdiff_simplexBoundary Q hQ]
      exact ⟨hxP, hxB⟩
    have hgerm := (eventually_mem_convexHull_iff_sub_mem_vectorSpan hQ hxopen).filter_mono
      (nhdsWithin_le_nhds (s := {y | ℓ y = r}))
    filter_upwards [hgerm, self_mem_nhdsWithin] with y hy hyl
    rw [hLspace]
    apply hy.mpr
    rw [hQspan, LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.mpr (hyl.trans (hQr hxP).symm)
  have hfL : IsPLHomeomorphOn f L.space L.space := by rwa [hLspace]
  obtain ⟨h, hh, hhf, hhfix, hhℓ, hhInd⟩ :=
    exists_isPLHomeomorphOn_extension_preserving_height_of_eqOn_compl ℓ hℓ hB
      (hLspace.trans_le hQr) hbase hfL hfix hW hWopen hfW
  have himage : h '' D = e '' convexHull ℝ (T : Set _) := by
    rw [(hhf.mono (hDP.trans_eq hLspace.symm)).image_eq]
    change (e ∘ g ∘ π) '' D = e '' convexHull ℝ (T : Set _)
    rw [image_comp, image_comp, hgD]
  have hhp : h p = e (g (π p)) :=
    hhf (hLspace.symm ▸ openSimplex_subset_convexHull Q hpQ)
  have hmπ : m.comp π ≠ 0 := by
    intro hzero
    apply hm
    ext y
    have h := congrArg (fun l : E →ₗ[ℝ] ℝ => l (e y)) hzero
    simpa only [LinearMap.comp_apply, hleft y, LinearMap.zero_apply] using h
  refine ⟨h, m.comp π, e, T, hh, hhfix, hhℓ, hTcard, hT, hleft.injective,
    himage, hmπ, ?_, hhInd⟩
  rintro x ⟨hx, hxp⟩
  rw [himage] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyp : y ≠ g (π p) := by
    intro heq
    apply hxp
    change e y = h p
    rw [heq, hhp]
  change m (π (h p)) < m (π (e y))
  rw [hhp, hleft, hleft]
  exact hsep y ⟨hy, hyp⟩

end DifferentialGeometry.Topology.PiecewiseLinear
