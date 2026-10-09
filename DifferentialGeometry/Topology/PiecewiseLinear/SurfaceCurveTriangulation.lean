/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells
import DifferentialGeometry.Topology.PiecewiseLinear.LocalSurfaceLink
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyPolyhedral
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexMesh

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem notMem_boundaryComplex_two_of_two_cofaces {L : Geometry.SimplicialComplex ℝ E}
    (hL : ∀ u ∈ L.faces, u.card ≤ 3) {τ : Finset E} (hτc : τ.card = 2) {c d : E} (hcd : c ≠ d)
    (hc : c ∉ τ) (hd : d ∉ τ) (hcL : insert c τ ∈ L.faces) (hdL : insert d τ ∈ L.faces) :
    τ ∉ (boundaryComplex 2 L).faces := by
  intro hB
  obtain ⟨-, t, -, hτt, htc, hball⟩ := (mem_boundaryComplex_faces_iff 2 L).mp hB
  obtain rfl : τ = t := Finset.eq_of_subset_of_card_le hτt (by omega)
  rw [hτc, Nat.sub_self, geometricLink_space_eq_coface_vertices_of_card_le L τ
    (fun u hu _ => by have := hL u hu; omega), isPLBall_zero_iff] at hball
  obtain ⟨p, hp⟩ := hball
  have hcp : c ∈ ({p} : Set E) := by
    rw [← hp]
    exact ⟨hc, hcL⟩
  have hdp : d ∈ ({p} : Set E) := by
    rw [← hp]
    exact ⟨hd, hdL⟩
  exact hcd ((mem_singleton_iff.mp hcp).trans (mem_singleton_iff.mp hdp).symm)

open Classical in
theorem exists_isCombinatorialManifoldWithBoundary_two_curve_eventually_mem_iff {S Q : Set E}
    (hS : ∀ x ∈ S, ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U ∧ Nonempty (↥(W ∩ S) ≃ₜ U))
    (hloc : IsLocallyPolyhedral S) (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces]
    (hGdim : ∀ t ∈ G.faces, t.card ≤ 2) (hGS : G.space ⊆ S) (hQ : IsCompact Q) (hQS : Q ⊆ S) :
    ∃ L C : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 2 L ∧ C.faces ⊆ L.faces ∧
        (∀ t ∈ C.faces, t.card ≤ 2) ∧
        (∀ t ∈ C.faces, t.card = 2 → t ∉ (boundaryComplex 2 L).faces) ∧
        ∀ x ∈ Q, ∀ᶠ y in 𝓝 x, (y ∈ L.space ↔ y ∈ S) ∧ (y ∈ C.space ↔ y ∈ G.space) := by
  obtain ⟨P, hP, hQP, hPS, hPn⟩ := hloc.exists_isPolyhedron_neighborhood_of_isCompact hQ hQS
  obtain ⟨T₀, hT₀fin, hT₀⟩ := (hP.union (isPolyhedron_space G)).exists_simplicialComplex
  have : Finite T₀.faces := hT₀fin.to_subtype
  obtain ⟨T, hT, hTfin, hGT⟩ := exists_isSubdivision_restrict_isSubdivision T₀ G
    (by rw [hT₀]; exact subset_union_right)
  have : Finite T.faces := hTfin.to_subtype
  have hTspace : T.space = P ∪ G.space := hT.space_eq.trans hT₀
  have hTS : T.space ⊆ S := by
    rw [hTspace]
    exact union_subset hPS hGS
  have hO : IsOpen {x | ∀ᶠ y in 𝓝 x, y ∈ T.space ↔ y ∈ S} := isOpen_setOfPred_eventually_nhds
  have hQO : Q ⊆ {x | ∀ᶠ y in 𝓝 x, y ∈ T.space ↔ y ∈ S} := by
    intro x hx
    obtain ⟨V, hV, hVP⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hPn x hx)
    filter_upwards [hV] with y hyV
    refine ⟨fun hy => hTS hy, fun hy => ?_⟩
    rw [hTspace]
    exact Or.inl (hVP ⟨hyV, hy⟩)
  obtain ⟨δ, hδ, hδO⟩ := hQ.exists_cthickening_subset_open hO hQO
  obtain ⟨T', hT', hT'fin, hT'diam, hGT'⟩ := exists_isSubdivision_diam_lt_restrict_isSubdivision
    T (restrict T G.space) (restrict_faces_subset T G.space) (by positivity : (0 : ℝ) < δ / 4)
  have : Finite T'.faces := hT'fin.to_subtype
  have hGspace : (restrict T G.space).space = G.space := hGT.space_eq
  rw [hGspace] at hGT'
  have hT'space : T'.space = T.space := hT'.space_eq
  have hQ₁ : IsCompact (cthickening (δ / 2) Q ∩ T.space) :=
    hQ.cthickening.inter_right (isPolyhedron_space T).isClosed
  have hQ₁O : cthickening (δ / 2) Q ∩ T.space ⊆ {x | ∀ᶠ y in 𝓝 x, y ∈ T.space ↔ y ∈ S} :=
    fun x hx => hδO (cthickening_mono (by linarith) Q hx.1)
  have hQ₁T : cthickening (δ / 2) Q ∩ T.space ⊆ T'.space := by
    rw [hT'space]
    exact inter_subset_right
  have hlink : ∀ J : Geometry.SimplicialComplex ℝ E, IsSubdivision J T' → J.faces.Finite →
      ∀ v ∈ {x | ∀ᶠ y in 𝓝 x, y ∈ T.space ↔ y ∈ S}, ({v} : Finset E) ∈ J.faces →
        IsPLSphere 1 (SimplicialComplex.geometricLink J {v}).space ∨
          IsPLBall 1 (SimplicialComplex.geometricLink J {v}).space := by
    intro J hJ hJfin v hv hvJ
    have : Finite J.faces := hJfin.to_subtype
    have hvJs : v ∈ J.space := J.convexHull_subset_space hvJ (by simp)
    have hvS : v ∈ S := hTS (by rw [← hT'space, ← hJ.space_eq]; exact hvJs)
    obtain ⟨W, hW, hvW, U, hU, ⟨ψ⟩⟩ := hS v hvS
    refine Or.inl (isPLSphere_one_geometricLink_of_homeomorph J hU ψ hvJ ?_)
    have hv' : ∀ᶠ y in 𝓝 v, y ∈ T.space ↔ y ∈ S := hv
    filter_upwards [hv', hW.mem_nhds hvW] with y hy hyW
    rw [hJ.space_eq, hT'space]
    exact hy.trans ⟨fun h => ⟨hyW, h⟩, fun h => h.2⟩
  obtain ⟨K', L, hK', hK'fin, hLK', hL, -, hLn⟩ :=
    exists_isSubdivision_neighborhood_of_forall_geometricLink hQ₁ hQ₁T hO hQ₁O hlink
  have : Finite K'.faces := hK'fin.to_subtype
  have hK'T : K'.space = T.space := hK'.space_eq.trans hT'space
  have hLfin : L.faces.Finite := hK'fin.subset hLK'
  have : Finite L.faces := hLfin.to_subtype
  have hLT : L.space ⊆ T.space := hK'T ▸ space_mono_of_faces_subset hLK'
  have hK'diam : ∀ s ∈ K'.faces, diam (convexHull ℝ (s : Set E)) < δ / 4 := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hK'.exists_face_subset hs
    exact (diam_mono hst (t.finite_toSet.isCompact_convexHull ℝ).isBounded).trans_lt
      (hT'diam t ht)
  have hGK' : IsSubdivision (restrict K' G.space) (restrict T' G.space) := by
    have h := hK'.restrict (restrict T' G.space) (restrict_faces_subset T' G.space)
    rwa [hGT'.space_eq, hGspace] at h
  have hK'G : (restrict K' G.space).space = G.space :=
    hGK'.space_eq.trans (hGT'.space_eq.trans hGspace)
  have hcardG : ∀ s ∈ (restrict K' G.space).faces, s.card ≤ 2 :=
    fun s hs => (hGK'.trans (hGT'.trans hGT)).card_le hGdim hs
  have hLcard : ∀ u ∈ L.faces, u.card ≤ 3 := by
    intro u hu
    have := hL.card_le L hu
    omega
  refine ⟨L, restrict L (G.space ∩ (cthickening (δ / 2) Q ∩ T.space)), hLfin, hL,
    restrict_faces_subset L _, fun s hs => hcardG s ⟨hLK' hs.1, hs.2.trans inter_subset_left⟩,
    ?_, ?_⟩
  · intro τ hτ hτc
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hτc
    have haτ : a ∈ convexHull ℝ (({a, b} : Finset E) : Set E) := subset_convexHull ℝ _ (by simp)
    have haQ₁ : a ∈ cthickening (δ / 2) Q ∩ T.space := (hτ.2 haτ).2
    have haG : a ∈ G.space := (hτ.2 haτ).1
    obtain ⟨V, hV, hVL⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hLn a haQ₁)
    have hstar : ∀ σ ∈ K'.faces, a ∈ σ → σ ∈ L.faces := by
      intro σ hσ haσ
      obtain ⟨y, hy, hyV⟩ := exists_mem_openSimplex_mem_of_mem (K'.nonempty_of_mem_faces hσ) haσ hV
      have hyT : y ∈ T.space := by
        rw [← hK'T]
        exact K'.convexHull_subset_space hσ (openSimplex_subset_convexHull σ hy)
      exact mem_faces_of_mem_openSimplex_of_mem_space hLK' hσ hy
        (hVL ⟨hyV, by rw [hT'space]; exact hyT⟩)
    have hcard3 : ∀ s ∈ K'.faces, a ∈ s → s.card ≤ 3 :=
      fun s hs has => hLcard s (hstar s hs has)
    obtain ⟨W₀, hW₀, haW₀, U, hU, ⟨ψ⟩⟩ := hS a (hGS haG)
    obtain ⟨V', hV'p, hV'o, haV'⟩ := _root_.eventually_nhds_iff.mp (hQ₁O haQ₁)
    have hW : IsOpen (W₀ ∩ V') := hW₀.inter hV'o
    have hWK : (W₀ ∩ V') ∩ K'.space = (W₀ ∩ V') ∩ (W₀ ∩ S) := by
      ext y
      constructor
      · rintro ⟨⟨hy₀, hy'⟩, hyK⟩
        exact ⟨⟨hy₀, hy'⟩, hy₀, (hV'p y hy').mp (by rw [← hK'T]; exact hyK)⟩
      · rintro ⟨⟨hy₀, hy'⟩, -, hyS⟩
        exact ⟨⟨hy₀, hy'⟩, by rw [hK'T]; exact (hV'p y hy').mpr hyS⟩
    have haW : a ∈ W₀ ∩ V' := ⟨haW₀, haV'⟩
    obtain ⟨t₁, ht₁, hτt₁, ht₁c⟩ :=
      exists_card_three_superset_of_inter_eq K' hU ψ hW hWK haW hcard3 (hLK' hτ.1) (by simp)
    obtain ⟨c, hc⟩ : ∃ c, t₁ \ {a, b} = {c} :=
      Finset.card_eq_one.mp (by rw [Finset.card_sdiff_of_subset hτt₁, ht₁c, hτc])
    have hcmem : c ∈ t₁ \ {a, b} := by
      rw [hc]
      exact Finset.mem_singleton_self c
    rw [Finset.mem_sdiff] at hcmem
    have hca : a ≠ c := fun h => hcmem.2 (by simp [h])
    have hcb : b ≠ c := fun h => hcmem.2 (by simp [h])
    have ht₁eq : t₁ = {a, b, c} := by
      ext z
      constructor
      · intro hz
        by_cases hzab : z ∈ ({a, b} : Finset E)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hzab ⊢
          tauto
        · have hz' : z ∈ t₁ \ {a, b} := Finset.mem_sdiff.mpr ⟨hz, hzab⟩
          rw [hc, Finset.mem_singleton] at hz'
          simp [hz']
      · intro hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hτt₁ (by simp)
        · exact hτt₁ (by simp)
        · exact hcmem.1
    rw [ht₁eq] at ht₁
    obtain ⟨d, hda, hdb, hdc, hd⟩ :=
      exists_second_triangle_of_inter_eq K' hU ψ hW hWK hab hca hcb ht₁ haW
    have hinsc : insert c ({a, b} : Finset E) = {a, b, c} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hinsd : insert d ({a, b} : Finset E) = {a, b, d} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    refine notMem_boundaryComplex_two_of_two_cofaces hLcard hτc (Ne.symm hdc)
      (by simp [hca.symm, hcb.symm]) (by simp [hda, hdb]) ?_ ?_
    · rw [hinsc]
      exact hstar _ ht₁ (by simp)
    · rw [hinsd]
      exact hstar _ hd (by simp)
  · intro x hx
    have hxQ₁ : x ∈ cthickening (δ / 2) Q ∩ T.space :=
      ⟨self_subset_cthickening Q hx, by rw [hTspace]; exact Or.inl (hQP hx)⟩
    obtain ⟨V, hV, hVL⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hLn x hxQ₁)
    filter_upwards [hV, hQO hx, ball_mem_nhds x (by positivity : (0 : ℝ) < δ / 4)]
      with y hyV hyTS hyball
    refine ⟨⟨fun hyL => hTS (hLT hyL), fun hyS => hVL ⟨hyV, by rw [hT'space]; exact hyTS.mpr hyS⟩⟩,
      fun hyC => (restrict_space_subset L _ hyC).1, fun hyG => ?_⟩
    have hyT : y ∈ T.space := by
      rw [hTspace]
      exact Or.inr hyG
    have hyL : y ∈ L.space := hVL ⟨hyV, by rw [hT'space]; exact hyT⟩
    obtain ⟨σ, hσ, hyσ⟩ := exists_face_mem_openSimplex K' (by rw [hK'T]; exact hyT)
    have hσL : σ ∈ L.faces := mem_faces_of_mem_openSimplex_of_mem_space hLK' hσ hyσ hyL
    have hσG : σ ∈ (restrict K' G.space).faces :=
      mem_faces_of_mem_openSimplex_of_mem_space (restrict_faces_subset K' _) hσ hyσ
        (by rw [hK'G]; exact hyG)
    have hσQ₁ : convexHull ℝ (σ : Set E) ⊆ cthickening (δ / 2) Q ∩ T.space := by
      intro z hz
      refine ⟨?_, by rw [← hK'T]; exact K'.convexHull_subset_space hσ hz⟩
      have hzy : dist z y ≤ diam (convexHull ℝ (σ : Set E)) :=
        dist_le_diam_of_mem (σ.finite_toSet.isCompact_convexHull ℝ).isBounded hz
          (openSimplex_subset_convexHull σ hyσ)
      have hyx : dist y x < δ / 4 := hyball
      apply mem_cthickening_of_dist_le z x (δ / 2) Q hx
      linarith [dist_triangle z y x, hK'diam σ hσ]
    exact (restrict L _).convexHull_subset_space ⟨hσL, subset_inter hσG.2 hσQ₁⟩
      (openSimplex_subset_convexHull σ hyσ)

end DifferentialGeometry.Topology.PiecewiseLinear
