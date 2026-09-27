/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallVocabulary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem HasPLCurveCrossingOnAt.congr {S A B S' A' B' : Set E} {x : E}
    (hc : HasPLCurveCrossingOnAt S A B x) (hS : ∀ᶠ y in 𝓝 x, y ∈ S ↔ y ∈ S')
    (hA : ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ A') (hB : ∀ᶠ y in 𝓝 x, y ∈ B ↔ y ∈ B') :
    HasPLCurveCrossingOnAt S' A' B' x := by
  obtain ⟨U, V, φ, T, P, Q, hU, hV, hxU, hφ, hφx, hT, hP, hQ, hPT, hQT, hPQ, hlocal⟩ := hc
  refine ⟨U, V, φ, T, P, Q, hU, hV, hxU, hφ, hφx, hT, hP, hQ, hPT, hQT, hPQ, ?_⟩
  filter_upwards [hlocal, hS, hA, hB] with y hy hyS hyA hyB
  exact ⟨hyS.symm.trans hy.1, hyA.symm.trans hy.2.1, hyB.symm.trans hy.2.2⟩

open Classical in
theorem exists_isPLHomeomorphOn_linearize_coface_pair_fixing [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {s : Finset E} (hs : s ∈ K.faces)
    (hbound : ∀ t ∈ K.faces, s ⊆ t → t.card ≤ s.card + 1) {x a b : E}
    (hx : x ∈ openSimplex s) (hab : a ≠ b)
    (hpair : {w | w ∉ s ∧ insert w s ∈ K.faces} = {a, b}) (T : Submodule ℝ E)
    (hcompl : IsCompl (vectorSpan ℝ (s : Set E)) T) :
    ∃ (u : E) (h : E → E), u ∈ T ∧ u ≠ 0 ∧ IsPLHomeomorphOn h univ univ ∧
      (∀ y, y - x ∈ T ↔ h y ∈ T) ∧
      (∀ᶠ y in 𝓝 x, y ∈ K.space ↔ h y ∈ vectorSpan ℝ (s : Set E) ⊔ Submodule.span ℝ {u}) ∧
      ∀ y, y - x ∈ vectorSpan ℝ (s : Set E) → h y = y - x := by
  have ha : a ∉ s ∧ insert a s ∈ K.faces := by
    change a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
    rw [hpair]
    exact Set.mem_insert a _
  have hb : b ∉ s ∧ insert b s ∈ K.faces := by
    change b ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
    rw [hpair]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
  obtain ⟨u, huT, hu, hau, hru⟩ := exists_direction_into_simplex_of_transverse_submodule hx
    (notMem_affineSpan_of_affineIndependent_insert ha.1 (K.indep ha.2)) T hcompl.sup_eq_top
  obtain ⟨v, hvT, hv, hbv, hrv⟩ := exists_direction_into_simplex_of_transverse_submodule hx
    (notMem_affineSpan_of_affineIndependent_insert hb.1 (K.indep hb.2)) T hcompl.sup_eq_top
  have hfaces : insert a s ≠ insert b s := by
    intro heq
    have hamem : a ∈ insert b s := heq ▸ Finset.mem_insert_self a s
    rcases Finset.mem_insert.mp hamem with heq | has
    · exact hab heq
    · exact ha.1 has
  have hnot := not_pos_smul_of_eventually_mem_distinct_openSimplex K ha.2 hb.2 hfaces hru hrv
  obtain ⟨F, hF, hfix, hFT, hFcone, -⟩ :=
    exists_isPLHomeomorphOn_straighten_two_halfSpaces_sub_mem
    hcompl.disjoint huT hvT hu hv hnot
  let C : E → Set E := fun d =>
    {q | ∃ z ∈ vectorSpan ℝ (s : Set E), ∃ r : ℝ, 0 ≤ r ∧ q = z + r • d}
  have hCa : C (a - x) = C u := halfSpace_eq_of_sub_mem _ hau
  have hCb : C (b - x) = C v := halfSpace_eq_of_sub_mem _ hbv
  have hlocal : ∀ᶠ y in 𝓝 x, y ∈ K.space ↔ y - x ∈ C u ∪ C v := by
    filter_upwards [eventually_mem_space_iff_mem_codimension_one_cone K hs hbound ⟨a, ha⟩ hx]
      with y hy
    constructor
    · intro hyK
      obtain ⟨w, hws, hwface, hcone⟩ := hy.mp hyK
      have hwm : w ∈ {z | z ∉ s ∧ insert z s ∈ K.faces} := ⟨hws, hwface⟩
      rw [hpair] at hwm
      rcases hwm with rfl | hwb
      · exact Or.inl (hCa ▸ hcone)
      · have hwb' : w = b := hwb
        subst w
        exact Or.inr (hCb ▸ hcone)
    · intro hyC
      apply hy.mpr
      rcases hyC with hyu | hyv
      · refine ⟨a, ha.1, ha.2, ?_⟩
        change y - x ∈ C (a - x)
        rwa [hCa]
      · refine ⟨b, hb.1, hb.2, ?_⟩
        change y - x ∈ C (b - x)
        rwa [hCb]
  have hFinj : Function.Injective F := fun p q hpq => hF.bijOn.injOn (mem_univ p) (mem_univ q) hpq
  have hmem : ∀ (P : Set E) (y : E), F y ∈ F '' P ↔ y ∈ P := by
    intro P y
    constructor
    · rintro ⟨z, hz, heq⟩
      exact hFinj heq ▸ hz
    · exact fun hy => ⟨y, hy, rfl⟩
  let h : E → E := fun y => F (y - x)
  have hh : IsPLHomeomorphOn h univ univ := by
    have hcomp := (isPLHomeomorphOn_add_const (-x)).trans hF
    apply hcomp.congr
    intro y _
    change F (y - x) = F (y + -x)
    rw [sub_eq_add_neg]
  refine ⟨u, h, huT, hu, hh, ?_, ?_, fun y hy => hfix hy⟩
  · intro y
    change y - x ∈ T ↔ F (y - x) ∈ T
    have hm := hmem (T : Set E) (y - x)
    rw [hFT] at hm
    exact hm.symm
  · filter_upwards [hlocal] with y hy
    change (y ∈ K.space) ↔ F (y - x) ∈ vectorSpan ℝ (s : Set E) ⊔ Submodule.span ℝ {u}
    have hFcone' : F '' (C u ∪ C v) =
        (vectorSpan ℝ (s : Set E) ⊔ Submodule.span ℝ {u} : Submodule ℝ E) := hFcone
    have hm := hmem (C u ∪ C v) (y - x)
    rw [hFcone'] at hm
    exact hy.trans hm.symm

theorem finrank_vectorSpan_add_one_of_mem_faces (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) :
    Module.finrank ℝ (vectorSpan ℝ (s : Set E)) + 1 = s.card := by
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  have : Nonempty s := ⟨⟨v, hv⟩⟩
  have hrange : Set.range ((↑) : s → E) = (s : Set E) := by ext y; simp
  have h := (K.indep hs).finrank_vectorSpan_add_one
  change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → E))) + 1 = Fintype.card s at h
  rw [hrange] at h
  simpa only [Fintype.card_coe] using h

open Classical in
theorem hasPLCurveCrossingOnAt_of_transverse_faces [FiniteDimensional ℝ E]
    (K L C : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : ∀ s ∈ K.faces, s.card ≤ 3) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdimE : Module.finrank ℝ E = 3) (hCL : C.faces ⊆ L.faces) (hC : ∀ t ∈ C.faces, t.card ≤ 2)
    (hCB : ∀ t ∈ C.faces, t.card = 2 → t ∉ (boundaryComplex 2 L).faces)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤)
    {x : E} (hx : x ∈ K.space ∩ C.space) :
    HasPLCurveCrossingOnAt L.space (K.space ∩ L.space) C.space x := by
  have : Finite C.faces := ((Set.toFinite L.faces).subset hCL).to_subtype
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hx.1
  obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex C hx.2
  have htL := hCL ht
  have hst := htrans s hs t htL ⟨x, openSimplex_subset_convexHull _ hxs,
    openSimplex_subset_convexHull _ hxt⟩
  have hsRank := finrank_vectorSpan_add_one_of_mem_faces K hs
  have htRank := finrank_vectorSpan_add_one_of_mem_faces C ht
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E))
  rw [hst, finrank_top, hdimE] at hdim
  have hsb := hK s hs
  have htb := hC t ht
  have hinf : Module.finrank ℝ
      (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) : Submodule ℝ E) = 0 := by omega
  have htc : t.card = 2 := by omega
  have hSdim : Module.finrank ℝ (vectorSpan ℝ (t : Set E)) = 1 := by omega
  have hcompl : IsCompl (vectorSpan ℝ (t : Set E)) (vectorSpan ℝ (s : Set E)) := by
    refine IsCompl.of_eq ?_ ?_
    · rw [inf_comm]
      exact Submodule.finrank_eq_zero.mp hinf
    · rw [sup_comm]
      exact hst
  have hbound : ∀ r ∈ L.faces, t ⊆ r → r.card ≤ t.card + 1 := by
    intro r hr _
    have := hL.card_le L hr
    omega
  obtain ⟨a, b, hab, hpair⟩ :=
    hL.codimension_one_cofaces_of_notMem_boundary L htL htc (hCB t ht htc)
  obtain ⟨u, h, huT, hu, hh, hT, hLloc, hfixS⟩ :=
    exists_isPLHomeomorphOn_linearize_coface_pair_fixing L htL hbound hxt hab hpair
      (vectorSpan ℝ (s : Set E)) hcompl
  have hsmax : ∀ r ∈ K.faces, s ⊆ r → r.card ≤ s.card := by
    intro r hr _
    have := hK r hr
    omega
  have htmax : ∀ r ∈ C.faces, t ⊆ r → r.card ≤ t.card := by
    intro r hr _
    have := hC r hr
    omega
  have hKloc := eventually_mem_space_iff_sub_mem_vectorSpan K hs hsmax hxs
  have hCloc := eventually_mem_space_iff_sub_mem_vectorSpan C ht htmax hxt
  set S := vectorSpan ℝ (t : Set E) with hSdef
  set T := vectorSpan ℝ (s : Set E) with hTdef
  have huS : u ∉ S := fun h' => hu (Submodule.disjoint_def.mp hcompl.disjoint _ h' huT)
  have hPdim : Module.finrank ℝ (Submodule.span ℝ ({u} : Set E)) = 1 :=
    finrank_span_singleton hu
  have hSP : S ⊓ Submodule.span ℝ {u} = ⊥ :=
    disjoint_iff.mp (Submodule.disjoint_span_singleton_of_notMem huS)
  have hdimSP := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span ℝ {u})
  rw [hSP, finrank_bot] at hdimSP
  have hinjh : Function.Injective h := fun p q hpq =>
    hh.bijOn.injOn (mem_univ p) (mem_univ q) hpq
  have hSiff : ∀ y, y - x ∈ S ↔ h y ∈ S := by
    intro y
    constructor
    · intro hy
      rw [hfixS y hy]
      exact hy
    · intro hy
      have hx' : x + h y - x ∈ S := by rwa [add_sub_cancel_left]
      have heq : h (x + h y) = h y := by rw [hfixS _ hx', add_sub_cancel_left]
      rw [← hinjh heq, add_sub_cancel_left]
      exact hy
  have hTP : ∀ z ∈ T, z ∈ S ⊔ Submodule.span ℝ {u} → z ∈ Submodule.span ℝ {u} := by
    intro z hzT hz
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hq
    have hpT : p ∈ T := by
      simpa only [add_sub_cancel_right] using T.sub_mem hzT (T.smul_mem r huT)
    rw [Submodule.disjoint_def.mp hcompl.disjoint p hp hpT, zero_add]
    exact hq
  refine ⟨univ, univ, h, S ⊔ Submodule.span ℝ {u}, Submodule.span ℝ {u}, S, isOpen_univ,
    isOpen_univ, mem_univ x, hh, ?_, by omega, hPdim, hSdim, le_sup_right, le_sup_left, ?_, ?_⟩
  · rw [hfixS x (by rw [sub_self]; exact S.zero_mem), sub_self]
  · rw [inf_comm]
    exact hSP
  · filter_upwards [hLloc, hKloc, hCloc] with y hyL hyK hyC
    refine ⟨hyL, ⟨?_, ?_⟩, hyC.trans (hSiff y)⟩
    · rintro ⟨hyK', hyL'⟩
      exact hTP _ ((hT y).mp (hyK.mp hyK')) (hyL.mp hyL')
    · intro hyP
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hyP
      refine ⟨hyK.mpr ((hT y).mpr ?_), hyL.mpr (Submodule.mem_sup_right hyP)⟩
      rw [← hr]
      exact T.smul_mem r huT

open Classical in
theorem exists_small_homeomorph_transverse_relative [FiniteDimensional ℝ E]
    (K B L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hBK : B.faces ⊆ K.faces) (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hdimE : 2 ≤ Module.finrank ℝ E)
    (hB : ∀ s ∈ B.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (h : E → E) (M : Geometry.SimplicialComplex ℝ E),
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
        EqOn h id B.space ∧ M.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 M ∧
          M.space = h '' K.space ∧ ∀ s ∈ M.faces, ∀ t ∈ L.faces,
            (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
              vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ := by
  have : Finite B.faces := ((Set.toFinite K.faces).subset hBK).to_subtype
  let hc := centroid_mem_openSimplex_of_mem_faces K
  let R := relDerived hBK (IsSubdivision.refl B) hc
  have hR : IsSubdivision R K := relDerived_isSubdivision hBK (IsSubdivision.refl B) hc
  have : Finite R.faces := (relDerived_faces_finite hBK (IsSubdivision.refl B) hc).to_subtype
  have hBR : B.faces ⊆ R.faces := faces_subset_relDerived hBK (IsSubdivision.refl B) hc
  have hRman : IsCombinatorialManifoldWithBoundary 2 R := hK.of_isSubdivision hR
  have hRU : R.space ⊆ U := by rwa [hR.space_eq]
  obtain ⟨δ, hδ, hext⟩ :=
    exists_isPLHomeomorphOn_extension_of_small_vertex_perturbation R hU hRU hε
  have hcard : ∀ s ∈ R.faces, s.card ≤ Module.finrank ℝ E + 1 := by
    intro s hs
    have h := hRman.card_le R hs
    omega
  have hfixed : ∀ s ∈ R.faces, (s : Set E) ⊆ B.vertices →
      AffineIndependent ℝ (fun v : s => id (v : E)) ∧
        ∀ t ∈ L.faces, (convexHull ℝ (s.image id : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
          vectorSpan ℝ (s.image id : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ := by
    intro s hs hsub
    have hsB := mem_faces_of_mem_relDerived_of_forall_singleton_mem hBK (IsSubdivision.refl B)
      hc hs (fun v hv => hsub hv)
    refine ⟨R.indep hs, ?_⟩
    simpa only [Finset.image_id] using hB s hsB
  obtain ⟨φ, hφfix, hφclose, hgood⟩ :=
    exists_small_vertexMap_transverse_relative R L hcard id B.vertices hfixed hδ
  obtain ⟨h, hh, hclose, hzero, hagree⟩ := hext φ (fun v _ => hφclose v)
  have hinj : InjOn (simplicialMap R φ) R.space := by
    intro x hx y hy hxy
    apply hh.bijOn.injOn (mem_univ x) (mem_univ y)
    rw [hagree hx, hagree hy]
    exact hxy
  have hind : ∀ s ∈ R.faces, AffineIndependent ℝ ((↑) : ↥(s.image φ : Set E) → E) := by
    intro s hs
    exact ((affineIndependent_image_iff s φ).mp (hgood s hs).1).2
  let M := simplicialImage R φ hind hinj
  have : Finite M.faces := (simplicialImage_faces_finite R φ hind hinj).to_subtype
  have hMman : IsCombinatorialManifoldWithBoundary 2 M :=
    hRman.of_isPLHomeomorphOn (isPLHomeomorphOn_simplicialImage R φ hind hinj)
  have hMspace : M.space = h '' K.space := by
    rw [simplicialImage_space]
    have himage : simplicialMap R φ '' R.space = h '' R.space := image_congr hagree.symm
    rw [himage, hR.space_eq]
  refine ⟨h, M, hh, hclose, hzero, ?_, Set.toFinite _, hMman, hMspace, ?_⟩
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := B.mem_space_iff.mp hx
    have hxR : x ∈ R.space := R.convexHull_subset_space (hBR hs) hxs
    change h x = x
    rw [hagree hxR, simplicialMap_eq_of_mem R φ (hBR hs) hxs]
    calc ∑ v ∈ s, weights s x v • φ v = ∑ v ∈ s, weights s x v • v := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hφfix (B.down_closed hs (Finset.singleton_subset_iff.mpr hv)
            (Finset.singleton_nonempty v))]
          rfl
      _ = x := sum_weights_smul hxs
  · rintro _ ⟨s, hs, rfl⟩ t ht hinter
    exact (hgood s hs).2 t ht hinter

open Classical in
theorem exists_small_homeomorph_curveCrossing_relative [FiniteDimensional ℝ E]
    (K B L C : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hBK : B.faces ⊆ K.faces) (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L) (hdimE : Module.finrank ℝ E = 3)
    (hCL : C.faces ⊆ L.faces) (hC : ∀ t ∈ C.faces, t.card ≤ 2)
    (hCB : ∀ t ∈ C.faces, t.card = 2 → t ∉ (boundaryComplex 2 L).faces)
    (hB : ∀ s ∈ B.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : E → E, IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id B.space ∧
        (∀ x ∈ h '' K.space ∩ L.space, HasPLCrossingAt (h '' K.space) L.space x) ∧
        ∀ x ∈ h '' K.space ∩ C.space,
          HasPLCurveCrossingOnAt L.space (h '' K.space ∩ L.space) C.space x := by
  obtain ⟨h, M, hh, hclose, hzero, hfix, hMfin, hMman, hMspace, htrans⟩ :=
    exists_small_homeomorph_transverse_relative K B L hBK hK (by omega) hB hU hKU hε
  have : Finite M.faces := hMfin.to_subtype
  refine ⟨h, hh, hclose, hzero, hfix, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← hMspace] at hx ⊢
    exact hasPLCrossingAt_of_transverse_faces M L hMman hL hdimE htrans hx
  · rw [← hMspace] at hx ⊢
    refine hasPLCurveCrossingOnAt_of_transverse_faces M L C (fun s hs => ?_) hL hdimE hCL hC hCB
      htrans hx
    have := hMman.card_le M hs
    omega

end DifferentialGeometry.Topology.PiecewiseLinear
