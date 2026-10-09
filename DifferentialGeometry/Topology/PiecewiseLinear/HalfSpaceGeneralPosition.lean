/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HalfSpacePerturbation
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_small_vertexMaps_transverse_in_halfSpace [FiniteDimensional ℝ E]
    (V W : Finset E) (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hV : ∀ v ∈ V, 0 ≤ ℓ v) (hW : ∀ w ∈ W, 0 ≤ ℓ w) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ ψ : E → E, (∀ v, dist (φ v) v < ε) ∧ (∀ w, dist (ψ w) w < ε) ∧
      (∀ v ∈ V, (ℓ (φ v) = 0 ↔ ℓ v = 0) ∧ 0 ≤ ℓ (φ v)) ∧
        (∀ w ∈ W, (ℓ (ψ w) = 0 ↔ ℓ w = 0) ∧ 0 ≤ ℓ (ψ w)) ∧
          (∀ s : Finset E, s ⊆ V → s.card ≤ 3 → AffineIndependent ℝ (fun v : s => φ (v : E))) ∧
            (∀ t : Finset E, t ⊆ W → t.card ≤ 3 → AffineIndependent ℝ (fun v : t => ψ (v : E))) ∧
              ∀ s : Finset E, s ⊆ V → ∀ t : Finset E, t ⊆ W →
                (convexHull ℝ (s.image φ : Set E) ∩ convexHull ℝ (t.image ψ : Set E)).Nonempty →
                  vectorSpan ℝ (s.image φ : Set E) ⊔ vectorSpan ℝ (t.image ψ : Set E) =
                    if (∀ v ∈ s, ℓ (φ v) = 0) ∧ (∀ w ∈ t, ℓ (ψ w) = 0) then LinearMap.ker ℓ
                      else ⊤ := by
  let : DecidableEq (E ⊕ E) := Classical.typeDecidableEq _
  let A : Finset (E ⊕ E) := V.image Sum.inl ∪ W.image Sum.inr
  let f : E ⊕ E → E := Sum.elim id id
  let B : Finset (E ⊕ E) := A.filter fun v => ℓ (f v) = 0
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have hVA : ∀ v ∈ V, Sum.inl v ∈ A := fun v hv => Finset.mem_union.mpr (Or.inl
    (Finset.mem_image_of_mem _ hv))
  have hWA : ∀ v ∈ W, Sum.inr v ∈ A := fun v hv => Finset.mem_union.mpr (Or.inr
    (Finset.mem_image_of_mem _ hv))
  have hA : ∀ v ∈ A, 0 ≤ ℓ (f v) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact hV w hw
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact hW w hw
  have hB : ∀ v ∈ B, ℓ (f v) = 0 := fun _ hv => (Finset.mem_filter.mp hv).2
  have hpos : ∀ v ∈ A \ B, 0 < ℓ (f v) := by
    intro v hv
    have hvA := (Finset.mem_sdiff.mp hv).1
    have hv0 : ℓ (f v) ≠ 0 := fun h => (Finset.mem_sdiff.mp hv).2 (Finset.mem_filter.mpr ⟨hvA, h⟩)
    exact lt_of_le_of_ne (hA v hvA) (Ne.symm hv0)
  obtain ⟨θ, _, hclose, hzero, hpositive, hind, htrans⟩ :=
    exists_small_vertexMap_transverse_in_halfSpace A B hBA ℓ hℓ f hB hpos hε
  have hθ : ∀ v ∈ A, (ℓ (θ v) = 0 ↔ ℓ (f v) = 0) ∧ 0 ≤ ℓ (θ v) := by
    intro v hv
    by_cases hv0 : ℓ (f v) = 0
    · have h := hzero v (Finset.mem_filter.mpr ⟨hv, hv0⟩)
      exact ⟨iff_of_true h hv0, h.symm ▸ le_refl 0⟩
    · have hvB : v ∉ B := fun h => hv0 (hB v h)
      have h := hpositive v (Finset.mem_sdiff.mpr ⟨hv, hvB⟩)
      exact ⟨iff_of_false (ne_of_gt h) hv0, h.le⟩
  have hker : Module.finrank ℝ (LinearMap.ker ℓ) = 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [LinearMap.range_eq_top.mpr (LinearMap.surjective_of_ne_zero hℓ), finrank_top,
      Module.finrank_self, hdim] at h
    omega
  have hinl : ∀ s : Finset E, s ⊆ V → s.image Sum.inl ⊆ A := by
    intro s hs z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hVA x (hs hx)
  have hinr : ∀ t : Finset E, t ⊆ W → t.image Sum.inr ⊆ A := by
    intro t ht z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hWA x (ht hx)
  let φ : E → E := fun v => θ (Sum.inl v)
  let ψ : E → E := fun v => θ (Sum.inr v)
  have hφimage : ∀ s : Finset E, (s.image Sum.inl).image θ = s.image φ := by
    intro s
    simp only [Finset.image_image, φ, Function.comp_def]
  have hψimage : ∀ t : Finset E, (t.image Sum.inr).image θ = t.image ψ := by
    intro t
    simp only [Finset.image_image, ψ, Function.comp_def]
  refine ⟨φ, ψ, fun v => hclose (Sum.inl v), fun w => hclose (Sum.inr w),
    fun v hv => hθ (Sum.inl v) (hVA v hv), fun w hw => hθ (Sum.inr w) (hWA w hw), ?_, ?_, ?_⟩
  · intro s hs hcard
    have hi := hind (s.image Sum.inl) (hinl s hs)
      (by rw [hdim]; exact (Finset.card_image_le.trans hcard).trans (by norm_num))
      (by
        rw [hker]
        exact (Finset.card_le_card Finset.inter_subset_left).trans
          (Finset.card_image_le.trans hcard))
    have hφinj : InjOn φ (s : Set E) := by
      intro a ha b hb hab
      have heq := hi.injective (a₁ := ⟨Sum.inl a, Finset.mem_image_of_mem _ ha⟩)
        (a₂ := ⟨Sum.inl b, Finset.mem_image_of_mem _ hb⟩) hab
      exact Sum.inl_injective (congrArg Subtype.val heq)
    apply (affineIndependent_image_iff s φ).mpr
    refine ⟨hφinj, ?_⟩
    have h := ((affineIndependent_image_iff (s.image Sum.inl) θ).mp hi).2
    rwa [hφimage] at h
  · intro t ht hcard
    have hi := hind (t.image Sum.inr) (hinr t ht)
      (by rw [hdim]; exact (Finset.card_image_le.trans hcard).trans (by norm_num))
      (by
        rw [hker]
        exact (Finset.card_le_card Finset.inter_subset_left).trans
          (Finset.card_image_le.trans hcard))
    have hψinj : InjOn ψ (t : Set E) := by
      intro a ha b hb hab
      have heq := hi.injective (a₁ := ⟨Sum.inr a, Finset.mem_image_of_mem _ ha⟩)
        (a₂ := ⟨Sum.inr b, Finset.mem_image_of_mem _ hb⟩) hab
      exact Sum.inr_injective (congrArg Subtype.val heq)
    apply (affineIndependent_image_iff t ψ).mpr
    refine ⟨hψinj, ?_⟩
    have h := ((affineIndependent_image_iff (t.image Sum.inr) θ).mp hi).2
    rwa [hψimage] at h
  · intro s hs t ht hinter
    have hdisj : Disjoint (s.image Sum.inl) (t.image Sum.inr) := by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨b, _, hba⟩ := Finset.mem_image.mp hz'
      cases hba
    have hi : (convexHull ℝ (((s.image Sum.inl).image θ) : Set E) ∩
        convexHull ℝ (((t.image Sum.inr).image θ) : Set E)).Nonempty := by
      rwa [hφimage, hψimage]
    have h := htrans (s.image Sum.inl) (hinl s hs) (t.image Sum.inr) (hinr t ht) hdisj hi
    rw [hφimage, hψimage] at h
    have hiff : s.image Sum.inl ∪ t.image Sum.inr ⊆ B ↔
        (∀ v ∈ s, ℓ (φ v) = 0) ∧ (∀ w ∈ t, ℓ (ψ w) = 0) := by
      constructor
      · intro hsub
        exact ⟨fun v hv => hzero (Sum.inl v) (hsub (Finset.mem_union.mpr (Or.inl
          (Finset.mem_image_of_mem _ hv)))),
          fun w hw => hzero (Sum.inr w) (hsub (Finset.mem_union.mpr (Or.inr
            (Finset.mem_image_of_mem _ hw))))⟩
      · rintro ⟨hφ0, hψ0⟩ z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
          exact Finset.mem_filter.mpr ⟨hVA v (hs hv), (hθ (Sum.inl v) (hVA v (hs hv))).1.mp
            (hφ0 v hv)⟩
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
          exact Finset.mem_filter.mpr ⟨hWA w (ht hw), (hθ (Sum.inr w) (hWA w (ht hw))).1.mp
            (hψ0 w hw)⟩
    change vectorSpan ℝ (s.image φ : Set E) ⊔ vectorSpan ℝ (t.image ψ : Set E) =
      (if s.image Sum.inl ∪ t.image Sum.inr ⊆ B then LinearMap.ker ℓ else ⊤) at h
    simpa only [hiff] using h

open Classical in
theorem exists_small_homeomorphs_transverse_in_halfSpace_with_lipschitz_displacement
    [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hKcard : ∀ s ∈ K.faces, s.card ≤ 3) (hLcard : ∀ t ∈ L.faces, t.card ≤ 3)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLℓ : ∀ w ∈ L.vertices, 0 ≤ ℓ w)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) (hLU : L.space ⊆ U) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ (φ ψ h g : E → E) (ka kb : NNReal),
      LipschitzWith ka (fun x => h x - x) ∧ LipschitzWith kb (fun x => g x - x) ∧
      (ka : ℝ) < η ∧ (kb : ℝ) < η ∧ ka < 1 ∧ kb < 1 ∧
      IsPLHomeomorphOn h univ univ ∧ IsPLHomeomorphOn g univ univ ∧
      (∀ x, dist (h x) x < ε) ∧ (∀ x, dist (g x) x < ε) ∧ EqOn h id Uᶜ ∧ EqOn g id Uᶜ ∧
        EqOn h (simplicialMap K φ) K.space ∧ EqOn g (simplicialMap L ψ) L.space ∧
          (∀ x, (ℓ (h x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (h x) ↔ 0 ≤ ℓ x)) ∧
            (∀ x, (ℓ (g x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (g x) ↔ 0 ≤ ℓ x)) ∧
              (∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E))) ∧
                (∀ t ∈ L.faces, AffineIndependent ℝ (fun v : t => ψ (v : E))) ∧
                  ∀ s ∈ K.faces, ∀ t ∈ L.faces,
                    (convexHull ℝ (s.image φ : Set E) ∩ convexHull ℝ (t.image ψ : Set E)).Nonempty →
                      vectorSpan ℝ (s.image φ : Set E) ⊔ vectorSpan ℝ (t.image ψ : Set E) =
                        if (∀ v ∈ s, ℓ (φ v) = 0) ∧ (∀ w ∈ t, ℓ (ψ w) = 0) then LinearMap.ker
                          ℓ else ⊤ := by
  obtain ⟨ηK, hηK, hExtK⟩ :=
    exists_lipschitz_displacement_extending_vertex_perturbation_preserving_halfSpace
    K ℓ hℓ hKℓ hU hKU hε hη
  obtain ⟨ηL, hηL, hExtL⟩ :=
    exists_lipschitz_displacement_extending_vertex_perturbation_preserving_halfSpace
    L ℓ hℓ hLℓ hU hLU hε hη
  have hKV : K.vertices.Finite := Set.Finite.preimage Finset.singleton_injective.injOn
    (Set.toFinite K.faces)
  have hLV : L.vertices.Finite := Set.Finite.preimage Finset.singleton_injective.injOn
    (Set.toFinite L.faces)
  let V := hKV.toFinset
  let W := hLV.toFinset
  have hV : ∀ v, v ∈ V ↔ v ∈ K.vertices := fun _ => hKV.mem_toFinset
  have hW : ∀ v, v ∈ W ↔ v ∈ L.vertices := fun _ => hLV.mem_toFinset
  obtain ⟨φ, ψ, hφclose, hψclose, hφheight, hψheight, hφind, hψind, htrans⟩ :=
    exists_small_vertexMaps_transverse_in_halfSpace V W hdim ℓ hℓ
      (fun v hv => hKℓ v ((hV v).mp hv)) (fun v hv => hLℓ v ((hW v).mp hv)) (lt_min hηK hηL)
  obtain ⟨a, ka, _, halip, hka, hka1, hanorm, hazero, _, hhmap, hh, hhheight⟩ := hExtK φ
    (fun v _ => (hφclose v).trans_le (min_le_left ηK ηL))
    (fun v hv hv0 => (hφheight v ((hV v).mpr hv)).1.mpr hv0)
  obtain ⟨b, kb, _, hblip, hkb, hkb1, hbnorm, hbzero, _, hgmap, hg, hgheight⟩ := hExtL ψ
    (fun v _ => (hψclose v).trans_le (min_le_right ηK ηL))
    (fun v hv hv0 => (hψheight v ((hW v).mpr hv)).1.mpr hv0)
  let h : E → E := fun x => x + a x
  let g : E → E := fun x => x + b x
  have hhclose (x : E) : dist (h x) x < ε := by
    simpa only [h, dist_eq_norm, add_sub_cancel_left] using hanorm x
  have hgclose (x : E) : dist (g x) x < ε := by
    simpa only [g, dist_eq_norm, add_sub_cancel_left] using hbnorm x
  have hhfix : EqOn h id Uᶜ := fun x hx => by
    change x + a x = x
    rw [hazero hx, add_zero]
  have hgfix : EqOn g id Uᶜ := fun x hx => by
    change x + b x = x
    rw [hbzero hx, add_zero]
  have hhlip : LipschitzWith ka (fun x => h x - x) := by
    simpa only [h, add_sub_cancel_left] using halip
  have hglip : LipschitzWith kb (fun x => g x - x) := by
    simpa only [g, add_sub_cancel_left] using hblip
  have hfaceK : ∀ s ∈ K.faces, s ⊆ V := fun s hs v hv => (hV v).mpr
    (K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  have hfaceL : ∀ t ∈ L.faces, t ⊆ W := fun t ht v hv => (hW v).mpr
    (L.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  exact ⟨φ, ψ, h, g, ka, kb, hhlip, hglip, hka, hkb, hka1, hkb1, hh, hg,
    hhclose, hgclose, hhfix, hgfix, hhmap, hgmap, hhheight, hgheight,
    fun s hs => hφind s (hfaceK s hs) (hKcard s hs), fun t ht => hψind t (hfaceL t ht) (hLcard
      t ht),
    fun s hs t ht => htrans s (hfaceK s hs) t (hfaceL t ht)⟩

open Classical in
theorem exists_small_homeomorphs_transverse_in_halfSpace [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hKcard : ∀ s ∈ K.faces, s.card ≤ 3) (hLcard : ∀ t ∈ L.faces, t.card ≤ 3)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLℓ : ∀ w ∈ L.vertices, 0 ≤ ℓ w)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) (hLU : L.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ ψ h g : E → E, IsPLHomeomorphOn h univ univ ∧ IsPLHomeomorphOn g univ univ ∧
      (∀ x, dist (h x) x < ε) ∧ (∀ x, dist (g x) x < ε) ∧ EqOn h id Uᶜ ∧ EqOn g id Uᶜ ∧
        EqOn h (simplicialMap K φ) K.space ∧ EqOn g (simplicialMap L ψ) L.space ∧
          (∀ x, (ℓ (h x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (h x) ↔ 0 ≤ ℓ x)) ∧
            (∀ x, (ℓ (g x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (g x) ↔ 0 ≤ ℓ x)) ∧
              (∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E))) ∧
                (∀ t ∈ L.faces, AffineIndependent ℝ (fun v : t => ψ (v : E))) ∧
                  ∀ s ∈ K.faces, ∀ t ∈ L.faces,
                    (convexHull ℝ (s.image φ : Set E) ∩ convexHull ℝ (t.image ψ : Set E)).Nonempty →
                      vectorSpan ℝ (s.image φ : Set E) ⊔ vectorSpan ℝ (t.image ψ : Set E) =
                        if (∀ v ∈ s, ℓ (φ v) = 0) ∧ (∀ w ∈ t, ℓ (ψ w) = 0) then LinearMap.ker
                          ℓ else ⊤ := by
  obtain ⟨φ, ψ, h, g, ka, kb, _, _, _, _, _, _, hh, hg, hhclose, hgclose, hhfix,
    hgfix, hhmap, hgmap, hhheight, hgheight, hφind, hψind, htrans⟩ :=
    exists_small_homeomorphs_transverse_in_halfSpace_with_lipschitz_displacement K L
      hKcard hLcard hdim ℓ hℓ hKℓ hLℓ hU hKU hLU hε zero_lt_one
  exact ⟨φ, ψ, h, g, hh, hg, hhclose, hgclose, hhfix, hgfix, hhmap, hgmap,
    hhheight, hgheight, hφind, hψind, htrans⟩

open Classical in
theorem exists_small_homeomorphs_generalPosition_in_halfSpace_with_lipschitz_displacement
    [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLℓ : ∀ w ∈ L.vertices, 0 ≤ ℓ w)
    (hKboundary : ∀ x ∈ K.space, ℓ x = 0 → x ∈ (boundaryComplex 2 K).space)
    (hLboundary : ∀ x ∈ L.space, ℓ x = 0 → x ∈ (boundaryComplex 2 L).space)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) (hLU : L.space ⊆ U) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ (h g : E → E) (G : Geometry.SimplicialComplex ℝ E) (ka kb : NNReal),
      LipschitzWith ka (fun x => h x - x) ∧ LipschitzWith kb (fun x => g x - x) ∧
      (ka : ℝ) < η ∧ (kb : ℝ) < η ∧ ka < 1 ∧ kb < 1 ∧
      IsPLHomeomorphOn h univ univ ∧ IsPLHomeomorphOn g univ univ ∧
        (∀ x, dist (h x) x < ε) ∧ (∀ x, dist (g x) x < ε) ∧ EqOn h id Uᶜ ∧ EqOn g id Uᶜ ∧
          (∀ x, (ℓ (h x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (h x) ↔ 0 ≤ ℓ x)) ∧
            (∀ x, (ℓ (g x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (g x) ↔ 0 ≤ ℓ x)) ∧
              G.faces.Finite ∧ G.space = h '' K.space ∩ g '' L.space ∧
                IsCombinatorialManifoldWithBoundary 1 G ∧
                  ∀ y ∈ G.space,
                    (ℓ y = 0 ∧ HasPLBoundaryCrossingAt {x : E | 0 ≤ ℓ x} (h '' K.space) (g ''
                      L.space) y) ∨
                    (0 < ℓ y ∧ HasPLCrossingAt (h '' K.space) (g '' L.space) y) := by
  obtain ⟨φ, ψ, h, g, ka, kb, hhlip, hglip, hka, hkb, hka1, hkb1, hh, hg,
    hhclose, hgclose, hhfix, hgfix, hhmap, hgmap, hhheight, hgheight,
      hφind, hψind, htrans⟩ :=
    exists_small_homeomorphs_transverse_in_halfSpace_with_lipschitz_displacement K L
    (fun s hs => hK.card_le K hs) (fun t ht => hL.card_le L ht) hdim ℓ hℓ hKℓ hLℓ hU hKU hLU hε hη
  have hφinj : InjOn (simplicialMap K φ) K.space := by
    intro x hx y hy hxy
    exact hh.bijOn.injOn (mem_univ _) (mem_univ _) ((hhmap hx).trans (hxy.trans (hhmap hy).symm))
  have hψinj : InjOn (simplicialMap L ψ) L.space := by
    intro x hx y hy hxy
    exact hg.bijOn.injOn (mem_univ _) (mem_univ _) ((hgmap hx).trans (hxy.trans (hgmap hy).symm))
  obtain ⟨K', hKfinite, hKspace, hKPL, hKfaces⟩ := exists_simplicialImage_of_faces_subset K K
    Subset.rfl φ hφind hφinj
  obtain ⟨L', hLfinite, hLspace, hLPL, hLfaces⟩ := exists_simplicialImage_of_faces_subset L L
    Subset.rfl ψ hψind hψinj
  have : Finite K'.faces := hKfinite.to_subtype
  have : Finite L'.faces := hLfinite.to_subtype
  have hKman : IsCombinatorialManifoldWithBoundary 2 K' := hK.of_isPLHomeomorphOn hKPL
  have hLman : IsCombinatorialManifoldWithBoundary 2 L' := hL.of_isPLHomeomorphOn hLPL
  have hKspace' : K'.space = h '' K.space := hKspace.trans hhmap.image_eq.symm
  have hLspace' : L'.space = g '' L.space := hLspace.trans hgmap.image_eq.symm
  have hKzero : ∀ x ∈ K'.space, ℓ x = 0 → x ∈ (boundaryComplex 2 K').space := by
    intro x hx hx0
    obtain ⟨y, hy, rfl⟩ := hKspace ▸ hx
    have hy0 : ℓ y = 0 := (hhheight y).1.mp ((congrArg ℓ (hhmap hy)).trans hx0)
    rw [boundaryComplex_space_of_isPLHomeomorphOn K K' hK hKPL]
    exact ⟨y, hKboundary y hy hy0, rfl⟩
  have hLzero : ∀ x ∈ L'.space, ℓ x = 0 → x ∈ (boundaryComplex 2 L').space := by
    intro x hx hx0
    obtain ⟨y, hy, rfl⟩ := hLspace ▸ hx
    have hy0 : ℓ y = 0 := (hgheight y).1.mp ((congrArg ℓ (hgmap hy)).trans hx0)
    rw [boundaryComplex_space_of_isPLHomeomorphOn L L' hL hLPL]
    exact ⟨y, hLboundary y hy hy0, rfl⟩
  have hzeroFace : ∀ C : Geometry.SimplicialComplex ℝ E,
      (∀ x ∈ C.space, ℓ x = 0 → x ∈ (boundaryComplex 2 C).space) →
        ∀ s ∈ C.faces, 2 ≤ s.card → (∀ v ∈ s, ℓ v = 0) → s ∈ (boundaryComplex 2 C).faces := by
    intro C hC s hs _ hs0
    let x := s.centroid ℝ id
    have hx : x ∈ openSimplex s := centroid_mem_openSimplex (C.nonempty_of_mem_faces hs)
    have hxHull := openSimplex_subset_convexHull s hx
    have hkerHull : convexHull ℝ (s : Set E) ⊆ LinearMap.ker ℓ :=
      convexHull_min (fun v hv => hs0 v hv) (LinearMap.ker ℓ).convex
    have hxB := hC x (C.convexHull_subset_space hs hxHull) (hkerHull hxHull)
    by_contra hnot
    exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset 2 C) hs hnot hx hxB
  have hKnonneg : ∀ v ∈ K'.vertices, 0 ≤ ℓ v := by
    intro v hv
    obtain ⟨x, hx, hfx⟩ := hKspace' ▸ K'.subset_space hv (Finset.mem_singleton_self v)
    rw [← hfx]
    apply (hhheight x).2.mpr
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    have heq : ℓ x = ∑ w ∈ s, weights s x w * ℓ w := by
      calc ℓ x = ℓ (∑ w ∈ s, weights s x w • w) := congrArg ℓ (sum_weights_smul hxs).symm
        _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul]
    rw [heq]
    exact Finset.sum_nonneg fun w hw => mul_nonneg (weights_nonneg hxs hw)
      (hKℓ w (K.down_closed hs (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)))
  have hLnonneg : ∀ v ∈ L'.vertices, 0 ≤ ℓ v := by
    intro v hv
    obtain ⟨x, hx, hfx⟩ := hLspace' ▸ L'.subset_space hv (Finset.mem_singleton_self v)
    rw [← hfx]
    apply (hgheight x).2.mpr
    obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hx
    have heq : ℓ x = ∑ w ∈ s, weights s x w * ℓ w := by
      calc ℓ x = ℓ (∑ w ∈ s, weights s x w • w) := congrArg ℓ (sum_weights_smul hxs).symm
        _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul]
    rw [heq]
    exact Finset.sum_nonneg fun w hw => mul_nonneg (weights_nonneg hxs hw)
      (hLℓ w (L.down_closed hs (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)))
  have htrans' : ∀ s ∈ K'.faces, ∀ t ∈ L'.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) =
          if ∀ v ∈ s ∪ t, ℓ v = 0 then LinearMap.ker ℓ else ⊤ := by
    intro s hs t ht hinter
    obtain ⟨s₀, hs₀, rfl⟩ := hKfaces s hs
    obtain ⟨t₀, ht₀, rfl⟩ := hLfaces t ht
    have heq := htrans s₀ hs₀ t₀ ht₀ hinter
    have hiff : (∀ v ∈ s₀.image φ ∪ t₀.image ψ, ℓ v = 0) ↔
        (∀ v ∈ s₀, ℓ (φ v) = 0) ∧ (∀ w ∈ t₀, ℓ (ψ w) = 0) := by
      constructor
      · intro hz
        exact ⟨fun v hv => hz (φ v) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)),
          fun w hw => hz (ψ w) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw))⟩
      · rintro ⟨hszero, htzero⟩ v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
          exact hszero w hw
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
          exact htzero w hw
    simpa only [hiff] using heq
  obtain ⟨G, hGfinite, hGspace, hGman, _⟩ :=
    exists_isCombinatorialManifoldWithBoundary_inter_in_halfSpace_of_boundary_edges K' L'
      hKman hLman
      hdim ℓ hKnonneg hLnonneg (hzeroFace K' hKzero) (hzeroFace L' hLzero) htrans'
  refine ⟨h, g, G, ka, kb, hhlip, hglip, hka, hkb, hka1, hkb1, hh, hg,
    hhclose, hgclose, hhfix, hgfix, hhheight, hgheight,
    hGfinite, hGspace.trans (by rw [hKspace', hLspace']), hGman, ?_⟩
  intro y hy
  have hcross := hasPLCrossingAt_or_hasPLBoundaryCrossingAt_of_transverse_faces K' L' hKman hLman
    hdim ℓ hKnonneg hLnonneg (hzeroFace K' hKzero) (hzeroFace L' hLzero) htrans' (hGspace ▸ hy)
  rw [hKspace', hLspace'] at hcross
  rcases hcross with ⟨hy0, hycross, _⟩ | hpos
  · exact Or.inl ⟨hy0, hycross⟩
  · exact Or.inr hpos

open Classical in
theorem exists_small_homeomorphs_generalPosition_in_halfSpace [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLℓ : ∀ w ∈ L.vertices, 0 ≤ ℓ w)
    (hKboundary : ∀ x ∈ K.space, ℓ x = 0 → x ∈ (boundaryComplex 2 K).space)
    (hLboundary : ∀ x ∈ L.space, ℓ x = 0 → x ∈ (boundaryComplex 2 L).space)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) (hLU : L.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (h g : E → E) (G : Geometry.SimplicialComplex ℝ E),
      IsPLHomeomorphOn h univ univ ∧ IsPLHomeomorphOn g univ univ ∧
        (∀ x, dist (h x) x < ε) ∧ (∀ x, dist (g x) x < ε) ∧ EqOn h id Uᶜ ∧ EqOn g id Uᶜ ∧
          (∀ x, (ℓ (h x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (h x) ↔ 0 ≤ ℓ x)) ∧
            (∀ x, (ℓ (g x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (g x) ↔ 0 ≤ ℓ x)) ∧
              G.faces.Finite ∧ G.space = h '' K.space ∩ g '' L.space ∧
                IsCombinatorialManifoldWithBoundary 1 G ∧
                  ∀ y ∈ G.space,
                    (ℓ y = 0 ∧ HasPLBoundaryCrossingAt {x : E | 0 ≤ ℓ x} (h '' K.space) (g ''
                      L.space) y) ∨
                    (0 < ℓ y ∧ HasPLCrossingAt (h '' K.space) (g '' L.space) y) := by
  obtain ⟨h, g, G, ka, kb, _, _, _, _, _, _, hh, hg, hhclose, hgclose, hhfix, hgfix,
    hhheight, hgheight, hGfin, hGspace, hGman, hGcross⟩ :=
    exists_small_homeomorphs_generalPosition_in_halfSpace_with_lipschitz_displacement K L
      hK hL hdim ℓ hℓ hKℓ hLℓ hKboundary hLboundary hU hKU hLU hε zero_lt_one
  exact ⟨h, g, G, hh, hg, hhclose, hgclose, hhfix, hgfix, hhheight, hgheight,
    hGfin, hGspace, hGman, hGcross⟩

omit [NormedSpace ℝ E] in
private theorem lipschitz_displacement_of_comp_eq {h g u : E → E} {ka kb : NNReal}
    (ha : LipschitzWith ka (fun x => h x - x))
    (hb : LipschitzWith kb (fun x => g x - x)) (hkb : kb < 1)
    (hu : ∀ x, g (u x) = h x) :
    LipschitzWith ((ka + kb) / (1 - kb)) (fun x => u x - x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hdist : dist (u x) (u y) ≤ dist x y + dist (u x - x) (u y - y) := by
    calc dist (u x) (u y) = ‖(x - y) + ((u x - x) - (u y - y))‖ := by
          rw [dist_eq_norm]
          congr 1
          abel
      _ ≤ ‖x - y‖ + ‖(u x - x) - (u y - y)‖ := norm_add_le _ _
      _ = dist x y + dist (u x - x) (u y - y) := by rw [dist_eq_norm, dist_eq_norm]
  have hbound : dist (u x - x) (u y - y) ≤
      (ka : ℝ) * dist x y + (kb : ℝ) * dist (u x) (u y) := by
    calc dist (u x - x) (u y - y) =
          ‖((h x - x) - (h y - y)) - ((g (u x) - u x) - (g (u y) - u y))‖ := by
            rw [dist_eq_norm, hu, hu]
            congr 1
            abel
      _ ≤ ‖(h x - x) - (h y - y)‖ + ‖(g (u x) - u x) - (g (u y) - u y)‖ :=
        norm_sub_le _ _
      _ ≤ (ka : ℝ) * dist x y + (kb : ℝ) * dist (u x) (u y) :=
        by simpa only [dist_eq_norm] using
          add_le_add (ha.dist_le_mul x y) (hb.dist_le_mul (u x) (u y))
  have hpos : 0 < 1 - (kb : ℝ) := sub_pos.mpr hkb
  simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_sub hkb.le, NNReal.coe_one]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpos).mpr
  have hmul := mul_le_mul_of_nonneg_left hdist kb.property
  have htotal : dist (u x - x) (u y - y) ≤
      (ka : ℝ) * dist x y + (kb : ℝ) * (dist x y + dist (u x - x) (u y - y)) :=
    hbound.trans (add_le_add (le_refl ((ka : ℝ) * dist x y)) hmul)
  calc dist (u x - x) (u y - y) * (1 - (kb : ℝ)) =
        dist (u x - x) (u y - y) - (kb : ℝ) * dist (u x - x) (u y - y) := by ring
    _ ≤ (ka : ℝ) * dist x y + (kb : ℝ) * dist x y := by
      apply sub_le_iff_le_add.mpr
      simpa only [mul_add, ← add_assoc] using htotal
    _ = ((ka : ℝ) + (kb : ℝ)) * dist x y := by ring

open Classical in
theorem exists_small_homeomorph_generalPosition_in_halfSpace_with_lipschitz_displacement
    [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLℓ : ∀ w ∈ L.vertices, 0 ≤ ℓ w)
    (hKboundary : ∀ x ∈ K.space, ℓ x = 0 → x ∈ (boundaryComplex 2 K).space)
    (hLboundary : ∀ x ∈ L.space, ℓ x = 0 → x ∈ (boundaryComplex 2 L).space)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) (hLU : L.space ⊆ U) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ (h : E → E) (G : Geometry.SimplicialComplex ℝ E) (k : NNReal),
      LipschitzWith k (fun x => h x - x) ∧ (k : ℝ) < η ∧ k < 1 ∧ IsPLHomeomorphOn h univ univ ∧
      (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
        (∀ x, (ℓ (h x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (h x) ↔ 0 ≤ ℓ x)) ∧
          G.faces.Finite ∧ G.space = h '' K.space ∩ L.space ∧
            IsCombinatorialManifoldWithBoundary 1 G ∧
            ∀ y ∈ G.space,
              (ℓ y = 0 ∧ HasPLBoundaryCrossingAt {x : E | 0 ≤ ℓ x} (h '' K.space) L.space y) ∨
              (0 < ℓ y ∧ HasPLCrossingAt (h '' K.space) L.space y) := by
  obtain ⟨h, g, H, ka, kb, hhlip, hglip, hka, hkb, hka1, hkb1, hh, hg,
    hhclose, hgclose, hhfix, hgfix, hhheight, hgheight,
      hHfinite, hHspace, hHman, hHcross⟩ :=
        exists_small_homeomorphs_generalPosition_in_halfSpace_with_lipschitz_displacement K L hK hL
    hdim ℓ hℓ hKℓ hLℓ hKboundary hLboundary hU hKU hLU (half_pos hε)
      (show 0 < min (1 / 4 : ℝ) (η / 8) from
        lt_min (by norm_num) (div_pos hη (by norm_num)))
  have : Finite H.faces := hHfinite.to_subtype
  let e := hg.toOpenPartialHomeomorph isOpen_univ isOpen_univ
  let u := e.symm ∘ h
  let k : NNReal := (ka + kb) / (1 - kb)
  have hulip : LipschitzWith k (fun x => u x - x) :=
    lipschitz_displacement_of_comp_eq hhlip hglip hkb1 (fun x => e.right_inv (mem_univ (h x)))
  have hkaq : (ka : ℝ) < 1 / 4 := hka.trans_le (min_le_left _ _)
  have hkbq : (kb : ℝ) < 1 / 4 := hkb.trans_le (min_le_left _ _)
  have hkaη : (ka : ℝ) < η / 8 := hka.trans_le (min_le_right _ _)
  have hkbη : (kb : ℝ) < η / 8 := hkb.trans_le (min_le_right _ _)
  have hkEq : (k : ℝ) = ((ka : ℝ) + kb) / (1 - (kb : ℝ)) := by
    simp only [k, NNReal.coe_div, NNReal.coe_add, NNReal.coe_sub hkb1.le, NNReal.coe_one]
  have hkη : (k : ℝ) < η := by
    rw [hkEq]
    apply (div_lt_iff₀ (sub_pos.mpr (show (kb : ℝ) < 1 from hkb1))).mpr
    have hmul := mul_lt_mul_of_pos_left hkbq hη
    nlinarith
  have hk1 : k < 1 := by
    change (k : ℝ) < 1
    rw [hkEq]
    apply (div_lt_iff₀ (sub_pos.mpr (show (kb : ℝ) < 1 from hkb1))).mpr
    nlinarith
  have he : IsPiecewiseAffineOn e e.source := hg.isPiecewiseAffineOn
  have heTarget : e.target = univ := rfl
  have hinvHeight : ∀ y, (ℓ (e.symm y) = 0 ↔ ℓ y = 0) ∧ (0 ≤ ℓ (e.symm y) ↔ 0 ≤ ℓ y) := by
    intro y
    have hp := hgheight (e.symm y)
    change (ℓ (e (e.symm y)) = 0 ↔ ℓ (e.symm y) = 0) ∧ (0 ≤ ℓ (e (e.symm y)) ↔ 0 ≤ ℓ (e.symm
      y)) at hp
    rw [e.right_inv (mem_univ y)] at hp
    exact ⟨hp.1.symm, hp.2.symm⟩
  have hinvClose : ∀ y, dist (e.symm y) y < ε / 2 := by
    intro y
    have hp := hgclose (e.symm y)
    change dist (e (e.symm y)) (e.symm y) < ε / 2 at hp
    rwa [e.right_inv (mem_univ y), dist_comm] at hp
  have huPL : IsPLHomeomorphOn u univ univ := hh.trans hg.symm
  have huclose : ∀ x, dist (u x) x < ε := by
    intro x
    have hp := (dist_triangle (e.symm (h x)) (h x) x).trans_lt (add_lt_add (hinvClose (h x))
      (hhclose x))
    rw [add_halves] at hp
    exact hp
  have hufix : EqOn u id Uᶜ := by
    intro x hx
    change e.symm (h x) = x
    rw [hhfix hx]
    calc e.symm x = e.symm (g x) := congrArg e.symm (hgfix hx).symm
      _ = x := e.left_inv (mem_univ x)
  have huheight : ∀ x, (ℓ (u x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (u x) ↔ 0 ≤ ℓ x) := fun x =>
    ⟨(hinvHeight (h x)).1.trans (hhheight x).1, (hinvHeight (h x)).2.trans (hhheight x).2⟩
  have hPLH : IsPiecewiseAffineOn e.symm H.space := hg.symm.isPiecewiseAffineOn.mono_of_isPolyhedron
    (isPolyhedron_space H) (subset_univ _)
  obtain ⟨G, hGfinite, hGspace, hGPL⟩ := exists_isPLHomeomorphOn_image H hPLH
    (hg.symm.bijOn.injOn.mono (subset_univ _))
  have : Finite G.faces := hGfinite.to_subtype
  have hGman : IsCombinatorialManifoldWithBoundary 1 G := hHman.of_isPLHomeomorphOn hGPL
  have hKimage : e.symm '' (e.target ∩ h '' K.space) = u '' K.space := by
    simp only [heTarget, univ_inter, image_image, u, Function.comp_def]
  have hLimage : e.symm '' (e.target ∩ g '' L.space) = L.space := by
    rw [heTarget, univ_inter]
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, hxy⟩
      have heq : x = y := (e.left_inv (mem_univ x)).symm.trans hxy
      exact heq ▸ hx
    · intro hy
      exact ⟨g y, ⟨y, hy, rfl⟩, e.left_inv (mem_univ y)⟩
  have hMimage : e.symm '' (e.target ∩ {x : E | 0 ≤ ℓ x}) = {x : E | 0 ≤ ℓ x} := by
    ext y
    constructor
    · rintro ⟨z, ⟨_, hz⟩, rfl⟩
      exact (hinvHeight z).2.mpr hz
    · intro hy
      exact ⟨g y, ⟨mem_univ _, (hgheight y).2.mpr hy⟩, e.left_inv (mem_univ y)⟩
  have hGspace' : G.space = u '' K.space ∩ L.space := by
    rw [hGspace, hHspace]
    ext y
    constructor
    · rintro ⟨z, ⟨hzK, hzL⟩, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hzK
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      obtain ⟨w, hw, hwx⟩ := hzL
      have heq : e.symm (h x) = w := by rw [← hwx]; exact e.left_inv (mem_univ w)
      exact heq.symm ▸ hw
    · rintro ⟨⟨x, hx, rfl⟩, hxL⟩
      refine ⟨h x, ⟨⟨x, hx, rfl⟩, ⟨u x, hxL, ?_⟩⟩, rfl⟩
      exact e.right_inv (mem_univ (h x))
  refine ⟨u, G, k, hulip, hkη, hk1, huPL, huclose, hufix, huheight, hGfinite, hGspace', hGman, ?_⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hGspace ▸ hy
  rcases hHcross z hz with ⟨hz0, hcross⟩ | ⟨hzpos, hcross⟩
  · have hc := hcross.image_openPartialHomeomorph e.symm he.symm (mem_univ z)
    change HasPLBoundaryCrossingAt (e.symm '' (e.target ∩ {x : E | 0 ≤ ℓ x}))
      (e.symm '' (e.target ∩ h '' K.space)) (e.symm '' (e.target ∩ g '' L.space)) (e.symm z) at hc
    rw [hMimage, hKimage, hLimage] at hc
    exact Or.inl ⟨(hinvHeight z).1.mpr hz0, hc⟩
  · have hc := hcross.image_openPartialHomeomorph e.symm he.symm (mem_univ z)
    change HasPLCrossingAt (e.symm '' (e.target ∩ h '' K.space))
      (e.symm '' (e.target ∩ g '' L.space)) (e.symm z) at hc
    rw [hKimage, hLimage] at hc
    have hz' : 0 < ℓ (e.symm z) := lt_of_le_of_ne ((hinvHeight z).2.mpr hzpos.le)
      (fun heq => (ne_of_gt hzpos) ((hinvHeight z).1.mp heq.symm))
    exact Or.inr ⟨hz', hc⟩

open Classical in
theorem exists_small_homeomorph_generalPosition_in_halfSpace [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLℓ : ∀ w ∈ L.vertices, 0 ≤ ℓ w)
    (hKboundary : ∀ x ∈ K.space, ℓ x = 0 → x ∈ (boundaryComplex 2 K).space)
    (hLboundary : ∀ x ∈ L.space, ℓ x = 0 → x ∈ (boundaryComplex 2 L).space)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) (hLU : L.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (h : E → E) (G : Geometry.SimplicialComplex ℝ E), IsPLHomeomorphOn h univ univ ∧
      (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
        (∀ x, (ℓ (h x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (h x) ↔ 0 ≤ ℓ x)) ∧
          G.faces.Finite ∧ G.space = h '' K.space ∩ L.space ∧
            IsCombinatorialManifoldWithBoundary 1 G ∧
            ∀ y ∈ G.space,
              (ℓ y = 0 ∧ HasPLBoundaryCrossingAt {x : E | 0 ≤ ℓ x} (h '' K.space) L.space y) ∨
              (0 < ℓ y ∧ HasPLCrossingAt (h '' K.space) L.space y) := by
  obtain ⟨h, G, k, _, _, _, hh, hclose, hfix, hheight, hfin, hspace, hman, hcross⟩ :=
    exists_small_homeomorph_generalPosition_in_halfSpace_with_lipschitz_displacement K L
      hK hL hdim ℓ hℓ hKℓ hLℓ hKboundary hLboundary hU hKU hLU hε zero_lt_one
  exact ⟨h, G, hh, hclose, hfix, hheight, hfin, hspace, hman, hcross⟩

open Classical in
theorem exists_small_homeomorph_generalPosition_off_polyhedron_in_halfSpace
    [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hKhalf : K.space ⊆ {x | 0 ≤ ℓ x})
    {Q : Set E} (hQ : IsPolyhedron Q) (hKzero : K.space ∩ {x | ℓ x = 0} ⊆ Q)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) (hQU : Q ⊆ U)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ (h : E → E) (k : NNReal), LipschitzWith k (fun x => h x - x) ∧
      (k : ℝ) < η ∧ k < 1 ∧ IsPLHomeomorphOn h univ univ ∧
      (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧ EqOn h id Q ∧
      (∀ x, (ℓ (h x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (h x) ↔ 0 ≤ ℓ x)) ∧
      ∀ x ∈ h '' K.space ∩ L.space, x ∉ Q →
        0 < ℓ x ∧ HasPLCrossingAt (h '' K.space) L.space x := by
  obtain ⟨R, hR, hRfinite, hBspace⟩ := exists_isSubdivision_restrict_space K
    ((isPolyhedron_space K).inter hQ) inter_subset_left
  let _ := hRfinite.to_subtype
  let B := restrict R (K.space ∩ Q)
  have hBR : B.faces ⊆ R.faces := restrict_faces_subset R (K.space ∩ Q)
  let _ : Finite B.faces := (hRfinite.subset hBR).to_subtype
  let hc := centroid_mem_openSimplex_of_mem_faces R
  let T := relDerived hBR (IsSubdivision.refl B) hc
  have hT : IsSubdivision T R := relDerived_isSubdivision hBR (IsSubdivision.refl B) hc
  let _ : Finite T.faces :=
    (relDerived_faces_finite hBR (IsSubdivision.refl B) hc).to_subtype
  have hBT : B.faces ⊆ T.faces := faces_subset_relDerived hBR (IsSubdivision.refl B) hc
  have hTspace : T.space = K.space := hT.space_eq.trans hR.space_eq
  have hBspaceT : B.space = T.space ∩ Q := by rwa [hTspace]
  have hTman : IsCombinatorialManifoldWithBoundary 2 T :=
    (hK.of_isSubdivision hR).of_isSubdivision hT
  have hTnonneg : ∀ v ∈ T.vertices, 0 ≤ ℓ v := fun v hv =>
    hKhalf (hTspace ▸ T.subset_space hv (Finset.mem_singleton_self v))
  obtain ⟨δ, hδ, hext⟩ :=
    exists_lipschitz_displacement_extending_vertex_perturbation_fixing_polyhedron_in_halfSpace
      T B hBT hQ hBspaceT ℓ hℓ hTnonneg hU (by rwa [hTspace]) hQU hε hη
  have hcard : ∀ t ∈ T.faces, t.card ≤ Module.finrank ℝ E + 1 := by
    intro t ht
    have htcard := hTman.card_le T ht
    omega
  obtain ⟨φ, hφfix, hφclose, hgood⟩ := exists_small_vertexMap_transverse_off_fixed T L hcard id
    B.vertices (fun t ht _ => T.indep ht) hδ
  have hφplane : ∀ v ∈ T.vertices, ℓ v = 0 → ℓ (φ v) = 0 := by
    intro v hv hvzero
    have hvK : v ∈ K.space := hTspace ▸ T.subset_space hv (Finset.mem_singleton_self v)
    have hvBspace : v ∈ B.space := hBspace.symm ▸ ⟨hvK, hKzero ⟨hvK, hvzero⟩⟩
    obtain ⟨t, ht, hvt⟩ := B.mem_space_iff.mp hvBspace
    have hvt' := mem_of_mem_convexHull_of_singleton_mem T hv (hBT ht) hvt
    have hvB : v ∈ B.vertices := B.down_closed ht
      (Finset.singleton_subset_iff.mpr hvt') (Finset.singleton_nonempty v)
    rw [hφfix hvB]
    exact hvzero
  obtain ⟨a, k, -, hklip, hkη, hk1, hnorm, hzero, -, hagree, hh, hheight, hzeroQ⟩ :=
    hext φ (fun v _ => hφclose v) hφplane hφfix
  let h : E → E := fun x => x + a x
  have hfixQ : EqOn h id Q := by
    intro x hx
    change x + a x = x
    rw [hzeroQ hx, add_zero]
  have hinj : InjOn (simplicialMap T φ) T.space := by
    intro x hx y hy hxy
    apply hh.bijOn.injOn (mem_univ x) (mem_univ y)
    rw [hagree hx, hagree hy]
    exact hxy
  have hind : ∀ t ∈ T.faces, AffineIndependent ℝ ((↑) : ↥(t.image φ : Set E) → E) := by
    intro t ht
    exact ((affineIndependent_image_iff t φ).mp (hgood t ht).1).2
  let M := simplicialImage T φ hind hinj
  let _ : Finite M.faces := (simplicialImage_faces_finite T φ hind hinj).to_subtype
  have hMman : IsCombinatorialManifoldWithBoundary 2 M :=
    hTman.of_isPLHomeomorphOn (isPLHomeomorphOn_simplicialImage T φ hind hinj)
  have hMspace : M.space = h '' K.space := by
    rw [simplicialImage_space]
    have himage : simplicialMap T φ '' T.space = h '' T.space := image_congr hagree.symm
    rw [himage, hTspace]
  have hfixedHull : ∀ t ∈ T.faces, convexHull ℝ (id '' ((t : Set E) ∩ B.vertices)) ⊆ Q := by
    intro t ht
    let r := t.filter (fun v => v ∈ B.vertices)
    have hrset : (r : Set E) = (t : Set E) ∩ B.vertices := by
      simp only [r, Finset.coe_filter]
      rfl
    rw [image_id, ← hrset]
    by_cases hrne : r.Nonempty
    · have hrT := T.down_closed ht (Finset.filter_subset _ _) hrne
      have hrB := mem_faces_of_mem_relDerived_of_forall_singleton_mem hBR (IsSubdivision.refl B)
        hc hrT (fun v hv => (Finset.mem_filter.mp hv).2)
      exact (B.convexHull_subset_space hrB).trans (hBspace ▸ inter_subset_right)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hrne, Finset.coe_empty, convexHull_empty]
      exact empty_subset _
  refine ⟨h, k, ?_, hkη, hk1, hh, ?_, ?_, hfixQ, hheight, fun x hx hxQ => ?_⟩
  · simpa only [h, add_sub_cancel_left] using hklip
  · intro x
    simpa only [h, dist_eq_norm, add_sub_cancel_left] using hnorm x
  · intro x hx
    change x + a x = x
    rw [hzero hx, add_zero]
  · have hxpos : 0 < ℓ x := by
      obtain ⟨y, hyK, rfl⟩ := hx.1
      have hypos : 0 < ℓ y := lt_of_le_of_ne (hKhalf hyK) (fun hy0 => by
        have hyQ := hKzero ⟨hyK, hy0.symm⟩
        exact hxQ ((hfixQ hyQ).symm ▸ hyQ))
      exact lt_of_le_of_ne ((hheight y).2.mpr hypos.le)
        (fun hx0 => hypos.ne' ((hheight y).1.mp hx0.symm))
    refine ⟨hxpos, ?_⟩
    have hxM : x ∈ M.space := hMspace.symm ▸ hx.1
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex M hxM
    obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex L hx.2
    have htrans : vectorSpan ℝ (u : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ := by
      obtain ⟨s, hs, rfl⟩ := hu
      rcases (hgood s hs).2 t ht with htop | hsub
      · exact htop
      · exact False.elim (hxQ (hfixedHull s hs (hsub
          ⟨openSimplex_subset_convexHull _ hxu, openSimplex_subset_convexHull _ hxt⟩)))
    have hcross := hasPLCrossingAt_of_transverse_face M L hMman hL hdimE hu ht hxu hxt htrans
    rwa [hMspace] at hcross

open Classical in
theorem exists_small_homeomorph_generalPosition_in_halfSpace_with_chart_displacements
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hKhalf : K.space ⊆ {x | 0 ≤ ℓ x})
    {Q : Set E} (hQ : IsPolyhedron Q) (hKzero : K.space ∩ {x | ℓ x = 0} ⊆ Q)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) (hQU : Q ⊆ U)
    (P : ι → Set E) (hP : ∀ i, IsPolyhedron (P i)) (hPU : ∀ i, P i ⊆ U)
    (f : ι → E → F) (hf : ∀ i, IsPiecewiseAffineOn (f i) (P i)) :
    ∃ S : Set E, IsPolyhedron S ∧ S ⊆ ⋃ i, P i ∧ interior S = ∅ ∧
      ∀ ε η : ℝ, 0 < ε → 0 < η →
        ∃ (h : E → E) (k : NNReal), LipschitzWith k (fun x => h x - x) ∧
          (k : ℝ) < η ∧ k < 1 ∧ IsPLHomeomorphOn h univ univ ∧
          (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧ EqOn h id (Q ∪ S) ∧
          (∀ x, (ℓ (h x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (h x) ↔ 0 ≤ ℓ x)) ∧
          (∀ x ∈ h '' K.space ∩ L.space, x ∉ Q ∪ S →
            0 < ℓ x ∧ HasPLCrossingAt (h '' K.space) L.space x) ∧
          ∀ i, (∀ x, h x ∈ P i ↔ x ∈ P i) ∧
            ∃ (b : E → F) (ki : NNReal), IsPiecewiseAffineOn b univ ∧
              LipschitzWith ki b ∧ (ki : ℝ) < η ∧
              EqOn b (fun x => f i (h x) - f i x) (P i) ∧ EqOn b (fun _ => 0) (P i)ᶜ := by
  choose S c hS hSP hSint hext using fun i =>
    (hf i).exists_polyhedron_lipschitz_displacement (hP i)
  let T : Set E := ⋃ i, S i
  have hT : IsPolyhedron T := IsPolyhedron.iUnion hS
  have hTP : T ⊆ ⋃ i, P i := iUnion_mono hSP
  have hTinterior : interior T = ∅ :=
    interior_iUnion_eq_empty_of_finite (fun i => (hS i).isClosed) hSint
  have hTU : T ⊆ U := iUnion_subset fun i => (hSP i).trans (hPU i)
  let _ := Fintype.ofFinite ι
  let C : NNReal := Finset.univ.sup c
  refine ⟨T, hT, hTP, hTinterior, fun ε η hε hη => ?_⟩
  let μ : ℝ := min η (η / ((C : ℝ) + 1))
  have hμ : 0 < μ := lt_min hη (div_pos hη (by positivity))
  obtain ⟨h, k, hk, hkμ, hk1, hh, hclose, hfix, hfixQ, hheight, hcross⟩ :=
    exists_small_homeomorph_generalPosition_off_polyhedron_in_halfSpace K L hK hL hdimE
      ℓ hℓ hKhalf (hQ.union hT) (hKzero.trans subset_union_left) hU hKU
      (union_subset hQU hTU) hε hμ
  have hkη : (k : ℝ) < η := hkμ.trans_le (min_le_left _ _)
  let a : E → E := fun x => h x - x
  have ha : IsPiecewiseAffineOn a univ := by
    have hneg := (isPiecewiseAffineOn_id (E := E) isOpen_univ).affine_comp
      (-AffineMap.id ℝ E)
    change IsPiecewiseAffineOn (fun x : E => -x) univ at hneg
    simpa only [a, sub_eq_add_neg] using hh.isPiecewiseAffineOn.add hneg
  have hformula (x : E) : x + a x = h x := by dsimp only [a]; abel
  refine ⟨h, k, hk, hkη, hk1, hh, hclose, hfix, hfixQ, hheight, hcross, fun i => ?_⟩
  have hzero : EqOn a (fun _ => 0) (S i) := by
    intro x hx
    change h x - x = 0
    rw [hfixQ (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))]
    exact sub_self x
  obtain ⟨b, hb, hblip, hbmap, hbzero, hmem⟩ := hext i a k ha hk hk1 hzero
  refine ⟨fun x => by simpa only [hformula] using hmem x, b, c i * k, hb, hblip, ?_, ?_, hbzero⟩
  · have hci : c i ≤ C := Finset.le_sup (f := c) (Finset.mem_univ i)
    have hsmall : (k : ℝ) * ((C : ℝ) + 1) < η :=
      (lt_div_iff₀ (show 0 < (C : ℝ) + 1 by positivity)).mp
        (hkμ.trans_le (min_le_right _ _))
    change (c i : ℝ) * (k : ℝ) < η
    calc (c i : ℝ) * (k : ℝ) ≤ (C : ℝ) * (k : ℝ) :=
          mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hci) k.property
      _ ≤ (k : ℝ) * ((C : ℝ) + 1) := by
        rw [mul_add, mul_one, mul_comm (k : ℝ) (C : ℝ)]
        exact le_add_of_nonneg_right k.property
      _ < η := hsmall
  · simpa only [hformula] using hbmap

open Classical in
theorem exists_small_homeomorph_generalPosition_in_halfSpace_with_local_conjugates
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite ι]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hKhalf : K.space ⊆ {x | 0 ≤ ℓ x})
    {Q : Set E} (hQ : IsPolyhedron Q) (hKzero : K.space ∩ {x | ℓ x = 0} ⊆ Q)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) (hQU : Q ⊆ U)
    (P : ι → Set E) (hP : ∀ i, IsPolyhedron (P i)) (hPU : ∀ i, P i ⊆ U)
    (e : ι → OpenPartialHomeomorph E E)
    (he : ∀ i, IsPiecewiseAffineOn (e i) (e i).source)
    (hPe : ∀ i, P i ⊆ (e i).source) :
    ∃ S : Set E, IsPolyhedron S ∧ S ⊆ ⋃ i, P i ∧ interior S = ∅ ∧
      ∀ ε η : ℝ, 0 < ε → 0 < η →
        ∃ (h : E → E) (k : NNReal), LipschitzWith k (fun x => h x - x) ∧
          (k : ℝ) < η ∧ k < 1 ∧ IsPLHomeomorphOn h univ univ ∧
          (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧ EqOn h id (Q ∪ S) ∧
          (∀ x, (ℓ (h x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (h x) ↔ 0 ≤ ℓ x)) ∧
          (∀ x ∈ h '' K.space ∩ L.space, x ∉ Q ∪ S →
            0 < ℓ x ∧ HasPLCrossingAt (h '' K.space) L.space x) ∧
          ∀ i, (∀ x, h x ∈ P i ↔ x ∈ P i) ∧
            ∃ (H : E → E) (ki : NNReal), IsPLHomeomorphOn H univ univ ∧
              LipschitzWith ki (fun y => H y - y) ∧ (ki : ℝ) < η ∧ ki < 1 ∧
              EqOn H ((e i) ∘ h ∘ (e i).symm) ((e i) '' P i) := by
  have heP (i : ι) : IsPiecewiseAffineOn (e i) (P i) :=
    (he i).mono_of_isPolyhedron (hP i) (hPe i)
  have hR (i : ι) : IsPolyhedron ((e i) '' P i) :=
    (hP i).image_of_isPiecewiseAffineOn (heP i) ((e i).injOn.mono (hPe i))
  have hRtarget (i : ι) : (e i) '' P i ⊆ (e i).target := by
    rintro y ⟨x, hx, rfl⟩
    exact (e i).map_source (hPe i hx)
  have hinv (i : ι) : IsPiecewiseAffineOn (e i).symm ((e i) '' P i) :=
    (IsPiecewiseAffineOn.symm (e := e i) (he i)).mono_of_isPolyhedron (hR i) (hRtarget i)
  choose g c hg hglip hgfix hgzero hgrange using fun i =>
    (hinv i).exists_lipschitz_extension (hR i) isOpen_univ (subset_univ _)
  obtain ⟨S, hS, hSP, hSint, hperturb⟩ :=
    exists_small_homeomorph_generalPosition_in_halfSpace_with_chart_displacements
      K L hK hL hdimE ℓ hℓ hKhalf hQ hKzero hU hKU hQU P hP hPU
      (fun i => e i) heP
  let _ := Fintype.ofFinite ι
  let C : NNReal := Finset.univ.sup c
  refine ⟨S, hS, hSP, hSint, fun ε η hε hη => ?_⟩
  let τ : ℝ := min η 1
  have hτ : 0 < τ := lt_min hη zero_lt_one
  let μ : ℝ := min τ (τ / ((C : ℝ) + 1))
  have hμ : 0 < μ := lt_min hτ (div_pos hτ (by positivity))
  obtain ⟨h, k, hk, hkμ, hk1, hh, hclose, hfix, hfixQ, hheight, hcross, hchart⟩ :=
    hperturb ε μ hε hμ
  have hkη : (k : ℝ) < η := hkμ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  refine ⟨h, k, hk, hkη, hk1, hh, hclose, hfix, hfixQ, hheight, hcross, fun i => ?_⟩
  obtain ⟨hmem, b, ki, hb, hbLip, hki, hbmap, _⟩ := hchart i
  let a : E → E := b ∘ g i
  have ha : IsPiecewiseAffineOn a univ := by
    simpa only [inter_univ, preimage_univ] using hb.comp (hg i)
  have halip : LipschitzWith (ki * c i) a := hbLip.comp (hglip i)
  have hbound : (ki * c i : NNReal) < τ := by
    have hci : c i ≤ C := Finset.le_sup (f := c) (Finset.mem_univ i)
    have hsmall : (ki : ℝ) * ((C : ℝ) + 1) < τ :=
      (lt_div_iff₀ (show 0 < (C : ℝ) + 1 by positivity)).mp
        (hki.trans_le (min_le_right _ _))
    change (ki : ℝ) * (c i : ℝ) < τ
    calc (ki : ℝ) * (c i : ℝ) ≤ (ki : ℝ) * (C : ℝ) :=
          mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hci) ki.property
      _ ≤ (ki : ℝ) * ((C : ℝ) + 1) := by
        rw [mul_add, mul_one]
        exact le_add_of_nonneg_right ki.property
      _ < τ := hsmall
  have hprod1 : ki * c i < 1 := hbound.trans_le (min_le_right _ _)
  refine ⟨hmem, fun y => y + a y, ki * c i,
    isPLHomeomorphOn_id_add_of_lipschitz ha halip hprod1, ?_,
    hbound.trans_le (min_le_left _ _), hprod1, ?_⟩
  · simpa only [add_sub_cancel_left] using halip
  · rintro y ⟨x, hx, rfl⟩
    change e i x + b (g i (e i x)) = e i (h ((e i).symm (e i x)))
    rw [hgfix i ⟨x, hx, rfl⟩, (e i).left_inv (hPe i hx), hbmap hx]
    rw [← add_sub_assoc, add_sub_cancel_left]

end DifferentialGeometry.Topology.PiecewiseLinear
