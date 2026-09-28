/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ProtectedSubdivisionTools
import DifferentialGeometry.Topology.PiecewiseLinear.AdmissibleVertexMapVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.FreeGermVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.GenericDoublePointSheets
import DifferentialGeometry.Topology.PiecewiseLinear.MapApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.LinkEuclidean
import DifferentialGeometry.Topology.PiecewiseLinear.Mesh

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem closure_sdiff_subset_of_frontier_cover {E : Type*} [TopologicalSpace E]
    {Rsp Asp Ω Nb : Set E} (hRc : IsClosed Rsp) (hNb : IsOpen Nb) (hNbfr : Rsp \ Ω ⊆ Nb)
    (hNbA : Rsp ∩ Nb ⊆ Asp) : closure (Rsp \ Asp) ⊆ Ω := by
  intro z hz
  by_contra hzΩ
  have hzR : z ∈ Rsp := hRc.closure_subset (closure_mono sdiff_subset hz)
  have hzN : z ∈ Nb := hNbfr ⟨hzR, hzΩ⟩
  obtain ⟨w, hwN, hwR, hwA⟩ := mem_closure_iff.mp hz Nb hNb hzN
  exact hwA (hNbA ⟨hwR, hwN⟩)

theorem exists_pos_cthickening_chart_nhds {X : Type*} [MetricSpace X]
    (ec : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3))) {V L : Set X} (hV : IsOpen V)
    (hVs : V ⊆ ec.source) (hL : IsCompact L) (hLV : L ⊆ V) :
    ∃ ρ : ℝ, 0 < ρ ∧ cthickening ρ (ec '' L) ⊆ ec '' V ∧
      IsCompact (ec.symm '' cthickening ρ (ec '' L)) ∧ ec.symm '' cthickening ρ (ec '' L) ⊆ V ∧
      L ⊆ interior (ec.symm '' cthickening ρ (ec '' L)) := by
  have hVo : IsOpen (ec '' V) := ec.isOpen_image_of_subset_source hV hVs
  have hLc : IsCompact (ec '' L) := hL.image_of_continuousOn (ec.continuousOn.mono (hLV.trans hVs))
  obtain ⟨ρ, hρ, hsub⟩ := hLc.exists_cthickening_subset_open hVo (image_mono hLV)
  have hVt : ec '' V ⊆ ec.target := by
    rintro _ ⟨v, hv, rfl⟩
    exact ec.map_source (hVs hv)
  refine ⟨ρ, hρ, hsub, hLc.cthickening.image_of_continuousOn
    (ec.continuousOn_symm.mono (hsub.trans hVt)), ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hsub hz
    rw [ec.left_inv (hVs hv)]
    exact hv
  · intro l hl
    have hth : thickening ρ (ec '' L) ⊆ ec.symm.source :=
      (thickening_subset_cthickening ρ _).trans (hsub.trans hVt)
    have ho : IsOpen (ec.symm '' thickening ρ (ec '' L)) :=
      ec.symm.isOpen_image_of_subset_source isOpen_thickening hth
    refine interior_maximal (image_mono (thickening_subset_cthickening ρ _)) ho ⟨ec l, ?_, ?_⟩
    · exact self_subset_thickening hρ _ (mem_image_of_mem ec hl)
    · exact ec.left_inv (hVs (hLV hl))

section MetricAmbient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_isSubdivision_affine_injOn_closedStar_mesh (D : SingularTwoCell M)
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (hRfin : Rc.faces.Finite)
    (hRdom : Rc.space ⊆ D.domain) (hRsrc : Rc.space ⊆ ⇑D ⁻¹' ec.source) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)), IsSubdivision R Rc ∧
      R.faces.Finite ∧
      (∀ s ∈ R.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
        EqOn (fun x => ec (D x)) A (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2))))) ∧
      (∀ v ∈ R.vertices, InjOn (⇑D) (closedStar R v)) ∧
      ∀ s ∈ R.faces, ∀ x ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2))),
        ∀ y ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2))),
          dist (ec (D x)) (ec (D y)) < θ := by
  have : Finite Rc.faces := hRfin.to_subtype
  have hPL : IsPiecewiseAffineOn (fun x => ec (D x)) Rc.space :=
    D.isPiecewiseAffineOn_chart_comp hec (isPolyhedron_space Rc) hRdom hRsrc
  obtain ⟨R₁, hR₁, hR₁fin, hR₁aff⟩ := hPL.exists_isSubdivision_affineOn_faces Rc
  have : Finite R₁.faces := hR₁fin.to_subtype
  have hRcc : IsCompact Rc.space := (isPolyhedron_space Rc).isCompact
  obtain ⟨β, hβ, hβ'⟩ := Metric.uniformContinuousOn_iff.mp
    (hRcc.uniformContinuousOn_of_continuous hPL.continuousOn) θ hθ
  have hO : ∀ x ∈ D.domain, ∃ O : Set (EuclideanSpace ℝ (Fin 2)), IsOpen O ∧ x ∈ O ∧
      InjOn (⇑D) (O ∩ D.domain) := by
    intro x hx
    obtain ⟨U, hU, hinj⟩ := hloc x hx
    obtain ⟨O, hOo, hxO, hOU⟩ := mem_nhdsWithin.mp hU
    exact ⟨O, hOo, hxO, hinj.mono hOU⟩
  choose O hOo hxO hOinj using hO
  let U : D.domain → Set (EuclideanSpace ℝ (Fin 2)) := fun p =>
    ball (p : EuclideanSpace ℝ (Fin 2)) (β / 2) ∩ O p p.2
  have hUo : ∀ p, IsOpen (((↑) : R₁.space → EuclideanSpace ℝ (Fin 2)) ⁻¹' U p) := fun p =>
    (isOpen_ball.inter (hOo p p.2)).preimage continuous_subtype_val
  have hcover : R₁.space ⊆ ⋃ p, U p := by
    intro x hx
    have hxD : x ∈ D.domain := hRdom (hR₁.space_eq ▸ hx)
    exact mem_iUnion.mpr ⟨⟨x, hxD⟩, mem_ball_self (half_pos hβ), hxO x hxD⟩
  obtain ⟨R, hR, hRfin', hRU⟩ := exists_isSubdivision_closedStars_subset_cover R₁ U hUo hcover
  have hRspace : R.space = Rc.space := hR.space_eq.trans hR₁.space_eq
  refine ⟨R, hR.trans hR₁, hRfin', ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, hst⟩ := hR.exists_face_subset hs
    obtain ⟨A, hA⟩ := hR₁aff t ht
    exact ⟨A, hA.mono hst⟩
  · intro v hv
    obtain ⟨p, hp⟩ := hRU {v} hv
    have hsub : closedStar R v ⊆ U p := fun y hy =>
      hp (mem_iUnion₂.mpr ⟨v, Finset.mem_singleton_self v, hy⟩)
    have hsub2 : closedStar R v ⊆ O p p.2 ∩ D.domain := fun y hy =>
      ⟨(hsub hy).2, hRdom (hRspace ▸ closedStar_subset_space R v hy)⟩
    exact (hOinj p p.2).mono hsub2
  · intro s hs x hx y hy
    obtain ⟨v, hv⟩ := R.nonempty_of_mem_faces hs
    obtain ⟨p, hp⟩ := hRU s hs
    have hcs : convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ closedStar R v :=
      fun z hz => mem_biUnion ⟨hs, subset_convexHull ℝ _ hv⟩ hz
    have hxU := hp (mem_iUnion₂.mpr ⟨v, hv, hcs hx⟩)
    have hyU := hp (mem_iUnion₂.mpr ⟨v, hv, hcs hy⟩)
    have hxy : dist x y < β := by
      have h1 := hxU.1
      have h2 := hyU.1
      rw [mem_ball] at h1 h2
      calc dist x y ≤ dist x (p : EuclideanSpace ℝ (Fin 2)) +
            dist y (p : EuclideanSpace ℝ (Fin 2)) := dist_triangle_right _ _ _
        _ < β / 2 + β / 2 := add_lt_add h1 h2
        _ = β := by ring
    have hxR : x ∈ Rc.space := hRspace ▸ R.convexHull_subset_space hs hx
    have hyR : y ∈ Rc.space := hRspace ▸ R.convexHull_subset_space hs hy
    exact hβ' x hxR y hyR hxy

theorem simplicialMap_eq_of_affine_faces {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {f : EuclideanSpace ℝ (Fin 2) → F}
    (hlinear : ∀ s ∈ R.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] F,
      EqOn f A (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2)))))
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ R.space) : simplicialMap R f x = f x := by
  obtain ⟨s, hs, hxs⟩ := R.mem_space_iff.mp hx
  obtain ⟨A, hA⟩ := hlinear s hs
  exact simplicialMap_eqOn_of_affineOn R f hs hA hxs

theorem regionGluedMap_chart_of_mem (D : SingularTwoCell M) {V : Set M}
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) (hVs : V ⊆ ec.source)
    (R Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hmaps : MapsTo (simplicialMap R φ) Rc.space (⇑ec '' V))
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ Rc.space) :
    regionGluedMap D ec R φ Rc x ∈ V ∧ ec (regionGluedMap D ec R φ Rc x) = simplicialMap R φ x := by
  rw [regionGluedMap_of_mem D ec R φ hx]
  obtain ⟨v, hv, hveq⟩ := hmaps hx
  rw [← hveq, ec.left_inv (hVs hv)]
  exact ⟨hv, rfl⟩

theorem regionGluedMap_of_notMem (D : SingularTwoCell M)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (R Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∉ Rc.space) : regionGluedMap D ec R φ Rc x = D x := by
  classical
  simp only [regionGluedMap, ite_eq_right hx]

theorem admissibleVertexMap_region_clauses (D : SingularTwoCell M) {BdM C V W K : Set M}
    {τ ε d₀ ρ : ℝ} (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C) (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hVs : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsub : IsSubdivision R Rc) (hRfin : R.faces.Finite)
    (hlinear : ∀ s ∈ R.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
      EqOn (fun x => ec (D x)) A (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2)))))
    (hAR : Ac.faces ⊆ Rc.faces) (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hd₀ : ∀ a ∈ Ac.space, ∀ w ∈ closure W, d₀ ≤ dist (ec (D a)) (ec w))
    (hmesh : ∀ s ∈ R.faces, ∀ x ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2))),
      ∀ y ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2))),
        dist (ec (D x)) (ec (D y)) < d₀ / 2)
    (hτd : τ ≤ d₀ / 2) (hτε : τ ≤ ε)
    (hconvV : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → z ∈ ⇑ec '' V)
    (hτρ : τ ≤ ρ) (hK : ec.symm '' cthickening ρ (⇑ec '' (⇑D '' Rc.space)) ⊆ K)
    {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hadm : AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ) :
    IsPiecewiseAffineOn (simplicialMap R φ) Rc.space ∧
      (∀ x ∈ Rc.space, dist (simplicialMap R φ x) (ec (D x)) < τ) ∧
      EqOn (simplicialMap R φ) (fun x => ec (D x)) Ac.space ∧
      (∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap R φ x)) ∧
      (∀ x ∈ Rc.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ Lc.space) ∧
      (∀ σ ∈ R.faces, (∃ v ∈ σ, v ∈ Ac.space) →
        Disjoint (simplicialMap R φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))
          (⇑ec '' closure W)) ∧
      MapsTo (simplicialMap R φ) Rc.space (⇑ec '' V) ∧
      regionGluedMap D ec R φ Rc '' Rc.space ⊆ K := by
  obtain ⟨-, hBvL, hdist, hfixA, hBv0, hBvpos⟩ := hadm
  have : Finite R.faces := hRfin.to_subtype
  have hRsp : R.space = Rc.space := hsub.space_eq
  have hvR : ∀ v ∈ R.vertices, v ∈ Rc.space := fun v hv =>
    hRsp ▸ R.convexHull_subset_space hv (subset_convexHull ℝ _ (Finset.mem_singleton_self v))
  have hsrc : ∀ x ∈ Rc.space, D x ∈ ec.source := fun x hx => hVs (hRV hx)
  have hlin' : ∀ x ∈ Rc.space, simplicialMap R (fun v => ec (D v)) x = ec (D x) := fun x hx =>
    simplicialMap_eq_of_affine_faces R hlinear (hRsp ▸ hx)
  have hclose : ∀ x ∈ Rc.space, dist (simplicialMap R φ x) (ec (D x)) < τ := by
    intro x hx
    rw [← hlin' x hx]
    exact dist_simplicialMap_lt_of_dist_vertices_lt R hdist (hRsp ▸ hx)
  have hmaps : MapsTo (simplicialMap R φ) Rc.space (⇑ec '' V) := fun x hx =>
    hconvV x hx _ ((hclose x hx).trans_le hτε)
  have hfixed : EqOn (simplicialMap R φ) (fun x => ec (D x)) Ac.space := by
    intro x hx
    have hxR : x ∈ Rc.space := by
      obtain ⟨t, ht, hxt⟩ := Ac.mem_space_iff.mp hx
      exact Rc.convexHull_subset_space (hAR ht) hxt
    rw [hsub.simplicialMap_eqOn_of_eqOn_vertices hAR (ψ := fun v => ec (D v))
      (fun v hv hvA => hfixA v hv hvA) hx]
    exact hlin' x hxR
  have hℓD : ∀ x ∈ Rc.space, (ℓ (ec (D x)) = 0 ↔ x ∈ Lc.space) := by
    intro x hx
    rw [← hBdchart (D x) (hsrc x hx), hLspace]
    constructor
    · intro hB
      have hmem : x ∈ D.domain ∩ ⇑D ⁻¹' BdM := ⟨hRdom hx, hB⟩
      rw [hproper] at hmem
      exact ⟨hx, hmem⟩
    · rintro ⟨-, hfr⟩
      have hmem : x ∈ D.domain ∩ ⇑D ⁻¹' BdM := by rw [hproper]; exact hfr
      exact hmem.2
  have hℓD0 : ∀ x ∈ Rc.space, 0 ≤ ℓ (ec (D x)) := fun x hx =>
    (hCchart (D x) (hsrc x hx)).mp (hmapC (hRdom hx))
  have hℓφ0 : ∀ v ∈ R.vertices, 0 ≤ ℓ (φ v) := by
    intro v hv
    by_cases hB : v ∈ Bv
    · exact (hBv0 v hv hB).ge
    · exact (hBvpos v hv hB).le
  have hℓeq : ∀ v ∈ R.vertices, (ℓ (φ v) = 0 ↔ ℓ (ec (D v)) = 0) := by
    intro v hv
    rw [hℓD v (hvR v hv), ← hBvL v hv]
    constructor
    · intro h0
      by_contra hB
      exact (hBvpos v hv hB).ne' h0
    · exact hBv0 v hv
  refine ⟨?_, hclose, hfixed, ?_, ?_, ?_, hmaps, ?_⟩
  · rw [← hRsp]
    exact isPiecewiseAffineOn_simplicialMap R φ
  · intro x hx
    rw [linearMap_simplicialMap R φ ℓ x]
    exact simplicialMap_nonneg_of_nonneg_vertices R _ hℓφ0 (hRsp ▸ hx)
  · intro x hx
    rw [linearMap_simplicialMap R φ ℓ x, simplicialMap_eq_zero_iff_of_eq_zero_on_vertices R
      (ℓ ∘ φ) (fun v => ℓ (ec (D v))) hℓφ0 (fun v hv => hℓD0 v (hvR v hv)) hℓeq (hRsp ▸ hx)]
    have e : simplicialMap R (fun v => ℓ (ec (D v))) x = ℓ (ec (D x)) := by
      have h1 := linearMap_simplicialMap R (fun v => ec (D v)) ℓ x
      rw [hlin' x hx] at h1
      exact h1.symm
    rw [e]
    exact hℓD x hx
  · rintro σ hσ ⟨v, hvσ, hvA⟩
    rw [Set.disjoint_left]
    rintro _ ⟨x, hxσ, rfl⟩ ⟨w, hw, hwx⟩
    have hvhull : v ∈ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) :=
      subset_convexHull ℝ _ hvσ
    have hxR : x ∈ Rc.space := hRsp ▸ R.convexHull_subset_space hσ hxσ
    have h1 := hd₀ v hvA w hw
    rw [hwx] at h1
    have h2 := hmesh σ hσ v hvhull x hxσ
    have h3 := hclose x hxR
    have h4 : dist (ec (D v)) (simplicialMap R φ x) ≤
        dist (ec (D v)) (ec (D x)) + dist (simplicialMap R φ x) (ec (D x)) := by
      calc dist (ec (D v)) (simplicialMap R φ x)
          ≤ dist (ec (D v)) (ec (D x)) + dist (ec (D x)) (simplicialMap R φ x) :=
            dist_triangle _ _ _
        _ = dist (ec (D v)) (ec (D x)) + dist (simplicialMap R φ x) (ec (D x)) := by
            rw [dist_comm (ec (D x))]
    linarith
  · rintro _ ⟨x, hx, rfl⟩
    apply hK
    refine ⟨simplicialMap R φ x, ?_, ?_⟩
    · exact mem_cthickening_of_dist_le _ (ec (D x)) ρ _ (mem_image_of_mem ec
        (mem_image_of_mem D hx)) ((hclose x hx).le.trans hτρ)
    · rw [regionGluedMap_of_mem D ec R φ hx]

end MetricAmbient

end DifferentialGeometry.Topology.PiecewiseLinear
