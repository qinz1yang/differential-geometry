/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ProtectedSubdivisionClauses

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section MetricAmbient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_pos_starInj_regionGluedMap (D : SingularTwoCell M) {V : Set M}
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hVs : V ⊆ ec.source)
    (Rc Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))} (hsub : IsSubdivision R Rc) (hRfin : R.faces.Finite)
    (hlinear : ∀ s ∈ R.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
      EqOn (fun x => ec (D x)) A (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2)))))
    (hAR : Ac.faces ⊆ Rc.faces) (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hinjR : ∀ v ∈ R.vertices, InjOn (⇑D) (closedStar R v))
    (hΩ : IsOpen Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (hTfin : T.faces.Finite)
    (hTspace : T.space = D.domain) (hTstar : StarInj T (⇑D)) {ε : ℝ} (hε : 0 < ε)
    (hconvV : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → z ∈ ⇑ec '' V) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
      (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
      AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ → StarInj T (regionGluedMap D ec R φ Rc) := by
  have : Finite R.faces := hRfin.to_subtype
  have : Finite T.faces := hTfin.to_subtype
  have hRsp : R.space = Rc.space := hsub.space_eq
  have hsrc : ∀ x ∈ Rc.space, D x ∈ ec.source := fun x hx => hVs (hRV hx)
  have hlin' : ∀ x ∈ Rc.space, simplicialMap R (fun v => ec (D v)) x = ec (D x) := fun x hx =>
    simplicialMap_eq_of_affine_faces R hlinear (hRsp ▸ hx)
  have hinj₀ : ∀ v ∈ R.vertices,
      InjOn (simplicialMap R (fun v => ec (D v))) (closedStar R v) := by
    intro v hv x hx y hy hxy
    have hxR : x ∈ Rc.space := hRsp ▸ closedStar_subset_space R v hx
    have hyR : y ∈ Rc.space := hRsp ▸ closedStar_subset_space R v hy
    rw [hlin' x hxR, hlin' y hyR] at hxy
    exact hinjR v hv hx hy (ec.injOn (hsrc x hxR) (hsrc y hyR) hxy)
  obtain ⟨δR, hδR, hδRinj⟩ :=
    exists_injOn_closedStar_of_small_vertex_perturbation R (fun v => ec (D v)) hinj₀
  set τ₀ : ℝ := min δR ε
  have hτ₀pos : 0 < τ₀ := lt_min hδR hε
  have hRcc : IsClosed Rc.space := hRsp ▸ (isPolyhedron_space R).isCompact.isClosed
  have hKc : closure (Rc.space \ Ac.space) ⊆ Ω :=
    closure_sdiff_subset_of_frontier_cover hRcc hNb hNbfr hNbA
  have hclose : ∀ {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
      {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)} {τ : ℝ},
      AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ →
        ∀ x ∈ Rc.space, dist (simplicialMap R φ x) (ec (D x)) < τ := by
    intro Bv φ τ hadm x hx
    rw [← hlin' x hx]
    exact dist_simplicialMap_lt_of_dist_vertices_lt R hadm.2.2.1 (hRsp ▸ hx)
  have hfixA : ∀ {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
      {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)} {τ : ℝ},
      AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ →
        ∀ x ∈ Ac.space, simplicialMap R φ x = ec (D x) := by
    intro Bv φ τ hadm x hx
    have hxR : x ∈ Rc.space := by
      obtain ⟨t, ht, hxt⟩ := Ac.mem_space_iff.mp hx
      exact Rc.convexHull_subset_space (hAR ht) hxt
    rw [hsub.simplicialMap_eqOn_of_eqOn_vertices hAR (ψ := fun v => ec (D v))
      (fun v hv hvA => hadm.2.2.2.1 v hv hvA) hx]
    exact hlin' x hxR
  let P : (EuclideanSpace ℝ (Fin 2) → M) → Prop := fun g =>
    ∃ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
      (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
      AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ₀ ∧ g = regionGluedMap D ec R φ Rc
  have hmapsP : ∀ {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
      {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)},
      AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ₀ →
        MapsTo (simplicialMap R φ) Rc.space (⇑ec '' V) := fun hadm x hx =>
    hconvV x hx _ ((hclose hadm x hx).trans_le (min_le_right _ _))
  have hlocal : ∀ z ∈ T.space, ∃ G : Set (EuclideanSpace ℝ (Fin 2)), IsOpen G ∧ z ∈ G ∧
      ∀ g, P g → InjOn g (T.space ∩ G) := by
    intro z hz
    rw [hTspace] at hz
    by_cases hzΩ : z ∈ Ω
    · have hzR : z ∈ R.space := hRsp ▸ hΩR ⟨hz, hzΩ⟩
      obtain ⟨w, hw, G₁, hG₁o, hzG₁, hG₁sub⟩ := exists_isOpen_inter_space_subset_closedStar R hzR
      refine ⟨Ω ∩ G₁, hΩ.inter hG₁o, ⟨hzΩ, hzG₁⟩, ?_⟩
      rintro g ⟨Bv, φ, hadm, rfl⟩ x hx y hy hxy
      rw [hTspace] at hx hy
      have hxR : x ∈ Rc.space := hΩR ⟨hx.1, hx.2.1⟩
      have hyR : y ∈ Rc.space := hΩR ⟨hy.1, hy.2.1⟩
      have hxS : x ∈ closedStar R w := hG₁sub ⟨hx.2.2, hRsp ▸ hxR⟩
      have hyS : y ∈ closedStar R w := hG₁sub ⟨hy.2.2, hRsp ▸ hyR⟩
      have hpx := (regionGluedMap_chart_of_mem D ec hVs R Rc φ (hmapsP hadm) hxR).2
      have hpy := (regionGluedMap_chart_of_mem D ec hVs R Rc φ (hmapsP hadm) hyR).2
      have hpxy : simplicialMap R φ x = simplicialMap R φ y := by
        rw [← hpx, ← hpy, hxy]
      exact hδRinj φ (fun v hv => (hadm.2.2.1 v hv).trans_le (min_le_left _ _)) w hw hxS hyS hpxy
    · have hzK : z ∉ closure (Rc.space \ Ac.space) := fun h => hzΩ (hKc h)
      obtain ⟨U, hU, hUinj⟩ := hloc z hz
      obtain ⟨O, hOo, hzO, hOU⟩ := mem_nhdsWithin.mp hU
      refine ⟨(closure (Rc.space \ Ac.space))ᶜ ∩ O, isClosed_closure.isOpen_compl.inter hOo,
        ⟨hzK, hzO⟩, ?_⟩
      rintro g ⟨Bv, φ, hadm, rfl⟩
      rw [hTspace]
      have heq : EqOn (⇑D) (regionGluedMap D ec R φ Rc)
          (D.domain ∩ ((closure (Rc.space \ Ac.space))ᶜ ∩ O)) := by
        rintro x ⟨hxD, hxK, -⟩
        by_cases hxR : x ∈ Rc.space
        · have hxA : x ∈ Ac.space := by
            by_contra hxA
            exact hxK (subset_closure ⟨hxR, hxA⟩)
          rw [regionGluedMap_of_mem D ec R φ hxR, hfixA hadm x hxA, ec.left_inv (hsrc x hxR)]
        · rw [regionGluedMap_of_notMem D ec R Rc φ hxR]
      refine (hUinj.mono ?_).congr heq
      rintro x ⟨hxD, -, hxO⟩
      exact hOU ⟨hxO, hxD⟩
  have hDc : ContinuousOn (⇑D) T.space := hTspace ▸ D.continuousOn
  obtain ⟨m, hm, hmT⟩ := starInj_of_forall_injOn_nhds T hDc hTstar P hlocal
  have hRcomp : IsCompact Rc.space := hRsp ▸ (isPolyhedron_space R).isCompact
  have hK₁ : IsCompact (⇑ec '' (⇑D '' Rc.space)) :=
    (hRcomp.image_of_continuousOn (D.continuousOn.mono hRdom)).image_of_continuousOn
      (ec.continuousOn.mono fun _ ⟨x, hx, hxy⟩ => hxy ▸ hsrc x hx)
  have hK₁t : ⇑ec '' (⇑D '' Rc.space) ⊆ ec.target := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ec.map_source (hsrc x hx)
  obtain ⟨τ₁, hτ₁, hτ₁'⟩ := OpenPartialHomeomorph.exists_pos_dist_symm_lt ec hK₁ hK₁t hm
  refine ⟨min τ₀ τ₁, lt_min hτ₀pos hτ₁, fun Bv φ hadm => ?_⟩
  have hadm₀ : AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ₀ := hadm.mono (min_le_left _ _)
  refine hmT _ ⟨Bv, φ, hadm₀, rfl⟩ fun x hx => ?_
  rw [hTspace] at hx
  by_cases hxR : x ∈ Rc.space
  · have hk : ec (D x) ∈ ⇑ec '' (⇑D '' Rc.space) := mem_image_of_mem ec (mem_image_of_mem D hxR)
    have h1 := (hτ₁' _ hk _ ((hclose hadm x hxR).trans_le (min_le_right _ _))).2
    rw [regionGluedMap_of_mem D ec R φ hxR]
    rwa [ec.left_inv (hsrc x hxR)] at h1
  · rw [regionGluedMap_of_notMem D ec R Rc φ hxR, dist_self]
    exact hm

end MetricAmbient

end DifferentialGeometry.Topology.PiecewiseLinear
