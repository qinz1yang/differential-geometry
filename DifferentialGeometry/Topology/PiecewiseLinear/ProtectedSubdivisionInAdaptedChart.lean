/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ProtectedSubdivisionBlocks
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingDoubleCrossing

open Set Topology Metric
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_pos_le_dist_of_disjoint {X : Type*} [MetricSpace X] {s t : Set X}
    (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ d : ℝ, 0 < d ∧ ∀ a ∈ s, ∀ b ∈ t, d ≤ dist a b := by
  obtain ⟨d, hd, hdisj⟩ := hst.exists_thickenings hs ht
  refine ⟨d, hd, fun a ha b hb => ?_⟩
  by_contra hlt
  have h1 : b ∈ thickening d s := mem_thickening_iff.mpr ⟨a, ha, by
    rw [dist_comm]
    exact not_le.mp hlt⟩
  exact Set.disjoint_left.mp hdisj h1 (self_subset_thickening hd t hb)

section MetricAmbient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem isPLOn_regionGluedMap (D : SingularTwoCell M) {V : Set M}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M) (hVs : V ⊆ ec.source)
    (R Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Kc : Set (EuclideanSpace ℝ (Fin 2))} (hRfin : R.faces.Finite) (hRsp : R.space = Rc.space)
    (hRdom : Rc.space ⊆ D.domain) (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hmaps : MapsTo (simplicialMap R φ) Rc.space (⇑ec '' V)) (hΩ : IsOpen Ω)
    (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hKc : IsClosed Kc) (hKcΩ : Kc ⊆ Ω)
    (hgK : ∀ x ∈ D.domain, x ∉ Kc → regionGluedMap D ec R φ Rc x = D x) :
    IsPLOn 2 3 (regionGluedMap D ec R φ Rc) D.domain := by
  have : Finite R.faces := hRfin.to_subtype
  intro x hx
  by_cases hxK : x ∈ Kc
  · have hxΩ : x ∈ Ω := hKcΩ hxK
    have hxR : x ∈ Rc.space := hΩR ⟨hx, hxΩ⟩
    obtain ⟨v, hvV, hveq⟩ := hmaps hxR
    have hpt : simplicialMap R φ x ∈ ec.target := hveq ▸ ec.map_source (hVs hvV)
    have hgx : regionGluedMap D ec R φ Rc x = ec.symm (simplicialMap R φ x) :=
      regionGluedMap_of_mem D ec R φ hxR
    set c := chartAt (EuclideanSpace ℝ (Fin 3)) (regionGluedMap D ec R φ Rc x)
    have hT : ec.symm ≫ₕ c ∈ plGroupoid 3 :=
      StructureGroupoid.compatible_of_mem_maximalAtlas_left hec
    have hTpl := (mem_plGroupoid_iff.mp hT).1
    have hmem : simplicialMap R φ x ∈ (ec.symm ≫ₕ c).source := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      refine ⟨hpt, ?_⟩
      rw [mem_preimage, ← hgx]
      exact mem_chart_source _ _
    have hp : IsPiecewiseAffineWithinAt (simplicialMap R φ) Rc.space x := by
      have h1 := isPiecewiseAffineOn_simplicialMap R φ
      rw [hRsp] at h1
      exact h1 x hxR
    have hcomp := IsPiecewiseAffineWithinAt.comp (f := simplicialMap R φ) (x := x)
      (hTpl _ hmem) hp
    obtain ⟨W₁, hW₁o, hxW₁, hW₁sub⟩ := mem_nhdsWithin.mp
      (hp.continuousWithinAt.preimage_mem_nhdsWithin
        ((ec.symm ≫ₕ c).open_source.mem_nhds hmem))
    have hWo : IsOpen (W₁ ∩ Ω) := hW₁o.inter hΩ
    have hxW : x ∈ W₁ ∩ Ω := ⟨hxW₁, hxΩ⟩
    have hset : (Rc.space ∩ simplicialMap R φ ⁻¹' (ec.symm ≫ₕ c).source) ∩ (W₁ ∩ Ω) =
        D.domain ∩ (W₁ ∩ Ω) := by
      ext y
      constructor
      · rintro ⟨⟨hyR, -⟩, hyW⟩
        exact ⟨hRdom hyR, hyW⟩
      · rintro ⟨hyD, hyW⟩
        have hyR : y ∈ Rc.space := hΩR ⟨hyD, hyW.2⟩
        exact ⟨⟨hyR, hW₁sub ⟨hyW.1, hyR⟩⟩, hyW⟩
    have heq : EqOn (fun y => c (regionGluedMap D ec R φ Rc y))
        ((ec.symm ≫ₕ c) ∘ simplicialMap R φ) (D.domain ∩ (W₁ ∩ Ω)) := by
      rintro y ⟨hyD, hyW⟩
      have hyR : y ∈ Rc.space := hΩR ⟨hyD, hyW.2⟩
      simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans,
        regionGluedMap_of_mem D ec R φ hyR]
    have h1 := hcomp.inter_of_mem_nhds (hWo.mem_nhds hxW)
    rw [hset] at h1
    have hprop : IsPiecewiseAffineWithinAt (fun y => c (regionGluedMap D ec R φ Rc y))
        D.domain x := (h1.congr heq).of_inter_of_mem_nhds (hWo.mem_nhds hxW)
    have hcont : ContinuousWithinAt (regionGluedMap D ec R φ Rc) D.domain x := by
      have h3 : ContinuousWithinAt (simplicialMap R φ) D.domain x := by
        rw [← continuousWithinAt_inter (hΩ.mem_nhds hxΩ)]
        exact hp.continuousWithinAt.mono fun y hy => hΩR hy
      have h2 : ContinuousWithinAt (fun y => ec.symm (simplicialMap R φ y)) D.domain x :=
        (ec.continuousAt_symm hpt).comp_continuousWithinAt h3
      refine h2.congr_of_eventuallyEq ?_ hgx
      filter_upwards [inter_mem_nhdsWithin D.domain (hΩ.mem_nhds hxΩ)] with y hy
      exact regionGluedMap_of_mem D ec R φ (hΩR hy)
    exact ⟨hcont, hprop⟩
  · have hW : IsOpen Kcᶜ := hKc.isOpen_compl
    obtain ⟨hcont, hpl⟩ := D.isPLOn x hx
    have hcoord : IsPiecewiseAffineWithinAt
        (⇑(chartAt (EuclideanSpace ℝ (Fin 3)) (D x)) ∘ ⇑D) D.domain x := hpl
    have hgx : regionGluedMap D ec R φ Rc x = D x := hgK x hx hxK
    have heq : EqOn (fun y => chartAt (EuclideanSpace ℝ (Fin 3)) (D x)
        (regionGluedMap D ec R φ Rc y))
        (⇑(chartAt (EuclideanSpace ℝ (Fin 3)) (D x)) ∘ ⇑D) (D.domain ∩ Kcᶜ) := by
      rintro y ⟨hyD, hyK⟩
      simp only [Function.comp_apply, hgK y hyD hyK]
    have hprop := ((hcoord.inter_of_mem_nhds (hW.mem_nhds hxK)).congr heq).of_inter_of_mem_nhds
      (hW.mem_nhds hxK)
    have hcont' : ContinuousWithinAt (regionGluedMap D ec R φ Rc) D.domain x := by
      refine hcont.congr_of_eventuallyEq ?_ hgx
      filter_upwards [inter_mem_nhdsWithin D.domain (hW.mem_nhds hxK)] with y hy
      exact hgK y hy.1 hy.2
    refine ⟨hcont', ?_⟩
    rw [hgx]
    exact hprop

theorem exists_pos_hasStableCrossingBlocks_regionGluedMap (D : SingularTwoCell M)
    {BdM C Z V W : Set M} {η κ δ τS : ℝ}
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C) (hZclosed : IsClosed Z)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hVs : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))} (hsub : IsSubdivision R Rc) (hRfin : R.faces.Finite)
    (hlinear : ∀ s ∈ R.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
      EqOn (fun x => ec (D x)) A (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2)))))
    (hAR : Ac.faces ⊆ Rc.faces) (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hΩ : IsOpen Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (hstable : HasStableCrossingBlocks (⇑D) D.domain ec ℓ BdM (Z ∩ closure (V \ closure W)) η)
    (T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (hκ : 0 < κ) (hδ : 0 < δ)
    (hcert : ∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
      StarInj T g → UniformInjectivityScale D.domain g κ ∧
        ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2)
    (hτS : 0 < τS)
    (hgood : ∀ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
      (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
      AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τS →
        StarInj T (regionGluedMap D ec R φ Rc) ∧
          MapsTo (simplicialMap R φ) Rc.space (⇑ec '' V) ∧
          (∀ x ∈ Rc.space, dist (ec.symm (simplicialMap R φ x)) (D x) < δ) ∧
          (∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap R φ x)) ∧
          ∀ x ∈ Rc.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ Lc.space) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ τS ∧ ∀ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
      (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
      AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ →
        HasStableCrossingBlocks (regionGluedMap D ec R φ Rc) D.domain ec ℓ BdM
          (Z ∩ closure (V \ closure W)) (η / 2) := by
  classical
  have : Finite R.faces := hRfin.to_subtype
  have hQ'c : IsClosed (Z ∩ closure (V \ closure W)) := hZclosed.inter isClosed_closure
  obtain ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb, hcov, hblk⟩ := hstable
  have hRsp : R.space = Rc.space := hsub.space_eq
  have hRcomp : IsCompact Rc.space := hRsp ▸ (isPolyhedron_space R).isCompact
  have hKcΩ : closure (Rc.space \ Ac.space) ⊆ Ω :=
    closure_sdiff_subset_of_frontier_cover hRcomp.isClosed hNb hNbfr hNbA
  have hS : IsCompact D.domain := D.isPLBall_domain.isPolyhedron.isCompact
  have hsrc : ∀ x ∈ Rc.space, D x ∈ ec.source := fun x hx => hVs (hRV hx)
  have hlin' : ∀ x ∈ Rc.space, simplicialMap R (fun v => ec (D v)) x = ec (D x) := fun x hx =>
    simplicialMap_eq_of_affine_faces R hlinear (hRsp ▸ hx)
  have hK₀ : IsCompact (doublePointSet (⇑D) D.domain ∩ (Z ∩ closure (V \ closure W))) :=
    (D.isCompact_doublePointSet hloc).inter_right hQ'c
  choose A' r' tlo' O hOo hyO hOs hOin ε₀ hε₀ lam₀ hlam₀ hmain using
    fun (y : M) (hy : y ∈ doublePointSet (⇑D) D.domain ∩ (Z ∩ closure (V \ closure W))) =>
      (hblk (Classical.choose (mem_iUnion.mp (hcov hy)))).exists_regional_perturbation hBdchart
        hy.1 (Classical.choose_spec (mem_iUnion.mp (hcov hy))) hΩ isClosed_closure hKcΩ
  obtain ⟨t, ht⟩ := hK₀.elim_finite_subcover
    (fun p : ↥(doublePointSet (⇑D) D.domain ∩ (Z ∩ closure (V \ closure W))) => O p p.2)
    (fun p => hOo p p.2) (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hyO y hy⟩)
  have hOu : IsOpen (⋃ p ∈ t, O p p.2) := isOpen_biUnion fun p _ => hOo p p.2
  obtain ⟨m₀, hm₀, hΦ⟩ := exists_pos_doublePointSet_inter_subset hS D.continuousOn hκ hQ'c hOu ht
  obtain ⟨e₁, he₁, he₁le⟩ :=
    Finset.exists_pos_forall_le_of_pos t (fun p => ε₀ p p.2) fun p _ => hε₀ p p.2
  obtain ⟨e₂, he₂, he₂le⟩ :=
    Finset.exists_pos_forall_le_of_pos t (fun p => lam₀ p p.2) fun p _ => hlam₀ p p.2
  obtain ⟨Vs, Λ, hΛ, -, hdisp⟩ := exists_vertex_displacement_lipschitz R hRfin
  have hK₁ : IsCompact (⇑ec '' (⇑D '' Rc.space)) :=
    (hRcomp.image_of_continuousOn (D.continuousOn.mono hRdom)).image_of_continuousOn
      (ec.continuousOn.mono fun _ ⟨x, hx, hxy⟩ => hxy ▸ hsrc x hx)
  have hK₁t : ⇑ec '' (⇑D '' Rc.space) ⊆ ec.target := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ec.map_source (hsrc x hx)
  obtain ⟨τ₁, hτ₁, hτ₁'⟩ := OpenPartialHomeomorph.exists_pos_dist_symm_lt ec hK₁ hK₁t hm₀
  have hΛ1 : 0 < Λ + 1 := by linarith
  refine ⟨min (min τS e₁) (min (e₂ / (Λ + 1)) τ₁),
    lt_min (lt_min hτS he₁) (lt_min (div_pos he₂ hΛ1) hτ₁),
    (min_le_left _ _).trans (min_le_left _ _), fun Bv φ hadm => ?_⟩
  set τ := min (min τS e₁) (min (e₂ / (Λ + 1)) τ₁) with hτdef
  have hττS : τ ≤ τS := (min_le_left _ _).trans (min_le_left _ _)
  have hτe₁ : τ ≤ e₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hτe₂ : τ ≤ e₂ / (Λ + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hττ₁ : τ ≤ τ₁ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨hstarg, hmaps, hdistδ, hℓ0, hℓL⟩ := hgood Bv φ (hadm.mono hττS)
  have hclose : ∀ x ∈ Rc.space, dist (simplicialMap R φ x) (ec (D x)) < τ := by
    intro x hx
    rw [← hlin' x hx]
    exact dist_simplicialMap_lt_of_dist_vertices_lt R hadm.2.2.1 (hRsp ▸ hx)
  have hgRc : ∀ x ∈ Rc.space, regionGluedMap D ec R φ Rc x ∈ V ∧
      ec (regionGluedMap D ec R φ Rc x) = simplicialMap R φ x := fun x hx =>
    regionGluedMap_chart_of_mem D ec hVs R Rc φ hmaps hx
  have hgout : ∀ x ∉ Rc.space, regionGluedMap D ec R φ Rc x = D x := fun x hx =>
    regionGluedMap_of_notMem D ec R Rc φ hx
  have hgδ : ∀ x ∈ D.domain, dist (regionGluedMap D ec R φ Rc x) (D x) < δ := by
    intro x _
    by_cases hxR : x ∈ Rc.space
    · rw [regionGluedMap_of_mem D ec R φ hxR]
      exact hdistδ x hxR
    · rw [hgout x hxR, dist_self]
      exact hδ
  have huis := (hcert _ hgδ hstarg).1
  have hgm : ∀ x ∈ D.domain, dist (regionGluedMap D ec R φ Rc x) (D x) < m₀ := by
    intro x _
    by_cases hxR : x ∈ Rc.space
    · have hk : ec (D x) ∈ ⇑ec '' (⇑D '' Rc.space) :=
        mem_image_of_mem ec (mem_image_of_mem D hxR)
      have h1 := (hτ₁' _ hk _ ((hclose x hxR).trans_le hττ₁)).2
      rw [regionGluedMap_of_mem D ec R φ hxR]
      rwa [ec.left_inv (hsrc x hxR)] at h1
    · rw [hgout x hxR, dist_self]
      exact hm₀
  have hDP := hΦ _ hgm huis
  obtain ⟨δφ, lam, hδpl, hδL, hlamΛ, hδeq⟩ := hdisp φ (fun v => ec (D v)) τ hadm.2.2.1
  have hΛτ : Λ * τ ≤ e₂ := by
    have h2 : Λ * τ ≤ Λ * (e₂ / (Λ + 1)) := mul_le_mul_of_nonneg_left hτe₂ hΛ
    have h3 : Λ * (e₂ / (Λ + 1)) ≤ e₂ := by
      rw [mul_div_assoc', div_le_iff₀ hΛ1]
      nlinarith
    linarith
  have hlam : ∀ p ∈ t, (lam : ℝ) ≤ lam₀ p p.2 := fun p hp =>
    hlamΛ.trans (hΛτ.trans (he₂le p hp))
  have hEqA : ∀ x ∈ Ac.space, simplicialMap R φ x = ec (D x) := by
    intro x hx
    have hxR : x ∈ Rc.space := by
      obtain ⟨t', ht', hxt⟩ := Ac.mem_space_iff.mp hx
      exact Rc.convexHull_subset_space (hAR ht') hxt
    rw [hsub.simplicialMap_eqOn_of_eqOn_vertices hAR (ψ := fun v => ec (D v))
      (fun v hv hvA => hadm.2.2.2.1 v hv hvA) hx]
    exact hlin' x hxR
  have hgK : ∀ x ∈ D.domain, x ∉ closure (Rc.space \ Ac.space) →
      regionGluedMap D ec R φ Rc x = D x := by
    intro x _ hxK
    by_cases hxR : x ∈ Rc.space
    · have hxA : x ∈ Ac.space := by
        by_contra hxA
        exact hxK (subset_closure ⟨hxR, hxA⟩)
      rw [regionGluedMap_of_mem D ec R φ hxR, hEqA x hxA, ec.left_inv (hsrc x hxR)]
    · exact hgout x hxR
  have hgΩ : ∀ x ∈ D.domain, x ∈ Ω → regionGluedMap D ec R φ Rc x ∈ ec.source ∧
      ec (regionGluedMap D ec R φ Rc x) = ec (D x) + δφ x := by
    intro x hxD hxΩ
    have hxR : x ∈ Rc.space := hΩR ⟨hxD, hxΩ⟩
    obtain ⟨hgV, hgeq⟩ := hgRc x hxR
    refine ⟨hVs hgV, ?_⟩
    rw [hgeq, hδeq x (hRsp ▸ hxR), hlin' x hxR, add_sub_cancel]
  have hG1 : ∀ x ∈ D.domain, regionGluedMap D ec R φ Rc x ∈ ec.source →
      D x ∈ ec.source ∧ ‖ec (regionGluedMap D ec R φ Rc x) - ec (D x)‖ ≤ e₁ := by
    intro x _ hgs
    by_cases hxR : x ∈ Rc.space
    · refine ⟨hsrc x hxR, ?_⟩
      rw [(hgRc x hxR).2, ← dist_eq_norm]
      exact (hclose x hxR).le.trans hτe₁
    · rw [hgout x hxR] at hgs ⊢
      refine ⟨hgs, ?_⟩
      rw [sub_self, norm_zero]
      exact he₁.le
  have hfC : ∀ x ∈ D.domain, D x ∈ ec.source → 0 ≤ ℓ (ec (D x)) := fun x hx hs =>
    (hCchart _ hs).mp (hmapC hx)
  have hg4 : ∀ x ∈ D.domain, regionGluedMap D ec R φ Rc x ∈ ec.source →
      0 ≤ ℓ (ec (regionGluedMap D ec R φ Rc x)) ∧
        (x ∈ frontier D.domain ↔ ℓ (ec (regionGluedMap D ec R φ Rc x)) = 0) := by
    intro x hxD hgs
    by_cases hxR : x ∈ Rc.space
    · rw [(hgRc x hxR).2]
      refine ⟨hℓ0 x hxR, ?_⟩
      rw [hℓL x hxR, hLspace]
      exact ⟨fun h => ⟨hxR, h⟩, fun h => h.2⟩
    · rw [hgout x hxR] at hgs ⊢
      refine ⟨hfC x hxD hgs, ?_⟩
      rw [← hBdchart _ hgs]
      constructor
      · intro hfr
        have hmem : x ∈ D.domain ∩ ⇑D ⁻¹' BdM := by
          rw [hproper]
          exact hfr
        exact hmem.2
      · intro hB
        have hmem : x ∈ D.domain ∩ ⇑D ⁻¹' BdM := ⟨hxD, hB⟩
        rw [hproper] at hmem
        exact hmem
  have hblocks : ∀ p ∈ t, ∃ (SA' SB' : Set (EuclideanSpace ℝ (Fin 2))) (a' b' : ℝ × ℝ → ℝ)
      (La' Lb' : ℝ), IsStableCrossingBlock (regionGluedMap D ec R φ Rc) D.domain ec ℓ BdM
        (A' p p.2) (r' p p.2) (tlo' p p.2) SA' SB' a' b' La' Lb' (η / 2) := fun p hp =>
    hmain p p.2 _ δφ lam (hlam p hp) hδpl hδL
      (fun x hx hgs => ⟨(hG1 x hx hgs).1, (hG1 x hx hgs).2.trans (he₁le p hp)⟩) hfC hgΩ hgK hg4
  choose! SA' SB' a' b' La' Lb' hblk' using hblocks
  refine hasStableCrossingBlocks_of_finset (half_pos hη) t (fun p => A' p p.2)
    (fun p => r' p p.2) (fun p => tlo' p p.2) SA' SB' a' b' La' Lb' ?_ hblk'
  intro y hy
  obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (hDP hy)
  refine mem_iUnion₂.mpr ⟨p, hp, hOin p p.2 y hyp ?_⟩
  obtain ⟨⟨x, hx, -, -, -, hgx, -⟩, -⟩ := hy
  have hys : y ∈ ec.source := hOs p p.2 hyp
  rw [← hgx] at hys ⊢
  exact (hg4 x hx hys).1

open Classical in
theorem exists_protectedSubdivision_in_adaptedChart [CompactSpace M]
    (D : SingularTwoCell M) {BdM C Z O W V : Set M} {η κ δ ε : ℝ}
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (hnormal : ∀ y ∈ doublePointSet (⇑D) D.domain ∩ O,
      ∃ e₀ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₀.source ∧
        HasPLNormalDoubleCrossingAt (e₀ ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e₀.source)
          (e₀ '' (e₀.source ∩ BdM)) (e₀ y))
    (hZclosed : IsClosed Z) (hOopen : IsOpen O) (hZO : Z ⊆ O)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hℓ : ℓ ≠ 0) (hVopen : IsOpen V) (hVec : closure V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hLR : Lc.faces ⊆ Rc.faces) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hΩ : IsOpen Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (hWV : closure W ⊆ V) (hAfree : Disjoint Ac.space (⇑D ⁻¹' closure W))
    (hstable : HasStableCrossingBlocks (⇑D) D.domain ec ℓ BdM
      (Z ∩ closure (V \ closure W)) η)
    (T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (hTfin : T.faces.Finite)
    (hTspace : T.space = D.domain) (hTstar : StarInj T (⇑D))
    (hκ : 0 < κ) (hδ : 0 < δ) (hε : 0 < ε)
    (hcert : ∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
      StarInj T g → UniformInjectivityScale D.domain g κ ∧
        ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2)
    (hconv : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → z ∈ ⇑ec '' V ∧ dist (ec.symm z) (D x) < δ) :
    ∃ (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (τ : ℝ) (K : Set M),
      0 < τ ∧ IsSubdivision R Rc ∧ R.faces.Finite ∧
        (∀ s ∈ R.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
          EqOn (fun x => ec (D x)) A
            (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2))))) ∧
        IsCompact K ∧ K ⊆ V ∧ ⇑D '' Rc.space ⊆ interior K ∧
        ∀ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
          (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
          AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ →
          IsPiecewiseAffineOn (simplicialMap R φ) Rc.space ∧
            (∀ x ∈ Rc.space, dist (simplicialMap R φ x) (ec (D x)) < ε) ∧
            EqOn (simplicialMap R φ) (fun x => ec (D x)) Ac.space ∧
            (∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap R φ x)) ∧
            (∀ x ∈ Rc.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ Lc.space) ∧
            (∀ σ ∈ R.faces, (∃ v ∈ σ, v ∈ Ac.space) →
              Disjoint
                (simplicialMap R φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))
                (⇑ec '' closure W)) ∧
            MapsTo (simplicialMap R φ) Rc.space (⇑ec '' V) ∧
            regionGluedMap D ec R φ Rc '' Rc.space ⊆ K ∧
            StarInj T (regionGluedMap D ec R φ Rc) ∧
            (∀ y ∈ doublePointSet (regionGluedMap D ec R φ Rc) D.domain ∩ Z ∩ K,
              (∃ σ ∈ R.faces, (∃ v ∈ σ, v ∈ Ac.space) ∧
                  (D.domain ∩ regionGluedMap D ec R φ Rc ⁻¹' {y} ∩
                    convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))).Nonempty) →
                ∃ e₁ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₁.source ∧
                  HasPLNormalDoubleCrossingAt (⇑e₁ ∘ regionGluedMap D ec R φ Rc)
                    (D.domain ∩ regionGluedMap D ec R φ Rc ⁻¹' e₁.source)
                    (⇑e₁ '' (e₁.source ∩ BdM)) (e₁ y)) ∧
            HasStableCrossingBlocks (regionGluedMap D ec R φ Rc) D.domain ec ℓ BdM
              (Z ∩ closure (V \ closure W)) (η / 2) := by
  let _ := hfiber
  let _ := hnormal
  let _ := hOopen
  let _ := hZO
  let _ := hRman
  let _ := hLR
  have hVs : V ⊆ ec.source := subset_closure.trans hVec
  have hRsrc : Rc.space ⊆ ⇑D ⁻¹' ec.source := fun x hx => hVs (hRV hx)
  have : Finite Rc.faces := hRfin.to_subtype
  have : Finite Ac.faces := (hRfin.subset hAR).to_subtype
  have hWc : IsCompact (closure W) := isClosed_closure.isCompact
  have hWs : closure W ⊆ ec.source := hWV.trans (subset_closure.trans hVec)
  have hAR' : Ac.space ⊆ Rc.space := space_mono_of_faces_subset hAR
  have hKA : IsCompact (⇑ec '' (⇑D '' Ac.space)) :=
    ((isPolyhedron_space Ac).isCompact.image_of_continuousOn
      (D.continuousOn.mono (hAR'.trans hRdom))).image_of_continuousOn
      (ec.continuousOn.mono fun _ ⟨x, hx, hxy⟩ => hxy ▸ hRsrc (hAR' hx))
  have hKW : IsClosed (⇑ec '' closure W) :=
    (hWc.image_of_continuousOn (ec.continuousOn.mono hWs)).isClosed
  have hdisj : Disjoint (⇑ec '' (⇑D '' Ac.space)) (⇑ec '' closure W) := by
    rw [Set.disjoint_left]
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ ⟨w, hw, hwa⟩
    have h1 : w = D a := ec.injOn (hWs hw) (hRsrc (hAR' ha)) hwa
    exact Set.disjoint_left.mp hAfree ha (show D a ∈ closure W by rw [← h1]; exact hw)
  obtain ⟨d₀, hd₀, hd₀'⟩ := exists_pos_le_dist_of_disjoint hKA hKW hdisj
  have hd₀A : ∀ a ∈ Ac.space, ∀ w ∈ closure W, d₀ ≤ dist (ec (D a)) (ec w) :=
    fun a ha w hw => hd₀' _ (mem_image_of_mem ec (mem_image_of_mem D ha)) _
      (mem_image_of_mem ec hw)
  obtain ⟨R, hsub, hRfin', hlinear, hinjR, hmesh⟩ :=
    exists_isSubdivision_affine_injOn_closedStar_mesh D hloc hec Rc hRfin hRdom hRsrc
      (half_pos hd₀)
  have hL : IsCompact (⇑D '' Rc.space) :=
    (isPolyhedron_space Rc).isCompact.image_of_continuousOn (D.continuousOn.mono hRdom)
  obtain ⟨ρ, hρ, -, hKc, hKV, hKint⟩ := exists_pos_cthickening_chart_nhds ec hVopen hVs hL
    (by rintro _ ⟨x, hx, rfl⟩; exact hRV hx)
  have hconvV : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → z ∈ ⇑ec '' V := fun x hx z hz => (hconv x hx z hz).1
  obtain ⟨τb, hτb, hstar⟩ := exists_pos_starInj_regionGluedMap D hloc ec ℓ hVs Rc Lc Ac R hsub
    hRfin' hlinear hAR hRdom hRV hinjR hΩ hΩR hNb hNbfr hNbA T hTfin hTspace hTstar hε hconvV
  have hτa : 0 < min (d₀ / 2) (min ε ρ) := lt_min (half_pos hd₀) (lt_min hε hρ)
  have hτS : 0 < min (min (d₀ / 2) (min ε ρ)) τb := lt_min hτa hτb
  have hle1 : ∀ {τ : ℝ}, τ ≤ min (d₀ / 2) (min ε ρ) → τ ≤ d₀ / 2 := fun h =>
    h.trans (min_le_left _ _)
  have hle2 : ∀ {τ : ℝ}, τ ≤ min (d₀ / 2) (min ε ρ) → τ ≤ ε := fun h =>
    h.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hle3 : ∀ {τ : ℝ}, τ ≤ min (d₀ / 2) (min ε ρ) → τ ≤ ρ := fun h =>
    h.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hSa : min (min (d₀ / 2) (min ε ρ)) τb ≤ min (d₀ / 2) (min ε ρ) := min_le_left _ _
  obtain ⟨τd, hτd, hτdS, hpersist⟩ := exists_pos_hasStableCrossingBlocks_regionGluedMap D hloc
    hproper hmapC hZclosed ec ℓ hVs hCchart hBdchart Rc Lc Ac R hsub hRfin' hlinear hAR hRdom
    hRV hLspace hΩ hΩR hNb hNbfr hNbA hstable T hκ hδ hcert hτS fun Bv φ hadm => by
      obtain ⟨-, c2, -, c4, c5, -, c7, -⟩ := admissibleVertexMap_region_clauses D hproper hmapC
        ec ℓ hVs hCchart hBdchart Rc Lc Ac R hsub hRfin' hlinear hAR hRdom hRV hLspace hd₀A
        hmesh (hle1 hSa) (hle2 hSa) hconvV (hle3 hSa) subset_rfl hadm
      exact ⟨hstar Bv φ (hadm.mono (min_le_right _ _)), c7,
        fun x hx => (hconv x hx _ ((c2 x hx).trans_le (hle2 hSa))).2, c4, c5⟩
  have hτda : τd ≤ min (d₀ / 2) (min ε ρ) := hτdS.trans hSa
  refine ⟨R, τd, ec.symm '' cthickening ρ (⇑ec '' (⇑D '' Rc.space)), hτd, hsub, hRfin', hlinear,
    hKc, hKV, hKint, fun Bv φ hadm => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := admissibleVertexMap_region_clauses D hproper hmapC
    ec ℓ hVs hCchart hBdchart Rc Lc Ac R hsub hRfin' hlinear hAR hRdom hRV hLspace hd₀A hmesh
    (hle1 hτda) (hle2 hτda) hconvV (hle3 hτda) subset_rfl hadm
  have hst := hstar Bv φ (hadm.mono (hτdS.trans (min_le_right _ _)))
  have hpers := hpersist Bv φ hadm
  have hRsp : R.space = Rc.space := hsub.space_eq
  have hKcΩ : closure (Rc.space \ Ac.space) ⊆ Ω :=
    closure_sdiff_subset_of_frontier_cover (hRsp ▸ (isPolyhedron_space Rc).isCompact.isClosed)
      hNb hNbfr hNbA
  have hgK : ∀ x ∈ D.domain, x ∉ closure (Rc.space \ Ac.space) →
      regionGluedMap D ec R φ Rc x = D x := by
    intro x _ hxK
    by_cases hxR : x ∈ Rc.space
    · have hxA : x ∈ Ac.space := by
        by_contra hxA
        exact hxK (subset_closure ⟨hxR, hxA⟩)
      rw [regionGluedMap_of_mem D ec R φ hxR, c3 hxA, ec.left_inv (hRsrc hxR)]
    · exact regionGluedMap_of_notMem D ec R Rc φ hxR
  refine ⟨c1, fun x hx => (c2 x hx).trans_le (hle2 hτda), c3, c4, c5, c6, c7, c8, hst, ?_, hpers⟩
  rintro y ⟨⟨hyDP, hyZ⟩, hyK⟩ ⟨σ, hσ, ⟨v, hvσ, hvA⟩, x, ⟨hxD, hxy⟩, hxσ⟩
  have hxR : x ∈ Rc.space := hRsp ▸ R.convexHull_subset_space hσ hxσ
  have hgx : regionGluedMap D ec R φ Rc x = y := hxy
  have hecy : ec y = simplicialMap R φ x := by
    rw [← hgx]
    exact (regionGluedMap_chart_of_mem D ec hVs R Rc φ c7 hxR).2
  have hyW : y ∉ closure W := by
    intro hyW
    exact Set.disjoint_left.mp (c6 σ hσ ⟨v, hvσ, hvA⟩) ⟨x, hxσ, rfl⟩ ⟨y, hyW, hecy⟩
  have hyQ : y ∈ Z ∩ closure (V \ closure W) := ⟨hyZ, subset_closure ⟨hKV hyK, hyW⟩⟩
  obtain ⟨-, m, A, r, tlo, SA, SB, a, b, La, Lb, hcov, hblk⟩ := hpers
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov ⟨hyDP, hyQ⟩)
  let D' : SingularTwoCell M :=
    { domain := D.domain
      isPLBall_domain := D.isPLBall_domain
      toFun := regionGluedMap D ec R φ Rc
      isPLOn := isPLOn_regionGluedMap D hec hVs R Rc hRfin' hRsp hRdom φ c7 hΩ hΩR
        isClosed_closure hKcΩ hgK }
  exact hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock D' ec ℓ hec hℓ hBdchart (hblk i)
    hyDP hi

end MetricAmbient

end DifferentialGeometry.Topology.PiecewiseLinear
