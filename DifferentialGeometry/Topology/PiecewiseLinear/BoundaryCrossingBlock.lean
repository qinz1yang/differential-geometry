/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleCrossingBlock
import DifferentialGeometry.Topology.PiecewiseLinear.EdgeSideCoordinates

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
theorem exists_boundaryEdgeSheet
    {R Ac Lc Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {S : Set (EuclideanSpace ℝ (Fin 2))} (hℓ : ℓ ≠ 0)
    (hsub : IsSubdivision R Rc) (hRsfin : R.faces.Finite) (hRS : Rc.space ⊆ S)
    (hLspace : Lc.space = Rc.space ∩ frontier S)
    (hBvL : ∀ v ∈ R.vertices, v ∈ Bv ↔ v ∈ Lc.space)
    (hpzero : ∀ x ∈ Rc.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ Lc.space)
    (hpnn : ∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap R φ x))
    (hguard : ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
      (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
        (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
        AffineIndependent ℝ
          (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
        AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))))
    (hSball : closure (interior S) = S) {σ : Finset (EuclideanSpace ℝ (Fin 2))}
    {x : EuclideanSpace ℝ (Fin 2)} (hσ : σ ∈ R.faces) (h2 : σ.card = 2) (hσB : σ ⊆ Bv)
    (hx : x ∈ openSimplex σ) (hRnb : R.space ∈ 𝓝[S] x)
    (hfree : ∀ τ ∈ R.faces, x ∈ convexHull ℝ (τ : Set (EuclideanSpace ℝ (Fin 2))) →
      ∀ v ∈ τ, v ∉ Ac.space) :
    ∃ (c : EuclideanSpace ℝ (Fin 2)) (A' : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
      (ε : ℝ), c ∉ σ ∧ insert c σ ∈ R.faces ∧
      EqOn (simplicialMap R φ) A' (convexHull ℝ ((insert c σ : Finset _) :
        Set (EuclideanSpace ℝ (Fin 2)))) ∧
      Function.Injective A'.linear ∧ 0 < ε ∧
      (∀ z ∈ ball x ε, z ∈ S ↔ 0 ≤ ℓ (A'.linear (z - x))) ∧
      (∀ z ∈ ball x ε, z ∈ S → z ∈ convexHull ℝ ((insert c σ : Finset _) :
        Set (EuclideanSpace ℝ (Fin 2)))) ∧
      (∀ ζ, ℓ (A'.linear ζ) = 0 → ζ ∈ vectorSpan ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      0 < ℓ (φ c) := by
  have : Finite R.faces := hRsfin.to_subtype
  have hhull : ∀ {τ : Finset (EuclideanSpace ℝ (Fin 2))}, τ ∈ R.faces →
      ∀ z ∈ convexHull ℝ (τ : Set (EuclideanSpace ℝ (Fin 2))), z ∈ Rc.space :=
    fun hτ z hz => hsub.space_eq ▸ R.convexHull_subset_space hτ hz
  have hxh := openSimplex_subset_convexHull σ hx
  have hxL : x ∈ Lc.space :=
    convexHull_subset_of_subset_boundaryVertices hsub hBvL hpzero hσ hσB hxh
  have hxfr : x ∈ frontier S := by
    rw [hLspace] at hxL
    exact hxL.2
  have hxcl : x ∈ closure (interior S) := by
    rw [hSball]
    exact hRS (hhull hσ x hxh)
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
  obtain ⟨c, hc, hτ⟩ := exists_insert_mem_faces_of_mem_closure_interior R hσ h2 hx hRnb hxcl
  obtain ⟨A', hA'⟩ := exists_affineMap_eqOn_simplicialMap R φ hτ
  have hxτ : x ∈ convexHull ℝ (((insert c ({a, b} : Finset _)) : Finset _) :
      Set (EuclideanSpace ℝ (Fin 2))) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _)) hxh
  have hvφ : ∀ v ∈ insert c ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))), A' v = φ v := by
    intro v hv
    rw [← hA' (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))]
    exact simplicialMap_vertex R φ
      (R.down_closed hτ (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  have hcard3 : (insert c ({a, b} : Finset (EuclideanSpace ℝ (Fin 2)))).card = 3 := by
    rw [Finset.card_insert_of_notMem hc, Finset.card_pair hab]
  have hind : AffineIndependent ℝ
      (fun v : (insert c ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) : Finset _) =>
        φ (v : EuclideanSpace ℝ (Fin 2))) := by
    refine affineIndependent_of_wallGuard hℓ hguard ?_ (by omega)
      ((Finset.card_le_card Finset.inter_subset_left).trans hcard3.le) (hfree _ hτ hxτ)
    intro v hv
    exact R.down_closed hτ (Finset.singleton_subset_iff.mpr (Finset.mem_coe.mp hv))
      (Finset.singleton_nonempty v)
  have hind' : AffineIndependent ℝ
      (fun v : (insert c ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) ∪
        insert c ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) : Finset _) =>
        φ (v : EuclideanSpace ℝ (Fin 2))) := by
    rw [Finset.union_self]
    exact hind
  have hint : interior (convexHull ℝ (((insert c ({a, b} : Finset _)) : Finset _) :
      Set (EuclideanSpace ℝ (Fin 2)))) = openSimplex (insert c ({a, b} : Finset _)) :=
    interior_convexHull_eq_openSimplex (R.indep hτ) (by rw [hcard3, finrank_euclideanSpace_fin])
  have hL : Function.Injective A'.linear := by
    refine linear_injective_of_injOn_of_interior_nonempty (C := convexHull ℝ
      (((insert c ({a, b} : Finset _)) : Finset _) : Set (EuclideanSpace ℝ (Fin 2)))) ?_
      ⟨(insert c ({a, b} : Finset (EuclideanSpace ℝ (Fin 2)))).centroid ℝ id, by
        rw [hint]; exact centroid_mem_openSimplex (R.nonempty_of_mem_faces hτ)⟩
    intro z hz z' hz' h
    exact eq_of_simplicialMap_eq_of_affineIndependent R φ hτ hτ hz hz' hind'
      (by rw [hA' hz, hA' hz', h])
  let f : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ := ℓ.comp A'.linear
  have hf : ∀ ζ, f ζ = ℓ (A'.linear ζ) := fun _ => rfl
  have hAx : ℓ (A' x) = 0 := by
    rw [← hA' hxτ]
    exact (hpzero x (hhull hσ x hxh)).mpr hxL
  have hlin : ∀ v, f (v - x) = ℓ (A' v) := by
    intro v
    have h := A'.linearMap_vsub v x
    rw [vsub_eq_sub, vsub_eq_sub] at h
    rw [hf, h, map_sub, hAx, sub_zero]
  have hBv0 : ∀ v ∈ ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))), ℓ (φ v) = 0 := by
    intro v hv
    have hvV : v ∈ R.vertices :=
      R.down_closed hσ (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hvL := (hBvL v hvV).mp (hσB hv)
    rw [← simplicialMap_vertex R φ hvV]
    exact (hpzero v (hhull hσ v (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)))).mpr hvL
  have hfσ : ∀ v ∈ ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))), f (v - x) = 0 := by
    intro v hv
    rw [hlin, hvφ v (Finset.mem_insert_of_mem hv), hBv0 v hv]
  have hcB : c ∉ Bv := by
    intro hcB
    refine not_subset_boundaryVertices_of_card_eq_three hsub hRS hLspace hBvL hpzero hτ hcard3 ?_
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hcB
    · exact hσB hv
  have hℓc : 0 < ℓ (φ c) := by
    have hcV : c ∈ R.vertices :=
      R.down_closed hτ (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self c _))
        (Finset.singleton_nonempty c)
    have hcRc : c ∈ Rc.space := hhull hτ c (subset_convexHull ℝ _ (Finset.mem_coe.mpr
      (Finset.mem_insert_self c _)))
    rw [← simplicialMap_vertex R φ hcV]
    refine lt_of_le_of_ne (hpnn c hcRc) fun h => hcB ?_
    exact (hBvL c hcV).mpr ((hpzero c hcRc).mp h.symm)
  have hfc : f (c - x) = ℓ (φ c) := by rw [hlin, hvφ c (Finset.mem_insert_self c _)]
  obtain ⟨G, θ, -, -, -, -, hdec, hkerG, -, -, -⟩ := exists_edgeSideCoordinates R hab hx hc hτ
  have hfe : f (b - a) = 0 := by
    have h : b - a = (b - x) - (a - x) := by abel
    rw [h, map_sub, hfσ b (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)),
      hfσ a (Finset.mem_insert_self a {b}), sub_zero]
  have hker : ∀ ζ, f ζ = 0 → ζ ∈ vectorSpan ℝ
      (((({a, b} : Finset (EuclideanSpace ℝ (Fin 2)))) : Set (EuclideanSpace ℝ (Fin 2)))) := by
    intro ζ hζ
    apply hkerG
    have h := congrArg f (hdec ζ)
    rw [map_add, map_smul, map_smul, hfe, hfc, smul_zero, zero_add, smul_eq_mul, hζ] at h
    rcases mul_eq_zero.mp h.symm with h0 | h0
    · exact h0
    · exact absurd h0 hℓc.ne'
  obtain ⟨ε₀, hε₀, hb₀⟩ := exists_pos_forall_mem_ball_mem_convexHull_insert (R.indep hτ) hx hc
    f hker (by rw [hfc]; exact hℓc.ne')
  have hside : ∀ c', c' ∉ ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) →
      insert c' ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) ∈ R.faces → 0 < f (c' - x) := by
    intro c' hc' hτ'
    rcases lt_trichotomy (f (c' - x)) 0 with hneg | hzero | hpos
    · exfalso
      obtain ⟨ε', hε', hb'⟩ := exists_pos_forall_mem_ball_mem_convexHull_insert (R.indep hτ') hx
        hc' f hker hneg.ne
      have hsubS : ball x (min ε₀ ε') ⊆ S := by
        intro z hz
        rcases le_or_gt 0 (f (z - x)) with h | h
        · exact hRS (hhull hτ z (hb₀ z (ball_subset_ball (min_le_left _ _) hz)
            (by rw [hfc]; exact mul_nonneg h hℓc.le)))
        · exact hRS (hhull hτ' z (hb' z (ball_subset_ball (min_le_right _ _) hz) (by nlinarith)))
      have hxint : x ∈ interior S :=
        mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨_, lt_min hε₀ hε', hsubS⟩)
      exact hxfr.2 hxint
    · exfalso
      obtain ⟨G', θ', -, -, -, hG', -, -, -, -, hGc'⟩ := exists_edgeSideCoordinates R hab hx hc' hτ'
      have hmem := hker _ hzero
      rw [Finset.coe_pair, vectorSpan_pair, Submodule.mem_span_singleton] at hmem
      obtain ⟨α, hα⟩ := hmem
      have h1 : c' - x = (-α) • (b - a) + (0 : ℝ) • (c' - x) := by
        rw [← hα, vsub_eq_sub]
        module
      rw [h1, hG'] at hGc'
      simp at hGc'
    · exact hpos
  obtain ⟨U, hU, hUR⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hRnb
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem hU (eventually_mem_space_iff_mem_coface R hσ hx))
  have hconv : ∀ z ∈ convexHull ℝ (((({a, b} : Finset (EuclideanSpace ℝ (Fin 2)))) :
      Set (EuclideanSpace ℝ (Fin 2)))), f (z - x) = 0 := by
    have hc0 : Convex ℝ {q : EuclideanSpace ℝ (Fin 2) | f (q - x) = 0} := by
      have h : {q : EuclideanSpace ℝ (Fin 2) | f (q - x) = 0} =
          (f.toAffineMap.comp ((AffineEquiv.vaddConst ℝ x).symm.toAffineMap)) ⁻¹' {0} := by
        ext q
        simp [vsub_eq_sub]
      rw [h]
      exact (convex_singleton (0 : ℝ)).affine_preimage _
    exact fun z hz => convexHull_min (fun v hv => hfσ v (Finset.mem_coe.mp hv)) hc0 hz
  have hnonneg : ∀ z ∈ ball x ε₁, z ∈ S → 0 ≤ f (z - x) := by
    intro z hz hzS
    obtain ⟨hzU, hzev⟩ := hb₁ hz
    obtain ⟨u, hu, hσu, hzu⟩ := hzev.mp (hUR ⟨hzU, hzS⟩)
    by_cases hue : u = {a, b}
    · rw [hue] at hzu
      exact (hconv z hzu).symm.le
    · obtain ⟨c', hc', hu'⟩ := exists_eq_insert_of_ssubset_of_card_eq_two R h2 hu hσu hue
      rw [hu'] at hzu hu
      obtain ⟨r, hr, hfr⟩ := exists_apply_sub_eq_mul_of_mem_convexHull_insert hc' f hfσ hzu
      rw [hfr]
      exact mul_nonneg hr (hside c' hc' hu).le
  refine ⟨c, A', min ε₀ ε₁, hc, hτ, hA', hL, lt_min hε₀ hε₁, ?_, ?_, fun ζ hζ => hker ζ hζ, hℓc⟩
  · intro z hz
    constructor
    · intro hzS
      exact hnonneg z (ball_subset_ball (min_le_right _ _) hz) hzS
    · intro h
      exact hRS (hhull hτ z (hb₀ z (ball_subset_ball (min_le_left _ _) hz)
        (by rw [hfc]; exact mul_nonneg h hℓc.le)))
  · intro z hz hzS
    have h0 := hnonneg z (ball_subset_ball (min_le_right _ _) hz) hzS
    refine hb₀ z (ball_subset_ball (min_le_left _ _) hz) ?_
    rw [hfc]
    exact mul_nonneg h0 hℓc.le

section Ambient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

open Classical in
theorem exists_wallProductBlock_of_boundary_crossing {BdM C : Set M} {ι : Type}
    (ecf : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓf : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) (Eb Eb' : ι → Set M)
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)} (i₀ : ι)
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ecf ℓf Eb Eb')
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : IsCompact S) (hgc : ContinuousOn g S) (hgC : MapsTo g S C)
    (hSball : closure (interior S) = S)
    {R Ac Lc Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hsub : IsSubdivision R Rc) (hRsfin : R.faces.Finite) (hRS : Rc.space ⊆ S)
    (hLspace : Lc.space = Rc.space ∩ frontier S)
    (hBvL : ∀ v ∈ R.vertices, v ∈ Bv ↔ v ∈ Lc.space)
    (hpzero : ∀ x ∈ Rc.space, ℓf i₀ (simplicialMap R φ x) = 0 ↔ x ∈ Lc.space)
    (hguard : ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
      (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
        (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker (ℓf i₀)) + 1 →
        AffineIndependent ℝ
          (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
        AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))))
    (hgR : ∀ z ∈ Rc.space, g z ∈ (ecf i₀).source ∧ ecf i₀ (g z) = simplicialMap R φ z)
    {y : M} {x₁ x₂ : EuclideanSpace ℝ (Fin 2)} (hne : x₁ ≠ x₂) (hgx₁ : g x₁ = y)
    (hgx₂ : g x₂ = y) (hfib : ∀ x ∈ S, g x = y → x = x₁ ∨ x = x₂)
    (hRnb₁ : R.space ∈ 𝓝[S] x₁) (hRnb₂ : R.space ∈ 𝓝[S] x₂)
    (hfree₁ : ∀ σ ∈ R.faces, x₁ ∈ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) →
      ∀ v ∈ σ, v ∉ Ac.space)
    (hfree₂ : ∀ σ ∈ R.faces, x₂ ∈ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) →
      ∀ v ∈ σ, v ∉ Ac.space)
    {σ₁ σ₂ : Finset (EuclideanSpace ℝ (Fin 2))} (hσ₁ : σ₁ ∈ R.faces) (hσ₂ : σ₂ ∈ R.faces)
    (h2₁ : σ₁.card = 2) (h2₂ : σ₂.card = 2) (hdisj : Disjoint σ₁ σ₂) (hB : σ₁ ∪ σ₂ ⊆ Bv)
    (hx₁ : x₁ ∈ openSimplex σ₁) (hx₂ : x₂ ∈ openSimplex σ₂)
    (hyE : y ∈ interior (Eb i₀)) (hyskel : y ∉ wallSystemSkeleton Q ρ) :
    ∃ (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ)
      (SA SB : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ × ℝ → ℝ) (La Lb : ℝ),
      WallProductBlock g S (ecf i₀) (ℓf i₀) BdM C Q ρ A r tlo SA SB a b La Lb 1 ∧
        chartBlock (ecf i₀) A r tlo ⊆ Eb i₀ ∧ A (ecf i₀ y) = 0 ∧
          (tlo = -r ∨ (tlo = 0 ∧ ∀ q, (A q).2.2 = ℓf i₀ q)) := by
  set ec := ecf i₀ with hecdef
  set ℓ := ℓf i₀ with hℓdef
  have hℓ0 : ℓ ≠ 0 := hsys.normalNe i₀
  have hhull : ∀ {σ : Finset (EuclideanSpace ℝ (Fin 2))}, σ ∈ R.faces →
      ∀ z ∈ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))), z ∈ Rc.space :=
    fun hσ z hz => hsub.space_eq ▸ R.convexHull_subset_space hσ hz
  have hvσ : ∀ {σ : Finset (EuclideanSpace ℝ (Fin 2))}
      {A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)}, σ ∈ R.faces →
      EqOn (simplicialMap R φ) A (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) →
      ∀ v ∈ σ, A v = φ v := by
    intro σ A hσ hA v hv
    rw [← hA (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))]
    exact simplicialMap_vertex R φ
      (R.down_closed hσ (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  have hAform : ∀ (A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
      (x z : EuclideanSpace ℝ (Fin 2)), A z = A x + A.linear (z - x) := by
    intro A x z
    have h := A.linearMap_vsub z x
    rw [vsub_eq_sub, vsub_eq_sub] at h
    rw [h]
    abel
  have hfarpt : ∀ {H : Set (EuclideanSpace ℝ (Fin 2))} {x : EuclideanSpace ℝ (Fin 2)},
      IsClosed H → x ∉ H → ∃ ε > 0, Disjoint H (ball x ε) := by
    intro H x hcl hxn
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hcl.isOpen_compl x hxn
    exact ⟨ε, hε, Set.disjoint_left.mpr fun z hz hzb => hball hzb hz⟩
  have hclosed : ∀ σ : Finset (EuclideanSpace ℝ (Fin 2)),
      IsClosed (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    fun σ => (σ.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
  have hpnn : ∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap R φ x) := by
    intro x hx
    rw [← (hgR x hx).2]
    exact (hsys.chartC i₀ (g x) (hgR x hx).1).mp (hgC (hRS hx))
  have hσ₁B : σ₁ ⊆ Bv := Finset.subset_union_left.trans hB
  have hσ₂B : σ₂ ⊆ Bv := Finset.subset_union_right.trans hB
  obtain ⟨c₁, A₁, ε₁, hc₁, hτ₁, hA₁, hL₁, hε₁, hS₁, hloc₁, hker₁, hℓc₁⟩ :=
    exists_boundaryEdgeSheet hℓ0 hsub hRsfin hRS hLspace hBvL hpzero hpnn hguard hSball hσ₁ h2₁
      hσ₁B hx₁ hRnb₁ hfree₁
  obtain ⟨c₂, A₂, ε₂, hc₂, hτ₂, hA₂, hL₂, hε₂, hS₂, hloc₂, hker₂, hℓc₂⟩ :=
    exists_boundaryEdgeSheet hℓ0 hsub hRsfin hRS hLspace hBvL hpzero hpnn hguard hSball hσ₂ h2₂
      hσ₂B hx₂ hRnb₂ hfree₂
  have hx₁h := openSimplex_subset_convexHull σ₁ hx₁
  have hx₂h := openSimplex_subset_convexHull σ₂ hx₂
  have hx₁τ : x₁ ∈ convexHull ℝ ((insert c₁ σ₁ : Finset _) : Set (EuclideanSpace ℝ (Fin 2))) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _)) hx₁h
  have hx₂τ : x₂ ∈ convexHull ℝ ((insert c₂ σ₂ : Finset _) : Set (EuclideanSpace ℝ (Fin 2))) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _)) hx₂h
  have hRx₁ : x₁ ∈ Rc.space := hhull hσ₁ x₁ hx₁h
  have hRx₂ : x₂ ∈ Rc.space := hhull hσ₂ x₂ hx₂h
  have hysrc : y ∈ ec.source := hgx₁ ▸ (hgR x₁ hRx₁).1
  have hA₁x : A₁ x₁ = ec y := by rw [← hA₁ hx₁τ, ← (hgR x₁ hRx₁).2, hgx₁]
  have hA₂x : A₂ x₂ = ec y := by rw [← hA₂ hx₂τ, ← (hgR x₂ hRx₂).2, hgx₂]
  have hec₁ : ∀ z ∈ convexHull ℝ ((insert c₁ σ₁ : Finset _) : Set (EuclideanSpace ℝ (Fin 2))),
      ec (g z) = ec y + A₁.linear (z - x₁) := fun z hz => by
    rw [(hgR z (hhull hτ₁ z hz)).2, hA₁ hz, hAform A₁ x₁ z, hA₁x]
  have hec₂ : ∀ z ∈ convexHull ℝ ((insert c₂ σ₂ : Finset _) : Set (EuclideanSpace ℝ (Fin 2))),
      ec (g z) = ec y + A₂.linear (z - x₂) := fun z hz => by
    rw [(hgR z (hhull hτ₂ z hz)).2, hA₂ hz, hAform A₂ x₂ z, hA₂x]
  have hx₁L : x₁ ∈ Lc.space :=
    convexHull_subset_of_subset_boundaryVertices hsub hBvL hpzero hσ₁ hσ₁B hx₁h
  have hℓy : ℓ (ec y) = 0 := by
    rw [← hgx₁, (hgR x₁ hRx₁).2]
    exact (hpzero x₁ hRx₁).mpr hx₁L
  have hyB : y ∈ BdM := (hsys.chartBd i₀ y hysrc).mpr hℓy
  have hℓv : ∀ v ∈ Bv, {v} ∈ R.faces → ℓ (φ v) = 0 := by
    intro v hvB hv
    have hvL := (hBvL v hv).mp hvB
    have hvR : v ∈ Rc.space := hsub.space_eq ▸ Geometry.SimplicialComplex.vertices_subset_space hv
    rw [← simplicialMap_vertex R φ hv]
    exact (hpzero v hvR).mpr hvL
  have hc₁V : {c₁} ∈ R.faces :=
    R.down_closed hτ₁ (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
      (Finset.singleton_nonempty _)
  have hc₂V : {c₂} ∈ R.faces :=
    R.down_closed hτ₂ (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
      (Finset.singleton_nonempty _)
  have hc₁B : c₁ ∉ Bv := fun h => absurd (hℓv c₁ h hc₁V) hℓc₁.ne'
  have hc₂B : c₂ ∉ Bv := fun h => absurd (hℓv c₂ h hc₂V) hℓc₂.ne'
  obtain ⟨a₁, b₁, hab₁, rfl⟩ := Finset.card_eq_two.mp h2₁
  obtain ⟨a₂, b₂, hab₂, rfl⟩ := Finset.card_eq_two.mp h2₂
  have ha₁σ : a₁ ∈ ({a₁, b₁} : Finset (EuclideanSpace ℝ (Fin 2))) := Finset.mem_insert_self _ _
  have hb₁σ : b₁ ∈ ({a₁, b₁} : Finset (EuclideanSpace ℝ (Fin 2))) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have ha₂σ : a₂ ∈ ({a₂, b₂} : Finset (EuclideanSpace ℝ (Fin 2))) := Finset.mem_insert_self _ _
  have hb₂σ : b₂ ∈ ({a₂, b₂} : Finset (EuclideanSpace ℝ (Fin 2))) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have ha₂σ₁ : a₂ ∉ ({a₁, b₁} : Finset (EuclideanSpace ℝ (Fin 2))) :=
    fun h => Finset.disjoint_left.mp hdisj h ha₂σ
  have ha₁σ₂ : a₁ ∉ ({a₂, b₂} : Finset (EuclideanSpace ℝ (Fin 2))) :=
    fun h => Finset.disjoint_left.mp hdisj ha₁σ h
  have ha₂τ₁ : a₂ ∉ insert c₁ ({a₁, b₁} : Finset (EuclideanSpace ℝ (Fin 2))) := by
    rw [Finset.mem_insert, not_or]
    refine ⟨fun h => hc₁B ?_, ha₂σ₁⟩
    rw [← h]
    exact hσ₂B ha₂σ
  have ha₁τ₂ : a₁ ∉ insert c₂ ({a₂, b₂} : Finset (EuclideanSpace ℝ (Fin 2))) := by
    rw [Finset.mem_insert, not_or]
    refine ⟨fun h => hc₂B ?_, ha₁σ₂⟩
    rw [← h]
    exact hσ₁B ha₁σ
  have hcard₁ : (insert c₁ ({a₁, b₁} : Finset (EuclideanSpace ℝ (Fin 2)))).card = 3 := by
    rw [Finset.card_insert_of_notMem hc₁, Finset.card_pair hab₁]
  have hvert : ∀ {σ : Finset (EuclideanSpace ℝ (Fin 2))}, σ ∈ R.faces →
      (σ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices :=
    fun hσ v hv => R.down_closed hσ (Finset.singleton_subset_iff.mpr (Finset.mem_coe.mp hv))
      (Finset.singleton_nonempty v)
  have hLab : ∀ (A' : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
      {τ : Finset (EuclideanSpace ℝ (Fin 2))} {u v : EuclideanSpace ℝ (Fin 2)}, τ ∈ R.faces →
      EqOn (simplicialMap R φ) A' (convexHull ℝ (τ : Set (EuclideanSpace ℝ (Fin 2)))) →
      u ∈ τ → v ∈ τ → A'.linear (v - u) = φ v - φ u := by
    intro A' τ u v hτ hA' hu hv
    have h := A'.linearMap_vsub v u
    rw [vsub_eq_sub, vsub_eq_sub, hvσ hτ hA' v hv, hvσ hτ hA' u hu] at h
    exact h
  have hz : A₂.linear (a₂ - x₂) ∉ LinearMap.range A₁.linear := by
    rintro ⟨ζ, hζ⟩
    have hφ : φ a₂ = A₁ (x₁ + ζ) := by
      rw [← hvσ hτ₂ hA₂ a₂ (Finset.mem_insert_of_mem ha₂σ), hAform A₂ x₂ a₂, hA₂x, ← hζ,
        hAform A₁ x₁ (x₁ + ζ), hA₁x, add_sub_cancel_left]
    have hnotB : ¬ (insert a₂ (insert c₁ ({a₁, b₁} : Finset (EuclideanSpace ℝ (Fin 2)))) ⊆ Bv) :=
      fun h => hc₁B (h (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    obtain ⟨u, hu, huB⟩ := Finset.not_subset.mp hnotB
    have hind : AffineIndependent ℝ (fun u : (insert a₂ (insert c₁ ({a₁, b₁} :
        Finset (EuclideanSpace ℝ (Fin 2)))) : Finset _) => φ (u : EuclideanSpace ℝ (Fin 2))) := by
      refine affineIndependent_of_wallGuard hℓ0 hguard ?_ ?_ ?_ ?_
      · rw [Finset.coe_insert]
        exact insert_subset (hvert hσ₂ (Finset.mem_coe.mpr ha₂σ)) (hvert hτ₁)
      · rw [Finset.card_insert_of_notMem ha₂τ₁, hcard₁]
      · have hlt : (insert a₂ (insert c₁ ({a₁, b₁} : Finset _)) ∩ Bv).card <
            (insert a₂ (insert c₁ ({a₁, b₁} : Finset (EuclideanSpace ℝ (Fin 2))))).card := by
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨Finset.inter_subset_left, fun h => huB ?_⟩)
          have hmem : u ∈ insert a₂ (insert c₁ ({a₁, b₁} : Finset _)) ∩ Bv := by
            rw [h]
            exact hu
          exact (Finset.mem_inter.mp hmem).2
        rw [Finset.card_insert_of_notMem ha₂τ₁, hcard₁] at hlt
        omega
      · intro u' hu'
        rcases Finset.mem_insert.mp hu' with rfl | hu'
        · exact hfree₂ _ hσ₂ hx₂h _ ha₂σ
        · exact hfree₁ _ hτ₁ hx₁τ u' hu'
    exact not_affineIndependent_insert_of_mem_range (R.indep hτ₁)
      (by rw [hcard₁, finrank_euclideanSpace_fin]) (hvσ hτ₁ hA₁) ha₂τ₁ hφ hind
  have htrans : ∃ ζ₁ ζ₂, A₁.linear ζ₁ = A₂.linear ζ₂ ∧ ℓ (A₁.linear ζ₁) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨ζ₁, ζ₂, hζ, hζ0⟩ := exists_apply_eq_apply_ne_zero
      (by rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]; norm_num) hL₁ hL₂
    have h1 := hker₁ ζ₁ (hcon ζ₁ ζ₂ hζ)
    have h2 := hker₂ ζ₂ (by rw [← hζ]; exact hcon ζ₁ ζ₂ hζ)
    rw [Finset.coe_pair, vectorSpan_pair, Submodule.mem_span_singleton] at h1 h2
    obtain ⟨α₁, hα₁⟩ := h1
    obtain ⟨α₂, hα₂⟩ := h2
    rw [vsub_eq_sub] at hα₁ hα₂
    have hα₂0 : α₂ ≠ 0 := fun h => hζ0 (by rw [hζ, ← hα₂, h, zero_smul, map_zero])
    have hrel : α₁ • (φ a₁ - φ b₁) = α₂ • (φ a₂ - φ b₂) := by
      rw [← hLab A₁ hτ₁ hA₁ (Finset.mem_insert_of_mem hb₁σ) (Finset.mem_insert_of_mem ha₁σ),
        ← hLab A₂ hτ₂ hA₂ (Finset.mem_insert_of_mem hb₂σ) (Finset.mem_insert_of_mem ha₂σ),
        ← map_smul, ← map_smul, hα₁, hα₂, hζ]
    obtain ⟨θ₁, -, -, hxθ₁⟩ := exists_eq_add_smul_of_mem_openSimplex_pair hab₁ hx₁
    obtain ⟨θ₂, -, -, hxθ₂⟩ := exists_eq_add_smul_of_mem_openSimplex_pair hab₂ hx₂
    have e1 : ec y = φ a₁ + θ₁ • (φ b₁ - φ a₁) := by
      rw [← hA₁x, hAform A₁ a₁ x₁, hxθ₁, add_sub_cancel_left, map_smul,
        hLab A₁ hτ₁ hA₁ (Finset.mem_insert_of_mem ha₁σ) (Finset.mem_insert_of_mem hb₁σ),
        hvσ hτ₁ hA₁ a₁ (Finset.mem_insert_of_mem ha₁σ)]
    have e2 : ec y = φ a₂ + θ₂ • (φ b₂ - φ a₂) := by
      rw [← hA₂x, hAform A₂ a₂ x₂, hxθ₂, add_sub_cancel_left, map_smul,
        hLab A₂ hτ₂ hA₂ (Finset.mem_insert_of_mem ha₂σ) (Finset.mem_insert_of_mem hb₂σ),
        hvσ hτ₂ hA₂ a₂ (Finset.mem_insert_of_mem ha₂σ)]
    have hv : φ b₂ - φ a₂ = (α₁ / α₂) • (φ b₁ - φ a₁) := by
      have h3 : φ b₂ - φ a₂ = -(α₂⁻¹ • (α₂ • (φ a₂ - φ b₂))) := by
        rw [smul_smul, inv_mul_cancel₀ hα₂0, one_smul, neg_sub]
      rw [h3, ← hrel]
      module
    have hφ : φ a₂ = AffineMap.lineMap (φ a₁) (φ b₁) (θ₁ - θ₂ * (α₁ / α₂)) := by
      rw [AffineMap.lineMap_apply_module']
      have e2' : φ a₂ = ec y - θ₂ • (φ b₂ - φ a₂) := by
        rw [e2]
        abel
      rw [e2', hv, e1]
      module
    have ha₂a₁ : a₂ ≠ a₁ := fun h => ha₂σ₁ (h ▸ ha₁σ)
    have ha₂b₁ : a₂ ≠ b₁ := fun h => ha₂σ₁ (h ▸ hb₁σ)
    have hind : AffineIndependent ℝ (fun u : (insert a₂ ({a₁, b₁} :
        Finset (EuclideanSpace ℝ (Fin 2))) : Finset _) => φ (u : EuclideanSpace ℝ (Fin 2))) := by
      refine affineIndependent_of_wallGuard hℓ0 hguard ?_ ?_ ?_ ?_
      · rw [Finset.coe_insert]
        exact insert_subset (hvert hσ₂ (Finset.mem_coe.mpr ha₂σ)) (hvert hσ₁)
      · rw [Finset.card_insert_of_notMem ha₂σ₁, Finset.card_pair hab₁]
        norm_num
      · refine (Finset.card_le_card Finset.inter_subset_left).trans ?_
        rw [Finset.card_insert_of_notMem ha₂σ₁, Finset.card_pair hab₁]
      · intro u' hu'
        rcases Finset.mem_insert.mp hu' with rfl | hu'
        · exact hfree₂ _ hσ₂ hx₂h _ ha₂σ
        · exact hfree₁ _ hσ₁ hx₁h u' hu'
    exact not_affineIndependent_insert_of_eq_lineMap hab₁ ha₂a₁ ha₂b₁ hφ hind
  obtain ⟨A, F₁, F₂, hAν, hAF₁, hAF₂⟩ := exists_affineEquiv_flatSheets
    finrank_euclideanSpace_fin finrank_euclideanSpace_fin hL₁ hL₂ hz htrans (ec y)
  have hAℓ : ∀ q, (A q).2.2 = ℓ q := fun q => by rw [hAν, map_sub, hℓy, sub_zero]
  have hA0 : A (ec y) = 0 := by
    have h := hAF₁ 0
    simp only [map_zero, add_zero] at h
    rw [h]
    rfl
  have hx₂τ₁ : x₂ ∉ convexHull ℝ ((insert c₁ ({a₁, b₁} : Finset _) : Finset _) :
      Set (EuclideanSpace ℝ (Fin 2))) := by
    intro h
    exact ha₂τ₁ (face_subset_of_mem_openSimplex_of_mem_convexHull R hσ₂ hτ₁ hx₂ h ha₂σ)
  have hx₁τ₂ : x₁ ∉ convexHull ℝ ((insert c₂ ({a₂, b₂} : Finset _) : Finset _) :
      Set (EuclideanSpace ℝ (Fin 2))) := by
    intro h
    exact ha₁τ₂ (face_subset_of_mem_openSimplex_of_mem_convexHull R hσ₁ hτ₂ hx₁ h ha₁σ)
  obtain ⟨ε₃, hε₃, hfar₃⟩ := hfarpt (hclosed _) hx₂τ₁
  obtain ⟨ε₄, hε₄, hfar₄⟩ := hfarpt (hclosed _) hx₁τ₂
  have hd12 : 0 < dist x₁ x₂ := dist_pos.mpr hne
  obtain ⟨ρ', hρ'pos, hρ1, hρ2, hρ3, hρ4, hρ5⟩ : ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ε₁ ∧ ρ' ≤ ε₂ ∧
      ρ' ≤ ε₃ ∧ ρ' ≤ ε₄ ∧ ρ' ≤ dist x₁ x₂ / 2 :=
    ⟨min (min ε₁ ε₂) (min (min ε₃ ε₄) (dist x₁ x₂ / 2)),
      lt_min (lt_min hε₁ hε₂) (lt_min (lt_min hε₃ hε₄) (half_pos hd12)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  have hballs : Disjoint (ball x₁ ρ') (ball x₂ ρ') := Metric.ball_disjoint_ball (by linarith)
  obtain ⟨Osep, hOsep, hyOsep, hsep⟩ :=
    exists_isOpen_inter_preimage_subset_ball_union hS hgc hfib hρ'pos
  have hyw' : y ∈ ⋃ w ∈ Bf, wallSystemCell ρ w := by
    rw [← hsys.eqBd]
    exact hyB
  obtain ⟨w, hwBf, hyw⟩ := mem_iUnion₂.mp hyw'
  have hw : w ∈ wallSystemWalls Q := hsys.facesBd hwBf
  obtain ⟨cm, hcm, cp, hcp, -, hwm, hwp, -, U, hU, hyU, -, -, hUcells, hUwalls, hUskel, -, -, -,
    -, -⟩ := hsys.exists_wallChart_sides i₀ hw hyw hyskel (interior_subset hyE)
  obtain ⟨c, hcCf, hwc, hcuniq⟩ := hsys.boundarySides w hwBf
  have hOo : IsOpen (U ∩ interior (Eb i₀)) := hU.inter isOpen_interior
  obtain ⟨r, hr, hsmall⟩ := exists_pos_chartBlock_subset_of_isOpen ec A hysrc hA0
    (hOo.inter hOsep) ⟨⟨hyU, hyE⟩, hyOsep⟩
  obtain ⟨hbox, hcpt, hsrcl, hpts⟩ := hsmall r 0 hr le_rfl (by linarith)
  obtain ⟨Φ₁, hΦ₁⟩ := exists_homeomorph_apply_eq_sub F₁ x₁
  obtain ⟨Φ₂, hΦ₂⟩ := exists_homeomorph_apply_eq_sub F₂ x₂
  have hpoly : ∀ {σ : Finset (EuclideanSpace ℝ (Fin 2))}, σ ∈ R.faces →
      IsHPolytope (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    fun hσ => isHPolytope_convexHull_of_affineIndependent _ (R.indep hσ)
  have hpa0 : IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
    (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ) (0 : ℝ)) isOpen_univ).congr
      fun _ _ => rfl
  have hF₁ : ∀ ζ, (F₁ ζ).2 = ℓ (A₁.linear ζ) := by
    intro ζ
    have h := congrArg (fun q : ℝ × ℝ × ℝ => q.2.2) (hAF₁ ζ)
    simp only at h
    rw [hAℓ, map_add, hℓy, zero_add] at h
    exact h.symm
  have hF₂ : ∀ ζ, (F₂ ζ).2 = ℓ (A₂.linear ζ) := by
    intro ζ
    have h := congrArg (fun q : ℝ × ℝ × ℝ => q.2.2) (hAF₂ ζ)
    simp only at h
    rw [hAℓ, map_add, hℓy, zero_add] at h
    exact h.symm
  have hfront : ∀ x ∈ convexHull ℝ ((insert c₁ ({a₁, b₁} : Finset _) : Finset _) :
      Set (EuclideanSpace ℝ (Fin 2))) ∪ convexHull ℝ ((insert c₂ ({a₂, b₂} : Finset _) :
      Finset _) : Set (EuclideanSpace ℝ (Fin 2))), (x ∈ frontier S ↔ (A (ec (g x))).2.2 = 0) := by
    intro x hx
    have hxR : x ∈ Rc.space := by
      rcases hx with hx | hx
      · exact hhull hτ₁ x hx
      · exact hhull hτ₂ x hx
    rw [hAℓ, (hgR x hxR).2, hpzero x hxR, hLspace]
    exact ⟨fun h => ⟨hxR, h⟩, fun h => h.2⟩
  have hpl₁ : IsPiecewiseAffineOn (fun z => A (ec (g z)))
      (convexHull ℝ ((insert c₁ ({a₁, b₁} : Finset _) : Finset _) :
        Set (EuclideanSpace ℝ (Fin 2)))) := by
    refine (isPiecewiseAffineOn_of_affine_of_isHPolytope (A.toAffineMap.comp A₁)
      (hpoly hτ₁)).congr fun z hz => ?_
    simp only [AffineMap.comp_apply]
    rw [(hgR z (hhull hτ₁ z hz)).2, hA₁ hz]
    rfl
  have hpl₂ : IsPiecewiseAffineOn (fun z => A (ec (g z)))
      (convexHull ℝ ((insert c₂ ({a₂, b₂} : Finset _) : Finset _) :
        Set (EuclideanSpace ℝ (Fin 2)))) := by
    refine (isPiecewiseAffineOn_of_affine_of_isHPolytope (A.toAffineMap.comp A₂)
      (hpoly hτ₂)).congr fun z hz => ?_
    simp only [AffineMap.comp_apply]
    rw [(hgR z (hhull hτ₂ z hz)).2, hA₂ hz]
    rfl
  have hgraph₁ : ∀ z ∈ convexHull ℝ ((insert c₁ ({a₁, b₁} : Finset _) : Finset _) :
      Set (EuclideanSpace ℝ (Fin 2))),
      (A (ec (g z))).1 = (fun _ : ℝ × ℝ => (0 : ℝ)) ((A (ec (g z))).2.1, (A (ec (g z))).2.2) := by
    intro z hz
    rw [hec₁ z hz, hAF₁]
  have hgraph₂ : ∀ z ∈ convexHull ℝ ((insert c₂ ({a₂, b₂} : Finset _) : Finset _) :
      Set (EuclideanSpace ℝ (Fin 2))),
      (A (ec (g z))).2.1 = (fun _ : ℝ × ℝ => (0 : ℝ)) ((A (ec (g z))).1, (A (ec (g z))).2.2) := by
    intro z hz
    rw [hec₂ z hz, hAF₂]
  have hΦ₁' : ∃ Φ : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ,
      (∀ z ∈ convexHull ℝ ((insert c₁ ({a₁, b₁} : Finset _) : Finset _) :
        Set (EuclideanSpace ℝ (Fin 2))), blockSheetProjA ec A g z = Φ z) ∧
      ∀ z ∈ ball x₁ ρ', (z ∈ S ↔ ((0 : ℝ) = 0 → 0 ≤ (Φ z).2)) := by
    refine ⟨Φ₁, fun z hz => ?_, fun z hz => ?_⟩
    · simp only [blockSheetProjA]
      rw [hec₁ z hz, hAF₁, hΦ₁]
    · rw [hS₁ z (ball_subset_ball hρ1 hz), hΦ₁, hF₁]
      exact ⟨fun h _ => h, fun h => h rfl⟩
  have hΦ₂' : ∃ Φ : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ,
      (∀ z ∈ convexHull ℝ ((insert c₂ ({a₂, b₂} : Finset _) : Finset _) :
        Set (EuclideanSpace ℝ (Fin 2))), blockSheetProjB ec A g z = Φ z) ∧
      ∀ z ∈ ball x₂ ρ', (z ∈ S ↔ ((0 : ℝ) = 0 → 0 ≤ (Φ z).2)) := by
    refine ⟨Φ₂, fun z hz => ?_, fun z hz => ?_⟩
    · simp only [blockSheetProjB]
      rw [hec₂ z hz, hAF₂, hΦ₂]
    · rw [hS₂ z (ball_subset_ball hρ2 hz), hΦ₂, hF₂]
      exact ⟨fun h _ => h, fun h => h rfl⟩
  have hblk := isStableCrossingBlock_of_sheets (ℓ := ℓ) (BdM := BdM) hr one_pos le_rfl le_rfl
    (by norm_num) hcpt hsrcl (Or.inr ⟨rfl, hAℓ, hfront⟩)
    (fun _ x hx hs => by rw [hAℓ]; exact (hsys.chartC i₀ (g x) hs).mp (hgC hx))
    hgc hbox (fun z hz => hsep ⟨hz.1, hz.2.2⟩) hballs
    (fun z hz => hRS (hhull hτ₁ z hz)) (fun z hz => hRS (hhull hτ₂ z hz))
    (fun z hz => hloc₁ z (ball_subset_ball hρ1 hz.2) hz.1)
    (fun z hz => hloc₂ z (ball_subset_ball hρ2 hz.2) hz.1)
    (hfar₃.mono_right (ball_subset_ball hρ3)) (hfar₄.mono_right (ball_subset_ball hρ4))
    (hpoly hτ₁).isPolyhedron (hpoly hτ₂).isPolyhedron
    (fun z hz => (hgR z (hhull hτ₁ z hz)).1) (fun z hz => (hgR z (hhull hτ₂ z hz)).1)
    hpl₁ hpl₂ hgraph₁ hgraph₂ hΦ₁' hΦ₂' (fun _ _ _ => by simp) (fun _ _ _ => by simp) hpa0 hpa0
  have hbU : chartBlock ec A r 0 ⊆ U := fun z hz => (hbox hz).1.1
  have hCsub : chartBlock ec A r 0 ∩ C ⊆ wallSystemCell ρ c := by
    rintro z ⟨hzb, hzC⟩
    rw [hsys.eqC] at hzC
    obtain ⟨c'', hc''Cf, hzc''⟩ := mem_iUnion₂.mp hzC
    have hc'' := hUcells c'' (hsys.facesC hc''Cf) ⟨z, hbU hzb, hzc''⟩
    have hwc'' : w ⊆ c'' := by
      rcases hc'' with rfl | rfl
      · exact hwm
      · exact hwp
    rw [← hcuniq c'' hc''Cf hwc'']
    exact hzc''
  have hwB : wallSystemCell ρ w ⊆ BdM := by
    intro z hz
    rw [hsys.eqBd]
    exact mem_iUnion₂.mpr ⟨w, hwBf, hz⟩
  refine ⟨A, r, 0, _, _, _, _, 0, 0, ⟨hblk, Set.disjoint_of_subset_left hbU hUskel,
    Or.inr (Or.inr ⟨c, hsys.facesC hcCf, w, hw, rfl, hwc, hAℓ, hCsub, ?_, ?_,
      fun w' hw' z hz => hUwalls w' hw' ⟨hbU hz.1, hz.2⟩⟩)⟩,
    fun z hz => interior_subset (hbox hz).1.2, hA0, Or.inr ⟨rfl, hAℓ⟩⟩
  · obtain ⟨z, hz, hAz⟩ := hpts ((0 : ℝ), (0 : ℝ), r / 2)
      ⟨by simp only [abs_zero]; exact hr.le, by simp only [abs_zero]; exact hr.le,
        by linarith, by linarith⟩
    have hℓz : ℓ (ec z) = r / 2 := by rw [← hAℓ, hAz]
    have hzs : z ∈ ec.source := hz.1
    have hzC : z ∈ C := (hsys.chartC i₀ z hzs).mpr (by rw [hℓz]; linarith)
    have hzc : z ∈ wallSystemCell ρ c := hCsub ⟨hz, hzC⟩
    refine ⟨z, hz, ?_⟩
    by_contra hni
    obtain ⟨w', hw', hzw'⟩ :=
      mem_iUnion₂.mp (wallSystemCell_sdiff_subset_iUnion_wall (hsys.facesC hcCf) ⟨hzc, hni⟩)
    have hzw := hUwalls w' hw' ⟨hbU hz, hzw'⟩
    have hzB := hwB hzw
    have h0 := (hsys.chartBd i₀ z hzs).mp hzB
    rw [hℓz] at h0
    linarith
  · rintro z ⟨hzb, hzB⟩
    rw [hsys.eqBd] at hzB
    obtain ⟨w'', hw''Bf, hzw''⟩ := mem_iUnion₂.mp hzB
    exact hUwalls w'' (hsys.facesBd hw''Bf) ⟨hbU hzb, hzw''⟩

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
