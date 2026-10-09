/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleCrossingBlock
import DifferentialGeometry.Topology.PiecewiseLinear.EdgeSideCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.KinkedBlockCoordinates

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Ambient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

open Classical in
theorem exists_wallProductBlock_of_edge_crossing {BdM C : Set M} {ι : Type}
    (ecf : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓf : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) (Eb Eb' : ι → Set M)
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)} (i₀ : ι)
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ecf ℓf Eb Eb')
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : IsCompact S) (hgc : ContinuousOn g S)
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
    (hRnb₁ : R.space ∈ 𝓝[S] x₁)
    (hfree₁ : ∀ σ ∈ R.faces, x₁ ∈ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) →
      ∀ v ∈ σ, v ∉ Ac.space)
    {σ₁ σ₂ : Finset (EuclideanSpace ℝ (Fin 2))} (hσ₁ : σ₁ ∈ R.faces) (hσ₂ : σ₂ ∈ R.faces)
    (h2₁ : σ₁.card = 2) (h3₂ : σ₂.card = 3) (hdisj : Disjoint σ₁ σ₂)
    (hfr₂ : ∀ v ∈ σ₂, v ∉ Ac.space)
    (hx₁ : x₁ ∈ openSimplex σ₁) (hx₂ : x₂ ∈ openSimplex σ₂)
    (hyE : y ∈ interior (Eb i₀)) (hnowall : ∀ w ∈ wallSystemWalls Q, y ∉ wallSystemCell ρ w) :
    ∃ (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ)
      (SA SB : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ × ℝ → ℝ) (La Lb : ℝ),
      WallProductBlock g S (ecf i₀) (ℓf i₀) BdM C Q ρ A r tlo SA SB a b La Lb 1 ∧
        chartBlock (ecf i₀) A r tlo ⊆ Eb i₀ ∧ A (ecf i₀ y) = 0 ∧
          (tlo = -r ∨ (tlo = 0 ∧ ∀ q, (A q).2.2 = ℓf i₀ q)) := by
  set ec := ecf i₀ with hecdef
  set ℓ := ℓf i₀ with hℓdef
  have hℓ0 : ℓ ≠ 0 := hsys.normalNe i₀
  have : Finite R.faces := hRsfin.to_subtype
  have hhull : ∀ {σ : Finset (EuclideanSpace ℝ (Fin 2))}, σ ∈ R.faces →
      ∀ z ∈ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))), z ∈ Rc.space :=
    fun hσ z hz => hsub.space_eq ▸ R.convexHull_subset_space hσ hz
  have hvert : ∀ {σ : Finset (EuclideanSpace ℝ (Fin 2))}, σ ∈ R.faces →
      (σ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices :=
    fun hσ v hv => R.down_closed hσ (Finset.singleton_subset_iff.mpr (Finset.mem_coe.mp hv))
      (Finset.singleton_nonempty v)
  have hint : ∀ {σ : Finset (EuclideanSpace ℝ (Fin 2))}, σ ∈ R.faces → σ.card = 3 →
      interior (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) = openSimplex σ :=
    fun hσ h3 => interior_convexHull_eq_openSimplex (R.indep hσ)
      (by rw [h3, finrank_euclideanSpace_fin])
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
  have hinjA : ∀ {σ : Finset (EuclideanSpace ℝ (Fin 2))}
      {A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)}
      {x : EuclideanSpace ℝ (Fin 2)}, σ ∈ R.faces → σ.card = 3 → (∀ v ∈ σ, v ∉ Ac.space) →
      EqOn (simplicialMap R φ) A (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) →
      x ∈ openSimplex σ → Function.Injective A.linear := by
    intro σ A x hσ h3 hfr hA hx
    have hind : AffineIndependent ℝ (fun v : σ => φ (v : EuclideanSpace ℝ (Fin 2))) :=
      affineIndependent_of_wallGuard hℓ0 hguard (hvert hσ) (by omega)
        ((Finset.card_le_card Finset.inter_subset_left).trans h3.le) hfr
    have hind' : AffineIndependent ℝ
        (fun v : (σ ∪ σ : Finset _) => φ (v : EuclideanSpace ℝ (Fin 2))) := by
      rw [Finset.union_self]
      exact hind
    refine linear_injective_of_injOn_of_interior_nonempty
      (C := convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) ?_
      ⟨x, by rw [hint hσ h3]; exact hx⟩
    intro z hz z' hz' h
    exact eq_of_simplicialMap_eq_of_affineIndependent R φ hσ hσ hz hz' hind'
      (by rw [hA hz, hA hz', h])
  have hguard4 : ∀ {v : EuclideanSpace ℝ (Fin 2)} {τ : Finset (EuclideanSpace ℝ (Fin 2))},
      τ ∈ R.faces → τ.card = 3 → v ∉ τ → {v} ∈ R.faces → (∀ u ∈ insert v τ, u ∉ Ac.space) →
      ¬ (insert v τ ⊆ Bv) →
      AffineIndependent ℝ
        (fun u : (insert v τ : Finset _) => φ (u : EuclideanSpace ℝ (Fin 2))) := by
    intro v τ hτ h3 hvτ hv hfr hB
    obtain ⟨u, hu, huB⟩ := Finset.not_subset.mp hB
    refine affineIndependent_of_wallGuard hℓ0 hguard ?_ ?_ ?_ hfr
    · rw [Finset.coe_insert]
      exact insert_subset hv (hvert hτ)
    · rw [Finset.card_insert_of_notMem hvτ, h3]
    · have hlt : (insert v τ ∩ Bv).card < (insert v τ).card := by
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.inter_subset_left, fun h => huB ?_⟩)
        have hmem : u ∈ insert v τ ∩ Bv := by
          rw [h]
          exact hu
        exact (Finset.mem_inter.mp hmem).2
      rw [Finset.card_insert_of_notMem hvτ, h3] at hlt
      omega
  have hfarpt : ∀ {H : Set (EuclideanSpace ℝ (Fin 2))} {x : EuclideanSpace ℝ (Fin 2)},
      IsClosed H → x ∉ H → ∃ ε > 0, Disjoint H (ball x ε) := by
    intro H x hcl hxn
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hcl.isOpen_compl x hxn
    exact ⟨ε, hε, Set.disjoint_left.mpr fun z hz hzb => hball hzb hz⟩
  have hclosed : ∀ σ : Finset (EuclideanSpace ℝ (Fin 2)),
      IsClosed (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    fun σ => (σ.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
  obtain ⟨A₂, hA₂⟩ := exists_affineMap_eqOn_simplicialMap R φ hσ₂
  have hL₂ := hinjA hσ₂ h3₂ hfr₂ hA₂ hx₂
  have hx₁h := openSimplex_subset_convexHull σ₁ hx₁
  have hx₂h := openSimplex_subset_convexHull σ₂ hx₂
  have hRx₁ : x₁ ∈ Rc.space := hhull hσ₁ x₁ hx₁h
  have hRx₂ : x₂ ∈ Rc.space := hhull hσ₂ x₂ hx₂h
  have hysrc : y ∈ ec.source := hgx₁ ▸ (hgR x₁ hRx₁).1
  have hy'₂ : A₂ x₂ = ec y := by rw [← hA₂ hx₂h, ← (hgR x₂ hRx₂).2, hgx₂]
  have hec₂ : ∀ z ∈ convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2))),
      ec (g z) = ec y + A₂.linear (z - x₂) := fun z hz => by
    rw [(hgR z (hhull hσ₂ z hz)).2, hA₂ hz, hAform A₂ x₂ z, hy'₂]
  have hx₂int : x₂ ∈ interior S :=
    interior_mono (fun z hz => hRS (hhull hσ₂ z hz)) (by rw [hint hσ₂ h3₂]; exact hx₂)
  have hℓy : ℓ (ec y) ≠ 0 := by
    intro h0
    rw [← hgx₂, (hgR x₂ hRx₂).2] at h0
    have hL := (hpzero x₂ hRx₂).mp h0
    rw [hLspace] at hL
    exact hL.2.2 hx₂int
  have hyB : y ∉ BdM := fun hyB => hℓy ((hsys.chartBd i₀ y hysrc).mp hyB)
  have hx₁int : x₁ ∈ interior S := by
    by_contra hni
    have hL : x₁ ∈ Lc.space := by
      rw [hLspace]
      exact ⟨hRx₁, subset_closure (hRS hRx₁), hni⟩
    have h0 := (hpzero x₁ hRx₁).mpr hL
    rw [← (hgR x₁ hRx₁).2, hgx₁] at h0
    exact hℓy h0
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2₁
  obtain ⟨cp, hcp, hτp⟩ := exists_insert_mem_faces_of_mem_closure_interior R hσ₁ h2₁ hx₁ hRnb₁
    (subset_closure hx₁int)
  obtain ⟨G, θ, -, -, hxθ, hG, hdec, hker, hGa, hGb, hGc⟩ :=
    exists_edgeSideCoordinates R hab hx₁ hcp hτp
  let f : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ := (LinearMap.snd ℝ ℝ ℝ).comp G.toLinearMap
  have hf : ∀ ζ, f ζ = (G ζ).2 := fun _ => rfl
  have hfσ : ∀ v ∈ ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))), f (v - x₁) = 0 := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hGa
    · rw [Finset.mem_singleton.mp hv]
      exact hGb
  have hfhull : ∀ z ∈ convexHull ℝ ((({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) :
      Set (EuclideanSpace ℝ (Fin 2)))), f (z - x₁) = 0 := by
    have hconv : Convex ℝ {q : EuclideanSpace ℝ (Fin 2) | f (q - x₁) = 0} := by
      have h : {q : EuclideanSpace ℝ (Fin 2) | f (q - x₁) = 0} =
          (f.toAffineMap.comp ((AffineEquiv.vaddConst ℝ x₁).symm.toAffineMap)) ⁻¹' {0} := by
        ext q
        simp [vsub_eq_sub]
      rw [h]
      exact (convex_singleton (0 : ℝ)).affine_preimage _
    exact fun z hz => convexHull_min (fun v hv => hfσ v (Finset.mem_coe.mp hv)) hconv hz
  have hfcp : f (cp - x₁) = 1 := hGc
  obtain ⟨cm, hcm, hτm, hfcm⟩ : ∃ c', c' ∉ ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) ∧
      insert c' ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) ∈ R.faces ∧ f (c' - x₁) < 0 := by
    obtain ⟨U₁, hU₁, hU₁R⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hRnb₁
    have hN := Filter.inter_mem (Filter.inter_mem (isOpen_interior.mem_nhds hx₁int) hU₁)
      (eventually_mem_space_iff_mem_coface R hσ₁ hx₁)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hN
    set n : EuclideanSpace ℝ (Fin 2) := cp - x₁ with hn
    set t : ℝ := ε / (2 * (‖n‖ + 1)) with ht
    have hden : 0 < 2 * (‖n‖ + 1) := by positivity
    have htpos : 0 < t := div_pos hε hden
    have hz₀ : x₁ - t • n ∈ ball x₁ ε := by
      rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_pos htpos]
      have h1 : t * ‖n‖ ≤ t * (‖n‖ + 1) := by nlinarith [norm_nonneg n]
      have h2 : t * (‖n‖ + 1) = ε / 2 := by
        rw [ht]
        field_simp
      linarith
    obtain ⟨⟨hzint, hzU⟩, hzev⟩ := hball hz₀
    have hzR : x₁ - t • n ∈ R.space := hU₁R ⟨hzU, interior_subset hzint⟩
    obtain ⟨u, hu, hσu, hzu⟩ := hzev.mp hzR
    have hfz : f (x₁ - t • n - x₁) = -t := by
      rw [sub_sub_cancel_left, map_neg, map_smul, hfcp, smul_eq_mul, mul_one]
    have hune : u ≠ {a, b} := by
      intro h
      rw [h] at hzu
      have := hfhull _ hzu
      rw [hfz] at this
      linarith
    obtain ⟨c', hc', hu'⟩ := exists_eq_insert_of_ssubset_of_card_eq_two R h2₁ hu hσu hune
    rw [hu'] at hzu hu
    obtain ⟨r, hr, hfr⟩ := exists_apply_sub_eq_mul_of_mem_convexHull_insert hc' f hfσ hzu
    refine ⟨c', hc', hu, ?_⟩
    rw [hfz] at hfr
    by_contra hge
    push Not at hge
    nlinarith
  have hcpcm : cp ≠ cm := by
    intro h
    rw [h] at hfcp
    linarith
  have hcard : ∀ {c : EuclideanSpace ℝ (Fin 2)},
      c ∉ ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) →
        (insert c ({a, b} : Finset (EuclideanSpace ℝ (Fin 2)))).card = 3 := by
    intro c hc
    rw [Finset.card_insert_of_notMem hc, Finset.card_pair hab]
  have hx₁τ : ∀ c : EuclideanSpace ℝ (Fin 2), x₁ ∈ convexHull ℝ
      (((insert c ({a, b} : Finset (EuclideanSpace ℝ (Fin 2)))) : Finset _) :
        Set (EuclideanSpace ℝ (Fin 2))) :=
    fun c => convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _)) hx₁h
  have hfrp := hfree₁ _ hτp (hx₁τ cp)
  have hfrm := hfree₁ _ hτm (hx₁τ cm)
  obtain ⟨Ap, hAp⟩ := exists_affineMap_eqOn_simplicialMap R φ hτp
  obtain ⟨Am, hAm⟩ := exists_affineMap_eqOn_simplicialMap R φ hτm
  have hLm : Function.Injective Am.linear := hinjA hτm (hcard hcm) hfrm hAm
    (centroid_mem_openSimplex (R.nonempty_of_mem_faces hτm))
  have hApx : Ap x₁ = ec y := by rw [← hAp (hx₁τ cp), ← (hgR x₁ hRx₁).2, hgx₁]
  have hAmx : Am x₁ = ec y := by rw [← hAm (hx₁τ cm), ← (hgR x₁ hRx₁).2, hgx₁]
  have hmemτ : ∀ {c v : EuclideanSpace ℝ (Fin 2)}, v ∈ ({a, b} : Finset _) →
      v ∈ insert c ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) :=
    fun hv => Finset.mem_insert_of_mem hv
  have hLe : Ap.linear (b - a) = Am.linear (b - a) := by
    have h1 := Ap.linearMap_vsub b a
    have h2 := Am.linearMap_vsub b a
    rw [vsub_eq_sub, vsub_eq_sub] at h1 h2
    rw [h1, h2, hvσ hτp hAp b (hmemτ (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))),
      hvσ hτp hAp a (hmemτ (Finset.mem_insert_self a {b})),
      hvσ hτm hAm b (hmemτ (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))),
      hvσ hτm hAm a (hmemτ (Finset.mem_insert_self a {b}))]
  set w : EuclideanSpace ℝ (Fin 3) := Ap.linear (cp - x₁) - Am.linear (cp - x₁) with hw
  have hdecomp : ∀ (A' : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
      (ζ : EuclideanSpace ℝ (Fin 2)),
      A'.linear ζ = (G ζ).1 • A'.linear (b - a) + (G ζ).2 • A'.linear (cp - x₁) := by
    intro A' ζ
    have h := congrArg A'.linear (hdec ζ)
    rw [map_add, map_smul, map_smul] at h
    exact h
  have hD : ∀ z, Ap z = Am z + f (z - x₁) • w := by
    intro z
    rw [hAform Ap x₁ z, hAform Am x₁ z, hApx, hAmx, hdecomp Ap (z - x₁), hdecomp Am (z - x₁),
      hLe, hf, hw]
    module
  have hAmz : ∀ z, Am z = ec y + ((G (z - x₁)).1 • Am.linear (b - a) +
      (G (z - x₁)).2 • Am.linear (cp - x₁)) := by
    intro z
    rw [hAform Am x₁ z, hAmx, hdecomp Am (z - x₁)]
  have hbent : ∀ z ∈ convexHull ℝ ((insert cp ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) :
      Finset _) : Set (EuclideanSpace ℝ (Fin 2))) ∪ convexHull ℝ ((insert cm ({a, b} :
      Finset (EuclideanSpace ℝ (Fin 2))) : Finset _) : Set (EuclideanSpace ℝ (Fin 2))),
      ec (g z) = ec y + ((G (z - x₁)).1 • Am.linear (b - a) +
        (G (z - x₁)).2 • Am.linear (cp - x₁) + max (G (z - x₁)).2 0 • w) := by
    rintro z (hz | hz)
    · obtain ⟨r, hr, hfr⟩ := exists_apply_sub_eq_mul_of_mem_convexHull_insert hcp f hfσ hz
      rw [hfcp, mul_one] at hfr
      have hmax : max (G (z - x₁)).2 0 = (G (z - x₁)).2 := by
        rw [← hf, hfr]
        exact max_eq_left hr
      rw [(hgR z (hhull hτp z hz)).2, hAp hz, hD z, hAmz z, hmax, hf]
      abel
    · obtain ⟨r, hr, hfr⟩ := exists_apply_sub_eq_mul_of_mem_convexHull_insert hcm f hfσ hz
      have hmax : max (G (z - x₁)).2 0 = 0 := by
        rw [← hf, hfr]
        exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos hr hfcm.le)
      rw [(hgR z (hhull hτm z hz)).2, hAm hz, hAmz z, hmax, zero_smul, add_zero]
  have hen : ∀ α β : ℝ, α • (b - a) + β • (cp - x₁) = 0 → α = 0 ∧ β = 0 := by
    intro α β h
    have h1 := hG α β
    rw [h, map_zero] at h1
    exact ⟨(congrArg Prod.fst h1).symm, (congrArg Prod.snd h1).symm⟩
  have hcpτm : cp ∉ insert cm ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) := by
    rw [Finset.mem_insert, not_or]
    exact ⟨hcpcm, hcp⟩
  have hwr : w ∉ LinearMap.range Am.linear := by
    rintro ⟨ζ, hζ⟩
    have hφ : φ cp = Am (cp + ζ) := by
      rw [← hvσ hτp hAp cp (Finset.mem_insert_self cp _), hD cp, hfcp, one_smul, ← hζ,
        hAform Am cp (cp + ζ), add_sub_cancel_left]
    have hsub' : insert cp ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) ⊆
        insert cp (insert cm ({a, b} : Finset (EuclideanSpace ℝ (Fin 2)))) :=
      Finset.insert_subset_insert _ (Finset.subset_insert _ _)
    have hnotB : ¬ (insert cp (insert cm ({a, b} : Finset (EuclideanSpace ℝ (Fin 2)))) ⊆ Bv) :=
      fun h => not_subset_boundaryVertices_of_card_eq_three hsub hRS hLspace hBvL hpzero hτp
        (hcard hcp) (hsub'.trans h)
    have hfr4 : ∀ u ∈ insert cp (insert cm ({a, b} : Finset (EuclideanSpace ℝ (Fin 2)))),
        u ∉ Ac.space := by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hfrp _ (Finset.mem_insert_self _ _)
      · exact hfrm u hu
    exact not_affineIndependent_insert_of_mem_range (R.indep hτm)
      (by rw [hcard hcm, finrank_euclideanSpace_fin]) (hvσ hτm hAm) hcpτm hφ
      (hguard4 hτm (hcard hcm) hcpτm (hvert hτp (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)))
        hfr4 hnotB)
  have haσ₂ : a ∉ σ₂ := fun h => Finset.disjoint_left.mp hdisj (Finset.mem_insert_self a {b}) h
  have her : Am.linear (b - a) ∉ LinearMap.range A₂.linear := by
    rintro ⟨ζ, hζ⟩
    have hφ : φ a = A₂ (x₂ + (-θ) • ζ) := by
      rw [← hvσ hτm hAm a (hmemτ (Finset.mem_insert_self a {b})), hAform Am x₁ a, hAmx,
        hAform A₂ x₂ (x₂ + (-θ) • ζ), hy'₂, add_sub_cancel_left, map_smul, hζ, ← map_smul]
      congr 2
      rw [hxθ]
      module
    have hnotB : ¬ (insert a σ₂ ⊆ Bv) :=
      fun h => not_subset_boundaryVertices_of_card_eq_three hsub hRS hLspace hBvL hpzero hσ₂ h3₂
        ((Finset.subset_insert _ _).trans h)
    have hfr4 : ∀ u ∈ insert a σ₂, u ∉ Ac.space := by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hfree₁ _ hσ₁ hx₁h _ (Finset.mem_insert_self _ _)
      · exact hfr₂ u hu
    exact not_affineIndependent_insert_of_mem_range (R.indep hσ₂)
      (by rw [h3₂, finrank_euclideanSpace_fin]) (hvσ hσ₂ hA₂) haσ₂ hφ
      (hguard4 hσ₂ h3₂ haσ₂ (hvert hσ₁ (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))) hfr4
        hnotB)
  obtain ⟨A, μ, μ', F₂, hAb, hA2⟩ := exists_affineEquiv_bentSheet finrank_euclideanSpace_fin
    finrank_euclideanSpace_fin hLm hL₂ hen hwr her (ec y)
  have hA0 : A (ec y) = 0 := by
    have h := hA2 0
    simp only [map_zero, add_zero] at h
    rw [h]
    rfl
  obtain ⟨εp, hεp, hbp⟩ := exists_pos_forall_mem_ball_mem_convexHull_insert (R.indep hτp) hx₁ hcp
    f hker (by rw [hfcp]; norm_num)
  obtain ⟨εm, hεm, hbm⟩ := exists_pos_forall_mem_ball_mem_convexHull_insert (R.indep hτm) hx₁ hcm
    f hker hfcm.ne
  set H₁ : Set (EuclideanSpace ℝ (Fin 2)) := convexHull ℝ ((insert cp ({a, b} :
    Finset (EuclideanSpace ℝ (Fin 2))) : Finset _) : Set (EuclideanSpace ℝ (Fin 2))) ∪
    convexHull ℝ ((insert cm ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) : Finset _) :
    Set (EuclideanSpace ℝ (Fin 2))) with hH₁
  have hballH : ∀ z ∈ ball x₁ (min εp εm), z ∈ H₁ := by
    intro z hz
    rcases le_or_gt 0 (f (z - x₁)) with h | h
    · exact Or.inl (hbp z (ball_subset_ball (min_le_left _ _) hz) (by rw [hfcp, mul_one]; exact h))
    · exact Or.inr (hbm z (ball_subset_ball (min_le_right _ _) hz) (by nlinarith))
  have hH₁R : ∀ z ∈ H₁, z ∈ Rc.space := by
    rintro z (hz | hz)
    · exact hhull hτp z hz
    · exact hhull hτm z hz
  have hx₂H₁ : x₂ ∉ H₁ := by
    have hnot : ∀ {c : EuclideanSpace ℝ (Fin 2)},
        insert c ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) ∈ R.faces →
        x₂ ∉ convexHull ℝ ((insert c ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) :
          Finset _) : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro c hτ h
      have hs := face_subset_of_mem_openSimplex_of_mem_convexHull R hσ₂ hτ hx₂ h
      have h3 : (insert c ({a, b} : Finset (EuclideanSpace ℝ (Fin 2)))).card ≤ 3 := by
        have hh := (R.indep hτ).card_le_finrank_succ
        have h2' := Submodule.finrank_le
          (vectorSpan ℝ (Set.range ((↑) : (insert c ({a, b} : Finset _) : Finset _) →
            EuclideanSpace ℝ (Fin 2))))
        rw [Fintype.card_coe] at hh
        rw [finrank_euclideanSpace_fin] at h2'
        omega
      have heq := Finset.eq_of_subset_of_card_le hs (by rw [h3₂]; exact h3)
      exact haσ₂ (by rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self a {b}))
    rintro (h | h)
    · exact hnot hτp h
    · exact hnot hτm h
  have hx₁σ₂ : x₁ ∉ convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro h
    have hs := face_subset_of_mem_openSimplex_of_mem_convexHull R hσ₁ hσ₂ hx₁ h
    exact haσ₂ (hs (Finset.mem_insert_self a {b}))
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp (by rw [hint hσ₂ h3₂]; exact hx₂))
  obtain ⟨ε₃, hε₃, hfar₃⟩ := hfarpt ((hclosed _).union (hclosed _)) hx₂H₁
  obtain ⟨ε₄, hε₄, hfar₄⟩ := hfarpt (hclosed σ₂) hx₁σ₂
  have hd12 : 0 < dist x₁ x₂ := dist_pos.mpr hne
  obtain ⟨ρ', hρ'pos, hρ1, hρ2, hρ3, hρ4, hρ5⟩ : ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ min εp εm ∧
      ρ' ≤ ε₂ ∧ ρ' ≤ ε₃ ∧ ρ' ≤ ε₄ ∧ ρ' ≤ dist x₁ x₂ / 2 :=
    ⟨min (min (min εp εm) ε₂) (min (min ε₃ ε₄) (dist x₁ x₂ / 2)),
      lt_min (lt_min (lt_min hεp hεm) hε₂) (lt_min (lt_min hε₃ hε₄) (half_pos hd12)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  have hballs : Disjoint (ball x₁ ρ') (ball x₂ ρ') := Metric.ball_disjoint_ball (by linarith)
  obtain ⟨Osep, hOsep, hyOsep, hsep⟩ :=
    exists_isOpen_inter_preimage_subset_ball_union hS hgc hfib hρ'pos
  have hycell : ∃ c ∈ wallSystemCells Q, y ∈ wallSystemCellInt ρ c := by
    have hcov := iUnion_wallSystemCell_eq_univ hsys.rangeEq hsys.memCell
    have hy : y ∈ ⋃ c ∈ wallSystemCells Q, wallSystemCell ρ c := by
      rw [hcov]
      exact mem_univ y
    obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.mp hy
    refine ⟨c, hc, ?_⟩
    by_contra hni
    obtain ⟨w', hw', hyw'⟩ :=
      mem_iUnion₂.mp (wallSystemCell_sdiff_subset_iUnion_wall hc ⟨hyc, hni⟩)
    exact hnowall w' hw' hyw'
  obtain ⟨c, hc, hyc⟩ := hycell
  have hcint : IsOpen (wallSystemCellInt ρ c) :=
    isOpen_wallSystemCellInt hsys.finiteFaces hsys.continuous hsys.rangeEq hsys.dimLe hc
  have hBdc : IsClosed BdM := hsys.isClosed_physicalBoundary
  set O : Set M := wallSystemCellInt ρ c ∩ interior (Eb i₀) ∩ BdMᶜ with hO
  have hOo : IsOpen O := (hcint.inter isOpen_interior).inter hBdc.isOpen_compl
  obtain ⟨r, hr, hsmall⟩ := exists_pos_chartBlock_subset_of_isOpen ec A hysrc hA0
    (hOo.inter hOsep) ⟨⟨⟨hyc, hyE⟩, hyB⟩, hyOsep⟩
  obtain ⟨hbox, hcpt, hsrcl, -⟩ := hsmall r (-r) hr le_rfl le_rfl
  obtain ⟨ΦG, hΦG⟩ := exists_homeomorph_apply_eq_sub G x₁
  obtain ⟨Ψ, hΨ⟩ := exists_homeomorph_kinkShear μ μ'
  obtain ⟨Φ₂, hΦ₂⟩ := exists_homeomorph_apply_eq_sub F₂ x₂
  have hr0 : -r ≠ 0 := neg_ne_zero.mpr hr.ne'
  have hpoly : ∀ {σ : Finset (EuclideanSpace ℝ (Fin 2))}, σ ∈ R.faces →
      IsHPolytope (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    fun hσ => isHPolytope_convexHull_of_affineIndependent _ (R.indep hσ)
  have hpa0 : IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
    (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ) (0 : ℝ)) isOpen_univ).congr
      fun _ _ => rfl
  have hpam : IsPiecewiseAffineOn (fun q : ℝ × ℝ => max q.2 0) univ :=
    (isPiecewiseAffineOn_add_mul_max (AffineMap.const ℝ (ℝ × ℝ) (0 : ℝ))
      (LinearMap.snd ℝ ℝ ℝ).toAffineMap 1).congr fun q _ => by simp
  have hAbent : ∀ z ∈ H₁, A (ec (g z)) = (max (G (z - x₁)).2 0,
      (G (z - x₁)).1 - μ' * (G (z - x₁)).2 - μ * max (G (z - x₁)).2 0, (G (z - x₁)).2) := by
    intro z hz
    rw [hbent z hz, hAb]
  have hpl₁ : IsPiecewiseAffineOn (fun z => A (ec (g z))) H₁ := by
    refine IsPiecewiseAffineOn.union_of_isClosed ?_ ?_ (hclosed _) (hclosed _)
    · refine (isPiecewiseAffineOn_of_affine_of_isHPolytope (A.toAffineMap.comp Ap)
        (hpoly hτp)).congr fun z hz => ?_
      simp only [AffineMap.comp_apply]
      rw [(hgR z (hhull hτp z hz)).2, hAp hz]
      rfl
    · refine (isPiecewiseAffineOn_of_affine_of_isHPolytope (A.toAffineMap.comp Am)
        (hpoly hτm)).congr fun z hz => ?_
      simp only [AffineMap.comp_apply]
      rw [(hgR z (hhull hτm z hz)).2, hAm hz]
      rfl
  have hpl₂ : IsPiecewiseAffineOn (fun z => A (ec (g z)))
      (convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2)))) := by
    refine (isPiecewiseAffineOn_of_affine_of_isHPolytope (A.toAffineMap.comp A₂)
      (hpoly hσ₂)).congr fun z hz => ?_
    simp only [AffineMap.comp_apply]
    rw [(hgR z (hhull hσ₂ z hz)).2, hA₂ hz]
    rfl
  have hgraph₁ : ∀ z ∈ H₁, (A (ec (g z))).1 =
      (fun q : ℝ × ℝ => max q.2 0) ((A (ec (g z))).2.1, (A (ec (g z))).2.2) := by
    intro z hz
    rw [hAbent z hz]
  have hgraph₂ : ∀ z ∈ convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2))),
      (A (ec (g z))).2.1 = (fun _ : ℝ × ℝ => (0 : ℝ)) ((A (ec (g z))).1, (A (ec (g z))).2.2) := by
    intro z hz
    rw [hec₂ z hz, hA2]
  have hΦ₁ : ∃ Φ : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ,
      (∀ z ∈ H₁, blockSheetProjA ec A g z = Φ z) ∧
        ∀ z ∈ ball x₁ ρ', (z ∈ S ↔ (-r = 0 → 0 ≤ (Φ z).2)) := by
    refine ⟨ΦG.trans Ψ, fun z hz => ?_, fun z hz => ⟨fun _ h => absurd h hr0,
      fun _ => hRS (hH₁R z (hballH z (ball_subset_ball hρ1 hz)))⟩⟩
    simp only [blockSheetProjA, Homeomorph.trans_apply]
    rw [hAbent z hz, hΦG, hΨ]
  have hΦ₂' : ∃ Φ : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ,
      (∀ z ∈ convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2))), blockSheetProjB ec A g z = Φ z) ∧
        ∀ z ∈ ball x₂ ρ', (z ∈ S ↔ (-r = 0 → 0 ≤ (Φ z).2)) := by
    refine ⟨Φ₂, fun z hz => ?_, fun z hz => ⟨fun _ h => absurd h hr0,
      fun _ => hRS (hhull hσ₂ z (hb₂ (ball_subset_ball hρ2 hz)))⟩⟩
    simp only [blockSheetProjB]
    rw [hec₂ z hz, hA2, hΦ₂]
  have hblk := isStableCrossingBlock_of_sheets (ℓ := ℓ) (BdM := BdM) hr one_pos le_rfl le_rfl
    (by norm_num) hcpt hsrcl
    (Or.inl ⟨rfl, Set.disjoint_of_subset_left (hbox.trans inter_subset_left)
      (Set.disjoint_left.mpr fun z hz hzB => hz.2 hzB)⟩)
    (fun h => absurd h hr0) hgc hbox (fun z hz => hsep ⟨hz.1, hz.2.2⟩) hballs
    (fun z hz => hRS (hH₁R z hz)) (fun z hz => hRS (hhull hσ₂ z hz))
    (fun z hz => hballH z (ball_subset_ball hρ1 hz.2))
    (fun z hz => hb₂ (ball_subset_ball hρ2 hz.2))
    (hfar₃.mono_right (ball_subset_ball hρ3)) (hfar₄.mono_right (ball_subset_ball hρ4))
    ((hpoly hτp).isPolyhedron.union (hpoly hτm).isPolyhedron) (hpoly hσ₂).isPolyhedron
    (fun z hz => (hgR z (hH₁R z hz)).1) (fun z hz => (hgR z (hhull hσ₂ z hz)).1) hpl₁ hpl₂
    hgraph₁ hgraph₂ hΦ₁ hΦ₂' (fun _ _ _ => by simp) (fun _ _ _ => by simp) hpam hpa0
  have hbc : chartBlock ec A r (-r) ⊆ wallSystemCellInt ρ c := fun z hz => (hbox hz).1.1.1
  exact ⟨A, r, -r, _, _, _, _, 0, 0, ⟨hblk, Set.disjoint_of_subset_left hbc
    (disjoint_wallSystemCellInt_wallSystemSkeleton hc), Or.inl ⟨c, hc, rfl, hbc⟩⟩,
    fun z hz => interior_subset (hbox hz).1.1.2, hA0, Or.inl rfl⟩

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
