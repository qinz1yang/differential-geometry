/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GenericDoublePointSheets
import DifferentialGeometry.Topology.PiecewiseLinear.SheetBlockAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.BlockCoordinateAlgebra
import DifferentialGeometry.Topology.PiecewiseLinear.WallChartLocalPicture

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_apply_eq_apply_ne_zero {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (hEF : Module.finrank ℝ F < Module.finrank ℝ E + Module.finrank ℝ E) {L₁ L₂ : E →ₗ[ℝ] F}
    (h₁ : Function.Injective L₁) (h₂ : Function.Injective L₂) :
    ∃ ζ₁ ζ₂ : E, L₁ ζ₁ = L₂ ζ₂ ∧ L₁ ζ₁ ≠ 0 := by
  let Ψ : E × E →ₗ[ℝ] F := L₁.coprod (-L₂)
  have hker : LinearMap.ker Ψ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rw [Module.finrank_prod]; exact hEF)
  obtain ⟨⟨ζ₁, ζ₂⟩, hmem, hne⟩ := Submodule.ne_bot_iff _ |>.mp hker
  have heq : L₁ ζ₁ = L₂ ζ₂ := by
    have h : Ψ (ζ₁, ζ₂) = 0 := hmem
    simp only [Ψ, LinearMap.coprod_apply, LinearMap.neg_apply] at h
    exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h)
  refine ⟨ζ₁, ζ₂, heq, fun h0 => hne ?_⟩
  have hζ₁ : ζ₁ = 0 := h₁ (by rw [h0, map_zero])
  have hζ₂ : ζ₂ = 0 := h₂ (by rw [← heq, h0, map_zero])
  rw [hζ₁, hζ₂]
  rfl

section Ambient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

theorem IsCommonWallSystem.isClosed_physicalBoundary {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {Cf Bf : Set (Finset Ea)} {BdM C : Set M} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb Eb' : ι → Set M}
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ec ℓ Eb Eb') : IsClosed BdM := by
  rw [hsys.eqBd]
  exact Set.Finite.isClosed_biUnion (hsys.finiteFaces.subset fun w hw => (hsys.facesBd hw).1)
    fun w _ => isClosed_wallSystemCell hsys.continuous w

open Classical in
theorem exists_wallProductBlock_of_triangle_crossing {BdM C : Set M} {ι : Type}
    (ecf : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓf : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) (Eb Eb' : ι → Set M)
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)} (i₀ : ι)
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ecf ℓf Eb Eb')
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : IsCompact S) (hgc : ContinuousOn g S)
    {R Ac Lc Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hsub : IsSubdivision R Rc) (hRS : Rc.space ⊆ S)
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
    {σ₁ σ₂ : Finset (EuclideanSpace ℝ (Fin 2))} (hσ₁ : σ₁ ∈ R.faces) (hσ₂ : σ₂ ∈ R.faces)
    (h3₁ : σ₁.card = 3) (h3₂ : σ₂.card = 3) (hdisj : Disjoint σ₁ σ₂)
    (hfr₁ : ∀ v ∈ σ₁, v ∉ Ac.space) (hfr₂ : ∀ v ∈ σ₂, v ∉ Ac.space)
    (hx₁ : x₁ ∈ openSimplex σ₁) (hx₂ : x₂ ∈ openSimplex σ₂)
    (hyE : y ∈ interior (Eb i₀)) (hyskel : y ∉ wallSystemSkeleton Q ρ)
    (hcross : ∀ w ∈ wallSystemWalls Q, y ∈ wallSystemCell ρ w →
      ∃ cm ∈ wallSystemCells Q, ∃ cp ∈ wallSystemCells Q, cm ≠ cp ∧
        y ∈ wallSystemCell ρ cm ∧ y ∈ wallSystemCell ρ cp ∧
        ∀ U ∈ 𝓝 y, (doublePointSet g S ∩ U ∩ wallSystemCellInt ρ cm).Nonempty ∧
          (doublePointSet g S ∩ U ∩ wallSystemCellInt ρ cp).Nonempty) :
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
  obtain ⟨A₁, hA₁⟩ := exists_affineMap_eqOn_simplicialMap R φ hσ₁
  obtain ⟨A₂, hA₂⟩ := exists_affineMap_eqOn_simplicialMap R φ hσ₂
  have hL₁ := hinjA hσ₁ h3₁ hfr₁ hA₁ hx₁
  have hL₂ := hinjA hσ₂ h3₂ hfr₂ hA₂ hx₂
  have hx₁h := openSimplex_subset_convexHull σ₁ hx₁
  have hx₂h := openSimplex_subset_convexHull σ₂ hx₂
  have hRx₁ : x₁ ∈ Rc.space := hhull hσ₁ x₁ hx₁h
  have hRx₂ : x₂ ∈ Rc.space := hhull hσ₂ x₂ hx₂h
  have hysrc : y ∈ ec.source := hgx₁ ▸ (hgR x₁ hRx₁).1
  have hy'₁ : A₁ x₁ = ec y := by rw [← hA₁ hx₁h, ← (hgR x₁ hRx₁).2, hgx₁]
  have hy'₂ : A₂ x₂ = ec y := by rw [← hA₂ hx₂h, ← (hgR x₂ hRx₂).2, hgx₂]
  have hec₁ : ∀ z ∈ convexHull ℝ (σ₁ : Set (EuclideanSpace ℝ (Fin 2))),
      ec (g z) = ec y + A₁.linear (z - x₁) := fun z hz => by
    rw [(hgR z (hhull hσ₁ z hz)).2, hA₁ hz, hAform A₁ x₁ z, hy'₁]
  have hec₂ : ∀ z ∈ convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2))),
      ec (g z) = ec y + A₂.linear (z - x₂) := fun z hz => by
    rw [(hgR z (hhull hσ₂ z hz)).2, hA₂ hz, hAform A₂ x₂ z, hy'₂]
  obtain ⟨v₀, hv₀⟩ := R.nonempty_of_mem_faces hσ₂
  have hv₀σ₁ : v₀ ∉ σ₁ := fun h => Finset.disjoint_left.mp hdisj h hv₀
  have hz : A₂.linear (v₀ - x₂) ∉ LinearMap.range A₁.linear := by
    rintro ⟨ζ, hζ⟩
    have hnot : ¬ σ₁ ⊆ Bv :=
      not_subset_boundaryVertices_of_card_eq_three hsub hRS hLspace hBvL hpzero hσ₁ h3₁
    obtain ⟨u, hu, huB⟩ := Finset.not_subset.mp hnot
    have hind4 : AffineIndependent ℝ
        (fun u : (insert v₀ σ₁ : Finset _) => φ (u : EuclideanSpace ℝ (Fin 2))) := by
      refine affineIndependent_of_wallGuard hℓ0 hguard ?_ ?_ ?_ ?_
      · rw [Finset.coe_insert]
        exact insert_subset (hvert hσ₂ (Finset.mem_coe.mpr hv₀)) (hvert hσ₁)
      · rw [Finset.card_insert_of_notMem hv₀σ₁, h3₁]
      · have hlt : (insert v₀ σ₁ ∩ Bv).card < (insert v₀ σ₁).card := by
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨Finset.inter_subset_left, fun h => huB ?_⟩)
          have hmem : u ∈ insert v₀ σ₁ ∩ Bv := by
            rw [h]
            exact Finset.mem_insert_of_mem hu
          exact (Finset.mem_inter.mp hmem).2
        rw [Finset.card_insert_of_notMem hv₀σ₁, h3₁] at hlt
        omega
      · intro u' hu'
        rcases Finset.mem_insert.mp hu' with rfl | h
        · exact hfr₂ _ hv₀
        · exact hfr₁ u' h
    refine not_affineIndependent_insert_of_mem_range (R.indep hσ₁)
      (by rw [h3₁, finrank_euclideanSpace_fin]) (hvσ hσ₁ hA₁) hv₀σ₁ (z := x₁ + ζ) ?_ hind4
    rw [← hvσ hσ₂ hA₂ v₀ hv₀, hAform A₂ x₂ v₀, hy'₂, ← hζ, hAform A₁ x₁ (x₁ + ζ), hy'₁,
      add_sub_cancel_left]
  have hnhds : ∀ {σ : Finset (EuclideanSpace ℝ (Fin 2))} {x : EuclideanSpace ℝ (Fin 2)},
      σ ∈ R.faces → σ.card = 3 → x ∈ openSimplex σ →
        convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) ∈ 𝓝 x :=
    fun hσ h3 hx => mem_interior_iff_mem_nhds.mp (by rw [hint hσ h3]; exact hx)
  have hfarpt : ∀ {σ τ : Finset (EuclideanSpace ℝ (Fin 2))} {x : EuclideanSpace ℝ (Fin 2)},
      σ ∈ R.faces → τ ∈ R.faces → Disjoint σ τ → x ∈ openSimplex τ →
        ∃ ε > 0, Disjoint (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) (ball x ε) := by
    intro σ τ x hσ hτ hd hx
    have hxn : x ∉ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro h
      have hsub' := face_subset_of_mem_openSimplex_of_mem_convexHull R hτ hσ hx h
      obtain ⟨u, hu⟩ := R.nonempty_of_mem_faces hτ
      exact Finset.disjoint_left.mp hd (hsub' hu) hu
    have hcl : IsClosed (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) :=
      (σ.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hcl.isOpen_compl x hxn
    exact ⟨ε, hε, Set.disjoint_left.mpr fun z hz hzb => hball hzb hz⟩
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhds_iff.mp (hnhds hσ₁ h3₁ hx₁)
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhds_iff.mp (hnhds hσ₂ h3₂ hx₂)
  obtain ⟨ε₃, hε₃, hfar₃⟩ := hfarpt hσ₁ hσ₂ hdisj hx₂
  obtain ⟨ε₄, hε₄, hfar₄⟩ := hfarpt hσ₂ hσ₁ hdisj.symm hx₁
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
  have hloc₁ : S ∩ ball x₁ ρ' ⊆ convexHull ℝ (σ₁ : Set (EuclideanSpace ℝ (Fin 2))) :=
    fun z hz => hb₁ (ball_subset_ball hρ1 hz.2)
  have hloc₂ : S ∩ ball x₂ ρ' ⊆ convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2))) :=
    fun z hz => hb₂ (ball_subset_ball hρ2 hz.2)
  have hfar₁ : Disjoint (convexHull ℝ (σ₁ : Set (EuclideanSpace ℝ (Fin 2)))) (ball x₂ ρ') :=
    hfar₃.mono_right (ball_subset_ball hρ3)
  have hfar₂ : Disjoint (convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2)))) (ball x₁ ρ') :=
    hfar₄.mono_right (ball_subset_ball hρ4)
  obtain ⟨Osep, hOsep, hyOsep, hsep⟩ :=
    exists_isOpen_inter_preimage_subset_ball_union hS hgc hfib hρ'pos
  have hyB : y ∉ BdM := by
    intro hyB
    have h0 : ℓ (ec y) = 0 := (hsys.chartBd i₀ y hysrc).mp hyB
    rw [← hgx₁, (hgR x₁ hRx₁).2] at h0
    have hL := (hpzero x₁ hRx₁).mp h0
    rw [hLspace] at hL
    have hint₁ : x₁ ∈ interior S :=
      interior_mono (fun z hz => hRS (hhull hσ₁ z hz)) (by rw [hint hσ₁ h3₁]; exact hx₁)
    exact hL.2.2 hint₁
  have hBdc : IsClosed BdM := hsys.isClosed_physicalBoundary
  have hpoly : ∀ {σ : Finset (EuclideanSpace ℝ (Fin 2))}, σ ∈ R.faces →
      IsHPolytope (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    fun hσ => isHPolytope_convexHull_of_affineIndependent _ (R.indep hσ)
  have hpa : IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
    (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ) (0 : ℝ)) isOpen_univ).congr
      fun _ _ => rfl
  have assemble : ∀ (ν : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (O : Set M),
      (∃ ζ₁ ζ₂, A₁.linear ζ₁ = A₂.linear ζ₂ ∧ ν (A₁.linear ζ₁) ≠ 0) → IsOpen O → y ∈ O →
      Disjoint O BdM →
      ∃ (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r : ℝ), 0 < r ∧
        IsStableCrossingBlock g S ec ℓ BdM A r (-r)
          (convexHull ℝ (σ₁ : Set (EuclideanSpace ℝ (Fin 2))) ∩ g ⁻¹' chartBlock ec A r (-r))
          (convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2))) ∩ g ⁻¹' chartBlock ec A r (-r))
          (fun _ => 0) (fun _ => 0) 0 0 1 ∧
        chartBlock ec A r (-r) ⊆ O ∧ (∀ q, (A q).2.2 = ν (q - ec y)) ∧ A (ec y) = 0 ∧
        ∀ q ∈ blockBox r (-r), ∃ z ∈ chartBlock ec A r (-r), A (ec z) = q := by
    intro ν O hν hO hyO hOB
    obtain ⟨A, F₁, F₂, hAν, hAF₁, hAF₂⟩ := exists_affineEquiv_flatSheets
      finrank_euclideanSpace_fin finrank_euclideanSpace_fin hL₁ hL₂ hz hν (ec y)
    have hA0 : A (ec y) = 0 := by
      have h := hAF₁ 0
      simp only [map_zero, add_zero] at h
      rw [h]
      rfl
    obtain ⟨r, hr, hsmall⟩ := exists_pos_chartBlock_subset_of_isOpen ec A hysrc hA0
      (hO.inter hOsep) ⟨hyO, hyOsep⟩
    obtain ⟨hbox, hcpt, hsrcl, hpts⟩ := hsmall r (-r) hr le_rfl le_rfl
    obtain ⟨Φ₁, hΦ₁⟩ := exists_homeomorph_apply_eq_sub F₁ x₁
    obtain ⟨Φ₂, hΦ₂⟩ := exists_homeomorph_apply_eq_sub F₂ x₂
    have hr0 : -r ≠ 0 := neg_ne_zero.mpr hr.ne'
    refine ⟨A, r, hr, isStableCrossingBlock_of_sheets hr one_pos le_rfl le_rfl (by norm_num)
      hcpt hsrcl (Or.inl ⟨rfl, Set.disjoint_of_subset_left (hbox.trans inter_subset_left) hOB⟩)
      (fun h => absurd h hr0) hgc hbox (fun z hz => hsep ⟨hz.1, hz.2.2⟩) hballs
      (fun z hz => hRS (hhull hσ₁ z hz)) (fun z hz => hRS (hhull hσ₂ z hz)) hloc₁ hloc₂
      hfar₁ hfar₂ (hpoly hσ₁).isPolyhedron (hpoly hσ₂).isPolyhedron
      (fun z hz => (hgR z (hhull hσ₁ z hz)).1) (fun z hz => (hgR z (hhull hσ₂ z hz)).1)
      ?_ ?_ ?_ ?_ ?_ ?_ (fun _ _ _ => by simp) (fun _ _ _ => by simp) hpa hpa,
      hbox.trans inter_subset_left, hAν, hA0, hpts⟩
    · refine (isPiecewiseAffineOn_of_affine_of_isHPolytope (A.toAffineMap.comp A₁)
        (hpoly hσ₁)).congr fun z hz => ?_
      simp only [AffineMap.comp_apply]
      rw [(hgR z (hhull hσ₁ z hz)).2, hA₁ hz]
      rfl
    · refine (isPiecewiseAffineOn_of_affine_of_isHPolytope (A.toAffineMap.comp A₂)
        (hpoly hσ₂)).congr fun z hz => ?_
      simp only [AffineMap.comp_apply]
      rw [(hgR z (hhull hσ₂ z hz)).2, hA₂ hz]
      rfl
    · intro z hz
      rw [hec₁ z hz, hAF₁]
    · intro z hz
      rw [hec₂ z hz, hAF₂]
    · refine ⟨Φ₁, fun z hz => ?_, fun z hz => ⟨fun _ h => absurd h hr0,
        fun _ => hRS (hhull hσ₁ z (hb₁ (ball_subset_ball hρ1 hz)))⟩⟩
      simp only [blockSheetProjA]
      rw [hec₁ z hz, hAF₁, hΦ₁]
    · refine ⟨Φ₂, fun z hz => ?_, fun z hz => ⟨fun _ h => absurd h hr0,
        fun _ => hRS (hhull hσ₂ z (hb₂ (ball_subset_ball hρ2 hz)))⟩⟩
      simp only [blockSheetProjB]
      rw [hec₂ z hz, hAF₂, hΦ₂]
  by_cases hwall : ∃ w ∈ wallSystemWalls Q, y ∈ wallSystemCell ρ w
  · obtain ⟨w, hw, hyw⟩ := hwall
    obtain ⟨cm, hcm, cp, hcp, hcmp, hwm, hwp, ν, U, hU, hyU, -, hUcov, -, hUwalls, hUskel,
      hUzero, hUm, hUp, hUintm, hUintp⟩ :=
      hsys.exists_wallChart_sides i₀ hw hyw hyskel (interior_subset hyE)
    have hνy : ν (ec y) = 0 := (hUzero y hyU).mp hyw
    have hνform : ∀ q, ν q = ν.linear (q - ec y) := by
      intro q
      have h := ν.linearMap_vsub q (ec y)
      rw [vsub_eq_sub, vsub_eq_sub, hνy, sub_zero] at h
      exact h.symm
    have hywInt : y ∈ wallSystemCellInt ρ w := by
      by_contra h
      exact hyskel (wallSystemCell_sdiff_subset_wallSystemSkeleton hw ⟨hyw, h⟩)
    have htrans : ∃ ζ₁ ζ₂, A₁.linear ζ₁ = A₂.linear ζ₂ ∧ ν.linear (A₁.linear ζ₁) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨cm', hcm', _, _, _, hycm', _, hacc⟩ := hcross w hw hyw
      obtain ⟨y'', ⟨hyd, hyOs, hyU''⟩, hyint⟩ :=
        (hacc _ (Filter.inter_mem (hOsep.mem_nhds hyOsep) (hU.mem_nhds hyU))).1
      obtain ⟨z₁, hz₁S, z₂, hz₂S, hz12, hgz₁, hgz₂⟩ := hyd
      have hball : ∀ z ∈ S, g z = y'' →
          (z ∈ convexHull ℝ (σ₁ : Set (EuclideanSpace ℝ (Fin 2))) ∧
            ec y'' = ec y + A₁.linear (z - x₁)) ∨
          (z ∈ convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2))) ∧
            ec y'' = ec y + A₂.linear (z - x₂)) := by
        intro z hzS hgz
        rcases hsep ⟨hzS, by rw [mem_preimage, hgz]; exact hyOs⟩ with h | h
        · have hzh := hloc₁ ⟨hzS, h⟩
          exact Or.inl ⟨hzh, by rw [← hgz, hec₁ z hzh]⟩
        · have hzh := hloc₂ ⟨hzS, h⟩
          exact Or.inr ⟨hzh, by rw [← hgz, hec₂ z hzh]⟩
      have hcontra : ∀ {z z' : EuclideanSpace ℝ (Fin 2)},
          ec y'' = ec y + A₁.linear (z - x₁) → ec y'' = ec y + A₂.linear (z' - x₂) →
            False := by
        intro z z' h1 h2
        have hL : A₁.linear (z - x₁) = A₂.linear (z' - x₂) :=
          add_left_cancel (h1.symm.trans h2)
        have hνy'' : ν (ec y'') = 0 := by
          rw [hνform, h1, add_sub_cancel_left]
          exact hcon _ _ hL
        have hy''w : y'' ∈ wallSystemCell ρ w := (hUzero y'' hyU'').mpr hνy''
        have hsub' := face_subset_of_mem_openSimplex_of_mem_convexHull Q hcm'.1 hw.1 hyint hy''w
        have h4 : cm'.card = 4 := hcm'.2
        have h3 : w.card = 3 := hw.2
        have := Finset.card_le_card hsub'
        omega
      rcases hball z₁ hz₁S hgz₁ with ⟨-, e1⟩ | ⟨-, e1⟩ <;>
        rcases hball z₂ hz₂S hgz₂ with ⟨-, e2⟩ | ⟨-, e2⟩
      · exact hz12 (sub_left_inj.mp (hL₁ (add_left_cancel (e1.symm.trans e2))))
      · exact hcontra e1 e2
      · exact hcontra e2 e1
      · exact hz12 (sub_left_inj.mp (hL₂ (add_left_cancel (e1.symm.trans e2))))
    obtain ⟨A, r, hr, hblk, hbox, hAν, hA0, hpts⟩ := assemble ν.linear
      (U ∩ interior (Eb i₀) ∩ BdMᶜ) htrans ((hU.inter isOpen_interior).inter hBdc.isOpen_compl)
      ⟨⟨hyU, hyE⟩, hyB⟩ (Set.disjoint_left.mpr fun z hz hzB => hz.2 hzB)
    have hAt : ∀ z, (A (ec z)).2.2 = ν (ec z) := fun z => by rw [hAν, hνform]
    have hbU : chartBlock ec A r (-r) ⊆ U := fun z hz => (hbox hz).1.1
    have hmid : ∀ s : ℝ, |s| ≤ r → ((0 : ℝ), (0 : ℝ), s) ∈ blockBox r (-r) := by
      intro s hs
      refine ⟨by simp only [abs_zero]; exact hr.le, by simp only [abs_zero]; exact hr.le,
        (abs_le.mp hs).1, (abs_le.mp hs).2⟩
    refine ⟨A, r, -r, _, _, _, _, 0, 0, ⟨hblk, Set.disjoint_of_subset_left hbU hUskel,
      Or.inr (Or.inl ⟨w, hw, cm, hcm, cp, hcp, rfl, hcmp, hwm, hwp, hbU.trans hUcov, ?_, ?_,
        fun w' hw' z hz => hUwalls w' hw' ⟨hbU hz.1, hz.2⟩,
        fun z hz => by rw [hAt z]; exact hUzero z (hbU hz),
        fun z hz => by rw [hAt z]; exact hUm z ⟨hbU hz.1, hz.2⟩,
        fun z hz => by rw [hAt z]; exact hUp z ⟨hbU hz.1, hz.2⟩⟩)⟩,
      fun z hz => interior_subset (hbox hz).1.2, hA0, Or.inl rfl⟩
    · obtain ⟨z, hz, hAz⟩ := hpts _
        (hmid (-(r / 2)) (by rw [abs_neg, abs_of_pos (half_pos hr)]; linarith))
      refine ⟨z, hz, hUintm z (hbU hz) ?_⟩
      rw [← hAt z, hAz]
      linarith
    · obtain ⟨z, hz, hAz⟩ := hpts _ (hmid (r / 2) (by rw [abs_of_pos (half_pos hr)]; linarith))
      refine ⟨z, hz, hUintp z (hbU hz) ?_⟩
      rw [← hAt z, hAz]
      linarith
  · have hycell : ∃ c ∈ wallSystemCells Q, y ∈ wallSystemCellInt ρ c := by
      have hcov := iUnion_wallSystemCell_eq_univ hsys.rangeEq hsys.memCell
      have hy : y ∈ ⋃ c ∈ wallSystemCells Q, wallSystemCell ρ c := by
        rw [hcov]
        exact mem_univ y
      obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.mp hy
      refine ⟨c, hc, ?_⟩
      by_contra hni
      obtain ⟨w, hw, hyw⟩ :=
        mem_iUnion₂.mp (wallSystemCell_sdiff_subset_iUnion_wall hc ⟨hyc, hni⟩)
      exact hwall ⟨w, hw, hyw⟩
    obtain ⟨c, hc, hyc⟩ := hycell
    obtain ⟨ζ₁, ζ₂, hζ, hζ0⟩ := exists_apply_eq_apply_ne_zero
      (by rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]; norm_num) hL₁ hL₂
    obtain ⟨ν, hν⟩ := Module.Projective.exists_dual_ne_zero ℝ hζ0
    have hcint : IsOpen (wallSystemCellInt ρ c) :=
      isOpen_wallSystemCellInt hsys.finiteFaces hsys.continuous hsys.rangeEq hsys.dimLe hc
    obtain ⟨A, r, hr, hblk, hbox, -, hA0, -⟩ := assemble ν
      (wallSystemCellInt ρ c ∩ interior (Eb i₀) ∩ BdMᶜ) ⟨ζ₁, ζ₂, hζ, hν⟩
      ((hcint.inter isOpen_interior).inter hBdc.isOpen_compl) ⟨⟨hyc, hyE⟩, hyB⟩
      (Set.disjoint_left.mpr fun z hz hzB => hz.2 hzB)
    have hbc : chartBlock ec A r (-r) ⊆ wallSystemCellInt ρ c := fun z hz => (hbox hz).1.1
    exact ⟨A, r, -r, _, _, _, _, 0, 0, ⟨hblk, Set.disjoint_of_subset_left hbc
      (disjoint_wallSystemCellInt_wallSystemSkeleton hc), Or.inl ⟨c, hc, rfl, hbc⟩⟩,
      fun z hz => interior_subset (hbox hz).1.2, hA0, Or.inl rfl⟩

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
