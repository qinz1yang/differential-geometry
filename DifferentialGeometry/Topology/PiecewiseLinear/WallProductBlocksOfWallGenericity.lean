/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.EdgeCrossingBlock
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryCrossingBlock
import DifferentialGeometry.Topology.PiecewiseLinear.GluedCellGlobalInvariants
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section MetricAmbient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

open Classical in
theorem wallProductBlocks_of_wallGenericity (D : SingularTwoCell M) {BdM C W V Kt : Set M}
    {ι : Type} (ecf : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓf : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) (Eb Eb' : ι → Set M)
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)}
    {ε κ : ℝ} (i₀ : ι)
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ecf ℓf Eb Eb')
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C) (hκ : 0 < κ)
    (hVopen : IsOpen V) (hVec : closure V ⊆ (ecf i₀).source) (hWV : closure W ⊆ V)
    (hWE : closure W ⊆ interior (Eb i₀))
    (Rc Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hRfin : Rc.faces.Finite) (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hsub : IsSubdivision R Rc) (hRsfin : R.faces.Finite) (hε : 0 < ε)
    (hBvL : ∀ v ∈ R.vertices, v ∈ Bv ↔ v ∈ Lc.space)
    (hsmall : ∀ x ∈ Rc.space, dist (simplicialMap R φ x) (ecf i₀ (D x)) < ε)
    (hpnonneg : ∀ x ∈ Rc.space, 0 ≤ ℓf i₀ (simplicialMap R φ x))
    (hpzero : ∀ x ∈ Rc.space, ℓf i₀ (simplicialMap R φ x) = 0 ↔ x ∈ Lc.space)
    (hfrozen : EqOn (simplicialMap R φ) (fun x => ecf i₀ (D x)) Ac.space)
    (hmaps : MapsTo (simplicialMap R φ) Rc.space (⇑(ecf i₀) '' V))
    (hD'K : regionGluedMap D (ecf i₀) R φ Rc '' Rc.space ⊆ Kt) (hKV : Kt ⊆ V)
    (hinj' : UniformInjectivityScale D.domain (regionGluedMap D (ecf i₀) R φ Rc) κ)
    (hgcont : ContinuousOn (regionGluedMap D (ecf i₀) R φ Rc) D.domain)
    (hgfiber : ∀ y,
      (D.domain ∩ regionGluedMap D (ecf i₀) R φ Rc ⁻¹' {y}).encard ≤ 2)
    (hguard : ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
      (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
        (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker (ℓf i₀)) + 1 →
        AffineIndependent ℝ
          (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
        AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))))
    (hfree : ∀ y ∈ closure W,
      FreeSourceGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain y)
    (hgenskel : ∀ y ∈ doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain,
      FreeSourceGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain y →
        y ∉ wallSystemSkeleton Q ρ)
    (hgenfold : ∀ y ∈ doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain,
      IsFreeDoubleGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain BdM y →
        ∀ σ ∈ R.faces, σ.card ≤ 2 →
          y ∈ regionGluedMap D (ecf i₀) R φ Rc ''
              (Rc.space ∩ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) →
            ∀ w ∈ wallSystemWalls Q, y ∉ wallSystemCell ρ w)
    (hgencross : ∀ y ∈ doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain,
      IsFreeInteriorDoubleGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain BdM y →
        ∀ w ∈ wallSystemWalls Q, y ∈ wallSystemCell ρ w →
          ∃ cm ∈ wallSystemCells Q, ∃ cp ∈ wallSystemCells Q, cm ≠ cp ∧
            y ∈ wallSystemCell ρ cm ∧ y ∈ wallSystemCell ρ cp ∧
            ∀ U ∈ 𝓝 y,
              (doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain ∩ U ∩
                wallSystemCellInt ρ cm).Nonempty ∧
              (doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain ∩ U ∩
                wallSystemCellInt ρ cp).Nonempty) :
    ∃ η' : ℝ, 0 < η' ∧
      HasWallProductBlocks (regionGluedMap D (ecf i₀) R φ Rc) D.domain ecf ℓf Eb BdM C
        Q ρ (closure W) η' := by
  let _ := hfiber
  let _ := hproper
  let _ := hVopen
  let _ := hWV
  let _ := hRfin
  let _ := hRV
  let _ := hε
  let _ := hsmall
  let _ := hfrozen
  let _ := hD'K
  let _ := hKV
  set g := regionGluedMap D (ecf i₀) R φ Rc with hgdef
  set S := D.domain with hSdef
  set ec := ecf i₀ with hecdef
  set ℓ := ℓf i₀ with hℓdef
  have hS : IsCompact S := D.isPLBall_domain.isPolyhedron.isCompact
  have hSball : closure (interior S) = S := D.isPLBall_domain.closure_interior
  have hRS : Rc.space ⊆ S := hRdom
  have hgR : ∀ z ∈ Rc.space, g z ∈ ec.source ∧ ec (g z) = simplicialMap R φ z := by
    intro z hz
    obtain ⟨v, hvV, hv⟩ := hmaps hz
    have hvs : v ∈ ec.source := hVec (subset_closure hvV)
    have ht : simplicialMap R φ z ∈ ec.target := hv ▸ ec.map_source hvs
    rw [hgdef, regionGluedMap_of_mem D ec R φ hz]
    exact ⟨ec.map_target ht, ec.right_inv ht⟩
  have hgC : MapsTo g S C := by
    intro x hx
    by_cases hxR : x ∈ Rc.space
    · obtain ⟨hs, he⟩ := hgR x hxR
      exact (hsys.chartC i₀ (g x) hs).mpr (by rw [he]; exact hpnonneg x hxR)
    · have hgx : g x = D x := by
        rw [hgdef]
        simp only [regionGluedMap, ite_eq_right hxR]
      rw [hgx]
      exact hmapC hx
  have hpinj : ∀ x ∈ Rc.space, ∀ z ∈ Rc.space, dist x z < κ →
      simplicialMap R φ x = simplicialMap R φ z → x = z := by
    intro x hx z hz hd hp
    refine hinj' x (hRS hx) z (hRS hz) hd ?_
    rw [hgdef, regionGluedMap_of_mem D ec R φ hx, regionGluedMap_of_mem D ec R φ hz, hp]
  have hint3 : ∀ {σ : Finset (EuclideanSpace ℝ (Fin 2))}, σ ∈ R.faces → σ.card = 3 →
      interior (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) = openSimplex σ :=
    fun hσ h3 => interior_convexHull_eq_openSimplex (R.indep hσ)
      (by rw [h3, finrank_euclideanSpace_fin])
  have key : ∀ y ∈ doublePointSet g S ∩ closure W,
      ∃ (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ)
        (SA SB : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ × ℝ → ℝ) (La Lb : ℝ),
        WallProductBlock g S ec ℓ BdM C Q ρ A r tlo SA SB a b La Lb 1 ∧
          chartBlock ec A r tlo ⊆ Eb i₀ ∧ A (ec y) = 0 ∧
            (tlo = -r ∨ (tlo = 0 ∧ ∀ q, (A q).2.2 = ℓ q)) := by
    rintro y ⟨hyd, hyW⟩
    obtain ⟨x₁, hx₁S, x₂, hx₂S, hne, hgx₁, hgx₂⟩ := hyd
    have hfib : ∀ x ∈ S, g x = y → x = x₁ ∨ x = x₂ := fun x hx hgx =>
      eq_or_eq_of_encard_le_two (hgfiber y) ⟨hx₁S, hgx₁⟩ ⟨hx₂S, hgx₂⟩ ⟨hx, hgx⟩ hne
    have hfr := hfree y hyW
    have hG₁ := hfr x₁ ⟨hx₁S, hgx₁⟩
    have hG₂ := hfr x₂ ⟨hx₂S, hgx₂⟩
    have hx₁R : x₁ ∈ R.space := mem_of_mem_nhdsWithin hx₁S hG₁.1
    have hx₂R : x₂ ∈ R.space := mem_of_mem_nhdsWithin hx₂S hG₂.1
    have hRx₁ : x₁ ∈ Rc.space := hsub.space_eq ▸ hx₁R
    have hRx₂ : x₂ ∈ Rc.space := hsub.space_eq ▸ hx₂R
    have hσ₁ := carrierFace_mem hx₁R
    have hσ₂ := carrierFace_mem hx₂R
    have hx₁o := mem_openSimplex_carrierFace hx₁R
    have hx₂o := mem_openSimplex_carrierFace hx₂R
    have hfr₁ := hG₁.2 _ hσ₁ (mem_convexHull_carrierFace hx₁R)
    have hfr₂ := hG₂.2 _ hσ₂ (mem_convexHull_carrierFace hx₂R)
    have hpeq : simplicialMap R φ x₁ = simplicialMap R φ x₂ := by
      rw [← (hgR x₁ hRx₁).2, ← (hgR x₂ hRx₂).2, hgx₁, hgx₂]
    have hyd : y ∈ doublePointSet g S := ⟨x₁, hx₁S, x₂, hx₂S, hne, hgx₁, hgx₂⟩
    obtain ⟨hdisj, hcases⟩ := faces_cases_of_simplicialMap_eq (hsys.normalNe i₀) hsub hRdom
      hLspace hBvL hpzero hguard hκ hpinj hσ₁ hσ₂ hfr₁ hfr₂ hx₁o hx₂o hne hpeq
    have hyskel : y ∉ wallSystemSkeleton Q ρ := hgenskel y hyd hfr
    have hyE : y ∈ interior (Eb i₀) := hWE hyW
    have hyB_of : ∀ {x : EuclideanSpace ℝ (Fin 2)} {σ : Finset (EuclideanSpace ℝ (Fin 2))},
        σ ∈ R.faces → σ.card = 3 → x ∈ openSimplex σ → x ∈ Rc.space → g x = y → y ∉ BdM := by
      intro x σ hσ h3 hx hxR hgx hyB
      have hxint : x ∈ interior S :=
        interior_mono (fun z hz => hRS (hsub.space_eq ▸ R.convexHull_subset_space hσ hz))
          (by rw [hint3 hσ h3]; exact hx)
      have h0 : ℓ (ec y) = 0 := (hsys.chartBd i₀ y (hgx ▸ (hgR x hxR).1)).mp hyB
      rw [← hgx, (hgR x hxR).2] at h0
      have hL := (hpzero x hxR).mp h0
      rw [hLspace] at hL
      exact hL.2.2 hxint
    rcases hcases with ⟨h3₁, h3₂⟩ | ⟨h2₁, h3₂⟩ | ⟨h3₁, h2₂⟩ | ⟨h2₁, h2₂, hB⟩
    · have hyB := hyB_of hσ₁ h3₁ hx₁o hRx₁ hgx₁
      have hinter : IsFreeInteriorDoubleGerm R Ac g S BdM y := by
        refine ⟨⟨hyB, hfr⟩, fun x hx => ?_⟩
        rcases hfib x hx.1 hx.2 with rfl | rfl
        · exact ⟨_, hσ₁, h3₁, by rw [hint3 hσ₁ h3₁]; exact hx₁o⟩
        · exact ⟨_, hσ₂, h3₂, by rw [hint3 hσ₂ h3₂]; exact hx₂o⟩
      exact exists_wallProductBlock_of_triangle_crossing ecf ℓf Eb Eb' i₀ hsys hS hgcont hsub hRS
        hLspace hBvL hpzero hguard hgR hne hgx₁ hgx₂ hfib hσ₁ hσ₂ h3₁ h3₂ hdisj hfr₁ hfr₂ hx₁o
        hx₂o hyE hyskel (hgencross y hyd hinter)
    · have hyB := hyB_of hσ₂ h3₂ hx₂o hRx₂ hgx₂
      have hnowall := hgenfold y hyd ⟨hyB, hfr⟩ _ hσ₁ h2₁.le
        ⟨x₁, ⟨hRx₁, mem_convexHull_carrierFace hx₁R⟩, hgx₁⟩
      exact exists_wallProductBlock_of_edge_crossing ecf ℓf Eb Eb' i₀ hsys hS hgcont hsub hRsfin
        hRS hLspace hBvL hpzero hguard hgR hne hgx₁ hgx₂ hfib hG₁.1 hG₁.2 hσ₁ hσ₂ h2₁ h3₂ hdisj
        hfr₂ hx₁o hx₂o hyE hnowall
    · have hyB := hyB_of hσ₁ h3₁ hx₁o hRx₁ hgx₁
      have hnowall := hgenfold y hyd ⟨hyB, hfr⟩ _ hσ₂ h2₂.le
        ⟨x₂, ⟨hRx₂, mem_convexHull_carrierFace hx₂R⟩, hgx₂⟩
      exact exists_wallProductBlock_of_edge_crossing ecf ℓf Eb Eb' i₀ hsys hS hgcont hsub hRsfin
        hRS hLspace hBvL hpzero hguard hgR hne.symm hgx₂ hgx₁
        (fun x hx hgx => (hfib x hx hgx).symm) hG₂.1 hG₂.2 hσ₂ hσ₁ h2₂ h3₁ hdisj.symm hfr₁ hx₂o
        hx₁o hyE hnowall
    · exact exists_wallProductBlock_of_boundary_crossing ecf ℓf Eb Eb' i₀ hsys hS hgcont hgC
        hSball hsub hRsfin hRS hLspace hBvL hpzero hguard hgR hne hgx₁ hgx₂ hfib hG₁.1 hG₂.1 hG₁.2
        hG₂.2 hσ₁ hσ₂ h2₁ h2₂ hdisj hB hx₁o hx₂o hyE hyskel
  have hloc : IsLocallyInjective (S.domRestrict g) := by
    intro x
    refine ⟨ball x (κ / 2), isOpen_ball, mem_ball_self (half_pos hκ), ?_⟩
    intro x₁ hx₁ x₂ hx₂ heq
    apply Subtype.ext
    refine hinj' x₁ x₁.2 x₂ x₂.2 ?_ heq
    have h1 : dist x₁ x₂ < κ := by
      calc dist x₁ x₂ ≤ dist x₁ x + dist x x₂ := dist_triangle _ _ _
        _ < κ / 2 + κ / 2 := by
          rw [dist_comm x x₂]
          exact add_lt_add (mem_ball.mp hx₁) (mem_ball.mp hx₂)
        _ = κ := by ring
    exact h1
  have hDPc : IsCompact (doublePointSet g S) :=
    isCompact_doublePointSet_of_isLocallyInjective hS hgcont hloc
  have hK : IsCompact (doublePointSet g S ∩ closure W) := hDPc.inter_right isClosed_closure
  have key' : ∀ y : ↥(doublePointSet g S ∩ closure W),
      ∃ (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ)
        (SA SB : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ × ℝ → ℝ) (La Lb : ℝ),
        WallProductBlock g S ec ℓ BdM C Q ρ A r tlo SA SB a b La Lb 1 ∧
          chartBlock ec A r tlo ⊆ Eb i₀ ∧
          (y : M) ∈ ec.source ∩ (fun z => A (ec z)) ⁻¹'
            {w | |w.1| < r / 2 ∧ |w.2.1| < r / 2 ∧ |w.2.2| < r / 2} ∧
          (tlo = -r ∨ (tlo = 0 ∧ ∀ q, (A q).2.2 = ℓ q)) := by
    rintro ⟨y, hy⟩
    obtain ⟨A, r, tlo, SA, SB, a, b, La, Lb, hwp, hEb, hA0, htlo⟩ := key y hy
    have hr : 0 < r := hwp.1.1
    have hysrc : y ∈ ec.source :=
      hsys.layerSource i₀ (hsys.layerSubset i₀ (interior_subset (hWE hy.2)))
    refine ⟨A, r, tlo, SA, SB, a, b, La, Lb, hwp, hEb, ⟨hysrc, ?_⟩, htlo⟩
    change |(A (ec y)).1| < r / 2 ∧ |(A (ec y)).2.1| < r / 2 ∧ |(A (ec y)).2.2| < r / 2
    rw [hA0]
    simp only [Prod.fst_zero, Prod.snd_zero, abs_zero]
    exact ⟨half_pos hr, half_pos hr, half_pos hr⟩
  choose A r tlo SA SB a b La Lb hwp hEb hmem htlo using key'
  let Wy : ↥(doublePointSet g S ∩ closure W) → Set M := fun y => ec.source ∩
    (fun z => A y (ec z)) ⁻¹' {w | |w.1| < r y / 2 ∧ |w.2.1| < r y / 2 ∧ |w.2.2| < r y / 2}
  have hWo : ∀ y, IsOpen (Wy y) := by
    intro y
    have hc : ContinuousOn (fun z => A y (ec z)) ec.source :=
      (A y).toAffineMap.continuous_of_finiteDimensional.comp_continuousOn ec.continuousOn
    exact hc.isOpen_inter_preimage ec.open_source
      ((isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
        ((isOpen_lt (continuous_abs.comp continuous_snd.fst) continuous_const).inter
          (isOpen_lt (continuous_abs.comp continuous_snd.snd) continuous_const)))
  have hWin : ∀ y, ∀ z ∈ doublePointSet g S ∩ Wy y,
      z ∈ innerChartBlock ec (A y) (r y) (tlo y) := by
    intro y z ⟨hzd, hzs, hz1, hz2, hz3⟩
    refine ⟨hzs, ?_⟩
    change |(A y (ec z)).1| ≤ r y / 2 ∧ |(A y (ec z)).2.1| ≤ r y / 2 ∧
      tlo y / 2 ≤ (A y (ec z)).2.2 ∧ (A y (ec z)).2.2 ≤ r y / 2
    rw [abs_lt] at hz3
    refine ⟨hz1.le, hz2.le, ?_, hz3.2.le⟩
    rcases htlo y with ht | ⟨ht, hAℓ⟩
    · rw [ht]
      linarith [hz3.1]
    · rw [ht, zero_div, hAℓ]
      obtain ⟨x, hx, -, -, -, hgx, -⟩ := hzd
      have hzC : z ∈ C := hgx ▸ hgC hx
      exact (hsys.chartC i₀ z hzs).mp hzC
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover Wy hWo fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hmem _⟩
  let p : Fin t.card → ↥(doublePointSet g S ∩ closure W) := fun i => (t.equivFin.symm i : ↥t)
  refine ⟨1, one_pos, one_pos, (⋃ y ∈ t, Wy y) ∪ (doublePointSet g S)ᶜ, t.card, fun _ => i₀,
    fun i => A (p i), fun i => r (p i), fun i => tlo (p i), fun i => SA (p i), fun i => SB (p i),
    fun i => a (p i), fun i => b (p i), fun i => La (p i), fun i => Lb (p i),
    (isOpen_biUnion fun y _ => hWo y).union hDPc.isClosed.isOpen_compl, ?_, ?_,
    fun i => hEb (p i), fun i => hwp (p i)⟩
  · intro z hz
    by_cases hzd : z ∈ doublePointSet g S
    · exact Or.inl (ht ⟨hzd, hz⟩)
    · exact Or.inr hzd
  · rintro z ⟨hzd, hzN | hzc⟩
    · obtain ⟨y, hyt, hzy⟩ := mem_iUnion₂.mp hzN
      refine mem_iUnion.mpr ⟨t.equivFin ⟨y, hyt⟩, ?_⟩
      have hp : p (t.equivFin ⟨y, hyt⟩) = y := by
        change ((t.equivFin.symm (t.equivFin ⟨y, hyt⟩) : ↥t) :
          ↥(doublePointSet g S ∩ closure W)) = y
        rw [Equiv.symm_apply_apply]
      change z ∈ innerChartBlock ec (A (p (t.equivFin ⟨y, hyt⟩)))
        (r (p (t.equivFin ⟨y, hyt⟩))) (tlo (p (t.equivFin ⟨y, hyt⟩)))
      rw [hp]
      exact hWin y z ⟨hzd, hzy⟩
    · exact absurd hzd hzc

end MetricAmbient

end DifferentialGeometry.Topology.PiecewiseLinear
