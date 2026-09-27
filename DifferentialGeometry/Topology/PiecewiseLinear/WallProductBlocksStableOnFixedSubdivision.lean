/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.WallProductBlockPerturbation

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

theorem WallProductBlock.exists_persistent_wallProductBlock [CompactSpace M] [T2Space M]
    {f : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb Eb' : ι → Set M} {BdM C Kt : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ} {y : M}
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ec ℓ Eb Eb') {j i₀ : ι}
    (h : WallProductBlock f S (ec j) (ℓ j) BdM C Q ρ A r tlo SA SB a b La Lb η)
    (hE : chartBlock (ec j) A r tlo ⊆ Eb j) (hyd : y ∈ doublePointSet f S)
    (hy : y ∈ innerChartBlock (ec j) A r tlo) (hfC : MapsTo f S C)
    (hKt : IsClosed Kt) (hKtE : Kt ⊆ interior (Eb i₀))
    {Ω Kc : Set (EuclideanSpace ℝ (Fin 2))} (hΩ : IsOpen Ω) (hKc : IsClosed Kc)
    (hKcΩ : Kc ⊆ Ω) :
    ∃ (k : ι) (A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r' tlo' : ℝ) (O : Set M),
      IsOpen O ∧ y ∈ O ∧ O ⊆ (ec k).source ∧
      (∀ z ∈ O, 0 ≤ ℓ k (ec k z) → z ∈ innerChartBlock (ec k) A' r' tlo') ∧
      chartBlock (ec k) A' r' tlo' ⊆ Eb k ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ (g : EuclideanSpace ℝ (Fin 2) → M)
          (δ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (lam : NNReal),
          (lam : ℝ) ≤ lam₀ → IsPiecewiseAffineOn δ univ → LipschitzWith lam δ →
          (∀ x ∈ S, g x ∉ Kt ∨ f x ∉ Kt → g x = f x) →
          (∀ x ∈ S, g x ∈ (ec i₀).source →
            f x ∈ (ec i₀).source ∧ ‖ec i₀ (g x) - ec i₀ (f x)‖ ≤ ε₀) →
          (∀ x ∈ S, x ∈ Ω → g x ∈ (ec i₀).source ∧ ec i₀ (g x) = ec i₀ (f x) + δ x) →
          (∀ x ∈ S, x ∉ Kc → g x = f x) →
          (∀ x ∈ S, g x ∈ (ec i₀).source →
            0 ≤ ℓ i₀ (ec i₀ (g x)) ∧ (x ∈ frontier S ↔ ℓ i₀ (ec i₀ (g x)) = 0)) →
          ∃ (SA' SB' : Set (EuclideanSpace ℝ (Fin 2))) (a' b' : ℝ × ℝ → ℝ) (La' Lb' : ℝ),
            WallProductBlock g S (ec k) (ℓ k) BdM C Q ρ A' r' tlo' SA' SB' a' b' La' Lb'
              (η / 2) := by
  classical
  obtain ⟨hstab, -, -⟩ := id h
  obtain ⟨hr, hη, -, -, -, -, -, hside, -⟩ := id hstab
  have htle : tlo ≤ 0 := by
    rcases hside with ⟨ht, -⟩ | ⟨ht, -⟩
    · linarith
    · exact ht.le
  have hyB : y ∈ chartBlock (ec j) A r tlo := chartBlock_mono_of_half (ec j) A hr.le htle hy
  have hyC : y ∈ C := by
    obtain ⟨x, hx, -, -, -, hxy, -⟩ := hyd
    rw [← hxy]
    exact hfC hx
  by_cases hyK : y ∈ Kt
  · have hyE : y ∈ Eb i₀ := interior_subset (hKtE hyK)
    obtain ⟨AT, rT, tloT, SAT, SBT, aT, bT, hT, hAT0, hTN⟩ :=
      h.exists_wallProductBlock_at hsys hE hyd hy hyE isOpen_interior (hKtE hyK)
    have hys : y ∈ (ec i₀).source := hsys.layerSource i₀ (hsys.layerSubset i₀ hyE)
    obtain ⟨hTs, -, -⟩ := id hT
    obtain ⟨hrT, -, -, -, -, -, -, hsideT, -⟩ := id hTs
    have htT : tloT / 2 = -(rT / 2) ∨ tloT / 2 = 0 := by
      rcases hsideT with ⟨ht, -⟩ | ⟨ht, -⟩
      · left
        rw [ht, neg_div]
      · right
        rw [ht, zero_div]
    have hyinT : y ∈ innerChartBlock (ec i₀) AT rT tloT :=
      mem_chartBlock_of_norm_lt hys (by rw [hAT0, norm_zero]; exact half_pos hrT) htT
        fun _ => by rw [hAT0]; exact le_rfl
    have hAc : Continuous AT := AT.toAffineMap.continuous_of_finiteDimensional
    have hO₀ : IsOpen ((ec i₀).source ∩ ⇑(ec i₀) ⁻¹' (⇑AT ⁻¹' ball 0 rT)) :=
      (ec i₀).isOpen_inter_preimage (isOpen_ball.preimage hAc)
    have hyO₀ : y ∈ (ec i₀).source ∩ ⇑(ec i₀) ⁻¹' (⇑AT ⁻¹' ball 0 rT) := by
      refine ⟨hys, ?_⟩
      change AT (ec i₀ y) ∈ ball 0 rT
      rw [hAT0]
      exact mem_ball_self hrT
    obtain ⟨A', r', tlo', O, hA'app, hr', hsub', hside', hOo, hyO, hOs, hOin, ε₀, hε₀, lam₀,
      hlam₀, hmain⟩ :=
      hTs.exists_regional_perturbation_subset (hsys.chartBd i₀) hyd hyinT hΩ hKc hKcΩ hO₀ hyO₀
    have hA'eq : A' = AT := AffineEquiv.ext fun z => by rw [hA'app, hAT0, sub_zero]
    rw [hA'eq] at hsub' hside' hOin hmain
    obtain ⟨-, -, hsubT⟩ :=
      hTs.chartBlock_subset_of_subset_ball (hsys.chartBd i₀) hr' hside' hys hAT0 hsub'
    refine ⟨i₀, AT, r', tlo', O, hOo, hyO, hOs, hOin, hsubT.trans (hTN.trans interior_subset),
      ε₀, hε₀, lam₀, hlam₀, ?_⟩
    intro g δ lam hlam hδ hδL _ hclose hgΩ hgK hg4
    obtain ⟨SA', SB', a', b', La', Lb', hblk⟩ := hmain g δ lam hlam hδ hδL hclose
      (fun x hx hs => (hsys.chartC i₀ (f x) hs).mp (hfC hx)) hgΩ hgK hg4
    exact ⟨SA', SB', a', b', La', Lb', hT.of_subset_ball hsys hblk hys hAT0 hyC hsub'⟩
  · obtain ⟨N₀, hN₀o, hyN₀, hN₀B⟩ := hstab.exists_isOpen_mem_chartBlock (hsys.chartBd j) hy
    obtain ⟨AT, rT, tloT, SAT, SBT, aT, bT, hT, hAT0, hTN⟩ :=
      h.exists_wallProductBlock_at hsys hE hyd hy (hE hyB) (hKt.isOpen_compl.inter hN₀o)
        ⟨hyK, hyN₀⟩
    have hys : y ∈ (ec j).source := hyB.1
    obtain ⟨hTs, -, -⟩ := id hT
    obtain ⟨hrT, -, -, -, -, -, -, hsideT, -⟩ := id hTs
    have htT : tloT / 2 = -(rT / 2) ∨ tloT / 2 = 0 := by
      rcases hsideT with ⟨ht, -⟩ | ⟨ht, -⟩
      · left
        rw [ht, neg_div]
      · right
        rw [ht, zero_div]
    have hsubT : chartBlock (ec j) AT rT tloT ⊆ chartBlock (ec j) A r tlo := by
      intro z hz
      refine hN₀B z (hTN hz).2 fun hyBd => ?_
      obtain ⟨ht0, hAℓ⟩ := hTs.tlo_eq_zero_of_center_mem hys hAT0 hyBd
      rw [← hAℓ]
      have h3 : tloT ≤ (AT (ec j z)).2.2 := hz.2.2.2.1
      rw [ht0] at h3
      exact h3
    have hAc : Continuous AT := AT.toAffineMap.continuous_of_finiteDimensional
    refine ⟨j, AT, rT, tloT, (ec j).source ∩ ⇑(ec j) ⁻¹' (⇑AT ⁻¹' ball 0 (rT / 2)),
      (ec j).isOpen_inter_preimage (isOpen_ball.preimage hAc), ⟨hys, ?_⟩, inter_subset_left, ?_,
      hsubT.trans hE, 1, one_pos, 1, one_pos, ?_⟩
    · change AT (ec j y) ∈ ball 0 (rT / 2)
      rw [hAT0]
      exact mem_ball_self (half_pos hrT)
    · intro z hz hz0
      refine mem_chartBlock_of_norm_lt hz.1 (mem_ball_zero_iff.mp hz.2) htT
        fun h0 => ?_
      rcases hsideT with ⟨ht, -⟩ | ⟨-, hAℓ, -⟩
      · exfalso
        rw [ht] at h0
        linarith
      · rw [hAℓ]
        exact hz0
    · intro g _ _ _ _ _ hKeq _ _ _ _
      refine ⟨SAT, SBT, aT, bT, La, Lb, ?_, hT.2⟩
      refine (hTs.congr_of_eq fun x hx hx' => hKeq x hx ?_).of_le_margin (half_pos hη)
        (by linarith)
      rcases hx' with hx' | hx'
      · exact Or.inl (hTN hx').1
      · exact Or.inr (hTN hx').1

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem hasWallProductBlocks_of_finset {κ : Type*} {g : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M} {BdM C Z N : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {η : ℝ} (hη : 0 < η)
    (hN : IsOpen N) (hZN : Z ⊆ N) (t : Finset κ) (k : κ → ι)
    (A : κ → (EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ)) (r tlo : κ → ℝ)
    (SA SB : κ → Set (EuclideanSpace ℝ (Fin 2))) (a b : κ → ℝ × ℝ → ℝ) (La Lb : κ → ℝ)
    (hcov : doublePointSet g S ∩ N ⊆ ⋃ p ∈ t, innerChartBlock (ec (k p)) (A p) (r p) (tlo p))
    (hE : ∀ p ∈ t, chartBlock (ec (k p)) (A p) (r p) (tlo p) ⊆ Eb (k p))
    (hblk : ∀ p ∈ t, WallProductBlock g S (ec (k p)) (ℓ (k p)) BdM C Q ρ (A p) (r p) (tlo p)
      (SA p) (SB p) (a p) (b p) (La p) (Lb p) η) :
    HasWallProductBlocks g S ec ℓ Eb BdM C Q ρ Z η := by
  let e := t.equivFin
  let p : Fin t.card → κ := fun i => (e.symm i : κ)
  refine ⟨hη, N, t.card, fun i => k (p i), fun i => A (p i), fun i => r (p i),
    fun i => tlo (p i), fun i => SA (p i), fun i => SB (p i), fun i => a (p i),
    fun i => b (p i), fun i => La (p i), fun i => Lb (p i), hN, hZN, ?_,
    fun i => hE (p i) (e.symm i).2, fun i => hblk (p i) (e.symm i).2⟩
  intro y hy
  obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.mp (hcov hy)
  refine mem_iUnion.mpr ⟨e ⟨q, hq⟩, ?_⟩
  have hpq : p (e ⟨q, hq⟩) = q := by simp [p]
  change y ∈ innerChartBlock (ec (k (p (e ⟨q, hq⟩)))) (A (p (e ⟨q, hq⟩)))
    (r (p (e ⟨q, hq⟩))) (tlo (p (e ⟨q, hq⟩)))
  rw [hpq]
  exact hyq

end Ambient

section MetricAmbient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

theorem AdmissibleVertexMap.normal_simplicialMap_clauses {D : SingularTwoCell M}
    {BdM C V : Set M} (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C) {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} (hVs : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    {Rc Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    (hsub : IsSubdivision R Rc)
    (hlinear : ∀ s ∈ R.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
      EqOn (fun x => ec (D x)) A (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2)))))
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)} {τ : ℝ}
    (hadm : AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ) :
    (∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap R φ x)) ∧
      ∀ x ∈ Rc.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ Lc.space := by
  obtain ⟨-, hBvL, -, -, hBv0, hBvpos⟩ := hadm
  have hRsp : R.space = Rc.space := hsub.space_eq
  have hvR : ∀ v ∈ R.vertices, v ∈ Rc.space := fun v hv =>
    hRsp ▸ R.convexHull_subset_space hv (subset_convexHull ℝ _ (Finset.mem_singleton_self v))
  have hsrc : ∀ x ∈ Rc.space, D x ∈ ec.source := fun x hx => hVs (hRV hx)
  have hlin' : ∀ x ∈ Rc.space, simplicialMap R (fun v => ec (D v)) x = ec (D x) := fun x hx =>
    simplicialMap_eq_of_affine_faces R hlinear (hRsp ▸ hx)
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
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [linearMap_simplicialMap R φ ℓ x]
    exact simplicialMap_nonneg_of_nonneg_vertices R _ hℓφ0 (hRsp ▸ hx)
  · rw [linearMap_simplicialMap R φ ℓ x, simplicialMap_eq_zero_iff_of_eq_zero_on_vertices R
      (ℓ ∘ φ) (fun v => ℓ (ec (D v))) hℓφ0 (fun v hv => hℓD0 v (hvR v hv)) hℓeq (hRsp ▸ hx)]
    have e : simplicialMap R (fun v => ℓ (ec (D v))) x = ℓ (ec (D x)) := by
      have h1 := linearMap_simplicialMap R (fun v => ec (D v)) ℓ x
      rw [hlin' x hx] at h1
      exact h1.symm
    rw [e]
    exact hℓD x hx

open Classical in
theorem wallProductBlocks_stable_on_fixedSubdivision [CompactSpace M] (D : SingularTwoCell M)
    {BdM C Z W V Kt : Set M} {ι : Type}
    (ecf : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓf : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) (Eb Eb' : ι → Set M)
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)}
    {η κ δ ε τ₀ : ℝ} (i₀ : ι)
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ecf ℓf Eb Eb')
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C) (hZclosed : IsClosed Z)
    (hVopen : IsOpen V) (hVec : closure V ⊆ (ecf i₀).source) (hWV : closure W ⊆ V)
    (hVE : closure V ⊆ interior (Eb i₀))
    (Rc Lc Ac R T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hΩ : IsOpen Ω) (hΩcover : D.domain ∩ ⇑D ⁻¹' closure W ⊆ Ω)
    (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb) (hNbfr : Rc.space \ Ω ⊆ Nb)
    (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (hsub : IsSubdivision R Rc) (hRsfin : R.faces.Finite)
    (hκ : 0 < κ) (hδ : 0 < δ) (hε : 0 < ε) (hτ₀ : 0 < τ₀)
    (hlinear : ∀ s ∈ R.faces,
      ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
        EqOn (fun x => ecf i₀ (D x)) A (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2)))))
    (hcert : ∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
      StarInj T g → UniformInjectivityScale D.domain g κ ∧
        ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2)
    (hconv : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ecf i₀ (D x)) < ε → z ∈ ⇑(ecf i₀) '' V ∧ dist ((ecf i₀).symm z) (D x) < δ)
    (hactive : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ecf i₀ (D x)) < ε → (ecf i₀).symm z ∈ closure W → x ∈ Rc.space \ Ac.space)
    (hKcpt : IsCompact Kt) (hKV : Kt ⊆ V) (hDKt : ⇑D '' Rc.space ⊆ interior Kt)
    (hwp : HasWallProductBlocks (⇑D) D.domain ecf ℓf Eb BdM C Q ρ Z η) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧
      ∀ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
        (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
        AdmissibleVertexMap D (ecf i₀) (ℓf i₀) Lc Ac R Bv φ τ →
        IsPiecewiseAffineOn (simplicialMap R φ) Rc.space →
        (∀ x ∈ Rc.space, dist (simplicialMap R φ x) (ecf i₀ (D x)) < ε) →
        EqOn (simplicialMap R φ) (fun x => ecf i₀ (D x)) Ac.space →
        (∀ σ ∈ R.faces, (∃ v ∈ σ, v ∈ Ac.space) →
          Disjoint (simplicialMap R φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))
            (⇑(ecf i₀) '' closure W)) →
        MapsTo (simplicialMap R φ) Rc.space (⇑(ecf i₀) '' V) →
        regionGluedMap D (ecf i₀) R φ Rc '' Rc.space ⊆ Kt →
        StarInj T (regionGluedMap D (ecf i₀) R φ Rc) →
        HasWallProductBlocks (regionGluedMap D (ecf i₀) R φ Rc) D.domain ecf ℓf Eb BdM C
          Q ρ Z (η / 2) := by
  classical
  let _ := hfiber
  let _ := hWV
  let _ := hRfin
  let _ := hΩcover
  let _ := hε
  let _ := hactive
  let _ := hVopen
  obtain ⟨hη, N, m, j, A, r, tlo, SA, SB, a, b, La, Lb, hNo, hZN, hcov, hEb, hblk⟩ := hwp
  obtain ⟨N', hN'o, hZN', hclN'⟩ := normal_exists_closure_subset hZclosed hNo hZN
  have : Finite R.faces := hRsfin.to_subtype
  have hRsp : R.space = Rc.space := hsub.space_eq
  have hRcomp : IsCompact Rc.space := hRsp ▸ (isPolyhedron_space R).isCompact
  have hKcΩ : closure (Rc.space \ Ac.space) ⊆ Ω :=
    closure_sdiff_subset_of_frontier_cover hRcomp.isClosed hNb hNbfr hNbA
  have hS : IsCompact D.domain := D.isPLBall_domain.isPolyhedron.isCompact
  have hVs : V ⊆ (ecf i₀).source := subset_closure.trans hVec
  have hsrc : ∀ x ∈ Rc.space, D x ∈ (ecf i₀).source := fun x hx => hVs (hRV hx)
  have hlin' : ∀ x ∈ Rc.space, simplicialMap R (fun v => ecf i₀ (D v)) x = ecf i₀ (D x) :=
    fun x hx => simplicialMap_eq_of_affine_faces R hlinear (hRsp ▸ hx)
  have hKtE : Kt ⊆ interior (Eb i₀) := hKV.trans (subset_closure.trans hVE)
  have hK₀ : IsCompact (doublePointSet (⇑D) D.domain ∩ closure N') :=
    (D.isCompact_doublePointSet hloc).inter_right isClosed_closure
  have hmem : ∀ y ∈ doublePointSet (⇑D) D.domain ∩ closure N',
      ∃ i, y ∈ innerChartBlock (ecf (j i)) (A i) (r i) (tlo i) :=
    fun y hy => mem_iUnion.mp (hcov ⟨hy.1, hclN' hy.2⟩)
  choose k A' r' tlo' O hOo hyO hOs hOin hOE ε₀ hε₀ lam₀ hlam₀ hmain using
    fun (y : M) (hy : y ∈ doublePointSet (⇑D) D.domain ∩ closure N') =>
      (hblk (Classical.choose (hmem y hy))).exists_persistent_wallProductBlock hsys
        (hEb _) hy.1 (Classical.choose_spec (hmem y hy)) hmapC hKcpt.isClosed hKtE hΩ
        isClosed_closure hKcΩ
  obtain ⟨t, ht⟩ := hK₀.elim_finite_subcover
    (fun p : ↥(doublePointSet (⇑D) D.domain ∩ closure N') => O p p.2)
    (fun p => hOo p p.2) (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hyO y hy⟩)
  have hOu : IsOpen (⋃ p ∈ t, O p p.2) := isOpen_biUnion fun p _ => hOo p p.2
  obtain ⟨m₀, hm₀, hΦ⟩ :=
    exists_pos_doublePointSet_inter_subset hS D.continuousOn hκ isClosed_closure hOu ht
  obtain ⟨e₁, he₁, he₁le⟩ :=
    Finset.exists_pos_forall_le_of_pos t (fun p => ε₀ p p.2) fun p _ => hε₀ p p.2
  obtain ⟨e₂, he₂, he₂le⟩ :=
    Finset.exists_pos_forall_le_of_pos t (fun p => lam₀ p p.2) fun p _ => hlam₀ p p.2
  obtain ⟨Vs, Λ, hΛ, -, hdisp⟩ := exists_vertex_displacement_lipschitz R hRsfin
  have hK₁ : IsCompact (⇑(ecf i₀) '' (⇑D '' Rc.space)) :=
    (hRcomp.image_of_continuousOn (D.continuousOn.mono hRdom)).image_of_continuousOn
      ((ecf i₀).continuousOn.mono fun _ ⟨x, hx, hxy⟩ => hxy ▸ hsrc x hx)
  have hK₁t : ⇑(ecf i₀) '' (⇑D '' Rc.space) ⊆ (ecf i₀).target := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact (ecf i₀).map_source (hsrc x hx)
  obtain ⟨τ₁, hτ₁, hτ₁'⟩ := OpenPartialHomeomorph.exists_pos_dist_symm_lt (ecf i₀) hK₁ hK₁t hm₀
  have hΛ1 : 0 < Λ + 1 := by linarith
  refine ⟨min (min τ₀ e₁) (min (e₂ / (Λ + 1)) τ₁),
    lt_min (lt_min hτ₀ he₁) (lt_min (div_pos he₂ hΛ1) hτ₁),
    (min_le_left _ _).trans (min_le_left _ _),
    fun Bv φ hadm _ hdistε hEqA _ hmaps hKimg hstar => ?_⟩
  set τ := min (min τ₀ e₁) (min (e₂ / (Λ + 1)) τ₁) with hτdef
  have hτe₁ : τ ≤ e₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hτe₂ : τ ≤ e₂ / (Λ + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hττ₁ : τ ≤ τ₁ := (min_le_right _ _).trans (min_le_right _ _)
  have hclose : ∀ x ∈ Rc.space, dist (simplicialMap R φ x) (ecf i₀ (D x)) < τ := by
    intro x hx
    rw [← hlin' x hx]
    exact dist_simplicialMap_lt_of_dist_vertices_lt R hadm.2.2.1 (hRsp ▸ hx)
  have hgRc : ∀ x ∈ Rc.space, regionGluedMap D (ecf i₀) R φ Rc x ∈ V ∧
      ecf i₀ (regionGluedMap D (ecf i₀) R φ Rc x) = simplicialMap R φ x := fun x hx =>
    regionGluedMap_chart_of_mem D (ecf i₀) hVs R Rc φ hmaps hx
  have hgout : ∀ x ∉ Rc.space, regionGluedMap D (ecf i₀) R φ Rc x = D x := fun x hx =>
    regionGluedMap_of_notMem D (ecf i₀) R Rc φ hx
  have hgδ : ∀ x ∈ D.domain, dist (regionGluedMap D (ecf i₀) R φ Rc x) (D x) < δ := by
    intro x _
    by_cases hxR : x ∈ Rc.space
    · rw [regionGluedMap_of_mem D (ecf i₀) R φ hxR]
      exact (hconv x hxR _ (hdistε x hxR)).2
    · rw [hgout x hxR, dist_self]
      exact hδ
  have huis := (hcert _ hgδ hstar).1
  have hgm : ∀ x ∈ D.domain, dist (regionGluedMap D (ecf i₀) R φ Rc x) (D x) < m₀ := by
    intro x _
    by_cases hxR : x ∈ Rc.space
    · have hk : ecf i₀ (D x) ∈ ⇑(ecf i₀) '' (⇑D '' Rc.space) :=
        mem_image_of_mem _ (mem_image_of_mem D hxR)
      have h1 := (hτ₁' _ hk _ ((hclose x hxR).trans_le hττ₁)).2
      rw [regionGluedMap_of_mem D (ecf i₀) R φ hxR]
      rwa [(ecf i₀).left_inv (hsrc x hxR)] at h1
    · rw [hgout x hxR, dist_self]
      exact hm₀
  have hDP := hΦ _ hgm huis
  obtain ⟨δφ, lam, hδpl, hδL, hlamΛ, hδeq⟩ := hdisp φ (fun v => ecf i₀ (D v)) τ hadm.2.2.1
  have hΛτ : Λ * τ ≤ e₂ := by
    have h2 : Λ * τ ≤ Λ * (e₂ / (Λ + 1)) := mul_le_mul_of_nonneg_left hτe₂ hΛ
    have h3 : Λ * (e₂ / (Λ + 1)) ≤ e₂ := by
      rw [mul_div_assoc', div_le_iff₀ hΛ1]
      nlinarith
    linarith
  have hlam : ∀ p ∈ t, (lam : ℝ) ≤ lam₀ p p.2 := fun p hp =>
    hlamΛ.trans (hΛτ.trans (he₂le p hp))
  have hgK : ∀ x ∈ D.domain, x ∉ closure (Rc.space \ Ac.space) →
      regionGluedMap D (ecf i₀) R φ Rc x = D x := by
    intro x _ hxK
    by_cases hxR : x ∈ Rc.space
    · have hxA : x ∈ Ac.space := by
        by_contra hxA
        exact hxK (subset_closure ⟨hxR, hxA⟩)
      have h1 : simplicialMap R φ x = ecf i₀ (D x) := hEqA hxA
      rw [regionGluedMap_of_mem D (ecf i₀) R φ hxR, h1, (ecf i₀).left_inv (hsrc x hxR)]
    · exact hgout x hxR
  have hgΩ : ∀ x ∈ D.domain, x ∈ Ω → regionGluedMap D (ecf i₀) R φ Rc x ∈ (ecf i₀).source ∧
      ecf i₀ (regionGluedMap D (ecf i₀) R φ Rc x) = ecf i₀ (D x) + δφ x := by
    intro x hxD hxΩ
    have hxR : x ∈ Rc.space := hΩR ⟨hxD, hxΩ⟩
    obtain ⟨hgV, hgeq⟩ := hgRc x hxR
    refine ⟨hVs hgV, ?_⟩
    rw [hgeq, hδeq x (hRsp ▸ hxR), hlin' x hxR, add_sub_cancel]
  have hG1 : ∀ x ∈ D.domain, regionGluedMap D (ecf i₀) R φ Rc x ∈ (ecf i₀).source →
      D x ∈ (ecf i₀).source ∧
        ‖ecf i₀ (regionGluedMap D (ecf i₀) R φ Rc x) - ecf i₀ (D x)‖ ≤ e₁ := by
    intro x _ hgs
    by_cases hxR : x ∈ Rc.space
    · refine ⟨hsrc x hxR, ?_⟩
      rw [(hgRc x hxR).2, ← dist_eq_norm]
      exact (hclose x hxR).le.trans hτe₁
    · rw [hgout x hxR] at hgs ⊢
      refine ⟨hgs, ?_⟩
      rw [sub_self, norm_zero]
      exact he₁.le
  obtain ⟨hℓ0, hℓL⟩ := hadm.normal_simplicialMap_clauses hproper hmapC hVs (hsys.chartC i₀)
    (hsys.chartBd i₀) hsub hlinear hRdom hRV hLspace
  have hg4 : ∀ x ∈ D.domain, regionGluedMap D (ecf i₀) R φ Rc x ∈ (ecf i₀).source →
      0 ≤ ℓf i₀ (ecf i₀ (regionGluedMap D (ecf i₀) R φ Rc x)) ∧
        (x ∈ frontier D.domain ↔ ℓf i₀ (ecf i₀ (regionGluedMap D (ecf i₀) R φ Rc x)) = 0) := by
    intro x hxD hgs
    by_cases hxR : x ∈ Rc.space
    · rw [(hgRc x hxR).2]
      refine ⟨hℓ0 x hxR, ?_⟩
      rw [hℓL x hxR, hLspace]
      exact ⟨fun h => ⟨hxR, h⟩, fun h => h.2⟩
    · rw [hgout x hxR] at hgs ⊢
      refine ⟨(hsys.chartC i₀ _ hgs).mp (hmapC hxD), ?_⟩
      rw [← hsys.chartBd i₀ _ hgs]
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
  have hgKt : ∀ x ∈ D.domain, regionGluedMap D (ecf i₀) R φ Rc x ∉ Kt ∨ D x ∉ Kt →
      regionGluedMap D (ecf i₀) R φ Rc x = D x := by
    intro x _ hx
    by_cases hxR : x ∈ Rc.space
    · exfalso
      rcases hx with hx | hx
      · exact hx (hKimg (mem_image_of_mem _ hxR))
      · exact hx (interior_subset (hDKt (mem_image_of_mem D hxR)))
    · exact hgout x hxR
  have hgC : ∀ x ∈ D.domain, regionGluedMap D (ecf i₀) R φ Rc x ∈ C := by
    intro x hx
    by_cases hxR : x ∈ Rc.space
    · have hgs : regionGluedMap D (ecf i₀) R φ Rc x ∈ (ecf i₀).source := hVs (hgRc x hxR).1
      exact (hsys.chartC i₀ _ hgs).mpr (hg4 x hx hgs).1
    · rw [hgout x hxR]
      exact hmapC hx
  have hblocks : ∀ p ∈ t, ∃ (SA' SB' : Set (EuclideanSpace ℝ (Fin 2))) (a' b' : ℝ × ℝ → ℝ)
      (La' Lb' : ℝ), WallProductBlock (regionGluedMap D (ecf i₀) R φ Rc) D.domain
        (ecf (k p p.2)) (ℓf (k p p.2)) BdM C Q ρ (A' p p.2) (r' p p.2) (tlo' p p.2) SA' SB' a' b'
        La' Lb' (η / 2) := fun p hp =>
    hmain p p.2 _ δφ lam (hlam p hp) hδpl hδL hgKt
      (fun x hx hgs => ⟨(hG1 x hx hgs).1, (hG1 x hx hgs).2.trans (he₁le p hp)⟩) hgΩ hgK hg4
  choose! SA' SB' a' b' La' Lb' hblk' using hblocks
  refine hasWallProductBlocks_of_finset (half_pos hη) hN'o hZN' t (fun p => k p p.2)
    (fun p => A' p p.2) (fun p => r' p p.2) (fun p => tlo' p p.2) SA' SB' a' b' La' Lb' ?_
    (fun p _ => hOE p p.2) hblk'
  intro y hy
  obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (hDP ⟨hy.1, subset_closure hy.2⟩)
  refine mem_iUnion₂.mpr ⟨p, hp, hOin p p.2 y hyp ?_⟩
  obtain ⟨⟨x, hx, -, -, -, hgx, -⟩, -⟩ := hy
  have hys : y ∈ (ecf (k p p.2)).source := hOs p p.2 hyp
  rw [← hgx] at hys ⊢
  exact (hsys.chartC _ _ hys).mp (hgC x hx)

end MetricAmbient

end DifferentialGeometry.Topology.PiecewiseLinear
