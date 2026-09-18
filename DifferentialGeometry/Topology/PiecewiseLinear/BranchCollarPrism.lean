import DifferentialGeometry.Topology.PiecewiseLinear.BranchBoundarySweep
import DifferentialGeometry.Topology.PiecewiseLinear.PrismArc

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem isPLBall_one_image_chart_of_isPLOn [HasGroupoid M (plGroupoid 3)]
    {q : EuclideanSpace ℝ (Fin 2) → M} {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLBall 1 J) (hq : IsPLOn 2 3 q J) (hinj : InjOn q J)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M) (hmap : MapsTo q J ec.source) :
    IsPLBall 1 ((ec ∘ q) '' J) := by
  obtain ⟨θ, hθ⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hJ
  have hpa : IsPiecewiseAffineOn (ec ∘ q) J :=
    (isPLOn_iff_isPiecewiseAffineOn_comp_chart ec hec hmap).mp hq
  have hmapθ : MapsTo θ (Icc (0 : ℝ) 1) J := hθ.bijOn.mapsTo
  have hcomp : IsPiecewiseAffineOn ((ec ∘ q) ∘ θ) (Icc (0 : ℝ) 1) := by
    have h := hpa.comp hθ.isPiecewiseAffineOn
    have hset : Icc (0 : ℝ) 1 ∩ θ ⁻¹' J = Icc (0 : ℝ) 1 := inter_eq_left.mpr hmapθ
    rwa [hset] at h
  have hinjc : InjOn ((ec ∘ q) ∘ θ) (Icc (0 : ℝ) 1) :=
    (ec.injOn.comp hinj hmap).comp hθ.bijOn.injOn hmapθ
  have himg : ((ec ∘ q) ∘ θ) '' Icc (0 : ℝ) 1 = (ec ∘ q) '' J := by
    rw [image_comp, hθ.image_eq]
  have h := isPLBall_image_Icc_of_isPiecewiseAffineOn (by norm_num : (0 : ℝ) < 1) hcomp hinjc
  rwa [himg] at h

theorem exists_isPLHomeomorphOn_Icc_image_chart_of_isPLOn [HasGroupoid M (plGroupoid 3)]
    {q : EuclideanSpace ℝ (Fin 2) → M} {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLBall 1 J) (hq : IsPLOn 2 3 q J) (hinj : InjOn q J)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M) (hmap : MapsTo q J ec.source) :
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn γ (Icc (0 : ℝ) 1) ((ec ∘ q) '' J) :=
  exists_isPLHomeomorphOn_Icc_of_isPLBall_one
    (isPLBall_one_image_chart_of_isPLOn hJ hq hinj ec hec hmap)

theorem exists_isPiecewiseAffineOn_prism_arc_landing
    {J : Set (EuclideanSpace ℝ (Fin 2))} {θ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hθ : IsPLHomeomorphOn θ (Icc (0 : ℝ) 1) J)
    {b : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)} (hb : IsPiecewiseAffineOn b J)
    (π : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hfix0 : π (b (θ 0)) = b (θ 0)) (hfix1 : π (b (θ 1)) = b (θ 1)) :
    ∃ Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3),
      IsPiecewiseAffineOn Ψ (J ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ J, Ψ (z, 0) = b z) ∧ (∀ z ∈ J, Ψ (z, 1) = π (b z)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Ψ (θ 0, t) = b (θ 0)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Ψ (θ 1, t) = b (θ 1)) ∧
      (∀ S : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ S → MapsTo b J S →
        MapsTo (fun z => π (b z)) J S → MapsTo Ψ (J ×ˢ Icc (0 : ℝ) 1) S) := by
  obtain ⟨Ψ, hPA, hbot, htop, hl, hr, himg⟩ :=
    exists_isPiecewiseAffineOn_prism_of_isPLHomeomorphOn hθ hb (hb.affine_comp π)
  refine ⟨Ψ, hPA, hbot, htop, ?_, ?_, ?_⟩
  · intro t ht
    rw [hl t ht]
    change b (θ 0) + t • (π (b (θ 0)) - b (θ 0)) = b (θ 0)
    rw [hfix0, sub_self, smul_zero, add_zero]
  · intro t ht
    rw [hr t ht]
    change b (θ 1) + t • (π (b (θ 1)) - b (θ 1)) = b (θ 1)
    rw [hfix1, sub_self, smul_zero, add_zero]
  · exact fun S hS hbS hpS => himg S hS hbS hpS

theorem isPLOn_prism_comp_of_mapsTo_chart [HasGroupoid M (plGroupoid 3)]
    {A J : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {τ : EuclideanSpace ℝ (Fin 2) → ℝ}
    {Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hρ : IsPiecewiseAffineOn ρ A) (hτ : IsPiecewiseAffineOn τ A)
    (hmapA : MapsTo (fun x => (ρ x, τ x)) A (J ×ˢ Icc (0 : ℝ) 1))
    (hΨ : IsPiecewiseAffineOn Ψ (J ×ˢ Icc (0 : ℝ) 1))
    (hΨmaps : MapsTo Ψ (J ×ˢ Icc (0 : ℝ) 1) ec.target) :
    IsPLOn 2 3 (fun x => ec.symm (Ψ (ρ x, τ x))) A := by
  have hμ : IsPiecewiseAffineOn (fun x => (ρ x, τ x)) A := hρ.prod_mk hτ
  have hcomp : IsPiecewiseAffineOn (fun x => Ψ (ρ x, τ x)) A := by
    have h := hΨ.comp hμ
    have hset : A ∩ (fun x => (ρ x, τ x)) ⁻¹' (J ×ˢ Icc (0 : ℝ) 1) = A :=
      inter_eq_left.mpr hmapA
    rw [hset] at h
    exact h
  have hsrc : MapsTo (fun x => ec.symm (Ψ (ρ x, τ x))) A ec.source :=
    fun x hx => ec.map_target (hΨmaps (hmapA hx))
  refine (isPLOn_iff_isPiecewiseAffineOn_comp_chart ec hec hsrc).mpr (hcomp.congr ?_)
  intro x hx
  exact ec.right_inv (hΨmaps (hmapA hx))

open Classical in
theorem isPLOn_collarSweep_of_prism_over_arc [HasGroupoid M (plGroupoid 3)]
    {q : EuclideanSpace ℝ (Fin 2) → M} {F : EuclideanSpace ℝ (Fin 2) → M}
    {Γ A B J : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {τ : EuclideanSpace ℝ (Fin 2) → ℝ}
    {Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hq : IsPLOn 2 3 q Γ)
    (hApoly : IsPolyhedron A) (hBpoly : IsPolyhedron B)
    (hρA : IsPiecewiseAffineOn ρ A) (hτA : IsPiecewiseAffineOn τ A)
    (hρB : IsPiecewiseAffineOn ρ B)
    (hmapA : MapsTo (fun x => (ρ x, τ x)) A (J ×ˢ Icc (0 : ℝ) 1))
    (hmapB : MapsTo ρ B Γ)
    (hΨ : IsPiecewiseAffineOn Ψ (J ×ˢ Icc (0 : ℝ) 1))
    (hΨmaps : MapsTo Ψ (J ×ˢ Icc (0 : ℝ) 1) ec.target)
    (hFA : ∀ x ∈ A, F x = ec.symm (Ψ (ρ x, τ x)))
    (hFB : ∀ x ∈ B, F x = q (ρ x)) :
    IsPLOn 2 3 F (A ∪ B) := by
  have hprism : IsPLOn 2 3 (fun x => ec.symm (Ψ (ρ x, τ x))) A :=
    isPLOn_prism_comp_of_mapsTo_chart ec hec hρA hτA hmapA hΨ hΨmaps
  have hconst : IsPLOn 2 3 (fun x => q (ρ x)) B :=
    isPLOn_of_isPiecewiseAffineOn_factorization hq hρB hmapB (fun _ _ => rfl)
  have hagree : EqOn (fun x => ec.symm (Ψ (ρ x, τ x))) (fun x => q (ρ x)) (A ∩ B) := by
    rintro x ⟨hxA, hxB⟩
    exact ((hFA x hxA).symm.trans (hFB x hxB))
  have hpiece :=
    hprism.piecewise_of_isClosed hconst hApoly.isCompact.isClosed hBpoly.isCompact.isClosed hagree
  intro x hx
  refine piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem
    (hpiece x hx) (fun y hy => ?_) hx
  by_cases hyA : y ∈ A
  · rw [Set.piecewise_eq_of_mem _ _ _ hyA]
    exact hFA y hyA
  · rw [Set.piecewise_eq_of_notMem _ _ _ hyA]
    exact hFB y (hy.resolve_left hyA)

open Classical in
theorem isPLOn_boundarySweep_annulus_of_prism [HasGroupoid M (plGroupoid 3)]
    {D : SingularTwoCell M} {BdM : Set M} {hs : M → M}
    {P A B J Δ' : Set (EuclideanSpace ℝ (Fin 2))} {Φ : M → ℝ → M}
    {ρ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {τ : EuclideanSpace ℝ (Fin 2) → ℝ}
    {Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hgpl : IsPLOn 2 3 (P.piecewise (hs ∘ D) D) (frontier D.domain))
    (hApoly : IsPolyhedron A) (hBpoly : IsPolyhedron B)
    (hunion : A ∪ B = Δ' \ interior D.domain)
    (hρA : IsPiecewiseAffineOn ρ A) (hτA : IsPiecewiseAffineOn τ A)
    (hρB : IsPiecewiseAffineOn ρ B)
    (hmapA : MapsTo (fun x => (ρ x, τ x)) A (J ×ˢ Icc (0 : ℝ) 1))
    (hmapB : MapsTo ρ B (frontier D.domain))
    (hΨ : IsPiecewiseAffineOn Ψ (J ×ˢ Icc (0 : ℝ) 1))
    (hΨmaps : MapsTo Ψ (J ×ˢ Icc (0 : ℝ) 1) ec.target)
    (hΦfix : ∀ y ∈ BdM, ∀ s : ℝ, Φ y s = y)
    (hBbd : ∀ x ∈ B, P.piecewise (hs ∘ D) D (ρ x) ∈ BdM)
    (hΦprism : ∀ x ∈ A,
      Φ (P.piecewise (hs ∘ D) D (ρ x)) (τ x) = ec.symm (Ψ (ρ x, τ x))) :
    IsPLOn 2 3 (fun x => Φ (P.piecewise (hs ∘ D) D (ρ x)) (τ x))
      (Δ' \ interior D.domain) := by
  rw [← hunion]
  refine isPLOn_collarSweep_of_prism_over_arc ec hec hgpl hApoly hBpoly hρA hτA hρB hmapA hmapB
    hΨ hΨmaps hΦprism (fun x hx => ?_)
  exact hΦfix _ (hBbd x hx) (τ x)

open Classical in
noncomputable def prismSweep (q : EuclideanSpace ℝ (Fin 2) → M)
    (J : Set (EuclideanSpace ℝ (Fin 2)))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)) : M → ℝ → M :=
  fun y s => if y ∈ q '' J then ec.symm (Ψ (Function.invFunOn q J y, s)) else y

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem prismSweep_of_mem {q : EuclideanSpace ℝ (Fin 2) → M}
    {J : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hinj : InjOn q J) {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ J) (s : ℝ) :
    prismSweep q J ec Ψ (q z) s = ec.symm (Ψ (z, s)) := by
  classical
  have hmem : q z ∈ q '' J := ⟨z, hz, rfl⟩
  have hinv : Function.invFunOn q J (q z) = z := hinj.leftInvOn_invFunOn hz
  simp only [prismSweep, if_pos hmem, hinv]

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem prismSweep_of_notMem {q : EuclideanSpace ℝ (Fin 2) → M}
    {J : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {y : M} (hy : y ∉ q '' J) (s : ℝ) : prismSweep q J ec Ψ y s = y := by
  classical
  simp only [prismSweep, if_neg hy]

open Classical in
theorem exists_boundarySweep_of_prism_over_arc [HasGroupoid M (plGroupoid 3)]
    {D : SingularTwoCell M} {BdM : Set M} {q : EuclideanSpace ℝ (Fin 2) → M}
    {A B J Δ' : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {τ : EuclideanSpace ℝ (Fin 2) → ℝ}
    {Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hq : IsPLOn 2 3 q (frontier D.domain))
    (hinj : InjOn q J) (hqsrc : MapsTo q J ec.source)
    (hfixJ : ∀ z ∈ J, q z ∈ BdM → ∀ s : ℝ, ec.symm (Ψ (z, s)) = q z)
    (hfr : ∀ z ∈ frontier D.domain, z ∉ J → q z ∈ BdM)
    (hApoly : IsPolyhedron A) (hBpoly : IsPolyhedron B)
    (hunion : A ∪ B = Δ' \ interior D.domain)
    (hρA : IsPiecewiseAffineOn ρ A) (hτA : IsPiecewiseAffineOn τ A)
    (hρB : IsPiecewiseAffineOn ρ B)
    (hmapA : MapsTo (fun x => (ρ x, τ x)) A (J ×ˢ Icc (0 : ℝ) 1))
    (hmapB : MapsTo ρ B (frontier D.domain))
    (hBbd : ∀ x ∈ B, q (ρ x) ∈ BdM)
    (hΨ : IsPiecewiseAffineOn Ψ (J ×ˢ Icc (0 : ℝ) 1))
    (hΨmaps : MapsTo Ψ (J ×ˢ Icc (0 : ℝ) 1) ec.target)
    (hbot : ∀ z ∈ J, Ψ (z, 0) = ec (q z))
    (htop : ∀ z ∈ J, ec.symm (Ψ (z, 1)) ∈ BdM)
    (hmeet : ∀ z ∈ J, ∀ s : ℝ, ec.symm (Ψ (z, s)) ∈ BdM → q z ∈ BdM ∨ s = 1) :
    ∃ Φ : M → ℝ → M, (∀ y : M, Φ y 0 = y) ∧
      (∀ z ∈ frontier D.domain, Φ (q z) 1 ∈ BdM) ∧
      (∀ y ∈ BdM, ∀ s : ℝ, Φ y s = y) ∧
      (∀ z ∈ frontier D.domain, ∀ s : ℝ, Φ (q z) s ∈ BdM → q z ∈ BdM ∨ s = 1) ∧
      IsPLOn 2 3 (fun x => Φ (q (ρ x)) (τ x)) (Δ' \ interior D.domain) := by
  classical
  have hfixall : ∀ y ∈ BdM, ∀ s : ℝ, prismSweep q J ec Ψ y s = y := by
    intro y hy s
    by_cases hmem : y ∈ q '' J
    · obtain ⟨z, hz, rfl⟩ := hmem
      rw [prismSweep_of_mem hinj hz]
      exact hfixJ z hz hy s
    · exact prismSweep_of_notMem hmem s
  refine ⟨prismSweep q J ec Ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ q '' J
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [prismSweep_of_mem hinj hz, hbot z hz, ec.left_inv (hqsrc hz)]
    · exact prismSweep_of_notMem hy 0
  · intro z hz
    by_cases hzJ : z ∈ J
    · rw [prismSweep_of_mem hinj hzJ]
      exact htop z hzJ
    · rw [hfixall _ (hfr z hz hzJ)]
      exact hfr z hz hzJ
  · exact hfixall
  · intro z hz s hmem
    by_cases hzJ : z ∈ J
    · rw [prismSweep_of_mem hinj hzJ] at hmem
      exact hmeet z hzJ s hmem
    · exact Or.inl (hfr z hz hzJ)
  · rw [← hunion]
    refine isPLOn_collarSweep_of_prism_over_arc ec hec hq hApoly hBpoly hρA hτA hρB hmapA
      hmapB hΨ hΨmaps (fun x hx => ?_) (fun x hx => ?_)
    · exact prismSweep_of_mem hinj (hmapA hx).1 (τ x)
    · exact hfixall _ (hBbd x hx) (τ x)

open Classical in
theorem exists_collarExtension_image_inter_boundary_of_prism_over_arc
    [HasGroupoid M (plGroupoid 3)]
    {D : SingularTwoCell M} {BdM N : Set M} {hslide : M → M}
    {P A B J Δ' : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {τ : EuclideanSpace ℝ (Fin 2) → ℝ}
    {Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hbdpre : D.domain ∩ D ⁻¹' BdM ⊆ frontier D.domain)
    (hDN : MapsTo D D.domain N)
    (hrefl : ∀ x ∈ N, hslide x ∈ BdM → x ∈ BdM)
    (hgpl : IsPLOn 2 3 (P.piecewise (hslide ∘ D) D) D.domain)
    (hΔ'ball : IsPLBall 2 Δ') (hsubint : D.domain ⊆ interior Δ')
    (hρid : ∀ x ∈ D.domain, ρ x = x)
    (hρfr : MapsTo ρ (Δ' \ D.domain) (frontier D.domain))
    (hρsurj : frontier D.domain ⊆ ρ '' frontier Δ')
    (hτ0 : ∀ x ∈ D.domain, τ x = 0) (hτ1 : ∀ x ∈ frontier Δ', τ x = 1)
    (hinj : InjOn (P.piecewise (hslide ∘ D) D) J)
    (hqsrc : MapsTo (P.piecewise (hslide ∘ D) D) J ec.source)
    (hfixJ : ∀ z ∈ J, P.piecewise (hslide ∘ D) D z ∈ BdM → ∀ s : ℝ,
      ec.symm (Ψ (z, s)) = P.piecewise (hslide ∘ D) D z)
    (hfr : ∀ z ∈ frontier D.domain, z ∉ J → P.piecewise (hslide ∘ D) D z ∈ BdM)
    (hApoly : IsPolyhedron A) (hBpoly : IsPolyhedron B)
    (hunion : A ∪ B = Δ' \ interior D.domain)
    (hρA : IsPiecewiseAffineOn ρ A) (hτA : IsPiecewiseAffineOn τ A)
    (hρB : IsPiecewiseAffineOn ρ B)
    (hmapA : MapsTo (fun x => (ρ x, τ x)) A (J ×ˢ Icc (0 : ℝ) 1))
    (hmapB : MapsTo ρ B (frontier D.domain))
    (hBbd : ∀ x ∈ B, P.piecewise (hslide ∘ D) D (ρ x) ∈ BdM)
    (hΨ : IsPiecewiseAffineOn Ψ (J ×ˢ Icc (0 : ℝ) 1))
    (hΨmaps : MapsTo Ψ (J ×ˢ Icc (0 : ℝ) 1) ec.target)
    (hbot : ∀ z ∈ J, Ψ (z, 0) = ec (P.piecewise (hslide ∘ D) D z))
    (htop : ∀ z ∈ J, ec.symm (Ψ (z, 1)) ∈ BdM)
    (hmeet : ∀ z ∈ J, ∀ s : ℝ, ec.symm (Ψ (z, s)) ∈ BdM →
      P.piecewise (hslide ∘ D) D z ∈ BdM ∨ s = 1) :
    ∃ G : SingularTwoCell M, G.domain = Δ' ∧
      EqOn G (P.piecewise (hslide ∘ D) D) D.domain ∧
      Set.range G.boundary ⊆ BdM ∧
      G '' G.domain ∩ BdM = Set.range G.boundary := by
  have hfrpoly : IsPolyhedron (frontier D.domain) :=
    D.isPLBall_domain.isPLSphere_frontier.isPolyhedron
  have hqfr : IsPLOn 2 3 (P.piecewise (hslide ∘ D) D) (frontier D.domain) :=
    hgpl.mono_of_isPolyhedron hfrpoly D.frontier_subset_domain
  obtain ⟨Φ, hΦ0, hΦ1, hΦfix, hΦmem, hann⟩ :=
    exists_boundarySweep_of_prism_over_arc (D := D) (BdM := BdM) ec hec hqfr hinj hqsrc hfixJ
      hfr hApoly hBpoly hunion hρA hτA hρB hmapA hmapB hBbd hΨ hΨmaps hbot htop hmeet
  exact exists_collarExtension_image_inter_boundary_of_exteriorCollapse hbdpre hDN hrefl hgpl
    hΔ'ball hsubint hρid hρfr hρsurj hτ0 hτ1 hΦ0 hΦ1 hΦfix hΦmem hann

end DifferentialGeometry.Topology.PiecewiseLinear
