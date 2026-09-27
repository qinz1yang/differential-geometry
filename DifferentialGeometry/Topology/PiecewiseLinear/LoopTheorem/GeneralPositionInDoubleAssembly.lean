/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularSetOfCell
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDiskBoundaryWord

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_boundary_loop_of_buffered_homotopy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : NormalSystem E) (K : Geometry.SimplicialComplex ℝ E)
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) (double 3 K).space]
    [PathConnectedSpace S.boundaryNeighborhoodSpace]
    (G A : SingularTwoCell (double 3 K).space)
    (β : ContinuousMap loopCircle (frontier G.domain))
    (γ : freeLoop S.boundaryNeighborhoodSpace)
    (hdom : A.domain = G.domain)
    (hmap : MapsTo A A.domain
      (((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
        ((simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)) '' K.space)))
    (hparam : ∀ θ, ((G (β θ) : (double 3 K).space) : E × E × ℝ) =
      simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id) (γ θ))
    (havoid : ¬loopClassMeets γ S.basepoint S.normalSubgroup)
    (hsurj : Function.Surjective β)
    (H : ContinuousMap (unitInterval × frontier G.domain) (double 3 K).space)
    (hzero : ∀ x, H (0, x) = G x)
    (hone : ∀ x, H (1, x) = A x)
    (hB : ∀ t x, H (t, x) ∈
      (((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
        ((simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)) ''
          S.boundaryNeighborhood.space)))
    (hBsub : S.boundaryNeighborhood.space ⊆ K.space) :
    ∃ (c : loopCircle ≃ₜ frontier A.domain) (δ : freeLoop S.boundaryNeighborhoodSpace),
      (∀ θ, ((A (c θ) : (double 3 K).space) : E × E × ℝ) =
        simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id) (δ θ)) ∧
        ¬loopClassMeets δ S.basepoint S.normalSubgroup := by
  let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
  let π : (double 3 K).space → E := fun x => glueSnd E E (x : E × E × ℝ)
  have hπi (x : E) (hx : x ∈ K.space) : glueSnd E E (ι x) = x :=
    glueSnd_simplicialMap K (PiecewiseLinear.boundaryComplex 3 K) id hx
  have hπmem (t : unitInterval) (θ : loopCircle) :
      π (H (t, β θ)) ∈ S.boundaryNeighborhood.space := by
    have hmem := hB t (β θ)
    change ((H (t, β θ) : (double 3 K).space) : E × E × ℝ) ∈
      ι '' S.boundaryNeighborhood.space at hmem
    obtain ⟨x, hx, hxeq⟩ := hmem
    have hxK : x ∈ K.space := hBsub hx
    have hπeq : π (H (t, β θ)) = x := by
      change glueSnd E E ((H (t, β θ) : (double 3 K).space) : E × E × ℝ) = x
      rw [← hxeq, hπi x hxK]
    exact hπeq ▸ hx
  have hπparam (θ : loopCircle) : π (H (0, β θ)) = (γ θ : E) := by
    rw [hzero (β θ)]
    change glueSnd E E ((G (β θ) : (double 3 K).space) : E × E × ℝ) = _
    rw [hparam θ]
    exact hπi _ (hBsub (γ θ).property)
  let η : freeLoop S.boundaryNeighborhoodSpace :=
    ⟨fun θ => ⟨π (H (1, β θ)), hπmem 1 θ⟩,
      (continuous_glueSnd.comp continuous_subtype_val).comp
        (H.continuous.comp (continuous_const.prodMk β.continuous)) |>.subtype_mk _⟩
  let hom : ContinuousMap.Homotopy γ η :=
    { toFun := fun z => ⟨π (H (z.1, β z.2)), hπmem z.1 z.2⟩
      continuous_toFun :=
        (continuous_glueSnd.comp continuous_subtype_val).comp
          (H.continuous.comp
            (continuous_fst.prodMk (β.continuous.comp continuous_snd))) |>.subtype_mk _
      map_zero_left := fun θ => Subtype.ext (hπparam θ)
      map_one_left := fun θ => rfl }
  have hηavoid : ¬loopClassMeets η S.basepoint S.normalSubgroup := by
    unfold loopClassMeets at havoid ⊢
    rw [(FreeLoop.conjugacyClass_eq_of_homotopic ⟨hom⟩ S.basepoint).symm]
    exact havoid
  obtain ⟨c⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one A.isPLSphere_frontier
  let cG : frontier G.domain ≃ₜ frontier A.domain :=
    Homeomorph.setCongr (congrArg frontier hdom.symm)
  let ρ : C(loopCircle, loopCircle) :=
    ⟨fun θ => c.symm (cG (β θ)),
      c.symm.continuous.comp (cG.continuous.comp β.continuous)⟩
  have hδmem (θ : loopCircle) : π (A (c θ)) ∈ S.boundaryNeighborhood.space := by
    let xG : frontier G.domain :=
      ⟨(c θ : EuclideanSpace ℝ (Fin 2)), by
        rw [← hdom]
        exact (c θ).property⟩
    obtain ⟨ζ, hζ⟩ := hsurj xG
    have hval : (β ζ : EuclideanSpace ℝ (Fin 2)) = (c θ : EuclideanSpace ℝ (Fin 2)) :=
      congrArg Subtype.val hζ
    have hAH : A (c θ) = H (1, β ζ) := by
      rw [hone (β ζ)]
      exact congrArg A hval.symm
    rw [hAH]
    exact hπmem 1 ζ
  let δ : freeLoop S.boundaryNeighborhoodSpace :=
    ⟨fun θ => ⟨π (A (c θ)), hδmem θ⟩, by
      refine Continuous.subtype_mk ?_ _
      exact (continuous_glueSnd.comp continuous_subtype_val).comp
        (A.continuousOn.comp_continuous (continuous_subtype_val.comp c.continuous)
          (fun θ => A.frontier_subset_domain (c θ).property))⟩
  have hηfac : η = δ.comp ρ := by
    apply ContinuousMap.ext
    intro θ
    apply Subtype.ext
    change π (H (1, β θ)) = π (A (c (ρ θ)))
    rw [hone (β θ)]
    congr 2
    have hc := congrArg Subtype.val (c.apply_symm_apply (cG (β θ)))
    exact hc.symm
  have hδavoid : ¬loopClassMeets δ S.basepoint S.normalSubgroup := by
    have := S.normal
    obtain ⟨F, n, hF, hshift⟩ := NormalSystem.exists_real_lift_intShift ρ
    have hpow := FreeLoop.conjugacyClass_comp_of_lift_intShift δ ρ F F.continuous n
      hF hshift S.basepoint
    have hpowAvoid :
        ¬conjugacyClassMeets
          (ConjClasses.mk (FreeLoop.fundamentalGroupRepresentative δ S.basepoint ^ n))
          S.normalSubgroup := by
      rw [← hpow, ← hηfac]
      exact hηavoid
    change ¬conjugacyClassMeets
      (ConjClasses.mk (FreeLoop.fundamentalGroupRepresentative δ S.basepoint))
      S.normalSubgroup
    exact NormalSystem.not_conjugacyClassMeets_of_not_conjugacyClassMeets_zpow
      (FreeLoop.fundamentalGroupRepresentative δ S.basepoint) n S.normalSubgroup hpowAvoid
  refine ⟨c, δ, ?_, hδavoid⟩
  · intro θ
    have hcdom : (c θ : EuclideanSpace ℝ (Fin 2)) ∈ A.domain :=
      A.frontier_subset_domain (c θ).property
    have hιπA : ι (π (A (c θ))) = (A (c θ) : E × E × ℝ) := by
      obtain ⟨x, hx, hxeq⟩ := hmap hcdom
      have hπA : π (A (c θ)) = x := by
        change glueSnd E E ((A (c θ) : (double 3 K).space) : E × E × ℝ) = x
        rw [← hxeq, hπi]
        exact hx
      change ι (π (A (c θ))) = (A (c θ) : E × E × ℝ)
      rw [hπA]
      exact hxeq
    change (A (c θ) : E × E × ℝ) = ι (δ θ)
    exact hιπA.symm

end DifferentialGeometry.Topology.PiecewiseLinear
