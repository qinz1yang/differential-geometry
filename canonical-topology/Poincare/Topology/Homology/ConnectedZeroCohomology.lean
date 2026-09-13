import Poincare.Topology.Homology.CapHomology
import Poincare.Topology.Homology.PathChains
import Poincare.Topology.Homology.ZeroAugmentation

noncomputable section

open CategoryTheory AlgebraicTopology

universe u

namespace Poincare.Topology

private theorem integralSingularCocycle_zero_eq_smul_augmentation
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] (a : X)
    (φ : integralSingularCochain 0 X) (hφ : integralSingularCoboundary X 0 1 φ = 0) :
    φ = (φ (integralVertexChain a)).down •
      ((ULift.moduleEquiv : integralSingularCoefficients ≃ₗ[ℤ] ℤ).symm.toLinearMap.comp
        integralSingularAugmentation) := by
  apply (integralSingularChainBasis 0 X).ext
  intro σ
  rw [integralSingularChainBasis_apply]
  have h := LinearMap.congr_fun hφ
    (integralPathChain (PathConnectedSpace.somePath a (TopCat.toSSetObj₀Equiv σ)))
  change φ ((integralSingularChains X).d 1 0
    (integralPathChain (PathConnectedSpace.somePath a (TopCat.toSSetObj₀Equiv σ)))) = 0 at h
  rw [integralPathChain_boundary, map_sub, sub_eq_zero] at h
  have hv : φ (integralSimplexChain 0 σ) = φ (integralVertexChain a) := by
    simpa only [integralVertexChain, Equiv.symm_apply_apply] using h
  change φ (integralSimplexChain 0 σ) =
    (φ (integralVertexChain a)).down • ULift.up
      (integralSingularAugmentation (integralSimplexChain 0 σ))
  rw [integralSingularAugmentation_simplex, hv]
  apply ULift.down_injective
  simp

private theorem integralSingularCohomologyClass_zero_eq_smul_unit
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] (a : X)
    (φ : LinearMap.ker ((integralSingularCochains X).sc 0).g.hom) :
    moduleHomologyClass ((integralSingularCochains X).sc 0) φ =
      ((show integralSingularCochain 0 X from φ.val) (integralVertexChain a)).down •
        integralSingularCohomologyUnit X := by
  let ψ : integralSingularCochain 0 X := φ.val
  symm
  unfold integralSingularCohomologyUnit
  dsimp only
  erw [← map_zsmul]
  congr 1
  apply Subtype.ext
  change (ψ (integralVertexChain a)).down •
    ((ULift.moduleEquiv : integralSingularCoefficients ≃ₗ[ℤ] ℤ).symm.toLinearMap.comp
      integralSingularAugmentation) = φ.val
  apply (integralSingularCocycle_zero_eq_smul_augmentation a φ.val ?_).symm
  have h := φ.property
  change integralSingularCoboundary X 0 ((ComplexShape.up ℕ).next 0) φ.val = 0 at h
  rwa [CochainComplex.next] at h

private theorem integralSingularCohomologyUnit_smul_surjective
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] :
    Function.Surjective (fun z : ℤ => z • integralSingularCohomologyUnit X) := by
  intro α
  obtain ⟨φ, rfl⟩ := moduleHomologyClass_surjective ((integralSingularCochains X).sc 0) α
  let a : X := Classical.choice inferInstance
  let ψ : integralSingularCochain 0 X := φ.val
  exact ⟨(ψ (integralVertexChain a)).down,
    (integralSingularCohomologyClass_zero_eq_smul_unit a φ).symm⟩

private theorem integralSingularCohomologyUnit_smul_injective
    {X : Type u} [TopologicalSpace X] [Nonempty X] :
    Function.Injective (fun z : ℤ => z • integralSingularCohomologyUnit X) := by
  intro z w h
  let a : X := Classical.choice inferInstance
  let c := integralZeroChainClass (integralVertexChain a)
  have heq := congrArg (fun α => integralSingularCohomologyCapProduct 0 0 α c) h
  erw [map_zsmul, map_zsmul] at heq
  change z • integralSingularCohomologyCapProduct 0 0 (integralSingularCohomologyUnit X) c =
    w • integralSingularCohomologyCapProduct 0 0 (integralSingularCohomologyUnit X) c at heq
  rw [integralSingularCohomologyCapProduct_unit] at heq
  have ha := congrArg integralZeroAugmentation heq
  change integralZeroAugmentation (z • c) = integralZeroAugmentation (w • c) at ha
  rw [map_zsmul, map_zsmul] at ha
  change z • integralZeroAugmentation (integralZeroChainClass (integralVertexChain a)) =
    w • integralZeroAugmentation (integralZeroChainClass (integralVertexChain a)) at ha
  simpa only [integralZeroAugmentation_vertex, smul_eq_mul, mul_one] using ha

private theorem integralSingularCohomologyUnit_span_apply
    (X : Type u) [TopologicalSpace X] (z : ℤ) :
    LinearMap.toSpanSingleton ℤ (integralSingularCohomology 0 X)
      (integralSingularCohomologyUnit X) z = z • integralSingularCohomologyUnit X := by
  change (ModuleCat.isModule (integralSingularCohomology 0 X)).smul z
    (integralSingularCohomologyUnit X) = _
  exact int_smul_eq_zsmul _ z _

def integralSingularCohomologyZeroEquiv
    (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] :
    integralSingularCohomology 0 X ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℤ (integralSingularCohomology 0 X)
      (integralSingularCohomologyUnit X))
    ⟨by
      intro z w h
      rw [integralSingularCohomologyUnit_span_apply,
        integralSingularCohomologyUnit_span_apply] at h
      exact integralSingularCohomologyUnit_smul_injective h, by
      intro α
      obtain ⟨z, hz⟩ := integralSingularCohomologyUnit_smul_surjective α
      exact ⟨z, (integralSingularCohomologyUnit_span_apply X z).trans hz⟩⟩).symm

theorem integralSingularCohomologyZeroEquiv_symm_apply
    (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (z : ℤ) :
    (integralSingularCohomologyZeroEquiv X).symm z = z • integralSingularCohomologyUnit X := by
  change LinearMap.toSpanSingleton ℤ (integralSingularCohomology 0 X)
    (integralSingularCohomologyUnit X) z = _
  exact integralSingularCohomologyUnit_span_apply X z

theorem integralSingularCohomologyZeroEquiv_unit
    (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] :
    integralSingularCohomologyZeroEquiv X (integralSingularCohomologyUnit X) = 1 := by
  apply (integralSingularCohomologyZeroEquiv X).symm.injective
  rw [LinearEquiv.symm_apply_apply, integralSingularCohomologyZeroEquiv_symm_apply, one_smul]

theorem integralSingularCohomologyZeroEquiv_class
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] (a : X)
    (φ : LinearMap.ker ((integralSingularCochains X).sc 0).g.hom) :
    integralSingularCohomologyZeroEquiv X
        (moduleHomologyClass ((integralSingularCochains X).sc 0) φ) =
      ((show integralSingularCochain 0 X from φ.val) (integralVertexChain a)).down := by
  rw [integralSingularCohomologyClass_zero_eq_smul_unit a φ, map_zsmul,
    integralSingularCohomologyZeroEquiv_unit]
  simp only [zsmul_eq_mul, mul_one, Int.cast_id]

theorem integralSingularCohomologyZeroEquiv_natural
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : ContinuousMap X Y)
    (α : integralSingularCohomology 0 Y) :
    integralSingularCohomologyZeroEquiv X (integralSingularCohomologyMap 0 f α) =
      integralSingularCohomologyZeroEquiv Y α := by
  obtain ⟨z, rfl⟩ := integralSingularCohomologyUnit_smul_surjective α
  rw [map_zsmul, integralSingularCohomologyMap_unit, map_zsmul, map_zsmul,
    integralSingularCohomologyZeroEquiv_unit, integralSingularCohomologyZeroEquiv_unit]

theorem integralSingularCohomologyCapProduct_zero
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] (m : ℕ)
    (α : integralSingularCohomology 0 X) (c : integralSingularHomology (0 + m) X) :
    integralSingularCohomologyCapProduct 0 m α c =
      integralSingularCohomologyZeroEquiv X α •
        (eqToHom (congrArg (fun n => integralSingularHomology n X) (Nat.zero_add m))) c := by
  obtain ⟨z, rfl⟩ := integralSingularCohomologyUnit_smul_surjective α
  erw [map_zsmul]
  change z • integralSingularCohomologyCapProduct 0 m (integralSingularCohomologyUnit X) c = _
  rw [integralSingularCohomologyCapProduct_unit, map_zsmul,
    integralSingularCohomologyZeroEquiv_unit]
  simp only [zsmul_eq_mul, mul_one, Int.cast_id]

theorem integralSingularCohomologyCapProduct_zero_bijective_iff
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] (m : ℕ)
    (c : integralSingularHomology (0 + m) X) :
    Function.Bijective (fun α : integralSingularCohomology 0 X =>
      integralSingularCohomologyCapProduct 0 m α c) ↔
      Function.Bijective (fun z : ℤ => z •
        (eqToHom (congrArg (fun n => integralSingularHomology n X) (Nat.zero_add m))) c) := by
  have hu : Function.Bijective (fun z : ℤ => z • integralSingularCohomologyUnit X) :=
    ⟨integralSingularCohomologyUnit_smul_injective, integralSingularCohomologyUnit_smul_surjective⟩
  rw [← Function.Bijective.of_comp_iff
    (fun α : integralSingularCohomology 0 X => integralSingularCohomologyCapProduct 0 m α c) hu]
  have heq : (fun α : integralSingularCohomology 0 X => integralSingularCohomologyCapProduct 0 m α c) ∘
      (fun z : ℤ => z • integralSingularCohomologyUnit X) =
      (fun z : ℤ => z •
        (eqToHom (congrArg (fun n => integralSingularHomology n X) (Nat.zero_add m))) c) := by
    funext z
    dsimp only [Function.comp_apply]
    rw [integralSingularCohomologyCapProduct_zero, map_zsmul,
      integralSingularCohomologyZeroEquiv_unit]
    simp only [zsmul_eq_mul, mul_one, Int.cast_id]
  rw [heq]

end Poincare.Topology

end
