import DifferentialGeometry.Geometry.Metric.ExteriorPowerBundle
import DifferentialGeometry.Bundle.Equiv

noncomputable section

open scoped Bundle Manifold ContDiff Topology

namespace Bundle.ExteriorPower

variable {B : Type*} [TopologicalSpace B]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ : B → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, InnerProductSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  {V₂ : B → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, InnerProductSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]

private theorem map_inCoordinates (k : ℕ) (x y : B)
    (h₁ : y ∈ (trivializationAt F₁ V₁ x).baseSet)
    (h₂ : y ∈ (trivializationAt F₂ V₂ x).baseSet) (φ : V₁ y →L[ℝ] V₂ y) :
    letI : ∀ z, FiniteDimensional ℝ (V₁ z) := fun z => VectorBundle.finiteDimensional ℝ F₁ V₁ z
    letI : ∀ z, FiniteDimensional ℝ (V₂ z) := fun z => VectorBundle.finiteDimensional ℝ F₂ V₂ z
    letI := totalSpaceTopology F₁ V₁ k
    letI := fiberBundle F₁ V₁ k
    letI := vector_bundle F₁ V₁ k
    letI := totalSpaceTopology F₂ V₂ k
    letI := fiberBundle F₂ V₂ k
    letI := vector_bundle F₂ V₂ k
    ContinuousLinearMap.inCoordinates (⋀[ℝ]^k F₁) (fun z => ⋀[ℝ]^k (V₁ z))
        (⋀[ℝ]^k F₂) (fun z => ⋀[ℝ]^k (V₂ z)) x y x y
        (exteriorPower.mapContinuousLinearMap k φ) =
      exteriorPower.mapContinuousLinearMap k
        (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x y x y φ) := by
  let : ∀ z, FiniteDimensional ℝ (V₁ z) := fun z => VectorBundle.finiteDimensional ℝ F₁ V₁ z
  let : ∀ z, FiniteDimensional ℝ (V₂ z) := fun z => VectorBundle.finiteDimensional ℝ F₂ V₂ z
  let := totalSpaceTopology F₁ V₁ k
  let := fiberBundle F₁ V₁ k
  let := vector_bundle F₁ V₁ k
  let := totalSpaceTopology F₂ V₂ k
  let := fiberBundle F₂ V₂ k
  let := vector_bundle F₂ V₂ k
  apply ContinuousLinearMap.ext
  intro u
  have h₁e : y ∈ (trivializationAt (⋀[ℝ]^k F₁) (fun z => ⋀[ℝ]^k (V₁ z)) x).baseSet := h₁
  have h₂e : y ∈ (trivializationAt (⋀[ℝ]^k F₂) (fun z => ⋀[ℝ]^k (V₂ z)) x).baseSet := h₂
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.symmL_apply _ h₁e, trivializationAt_eq F₁ V₁ k x,
    trivialization_symm_apply F₁ V₁ k _ h₁,
    Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ h₂e,
    trivializationAt_eq F₂ V₂ k x, trivialization_apply]
  change exteriorPower.map k ((trivializationAt F₂ V₂ x).continuousLinearMapAt ℝ y).toLinearMap
      (exteriorPower.map k φ.toLinearMap
        (exteriorPower.map k ((trivializationAt F₁ V₁ x).symmL ℝ y).toLinearMap u)) = _
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp,
    ← LinearMap.comp_apply, ← exteriorPower.map_comp]
  rfl

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [ChartedSpace HB B]

theorem contMDiff_mapContinuousLinearMap (k : ℕ) (n : ℕ∞ω)
    (φ : ∀ x, V₁ x →L[ℝ] V₂ x)
    (hφ : ContMDiff IB (IB.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) n
      (fun x => (⟨x, φ x⟩ : TotalSpace (F₁ →L[ℝ] F₂) (fun y => V₁ y →L[ℝ] V₂ y)))) :
    letI : ∀ z, FiniteDimensional ℝ (V₁ z) := fun z => VectorBundle.finiteDimensional ℝ F₁ V₁ z
    letI : ∀ z, FiniteDimensional ℝ (V₂ z) := fun z => VectorBundle.finiteDimensional ℝ F₂ V₂ z
    letI := totalSpaceTopology F₁ V₁ k
    letI := fiberBundle F₁ V₁ k
    letI := vector_bundle F₁ V₁ k
    letI := totalSpaceTopology F₂ V₂ k
    letI := fiberBundle F₂ V₂ k
    letI := vector_bundle F₂ V₂ k
    ContMDiff IB (IB.prod 𝓘(ℝ, (⋀[ℝ]^k F₁) →L[ℝ] ⋀[ℝ]^k F₂)) n
      (fun x => (⟨x, exteriorPower.mapContinuousLinearMap k (φ x)⟩ :
        TotalSpace ((⋀[ℝ]^k F₁) →L[ℝ] ⋀[ℝ]^k F₂)
          (fun y => (⋀[ℝ]^k (V₁ y)) →L[ℝ] ⋀[ℝ]^k (V₂ y)))) := by
  let : ∀ z, FiniteDimensional ℝ (V₁ z) := fun z => VectorBundle.finiteDimensional ℝ F₁ V₁ z
  let : ∀ z, FiniteDimensional ℝ (V₂ z) := fun z => VectorBundle.finiteDimensional ℝ F₂ V₂ z
  let := totalSpaceTopology F₁ V₁ k
  let := fiberBundle F₁ V₁ k
  let := vector_bundle F₁ V₁ k
  let := totalSpaceTopology F₂ V₂ k
  let := fiberBundle F₂ V₂ k
  let := vector_bundle F₂ V₂ k
  intro x
  have hx := hφ x
  rw [contMDiffAt_hom_bundle] at hx ⊢
  refine ⟨contMDiffAt_id, ?_⟩
  have h := (exteriorPower.contDiff_mapContinuousLinearMap (E := F₁) (F := F₂) k n).contMDiff.contMDiffAt.comp
    x hx.2
  apply h.congr_of_eventuallyEq
  filter_upwards [(trivializationAt F₁ V₁ x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F₁ V₁ x), (trivializationAt F₂ V₂ x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F₂ V₂ x)] with y h₁ h₂
  exact map_inCoordinates k x y h₁ h₂ (φ y)

end Bundle.ExteriorPower
