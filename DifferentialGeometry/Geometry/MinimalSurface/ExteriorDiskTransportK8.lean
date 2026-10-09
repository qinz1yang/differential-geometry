import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskArea

/-!
# `isExteriorSpanningDisk` 沿 smooth 映射 φ 的 transport（IMS08 kernel，G1，S-A14-KERNEL）

`φ : M₁ → M₂` 在 open `V ⊇ W₁` 上 smooth，在 `W₁` 上 injective 且 `mfderiv` injective，
并满足 `φ` 把 `W₁`、`interior W₁`、`frontier W₁` 分别送进 `W₂`、`interior W₂`、`frontier W₂`、
把 `γ₁` 送到 `γ₂`，则 `φ ∘ u` 是 `(W₂, γ₂)` 的 exterior spanning disk。
全部以显式函数与性质参数陈述（没有新 structure / 新具名 Prop）。
`φ` 不要求全局连续：`v z = φ (u z)` 逐点刻画 transported disk。
`M₂` 是 T2（OrientedThreeStage.Carrier 提供），所以 compact disk 上的 continuous injective map
自动是 embedding，不需要把 `IsEmbedding φ` 当假设。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set
open Filter Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.MinimalSurface

variable {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] [T2Space M₂]

/-- G1 主定理（存在形式）：exterior spanning disk `u` 沿 `φ` transport 成
`(W₂, γ₂)` 的 exterior spanning disk `v = φ ∘ u`。 -/
theorem exists_isExteriorSpanningDisk_map_K8
    {W₁ : Set M₁} {W₂ : Set M₂} {γ₁ : freeLoop M₁} {γ₂ : freeLoop M₂}
    {u : C(closedDisk, M₁)} (hu : isExteriorSpanningDisk W₁ γ₁ u)
    {φ : M₁ → M₂} {V : Set M₁} (hV : IsOpen V) (hWV : W₁ ⊆ V)
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ V)
    (hinj : InjOn φ W₁)
    (himm : ∀ p ∈ W₁, Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ p))
    (hW : MapsTo φ W₁ W₂) (hint : MapsTo φ (interior W₁) (interior W₂))
    (hfr : MapsTo φ (frontier W₁) (frontier W₂))
    (hγ : ∀ θ, φ (γ₁ θ) = γ₂ θ) :
    ∃ v : C(closedDisk, M₂), (∀ z, v z = φ (u z)) ∧ isExteriorSpanningDisk W₂ γ₂ v := by
  obtain ⟨htrace, hloop, hemb, hrange, hint', U, hUext, hUinj⟩ := hu
  have hu1 : ∀ z, u z ∈ W₁ := fun z => hrange ⟨z, rfl⟩
  have hcont : Continuous (fun z => φ (u z)) :=
    hφ.continuousOn.comp_continuous u.continuous (fun z => hWV (hu1 z))
  have hinjv : Function.Injective (fun z => φ (u z)) := fun z w h =>
    hemb.injective (hinj (hu1 z) (hu1 w) h)
  refine ⟨⟨fun z => φ (u z), hcont⟩, fun z => rfl, ?_, ?_,
    (hcont.isClosedEmbedding hinjv).isEmbedding, ?_, ?_, ?_⟩
  · ext θ
    have h1 : u (diskBoundary θ) = γ₁ θ := by
      rw [← htrace]; rfl
    change φ (u (diskBoundary θ)) = γ₂ θ
    rw [h1, hγ]
  · rintro _ ⟨θ, rfl⟩
    rw [← hγ θ]
    exact hfr (hloop ⟨θ, rfl⟩)
  · rintro _ ⟨z, rfl⟩
    exact hW (hu1 z)
  · intro z hz
    exact hint (hint' z hz)
  · obtain ⟨heq, N, hN, hDN, hUN⟩ := hUext
    have hUz : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, U z ∈ W₁ := fun z hz => by
      have := heq ⟨z, hz⟩
      rw [this]
      exact hu1 ⟨z, hz⟩
    have hN' : IsOpen (N ∩ U ⁻¹' V) := hUN.continuousOn.isOpen_inter_preimage hN hV
    refine ⟨φ ∘ U, ⟨fun z => congrArg φ (heq z), N ∩ U ⁻¹' V, hN', ?_,
      hφ.comp (hUN.mono inter_subset_left) (fun z hz => hz.2)⟩, ?_⟩
    · intro z hz
      exact ⟨hDN hz, hWV (hUz z hz)⟩
    · intro z hz
      have hUd : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓡 3) U z :=
        (hUN.mdifferentiableOn (by simp)).mdifferentiableAt (hN.mem_nhds (hDN hz))
      have hφd : MDifferentiableAt (𝓡 3) (𝓡 3) φ (U z) :=
        (hφ.mdifferentiableOn (by simp)).mdifferentiableAt
          (hV.mem_nhds (hWV (hUz z hz)))
      rw [mfderiv_comp z hφd hUd]
      exact (himm _ (hUz z hz)).comp (hUinj z hz)

/-- G1 主定理（给定 `v` 的形式，简报里的 `isExteriorSpanningDisk_map_K8`）。 -/
theorem isExteriorSpanningDisk_map_K8
    {W₁ : Set M₁} {W₂ : Set M₂} {γ₁ : freeLoop M₁} {γ₂ : freeLoop M₂}
    {u : C(closedDisk, M₁)} (hu : isExteriorSpanningDisk W₁ γ₁ u)
    {φ : M₁ → M₂} {V : Set M₁} (hV : IsOpen V) (hWV : W₁ ⊆ V)
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ V)
    (hinj : InjOn φ W₁)
    (himm : ∀ p ∈ W₁, Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ p))
    (hW : MapsTo φ W₁ W₂) (hint : MapsTo φ (interior W₁) (interior W₂))
    (hfr : MapsTo φ (frontier W₁) (frontier W₂))
    (hγ : ∀ θ, φ (γ₁ θ) = γ₂ θ)
    (v : C(closedDisk, M₂)) (hv : ∀ z, v z = φ (u z)) :
    isExteriorSpanningDisk W₂ γ₂ v := by
  obtain ⟨v', hv', h⟩ := exists_isExteriorSpanningDisk_map_K8 hu hV hWV hφ hinj himm hW hint hfr hγ
  have : v = v' := ContinuousMap.ext fun z => (hv z).trans (hv' z).symm
  rwa [this]

/-- Consumer / non-vacuity：`φ = id` 满足 G1 的全部假设，所以 transport 回到原来的 disk。
这里同时检查 hypotheses 的形状（`mfderiv id` injective、三个 `MapsTo`）是 inhabited 的。 -/
example {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)} (hu : isExteriorSpanningDisk W γ u) :
    isExteriorSpanningDisk W γ u := by
  refine isExteriorSpanningDisk_map_K8 (φ := id) hu isOpen_univ (subset_univ W)
    contMDiffOn_id (injOn_id W) (fun p _ => ?_) (mapsTo_id W) (mapsTo_id _) (mapsTo_id _)
    (fun θ => rfl) u (fun z => rfl)
  rw [mfderiv_id]
  exact fun a b h => h

end DifferentialGeometry.Geometry.MinimalSurface

end
