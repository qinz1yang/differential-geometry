import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskTransportK8
import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskAreaTransportK8

/-!
# IMS08 kernel，G3：由显式 transport data 得到 `hcomparison`（S-A14-KERNEL）

G1（`isExteriorSpanningDisk` 沿 φ transport）+ G2（`area g₂ (φ ∘ u) ≤ c * area g₁ u`）
合成 one-step transport lemma `exists_isExteriorSpanningDisk_area_le_K8`；
对固定 `t₀`、`ε` 与一族 `t`（`T ≤ t`，`|t - t₀| < δ`）各给一对映射
`φ : M t₀ → M t`、`ψ : M t → M t₀`（逐点性质，全部显式，没有新 structure），
得到 `continuousOn_leastExteriorDiskArea_of_local_disk_comparisons` 的 `hcomparison`
在 `(t₀, ε)` 处的实例；再对所有 `t₀`、`ε` 汇总并喂给该 continuity 定理。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.MinimalSurface

section OneStep

variable {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [IsManifold (𝓡 3) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] [IsManifold (𝓡 3) ∞ M₂]
  [T2Space M₂]

/-- One-step transport：`(W₁, γ₁)` 的 exterior spanning disk `u` 沿 `φ` 变成
`(W₂, γ₂)` 的 exterior spanning disk `v`，且 `area g₂ v ≤ c * area g₁ u`。 -/
theorem exists_isExteriorSpanningDisk_area_le_K8
    (g₁ : SmoothRiemannianMetric (𝓡 3) M₁) (g₂ : SmoothRiemannianMetric (𝓡 3) M₂)
    {W₁ : Set M₁} {W₂ : Set M₂} {γ₁ : freeLoop M₁} {γ₂ : freeLoop M₂}
    {φ : M₁ → M₂} {V : Set M₁} (hV : IsOpen V) (hWV : W₁ ⊆ V)
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ V)
    (hinj : InjOn φ W₁)
    (himm : ∀ p ∈ W₁, Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ p))
    (hW : MapsTo φ W₁ W₂) (hint : MapsTo φ (interior W₁) (interior W₂))
    (hfr : MapsTo φ (frontier W₁) (frontier W₂))
    (hγ : ∀ θ, φ (γ₁ θ) = γ₂ θ) {c : ℝ} (hc : 0 < c)
    (hmetric : ∀ p ∈ W₁, ∀ w : TangentSpace (𝓡 3) p,
      g₂.inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w) (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
        c * g₁.inner p w w)
    {u : C(closedDisk, M₁)} (hu : isExteriorSpanningDisk W₁ γ₁ u) :
    ∃ v : C(closedDisk, M₂), isExteriorSpanningDisk W₂ γ₂ v ∧
      riemannianDiskArea g₂ v ≤ c * riemannianDiskArea g₁ u := by
  obtain ⟨v, hv, hext⟩ := exists_isExteriorSpanningDisk_map_K8 hu hV hWV hφ hinj himm hW hint hfr hγ
  obtain ⟨_, _, _, hrange, _, U, hUext, _⟩ := hu
  exact ⟨v, hext, riemannianDiskArea_map_le_K8 g₁ g₂ hUext hV (hrange.trans hWV) hφ hrange hc
    hmetric v hv⟩

end OneStep

section Family

variable (M : ℝ → Type*) [∀ t, TopologicalSpace (M t)]
  [∀ t, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M t)] [∀ t, IsManifold (𝓡 3) ∞ (M t)]
  [∀ t, T2Space (M t)]

/-- G3：固定 `t₀`、`ε` 与 `δ`；对 `T ≤ t`、`|t - t₀| < δ` 有 forward 映射 `φ : M t₀ → M t`
与 backward 映射 `ψ : M t → M t₀`（各带 G1 + G2 的逐点性质，metric 常数 `exp ε`）⇒
`hcomparison` 在 `(t₀, ε)` 处的两向 comparison。 -/
theorem hcomparison_of_transport_K8
    (g : ∀ t, SmoothRiemannianMetric (𝓡 3) (M t))
    (W : ∀ t, Set (M t)) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (M t)) (t₀ : ℝ) (ht₀ : T ≤ t₀) (ε δ : ℝ)
    (hforward : ∀ (t : ℝ) (ht : T ≤ t), |t - t₀| < δ →
      ∃ (φ : M t₀ → M t) (V : Set (M t₀)), IsOpen V ∧ W t₀ ⊆ V ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ V ∧ InjOn φ (W t₀) ∧
        (∀ p ∈ W t₀, Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ p)) ∧
        MapsTo φ (W t₀) (W t) ∧ MapsTo φ (interior (W t₀)) (interior (W t)) ∧
        MapsTo φ (frontier (W t₀)) (frontier (W t)) ∧
        (∀ θ, φ (γ t₀ ht₀ θ) = γ t ht θ) ∧
        ∀ p ∈ W t₀, ∀ w : TangentSpace (𝓡 3) p,
          (g t).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w) (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
            Real.exp ε * (g t₀).inner p w w)
    (hbackward : ∀ (t : ℝ) (ht : T ≤ t), |t - t₀| < δ →
      ∃ (ψ : M t → M t₀) (V : Set (M t)), IsOpen V ∧ W t ⊆ V ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ ψ V ∧ InjOn ψ (W t) ∧
        (∀ p ∈ W t, Function.Injective (mfderiv (𝓡 3) (𝓡 3) ψ p)) ∧
        MapsTo ψ (W t) (W t₀) ∧ MapsTo ψ (interior (W t)) (interior (W t₀)) ∧
        MapsTo ψ (frontier (W t)) (frontier (W t₀)) ∧
        (∀ θ, ψ (γ t ht θ) = γ t₀ ht₀ θ) ∧
        ∀ p ∈ W t, ∀ w : TangentSpace (𝓡 3) p,
          (g t₀).inner (ψ p) (mfderiv (𝓡 3) (𝓡 3) ψ p w) (mfderiv (𝓡 3) (𝓡 3) ψ p w) ≤
            Real.exp ε * (g t).inner p w w) :
    ∀ (t : ℝ) (ht : T ≤ t), |t - t₀| < δ →
      (∀ u : C(closedDisk, M t₀), isExteriorSpanningDisk (W t₀) (γ t₀ ht₀) u →
        riemannianDiskArea (g t₀) u = leastExteriorDiskArea (g t₀) (W t₀) (γ t₀ ht₀) →
        ∃ v : C(closedDisk, M t), isExteriorSpanningDisk (W t) (γ t ht) v ∧
          riemannianDiskArea (g t) v ≤ Real.exp ε * riemannianDiskArea (g t₀) u) ∧
      (∀ v : C(closedDisk, M t), isExteriorSpanningDisk (W t) (γ t ht) v →
        riemannianDiskArea (g t) v = leastExteriorDiskArea (g t) (W t) (γ t ht) →
        ∃ u : C(closedDisk, M t₀), isExteriorSpanningDisk (W t₀) (γ t₀ ht₀) u ∧
          riemannianDiskArea (g t₀) u ≤ Real.exp ε * riemannianDiskArea (g t) v) := by
  intro t ht hd
  constructor
  · intro u hu _
    obtain ⟨φ, V, hV, hWV, hφ, hinj, himm, hW, hint, hfr, hγ, hmet⟩ := hforward t ht hd
    exact exists_isExteriorSpanningDisk_area_le_K8 (g t₀) (g t) hV hWV hφ hinj himm hW hint hfr
      hγ (Real.exp_pos ε) hmet hu
  · intro v hv _
    obtain ⟨ψ, V, hV, hWV, hψ, hinj, himm, hW, hint, hfr, hγ, hmet⟩ := hbackward t ht hd
    exact exists_isExteriorSpanningDisk_area_le_K8 (g t) (g t₀) hV hWV hψ hinj himm hW hint hfr
      hγ (Real.exp_pos ε) hmet hv

/-- Consumer / non-vacuity：常值 family（`M t = N`、`g t = g₀`、`W t = W`、`γ t = γ₀`），
transport 取 `φ = ψ = id`、`ε ≥ 0`，所有 hypotheses 都被满足，
`hcomparison_of_transport_K8` 给出该 family 的两向 comparison。 -/
example {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] [T2Space N] (g₀ : SmoothRiemannianMetric (𝓡 3) N) (W : Set N)
    (T : ℝ) (γ₀ : freeLoop N) (t₀ : ℝ) (ht₀ : T ≤ t₀) (ε δ : ℝ) (hε : 0 ≤ ε) :
    ∀ (t : ℝ) (_ : T ≤ t), |t - t₀| < δ →
      (∀ u : C(closedDisk, N), isExteriorSpanningDisk W γ₀ u →
        riemannianDiskArea g₀ u = leastExteriorDiskArea g₀ W γ₀ →
        ∃ v : C(closedDisk, N), isExteriorSpanningDisk W γ₀ v ∧
          riemannianDiskArea g₀ v ≤ Real.exp ε * riemannianDiskArea g₀ u) ∧
      (∀ v : C(closedDisk, N), isExteriorSpanningDisk W γ₀ v →
        riemannianDiskArea g₀ v = leastExteriorDiskArea g₀ W γ₀ →
        ∃ u : C(closedDisk, N), isExteriorSpanningDisk W γ₀ u ∧
          riemannianDiskArea g₀ u ≤ Real.exp ε * riemannianDiskArea g₀ v) := by
  have hid : ∃ (φ : N → N) (V : Set N), IsOpen V ∧ W ⊆ V ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ V ∧ InjOn φ W ∧
      (∀ p ∈ W, Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ p)) ∧
      MapsTo φ W W ∧ MapsTo φ (interior W) (interior W) ∧
      MapsTo φ (frontier W) (frontier W) ∧ (∀ θ, φ (γ₀ θ) = γ₀ θ) ∧
      ∀ p ∈ W, ∀ w : TangentSpace (𝓡 3) p,
        g₀.inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w) (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
          Real.exp ε * g₀.inner p w w := by
    refine ⟨id, univ, isOpen_univ, subset_univ W, contMDiffOn_id, injOn_id W,
      fun p _ => ?_, mapsTo_id W, mapsTo_id _, mapsTo_id _, fun θ => rfl, fun p _ w => ?_⟩
    · rw [mfderiv_id]
      exact fun a b h => h
    · rw [mfderiv_id]
      exact le_mul_of_one_le_left (metric_inner_self_nonneg g₀ p w) (Real.one_le_exp hε)
  exact hcomparison_of_transport_K8 (fun _ => N) (fun _ => g₀) (fun _ => W) T (fun _ _ => γ₀)
    t₀ ht₀ ε δ (fun _ _ _ => hid) (fun _ _ _ => hid)

end Family

end DifferentialGeometry.Geometry.MinimalSurface

end
