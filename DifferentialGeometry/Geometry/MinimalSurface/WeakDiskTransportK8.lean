import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskAreaTransportK8

/-!
# Route W：光滑 Morrey 类的 transport（IMS08′ kernel，G1′ + G2′，S-A14-KERNEL）

竞争者类（S-A08-ATTAIN 的 `morreyLeastAreaS` 的类）：
`{v : C(closedDisk, M) | DiskSmoothUpToBoundary v ∧ DiskWeakJordanTrace γ v ∧ range v ⊆ W}`。
不定义新 Prop；类的条件在每个定理里写出来，结论里的括号恰好是这个类的成员条件。

transport 只要求 `φ` 在 open `V ⊇ range v` 上 smooth（`ContMDiffOn`），所以
* 光滑性保持：`SmoothDiskExtension.map_contMDiffOn_K8`（`φ ∘ U` 在 `N ∩ U⁻¹' V` 上 smooth）；
* weak Jordan trace 保持（σ 不变，`DiskWeakJordanTrace.map_K8`）；
* `range` 保持：`MapsTo φ S W₂`（`S ⊇ range v`）；
* 面积：G2 `riemannianDiskArea_map_le_K8`（逐点 `φ^*g₂ ≤ c * g₁` 只在 `range v` 上要求）。
不需要 Lipschitz 保持、不需要 embedding / `mfderiv` injective。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

/-- weak Jordan trace 沿 `φ` 保持（σ 不变）。 -/
theorem DiskWeakJordanTrace.map_K8 {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
    {γ₁ : freeLoop M₁} {γ₂ : freeLoop M₂} {φ : M₁ → M₂} (hγ : ∀ θ, φ (γ₁ θ) = γ₂ θ)
    {v : C(closedDisk, M₁)} {w : C(closedDisk, M₂)} (hw : ∀ z, w z = φ (v z))
    (hv : DiskWeakJordanTrace γ₁ v) : DiskWeakJordanTrace γ₂ w := by
  obtain ⟨σ, hσ, htr⟩ := hv
  refine ⟨σ, hσ, ?_⟩
  ext θ
  have h1 : v (diskBoundary θ) = γ₁ (σ θ) := congrArg (fun f : freeLoop M₁ => f θ) htr
  change w (diskBoundary θ) = γ₂ (σ θ)
  rw [hw, h1, hγ]

/-- `range w ⊆ W₂`：`w = φ ∘ v`、`range v ⊆ S`、`MapsTo φ S W₂`。 -/
theorem range_map_subset_K8 {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
    {φ : M₁ → M₂} {S : Set M₁} {W₂ : Set M₂}
    {v : C(closedDisk, M₁)} {w : C(closedDisk, M₂)} (hw : ∀ z, w z = φ (v z))
    (hvS : range v ⊆ S) (hW : MapsTo φ S W₂) : range w ⊆ W₂ := by
  rintro _ ⟨z, rfl⟩
  rw [hw z]
  exact hW (hvS ⟨z, rfl⟩)

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [ChartedSpace E M₁] [IsManifold 𝓘(ℝ, E) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace E M₂] [IsManifold 𝓘(ℝ, E) ∞ M₂]

omit [IsManifold 𝓘(ℝ, E) ∞ M₁] [IsManifold 𝓘(ℝ, E) ∞ M₂] in
/-- `SmoothDiskExtension` 沿只在 open `V ⊇ range v` 上 smooth 的 `φ` 保持。 -/
theorem SmoothDiskExtension.map_contMDiffOn_K8 {v : C(closedDisk, M₁)} {U : ℂ → M₁}
    (hU : SmoothDiskExtension (E := E) v U) {φ : M₁ → M₂} {V : Set M₁} (hV : IsOpen V)
    (hrange : range v ⊆ V) (hφ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ V)
    {w : C(closedDisk, M₂)} (hw : ∀ z, w z = φ (v z)) :
    SmoothDiskExtension (E := E) w (φ ∘ U) := by
  obtain ⟨heq, N, hN, hDN, hUN⟩ := hU
  have hN' : IsOpen (N ∩ U ⁻¹' V) := hUN.continuousOn.isOpen_inter_preimage hN hV
  refine ⟨fun z => by rw [hw z, Function.comp_apply, heq z], N ∩ U ⁻¹' V, hN', fun z hz => ?_,
    hφ.comp (hUN.mono inter_subset_left) (fun z hz => hz.2)⟩
  refine ⟨hDN hz, hrange ⟨⟨z, hz⟩, ?_⟩⟩
  exact (heq ⟨z, hz⟩).symm

variable [CompleteSpace E]

/-- G1′ + G2′：光滑类 `{DiskSmoothUpToBoundary v ∧ DiskWeakJordanTrace γ₁ v ∧ range v ⊆ W₁}`
的元素 `v`，沿在 open `V ⊇ range v` 上 smooth 的 `φ`（`γ₁ ↦ γ₂`；`range v ⊆ S` 上
`MapsTo φ S W₂` 与逐点 `φ^*g₂ ≤ c * g₁`）变成 `(γ₂, W₂)` 光滑类的元素 `w = φ ∘ v`，
且 `area g₂ w ≤ c * area g₁ v`。 -/
theorem exists_smoothCompetitor_map_K8
    (g₁ : SmoothRiemannianMetric 𝓘(ℝ, E) M₁) (g₂ : SmoothRiemannianMetric 𝓘(ℝ, E) M₂)
    {W₂ : Set M₂} {γ₁ : freeLoop M₁} {γ₂ : freeLoop M₂} {φ : M₁ → M₂}
    (hγ : ∀ θ, φ (γ₁ θ) = γ₂ θ) {v : C(closedDisk, M₁)}
    (hvs : DiskSmoothUpToBoundary (E := E) v) (hv : DiskWeakJordanTrace γ₁ v)
    {V : Set M₁} (hV : IsOpen V) (hrange : range v ⊆ V)
    (hφ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ V)
    {S : Set M₁} (hS : range v ⊆ S) (hW : MapsTo φ S W₂) {c : ℝ} (hc : 0 < c)
    (hmetric : ∀ p ∈ S, ∀ w : TangentSpace 𝓘(ℝ, E) p,
      g₂.inner (φ p) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ p w) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ p w) ≤
        c * g₁.inner p w w) :
    ∃ w : C(closedDisk, M₂), (∀ z, w z = φ (v z)) ∧
      (DiskSmoothUpToBoundary (E := E) w ∧ DiskWeakJordanTrace γ₂ w ∧ range w ⊆ W₂) ∧
      riemannianDiskArea g₂ w ≤ c * riemannianDiskArea g₁ v := by
  obtain ⟨U, hU⟩ := exists_smoothDiskExtension_of_diskSmoothUpToBoundary hvs
  have hcont : Continuous (fun z => φ (v z)) :=
    hφ.continuousOn.comp_continuous v.continuous (fun z => hrange ⟨z, rfl⟩)
  have hw : ∀ z, (⟨fun z => φ (v z), hcont⟩ : C(closedDisk, M₂)) z = φ (v z) := fun z => rfl
  exact ⟨⟨fun z => φ (v z), hcont⟩, hw,
    ⟨(hU.map_contMDiffOn_K8 hV hrange hφ hw).smoothUpToBoundary,
      DiskWeakJordanTrace.map_K8 hγ hw hv, range_map_subset_K8 hw hS hW⟩,
    riemannianDiskArea_map_le_K8 g₁ g₂ hU hV hrange hφ hS hc hmetric _ hw⟩

/-- Consumer / non-vacuity：`φ = id`、`g₂ = scaleMetric c g₁`、`W₂ = W₁`，光滑类保持，
`area (c • g) w ≤ c * area g v`。 -/
example (g : SmoothRiemannianMetric 𝓘(ℝ, E) M₁) {W : Set M₁} {γ : freeLoop M₁}
    {v : C(closedDisk, M₁)} (hvs : DiskSmoothUpToBoundary (E := E) v)
    (hv : DiskWeakJordanTrace γ v) (hvW : range v ⊆ W) {c : ℝ} (hc : 0 < c) :
    ∃ w : C(closedDisk, M₁), (DiskSmoothUpToBoundary (E := E) w ∧ DiskWeakJordanTrace γ w ∧
        range w ⊆ W) ∧ riemannianDiskArea (scaleMetric c hc g) w ≤ c * riemannianDiskArea g v := by
  obtain ⟨w, _, hcls, harea⟩ := exists_smoothCompetitor_map_K8 g (scaleMetric c hc g) (φ := id)
    (fun θ => rfl) hvs hv isOpen_univ (subset_univ _) contMDiffOn_id hvW (mapsTo_id W) hc
    (fun p _ w => by
      rw [mfderiv_id]
      exact le_of_eq (scaleMetric_inner c hc g p w w))
  exact ⟨w, hcls, harea⟩

end Local

section Frozen

variable {M₀ M₁ : Type*}
  [TopologicalSpace M₀] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₀] [IsManifold (𝓡 3) ∞ M₀]
  [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [IsManifold (𝓡 3) ∞ M₁]

/-- **G1′ + G2′（O-IFACE 冻结的单向 transport packet 形状，光滑类）。**
`φ : M₀ → M₁`，open `K`，`ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ K`，`MapsTo φ (K ∩ W₀) W₁`，
`∀ θ, φ (γ₀ θ) = γ₁ θ`，`K` 上逐点 `g₁(dφ w, dφ w) ≤ c * g₀(w, w)`（`c > 0`）。
`v` 属于光滑类 `(W₀, γ₀)`（`DiskSmoothUpToBoundary v ∧ DiskWeakJordanTrace γ₀ v ∧ range v ⊆ W₀`）
且 `range v ⊆ K` ⇒ `w = φ ∘ v` 属于光滑类 `(W₁, γ₁)`，且 `area g₁ w ≤ c * area g₀ v`。
没有 injectivity / `mfderiv` injective / frontier 字段；不要求任何 Lipschitz 性。 -/
theorem smoothCompetitor_transport_K8
    (g₀ : SmoothRiemannianMetric (𝓡 3) M₀) (g₁ : SmoothRiemannianMetric (𝓡 3) M₁)
    {W₀ : Set M₀} {W₁ : Set M₁} {γ₀ : freeLoop M₀} {γ₁ : freeLoop M₁} {φ : M₀ → M₁}
    {K : Set M₀} {c : ℝ} (hc : 0 < c) (hK : IsOpen K)
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ K) (hW : MapsTo φ (K ∩ W₀) W₁)
    (hγ : ∀ θ, φ (γ₀ θ) = γ₁ θ)
    (hmetric : ∀ p ∈ K, ∀ w : TangentSpace (𝓡 3) p,
      g₁.inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w) (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
        c * g₀.inner p w w)
    {v : C(closedDisk, M₀)} (hvs : DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v)
    (hv : DiskWeakJordanTrace γ₀ v) (hvW : range v ⊆ W₀) (hvK : range v ⊆ K) :
    ∃ w : C(closedDisk, M₁), (∀ z, w z = φ (v z)) ∧
      (DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) w ∧ DiskWeakJordanTrace γ₁ w ∧
        range w ⊆ W₁) ∧
      riemannianDiskArea g₁ w ≤ c * riemannianDiskArea g₀ v :=
  exists_smoothCompetitor_map_K8 g₀ g₁ hγ hvs hv hK hvK hφ (S := K ∩ W₀)
    (fun _ hx => ⟨hvK hx, hvW hx⟩) hW hc (fun p hp => hmetric p hp.1)

/-- Consumer / non-vacuity：`φ = id`、`K = univ`、`c = 1`、`W₁ = W₀`：竞争者类在自身上封闭。 -/
example (g : SmoothRiemannianMetric (𝓡 3) M₀) {W : Set M₀} {γ : freeLoop M₀}
    {v : C(closedDisk, M₀)} (hvs : DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v)
    (hv : DiskWeakJordanTrace γ v) (hvW : range v ⊆ W) :
    ∃ w : C(closedDisk, M₀), (DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) w ∧
        DiskWeakJordanTrace γ w ∧ range w ⊆ W) ∧
      riemannianDiskArea g w ≤ 1 * riemannianDiskArea g v := by
  obtain ⟨w, _, hcls, harea⟩ := smoothCompetitor_transport_K8 g g (φ := id) (c := 1)
    one_pos isOpen_univ contMDiffOn_id (fun x hx => hx.2) (fun θ => rfl)
    (fun p _ w => by
      rw [mfderiv_id]
      exact le_of_eq (one_mul _).symm) hvs hv hvW (subset_univ _)
  exact ⟨w, hcls, harea⟩

end Frozen

end DifferentialGeometry.Geometry

end
