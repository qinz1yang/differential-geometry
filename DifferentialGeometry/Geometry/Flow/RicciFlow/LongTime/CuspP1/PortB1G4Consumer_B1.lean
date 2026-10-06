import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CoveringLift
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.LocalDiffeomorphLift
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.LocalDiffeomorphLiftLipschitz
import DifferentialGeometry.Topology.Covering.PuncturedBallMonodromy
import DifferentialGeometry.Topology.Covering.PuncturedBallConnected
import DifferentialGeometry.Topology.Covering.FiniteOrderedFiber
import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone.CoveringLift

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff NNReal ENNReal

-- S-MY-PORT-B1 G4 consumer：C9（covering 11 文件，verbatim IMS03）的型检查。
-- 主 consumer 是 `IsSmoothEmbeddedLoop.of_lift_through_localDiffeomorph`；其余 example 把
-- C9 的 lift 管线（metric-Lipschitz lift → Morrey 盘 lift → covering lift）逐个型检查。

section LoopLift

variable {E M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace E N]

-- `CoveringLift.lean:46`：Morrey 盘的边界 loop `γ` 是 smooth embedded loop，经 local
-- diffeomorphism `p : N → M` 的连续 lift `γLift` 仍是 smooth embedded loop，并且
-- 参数导数处处非零（真正使用结论：取出 embedding 与 immersed 两个分量）。
example
    {γ : freeLoop M} (hγ : IsSmoothEmbeddedLoop (E := E) γ) {p : N → M}
    (hps : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ p)
    (γLift : freeLoop N) (hloop : ∀ θ, p (γLift θ) = γ θ) :
    Topology.IsEmbedding γLift ∧
      ∀ t : ℝ, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γLift (s : loopCircle)) t 1 ≠ 0 :=
  let hγLift : IsSmoothEmbeddedLoop (E := E) γLift :=
    IsSmoothEmbeddedLoop.of_lift_through_localDiffeomorph hγ hps γLift hloop
  ⟨hγLift.embedding, hγLift.immersed⟩

end LoopLift

section DiskLift

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N] [T2Space N]

-- `LocalDiffeomorphLiftLipschitz.lean:28`：metric-Lipschitz 盘经 local diffeomorphism 的
-- 连续 lift 对 pullback metric 仍 metric-Lipschitz。
example
    (g : SmoothRiemannianMetric 𝓘(ℝ, F) N) (p : M → N)
    (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p x))
    (hps : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (u : C(closedDisk, N)) {L : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (uLift : C(closedDisk, M)) (hmap : ∀ z, p (uLift z) = u z) :
    ∃ K : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf (g.pullback p hp himm) (uLift z) (uLift w) ≤
        (K : ℝ≥0∞) * edist z w :=
  exists_lipschitz_disk_lift_of_localDiffeomorph g p hp himm hps u hu uLift hmap

-- `LocalDiffeomorphLift.lean:127`：同一 Morrey 盘的 lift 是 pullback metric 的 Morrey 盘。
-- 用 `exists_lipschitz_disk_lift_of_localDiffeomorph` 自动产生 `hLift`（管线串联）。
example
    {g : SmoothRiemannianMetric 𝓘(ℝ, F) N} {γ : freeLoop N} {u : C(closedDisk, N)}
    (hu : IsMorreyDisk g γ u) (p : M → N)
    (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p x))
    (hps : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (uLift : C(closedDisk, M)) (γLift : freeLoop M)
    (hmap : ∀ z, p (uLift z) = u z) (hloop : ∀ θ, p (γLift θ) = γ θ)
    (htrace : DiskWeakJordanTrace γLift uLift) {L : ℝ≥0}
    (hLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w) :
    IsMorreyDisk (g.pullback p hp himm) γLift uLift := by
  obtain ⟨K, hK⟩ :=
    exists_lipschitz_disk_lift_of_localDiffeomorph g p hp himm hps u hLip uLift hmap
  exact hu.of_localDiffeomorph_lift p hp himm hps uLift γLift hmap hloop htrace hK

-- `ImmersionLift.lean:31`：lift 盘对 pullback metric 的 weak-Jordan-trace Lipschitz 比较律。
example
    {g : SmoothRiemannianMetric 𝓘(ℝ, F) N}
    {γ : freeLoop N} {u : C(closedDisk, N)} (hu : IsMorreyDisk g γ u)
    (p : M → N) (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p x))
    (uLift : C(closedDisk, M)) (γLift : freeLoop M)
    (hmap : ∀ z, p (uLift z) = u z) (hloop : ∀ θ, p (γLift θ) = γ θ)
    {C : ℝ≥0}
    (hLift : ∀ z w, riemannianEDistOf (g.pullback p hp himm) (uLift z) (uLift w) ≤
      (C : ℝ≥0∞) * edist z w)
    (v : C(closedDisk, M)) (hvtrace : DiskWeakJordanTrace γLift v)
    (hvLip : ∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf (g.pullback p hp himm) (v z) (v w) ≤
        (L : ℝ≥0∞) * edist z w) :
    riemannianDiskArea (g.pullback p hp himm) uLift ≤
      riemannianDiskArea (g.pullback p hp himm) v :=
  hu.minimizesLipschitz_of_immersion_lift p hp himm uLift γLift hmap hloop hLift v hvtrace hvLip

-- `ImmersionPullback.lean:60`：immersion 后复合保持盘面积。
example
    (g : SmoothRiemannianMetric 𝓘(ℝ, F) N) (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x))
    {u : closedDisk → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf (g.pullback f hf himm) (u x) (u y) ≤
      (C : ℝ≥0∞) * edist x y) :
    riemannianDiskArea (g.pullback f hf himm) u = riemannianDiskArea g (f ∘ u) :=
  riemannianDiskArea_pullback_immersion g f hf himm hu

end DiskLift

section CoveringTopology

-- `WeaklyMonotone/CoveringLift.lean:42`：covering lift 沿 weakly monotone 相位下降，
-- 唯一性给出 `γLift` 与 `δ = γLift ∘ σ`。
example
    {B E : Type*} [TopologicalSpace B] [TopologicalSpace E]
    {σ : C(loopCircle, loopCircle)} (hσ : IsWeaklyMonotoneOnce σ)
    (p : E → B) (hp : IsCoveringMap p)
    (γ : C(loopCircle, B)) (δ : C(loopCircle, E))
    (hproj : ∀ θ, p (δ θ) = γ (σ θ)) :
    ∃ γLift : C(loopCircle, E), (∀ θ, p (γLift θ) = γ θ) ∧ δ = γLift.comp σ :=
  (hσ.existsUnique_covering_lift_of_comp p hp γ δ hproj).exists

-- `WeaklyMonotone/Fibers.lean:88/94`：相位满射且每个 fiber 连通。
example {σ : C(loopCircle, loopCircle)} (hσ : IsWeaklyMonotoneOnce σ) (θ : loopCircle) :
    Function.Surjective σ ∧ IsConnected (σ ⁻¹' {θ}) :=
  ⟨hσ.surjective, hσ.isConnected_fiber θ⟩

-- `FiniteOrderedFiber.lean:18`：有限 fiber 的路径连通 covering 上，连续实高度在某个
-- fiber 的两个不同点取同值（真正使用结论：取出碰撞对）。
example
    {T Y : Type*} [TopologicalSpace T] [PathConnectedSpace T]
    [TopologicalSpace Y] {p : T → Y} (hp : IsCoveringMap p)
    {y₀ : Y} {n : ℕ} (hcard : (p ⁻¹' {y₀}).encard = (n : ℕ∞))
    (hn : 1 < n) (h : T → ℝ) (hh : Continuous h) :
    ∃ x₁ x₂ : T, x₁ ≠ x₂ ∧ p x₁ = p x₂ ∧ h x₁ = h x₂ :=
  Covering.exists_fiber_collision_of_finite_fiber hp hcard hn h hh

-- `PuncturedBallConnected.lean:16`：中心唯一 fiber 附近的 covering 总空间路径连通。
example
    {F : ℂ → ℂ} {a : ℂ} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ)
    (hF : ContinuousOn F (Metric.closedBall a r))
    (hcenter : ∀ z ∈ Metric.closedBall a r, F z = F a ↔ z = a)
    (hcover : IsCoveringMap
      ((Metric.ball (F a) δ \ {F a}).restrictPreimage
        (fun z : Metric.closedBall a r => F z.val))) :
    PathConnectedSpace
      ((fun z : Metric.closedBall a r => F z.val) ⁻¹'
        (Metric.ball (F a) δ \ {F a})) :=
  Covering.pathConnectedSpace_preimage_puncturedBall_of_isCoveringMap hr hδ hF hcenter hcover

-- `PuncturedBallMonodromy.lean:19`：punctured ball 的连通有限 covering 有 cyclic monodromy，
-- 周期等于 fiber 基数。
example
    {T : Type*} [TopologicalSpace T] [PathConnectedSpace T]
    {c : ℂ} {δ : ℝ}
    {p : T → ↥(Metric.ball c δ \ {c})}
    (hp : IsCoveringMap p)
    (y : ↥(Metric.ball c δ \ {c})) {n : ℕ}
    (hcard : (p ⁻¹' {y}).encard = (n : ℕ∞)) :
    ∃ γ : FundamentalGroup ↥(Metric.ball c δ \ {c}) y,
      Function.Surjective (fun k : ℤ => γ ^ k) ∧
      (hp.monodromyPerm y γ).IsCycleOn Set.univ ∧
      ∀ (e : p ⁻¹' {y}) (k : ℤ),
        ((hp.monodromyPerm y γ) ^ k) e = e ↔ (n : ℤ) ∣ k :=
  Covering.exists_cyclic_monodromy_puncturedBall hp y hcard

end CoveringTopology

end
