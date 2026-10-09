import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.BoundaryCollar
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundaryTraceInjectivity
import DifferentialGeometry.Topology.Maps.CollisionPairs
import DifferentialGeometry.Topology.Maps.FiniteFiberNeighborhoods

/-!
# S-MY-R1：外审 Lemma R1（`trim_with_singleton_collar_and_compact_collision_relation`）

对一般 Morrey disk `q : C(closedDisk, M)`（`IsMorreyDisk g γ q`）+ `SmoothDiskExtension q Q`
+ 闭盘 rank（`Q` 在整个 `closedBall 0 1` 上 `mfderiv` 单射）；**不用 analytic**。

* G1 `SmoothDiskExtension.exists_singleton_collar_MR1`：`∃ ρ₀ ∈ (0,1)`，`‖z‖ > ρ₀` 的 `z`
  fiber 为 singleton（W8 `exists_singleton_regular_collar` 的 adapter，取 `max r₀ (1/2)` 使 `ρ₀ > 0`）。
* G2 `trimmed_disk_MR1`：`ρ₀ < r < 1` 时 `q_r = affineSubdisk q 0 r` 的 trace 是
  smooth embedded loop（`exists_regular_concentric_restrictions` adapter），且
  `q_r '' {‖z‖ < 1} ∩ q_r '' {‖z‖ = 1} = ∅`（由 G1 collar 直接推出）。
* G3 `SmoothDiskExtension.collision_separation_MR1`：`∃ ε > 0`，同 fiber 的不同点 `x ≠ y` 相距
  `≥ ε`（"collision sources 两两相距 ≥ ε" 的含义：**互相碰撞**的两个源点；不是说 collision 集是
  离散的）。证明用 compact collision relation `isCompact_orderedCollisionPairs`。
* G4 `SmoothDiskExtension.fiber_card_le_MR1`：`∃ m, ∀ p, (q ⁻¹' {p}).Finite ∧ ncard ≤ m`
  （G3 的 ε 分离 + `closedDisk` 全有界 ⇒ `ε/2` 有限覆盖，每个 ball 至多一点）。
* `lemma_R1_MR1`：四条合在一起的 Lemma R1 版本，从 `hseparate`（内部不碰边界曲线）
  推出 MY-1 的 boundary singleton 前提。

注意：只给 compact collision relation + 一致有限重数，**不**声称 collision 集是有限图、
不声称源/像的 collision 投影可同时三角剖分。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

/-! ## Part A：抽象拓扑（紧致 metric 源 + 局部单射 ⇒ ε 分离 + 一致 fiber 基数界） -/

section Abstract

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
  {f : X → Y}

/-- 连续局部单射 `f` 的 collision pairs 是紧集（W8 `isCompact_orderedCollisionPairs`），
`dist` 在其上取到最小值；该最小值给统一分离 `ε > 0`。 -/
theorem exists_collision_separation_MR1 (hf : Continuous f) (hloc : IsLocallyInjective f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x y : X, x ≠ y → f x = f y → ε ≤ dist x y := by
  have hK := isCompact_orderedCollisionPairs f hf hloc
  rcases (orderedCollisionPairs f).eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, fun x y hxy hfxy => ?_⟩
    have hmem : (x, y) ∈ orderedCollisionPairs f := ⟨hxy, hfxy⟩
    rw [h] at hmem
    exact absurd hmem (Set.notMem_empty _)
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn h
      (continuous_fst.dist continuous_snd).continuousOn
    refine ⟨dist z.1 z.2, dist_pos.mpr hz.1, fun x y hxy hfxy => ?_⟩
    exact hmin (show (x, y) ∈ orderedCollisionPairs f from ⟨hxy, hfxy⟩)

/-- 连续局部单射 `f` 在紧致 metric 源上：每个 fiber 有限，且基数有一致上界 `m`。 -/
theorem exists_fiber_card_le_MR1 (hf : Continuous f) (hloc : IsLocallyInjective f) :
    ∃ m : ℕ, ∀ p : Y, (f ⁻¹' {p}).Finite ∧ (f ⁻¹' {p}).ncard ≤ m := by
  obtain ⟨ε, hε, hsep⟩ := exists_collision_separation_MR1 hf hloc
  obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.mp
    (isCompact_univ (X := X)).totallyBounded (ε / 2) (half_pos hε)
  have hc : ∀ x : X, ∃ y, y ∈ t ∧ dist x y < ε / 2 := fun x => by
    simpa only [Set.mem_iUnion, Metric.mem_ball, exists_prop] using hcov (Set.mem_univ x)
  choose c hct hcd using hc
  refine ⟨t.ncard, fun p => ⟨finite_fiber_of_isLocallyInjective hf hloc p, ?_⟩⟩
  refine Set.ncard_le_ncard_of_injOn c (fun x _ => hct x) ?_ ht
  intro x hx x' hx' hcx
  by_contra hne
  have h1 := hsep x x' hne ((show f x = p from hx).trans (show f x' = p from hx').symm)
  have h2 : dist x x' < ε :=
    calc dist x x' ≤ dist x (c x) + dist (c x) x' := dist_triangle _ _ _
      _ = dist x (c x) + dist x' (c x') := by rw [hcx, dist_comm (c x') x']
      _ < ε / 2 + ε / 2 := add_lt_add (hcd x) (hcd x')
      _ = ε := add_halves ε
  exact absurd h2 (not_lt.mpr h1)

end Abstract

/-! ## Part B：闭盘 rank ⇒ `q` 局部单射 -/

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

-- 逐字拷自 `Embeddedness/BoundaryCollar.lean`（W8 里是 `private`，不能直接调用），仅改名。
private theorem exists_injective_regular_neighborhood_MR1
    {Q : ℂ → M} {N : Set ℂ} (hN : IsOpen N)
    (hQ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Q N)
    {a : ℂ} (ha : a ∈ N)
    (hrank : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q a)) :
    ∃ V : Set ℂ, IsOpen V ∧ a ∈ V ∧ V ⊆ N ∧
      Set.InjOn Q V ∧ ∀ z ∈ V, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) := by
  let S : TopologicalSpace.Opens ℂ := ⟨N, hN⟩
  let F : S → M := fun z => Q z
  let aS : S := ⟨a, ha⟩
  have hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F :=
    hQ.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  have hDF : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F aS) := by
    change Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z : S => Q z) aS : ℂ →L[ℝ] E)
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact hrank
  have hImm := DifferentialGeometry.Topology.Manifold.isImmersionAt_of_injective_mfderiv
    (by simp : (∞ : ℕ∞ω) ≠ 0) hF aS hDF
  have hnormal (z : S) (hz : z ∈ hImm.domChart.source) :
      (hImm.codChart.extend 𝓘(ℝ, E)) (F z) =
        hImm.equiv ((hImm.domChart.extend 𝓘(ℝ, ℂ)) z, 0) := by
    have hz' : z ∈ (hImm.domChart.extend 𝓘(ℝ, ℂ)).source := by
      rwa [OpenPartialHomeomorph.extend_source]
    have hh := hImm.writtenInCharts ((hImm.domChart.extend 𝓘(ℝ, ℂ)).map_source hz')
    simpa only [Function.comp_apply,
      (hImm.domChart.extend 𝓘(ℝ, ℂ)).left_inv hz'] using hh
  have hinj : Set.InjOn F hImm.domChart.source := by
    intro z hz w hw hzw
    have hh := (hnormal z hz).symm.trans
      ((congrArg (hImm.codChart.extend 𝓘(ℝ, E)) hzw).trans (hnormal w hw))
    apply (hImm.domChart.extend 𝓘(ℝ, ℂ)).injOn
    · rwa [OpenPartialHomeomorph.extend_source]
    · rwa [OpenPartialHomeomorph.extend_source]
    · exact congrArg Prod.fst (hImm.equiv.injective hh)
  let T : Set S := hImm.domChart.source ∩ {z | IsImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F z}
  have hT : IsOpen T := hImm.domChart.open_source.inter IsOpen.isImmersionAt
  let V : Set ℂ := Subtype.val '' T
  have hV : IsOpen V := hN.isOpenMap_subtype_val T hT
  refine ⟨V, hV, ⟨aS, ⟨hImm.mem_domChart_source, hImm⟩, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact z.property
  · rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ hzw
    exact congrArg (fun t : S => (t : ℂ)) (hinj hz.1 hw.1 hzw)
  · rintro _ ⟨z, hz, rfl⟩
    have hd := hz.2.mfderiv_injective (by simp : (∞ : ℕ∞ω) ≠ 0)
    change Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z : S => Q z) z : ℂ →L[ℝ] E) at hd
    rw [DifferentialGeometry.mfderiv_restrict_open] at hd
    exact hd

/-- 闭盘 rank（`Q` 在 `closedBall 0 1` 的每一点 `mfderiv` 单射）⇒ `q` 是局部单射：每个
`x : closedDisk` 有开邻域使 `q` 在其上单射。不对盘内 collision 作任何断言。 -/
theorem SmoothDiskExtension.isLocallyInjective_MR1 {q : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) :
    IsLocallyInjective q := by
  intro x
  obtain ⟨N, hN, hDN, hQN⟩ := hQ.2
  obtain ⟨V, hV, hxV, -, hQV, -⟩ :=
    exists_injective_regular_neighborhood_MR1 hN hQN (hDN x.property) (hrank x x.property)
  refine ⟨(Subtype.val : closedDisk → ℂ) ⁻¹' V, hV.preimage continuous_subtype_val, hxV, ?_⟩
  intro z hz w hw hzw
  apply Subtype.ext
  apply hQV hz hw
  exact (hQ.1 z).trans (hzw.trans (hQ.1 w).symm)

/-- G3 的紧性部分：**compact collision relation**（只是紧集，不是图/不是有限）。 -/
theorem SmoothDiskExtension.isCompact_collision_relation_MR1 [T2Space M]
    {q : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) :
    IsCompact (orderedCollisionPairs q) :=
  isCompact_orderedCollisionPairs q q.continuous (hQ.isLocallyInjective_MR1 hrank)

/-! ## G1：singleton collar -/

/-- **G1**（MR1）：boundary singleton fibers（MY-1 前提）+ 闭盘 rank ⇒ 存在 `ρ₀ ∈ (0,1)`，
`‖z‖ > ρ₀` 的点的 fiber 是 singleton：`‖z‖ > ρ₀ → q z = q w → z = w`。W8
`exists_singleton_regular_collar` 的 adapter。 -/
theorem SmoothDiskExtension.exists_singleton_collar_MR1 [T2Space M]
    {q : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    (hsingle : ∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → ∀ w, q w = q z → w = z)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧
      ∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w := by
  obtain ⟨r₀, -, hr₀1, hcollar⟩ := hQ.exists_singleton_regular_collar hsingle
    (fun z hz => hrank z (Metric.sphere_subset_closedBall hz))
  refine ⟨max r₀ (1 / 2), lt_max_of_lt_right one_half_pos,
    max_lt hr₀1 one_half_lt_one, fun z w hz hzw => ?_⟩
  exact ((hcollar z ((le_max_left _ _).trans_lt hz)).1 w hzw.symm).symm

/-- MY-1 的 boundary singleton 前提由「内部不碰边界曲线」+ boundary rank + weak Jordan trace
推出（W8 `boundary_fiber_eq` 的改写，思路同 IMS03 `Restriction/Collar`，但不依赖它）。 -/
theorem SmoothDiskExtension.boundary_singleton_MR1
    {γ : freeLoop M} {q : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) (htr : DiskWeakJordanTrace γ q)
    (hrank : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ γ θ) :
    ∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → ∀ w, q w = q z → w = z := by
  obtain ⟨σ, hσ, htrace⟩ := htr
  have hboundary := hQ.boundary_fiber_eq hγ hσ htrace hrank hseparate
  intro z hz w hw
  let c : Circle := ⟨(z : ℂ), mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
  have hb : diskBoundary θ = z := by
    apply Subtype.ext
    have hc := congrArg (fun v : Circle => (v : ℂ)) hθ
    simpa only [AddCircle.homeomorphCircle_apply] using! hc
  exact (hboundary θ w (hw.trans (congrArg q hb).symm)).trans hb

/-! ## G2：trimmed disk -/

/-- `z ↦ r • z`，`closedDisk → closedDisk`（`0 ≤ r ≤ 1`）；`q_r z = q (scaleDisk r z)`。 -/
def scaleDisk_MR1 (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (z : closedDisk) : closedDisk :=
  ⟨r • (z : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    have hz : ‖(z : ℂ)‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
    exact (mul_le_of_le_one_right hr0 hz).trans hr1⟩

/-- `affineSubdisk q 0 r` 就是 `z ↦ q (r • z)`。 -/
theorem affineSubdisk_zero_eq_MR1 {q : C(closedDisk, M)} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (z : closedDisk) : affineSubdisk q 0 r z = q (scaleDisk_MR1 r hr0 hr1 z) := by
  change diskExtension q (0 + r • (z : ℂ)) = _
  rw [zero_add]
  exact diskExtension_coe q (scaleDisk_MR1 r hr0 hr1 z)

/-- **G2**（MR1）：`q_r := affineSubdisk q 0 r`（`= fun z => q (r • z)`），`ρ₀ < r < 1`：
(a) `diskTrace q_r` 是 smooth embedded loop，且 `q_r` 仍是同一 metric 下的 Morrey disk，
trimmed boundary 的 fiber 是 singleton（`q w = trace θ → w = r • ∂θ`）；
(b) 内部像与边界像不交：`q_r '' {‖z‖ < 1} ∩ q_r '' {‖z‖ = 1} = ∅`。
`ρ₀` 同时满足 G1 的 collar。 -/
theorem trimmed_disk_MR1 [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hsingle : ∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → ∀ w, q w = q z → w = z)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧
      (∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w) ∧
      ∀ r : ℝ, ρ₀ < r → r < 1 →
        IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk q 0 r)) ∧
        IsMorreyDisk g (diskTrace (affineSubdisk q 0 r)) (affineSubdisk q 0 r) ∧
        (∀ (θ : loopCircle) (w : closedDisk),
          q w = diskTrace (affineSubdisk q 0 r) θ → (w : ℂ) = r • (diskBoundary θ : ℂ)) ∧
        Disjoint (affineSubdisk q 0 r '' {z : closedDisk | ‖(z : ℂ)‖ < 1})
          (affineSubdisk q 0 r '' {z : closedDisk | ‖(z : ℂ)‖ = 1}) := by
  obtain ⟨r₀, hr₀, hr₀1, -, hrestr⟩ := hq.exists_regular_concentric_restrictions hQ hsingle
    (fun z hz => hrank z (Metric.sphere_subset_closedBall hz))
  obtain ⟨ρ₀, hρ₀, hρ₀1, hcol⟩ := hQ.exists_singleton_collar_MR1 hsingle hrank
  have hge : r₀ ≤ max r₀ ρ₀ := le_max_left _ _
  refine ⟨max r₀ ρ₀, lt_max_of_lt_right hρ₀, max_lt hr₀1 hρ₀1,
    fun z w hz hzw => hcol z w ((le_max_right _ _).trans_lt hz) hzw, ?_⟩
  intro r hr hr1
  obtain ⟨hloop, hmorrey, hfiber⟩ := hrestr r (hge.trans_lt hr) hr1
  refine ⟨hloop, hmorrey, hfiber, ?_⟩
  have hρr : ρ₀ < r := (le_max_right _ _).trans_lt hr
  have hr0 : 0 < r := hρ₀.trans hρr
  rw [Set.disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
  rw [affineSubdisk_zero_eq_MR1 hr0.le hr1.le, affineSubdisk_zero_eq_MR1 hr0.le hr1.le] at hwz
  have hnorm : ‖((scaleDisk_MR1 r hr0.le hr1.le w : closedDisk) : ℂ)‖ = r := by
    change ‖r • (w : ℂ)‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, show ‖(w : ℂ)‖ = 1 from hw, mul_one]
  have hsc := hcol _ _ (by rw [hnorm]; exact hρr) hwz
  have hwz' : (w : ℂ) = (z : ℂ) := by
    have h1 := congrArg (fun v : closedDisk => r⁻¹ • (v : ℂ)) hsc
    simpa only [scaleDisk_MR1, inv_smul_smul₀ hr0.ne'] using h1
  have hlt : ‖(z : ℂ)‖ < 1 := hz
  rw [← hwz', show ‖(w : ℂ)‖ = 1 from hw] at hlt
  exact lt_irrefl _ hlt

/-! ## G3 / G4：collision 的统一 ε 分离与一致 fiber 基数界 -/

/-- **G3**（MR1）：闭盘 rank ⇒ `∃ ε > 0`，互相碰撞的不同源点 `x ≠ y`（`q x = q y`）
相距 `≥ ε`。不假设 / 不推出 collision 集离散或有限。 -/
theorem SmoothDiskExtension.collision_separation_MR1 [T2Space M]
    {q : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x y : closedDisk, x ≠ y → q x = q y → ε ≤ dist (x : ℂ) (y : ℂ) :=
  exists_collision_separation_MR1 q.continuous (hQ.isLocallyInjective_MR1 hrank)

/-- **G4**（MR1）：闭盘 rank ⇒ 每个 fiber `q ⁻¹' {p}` 有限且基数 `≤ m`（`m` 与 `p` 无关）。 -/
theorem SmoothDiskExtension.fiber_card_le_MR1 [T2Space M]
    {q : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) :
    ∃ m : ℕ, ∀ p : M, (q ⁻¹' {p}).Finite ∧ (q ⁻¹' {p}).ncard ≤ m :=
  exists_fiber_card_le_MR1 q.continuous (hQ.isLocallyInjective_MR1 hrank)

/-! ## Lemma R1（G1–G4 合并版） -/

/-- **外审 Lemma R1**：对 Morrey disk `q`（smooth embedded boundary loop `γ`，内部不碰 `γ`），
smooth extension `Q` 与闭盘 rank：存在 `ρ₀ ∈ (0,1)`、`ε > 0`、`m`，使 G1–G4 全部成立。
只产生 compact collision relation（`isCompact_collision_relation_MR1`）与有限重数，
**不**是有限图。 -/
theorem lemma_R1_MR1 [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ γ θ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧
      (∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w) ∧
      (∀ r : ℝ, ρ₀ < r → r < 1 →
        IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk q 0 r)) ∧
        IsMorreyDisk g (diskTrace (affineSubdisk q 0 r)) (affineSubdisk q 0 r) ∧
        Disjoint (affineSubdisk q 0 r '' {z : closedDisk | ‖(z : ℂ)‖ < 1})
          (affineSubdisk q 0 r '' {z : closedDisk | ‖(z : ℂ)‖ = 1})) ∧
      (∃ ε : ℝ, 0 < ε ∧
        ∀ x y : closedDisk, x ≠ y → q x = q y → ε ≤ dist (x : ℂ) (y : ℂ)) ∧
      ∃ m : ℕ, ∀ p : M, (q ⁻¹' {p}).Finite ∧ (q ⁻¹' {p}).ncard ≤ m := by
  have hsingle := hQ.boundary_singleton_MR1 hγ hq.trace
    (fun z hz => hrank z (Metric.sphere_subset_closedBall hz)) hseparate
  obtain ⟨ρ₀, hρ₀, hρ₀1, hcol, htrim⟩ := trimmed_disk_MR1 hq hQ hsingle hrank
  refine ⟨ρ₀, hρ₀, hρ₀1, hcol, fun r hr hr1 => ?_, hQ.collision_separation_MR1 hrank,
    hQ.fiber_card_le_MR1 hrank⟩
  obtain ⟨h1, h2, -, h4⟩ := htrim r hr hr1
  exact ⟨h1, h2, h4⟩

end DifferentialGeometry.Geometry
