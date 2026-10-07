import DifferentialGeometry.Topology.Maps.SheetTransitionR3B
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.CoincidentGermClosure
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TrimCollarMR1

/-!
# O-MY-R3B：闭盘上的 R3b 组装层（closedness 作为输入）+ Morrey 盘的 G3

把 G1（`Topology/Maps/SheetTransitionR3B.lean`）落到闭盘 `q : C(closedDisk, M)`：

* `exists_boundary_singleton_fiber_R3B`：MYD2 形状的边界单射 `hbdry` + 内部像不碰边界像 `hsep`
  ⇒ 边界点的 fiber 是单点（替代 MY-T Lemma 3 的 "degree one"）。
* `coincidentGermPairs_eq_empty_of_isClosed_R3B`：闭盘 `SmoothDiskExtension` + 闭盘 rank（⇒ 局部单射，
  `isLocallyInjective_MR1`）+ singleton fiber + coincident-germ 关系闭 ⇒ `coincidentGermPairs q = ∅`。
* `no_open_sheet_coincidence_of_coincidentGermPairs_eq_empty_R3B`：`coincidentGermPairs q = ∅` ⇒
  不存在不交非空开 `V₁ V₂ ⊆ D°`、`f` 在两边单射、`f '' V₁ = f '' V₂`（G1 的 Baire + invariance of
  domain 种子；只用紧 embedded patches）。
* **G3** `coincidentGermPairs_eq_empty_R3B`：Morrey 盘（树里
  `actual_morrey_coincident_germ_pairs_isClosed` 给闭性）的 coincident germ pairs 为空；
  `no_open_sheet_coincidence_morrey_R3B` 是其 R3b 形式。

无 minimality 的合同本体（G2）在 `NoSheetCoincidenceR3B.lean`，闭性来自去 minimizer 的 port 链。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 开盘内点处，`q` 在 `closedDisk` 上的 image germ 等于 `diskExtension q` 在 `ℂ` 上的 image germ。 -/
theorem map_nhds_closedDisk_eq_diskExtension_R3B {Y : Type*} (q : closedDisk → Y)
    (z : closedDisk) (hz : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1) :
    Filter.map q (𝓝 z) = Filter.map (diskExtension q) (𝓝 (z : ℂ)) := by
  have hrestriction : diskExtension q ∘ (Subtype.val : closedDisk → ℂ) = q :=
    funext (diskExtension_coe q)
  calc
    Filter.map q (𝓝 z) =
        Filter.map (diskExtension q ∘ (Subtype.val : closedDisk → ℂ)) (𝓝 z) := by
      rw [hrestriction]
    _ = Filter.map (diskExtension q) (𝓝 (z : ℂ)) := by
      rw [← Filter.map_map, map_nhds_subtype_val]
      rw [nhdsWithin_eq_nhds.2
        (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz)
          Metric.ball_subset_closedBall)]

/-- 闭盘上范数为 1 的点是某个 `diskBoundary θ`。 -/
theorem exists_diskBoundary_eq_of_not_mem_ball_R3B (x : closedDisk)
    (hx : ¬ ‖(x : ℂ)‖ < 1) : ∃ θ : loopCircle, diskBoundary θ = x := by
  have hnorm : ‖(x : ℂ)‖ = 1 := by
    have hle : ‖(x : ℂ)‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
    exact le_antisymm hle (le_of_not_gt hx)
  let c : Circle := ⟨(x : ℂ), mem_sphere_zero_iff_norm.mpr hnorm⟩
  obtain ⟨θ, hθ⟩ :=
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
  refine ⟨θ, Subtype.ext ?_⟩
  have hc := congrArg (fun w : Circle => (w : ℂ)) hθ
  simpa only [AddCircle.homeomorphCircle_apply] using! hc

/-- **边界 singleton fiber**（MYD2 形状）：边界单射 + 内部像不碰边界像 ⇒ 每个边界点的 fiber 单点。 -/
theorem exists_boundary_singleton_fiber_R3B {Y : Type*} (q : closedDisk → Y)
    (hbdry : ∀ θ θ' : loopCircle, q (diskBoundary θ) = q (diskBoundary θ') → θ = θ')
    (hsep : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ q (diskBoundary θ)) :
    ∃ x₀ : closedDisk, ∀ x : closedDisk, q x = q x₀ → x = x₀ := by
  refine ⟨diskBoundary 0, fun x hx => ?_⟩
  by_cases hlt : ‖(x : ℂ)‖ < 1
  · exact absurd hx (hsep x hlt 0)
  · obtain ⟨θ, rfl⟩ := exists_diskBoundary_eq_of_not_mem_ball_R3B x hlt
    rw [hbdry θ 0 hx]

/-- 闭盘组装：闭盘 smooth extension + 闭盘 rank + singleton fiber + 闭的 coincident-germ 关系 ⇒
`coincidentGermPairs q = ∅`（G1 的 continuation "全或无"）。 -/
theorem coincidentGermPairs_eq_empty_of_isClosed_R3B [T2Space M]
    {q : C(closedDisk, M)} {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hsingle : ∃ x₀ : closedDisk, ∀ x : closedDisk, q x = q x₀ → x = x₀)
    (hclosed : IsClosed {p : orderedCollisionPairs (q : closedDisk → M) |
      Filter.map q (𝓝 p.1.1) = Filter.map q (𝓝 p.1.2)}) :
    coincidentGermPairs (q : closedDisk → M) = ∅ :=
  coincidentGermPairs_eq_empty_of_singleton_R3B q.continuous (hQ.isLocallyInjective_MR1 hrank)
    hclosed hsingle

/-- `coincidentGermPairs q = ∅` ⇒ 没有开 sheet 重合：不存在不交非空开 `V₁ V₂ ⊆ D°`，`diskExtension q`
在两边单射且 `diskExtension q '' V₁ ⊆ diskExtension q '' V₂`（单向包含即可）。 -/
theorem no_open_sheet_inclusion_of_coincidentGermPairs_eq_empty_R3B [T2Space M]
    {q : C(closedDisk, M)} (hcgp : coincidentGermPairs (q : closedDisk → M) = ∅) :
    ¬ ∃ V₁ V₂ : Set ℂ, IsOpen V₁ ∧ IsOpen V₂ ∧ V₁.Nonempty ∧ Disjoint V₁ V₂ ∧
      V₁ ⊆ Metric.ball 0 1 ∧ V₂ ⊆ Metric.ball 0 1 ∧
      InjOn (diskExtension q) V₁ ∧ InjOn (diskExtension q) V₂ ∧
      diskExtension q '' V₁ ⊆ diskExtension q '' V₂ := by
  rintro ⟨V₁, V₂, hV₁, hV₂, hne, hdisj, hV₁D, hV₂D, hinj₁, hinj₂, himg⟩
  have hcont : Continuous (diskExtension q) :=
    q.continuous.comp diskRetraction_lipschitz.continuous
  obtain ⟨a, ha, b, hb, hab, hgerm⟩ :=
    exists_coincident_germ_of_image_subset_R3B hcont hV₁ hV₂ hne hinj₁ hinj₂ himg
  have haD : a ∈ Metric.ball (0 : ℂ) 1 := hV₁D ha
  have hbD : b ∈ Metric.ball (0 : ℂ) 1 := hV₂D hb
  let a' : closedDisk := ⟨a, Metric.ball_subset_closedBall haD⟩
  let b' : closedDisk := ⟨b, Metric.ball_subset_closedBall hbD⟩
  have hne' : a' ≠ b' := by
    intro h
    have hab' : a = b := congrArg Subtype.val h
    subst hab'
    exact Set.disjoint_left.mp hdisj ha hb
  have hval : q a' = q b' := by
    have h1 := diskExtension_coe q a'
    have h2 := diskExtension_coe q b'
    exact h1.symm.trans (hab.trans h2)
  have hmem : (a', b') ∈ coincidentGermPairs (q : closedDisk → M) :=
    ⟨hne', hval, (map_nhds_closedDisk_eq_diskExtension_R3B q a' haD).trans
      (hgerm.trans (map_nhds_closedDisk_eq_diskExtension_R3B q b' hbD).symm)⟩
  rw [hcgp] at hmem
  exact hmem

/-- R3b 形式（`f '' V₁ = f '' V₂`、两边非空）：由单向包含版直接得到。 -/
theorem no_open_sheet_coincidence_of_coincidentGermPairs_eq_empty_R3B [T2Space M]
    {q : C(closedDisk, M)} (hcgp : coincidentGermPairs (q : closedDisk → M) = ∅) :
    ¬ ∃ V₁ V₂ : Set ℂ, IsOpen V₁ ∧ IsOpen V₂ ∧ V₁.Nonempty ∧ V₂.Nonempty ∧ Disjoint V₁ V₂ ∧
      V₁ ⊆ Metric.ball 0 1 ∧ V₂ ⊆ Metric.ball 0 1 ∧
      InjOn (diskExtension q) V₁ ∧ InjOn (diskExtension q) V₂ ∧
      diskExtension q '' V₁ = diskExtension q '' V₂ := by
  rintro ⟨V₁, V₂, hV₁, hV₂, hne, -, hdisj, hV₁D, hV₂D, hinj₁, hinj₂, himg⟩
  exact no_open_sheet_inclusion_of_coincidentGermPairs_eq_empty_R3B hcgp
    ⟨V₁, V₂, hV₁, hV₂, hne, hdisj, hV₁D, hV₂D, hinj₁, hinj₂, himg.subset⟩

/-- **G3 Morrey 盘的 coincident germ pairs 为空。** 前提同树里
`actual_morrey_coincident_germ_pairs_isClosed`（闭性）；singleton fiber 来自
`SmoothDiskExtension.boundary_fiber_eq`（weak trace + smooth embedded `γ` + 边界 rank +
`hseparate`）。 -/
theorem coincidentGermPairs_eq_empty_R3B [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk g γ q) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hd3 : Module.finrank ℝ E = 3)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
      ∀ θ : loopCircle, q z ≠ γ θ) :
    coincidentGermPairs (q : closedDisk → M) = ∅ := by
  obtain ⟨σ, hσ, htrace⟩ := hq.trace
  have hboundary := hQ.boundary_fiber_eq hγ hσ htrace
    (fun z hz => hrank z (Metric.sphere_subset_closedBall hz)) hseparate
  exact coincidentGermPairs_eq_empty_of_isClosed_R3B hQ hrank
    ⟨diskBoundary 0, hboundary 0⟩
    (IMS03Embeddedness.actual_morrey_coincident_germ_pairs_isClosed hq hγ hd3 hQ hrank hseparate)

/-- G3 的 R3b 形式：Morrey 盘（闭盘 smooth + rank + `hseparate`）没有开 sheet 重合。 -/
theorem no_open_sheet_coincidence_morrey_R3B [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk g γ q) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hd3 : Module.finrank ℝ E = 3)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
      ∀ θ : loopCircle, q z ≠ γ θ) :
    ¬ ∃ V₁ V₂ : Set ℂ, IsOpen V₁ ∧ IsOpen V₂ ∧ V₁.Nonempty ∧ V₂.Nonempty ∧ Disjoint V₁ V₂ ∧
      V₁ ⊆ Metric.ball 0 1 ∧ V₂ ⊆ Metric.ball 0 1 ∧
      InjOn (diskExtension q) V₁ ∧ InjOn (diskExtension q) V₂ ∧
      diskExtension q '' V₁ = diskExtension q '' V₂ :=
  no_open_sheet_coincidence_of_coincidentGermPairs_eq_empty_R3B
    (coincidentGermPairs_eq_empty_R3B hq hγ hd3 hQ hrank hseparate)

end DifferentialGeometry.Geometry
