import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeWindowC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapCoordinates
import DifferentialGeometry.Topology.Manifold.ImmersionInterior

set_option autoImplicit false

/-!
# CE ⇐ HasRadialCoordinates（O-CH11-NATIVE-WINDOW G3，后缀 `_C11SP`）

G1c `native_trace_window_of_CC_CE_C11SP` 的 BLOCKED binder `hCE`（core exclusion）在 history 层的来源：
若 static cap 的 witness 有径向坐标（`StaticCapWitness.HasRadialCoordinates`，StaticCapCoordinates:20），
则 regular-crossing 像不落在 `window '' {‖z‖ ≤ TE}`。
证明：`‖z‖ ≤ TE = standardCapL` ⇒ `z ∈ standardCapClosedCore`，径向坐标第一条给 `window z = capChart z ∈
range cap`；`cap_eq` / `oldOutput_eq` + presentation 单射 ⇒ `capping.cap b k = coreInclusion w`；
`core_cap_intersection` ⇒ `w` 是 core 边界球点 `tube (y, ±1)`；`w` 在 `old` 中是 interior 点 ⇒
`old ↪ P` 在 `w` 处局部微分同胚（`isLocalDiffeomorphAt_of_isInteriorPoint_of_isImmersion`）⇒ `old` 的像
含 `tube (y, ±1)` 的 P-邻域；但 `tube (y, s)`（`|s| < 1`）属于 removed band、不在 core，矛盾。
**PROVED**。缺口只剩 producer 侧：records 合取不带 `HasRadialCoordinates`（见 state / G1 块）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- 局部微分同胚点处像含邻域。 -/
theorem range_mem_nhds_of_isLocalDiffeomorphAt_C11SP
    {E F H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    {f : M → N} {x : M} (h : IsLocalDiffeomorphAt I J ∞ f x) :
    Set.range f ∈ 𝓝 (f x) := by
  obtain ⟨Φ, hx, heq⟩ := h
  have hT : Φ.target ∈ 𝓝 (f x) := by
    rw [heq hx]
    exact Φ.open_target.mem_nhds (Φ.map_source hx)
  filter_upwards [hT] with y hy
  exact ⟨Φ.symm y, (heq (Φ.map_target hy)).trans (Φ.right_inv hy)⟩

/-- tube 边界球点的每个邻域都含 removed band 点。 -/
theorem exists_removedBand_near_boundarySphere_C11SP {M : Type*} [TopologicalSpace M]
    (T : TubeSystem M) (b : T.Boundary) (y : Sphere 2) {U : Set M}
    (hU : U ∈ 𝓝 (T.boundarySphere b y)) : ∃ p ∈ U, p ∉ T.core := by
  let lvl : ℝ := (TubeSystem.boundaryLevel b.2 : ℝ)
  have hlvl : lvl = 1 ∨ lvl = -1 := by
    rcases b with ⟨a, side⟩
    cases side
    · right; rfl
    · left; rfl
  let φ : ℝ → Icc (-2 : ℝ) 2 := fun s =>
    ⟨max (-2) (min 2 ((1 - s) * lvl)), le_max_left _ _,
      max_le (by norm_num) (min_le_left _ _)⟩
  have hφc : Continuous φ := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_const.max (continuous_const.min
      ((continuous_const.sub continuous_id).mul continuous_const))
  have hφ0 : φ 0 = TubeSystem.boundaryLevel b.2 := by
    apply Subtype.ext
    change max (-2) (min 2 ((1 - 0) * lvl)) = lvl
    rcases hlvl with h | h <;> rw [h] <;> norm_num
  let g : ℝ → M := fun s => T.tube b.1 (y, φ s)
  have hgc : Continuous g := (T.tube b.1).continuous.comp (continuous_const.prodMk hφc)
  have hg0 : g 0 = T.boundarySphere b y := by
    change T.tube b.1 (y, φ 0) = T.tube b.1 (y, TubeSystem.boundaryLevel b.2)
    rw [hφ0]
  have hpre : g ⁻¹' U ∈ 𝓝 (0 : ℝ) := hgc.continuousAt.preimage_mem_nhds (hg0 ▸ hU)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let s : ℝ := min (δ / 2) (1 / 2)
  have hs0 : 0 < s := lt_min (half_pos hδ) (by norm_num)
  have hs1 : s ≤ 1 / 2 := min_le_right _ _
  have hsδ : s < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hsU : g s ∈ U := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs0]
    exact hsδ)
  refine ⟨g s, hsU, ?_⟩
  intro hcore
  apply hcore
  have hval : (φ s : ℝ) = (1 - s) * lvl := by
    change max (-2) (min 2 ((1 - s) * lvl)) = (1 - s) * lvl
    rcases hlvl with h | h <;> rw [h]
    · rw [min_eq_right (by linarith only [hs0]), max_eq_right (by linarith only [hs1])]
    · rw [min_eq_right (by linarith only [hs1]), max_eq_right (by linarith only [hs0])]
  refine Set.mem_iUnion.mpr ⟨b.1, ⟨(y, φ s), ?_, rfl⟩⟩
  change (-1 : ℝ) < (φ s : ℝ) ∧ (φ s : ℝ) < 1
  rw [hval]
  rcases hlvl with h | h <;> rw [h] <;> constructor <;> linarith only [hs0, hs1]

/-- **G3（PROVED）CE ⇐ 径向坐标**：regular-crossing 像不落在 `window '' {‖z‖ ≤ TE}`。 -/
theorem window_ne_of_regularCrossing_of_radial_C11SP
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    {fixed : StaticCapScaffold} {D η : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m η b) (hrad : S.witness.HasRadialCoordinates)
    (z : standardCapWindow D) (hz : ‖z.val‖ ≤ StandardCap.transitionEnd)
    {pm : P.Carrier} {pp : Q.Carrier} (hcross : E.RegularCrossing pm pp) :
    S.window z ≠ pp := by
  intro hzpp
  let _ := E.oldCharts
  let _ := E.oldSmooth
  obtain ⟨w, hw, -, hwq⟩ := hcross
  have hc : z.val ∈ standardCapClosedCore := by
    rw [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right,
      standardCapL_eq_transitionEnd]
    exact hz
  have h1 : S.witness.window z = S.witness.capChart ⟨z.val, hc⟩ := hrad.1 z.val z.2 hc
  obtain ⟨k, hk⟩ : S.witness.capChart ⟨z.val, hc⟩ ∈ Set.range S.witness.cap := by
    rw [← S.witness.capChart_range]
    exact Set.mem_range_self _
  have h2 : E.transition.trace.presentation (E.transition.trace.capping.cap b.1 k) =
      E.transition.trace.presentation (E.transition.trace.capping.coreInclusion w.1) := by
    rw [S.cap_eq k, E.oldOutput_eq w, hk, ← h1]
    congr 1
    exact hzpp.trans hwq.symm
  have h3 := E.transition.trace.presentation.injective h2
  have hmem : E.transition.trace.capping.coreInclusion w.1 ∈
      Set.range E.transition.trace.capping.coreInclusion ∩
        Set.range (E.transition.trace.capping.cap b.1) := ⟨⟨_, rfl⟩, ⟨k, h3⟩⟩
  rw [E.transition.trace.capping.core_cap_intersection b.1] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hwy : E.transition.trace.tubes.coreBoundarySphere b.1 y = w.1 :=
    E.transition.trace.capping.coreEmbedding.injective hy
  have hloc :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_isInteriorPoint_of_isImmersion
      E.old_induced.isImmersion hw rfl
  have hnhds := range_mem_nhds_of_isLocalDiffeomorphAt_C11SP hloc
  have hpt : (w.1.1 : P.Carrier) = E.transition.trace.tubes.boundarySphere b.1 y := by
    rw [← hwy]
    rfl
  rw [hpt] at hnhds
  obtain ⟨p, ⟨x, rfl⟩, hpcore⟩ :=
    exists_removedBand_near_boundarySphere_C11SP E.transition.trace.tubes b.1 y hnhds
  exact hpcore x.1.2

/-- consumer（history 层）：records 径向 ⇒ G1b `exists_pair_firstExit_native_C11SP` /
`crossing_class_of_good_suffix_C11SP` 的 `hCE` 前提。 -/
example {H : ObservedHistory.{u}} {params : CutoffParameters}
    (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params)
    (hrad : ∀ e b, ((records e).static b).witness.HasRadialCoordinates) :
    ∀ (e : Fin H.eventCount) (pm : (H.stage e.castSucc).Carrier)
      (pp : (H.stage e.succ).Carrier), (H.event e).RegularCrossing pm pp →
      ∀ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
        ‖z.val‖ ≤ StandardCap.transitionEnd → ((records e).static b).window z ≠ pp :=
  fun e _ _ hcross b z hz =>
    window_ne_of_regularCrossing_of_radial_C11SP (H.event e) ((records e).static b) (hrad e b) z hz
      hcross

/-- consumer（tower 层）：G1c 的 `hCE` binder ⇐ records 径向坐标（tower 形，同一量词前缀）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hradT : ∀ {pBase : CutoffParameters} {Γf : GC.GeneralFlow.ClosedBirthConstants}
        (S : GC.GeneralFlow.PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        ∀ n e b, ((records n e).static b).witness.HasRadialCoordinates) :
    ∀ {pBase : CutoffParameters} {Γf : GC.GeneralFlow.ClosedBirthConstants}
        (S : GC.GeneralFlow.PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        ∀ (n : ℕ) (e : Fin (F.tower.history n).eventCount)
          (pm : ((F.tower.history n).toHistory.stage e.castSucc).Carrier)
          (pp : ((F.tower.history n).toHistory.stage e.succ).Carrier),
          ((F.tower.history n).toHistory.event e).RegularCrossing pm pp →
          ∀ (b : ((F.tower.history n).toHistory.event e).RetainedBoundaryIndex)
            (z : standardCapWindow params.modelRadius),
            ‖z.val‖ ≤ StandardCap.transitionEnd → ((records n e).static b).window z ≠ pp :=
  fun S F hT params records hcan n e _ _ hcross b z hz =>
    window_ne_of_regularCrossing_of_radial_C11SP _ ((records n e).static b)
      (hradT S F hT params records hcan n e b) z hz hcross

end GC.LongTime.Ch11
