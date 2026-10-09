import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceCone3_P6L

/-!
# L6-B：`BoundedCurvatureAtDistanceCone:603` 的局部化（`_P6L`）

局部化合同 §2 (W) + rev1a C2.2：原
`RetainedCoreHistory.final_slab_scalar_buffer_of_spatialCanonicalWitness`
（`ST/BoundedCurvatureAtDistanceCone.lean:603`）的 `hW`（carrier 全局）只在中心 `(y m).val` 求值
（原 l.658），z 处的标量控制全经 witness 自身的球。中心不在基点固定球内被证明，故在使用点补
成员关系：`hW` 限于 `U m`，新增 `hyU : ∀ᶠ m in atTop, (y m).val ∈ U m`（极限层 Cone:686 由收敛
几何供给，rev1a C2.3）。私有 `isCompact_riemannianClosedBallOf_endpoint`（`:53`）复制。证明体照抄。
-/

set_option autoImplicit false


noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u v

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance pointedLimitRegular (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

/-- `_P6L` 私有副本：原 private `isCompact_riemannianClosedBallOf_endpoint`（Cone:53），逐字。 -/
private theorem isCompact_riemannianClosedBallOf_endpoint_P6L {P : OrientedThreeStage.{u}} {a b : ℝ}
    (A : P.ClosedSlab a b)
    (g : SmoothRiemannianMetric ThreeModel
      (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen)
    (p : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) (r : ℝ) :
    IsCompact (riemannianClosedBallOf g p r) := by
  have hU : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion = univ :=
    A.terminalRegularRegion_eq_univ P
  have : CompactSpace (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen :=
    isCompact_iff_compactSpace.mp (by
      change IsCompact (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
      rw [hU]
      exact isCompact_univ)
  exact (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist g p)
    continuous_const).isCompact

/-- **`_P6L`**：原 `RetainedCoreHistory.final_slab_scalar_buffer_of_spatialCanonicalWitness`
（Cone:603）。改动：`hW` 限于 `U m`；加中心成员前提 `hyU : ∀ᶠ m in atTop, (y m).val ∈ U m`。
结论逐字。 -/
theorem RetainedCoreHistory.final_slab_scalar_buffer_of_spatialCanonicalWitness_P6L
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ m, ((H m).stage (Fin.last (H m).eventCount)).ClosedSlab
      ((H m).time (Fin.last (H m).eventCount)) (time m))
    (Ctime : ℝ≥0) (q : ℕ → ℝ)
    (y : ∀ m, ((A m).restrictIncoming le_rfl (A m).lt le_rfl).terminalRegularOpen)
    (Q₂ : ℕ → ℝ) (hQ₂ : ∀ m, 1 ≤ Q₂ m)
    (hQ₂y : ∀ m, Q₂ m = (A m).flow.scalar (time m) (y m).val)
    {eps C1 C2 : ℝ} (hC2 : 1 ≤ C2)
    (U : ∀ m, Set ((H m).stage (Fin.last (H m).eventCount)).Carrier)
    (hW : ∀ m, ∀ z ∈ U m, q m < (A m).flow.scalar (time m) z →
      ∃ W : SpatialCanonicalWitness ((A m).flow.base.metric (time m)) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hqy : ∀ᶠ m in atTop, q m < (A m).flow.scalar (time m) (y m).val)
    (hyU : ∀ᶠ m in atTop, (y m).val ∈ U m)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hwindow : ∀ m, (H m).time (Fin.last (H m).eventCount) ≤ time m - θ₀ / Q₂ m) :
    ∀ R : ℝ, 0 < R → R < 1 → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < 1 ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧
      ∀ᶠ m in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m))
            ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric)
          (y m) (R + r)) ∧
        (∀ z ∈ riemannianClosedBallOf
          (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m))
            ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric)
          (y m) (R + r),
          metricScalarAt
            ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric z ≤
            2 * (Amax * Q₂ m)) ∧
        ∃ first : Fin ((H m).eventCount + 1),
          (∀ z ∈ riemannianClosedBallOf
            (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m))
              ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric)
            (y m) (R + r),
            Nonempty (BackwardPointTrace (H m).toHistory first
              (Fin.last (H m).eventCount) (Fin.le_last first) z.val)) ∧
          (H m).time first ≤ time m - θ / Q₂ m := by
    intro R hR hR1
    let r := (1 - R) / 2
    have hr : 0 < r := by dsimp only [r]; linarith
    have hRr : R + r < 1 := by dsimp only [r]; linarith
    let θ := min θ₀ (1 / (6 * ((Ctime : ℝ) + 1) * C2))
    have hθ : 0 < θ := lt_min hθ₀ (by positivity)
    have hθθ₀ : θ ≤ θ₀ := min_le_left _ _
    have hθbudget : θ * (6 * ((Ctime : ℝ) + 1) * C2) ≤ 1 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hbudget : 6 * (Ctime : ℝ) * (C2 * θ) ≤ 1 := by
      have hC : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
      nlinarith [mul_nonneg (zero_le_one.trans hC2) hθ.le]
    refine ⟨r, C2, θ, hr, hRr, hC2, hθ, hbudget, ?_⟩
    filter_upwards [hqy, hyU] with m hm hmU
    refine ⟨isCompact_riemannianClosedBallOf_endpoint_P6L (A m) _ _ _, ?_,
      Fin.last (H m).eventCount, fun z _ =>
        ⟨BackwardPointTrace.singleton (H m).toHistory _ z.val⟩, ?_⟩
    · intro z hz
      obtain ⟨Wm, _⟩ := hW _ _ hmU hm
      have hQ₂pos : 0 < Q₂ m := zero_lt_one.trans_le (hQ₂ m)
      have hz' := ((A m).mem_scaled_endpoint_closedBall_iff (Q₂ m) hQ₂pos (y m) z (R + r)).mp hz
      have hball : z.val ∈ riemannianBallOf ((A m).flow.base.metric (time m))
          (y m).val (Real.sqrt (metricScalarAt ((A m).flow.base.metric (time m))
            (y m).val))⁻¹ := by
        have hsq : 0 < Real.sqrt (Q₂ m) := Real.sqrt_pos.mpr hQ₂pos
        change riemannianEDistOf _ _ _ < _
        apply lt_of_le_of_lt hz'
        rw [ENNReal.ofReal_lt_ofReal_iff (by rw [inv_pos]; exact Real.sqrt_pos.mpr Wm.Q_pos)]
        change (R + r) / Real.sqrt (Q₂ m) < (Real.sqrt ((A m).flow.scalar (time m) (y m).val))⁻¹
        rw [← hQ₂y, div_lt_iff₀ hsq, inv_mul_cancel₀ hsq.ne']
        exact hRr
      have hb := (Wm.scalar_bounds _ (Wm.ball_inside
        (riemannianBallOf_mono _ _ Wm.radius_lower hball))).2
      have hLz : metricScalarAt
          ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric z =
          (A m).flow.scalar (time m) z.val :=
        metricScalarAt_restrictOpen _ _ _
      rw [hLz]
      have : (A m).flow.scalar (time m) z.val ≤ C2 * Q₂ m := by
        rw [hQ₂y]
        exact hb
      nlinarith [hQ₂pos]
    · have hdiv : θ / Q₂ m ≤ θ₀ / Q₂ m :=
        div_le_div_of_nonneg_right hθθ₀ (zero_le_one.trans (hQ₂ m))
      linarith [hwindow m]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Set

/-- consumer：原 Cone:603（全局 `hW`）由 `_P6L` 版（`U = univ`）推出。 -/
example : type_of% @RetainedCoreHistory.final_slab_scalar_buffer_of_spatialCanonicalWitness.{0}
    := by
  intro H time A Ctime q y Q₂ hQ₂ hQ₂y eps C1 C2 hC2 hW hqy θ₀ hθ₀ hwindow
  exact RetainedCoreHistory.final_slab_scalar_buffer_of_spatialCanonicalWitness_P6L H time A Ctime
    q y Q₂ hQ₂ hQ₂y hC2 (fun _ => univ) (fun m z _ => hW m z) hqy
    (Eventually.of_forall fun _ => mem_univ _) hθ₀ hwindow

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
