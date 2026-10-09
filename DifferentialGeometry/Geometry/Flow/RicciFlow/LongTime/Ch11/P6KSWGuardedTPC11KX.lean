import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KSWGuardedLeafC11KX

/-!
# KSW-EXIT G3：L3（TP 复合叶）的 guarded 壳 → 子叶 T1（TL2）/ T4（TC）（O-CH11-KSWEXIT，`_C11KX`）

G1 壳剩余 binder L3 = `GuardedTPLeaf_C11KX`
（`exists_normalized_scalar_bound_of_chain_traces_age_C11KS2` 的 guarded 形）。TP 证明里 U 侧数据只经四个子叶：
* **T1** TL2 `exists_pointed_convergence_at_scalar_escape_of_traced_buffer_rad_age_C11KS2`
  （hderiv / hfinal / hgradient / htested；下接 TTC / Cone 叶与 escape-radius）——
  binder `GuardedTL2Leaf_C11KX`；
* **T2** `exists_isometric_ray_with_spatialNecks_of_bounded_threshold_window_P6WB`（只用 hgradient，
  窗口参数 `c i < s i` 任意）——**直接调旧叶**，窗口起点换 `c′ i`；
* **T3** `eventually_second_level_traces_of_chain_traces_window_P6WB`（只用 hgradient，窗口 `(a, ha)` 任意）
  ——**直接调旧叶**，窗口换 `c′`；
* **T4** TC `final_slab_punctured_cone_end_exclusion_of_trace_chains_of_radius_age_C11KS2`
  （hderiv / hfinal / htested，锥点尺度）——binder `GuardedTCLeaf_C11KX`。
`exists_guard_window_C11KX`（PROVED）：ClosedSlab `A` 在 compact carrier 上 `R(T, ·) ≤ Mb`（`scalarCont`）⇒
`∃ c′ ∈ [c, T)`，`[c′, T]` 上 guard 处处成立——这是五要素 3 中"`v → t⁻` 的传播邻域整体在 guard 内"。
`guardedTPLeaf_of_TL2_TC_C11KX`（PROVISIONAL[T1, T4]）：TP 证明逐字，T1 / T4 换 binder，T2 / T3 用 `c′`。
consumer：`shortSLT_guarded_of_TL2_TC_C11KX`（G1 壳 ∘ G2 L1 / L2 ∘ 本壳，PROVISIONAL[T1, T4]）。
T1 / T4 的修法（G4 起）：TTC:136 / Cone:108 的 buffer `θ` 再截短到 `min θ (1/(2·Ctime·B′))`（`B′` = 叶内
ceiling 常数，buffer 条件对 `θ` 向下封闭），使叶内深度落进 guard；锥点层同理（`Q₂` 尺度）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

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

/-- **guard 窗口（`_C11KX`，PROVED）**：ClosedSlab `A`（终端 `T`）、阈值 `q`、`Ct ≥ 0`、`c < T` ⇒
`∃ c′`，`c ≤ c′ < T`，`[c′, T]` 上 `GuardKX_C11KX (R(T, ·)) q Ct T t y` 对所有 `y` 成立（compact carrier +
`scalarCont` ⇒ `R(T, ·) ≤ Mb`）。 -/
theorem exists_guard_window_C11KX {P : OrientedThreeStage.{u}} {a T : ℝ} (A : P.ClosedSlab a T)
    (q : ℝ) (Ct : ℝ≥0) (c : ℝ) (hc : c < T) :
    ∃ c' : ℝ, c ≤ c' ∧ c' < T ∧ ∀ (y : P.Carrier) (t : ℝ), c' ≤ t → t ≤ T →
      GuardKX_C11KX (A.flow.scalar T) q Ct T t y := by
  have hTmem : T ∈ (RealTimeInterval.closed a T A.lt.le).carrier := by
    change T ∈ Icc a T
    exact ⟨A.lt.le, le_rfl⟩
  have h1 : Continuous (fun x : P.Carrier => ((T, x) : ℝ × P.Carrier)) :=
    continuous_const.prodMk continuous_id
  have h2 := A.equation.scalarCont.comp_continuous h1 (fun x => ⟨hTmem, mem_univ x⟩)
  obtain ⟨Mb, hMb⟩ := isCompact_univ.bddAbove_image h2.continuousOn
  have hMb' : ∀ x, A.flow.scalar T x ≤ Mb := fun x => hMb ⟨x, mem_univ x, rfl⟩
  have hden : 0 < 2 * ((Ct : ℝ) + 1) * (|Mb| + |q| + 1) := by positivity
  obtain ⟨τ, hτ, hb⟩ : ∃ τ : ℝ, 0 < τ ∧ (Ct : ℝ) * (|Mb| + |q| + 1) * τ ≤ 1 / 2 := by
    refine ⟨1 / (2 * ((Ct : ℝ) + 1) * (|Mb| + |q| + 1)), by positivity, ?_⟩
    rw [mul_one_div, div_le_iff₀ hden]
    nlinarith [Ct.coe_nonneg, abs_nonneg Mb, abs_nonneg q]
  refine ⟨max c (T - τ), le_max_left _ _, max_lt hc (by linarith), fun y t hct htT => ?_⟩
  have hR : A.flow.scalar T y ≤ |Mb| + |q| + 1 := by
    have := le_abs_self Mb
    linarith [hMb' y, abs_nonneg q]
  have hqM : q ≤ |Mb| + |q| + 1 := by
    have := le_abs_self q
    linarith [abs_nonneg Mb]
  exact guardKX_of_ceiling_C11KX Ct.coe_nonneg hR hqM htT ((le_max_right _ _).trans hct) hb

/-- **叶 T1（`_C11KX`，binder）**：TL2 `…_traced_buffer_rad_age_C11KS2` 逐字，`hderiv` / `hfinal` /
`hgradient` / `htested` 加 guard
`GuardKX_C11KX ((A i).flow.scalar (time i)) (q i) Ctime (time i) t ·`。 -/
def GuardedTL2Leaf_C11KX : Prop :=
  ∀ (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i)),
    let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl;
    let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount));
    ∀ (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount)),
    (∀ i, (H i).horizon < time i) →
    ∀ (Ctime Cgrad : ℝ≥0) (q : ℕ → ℝ), (∀ i, 0 < q i) →
    ∀ (U : ∀ i, Set ((H i).stage (Fin.last (H i).eventCount)).Carrier),
    ∀ (a : ℕ → ℝ), (∀ i, a i < time i) →
    (∀ i, ∀ j : Fin (H i).eventCount,
      ∀ (first : Fin ((H i).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U i, ∀ B : BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
        (Fin.le_last first) z,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ), a i ≤ t →
      q i < ((H i).toHistory.event j).incoming.flow.scalar t
        (B.point j.castSucc hf (Fin.le_last _)) →
      GuardKX_C11KX ((A i).flow.scalar (time i)) (q i) Ctime (time i) t z →
      |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v
        (B.point j.castSucc hf (Fin.le_last _))) (Iic t) t| ≤
        Ctime * ((H i).toHistory.event j).incoming.flow.scalar t
          (B.point j.castSucc hf (Fin.le_last _)) ^ 2) →
    (∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      a i ≤ t → q i < (A i).flow.scalar t y →
      GuardKX_C11KX ((A i).flow.scalar (time i)) (q i) Ctime (time i) t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2) →
    (∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      a i ≤ t → q i < (G i).flow.scalar t y →
      GuardKX_C11KX ((A i).flow.scalar (time i)) (q i) Ctime (time i) t y →
      ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential (G i).flow t y v| ≤
          Cgrad * (G i).flow.scalar t y * Real.sqrt ((G i).flow.scalar t y) *
            Real.sqrt (((G i).flow.base.metric t).inner y v v)) →
    ∀ (x : ∀ i, (G i).terminalRegularOpen) (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val),
    (∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val) →
    (∃ β : ℝ, 0 < β ∧ ∀ᶠ i in atTop,
      β ≤ (A i).flow.scalar (time i) (x i).val * (time i - a i)) →
    ∀ (Rad : ℝ), (∀ i, ∀ y ∈ riemannianBallOf
      (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
        (L i).metric) (x i) Rad, y.val ∈ U i) →
    (∀ R ε B : ℝ, 0 < R → 0 < ε → (∀ᶠ i in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
          (L i).metric) (x i) (R + ε),
        metricScalarAt (L i).metric y ≤ B * (A i).flow.scalar (time i) (x i).val) →
      ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ i in atTop, ∃ first : Fin ((H i).eventCount + 1),
        (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i).val ∧
        ∀ y ∈ riemannianClosedBallOf
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
            (L i).metric) (x i) R,
          Nonempty (BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
            (Fin.le_last first) y.val)) →
    (∃ R : ℝ, 0 < R ∧ R + 2 ≤ Rad ∧ ¬ ∃ B : ℝ, ∀ᶠ i in atTop,
      ∀ y : (G i).terminalRegularOpen,
        riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val)
          (zero_lt_one.trans_le (hQ i)) (L i).metric) (x i) y < ENNReal.ofReal R →
        metricScalarAt (L i).metric y / (A i).flow.scalar (time i) (x i).val ≤ B) →
    ∀ (Phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction Phi →
    (∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ) ∩ Ici (a i)) Phi) →
    (∀ i, Perelman.PhiAlmostNonnegative (G i).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i) ∩ Ici (a i)) Phi) →
    ∀ (κ σ₀ : ℝ) (σ : ℕ → ℝ), 0 < κ → 0 < σ₀ →
    (∀ i, σ₀ ≤ σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val)) →
    (∀ i (t : ℝ) (ht : (H i).horizon < t) (hts : t < time i), a i ≤ t →
      let B := (H i).extendHorizon t ht.le
        (((A i).restrictIncoming le_rfl (A i).lt le_rfl).closedPrefix t
          ((H i).time_le_horizon.trans_lt ht) hts) (hinit i);
      let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H i).horizon_nonneg.trans ht.le, le_rfl⟩;
      ∀ z ∈ U i, GuardKX_C11KX ((A i).flow.scalar (time i)) (q i) Ctime (time i) t z →
      ∀ (y : (B.toHistory.stageAt tm).Carrier), HEq y z →
      ∀ (b : ℝ), 0 < b → b ≤ σ i →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b)) →
    ∃ (rho : ℝ), 0 < rho ∧ rho + 2 ≤ Rad ∧ ∃ (ind : ℕ → ℕ), StrictMono ind ∧
      ∃ z : ∀ i, (G (ind i)).terminalRegularOpen,
      let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
        { obj := fun i =>
            { M := (G (ind i)).terminalRegularOpen
              basepoint := x (ind i)
              metric := scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
                (zero_lt_one.trans_le (hQ (ind i))) (L (ind i)).metric } };
      ∃ (f : ℕ → ℕ), StrictMono f ∧
        ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
        ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
          (F : PointedRiemannianConvergenceMaps X.connectedComponent P f),
          let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint;
          let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i);
          let F' := F.liftTargetOpen U hp;
          ∃ M : MetricConvergenceData F',
            metricScalarAt P.metric P.basepoint = 1 ∧
            (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
            (∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho) ∧
            (∀ R : ℝ, 0 ≤ R → R < rho →
              IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
            (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆
              F'.target n) ∧
            (∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ y ∈ F'.source n,
              ∀ v : TangentSpace ThreeModel y,
              (1 - eps) * P.metric.inner y v v ≤
                  (X.obj (f n)).metric.inner (F'.map n y)
                    (mfderiv ThreeModel ThreeModel (F'.map n) y v)
                    (mfderiv ThreeModel ThreeModel (F'.map n) y v) ∧
                (X.obj (f n)).metric.inner (F'.map n y)
                  (mfderiv ThreeModel ThreeModel (F'.map n) y v)
                  (mfderiv ThreeModel ThreeModel (F'.map n) y v) ≤
                    (1 + eps) * P.metric.inner y v v) ∧
            (∀ n, riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint (z (f n)) ≠ ⊤) ∧
            Tendsto (fun n => (riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint
              (z (f n))).toReal) atTop (𝓝 rho) ∧
            Tendsto (fun n => metricScalarAt (L (ind (f n))).metric (z (f n)) /
              (A (ind (f n))).flow.scalar (time (ind (f n))) (x (ind (f n))).val)
              atTop atTop

/-- **叶 T4（`_C11KX`，binder）**：TC `…_of_radius_age_C11KS2` 逐字，`hderiv` / `hfinal` / `htested` 加
guard `GuardKX_C11KX ((A i).flow.scalar (time i)) (q i) Ctime (time i) t ·`。 -/
def GuardedTCLeaf_C11KX : Prop :=
  ∀
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (_ : ∀ i, (H i).horizon < time i) (Ctime : ℝ≥0) (q : ℕ → ℝ) (_ : ∀ i, 0 < q i)
    (U : ∀ i, Set ((H i).stage (Fin.last (H i).eventCount)).Carrier) (a : ℕ → ℝ)
    (_ : ∀ i, ∀ j : Fin (H i).eventCount,
      ∀ (first : Fin ((H i).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U i, ∀ B : BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
        (Fin.le_last first) z,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ), a i ≤ t →
      q i < ((H i).toHistory.event j).incoming.flow.scalar t
        (B.point j.castSucc hf (Fin.le_last _)) →
      GuardKX_C11KX ((A i).flow.scalar (time i)) (q i) Ctime (time i) t z →
      |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v
        (B.point j.castSucc hf (Fin.le_last _))) (Iic t) t| ≤
        Ctime * ((H i).toHistory.event j).incoming.flow.scalar t
          (B.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (_ : ∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      a i ≤ t → q i < (A i).flow.scalar t y →
      GuardKX_C11KX ((A i).flow.scalar (time i)) (q i) Ctime (time i) t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (_ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    (_ : ∃ β : ℝ, 0 < β ∧ ∀ᶠ i in atTop,
      β ≤ (A i).flow.scalar (time i) (x i).val * (time i - a i))
    (Rad : ℝ) (_ : ∀ i, ∀ y ∈ riemannianBallOf
      (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
        ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
      (x i) Rad, y.val ∈ U i)
    {Phi : ℝ → ℝ} (_ : Perelman.AdmissiblePinchingFunction Phi)
    (_ : ∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ) ∩ Ici (a i)) Phi)
    (_ : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i) ∩ Ici (a i)) Phi)
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (_ : 0 < κ) (_ : 0 < σ₀)
    (_ : ∀ i, σ₀ ≤ σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val))
    (_ : ∀ i (t : ℝ) (ht : (H i).horizon < t) (hts : t < time i), a i ≤ t →
      let B := (H i).extendHorizon t ht.le
        (((A i).restrictIncoming le_rfl (A i).lt le_rfl).closedPrefix t
          ((H i).time_le_horizon.trans_lt ht) hts) (hinit i)
      let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H i).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ z ∈ U i, GuardKX_C11KX ((A i).flow.scalar (time i)) (q i) Ctime (time i) t z →
      ∀ (y : (B.toHistory.stageAt tm).Carrier), HEq y z →
      ∀ (b : ℝ), 0 < b → b ≤ σ i →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b))
    {eps C1 C2 : ℝ}
    (_ : ∀ i, ∀ y ∈ U i, q i < (A i).flow.scalar (time i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (time i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    {f : ℕ → ℕ} (_ : StrictMono f) (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((A i).flow.scalar (time i) (x i).val)
              (zero_lt_one.trans_le (hQ i))
              ((A i).endpointTerminalLimitMetric
                ((H i).stage (Fin.last (H i).eventCount))).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (_ : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    {rho : ℝ}
    (_ : ∀ z : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint z < ENNReal.ofReal rho)
    (_ : rho + 2 ≤ Rad)
    (W : TopologicalSpace.Opens Pl.M) (hWc : PathConnectedSpace W),
    let _ : PathConnectedSpace W := hWc
    let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
    let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
    ∀ (qW : UniformSpace.Completion W) (delta : ℝ), 0 < delta →
      IsCompact (Metric.closedBall qW delta) →
      Metric.closedBall qW delta ⊆
        insert qW (range (fun z : W => (z : UniformSpace.Completion W))) →
      Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) →
      ∀ xW : ℕ → W, Tendsto (fun n => (xW n : UniformSpace.Completion W)) atTop (𝓝 qW) →
      Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop →
      ∀ θ₂ : ℝ, 0 < θ₂ → (∀ m, ∀ᶠ n in atTop, ∃ first : Fin ((H (f n)).eventCount + 1),
        (H (f n)).time first ≤ time (f n) - θ₂ /
          (A (f n)).flow.scalar (time (f n)) (F.map n (xW m : Pl.M)).val ∧
        ∀ z ∈ riemannianBallOf ((A (f n)).flow.base.metric (time (f n)))
          (F.map n (xW m : Pl.M)).val
          (Real.sqrt ((A (f n)).flow.scalar (time (f n))
            (F.map n (xW m : Pl.M)).val))⁻¹,
          Nonempty (BackwardPointTrace (H (f n)).toHistory first
            (Fin.last (H (f n)).eventCount) (Fin.le_last first) z)) →
      ∀ c : ℝ, 0 < c →
      (∀ᶠ n in atTop, c ≤ metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2) →
      (∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B) → False

/-- **L3 壳（`_C11KX`，PROVISIONAL[T1, T4]）**：TP `…_chain_traces_age_C11KS2` 证明逐字；T1 / T4 调用换
binder；T2（ray with necks）/ T3（second-level traces）只在 `t → time⁻` 用梯度 ⇒ 窗口起点换
`c′ i`（`exists_guard_window_C11KX`）后**直接调树内旧叶**（guard 由 compact 上界付）。 -/
theorem guardedTPLeaf_of_TL2_TC_C11KX (hT1 : GuardedTL2Leaf_C11KX.{u})
    (hT4 : GuardedTCLeaf_C11KX.{u}) : GuardedTPLeaf_C11KX.{u} := by
  intro H time A hinit hs Ctime Cgrad q hq U a ha hderiv hfinal hgradient x hQ hqQ hQa Rad hU hQlim
    Phi hPhi hpinch hpinchFinal κ σ₀ σ hκ hσ₀ hσQ htested eps C1 C2 heps hW htime Kc lam θ hlam hθ D
    hD htrace
  choose c' hac' hc' hg' using fun i => exists_guard_window_C11KX (A i) (q i) Ctime (a i) (ha i)
  have hgr' : ∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      c' i ≤ t → q i < (A i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential
            ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow t y v| ≤
          Cgrad * (A i).flow.scalar t y * Real.sqrt ((A i).flow.scalar t y) *
            Real.sqrt (((A i).flow.base.metric t).inner y v v) :=
    fun i y hy t ht hct hqt v =>
      hgradient i y hy t ht ((hac' i).trans hct) hqt (hg' i y t hct ht.2.le) v
  intro R hR hRRad
  by_contra hB
  have hbuf : ∀ R' ε' B' : ℝ, 0 < R' → 0 < ε' → (∀ᶠ i in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
          (x i) (R' + ε'),
        metricScalarAt ((A i).endpointTerminalLimitMetric
          ((H i).stage (Fin.last (H i).eventCount))).metric y ≤
          B' * (A i).flow.scalar (time i) (x i).val) →
      ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∀ᶠ i in atTop, ∃ first : Fin ((H i).eventCount + 1),
        (H i).time first ≤ time i - θ₁ / (A i).flow.scalar (time i) (x i).val ∧
        ∀ y ∈ riemannianClosedBallOf
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
            ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
          (x i) R',
          Nonempty (BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
            (Fin.le_last first) y.val) := by
    intro R' ε' B' hR' hε' hB'
    by_cases hlt : R' + ε' < R
    · exact RetainedCoreHistory.traced_buffer_of_chain_traces_P6L H time A x hQ U Rad hU hθ D hD
        htime htrace R' ε' B' hR' hε' (by linarith) hB'
    · exfalso
      apply hB
      refine ⟨B', hB'.mono fun i hi y hy => ?_⟩
      rw [div_le_iff₀ (zero_lt_one.trans_le (hQ i))]
      exact hi y (hy.trans_le (ENNReal.ofReal_le_ofReal (not_lt.mp hlt))).le
  have hL1 :=
    hT1
    H time A hinit hs Ctime Cgrad q hq U a ha hderiv hfinal hgradient x hQ hqQ hQa Rad hU hbuf
    ⟨R, hR, hRRad, hB⟩ Phi hPhi hpinch hpinchFinal κ σ₀ σ hκ hσ₀ hσQ htested
  dsimp only at hL1
  obtain ⟨rho, hrho, hrhoRad, ind, hind, z, f, hf, r, hr, hrlim, Pl, F₀, M, _, hcan, hradial,
      hcompact, hcapture, hmetric, hfinite, hdist, hescape⟩ := hL1
  let F := PointedRiemannianConvergenceMaps.liftTargetOpen
    (S := { obj := fun i =>
          { M := ((A (ind i)).restrictIncoming le_rfl (A (ind i)).lt le_rfl).terminalRegularOpen
            basepoint := x (ind i)
            metric := scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
              (zero_lt_one.trans_le (hQ (ind i)))
              ((A (ind i)).endpointTerminalLimitMetric
                ((H (ind i)).stage (Fin.last (H (ind i)).eventCount))).metric } })
    (fun i => connectedComponentOpen (I := ThreeModel) (x (ind i)))
    (fun i => (mem_connectedComponent : x (ind i) ∈
      connectedComponentOpen (I := ThreeModel) (x (ind i)))) F₀
  have halpha : (0 : ℝ) < 1 / 4000000 := by norm_num
  obtain ⟨g, hg, hg0, hblow, hnecks⟩ :=
    exists_isometric_ray_with_spatialNecks_of_bounded_threshold_window_P6WB
    (fun i => (H (ind i)).stage (Fin.last (H (ind i)).eventCount))
    (fun i => (H (ind i)).time (Fin.last (H (ind i)).eventCount)) (fun i => time (ind i))
    (fun i => A (ind i)) Cgrad (fun i => q (ind i)) (fun i => U (ind i))
    (fun i => c' (ind i)) (fun i => hc' (ind i)) (fun i => hgr' (ind i))
    (fun i => x (ind i)) (fun i => hQ (ind i)) (fun i => hqQ (ind i)) halpha (by norm_num) heps
    (fun i => hW (ind i)) hrho f hf r (fun n => (hr n).1) hrlim Pl F M hcan hradial hcompact
    hcapture (fun ε hε => (hmetric ε hε).mono fun n hn y hy v => (hn y hy v).1)
    (fun n => z (f n)) hfinite hdist hescape (Rad := rho + 1) (by linarith) (fun i y hy => by
      have hQi : 0 < (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val :=
        zero_lt_one.trans_le (hQ (ind i))
      have hlpr := Perelman.CanonicalNeighborhood.localPropagationRadius_pos Cgrad.coe_nonneg
      have hlpr' := Perelman.CanonicalNeighborhood.localPropagationRadius_le Cgrad.coe_nonneg
      have hsQ : 0 < Real.sqrt ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) :=
        Real.sqrt_pos.mpr hQi
      have hs2 : Real.sqrt ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) ≤
          Real.sqrt (2 * (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) :=
        Real.sqrt_le_sqrt (by linarith)
      have hs2pos := hsQ.trans_le hs2
      have h1 : Real.sqrt ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) *
          (Perelman.CanonicalNeighborhood.localPropagationRadius Cgrad /
            Real.sqrt (2 * (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)) ≤
          Perelman.CanonicalNeighborhood.localPropagationRadius Cgrad := by
        rw [mul_div_assoc', div_le_iff₀ hs2pos]
        exact (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_left hs2 hlpr.le)
      refine (A (ind i)).eventually_moving_ball_subset_of_terminal_ball_P6L (U (ind i)) y.val
        (by positivity) ?_
      exact (A (ind i)).ball_subset_of_scaled_dist_lt_P6L hQi (x (ind i)) y (U (ind i))
        (by linarith) (by positivity) hy (by nlinarith) (hU (ind i)))
  have hsec := metricRm04StandardAt_nonneg_of_normalized_terminal_pinching_window_P6WA
    (fun i => (H (ind i)).stage (Fin.last (H (ind i)).eventCount))
    (fun i => (H (ind i)).time (Fin.last (H (ind i)).eventCount)) (fun i => time (ind i))
    (fun i => A (ind i)) (fun i => a (ind i)) (fun i => ha (ind i)) (fun i => x (ind i))
    (fun i => hQ (ind i)) hPhi (fun i => hpinchFinal (ind i)) Pl F M hcan
    (hQlim.comp (hind.comp hf).tendsto_atTop)
  let _ : EMetricSpace Pl.M := Pl.emetricSpace
  have hfin : ∀ a b : Pl.M, edist a b ≠ ⊤ := by
    intro a b
    apply ne_top_of_le_ne_top _ (edist_triangle_left a b Pl.basepoint)
    exact ENNReal.add_ne_top.mpr ⟨(hradial a).ne_top, (hradial b).ne_top⟩
  let _ : MetricSpace Pl.M := EMetricSpace.toMetricSpace hfin
  obtain ⟨qc, hqc, _⟩ :=
    DifferentialGeometry.Geometry.exists_completion_endpoint_of_isometry hrho hg
  obtain ⟨W, hWc, hrest⟩ := exists_punctured_cone_end_of_spatial_necks_with_ray_scalar_bound
    Pl.metric (fun _ _ => rfl) hrho halpha (by norm_num) hsec g hg hblow qc hqc hnecks
  let _ : PathConnectedSpace W := hWc
  let mW : MetricSpace W :=
    let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
    MetricSpace.ofT0PseudoMetricSpace W
  let _ : MetricSpace W := mW
  let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
  let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
  let eW : PseudoEMetricSpace W :=
    @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
  let _ : WeakPseudoEMetricSpace W :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
  obtain ⟨qW, delta, hdelta, _, _, hK, hcover, xW, times, hux, _, hxW, _, hQW, hlowerW, hupperW,
    hcone, Kr, hKr1, hKr⟩ := hrest
  have hQW' : Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop := by
    simpa only [metricScalarAt_restrictOpen] using hQW
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (hKr.and (hQW'.eventually_ge_atTop 3))
  have hlower' : ∀ᶠ n in atTop, ((2 * (1 / 4000000 : ℝ))⁻¹) ^ 2 / 8 ≤
      metricScalarAt Pl.metric (xW (n + m₀) : Pl.M) *
        dist (xW (n + m₀) : UniformSpace.Completion W) qW ^ 2 :=
    Eventually.of_forall fun n => by
      simpa only [metricScalarAt_restrictOpen] using hlowerW (n + m₀)
  have hupper' : ∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW (n + m₀) : Pl.M) *
      dist (xW (n + m₀) : UniformSpace.Completion W) qW ^ 2 ≤ B := by
    obtain ⟨B, _, hB⟩ := hupperW
    have hB' : ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
      simpa only [metricScalarAt_restrictOpen] using hB
    exact ⟨B, (tendsto_add_atTop_nat m₀).eventually hB'⟩
  have hux' (m : ℕ) : (xW (m + m₀) : Pl.M) = g (times (m + m₀)) := hux (m + m₀)
  obtain ⟨θ₂, hθ₂, htr₂⟩ :=
    RetainedCoreHistory.eventually_second_level_traces_of_chain_traces_window_P6WB
    (fun i => H (ind i)) (fun i => time (ind i)) (fun i => A (ind i))
    Cgrad (fun i => q (ind i)) (fun i => U (ind i)) (fun i => c' (ind i)) (fun i => hc' (ind i))
    (fun i => hgr' (ind i)) (fun i => x (ind i)) (fun i => hQ (ind i)) (fun i => hqQ (ind i))
    Rad (fun i => hU (ind i))
    (fun i => hW (ind i)) hlam hθ hPhi
    (fun i => D (ind i)) (hD.comp hind.tendsto_atTop) (htime.comp hind.tendsto_atTop)
    (fun i => htrace (ind i)) hf Pl F M hcan g (fun s t => (hg.edist_eq s t : _)) hrhoRad
    ⟨0, le_rfl, hrho⟩ rfl hg0 (fun m => times (m + m₀)) (fun m => (xW (m + m₀) : Pl.M)) hux'
    hKr1 (fun m => by
      have h := (hm₀ (m + m₀) (Nat.le_add_left _ _)).1
      intro s hs
      rw [← hux (m + m₀)] at h ⊢
      exact h s hs)
    (fun m => by
      rw [← hux (m + m₀)]
      exact (hm₀ (m + m₀) (Nat.le_add_left _ _)).2)
  exact hT4
    (fun i => H (ind i)) (fun i => time (ind i)) (fun i => A (ind i)) (fun i => hinit (ind i))
    (fun i => hs (ind i)) Ctime (fun i => q (ind i)) (fun i => hq _) (fun i => U (ind i))
    (fun i => a (ind i)) (fun i => hderiv (ind i))
    (fun i => hfinal (ind i)) (fun i => x (ind i)) (fun i => hQ _) (fun i => hqQ _)
    (age_comp_C11KS2 hQa hind.tendsto_atTop) Rad (fun i => hU (ind i)) hPhi (fun i => hpinch _)
    (fun i => hpinchFinal _) (fun i => σ (ind i)) hκ hσ₀ (fun i => hσQ _)
    (fun i => htested (ind i)) (fun i => hW (ind i)) hf Pl F M hcan hradial hrhoRad W hWc qW
    delta hdelta hK
    hcover hcone (fun n => xW (n + m₀)) (hxW.comp (tendsto_add_atTop_nat m₀))
    (hQW'.comp (tendsto_add_atTop_nat m₀)) θ₂ hθ₂ htr₂ _ (by norm_num) hlower' hupper'

/-- **consumer（G3，PROVISIONAL[T1, T4]）**：G1 壳 ∘ G2 的 L1 / L2 证书 ∘ L3 壳。 -/
theorem shortSLT_guarded_of_TL2_TC_C11KX (hT1 : GuardedTL2Leaf_C11KX.{u})
    (hT4 : GuardedTCLeaf_C11KX.{u}) {θ : ℝ} (hθ : 0 < θ) : ShortSLTGuarded_C11KX.{u} θ :=
  shortSLT_guarded_of_TP_C11KX (guardedTPLeaf_of_TL2_TC_C11KX hT1 hT4) hθ

/-- consumer：T1 ∧ T4 ⇒ K-SW（`0 < θ₀ ≤ 1/2`）。 -/
example (hT1 : GuardedTL2Leaf_C11KX.{u}) (hT4 : GuardedTCLeaf_C11KX.{u}) {θ₀ : ℝ}
    (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 1 / 2) : KSW_C11KS.{u} θ₀ :=
  ksw_of_shortSLT_C11KS hθ₀ hθ₀2
    (ShortSLTGuarded_C11KX.toShortSLT (shortSLT_guarded_of_TL2_TC_C11KX hT1 hT4 hθ₀))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
