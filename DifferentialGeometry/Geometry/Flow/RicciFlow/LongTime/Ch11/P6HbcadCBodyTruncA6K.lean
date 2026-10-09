import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HbcadCGuardedP6HK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDSlabsCaseP6SB2

/-!
# slice 槽 `hbcadC` 的截断孪生（O-CH11-KERNB-A6 / W7 G3d，`_A6K`）

HARNACK A1 G2 `hbcadC_of_guarded_P6HK`（无 `hclosC`）链的截断孪生：`hslabK` 全形
`EventSlabsDerivative C (Q n) (Fin.last)` 换 kernel body 截断形（终点 `min (time j.succ) (tK n)`），
加 `{tK}` 与连接行 `hTnK : ∀ n, Tn n ≤ tK n`（KTRUNC1 同法）。使用点核查：只有两处——
`hUVC` 的 (A) 天花板支（时刻 `v′ < v ≤ σ ≤ Tn ≤ tK`）与 core 的 CWP 支前缀 slab / 当前 slab
（时刻 `< v ≤ σ`）；两处改为 `lt_min`，其余三个定理逐字转发。生成：`gen/gen3c.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- 前缀 slab 时刻（`_A6K`，PROVED）。 -/
theorem time_succ_le_of_castSucc_lt_A6K (H : RetainedCoreHistory.{u}) {i j : Fin H.eventCount}
    (h : i.castSucc < j.castSucc) : H.time i.succ ≤ H.time j.castSucc :=
  H.time_strictMono.monotone (Fin.le_def.2 (by
    have := Fin.lt_def.1 h
    simp only [Fin.val_succ, Fin.val_castSucc] at this ⊢
    omega))

namespace RetainedCoreHistory

/-- `hbound_of_eventSlabs_P6SB2` 截断孪生（`_A6K`）。 -/
theorem hbound_of_eventSlabsT_A6K (K : RetainedCoreHistory.{u}) {C : ℝ≥0} {q : ℝ}
    {tK : ℝ} (hslab : ∀ e : Fin K.eventCount,
      (K.toHistory.event e).incoming.DerivativeBoundBefore C q (min (K.time e.succ) tK))
    {a t : Icc (0 : ℝ) K.toHistory.horizon} (hat : a ≤ t)
    (htl : K.toHistory.activeStage t < Fin.last K.eventCount) (htK : (t : ℝ) < tK)
    {y : (K.toHistory.stageAt t).Carrier}
    (A : BackwardPointTrace K.toHistory (K.toHistory.activeStage a) (K.toHistory.activeStage t)
      (K.toHistory.activeStage_mono hat) y) :
    ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      K.toHistory.time (K.toHistory.activeStage v) < (v : ℝ) → (v : ℝ) < K.toHistory.horizon →
      q < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
        (A.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
          (K.toHistory.activeStage_mono hvt)) →
      |derivWithin (fun s => metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) s)
        (A.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
          (K.toHistory.activeStage_mono hvt))) (Iic (v : ℝ)) v| ≤
        C * metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
          (A.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
            (K.toHistory.activeStage_mono hvt)) ^ 2 := by
  intro v hav hvt htv _ hq
  have hlt : K.toHistory.activeStage v < Fin.last K.eventCount :=
    lt_of_le_of_lt (K.toHistory.activeStage_mono hvt) htl
  obtain ⟨e, he⟩ := Fin.exists_castSucc_eq.mpr (ne_of_lt hlt)
  have hvlt : (K.toHistory.activeStage v).val < K.eventCount := by
    rw [← he]
    exact e.isLt
  have hnext := K.toHistory.activeStage_before_next v hvlt
  have hfin : (⟨(K.toHistory.activeStage v).val + 1, by omega⟩ : Fin (K.eventCount + 1)) =
      e.succ := by
    apply Fin.ext
    change (K.toHistory.activeStage v).val + 1 = e.succ.val
    rw [Fin.val_succ, ← he, Fin.val_castSucc]
  have hv2 : (v : ℝ) < K.toHistory.time e.succ :=
    hnext.trans_eq (congrArg K.toHistory.time hfin)
  have hgen : ∀ (m : Fin (K.eventCount + 1)) (hm : e.castSucc = m)
      (h1 : K.toHistory.activeStage a ≤ m) (h2 : m ≤ K.toHistory.activeStage t),
      K.toHistory.time m < (v : ℝ) →
      q < metricScalarAt (K.toHistory.stageMetric m v) (A.point m h1 h2) →
      |derivWithin (fun s => metricScalarAt (K.toHistory.stageMetric m s) (A.point m h1 h2))
          (Iic (v : ℝ)) v| ≤
        C * metricScalarAt (K.toHistory.stageMetric m v) (A.point m h1 h2) ^ 2 := by
    intro m hm h1 h2 htm hqm
    subst hm
    simp only [ObservedHistory.stageMetric_castSucc_apply] at hqm ⊢
    exact hslab e _ v ⟨htm, lt_min hv2 (lt_of_le_of_lt hvt htK)⟩ hqm
  exact hgen _ he _ _ htv hq

/-- `scalar_gt_of_slabs_prefix_P6SB2` 截断孪生（`_A6K`）。 -/
theorem scalar_gt_of_slabs_prefixT_A6K (K : RetainedCoreHistory.{u}) {C : ℝ≥0} {Q : ℝ}
    (hQ : 0 < Q) {tK : ℝ} (hslab : ∀ e : Fin K.eventCount,
      (K.toHistory.event e).incoming.DerivativeBoundBefore C Q (min (K.time e.succ) tK))
    (j : Fin K.eventCount) (σ : Icc (0 : ℝ) K.toHistory.horizon)
    (hact : K.toHistory.activeStage σ = j.castSucc)
    (i : Fin (K.prefixAt j.castSucc).eventCount)
    (first : Fin ((K.prefixAt j.castSucc).eventCount + 1)) (hf : first ≤ i.castSucc)
    (z : (K.stage j.castSucc).Carrier)
    (Btr : BackwardPointTrace (K.prefixAt j.castSucc).toHistory first
      (Fin.last (K.prefixAt j.castSucc).eventCount) (Fin.le_last first) z)
    (v' : Icc (0 : ℝ) K.toHistory.horizon) (hv1 : (K.prefixAt j.castSucc).time i.castSucc < v')
    (hv2 : (v' : ℝ) < (K.prefixAt j.castSucc).time i.succ) (hvs : v' ≤ σ)
    (htK : (σ : ℝ) < tK)
    (hend : 2 * Q < (K.toHistory.event j).incoming.flow.scalar σ z)
    (htime : C * (K.toHistory.event j).incoming.flow.scalar σ z * ((σ : ℝ) - v') ≤ 1 / 2) :
    Q < ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
      (Btr.point i.castSucc hf (Fin.le_last _)) := by
  obtain ⟨z', A, hz', hAx⟩ := K.exists_historyTrace_of_prefix_P6SB2 j σ hact i first hf z Btr v'
    hv1 hv2 hvs
  have hsc := K.scalar_of_incoming_P6JG3H j hact.symm (σ : ℝ) z z' hz'
  have htl : K.toHistory.activeStage σ < Fin.last K.eventCount := by
    rw [hact]
    exact Fin.castSucc_lt_last j
  have hlow := BackwardPointTrace.scalar_gt_of_time_local_derivative_control_P6SB2 hvs A hQ
    (K.hbound_of_eventSlabsT_A6K hslab hvs htl htK A) (by rw [hsc]; exact hend)
    (by rw [hsc]; exact htime) v' le_rfl hvs
  let e : Fin K.eventCount := Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i
  have hvact : K.toHistory.activeStage v' = e.castSucc :=
    K.activeStage_eq_of_mem_slab_P6JG3H e v' hv1.le hv2
  have hsc2 := K.scalar_of_incoming_P6JG3H e hvact.symm v'
    (Btr.point i.castSucc hf (Fin.le_last _)) _ hAx
  rw [hsc2] at hlow
  exact hlow

end RetainedCoreHistory

/-- **`hUVC_of_selection_Cg_guarded_P6HK` 的截断孪生（`_A6K`）**：见文件头。 -/
theorem ObservedHistory.hUVC_of_selection_Cg_guarded_A6K {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2')
    {κ Aκ : ℝ} (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L r ρV : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
      (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))
    {K : ℕ → RetainedCoreHistory.{u}} (hKh : Kh = fun n => (K n).toHistory) (hCg : 1 ≤ Cg)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    {Q T₀ tK : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hslabK : ∀ n (j₀ : Fin (K n).eventCount),
      ((K n).toHistory.event j₀).incoming.DerivativeBoundBefore Ctime' (Q n)
        (min ((K n).time j₀.succ) (tK n)))
    (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    {rX : ℝ} (hrX : 0 < rX)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) rX)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - rX ^ 2)
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s) (aP n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((L n / 4 + Dd) / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v x →
            ∃ W : SpatialCanonicalWitness (((Kh n).event j').incoming.flow.base.metric v)
              eps C1' C2' x, W.capTubeHasNeckChart eps) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential ((Kh n).event j').incoming.flow v' x ξ| ≤
                (C2'.toNNReal : ℝ) * ((Kh n).event j').incoming.flow.scalar v' x *
                  Real.sqrt (((Kh n).event j').incoming.flow.scalar v' x) *
                  Real.sqrt ((((Kh n).event j').incoming.flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (Kh n).horizon),
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (Kh n).time j'.castSucc < τ → (τ : ℝ) < (Kh n).time j'.succ →
            ∀ z ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                  (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            (v - τ) * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                  ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                  (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            |derivWithin (fun s => ((Kh n).event j').incoming.flow.scalar s x) (Iic v') v'| ≤
              Ctime' * ((Kh n).event j').incoming.flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (Kh n).eventCount) (first : Fin ((Kh n).eventCount + 1))
              (hf : first ≤ i.castSucc) (hij : i.castSucc < j'.castSucc),
            ∀ z ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (Kh n) first j'.castSucc (hf.trans hij.le) z,
            ∀ v' ∈ Ioo ((Kh n).time i.castSucc) ((Kh n).time i.succ),
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            Cg * R n < ((Kh n).event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf hij.le) →
            |derivWithin (fun s => ((Kh n).event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf hij.le)) (Iic v') v'| ≤
              Ctime' * ((Kh n).event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf hij.le) ^ 2) := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_hnc_of_records_P6SB2.{u}
  obtain ⟨κs, hκdef⟩ : ∃ κs : ℝ, κs = min (min (rX / 50) (localPropagationRadius C2' / 2))
      (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4)))) := ⟨_, rfl⟩
  have hρ : 0 < localPropagationRadius C2' := localPropagationRadius_pos hC2
  have hm1 : (1 : ℝ) ≤ max (Ctime' : ℝ) 1 := le_max_right _ _
  have hc0 : (0 : ℝ) ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by positivity
  have hc1 : 1 / (2 * max (Ctime' : ℝ) 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hCc : (Ctime' : ℝ) * (1 / (2 * max (Ctime' : ℝ) 1)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [le_max_left (Ctime' : ℝ) 1]
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  intro Rad B σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr
  obtain ⟨Cc, hCcdef⟩ : ∃ Cc : ℝ, Cc = max (max 1 (6 * Cg))
      (2 * Cg / localPropagationRadius C2' ^ 2) := ⟨_, rfl⟩
  obtain ⟨MC, hMCdef⟩ : ∃ MC : ℝ,
      MC = max 1 (2 * Real.sqrt 3 * (Cc / 2 + max Cc (2 * Real.exp 4))) := ⟨_, rfl⟩
  obtain ⟨ρg, hρgdef⟩ : ∃ ρg : ℝ, ρg = localPropagationRadius C2' / Real.sqrt (2 * Cg) :=
    ⟨_, rfl⟩
  have hRt : Tendsto R atTop atTop := tendsto_atTop_mono hRn1 hnat
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hX1 : (1 : ℝ) ≤ max B 0 - σ₁ + 1 := by
    have := le_max_right B 0
    linarith
  filter_upwards [Filter.Eventually.filter_mono hφt (hRt.eventually_ge_atTop (2500 * MC / rX ^ 2)),
    Filter.Eventually.filter_mono hφt (hL.eventually_ge_atTop
      (4 * (Dd + max Rad 0 + ρg) + 4 * (2 + 16 * Real.sqrt MC) + 4)),
    Filter.Eventually.filter_mono hφt
      (hL.eventually_ge_atTop (max (2 * max Rad 0) (max B 0 - σ₁ + 1))),
    Filter.Eventually.filter_mono hφt (hwin (max B 0 - σ₁ + 1) (by linarith)),
    Filter.Eventually.filter_mono hφt hκR, Filter.Eventually.filter_mono hφt hdistσ,
    Filter.Eventually.filter_mono hφt (hL.eventually_ge_atTop (max (max
      (8 * localPropagationRadius C2')
      (4 * (max Rad 0 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κs) + 4)) 2)),
    Filter.Eventually.filter_mono hφt (hT₀ (max B 0 - σ₁ + 1)),
    Filter.Eventually.filter_mono hφt (hnat.eventually_gt_atTop (StandardCap.transitionEnd + 10)),
    Filter.Eventually.filter_mono hφt (hnat.eventually_ge_atTop 9),
    Filter.Eventually.filter_mono hφt (hnat.eventually_ge_atTop (6 / rX ^ 2 + 1)),
    Filter.Eventually.filter_mono hφt (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (ge_mem_nhds (lt_min hε₀ (by norm_num : (0 : ℝ) < 1 / 2))))]
    with n hRbig hLbig hLn hwn hκn hdσ hLX2 hT₀n hTEn h9 hr6 hacn
  intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw
  have hRn := hR n
  have hLX : max B 0 - σ₁ + 1 ≤ L n := (le_max_right _ _).trans hLn
  have hL0 : 0 ≤ L n := by linarith
  have hRad : 2 * max Rad 0 ≤ L n := (le_max_left _ _).trans hLn
  have hvσ : v ≤ (σ n : ℝ) := by
    have : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    linarith
  have hvtK : v < tK n := by
    have : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    have h2 : (σ n : ℝ) ≤ Tn n := hsT n
    linarith [hTnK n]
  have hwinB : ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ →
      (aSeed n : ℝ) ≤ τ ∧ (σ n : ℝ) - L n ^ 2 / R n ≤ τ := fun τ hτ => by
    obtain ⟨e1, e2⟩ := window_P6L3 hRn hRw hvσ1 hτ le_rfl hX1 hLX
    exact ⟨hwn.trans e1, e2⟩
  have hwin0 : (aSeed n : ℝ) ≤ v ∧ (σ n : ℝ) - L n ^ 2 / R n ≤ v := by
    have hX0 : max 0 0 - σ₁ + 1 ≤ max B 0 - σ₁ + 1 := by
      rw [max_self]
      linarith [le_max_right B 0]
    obtain ⟨e1, e2⟩ := window_P6L3 (B := 0) (τ := v) hRn hRw hvσ1 (by simp) hX0 hX1 hLX
    exact ⟨hwn.trans e1, e2⟩
  have hCg0 : 0 < Cg := lt_of_lt_of_le one_pos hCg
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hρg0 : 0 ≤ ρg := by rw [hρgdef]; positivity
  have hβ0 : 0 ≤ 1 / (2 * max (Ctime' : ℝ) 1) / Cg := by positivity
  have hβ1 : 1 / (2 * max (Ctime' : ℝ) 1) / Cg ≤ 1 := by
    rw [div_le_one hCg0]
    exact hc1.trans hCg
  have hMC1 : 1 ≤ MC := by rw [hMCdef]; exact le_max_left _ _
  have hRr : 2500 * MC ≤ R n * rX ^ 2 := (div_le_iff₀ (by positivity)).1 hRbig
  rw [hMCdef] at hRr
  have hLc : 2 + 16 * Real.sqrt MC * max (1 / (2 * max (Ctime' : ℝ) 1) / Cg) 0 ≤
      L n - 2 * ρg := by
    have e1 : max (1 / (2 * max (Ctime' : ℝ) 1) / Cg) 0 ≤ 1 := max_le hβ1 zero_le_one
    have e2 : 0 ≤ Real.sqrt MC := Real.sqrt_nonneg _
    have e3 : 16 * Real.sqrt MC * max (1 / (2 * max (Ctime' : ℝ) 1) / Cg) 0 ≤
        16 * Real.sqrt MC := mul_le_of_le_one_right (by positivity) e1
    have e4 : 0 ≤ Dd + max Rad 0 := add_nonneg hDd.le (le_max_right _ _)
    linarith only [e3, e4, hLbig, hρg0, e2]
  rw [hMCdef] at hLc
  have hρL : L n - 2 * ρg + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Cg)) ≤ L n :=
    le_of_eq (by rw [hρgdef]; ring)
  have hC1c : 1 ≤ Cc := by rw [hCcdef]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hΛC : 6 * Cg ≤ Cc := by rw [hCcdef]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hρC : 2 * Cg ≤ localPropagationRadius C2' ^ 2 * Cc := by
    have e := le_max_right (max 1 (6 * Cg)) (2 * Cg / localPropagationRadius C2' ^ 2)
    rw [← hCcdef, div_le_iff₀ (by positivity)] at e
    linarith only [e, mul_comm Cc (localPropagationRadius C2' ^ 2)]
  have hbudP := pa_bud_P6HK (Ctime'.coe_nonneg) hCg0
  have hwseed2 : riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
      ((seedTrace n).point j'.castSucc h1 h2) w ≤
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) :=
    have e1 := le_max_right Rad 0
    have e2 := Real.sqrt_nonneg MC
    have e3 : L n / 4 + Dd ≤ L n / 2 := by linarith only [hLbig, hρg0, e1, hMC1, e2]
    budget_mono_P6HK e3 hwseed hsR.le
  have hrrx : Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w) ≤
      max Rad 0 / Real.sqrt (R n) :=
    (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left (le_max_right _ _) hsR (Real.sqrt_le_sqrt hRw))
  have hwlow : ∀ x : ((Kh n).stage j'.castSucc).Carrier, ∀ τ : ℝ,
      (v - τ) * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) ≤
        1 / (2 * max (Ctime' : ℝ) 1) →
      (aSeed n : ℝ) ≤ v - 1 / (2 * max (Ctime' : ℝ) 1) / Cg /
          (max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) / Cg) ∧
        (σ n : ℝ) - L n ^ 2 / R n ≤ v - 1 / (2 * max (Ctime' : ℝ) 1) / Cg /
          (max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) / Cg) ∧
        v - 1 / (2 * max (Ctime' : ℝ) 1) / Cg /
          (max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) / Cg) ≤ τ := by
    intro x τ hg
    have hMpos : 0 < max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) :=
      lt_of_lt_of_le (mul_pos hCg0 hRn) (le_max_left _ _)
    have hlow := pa_lower_P6HK (σ := (σ n : ℝ)) hRn (pa_q_ge_P6HK
      (X := ((Kh n).event j').incoming.flow.scalar v x) hCg0 hRn) hβ0 hβ1 hvσ1
      (le_max_right B 0)
    have hX1 : 1 ≤ max B 0 - σ₁ + 1 := hX1
    exact ⟨hwn.trans hlow, (pa_L_P6HK hRn hLX hX1).trans hlow, pa_window_P6HK hCg0 hMpos hg⟩
  have hcl' : ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
      (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)), ∀ τ : ℝ,
      (v - τ) * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) ≤
        1 / (2 * max (Ctime' : ℝ) 1) → τ ≤ v → (Kh n).time j'.castSucc < τ →
      riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
          ((seedTrace n).point j'.castSucc h1 h2) x ≤
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    intro x hx τ hg hτv hτ1
    obtain ⟨hav, hσL, hwτ⟩ := hwlow x τ hg
    have hlate : 1 ≤ R n * (v - 1 / (2 * max (Ctime' : ℝ) 1) / Cg /
        (max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) / Cg)) :=
      (hRa n).trans (mul_le_mul_of_nonneg_left hav hRn.le)
    have hwx : riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v) w x ≤
        ENNReal.ofReal (max Rad 0 / Real.sqrt (R n)) :=
      (le_of_lt hx).trans (ENNReal.ofReal_le_ofReal hrrx)
    have e1 := le_max_right Rad 0
    have e2 := Real.sqrt_nonneg MC
    have e3 : L n / 4 + Dd + max Rad 0 ≤ (L n - 2 * ρg) / 2 := by
      linarith only [hLbig, hρg0, hDd, e1, hMC1, e2]
    have e5 : 0 ≤ L n / 4 + Dd := by linarith only [hL0, hDd]
    have e4 : 0 ≤ (L n / 4 + Dd) / Real.sqrt (R n) := div_nonneg e5 hsR.le
    have hxG := budget_add_P6HK hsR.le e4 (div_nonneg e1 hsR.le) e3 hwseed hwx
    exact ObservedHistory.windowSeed_pointAnchor_C11WB hC2 (Kh n) (haT n) (hsT n) (has n)
      (hsmall n) (hclock n) (seedTrace n) (haP n) (hpin n) (y n) hRn (hgood n) j' h1 h2 hv2
      (pa_q_ge_P6HK hCg0 hRn) hCg0 (pa_CgL_P6HK hCg0) hbudP hC1c hΛC hρC hRr hLc hρL hav hvσ
      hσL hlate x ((riemannianEDistOf_triangle _ _ _ _).trans hxG) (pa_xv_P6HK hCg0) τ hwτ hτv
      hτ1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hRx
    exact (Kh n).witness_of_hgood_slab_Cg_P6LS3 (haT n) (hsT n) (has n) (seedTrace n) (y n) (R n)
      (L n) (hgood n) j' v hv1 hv2 hwin0.1 hvσ hwin0.2 h1 h2 x
      (seed_triangle_P6L3 (Kh n) j' v _ w x _ hRn hRw hL0 hRad hwseed2 hx) hRx.le
  · intro x hx v' hv' hBv' hRx hg ξ
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    exact (Kh n).gradient_of_hgood_slab_Cg_P6LS3 hC2 (haT n) (hsT n) (has n) (seedTrace n) (y n)
      (R n) (L n) (hgood n) j' v' hv'.1 (hv'.2.trans hv2) ha (hv'.2.le.trans hvσ) hLτ h1 h2 x
      (hcl' x hx v' hg hv'.2.le hv'.1) hRx.le ξ
  · intro τ _ hτv hτ1 hτ2 z hz hg
    obtain ⟨-, hσL, hwτ⟩ := hwlow z τ hg
    exact regionalKappa_of_closure_P6L3 (Kh n) (haT n) (hsT n) (has n) (seedTrace n) (y n) hRn hL0
      hκn hdσ j' {x | x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
          (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)) ∧
        (v - τ) * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) ≤
          1 / (2 * max (Ctime' : ℝ) 1)} τ v ((hroom n).trans (hσL.trans hwτ))
      (hvσ.trans (hsT n)) h1 h2
      (fun τ' haτ hτv' hτ1' _ x hx => hcl' x hx.1 τ'
        (cstar_guard_mono_P6HK (le_trans (mul_pos hCg0 hRn).le (le_max_left _ _)) hx.2 haτ)
        hτv' hτ1') τ le_rfl hτv hτ1 hτ2 z ⟨hz, hg⟩
  · intro x hx v' hv' hBv' hRx hg
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    exact (Kh n).deriv_of_hgood_slab_Cg_P6SD (haT n) (hsT n) (has n) (seedTrace n) (y n)
      (R n) (L n) (hgood n) j' v' hv'.1 (hv'.2.trans hv2) ha (hv'.2.le.trans hvσ) hLτ h1 h2 x
      (hcl' x hx v' hg hv'.2.le hv'.1) hRx.le
  · intro i first hf hij z hz Btr v' hv' hBv' hg hRx
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    obtain ⟨e1, -⟩ := window_P6L3 hRn hRw hvσ1 hBv' le_rfl hX1 hLX
    have hT₀v' : T₀ n ≤ v' := hT₀n.trans e1
    have hsj : i.succ ≤ j'.castSucc := Fin.le_def.mpr (by
      have := Fin.lt_def.mp hij
      simp only [Fin.val_succ, Fin.val_castSucc] at this ⊢
      omega)
    have hv'v : v' < v :=
      hv'.2.trans_le (((Kh n).time_strictMono.monotone hsj).trans hv1.le)
    have htv0 : 0 ≤ v - v' := sub_nonneg.mpr hv'v.le
    have h0 : (0 : ℝ) ≤ v' := ((Kh n).time_nonneg _).trans hv'.1.le
    have h0v : (0 : ℝ) ≤ v := h0.trans hv'v.le
    have hR1 : (1 : ℝ) ≤ R n := by
      have e1 := hRn1 n
      have e2 : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith only [e1, e2]
    have hL2 : (2 : ℝ) ≤ L n := (le_max_right _ _).trans hLX2
    have hLρ : 8 * localPropagationRadius C2' ≤ L n :=
      ((le_max_left _ _).trans (le_max_left _ _)).trans hLX2
    have hLc : 4 * (max Rad 0 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κs) + 4 ≤ L n :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans hLX2
    have hRle : (v - v') * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by
      have h3 := mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left hRn.le hCg).trans
        (le_max_left (Cg * R n) (((Kh n).event j').incoming.flow.scalar v z))) htv0
      exact h3.trans hg
    have hTv : v - v' ≤ 1 / R n := by
      rw [le_div_iff₀ hRn]
      exact hRle.trans hc1
    have hwinJ : ∀ s : ℝ, v - (L n / 2) ^ 2 / R n ≤ s → (σ n : ℝ) - L n ^ 2 / R n ≤ s := by
      intro s hs
      have hLa : -σ₁ + 1 ≤ L n := by linarith only [hLX, le_max_right B 0]
      have hσ0 : σ₁ < 0 := lt_of_le_of_lt h12 hσ₂
      have hsq := mul_le_mul hLa hLa (by linarith only [hσ0]) hL0
      have hA' : 0 ≤ σ₁ + 3 / 4 * L n ^ 2 := by
        nlinarith only [hsq, sq_nonneg (σ₁ - 1 / 3)]
      have hdiv : 0 ≤ (σ₁ + 3 / 4 * L n ^ 2) / R n := div_nonneg hA' hRn.le
      have heq : (σ₁ + 3 / 4 * L n ^ 2) / R n =
          σ₁ / R n + L n ^ 2 / R n - (L n / 2) ^ 2 / R n := by
        rw [add_div, mul_div_assoc, div_pow]
        ring
      linarith only [hvσ1, hdiv, heq, hs]
    have hrr : Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w) ≤
        max Rad 0 / Real.sqrt (R n) :=
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
        (div_le_div_of_nonneg_left (le_max_right _ _) (Real.sqrt_pos.2 hRn)
          (Real.sqrt_le_sqrt hRw))
    have hz' := riemannianBallOf_mono _ _ hrr hz
    have hQ1 : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (Q n) := le_max_left _ _
    have hQ0 : 0 < max ((n : ℝ) + 1) (Q n) := lt_of_lt_of_le (Nat.cast_add_one_pos n) hQ1
    subst hKh
    by_cases hA : max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event i).incoming.flow.scalar v' (Btr.point i.castSucc hf hij.le)
    · -- (A) 天花板以上：先验供给逐点
      exact hslabK n i _ v' ⟨hv'.1, lt_min hv'.2 (hv'v.trans hvtK)⟩
        ((le_max_right _ _).trans_lt hA)
    push Not at hA
    let vJ : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v, h0v, hvσ.trans (σ n).2.2⟩
    let vI : Icc (0 : ℝ) (K n).toHistory.horizon :=
      ⟨v', h0, (hv'v.le.trans hvσ).trans (σ n).2.2⟩
    have hvJσ : vJ ≤ σ n := hvσ
    have hvJT : vJ ≤ Tn n := hvJσ.trans (hsT n)
    have hvJa : aSeed n ≤ vJ := hwin0.1
    have hvIJ : vI ≤ vJ := hv'v.le
    have hvIa : aSeed n ≤ vI := ha
    have hactJ : (K n).toHistory.activeStage vJ = j'.castSucc :=
      (K n).toHistory.activeStage_eq_of_slab_P6L3 j' vJ hv1.le hv2
    have hik : i.val < ((K n).prefixAt j'.castSucc).eventCount := by
      have := Fin.lt_def.mp hij
      simp only [Fin.val_castSucc] at this
      exact this
    let ip : Fin ((K n).prefixAt j'.castSucc).eventCount := ⟨i.val, hik⟩
    have hfi : first.val < ((K n).prefixAt j'.castSucc).eventCount + 1 := by
      have := Fin.le_def.mp hf
      simp only [Fin.val_castSucc] at this
      omega
    let fp : Fin (((K n).prefixAt j'.castSucc).eventCount + 1) := ⟨first.val, hfi⟩
    have hfp : fp ≤ ip.castSucc := Fin.le_def.mpr (Fin.le_def.mp hf)
    let Btrp := (K n).prefixTraceOfHistory_P6SD j'.castSucc (first := fp) Btr
    by_cases hB : 2 * max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event j').incoming.flow.scalar v z
    · -- (B) 不可能：trace 下界（clipped reciprocal）
      exfalso
      have hRz : (v - v') * ((K n).toHistory.event j').incoming.flow.scalar v z ≤
          1 / (2 * max (Ctime' : ℝ) 1) :=
        (mul_le_mul_of_nonneg_left (le_max_right _ _) htv0).trans hg
      have htime : (Ctime' : ℝ) * ((K n).toHistory.event j').incoming.flow.scalar vJ z *
          ((vJ : ℝ) - vI) ≤ 1 / 2 := by
        change (Ctime' : ℝ) * ((K n).toHistory.event j').incoming.flow.scalar v z * (v - v') ≤
          1 / 2
        have h1' := mul_le_mul_of_nonneg_left hRz Ctime'.coe_nonneg
        calc (Ctime' : ℝ) * ((K n).toHistory.event j').incoming.flow.scalar v z * (v - v')
            = (Ctime' : ℝ) * ((v - v') *
              ((K n).toHistory.event j').incoming.flow.scalar v z) := by ring
          _ ≤ 1 / 2 := h1'.trans hCc
      have hgt := (K n).scalar_gt_of_slabs_prefixT_A6K hQ0
        (fun e => OrientedThreeStage.IncomingSlab.derivativeBoundBefore_of_threshold_le _
          (le_max_right _ _) (hslabK n e)) j' vJ hactJ ip fp hfp z Btrp vI
        hv'.1 hv'.2 hvIJ hvtK hB htime
      exact absurd hgt (not_lt.mpr hA)
    push Not at hB
    -- (C) 天花板以下：CXJD stay 以 (v, w, L/2) 重新锚定 + hgood
    obtain ⟨Qb, hQbdef⟩ : ∃ Qb : ℝ, Qb = max (max
        (((K n).toHistory.event j').incoming.flow.scalar v z / R n) Cg) 1 := ⟨_, rfl⟩
    obtain ⟨Tt, hTdef⟩ : ∃ Tt : ℝ, Tt = 1 / (2 * max (Ctime' : ℝ) 1) / Qb := ⟨_, rfl⟩
    have hQb1 : (1 : ℝ) ≤ Qb := by rw [hQbdef]; exact le_max_right _ _
    have hQbM : Qb * R n ≤
        max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v z) := by
      have hCgR : R n ≤ Cg * R n := le_mul_of_one_le_left hRn.le hCg
      have hle : Qb ≤ max (Cg * R n)
          (((K n).toHistory.event j').incoming.flow.scalar v z) / R n := by
        rw [hQbdef]
        refine max_le (max_le ?_ ?_) ?_
        · exact div_le_div_of_nonneg_right (le_max_right _ _) hRn.le
        · rw [le_div_iff₀ hRn]
          exact le_max_left _ _
        · rw [le_div_iff₀ hRn, one_mul]
          exact hCgR.trans (le_max_left _ _)
      calc Qb * R n ≤ max (Cg * R n)
            (((K n).toHistory.event j').incoming.flow.scalar v z) / R n * R n :=
          mul_le_mul_of_nonneg_right hle hRn.le
        _ = _ := div_mul_cancel₀ _ hRn.ne'
    have hQbQ : Qb * R n ≤ 2 * max ((n : ℝ) + 1) (Q n) :=
      hQbM.trans (max_le (by linarith only [hRx, hA, hQ0]) hB)
    have hacc1 : (p n).modelAccuracy ≤ min ε₀ (1 / 2) := (hacc n).trans hacn
    have hDm' : StandardCap.transitionEnd + 10 < (p n).modelRadius := by
      linarith only [hrad n, hTEn]
    have hncK := hnc0 (H := (K n).toHistory) (q := p n) (T₀ := T₀ n) (recordsK n)
      (hacc1.trans (min_le_left _ _)) (le_trans (by omega) (hord n)) (hcanK n)
    have hscale' : ∀ (e : Fin (K n).eventCount) (he : T₀ n ≤ (K n).time e.succ) b,
        (vI : ℝ) < (K n).toHistory.time e.succ → e.succ ≤ (K n).toHistory.activeStage vJ →
        2 * max (3 / rX ^ 2) (2 * (Qb * R n)) < ((recordsK n e he).static b).neck.scale := by
      intro e he b' _ _
      have hS := hscaleK n e he b'
      have h8 : 8 * max ((n : ℝ) + 1) (Q n) < ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) := by
        nlinarith only [h9, hQ0]
      have hn1 : (1 : ℝ) ≤ max ((n : ℝ) + 1) (Q n) :=
        le_trans (by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hQ1
      have hnQ : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) :=
        le_mul_of_one_le_right (Nat.cast_add_one_pos n).le hn1
      have h6 : 6 / rX ^ 2 < ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) := by
        linarith only [hnQ, hr6]
      have h63 : 2 * (3 / rX ^ 2) = 6 / rX ^ 2 := by ring
      have hmx : max (3 / rX ^ 2) (2 * (Qb * R n)) <
          ((recordsK n e he).static b').neck.scale / 2 :=
        max_lt (by linarith only [h6, hS, h63]) (by linarith only [hQbQ, h8, hS])
      linarith only [hmx]
    have hRa' : 1 ≤ R n * vI := by
      have := mul_le_mul_of_nonneg_left ha hRn.le
      change 1 ≤ R n * v'
      linarith only [this, hRa n]
    have haL : (vJ : ℝ) - (L n / 2) ^ 2 / R n ≤ vI := by
      have h1L : 1 / R n ≤ (L n / 2) ^ 2 / R n :=
        div_le_div_of_nonneg_right (by nlinarith only [hL2]) hRn.le
      change v - (L n / 2) ^ 2 / R n ≤ v'
      linarith only [h1L, hTv]
    let w' : ((K n).toHistory.stageAt vJ).Carrier :=
      cast (congrArg (fun m => ((K n).stage m).Carrier) hactJ.symm) w
    have hww : HEq w' w := cast_heq _ _
    have hwJ : riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage vJ) vJ)
          ((seedTrace n).point ((K n).toHistory.activeStage vJ)
            ((K n).toHistory.activeStage_mono hvJa) ((K n).toHistory.activeStage_mono hvJT)) w' ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) := by
      have hs := point_heq_of_eq_P6M2 (seedTrace n) hactJ ((K n).toHistory.activeStage_mono hvJa)
        ((K n).toHistory.activeStage_mono hvJT) h1 h2
      exact (edist_stage_eq_P6L2 j' hactJ v _ w' _ w hs hww).trans_le hwseed2
    have hc' : 0 ≤ L n / 2 / Real.sqrt (R n) :=
      div_nonneg (div_nonneg hL0 (by norm_num)) (Real.sqrt_nonneg _)
    have hbud : riemannianEDistOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage vJ) vJ)
          ((seedTrace n).point ((K n).toHistory.activeStage vJ)
            ((K n).toHistory.activeStage_mono hvJa) ((K n).toHistory.activeStage_mono hvJT)) w' +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) := by
      refine (add_le_add hwJ le_rfl).trans_eq ?_
      rw [add_assoc, ← ENNReal.ofReal_add hc' hc']
      congr 2
      ring
    have hdfn := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hdσ)
    have hdw := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hdfn, ENNReal.ofReal_ne_top⟩) hwJ
    obtain ⟨hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ := cstar_numerics_P6SP (Qb := Qb) (R := R n)
      (Rad := max Rad 0) (L := L n / 2) hrX hρ hc0 hQb1 hR1 hκdef (by linarith only [hLρ])
      (by linarith only [hLc])
    have hTeq : Tt / R n = 1 / (2 * max (Ctime' : ℝ) 1) / Qb / R n := by rw [hTdef]
    rw [← hTeq] at hnum
    have hstay := stay_cstar_prefix_sepRho_P6SB2 hC2 hCg (K n) j' hv1 hv2 (σ := vJ) rfl (haT n)
      (hsmall n) (hclock n) (seedTrace n) (haP n) (hpin n) hvJT hvJa w' w hww (L n / 2) hRn
      (fun v'' hav'' hvs'' hw'' z'' hd'' hR'' => hgood n v'' hav'' (hvs''.trans hvJσ)
        (hwinJ _ hw'') z'' (hd''.trans hbud) hR'')
      ip fp hfp z hz' Btrp vI hv'.1 hv'.2 hvIa hvIJ haL hRa' hQbdef hTdef hg hℓ hKℓ hℓr hKr hKC
      hℓρ hρL ((hT₀X n).trans ha) (hOldX n) (recordsK n) hT₀v' (hcanK n)
      (hacc1.trans (min_le_right _ _)) hDm' hncK hscale' (by linarith only [hL0]) hdw hnum
    exact ObservedHistory.slabDeriv_prefix_of_hgood_stay_P6SP (K n) j'.castSucc (haT n) (hsT n)
      (has n) (seedTrace n) (y n) (R n) (L n) (hgood n) ip
      (Btrp.point ip.castSucc hfp (Fin.le_last _)) vI hvIa (hvIJ.trans hvJσ) hv'.1 hv'.2 hLτ
      (fun x hx => (hstay x hx).trans hbud) hRx

/-- **`hsliceR_lateHI_core_localG_P6HK` 的截断孪生（`_A6K`）**：见文件头。 -/
theorem ObservedHistory.hsliceR_lateHI_core_localG_A6K
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ tK : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n (j₀ : Fin (K n).eventCount),
      ((K n).toHistory.event j₀).incoming.DerivativeBoundBefore Ctime (Q n)
        (min ((K n).time j₀.succ) (tK n)))
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n)
    (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
 :
    ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ Rad Bw : ℝ, 0 ≤ QB ∧
      Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
      ∀ l : Filter ℕ, l ≤ atTop → ∀ σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw : ℝ, 0 < Dw →
      (∀ᶠ n in l,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) + σ₁ / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      (∀ᶠ n in l,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((L n / 4 + Dd) / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v x →
            ∃ W : SpatialCanonicalWitness (((Kh n).event j').incoming.flow.base.metric v)
              ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - Bw / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential ((Kh n).event j').incoming.flow v' x ξ| ≤
                Cgrad * ((Kh n).event j').incoming.flow.scalar v' x *
                  Real.sqrt (((Kh n).event j').incoming.flow.scalar v' x) *
                  Real.sqrt ((((Kh n).event j').incoming.flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (Kh n).horizon),
            v - Bw / ((Kh n).event j').incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (Kh n).time j'.castSucc < τ → (τ : ℝ) < (Kh n).time j'.succ →
            ∀ z ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                  (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            (v - τ) * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                  ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                  (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - Bw / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            |derivWithin (fun s => ((Kh n).event j').incoming.flow.scalar s x) (Iic v') v'| ≤
              Ctime * ((Kh n).event j').incoming.flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (Kh n).eventCount) (first : Fin ((Kh n).eventCount + 1))
              (hf : first ≤ i.castSucc) (hij : i.castSucc < j'.castSucc),
            ∀ z ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (Kh n) first j'.castSucc (hf.trans hij.le) z,
            ∀ v' ∈ Ioo ((Kh n).time i.castSucc) ((Kh n).time i.succ),
            v - Bw / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            Cg * R n < ((Kh n).event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf hij.le) →
            |derivWithin (fun s => ((Kh n).event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf hij.le)) (Iic v') v'| ≤
              Ctime * ((Kh n).event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf hij.le) ^ 2)) →
      ∀ᶠ n in l,
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) + σ₁ / R n ≤ v →
        (v : ℝ) ≤ σ n + σ₂ / R n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₁,
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
        ∃ CWP : ((Kh n).stage ((Kh n).activeStage v)).Carrier → Prop,
          (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
            R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w → ∀ x,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v) w x <
              ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) x ≤
              QB * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w) ∧
          (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
            ∃ (Ξ : standardCapWindow D₂ → ((Kh n).stage ((Kh n).activeStage v)).Carrier)
              (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
              Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
              ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                  metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                      ((Kh n).stageMetric ((Kh n).activeStage v) v)) Ξ hΞ)
                    ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                    (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃) := by
  intro A Dd hA hDd
  obtain ⟨Cbirth, hCbirth, hP⟩ :=
    RetainedCoreHistory.slice_dichotomy_late_Cg_window_localG_P6HK hεle κ C1 C2 hκ Ctime Cgrad Cg
      (by linarith) hphi hη₃ hLc
  obtain ⟨QB, Dcap, D₂, hQB, hD₂, Λ, Rad, Bw, Rmin, ζmin, δ₀, m₀, hΛ, -, hζ, hδ₀, hmain⟩ :=
    hP A Dd hA hDd
  refine ⟨QB, Dcap, D₂, Rad, Bw, hQB, hD₂, fun l hl σ₁ σ₂ h12 hσ₂ Dw hDw hdl hUl => ?_⟩
  subst hKh
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hR : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRn1 hnat
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ δ₀ := h0.eventually (ge_mem_nhds hδ₀)
  have hacc' : ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζmin :=
    (h0.eventually (ge_mem_nhds hζ)).mono fun n hn => (hacc n).trans hn
  have hrad' : ∀ᶠ n in atTop, Rmin ≤ (p n).modelRadius :=
    (hnat.eventually_ge_atTop Rmin).mono fun n hn => hn.trans (hrad n)
  have hord' : ∀ᶠ n in atTop, m₀ ≤ (p n).modelOrder :=
    (eventually_ge_atTop m₀).mono fun n hn => le_trans (by omega) (hord n)
  have hbirth : ∀ᶠ n : ℕ in atTop, ∀ i hi b,
      max ((n : ℝ) + 1) (Q n) ≤ Cbirth * ((recordsK n i hi).static b).neck.scale ∧
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale := by
    filter_upwards [hnat.eventually_ge_atTop (1 / Cbirth), hbirthA] with n hn1 hbA i hi b
    have hs := hscaleK n i hi b
    have hC1 : 1 ≤ ((n : ℝ) + 1) * Cbirth := (div_le_iff₀ hCbirth).1 hn1
    have hq : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (Q n) := le_max_left _ _
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    refine ⟨?_, hbA i hi b⟩
    calc max ((n : ℝ) + 1) (Q n) = max ((n : ℝ) + 1) (Q n) * 1 := by ring
      _ ≤ max ((n : ℝ) + 1) (Q n) * (((n : ℝ) + 1) * Cbirth) :=
        mul_le_mul_of_nonneg_left hC1 (by linarith)
      _ = ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) * Cbirth := by ring
      _ ≤ ((recordsK n i hi).static b).neck.scale * Cbirth :=
        mul_le_mul_of_nonneg_right hs hCbirth.le
      _ = Cbirth * ((recordsK n i hi).static b).neck.scale := by ring
  have hT1 : 0 < -σ₁ := by linarith
  have hRσ : ∀ᶠ n in atTop, Λ - σ₁ ≤ R n * σ n := by
    filter_upwards [hwin (max (Λ - σ₁) 1) (lt_max_of_lt_right one_pos)] with n hn
    have ha0 : (0 : ℝ) ≤ aSeed n := (aSeed n).2.1
    have hRn := hRpos n
    have h1 : max (Λ - σ₁) 1 / R n ≤ σ n := by linarith
    rw [div_le_iff₀ hRn] at h1
    nlinarith [le_max_left (Λ - σ₁) 1]
  filter_upwards [Filter.Eventually.filter_mono hl hδ, Filter.Eventually.filter_mono hl hrad',
    Filter.Eventually.filter_mono hl hord', Filter.Eventually.filter_mono hl hacc',
    Filter.Eventually.filter_mono hl hbirth,
    Filter.Eventually.filter_mono hl (hR.eventually_ge_atTop Λ),
    Filter.Eventually.filter_mono hl hRσ,
    Filter.Eventually.filter_mono hl (hρV.eventually_ge_atTop Λ),
    Filter.Eventually.filter_mono hl (hL.eventually_ge_atTop (4 * Dd)),
    Filter.Eventually.filter_mono hl (hwin (-σ₁) hT1),
    Filter.Eventually.filter_mono hl (hT₀ (Bw - σ₁)), hdl, hUl]
    with n e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
  intro x₁ hx₁ v hvt hv1 hv2 hage tr₁ _
  have hvwin : (σ n : ℝ) - -σ₁ / R n ≤ v := by
    rw [neg_div, sub_neg_eq_add]
    exact hv1
  have hav : aSeed n ≤ v := show (aSeed n : ℝ) ≤ v from e10.trans hvwin
  have hT₀v : T₀ n ≤ v - Bw / R n := by
    have : (Bw - σ₁) / R n = Bw / R n - σ₁ / R n := sub_div _ _ _
    rw [this] at e11
    linarith
  have hlast : (K n).toHistory.activeStage v ≠ Fin.last (K n).eventCount := by
    intro h
    have h1 := ObservedHistory.activeStage_time_le (K n).toHistory v
    rw [h] at h1
    have h2 : (K n).time (j n).succ ≤ (K n).time (Fin.last (K n).eventCount) :=
      (K n).toHistory.time_strictMono.monotone (Fin.le_last _)
    have h3 : (v : ℝ) ≤ t n := by rw [← hσ n]; exact hvt
    have h4 := htj n
    change (K n).time (Fin.last (K n).eventCount) ≤ (v : ℝ) at h1
    linarith
  obtain ⟨j', hj'⟩ := Fin.exists_castSucc_eq.mpr hlast
  have hvtK : (v : ℝ) ≤ tK n :=
    (show (v : ℝ) ≤ Tn n from hvt.trans (hsT n)).trans (hTnK n)
  have ht1 : (K n).time j'.castSucc < v := by
    change (K n).toHistory.time j'.castSucc < v
    rw [hj']
    exact hage
  have ht2 : (v : ℝ) < (K n).time j'.succ := by
    have hlt : ((K n).toHistory.activeStage v : ℕ) < (K n).toHistory.eventCount := by
      rw [← hj']
      exact j'.isLt
    have h := (K n).toHistory.activeStage_before_next v hlt
    have heq : (⟨((K n).toHistory.activeStage v : ℕ) + 1, by omega⟩ :
        Fin ((K n).toHistory.eventCount + 1)) = j'.succ := by
      apply Fin.ext
      simp only [← hj', Fin.val_castSucc, Fin.val_succ]
    rwa [heq] at h
  have h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc := by
    rw [hj']
    exact (K n).toHistory.activeStage_mono hav
  have h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n) := by
    rw [hj']
    exact (K n).toHistory.activeStage_mono (hvt.trans (hsT n))
  have hs := point_heq_of_eq_P6M2 (seedTrace n) hj'.symm ((K n).toHistory.activeStage_mono hav)
    ((K n).toHistory.activeStage_mono (hvt.trans (hsT n))) h1 h2
  have hfn : (K n).toHistory.activeStage v ≤ j'.castSucc := le_of_eq hj'.symm
  have hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n) :=
    (le_of_eq hj').trans ((K n).toHistory.activeStage_mono hvt)
  have hzj := point_heq_of_eq_P6M2 tr₁ hj'.symm le_rfl ((K n).toHistory.activeStage_mono hvt)
    (hfn.trans le_rfl) hjσ
  have hΛv : Λ ≤ R n * v := by
    have hRv : R n * ((σ n : ℝ) + σ₁ / R n) ≤ R n * v :=
      mul_le_mul_of_nonneg_left hv1 (hRpos n).le
    have hRne := (hRpos n).ne'
    have heq : R n * ((σ n : ℝ) + σ₁ / R n) = R n * σ n + σ₁ := by
      field_simp
    linarith
  have hL0 : 0 ≤ L n / 4 / Real.sqrt (R n) := by
    have : 0 < Dd := hDd
    have : 0 ≤ L n := by linarith
    positivity
  refine hmain (K n) (T₀ n) (recordsK n) (hcanK n) e2 e3 e4 (hpinchK0 n) (recordsF n)
    (1 / ((n : ℝ) + 1)) (hδF n) e1 (max ((n : ℝ) + 1) (Q n)) (a₀ n)
    (lt_of_lt_of_le (by positivity) (le_max_left _ _)) (fun x => (hHI n x).1)
    (fun x => (hHI n x).2) e5 j'
    (fun i hi y' t' ht hR' => hslabK n i y' t' ⟨ht.1, lt_min ht.2 (ht.2.trans_le
      ((time_succ_le_of_castSucc_lt_A6K (K n) hi).trans (ht1.le.trans hvtK)))⟩
      ((le_max_right _ _).trans_lt hR')) v ht1 ht2
    (fun y' t' ht hR' => hslabK n j' y' t' ⟨ht.1, lt_min (ht.2.trans ht2) (ht.2.trans_le hvtK)⟩
      ((le_max_right _ _).trans_lt hR'))
    (R n) (ρV n) (hRpos n) e6 hΛv e8
    hT₀v _ hj'.symm
    (tr₁.point _ le_rfl _) _ _ hs _ (e12 x₁ hx₁ v hav hvt hv1 tr₁)
    ((tr₁.restrictFirst hfn hjσ).point j'.castSucc le_rfl hjσ) hzj ?_
  intro w hw hzw hRw
  refine (fun H => ?hU) (e13 j' v ht1 ht2 hv1 hv2 x₁ hx₁ hjσ (tr₁.restrictFirst hfn hjσ) h1 h2 w
    (hw.trans ?hd) hzw hRw)
  case hU =>
    obtain ⟨u1, u2, u3, u4, u5⟩ := H
    exact ⟨u1, u2, u3, u4, fun i first hf z hz Btr v' hv' hBv' hg hR =>
      u5 (Fin.castLE (Nat.le_of_lt_succ j'.castSucc.isLt) i)
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j'.castSucc.isLt)) first)
        (Fin.le_def.mpr (Fin.le_def.mp hf)) (Fin.lt_def.mpr i.isLt) z hz
        ((K n).backwardPointTraceOfPrefix j'.castSucc Btr) v' hv' hBv' hg hR⟩
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  rw [← ENNReal.ofReal_add hL0 (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 (hRpos n)
  rw [← add_div]

/-- **`hsliceRC_lateHI_of_slice_data_localG_P6HK` 的截断孪生（`_A6K`）**：见文件头。 -/
theorem ObservedHistory.hsliceRC_lateHI_of_slice_data_localG_A6K
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ tK : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n (j₀ : Fin (K n).eventCount),
      ((K n).toHistory.event j₀).incoming.DerivativeBoundBefore Ctime (Q n)
        (min ((K n).time j₀.succ) (tK n)))
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n)
    (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hUVC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((L n / 4 + Dd) / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v x →
            ∃ W : SpatialCanonicalWitness (((Kh n).event j').incoming.flow.base.metric v)
              ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential ((Kh n).event j').incoming.flow v' x ξ| ≤
                Cgrad * ((Kh n).event j').incoming.flow.scalar v' x *
                  Real.sqrt (((Kh n).event j').incoming.flow.scalar v' x) *
                  Real.sqrt ((((Kh n).event j').incoming.flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (Kh n).horizon),
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (Kh n).time j'.castSucc < τ → (τ : ℝ) < (Kh n).time j'.succ →
            ∀ z ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                  (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            (v - τ) * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                  ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                  (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            |derivWithin (fun s => ((Kh n).event j').incoming.flow.scalar s x) (Iic v') v'| ≤
              Ctime * ((Kh n).event j').incoming.flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (Kh n).eventCount) (first : Fin ((Kh n).eventCount + 1))
              (hf : first ≤ i.castSucc) (hij : i.castSucc < j'.castSucc),
            ∀ z ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (Kh n) first j'.castSucc (hf.trans hij.le) z,
            ∀ v' ∈ Ioo ((Kh n).time i.castSucc) ((Kh n).time i.succ),
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            Cg * R n < ((Kh n).event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf hij.le) →
            |derivWithin (fun s => ((Kh n).event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf hij.le)) (Iic v') v'| ≤
              Ctime * ((Kh n).event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf hij.le) ^ 2)) :
    ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
      Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw : ℝ, 0 < Dw →
      ∀ T Kc : ℝ, -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) + σ₁ / R n ≤ v →
        (v : ℝ) ≤ σ n + σ₂ / R n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₁,
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
        ∃ CWP : ((Kh n).stage ((Kh n).activeStage v)).Carrier → Prop,
          (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
            R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w → ∀ x,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v) w x <
              ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) x ≤
              QB * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w) ∧
          (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
            ∃ (Ξ : standardCapWindow D₂ → ((Kh n).stage ((Kh n).activeStage v)).Carrier)
              (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
              Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
              ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                  metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                      ((Kh n).stageMetric ((Kh n).activeStage v) v)) Ξ hΞ)
                    ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                    (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃) := by
  intro A Dd hA hDd
  obtain ⟨QB, Dcap, D₂, Rad, Bw, hQB, hD₂, hcore⟩ :=
    ObservedHistory.hsliceR_lateHI_core_localG_A6K hεle hκ hphi hCg hη₃ hLc htj recordsF hHI hcanK
      hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK Kh hKh σ y R hσ hRpos hRn1 hT₀ Tn aSeed haT
      hsT hTnK
      has pT
      seedTrace L hL hwin ρV hρV A Dd hA hDd
  refine ⟨QB, Dcap, D₂, hQB, hD₂, fun φ hφ σ₁ σ₂ h12 hσ₂ Dw hDw T Kc hT hKc htr => ?_⟩
  refine hcore (map φ atTop) hφ.tendsto_atTop σ₁ σ₂ h12 hσ₂ Dw hDw ?_
    (hUVC Rad Bw σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr)
  filter_upwards [hdistQC φ hφ Dw T Kc hDw (by linarith) hKc htr] with n hn
  intro x hx v hav hvs hv tr
  refine hn x hx v hav hvs ?_ tr
  have h1 : -T / R n ≤ σ₁ / R n := div_le_div_of_nonneg_right (by linarith) (hRpos n).le
  rw [sub_eq_add_neg, ← neg_div]
  linarith

/-- **`hbcadC_lateHI_of_slice_data_localG_P6HK` 的截断孪生（`_A6K`）**：见文件头。 -/
theorem ObservedHistory.hbcadC_lateHI_of_slice_data_localG_A6K
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cg : ℝ} (hCg : 1 ≤ Cg)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ tK : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n (j₀ : Fin (K n).eventCount),
      ((K n).toHistory.event j₀).incoming.DerivativeBoundBefore Ctime (Q n)
        (min ((K n).time j₀.succ) (tK n)))
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n)
    (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hUVC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((L n / 4 + Dd) / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v x →
            ∃ W : SpatialCanonicalWitness (((Kh n).event j').incoming.flow.base.metric v)
              ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential ((Kh n).event j').incoming.flow v' x ξ| ≤
                Cgrad * ((Kh n).event j').incoming.flow.scalar v' x *
                  Real.sqrt (((Kh n).event j').incoming.flow.scalar v' x) *
                  Real.sqrt ((((Kh n).event j').incoming.flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (Kh n).horizon),
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (Kh n).time j'.castSucc < τ → (τ : ℝ) < (Kh n).time j'.succ →
            ∀ z ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                  (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            (v - τ) * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                  ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                  (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            |derivWithin (fun s => ((Kh n).event j').incoming.flow.scalar s x) (Iic v') v'| ≤
              Ctime * ((Kh n).event j').incoming.flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (Kh n).eventCount) (first : Fin ((Kh n).eventCount + 1))
              (hf : first ≤ i.castSucc) (hij : i.castSucc < j'.castSucc),
            ∀ z ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (Kh n) first j'.castSucc (hf.trans hij.le) z,
            ∀ v' ∈ Ioo ((Kh n).time i.castSucc) ((Kh n).time i.succ),
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            Cg * R n < ((Kh n).event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf hij.le) →
            |derivWithin (fun s => ((Kh n).event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf hij.le)) (Iic v') v'| ≤
              Ctime * ((Kh n).event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf hij.le) ^ 2)) :
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (K * R n)) →
      ∀ᶠ n in map φ atTop,
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
      ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₁)
        (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₂),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤
          C * R n := by
  obtain ⟨η₃, Cup, Lc, hη₃, hCup, hLc, hB⟩ :=
    ObservedHistory.hbcadC_of_slice_dichotomy_open_P6L3.{u}
  have hsl := ObservedHistory.hsliceRC_lateHI_of_slice_data_localG_A6K hεle hκ hphi hCg hη₃ hLc htj
    recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK Kh hKh σ y R hσ hRpos hRn1
    hT₀ Tn aSeed haT
    hsT hTnK has pT seedTrace L hL hwin ρV hρV hdistQC hUVC
  have hR1 : ∀ᶠ n in atTop, 1 ≤ R n := Eventually.of_forall fun n => by
    have h1 := hRn1 n
    have h3 : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hlast : ∀ n, (σ n : ℝ) < (Kh n).time (Fin.last (Kh n).eventCount) := by
    subst hKh
    intro n
    rw [hσ n]
    exact (htj n).trans_le ((K n).toHistory.time_strictMono.monotone (Fin.le_last _))
  exact hB Kh σ y R hRpos hR1 hlast hsl

/-- **`hbcadC_of_guarded_P6HK` 的截断孪生（`_A6K`）**：见文件头。 -/
theorem ObservedHistory.hbcadC_of_guarded_A6K
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime' : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cg : ℝ} (hCg : 1 ≤ Cg)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ tK : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n (j₀ : Fin (K n).eventCount),
      ((K n).toHistory.event j₀).incoming.DerivativeBoundBefore Ctime' (Q n)
        (min ((K n).time j₀.succ) (tK n)))
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n)
    (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hC2 : 0 ≤ C2) {Aκ : ℝ} (r : ℕ → ℝ)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl ε C1 C2 Ctime' v z)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
      (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))
    {rX : ℝ} (hrX : 0 < rX)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) rX)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - rX ^ 2)
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s) (aP n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    :
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (K * R n)) →
      ∀ᶠ n in map φ atTop,
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
      ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₁)
        (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₂),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤
          C * R n := by
  have hUVC := ObservedHistory.hUVC_of_selection_Cg_guarded_A6K (Ctime' := Ctime') (Cg := Cg) hC2
    Kh Tn aSeed σ haT hsT has pT seedTrace y R L r ρV hRpos hL hgood hwin hroom hdistσ hκR
    hKh hCg hRn1 hcanK hacc hrad hord hscaleK hslabK hTnK hT₀ hrX hsmall hclock aP haP hpin hRa T₀X
    hT₀X hOldX
  exact ObservedHistory.hbcadC_lateHI_of_slice_data_localG_A6K hεle hκ hphi hCg htj recordsF hHI
    hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK Kh hKh σ y R hσ hRpos hRn1 hT₀ Tn aSeed
    haT hsT hTnK has pT seedTrace L hL hwin ρV hρV hdistQC hUVC

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
