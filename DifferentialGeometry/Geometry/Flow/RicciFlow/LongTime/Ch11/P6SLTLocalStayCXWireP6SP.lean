import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SLTLocalStayCXP6SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelsNoJ10P6JG3

/-!
# c⋆ 版 `hstayLoc` 的 prefix 帧逐点接线（O-CH11-SLTPROD G3b，后缀 `_P6SP`）

G3 `stay_cstar_of_firstExit_P6SP`（CXJD 跨 slab first-exit，逐点 `Cball := R_σ(z)/R`）是 `H` 帧、整窗 trace
形。G1 `hstayLoc`（c⋆ 档，`hslabsLoc_cstar_of_hgood_P6SP` 的 binder）是 kernel 帧逐点形：起点 `z` 在
incoming 帧、trace 是 `K.prefixAt j.castSucc` 的 prefix trace、guard 用 incoming 标量。本文件给逐点接线：
* `exists_trace_transport_P6SP` / `ofPrefix_point_heq_P6SP`（PROVED，trace 帧搬运）；
* `ObservedHistory.stay_cstar_prefix_of_firstExit_P6SP`（PROVED ⇐ CXJD 结构输入 + 数值）：G1 `hstayLoc`
  （c⋆ 档）的逐点结论。
序列层（`∀ Rad B, ∀ᶠ n` 包装 + eventual 数值 `ℓ`、`K`、`hnum`、`hρL`）未做（见 state HANDOVER）。
**不声称 J10 已去。**
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- trace 末端指标 / 端点的搬运（`_P6SP`，PROVED）：`l = l'`、`HEq x x'` ⇒ 同点 trace。 -/
theorem exists_trace_transport_P6SP {H : ObservedHistory.{u}} {f l l' : Fin (H.eventCount + 1)}
    {hle : f ≤ l} (hle' : f ≤ l') {x : (H.stage l).Carrier} (x' : (H.stage l').Carrier)
    (hl : l = l') (hx : HEq x x') (A : BackwardPointTrace H f l hle x) :
    ∃ A' : BackwardPointTrace H f l' hle' x', ∀ (m : Fin (H.eventCount + 1)) (h1 : f ≤ m)
      (h2 : m ≤ l) (h2' : m ≤ l'), A'.point m h1 h2' = A.point m h1 h2 := by
  subst hl
  obtain rfl := eq_of_heq hx
  exact ⟨A, fun _ _ _ _ => rfl⟩

/-- prefix trace 搬到 `K` 帧后的点与原 prefix 点 HEq（`_P6SP`，PROVED，指标值相等即可）。 -/
theorem ofPrefix_point_heq_P6SP (K : RetainedCoreHistory.{u}) (k : Fin (K.eventCount + 1))
    {first last : Fin ((K.prefixAt k).eventCount + 1)} {hle : first ≤ last}
    {x : ((K.prefixAt k).stage last).Carrier}
    (Btr : BackwardPointTrace (K.prefixAt k).toHistory first last hle x)
    (m : Fin ((K.prefixAt k).eventCount + 1)) (hm1 : first ≤ m) (hm2 : m ≤ last)
    (m' : Fin (K.eventCount + 1)) (hm' : m'.val = m.val)
    (h1 : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first ≤ m')
    (h2 : m' ≤ Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) last) :
    HEq ((K.backwardPointTraceOfPrefix k Btr).point m' h1 h2) (Btr.point m hm1 hm2) := by
  obtain ⟨mv, hmv⟩ := m
  obtain ⟨mv', hmv'⟩ := m'
  simp only at hm'
  subst hm'
  rfl

/-- **G3b：prefix 帧逐点 c⋆ stay（`_P6SP`，PROVED ⇐ CXJD 结构输入 + 数值）**：anchor / kernel 帧
（`K.prefixAt j.castSucc` 的 prefix trace `Btr`，起点 `z ∈ B(yG, D/√R)`，前 slab `i` 内时刻 `v'`）：
c⋆ guard `(t − v')·max(Cg·R, R_G(t, z)) ≤ c⋆`（incoming 标量，= G1 `hstayLoc` 的 c⋆ 档 guard）⇒ 对与
`Btr.point i.castSucc` HEq 的 `stageAt v'` 点 `x`，`d_{v'}(seed(v'), x) ≤ d_σ(seed, y) + L/√R`（= G1
`hstayLoc` 的逐点结论）。证明：prefix trace → `K` trace（`backwardPointTraceOfPrefix`）→ `restrictFirst` 到
`activeStage v'` → 末端搬到 `activeStage σ`；incoming ↔ stage 换算（JG3 helper）；喂 G3
`stay_cstar_of_firstExit_P6SP`（`a := v'`）。`hprotC` 对所有以 `z` 为端点的 trace 量化。 -/
theorem ObservedHistory.stay_cstar_prefix_of_firstExit_P6SP {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg Qb T Kc ℓ D : ℝ} (hC2 : 0 ≤ C2') (hCg : 1 ≤ Cg) (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) {t : ℝ} (hjt : K.time j.castSucc < t) (htj : t < K.time j.succ)
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (hσt : (σ : ℝ) = t) (haT : aSeed ≤ Tn)
    {pT : (K.toHistory.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (s : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage s) s)
        (a₀ + s) x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (K.toHistory.stageAt σ).Carrier)
    (yG : (K.stage j.castSucc).Carrier) (hyG : HEq y yG) {R : ℝ} (L : ℝ) (hR : 0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (i : Fin (K.prefixAt j.castSucc).eventCount)
    (first : Fin ((K.prefixAt j.castSucc).eventCount + 1)) (hf : first ≤ i.castSucc)
    (z : (K.stage j.castSucc).Carrier)
    (hz : z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) yG
      (D / Real.sqrt R))
    (Btr : BackwardPointTrace (K.prefixAt j.castSucc).toHistory first
      (Fin.last (K.prefixAt j.castSucc).eventCount) (Fin.le_last first) z)
    (v' : Icc (0 : ℝ) K.toHistory.horizon)
    (hv1 : (K.prefixAt j.castSucc).time i.castSucc < v')
    (hv2 : (v' : ℝ) < (K.prefixAt j.castSucc).time i.succ)
    (hav : aSeed ≤ v') (hvs : v' ≤ σ) (haL : (σ : ℝ) - L ^ 2 / R ≤ v') (hRa : 1 ≤ R * v')
    (hQbdef : Qb = max (max ((K.toHistory.event j).incoming.flow.scalar t z / R) Cg) 1)
    (hTdef : T = 1 / (2 * max (Ctime' : ℝ) 1) / Qb)
    (hguard : (t - v') * max (Cg * R) ((K.toHistory.event j).incoming.flow.scalar t z) ≤
      1 / (2 * max (Ctime' : ℝ) 1))
    (hℓ : 0 < ℓ) (hKℓ : Kc * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ Kc)
    (hKC : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ Kc)
    (hℓρ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (hρL : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (hT₀ : T₀ ≤ (v' : ℝ))
    (records : ∀ e : Fin K.eventCount, T₀ ≤ K.toHistory.time e.succ →
      GeometricCutoffRecord K.toHistory e q)
    (hOld : ∀ e : Fin K.eventCount, T₀ ≤ K.toHistory.time e.succ →
      (K.toHistory.event e).old = (K.toHistory.event e).transition.trace.retainedCore)
    (hcan : ∀ (e : Fin K.eventCount) (he : T₀ ≤ K.toHistory.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (hacc : q.modelAccuracy ≤ 1 / 2) (hDm : StandardCap.transitionEnd + 10 < q.modelRadius)
    (hprotC : ∀ (z'' : (K.toHistory.stageAt σ).Carrier), HEq z'' z →
      ∀ (A : BackwardPointTrace K.toHistory (K.toHistory.activeStage v')
          (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvs) z'')
        (e : Fin K.eventCount) (h1 : K.toHistory.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ K.toHistory.activeStage Tn) (h3 : K.toHistory.activeStage v' ≤ e.castSucc)
        (h4 : e.succ ≤ K.toHistory.activeStage σ) (he : T₀ ≤ K.toHistory.time e.succ),
        (∀ (w : Icc (0 : ℝ) K.toHistory.horizon) (hw : v' ≤ w) (hwσ : w ≤ σ),
          K.toHistory.time e.succ ≤ (w : ℝ) →
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage w) w)
              (seedTrace.point (K.toHistory.activeStage w)
                (K.toHistory.activeStage_mono (hav.trans hw))
                (K.toHistory.activeStage_mono (hwσ.trans hσT)))
              (A.point (K.toHistory.activeStage w) (K.toHistory.activeStage_mono hw)
                (K.toHistory.activeStage_mono hwσ)) <
            riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
                (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                  (K.toHistory.activeStage_mono hσT)) y +
              ENNReal.ofReal (L / 2 / Real.sqrt R)) → ∀ b,
        seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
          A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10})
    (hdσ : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
        (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
          (K.toHistory.activeStage_mono hσT)) y ≠ ⊤)
    (hnum : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R) :
    ∀ x : (K.toHistory.stageAt v').Carrier,
      HEq x (Btr.point i.castSucc hf (Fin.le_last _)) →
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v') v')
          (seedTrace.point (K.toHistory.activeStage v') (K.toHistory.activeStage_mono hav)
            (K.toHistory.activeStage_mono (hvs.trans hσT))) x ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
            (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
              (K.toHistory.activeStage_mono hσT)) y +
          ENNReal.ofReal (L / Real.sqrt R) := by
  intro x hx
  subst hσt
  have hact : K.toHistory.activeStage σ = j.castSucc :=
    K.activeStage_eq_of_mem_slab_P6JG3H j σ hjt.le htj
  let z' : (K.toHistory.stageAt σ).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hact.symm) z
  have hz' : HEq z' z := cast_heq _ _
  have hsc := K.scalar_of_incoming_P6JG3H j hact.symm (σ : ℝ) z z' hz'
  have hzy := K.mem_ball_of_incoming_P6JG3H j hact.symm (σ : ℝ) _ z yG z' y hz' hyG hz
  have hQbdef' : Qb = max (max (metricScalarAt (K.toHistory.stageMetric
      (K.toHistory.activeStage σ) σ) z' / R) Cg) 1 := by
    rw [hsc]
    exact hQbdef
  have hguard' : ((σ : ℝ) - v') * max (Cg * R) (metricScalarAt (K.toHistory.stageMetric
      (K.toHistory.activeStage σ) σ) z') ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by
    rw [hsc]
    exact hguard
  have hσlast : K.toHistory.activeStage σ < Fin.last K.eventCount := by
    rw [hact]
    exact Fin.castSucc_lt_last j
  have hvact : K.toHistory.activeStage v' =
      (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i).castSucc :=
    K.activeStage_eq_of_mem_slab_P6JG3H _ v' hv1.le hv2
  have hfn : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt)) first ≤
      K.toHistory.activeStage v' := by
    rw [hvact, Fin.le_iff_val_le_val]
    exact Fin.le_iff_val_le_val.mp hf
  have hnl : K.toHistory.activeStage v' ≤
      Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
        (Fin.last (K.prefixAt j.castSucc).eventCount) := by
    rw [hvact, Fin.le_iff_val_le_val]
    exact i.isLt.le
  have hl : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      (Fin.last (K.prefixAt j.castSucc).eventCount) = K.toHistory.activeStage σ := by
    rw [hact]
    exact Fin.ext rfl
  let B1 := K.backwardPointTraceOfPrefix j.castSucc Btr
  let B2 := B1.restrictFirst hfn hnl
  obtain ⟨A, hA⟩ := exists_trace_transport_P6SP (K.toHistory.activeStage_mono hvs) z' hl
    hz'.symm B2
  have hd := K.toHistory.stay_cstar_of_firstExit_P6SP hC2 hCg haT hsmall hclock seedTrace ha₀
    hpin hσT has y L hR hgood hav hvs hσlast haL hRa hQbdef' hTdef hguard' A hℓ hKℓ hℓr hKr hKC
    hℓρ hρL hT₀ records hOld hcan hacc hDm (hprotC z' hz' A) hzy hdσ hnum v' le_rfl hvs
  have e1 := hA (K.toHistory.activeStage v') (K.toHistory.activeStage_mono le_rfl) hnl
    (K.toHistory.activeStage_mono hvs)
  have hAx : HEq (A.point (K.toHistory.activeStage v') (K.toHistory.activeStage_mono le_rfl)
      (K.toHistory.activeStage_mono hvs)) (Btr.point i.castSucc hf (Fin.le_last _)) :=
    (heq_of_eq e1).trans (ofPrefix_point_heq_P6SP K j.castSucc Btr i.castSucc hf
      (Fin.le_last _) _ (by rw [hvact]; rfl) (hfn.trans (K.toHistory.activeStage_mono le_rfl))
      hnl)
  have hxA := eq_of_heq (hx.trans hAx.symm)
  rw [hxA]
  exact hd

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
