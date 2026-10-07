import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BackwardTraceChainCapture_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BackwardTraceScalarControlTimeWindow_P6N

/-!
# G1 footprint 时间窗改形（`_P6L′`）：`BTDT:58` + `BTCC:91/358/409` 的 `[u, t]` 窗口形（`_P6N`）

`BTCC:91_P6L` 只经 `BTDT:58_P6L` / `BTSC:168_P6L` 在窗口 `[u', t]`（`u' = time j.succ ≥ u`）上用导数界；
`hcmp`（当前 stage 的 metric comparison）在 `:358/:409` 由 `[time (activeStage t), t] ⊆ [u', t]` 上的
`normSq` 界给出 [V]。⇒ `hslabs`/`hcur`/`hcurrent`/`hfinal` 全加窗口 guard `(u : ℝ) ≤ v`，改调本车道
`BTSC:168` 窗口形（`…_window_P6N`）；guard 由 `u ≤ u'` 传递。`BTDT:58` 窗口形复制为 private
`…_window_P6N`。其余证明体照抄 `_P6L`；结论逐字。consumer：`BTCC:358/409_P6L`（全 slab）⇐ 窗口形。
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private ObservedHistory.activeStage_eq_of_time_mem
  ObservedHistory.time_lt_succ_of_activeStage_eq_castSucc
  ObservedHistory.backwardSurvivorInitialMetric_inner_le_exp
  ObservedHistory.initialMetric_inner_le_exp_of_normSq_le
  BackwardPointTrace.apply_point_eq_of_stage_eq
  RetainedCoreHistory.exists_window_point_of_edist_le from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortion

open private ObservedHistory.initialMetric_inner_le_exp_of_normSq_le_of_eq_last from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortionTerminal

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

private theorem normSq_stageMetric_le_of_backwardPointTrace_of_final_window_P6N
    {Ctime : ℝ≥0} {qcan M : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) p)
    (hslabs : ∀ i : Fin H.toHistory.eventCount, ∀ hf : H.toHistory.activeStage u ≤ i.castSucc,
      ∀ hl : i.succ ≤ H.toHistory.activeStage t,
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) (H.toHistory.time i.succ), (u : ℝ) ≤ v →
      qcan < (H.toHistory.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hcurrent : ∀ j : Fin H.toHistory.eventCount, ∀ y : (H.toHistory.stage j.castSucc).Carrier,
      j.castSucc = H.toHistory.activeStage t → HEq y p →
      ∀ v ∈ Ioo (H.toHistory.time j.castSucc) t, (u : ℝ) ≤ v →
      qcan < (H.toHistory.event j).incoming.flow.scalar v y →
      |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w y) (Iic v) v| ≤
        Ctime * (H.toHistory.event j).incoming.flow.scalar v y ^ 2)
    (hfinal : ∀ h : H.toHistory.time (Fin.last H.toHistory.eventCount) < H.toHistory.horizon,
      ∀ y : (H.toHistory.stage (Fin.last H.toHistory.eventCount)).Carrier,
      H.toHistory.activeStage t = Fin.last H.toHistory.eventCount → HEq y p →
      ∀ v ∈ Ioo (H.toHistory.time (Fin.last H.toHistory.eventCount)) t, (u : ℝ) ≤ v →
      qcan < ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y →
      |derivWithin (fun w =>
        ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w y) (Iic v) v| ≤
        Ctime * ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ^ 2)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hscalar : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u ≤ v) (hvt : v ≤ t) :
    normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
          (H.toHistory.activeStage_mono hvt)) 4
        (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt))) ≤
      (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by
  have hC : 0 ≤ 4 * Real.sqrt 3 * (1 + phi 1 + phi 0) := by
    have := hphi.pos 0
    have := hphi.pos 1
    positivity
  have hscal := H.scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds_window_P6N hut A
    hslabs hcurrent hfinal (by linarith) hqcan hscalar htime v huv hvt
  have hs := H.sqrt_rmNormSq_stageMetric_le_of_pinched hphi hpinch v
    (fun h => hlast (le_antisymm (Fin.le_last _) (h ▸ H.toHistory.activeStage_mono hvt)))
    (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
      (H.toHistory.activeStage_mono hvt))
  have hmax : max (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
      (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
        (H.toHistory.activeStage_mono hvt))) 1 ≤ 2 * M := max_le hscal (by linarith)
  have h1 := hs.trans (mul_le_mul_of_nonneg_left hmax hC)
  have hN := normSq0S_nonneg (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
    (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
      (H.toHistory.activeStage_mono hvt)) 4
    (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
      (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
        (H.toHistory.activeStage_mono hvt)))
  rw [← Real.sq_sqrt hN]
  calc _ ≤ (4 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (2 * M)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    _ = (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by ring

private theorem exists_cap_capture_of_chain_point_without_trace_of_comparison_window_P6N
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M Dcap Dstar : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (hcmp : ∀ (q : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (C : ℝ),
      (∀ s ∈ Icc (H.toHistory.time (H.toHistory.activeStage t)) (t : ℝ),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q) ≤ C) →
      ∀ w : TangentSpace ThreeModel q,
        (H.toHistory.initialMetric (H.toHistory.activeStage t)).inner q w w ≤
          Real.exp (18 * Real.sqrt C * ((t : ℝ) - H.toHistory.time (H.toHistory.activeStage t))) *
            (H.toHistory.stageMetric (H.toHistory.activeStage t) t).inner q w w)
    {N : ℕ} (pc : ℕ → (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (δ : ℕ → ℝ)
    (hδ : ∀ k ≤ N, 0 < δ k)
    (hchain : ∀ k < N, pc (k + 1) ∈
      riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (z : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hz : ∃ k ≤ N,
      z ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (hzt : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) z))
    (U : Set (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hchainU : ∀ k ≤ N, ∀ x ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k), x ∈ U)
    (hslabs : ∀ i : Fin H.toHistory.eventCount,
      ∀ (first : Fin (H.toHistory.eventCount + 1)) (hle : first ≤ H.toHistory.activeStage t),
      ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ H.toHistory.activeStage t,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H.toHistory first (H.toHistory.activeStage t) hle z,
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) (H.toHistory.time i.succ), (u : ℝ) ≤ v →
      qcan < (H.toHistory.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hcur : ∀ j : Fin H.toHistory.eventCount, ∀ y : (H.toHistory.stage j.castSucc).Carrier,
      j.castSucc = H.toHistory.activeStage t → ∀ z ∈ U, HEq y z →
      ∀ v ∈ Ioo (H.toHistory.time j.castSucc) t, (u : ℝ) ≤ v →
      qcan < (H.toHistory.event j).incoming.flow.scalar v y →
      |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w y) (Iic v) v| ≤
        Ctime * (H.toHistory.event j).incoming.flow.scalar v y ^ 2)
    (hfinal : ∀ h : H.toHistory.time (Fin.last H.toHistory.eventCount) < H.toHistory.horizon,
      ∀ y : (H.toHistory.stage (Fin.last H.toHistory.eventCount)).Carrier,
      H.toHistory.activeStage t = Fin.last H.toHistory.eventCount → ∀ z ∈ U, HEq y z →
      ∀ v ∈ Ioo (H.toHistory.time (Fin.last H.toHistory.eventCount)) t, (u : ℝ) ≤ v →
      qcan < ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y →
      |derivWithin (fun w =>
        ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w y) (Iic v) v| ≤
        Ctime * ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ^ 2)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ k ≤ N, ∀ x ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) *
        ∑ i ∈ Finset.range (N + 1), δ i < Dcap) :
    ∃ (j : Fin H.eventCount) (hl : j.succ ≤ H.toHistory.activeStage t)
      (A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl (pc 0))
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j).static b).window x ∧ ‖x.val‖ < Dcap ∧
      ((records j).static b).neck.scale ≤ 4 * M ∧
      ((records j).static b).neck.scale * ((t : ℝ) - H.time j.succ) ≤
        4 * M * ((t : ℝ) - u) := by
  classical
  set S : Set (H.toHistory.stage (H.toHistory.activeStage t)).Carrier :=
    {w | ∃ k ≤ N, w ∈ riemannianBallOf
      (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k)} with hSdef
  let good : Fin H.eventCount → Prop := fun j =>
    H.toHistory.activeStage u ≤ j.castSucc ∧ ∃ (hl : j.succ ≤ H.toHistory.activeStage t)
      (w : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier), w ∈ S ∧
      ∃ A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl w,
        ∀ p' : (H.toHistory.stage j.castSucc).Carrier,
          ¬ (H.toHistory.event j).RegularCrossing p' (A.point j.succ le_rfl hl)
  obtain ⟨j₀, hf₀, hl₀, A₀, hno₀⟩ :=
    H.toHistory.exists_latest_event_without_regularCrossing _ z hzt
  let T := Finset.univ.filter good
  have hTne : T.Nonempty :=
    ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf₀, hl₀, z, hz, A₀, hno₀⟩⟩
  obtain ⟨j, hjT, hjmax⟩ : ∃ j ∈ T, ∀ j' ∈ T, j' ≤ j :=
    ⟨T.max' hTne, T.max'_mem hTne, fun j' h => T.le_max' j' h⟩
  obtain ⟨-, hfj, hlj, zs, hzs, As, hnos⟩ := Finset.mem_filter.mp hjT
  have htr : ∀ w ∈ S,
      Nonempty (BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hlj w) := by
    intro w hw
    by_contra hn
    obtain ⟨j', hf', hl', A', hno'⟩ :=
      H.toHistory.exists_latest_event_without_regularCrossing hlj w (not_nonempty_iff.mp hn)
    have hmem : j' ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hfj.trans ((Fin.castSucc_lt_succ (i := j)).le.trans hf'), hl', w, hw, A', hno'⟩
    have h1 : j'.val ≤ j.val := hjmax j' hmem
    have h2 : j.val + 1 ≤ j'.val := hf'
    omega
  have hyS : pc 0 ∈ S := by
    refine ⟨0, Nat.zero_le _, ?_⟩
    change riemannianEDistOf _ (pc 0) (pc 0) < ENNReal.ofReal (δ 0)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (hδ 0 (Nat.zero_le _))
  let u' : Icc (0 : ℝ) H.toHistory.horizon :=
    ⟨H.toHistory.time j.succ, H.toHistory.time_nonneg _, H.toHistory.time_le_horizon_at _⟩
  have hau' : H.toHistory.activeStage u' = j.succ := H.toHistory.activeStage_at_time j.succ
  have hu'u : u ≤ u' := by
    change (u : ℝ) ≤ H.toHistory.time j.succ
    by_contra hle
    have h := H.toHistory.le_activeStage u j.succ (not_le.mp hle).le
    exact absurd (h.trans hfj) (not_le_of_gt (Fin.castSucc_lt_succ (i := j)))
  have huu' : (u : ℝ) ≤ u' := hu'u
  have hu't : u' ≤ t := by
    change H.toHistory.time j.succ ≤ (t : ℝ)
    exact (H.toHistory.time_strictMono.monotone hlj).trans (H.toHistory.activeStage_time_le t)
  have htime' : Ctime * M * ((t : ℝ) - u') ≤ 1 / 2 := by
    have hu : (u : ℝ) ≤ u' := hu'u
    have hC : 0 ≤ (Ctime : ℝ) * M := mul_nonneg Ctime.coe_nonneg (by linarith)
    nlinarith
  have hspaceS : ∀ q ∈ S,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) q ≤ M := by
    rintro q ⟨k, hk, hq⟩
    exact hspace k hk q hq
  have hSU : ∀ q ∈ S, q ∈ U := by
    rintro q ⟨k, hk, hq⟩
    exact hchainU k hk q hq
  have hRm : ∀ q ∈ S,
      ∀ Aq : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hlj q,
      ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u' ≤ v) (hvt : v ≤ t),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            ((Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)).point
              (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
              (H.toHistory.activeStage_mono hvt)) 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            ((Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)).point
              (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
              (H.toHistory.activeStage_mono hvt))) ≤
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := fun q hq Aq v huv hvt =>
    RetainedCoreHistory.normSq_stageMetric_le_of_backwardPointTrace_of_final_window_P6N H hphi
      hpinch hu't hlast (Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't))
      (fun i hf hl w hw huw => hslabs i _ _ hf hl q (hSU q hq)
        (Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)) w hw
        (huu'.trans huw))
      (fun j y hj hy w hw huw => hcur j y hj q (hSU q hq) hy w hw (huu'.trans huw))
      (fun h y ht hy w hw huw => hfinal h y ht q (hSU q hq) hy w hw (huu'.trans huw)) hM hqcan
      (hspaceS q hq) htime' v huv hvt
  obtain ⟨b, zc, hzc⟩ := (records j).exists_cap_of_not_regularCrossing_target hnos
  obtain ⟨-, -, -, -, -, -, -, hcap⟩ := hcan j b
  obtain ⟨xz, hxzn, hxz⟩ := hcap zc
  have hsM : ((records j).static b).neck.scale ≤ 4 * M := by
    have hb := H.scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds_window_P6N hu't
      (As.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't))
      (fun i hf hl w hw huw => hslabs i _ _ hf hl zs (hSU zs hzs)
        (As.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)) w hw
        (huu'.trans huw))
      (fun j y hj hy w hw huw => hcur j y hj zs (hSU zs hzs) hy w hw (huu'.trans huw))
      (fun h y ht hy w hw huw => hfinal h y ht zs (hSU zs hzs) hy w hw (huu'.trans huw))
      (by linarith) hqcan (hspaceS zs hzs) htime' u' le_rfl hu't
    have heq := BackwardPointTrace.apply_point_eq_of_stage_eq As
      (fun m q => metricScalarAt (H.toHistory.stageMetric m (H.toHistory.time j.succ)) q)
      hau' ((le_of_eq hau'.symm).trans (H.toHistory.activeStage_mono (le_refl u')))
      (H.toHistory.activeStage_mono hu't) le_rfl hlj
    have h2 : metricScalarAt ((records j).static b).witness.metric
        (((records j).static b).witness.cap zc) ≤ 2 * M := by
      rw [((records j).static b).scalar_eq, ← hzc, H.toHistory.event_output j,
        ← H.toHistory.stageMetric_initial]
      exact heq.symm.le.trans hb
    linarith [hscale j b zc]
  have hage : ((records j).static b).neck.scale * ((t : ℝ) - H.time j.succ) ≤
      4 * M * ((t : ℝ) - u) := by
    have hu : (u : ℝ) ≤ H.time j.succ := hu'u
    have hT : H.time j.succ ≤ (t : ℝ) := hu't
    nlinarith [mul_le_mul_of_nonneg_left hsM (sub_nonneg.mpr hT)]
  have hΛ0 : 0 ≤ 8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M := by
    have := hphi.pos 0
    have := hphi.pos 1
    have : 0 ≤ M := by linarith
    positivity
  have hlocal : ∀ q : H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj,
      q.val ∈ S → ∀ v : TangentSpace ThreeModel q,
        (H.toHistory.backwardSurvivorInitialMetric j.succ (H.toHistory.activeStage t) hlj j.succ
          le_rfl hlj).inner q v v ≤
        Real.exp (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
          ((t : ℝ) - H.toHistory.time j.succ)) *
          ((H.toHistory.stageMetric (H.toHistory.activeStage t) t).restrictOpen
            (H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj)).inner
            q v v := by
    intro q hq v
    have hb1 : ∀ v : Icc (0 : ℝ) H.toHistory.horizon, H.toHistory.time j.succ ≤ v →
        (v : ℝ) ≤ H.toHistory.time (H.toHistory.activeStage t) →
        ∀ (hf : j.succ ≤ H.toHistory.activeStage v)
          (hl : H.toHistory.activeStage v ≤ H.toHistory.activeStage t),
          normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
              ((Classical.choice q.property).point (H.toHistory.activeStage v) hf hl) 4
            (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
              ((Classical.choice q.property).point (H.toHistory.activeStage v) hf hl)) ≤
            (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := fun v hv1 hv2 _ _ =>
      hRm q.val hq (Classical.choice q.property) v hv1
        (hv2.trans (H.toHistory.activeStage_time_le t))
    have hb2 : ∀ s ∈ Icc (H.toHistory.time (H.toHistory.activeStage t)) (t : ℝ),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q.val 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q.val) ≤
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by
      intro s hs
      let v : Icc (0 : ℝ) H.toHistory.horizon :=
        ⟨s, (H.toHistory.time_nonneg _).trans hs.1, hs.2.trans t.2.2⟩
      have hav : H.toHistory.activeStage v = H.toHistory.activeStage t :=
        ObservedHistory.activeStage_eq_of_time_mem H.toHistory v _ hs.1 (fun i' h =>
          hs.2.trans_lt
            (ObservedHistory.time_lt_succ_of_activeStage_eq_castSucc H.toHistory t i' h))
      have huv : u' ≤ v := by
        change H.toHistory.time j.succ ≤ s
        exact (H.toHistory.time_strictMono.monotone hlj).trans hs.1
      have hb := hRm q.val hq (Classical.choice q.property) v huv hs.2
      have heq := BackwardPointTrace.apply_point_eq_of_stage_eq
        ((Classical.choice q.property).restrictFirst (le_of_eq hau'.symm)
          (H.toHistory.activeStage_mono hu't))
        (fun m x => normSq0S (H.toHistory.stageMetric m s) x 4
          (metricRm04At (H.toHistory.stageMetric m s) x))
        hav (H.toHistory.activeStage_mono huv) (H.toHistory.activeStage_mono hs.2)
        (H.toHistory.activeStage_mono hu't) le_rfl
      rw [BackwardPointTrace.endpoint_eq] at heq
      exact heq.symm.le.trans hb
    have h1 := ObservedHistory.backwardSurvivorInitialMetric_inner_le_exp H.toHistory hlj q hb1 v
    have h2 := hcmp q.val _ hb2 v
    rw [Real.sqrt_sq hΛ0] at h1 h2
    rw [SmoothRiemannianMetric.restrictOpen_inner]
    calc _ ≤ _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = _ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  set U := H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj with hUdef
  let y' : U := ⟨pc 0, htr (pc 0) hyS⟩
  let z' : U := ⟨zs, htr zs hzs⟩
  obtain ⟨kz, hkz, hzk⟩ := hzs
  have hz'' := riemannianEDistOf_lt_sqrt_mul_sum_of_ball_chain
    (H.toHistory.stageMetric (H.toHistory.activeStage t) t) U
    (H.toHistory.backwardSurvivorInitialMetric j.succ (H.toHistory.activeStage t) hlj j.succ
      le_rfl hlj) (Real.exp_pos (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
        ((t : ℝ) - H.toHistory.time j.succ))) hδ
    (fun k hk w hw => htr w ⟨k, hk, hw⟩) hchain (fun q hq v => hlocal q hq v) y' rfl kz hkz
    z' hzk
  have hmono : ∑ i ∈ Finset.range (kz + 1), δ i ≤ ∑ i ∈ Finset.range (N + 1), δ i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun i hi _ => (hδ i (by have := Finset.mem_range.mp hi; omega)).le)
  have hmap := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
    (H.toHistory.backwardSurvivorInitialMetric j.succ (H.toHistory.activeStage t) hlj j.succ
      le_rfl hlj)
    (H.toHistory.initialMetric j.succ)
    (H.toHistory.backwardSurvivorMap j.succ (H.toHistory.activeStage t) hlj j.succ le_rfl hlj)
    (H.toHistory.backwardSurvivorMap_isLocalDiffeomorph _ _ hlj j.succ le_rfl hlj) one_pos
    (fun x v => by
      rw [one_mul, ObservedHistory.backwardSurvivorInitialMetric, localPullMetric_inner])
    y' z'
  have hΦz : H.toHistory.backwardSurvivorMap j.succ (H.toHistory.activeStage t) hlj j.succ le_rfl
      hlj z' = As.point j.succ le_rfl hlj :=
    H.toHistory.backwardSurvivorMap_eq_point _ _ hlj j.succ le_rfl hlj z' As
  have hexp : Real.sqrt (Real.exp (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
      ((t : ℝ) - H.toHistory.time j.succ))) =
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
        ((t : ℝ) - H.toHistory.time j.succ)) := by
    rw [show 18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
        ((t : ℝ) - H.toHistory.time j.succ) =
        9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - H.toHistory.time j.succ) +
        9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - H.toHistory.time j.succ)
        by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range (N + 1), δ i :=
    Finset.sum_nonneg fun i hi => (hδ i (by have := Finset.mem_range.mp hi; omega)).le
  set dd := Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
      ((t : ℝ) - H.toHistory.time j.succ)) * ∑ i ∈ Finset.range (N + 1), δ i with hdd
  have hnear : riemannianEDistOf (H.toHistory.initialMetric j.succ)
      (((records j).static b).window xz)
      ((Classical.choice (htr (pc 0) hyS)).point j.succ le_rfl hlj) ≤ ENNReal.ofReal dd := by
    rw [hxz, ← hzc, ← hΦz, riemannianEDistOf_comm]
    rw [hexp] at hz''
    refine hmap.trans ?_
    rw [Real.sqrt_one, ENNReal.ofReal_one, one_mul]
    refine hz''.le.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
  have hwin' : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      (Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) *
        ∑ i ∈ Finset.range (N + 1), δ i) < Dcap := by
    rw [← mul_assoc]
    exact hwin
  have hdd' : dd ≤ Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
      ((t : ℝ) - u)) * ∑ i ∈ Finset.range (N + 1), δ i := by
    have hu : (u : ℝ) ≤ H.toHistory.time j.succ := hu'u
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hsum0
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  obtain ⟨x, hxn', hxeq⟩ := RetainedCoreHistory.exists_window_point_of_edist_le H records hcan
    hacc j b hsM hDstar hDmodel xz hxzn _ (hnear.trans (ENNReal.ofReal_le_ofReal hdd'))
    (mul_nonneg (Real.exp_pos _).le hsum0) hwin'
  exact ⟨j, hlj, Classical.choice (htr (pc 0) hyS), b, x, hxeq.symm, hxn', hsM, hage⟩

/-- **`_P6N`（`BTCC:358` 窗口形）**：`BTCC:358_P6L` 的 `hslabs`/`hcurrent` 只在 `[u, t]` 内要
（guard `(u : ℝ) ≤ v`）。结论逐字。 -/
theorem capWindowPoint_of_chain_point_without_trace_window_P6N {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M Dcap Dstar θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (i : Fin H.eventCount)
    (hi : H.toHistory.activeStage t = i.castSucc)
    {N : ℕ} (pc : ℕ → (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (δ : ℕ → ℝ)
    (hδ : ∀ k ≤ N, 0 < δ k)
    (hchain : ∀ k < N, pc (k + 1) ∈
      riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (z : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hz : ∃ k ≤ N,
      z ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (hzt : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) z))
    (U : Set (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hchainU : ∀ k ≤ N, ∀ x ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k), x ∈ U)
    (hslabs : ∀ i : Fin H.toHistory.eventCount,
      ∀ (first : Fin (H.toHistory.eventCount + 1)) (hle : first ≤ H.toHistory.activeStage t),
      ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ H.toHistory.activeStage t,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H.toHistory first (H.toHistory.activeStage t) hle z,
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) (H.toHistory.time i.succ), (u : ℝ) ≤ v →
      qcan < (H.toHistory.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hcurrent : ∀ y : (H.toHistory.stage i.castSucc).Carrier, ∀ z ∈ U, HEq y z →
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) t, (u : ℝ) ≤ v →
      qcan < (H.toHistory.event i).incoming.flow.scalar v y →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w y) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v y ^ 2)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ k ≤ N, ∀ x ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 4 * M * ((t : ℝ) - u) ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) *
        ∑ i ∈ Finset.range (N + 1), δ i < Dcap) :
    H.CapWindowPoint records (H.toHistory.activeStage t) (pc 0) t Dcap θcap := by
  have hne : H.toHistory.activeStage t ≠ Fin.last H.eventCount := by
    rw [hi]
    exact Fin.castSucc_ne_last i
  obtain ⟨j, hl, A, b, x, hx, hxn, -, hage⟩ :=
    exists_cap_capture_of_chain_point_without_trace_of_comparison_window_P6N H records hcan hscale
      hacc hphi hpinch hut (fun h => absurd h hne)
      (fun q _ hb w => ObservedHistory.initialMetric_inner_le_exp_of_normSq_le H.toHistory hi q
        (H.toHistory.activeStage_time_le t)
        (ObservedHistory.time_lt_succ_of_activeStage_eq_castSucc H.toHistory t i hi) hb w)
      pc δ hδ hchain z hz hzt U hchainU hslabs
      (fun j y hj => by
        have : j = i := Fin.castSucc_injective _ (hj.trans hi)
        subst this
        exact hcurrent y)
      (fun _ _ h => absurd h hne) hM hqcan hspace htime hDstar hDmodel hwin
  refine ⟨j, hl, A, b, x, hx, by linarith, ?_⟩
  rw [← div_eq_mul_inv, le_div_iff₀ ((records j).static b).neck.scale_pos]
  linarith

/-- **`_P6N`（`BTCC:409` 窗口形）**：`BTCC:409_P6L` 的 `hslabs`/`hfinal` 只在 `[u, t]` 内要
（guard `(u : ℝ) ≤ v`）。结论逐字。 -/
theorem capWindowPoint_of_chain_point_without_trace_of_activeStage_eq_last_window_P6N
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M Dcap Dstar θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    (hfinalPinch : Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
      (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    {N : ℕ} (pc : ℕ → (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (δ : ℕ → ℝ)
    (hδ : ∀ k ≤ N, 0 < δ k)
    (hchain : ∀ k < N, pc (k + 1) ∈
      riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (z : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hz : ∃ k ≤ N,
      z ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (hzt : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) z))
    (U : Set (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hchainU : ∀ k ≤ N, ∀ x ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k), x ∈ U)
    (hslabs : ∀ i : Fin H.toHistory.eventCount,
      ∀ (first : Fin (H.toHistory.eventCount + 1)) (hle : first ≤ H.toHistory.activeStage t),
      ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ H.toHistory.activeStage t,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H.toHistory first (H.toHistory.activeStage t) hle z,
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) (H.toHistory.time i.succ), (u : ℝ) ≤ v →
      qcan < (H.toHistory.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ y : (H.toHistory.stage (Fin.last H.eventCount)).Carrier, ∀ z ∈ U, HEq y z →
      ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, (u : ℝ) ≤ v →
      qcan < ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y →
      |derivWithin (fun w => ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w y)
        (Iic v) v| ≤ Ctime * ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ^ 2)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ k ≤ N, ∀ x ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 4 * M * ((t : ℝ) - u) ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) *
        ∑ i ∈ Finset.range (N + 1), δ i < Dcap) :
    H.CapWindowPoint records (H.toHistory.activeStage t) (pc 0) t Dcap θcap := by
  obtain ⟨j, hl, A, b, x, hx, hxn, -, hage⟩ :=
    exists_cap_capture_of_chain_point_without_trace_of_comparison_window_P6N H records hcan hscale
      hacc hphi hpinch hut (fun _ => ⟨h, hfinalPinch⟩)
      (fun q _ hb w => ObservedHistory.initialMetric_inner_le_exp_of_normSq_le_of_eq_last
        H.toHistory hlastA h q (H.toHistory.activeStage_time_le t) t.2.2 hb w)
      pc δ hδ hchain z hz hzt U hchainU hslabs
      (fun j _ hj => absurd (hj.trans hlastA) (Fin.castSucc_ne_last j))
      (fun _ y _ => hfinal y) hM hqcan hspace htime hDstar hDmodel hwin
  refine ⟨j, hl, A, b, x, hx, by linarith, ?_⟩
  rw [← div_eq_mul_inv, le_div_iff₀ ((records j).static b).neck.scale_pos]
  linarith

/-- consumer：`BTCC:358_P6L`（全 slab footprint 形）由窗口形推回（丢 guard）。 -/
example : type_of% @capWindowPoint_of_chain_point_without_trace_P6L.{u} := by
  intro H p records hcan hscale hacc Ctime qcan M Dcap Dstar θcap phi hphi hpinch u t hut i hi N pc
    δ hδ hchain z hz hzt U hchainU hslabs hcurrent hM hqcan hspace htime hDstar hDmodel hθ hwin
  exact capWindowPoint_of_chain_point_without_trace_window_P6N H records hcan hscale hacc hphi
    hpinch hut i hi pc δ hδ hchain z hz hzt U hchainU
    (fun j first hle hf hl z hz A v hv _ hR => hslabs j first hle hf hl z hz A v hv hR)
    (fun y z hz hyz v hv _ hR => hcurrent y z hz hyz v hv hR) hM hqcan hspace htime hDstar
    hDmodel hθ hwin

/-- consumer：`BTCC:409_P6L`（全 slab footprint 形）由窗口形推回（丢 guard）。 -/
example : type_of% @capWindowPoint_of_chain_point_without_trace_of_activeStage_eq_last_P6L.{u} := by
  intro H p records hcan hscale hacc Ctime qcan M Dcap Dstar θcap phi hphi hpinch u t hut h hlastA
    hfinalPinch N pc δ hδ hchain z hz hzt U hchainU hslabs hfinal hM hqcan hspace htime hDstar
    hDmodel hθ hwin
  exact capWindowPoint_of_chain_point_without_trace_of_activeStage_eq_last_window_P6N H records
    hcan hscale hacc hphi hpinch hut h hlastA hfinalPinch pc δ hδ hchain z hz hzt U hchainU
    (fun j first hle hf hl z hz A v hv _ hR => hslabs j first hle hf hl z hz A v hv hR)
    (fun y z hz hyz v hv _ hR => hfinal y z hz hyz v hv hR) hM hqcan hspace htime hDstar hDmodel
    hθ hwin

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
