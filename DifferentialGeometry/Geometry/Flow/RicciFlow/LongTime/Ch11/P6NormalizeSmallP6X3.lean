import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NormalizeP6X
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

/-!
# D-17 normalized 变体：`hPN` 前缀带种子小曲率（O-CH11-P6SEL3 G4a，后缀 `_P6X3`）

P6SEL G4 `lateCoreAt_of_normalized_P6X` 的坏种子在原尺度带 `hasSmallParabolicCurvature H t p r`，但
`hPN` 的形状把它丢了。本文件把它**经 rescale 搬到重标度种子**（`c := r²`，`r̃ = r/√c = 1`）并传进 `hPN`：
* `weighted_rm_sq_scale_inv_P6X3`：`(r/√c)⁴ |Rm|²_{c⁻¹g} = r⁴ |Rm|²_g`（树内 `metricRm_scale`、
  `normSq0S_smul`、`normSq0S_scale`）；`terminal_weighted_rm_sq_rescale_P6X3`：同式于重标度终端极限度量
  （`rescale_terminalRegularOpen` + `TerminalLimitMetric.rescale_metric_heq_P6N`，点以 `HEq` 对应）；
* `trace_transfer_point_P6X3`：`trace_transfer_P6X` 不改点；
* `RetainedCoreHistory.isRmControlled_rescale_P6X3`：`tr.isRmControlled ρ` ⇒ 重标度种子 trace
  （`seedTrace_rescale_P6X`）`isRmControlled (ρ/√c)`（slab 项走 `unscaleTime`，crossing 项走终端式）；
* **`RetainedCoreHistory.hasSmallParabolicCurvature_rescale_P6X3`**：
  `hasSmallParabolicCurvature H t p r` ⇒ 重标度 history 在 `(t/c, p̃)` 半径 `r/√c` 的同一谓词；
* **`lateCoreAt_of_normalizedS_P6X3` / `canonicalLateCore_of_normalizedS_P6X3`**：同 P6SEL G4，`hPNS` =
  `hPN` 前缀在 `1 ≤ ãSeed` 后多一项 `∀ k, hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1`（来源 = 原
  history 的 hsmall 经上条，`c = r²`）。
（`weighted_rm_sq…` 与 CX-SPINE 进行中的 `P6RmRescaleCXSP` 同式，独立证明，不 import 未登记文件。）
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- `(r/√c)⁴ |Rm|²_{c⁻¹ g} = r⁴ |Rm|²_g`。 -/
theorem weighted_rm_sq_scale_inv_P6X3
    {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (g : SmoothRiemannianMetric ThreeModel X) (c : ℝ) (hc : 0 < c) (r : ℝ) (x : X) :
    (r / Real.sqrt c) ^ 4 * normSq0S (scaleMetric c⁻¹ (inv_pos.mpr hc) g) x 4
        (metricRm04At (scaleMetric c⁻¹ (inv_pos.mpr hc) g) x) =
      r ^ 4 * normSq0S g x 4 (metricRm04At g x) := by
  let _ : IsManifold ThreeModel 1 X := IsManifold.of_le (n := ∞) (by decide)
  have hnorm : normSq0S (scaleMetric c⁻¹ (inv_pos.mpr hc) g) x 4
      (metricRm04At (scaleMetric c⁻¹ (inv_pos.mpr hc) g) x) =
      c ^ 2 * normSq0S g x 4 (metricRm04At g x) := by
    simp only [← metricRm04_apply]
    rw [metricRm_scale, normSq0S_smul, normSq0S_scale, inv_inv]
    have hcancel : (c⁻¹) ^ 2 * c ^ 4 = c ^ 2 := by
      calc
        _ = (c⁻¹ * c) ^ 2 * c ^ 2 := by ring
        _ = _ := by rw [inv_mul_cancel₀ hc.ne', one_pow, one_mul]
    rw [← mul_assoc, hcancel]
  have hsqrt : (Real.sqrt c) ^ 4 = c ^ 2 := by
    calc
      _ = ((Real.sqrt c) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hc.le]
  rw [hnorm, div_pow, hsqrt, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hc.ne')]

private theorem rm_sq_eq_of_open_heq_P6X3 {P : OrientedThreeStage.{u}}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    (gU : SmoothRiemannianMetric ThreeModel U) (gV : SmoothRiemannianMetric ThreeModel V)
    (hg : HEq gU gV) (xU : U) (xV : V) (hx : HEq xU xV) :
    normSq0S gU xU 4 (metricRm04At gU xU) = normSq0S gV xV 4 (metricRm04At gV xV) := by
  subst hUV
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hx
  rfl

/-- 终端极限度量版：`(r/√c)⁴ |Rm|²` 于重标度终端度量 = `r⁴ |Rm|²` 于原终端度量（点以 `HEq` 对应）。 -/
theorem terminal_weighted_rm_sq_rescale_P6X3 {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} (L : G.TerminalLimitMetric) (c : ℝ) (hc : 0 < c) (r : ℝ)
    (xS : (G.rescale c hc).terminalRegularOpen) (x : G.terminalRegularOpen) (hx : HEq xS x) :
    (r / Real.sqrt c) ^ 4 * normSq0S (L.rescale c hc).metric xS 4
        (metricRm04At (L.rescale c hc).metric xS) =
      r ^ 4 * normSq0S L.metric x 4 (metricRm04At L.metric x) := by
  rw [rm_sq_eq_of_open_heq_P6X3 (G.rescale_terminalRegularOpen c hc) (L.rescale c hc).metric
    (scaleMetric c⁻¹ (inv_pos.mpr hc) L.metric) (L.rescale_metric_heq_P6N c hc) xS x hx]
  exact weighted_rm_sq_scale_inv_P6X3 L.metric c hc r x

/-- 相等 open 的子类型点：值相等 ⇒ `HEq`。 -/
theorem heq_of_opens_val_P6X3 {X : Type*} [TopologicalSpace X]
    {U V : TopologicalSpace.Opens X} (h : U = V) (x : U) (y : V) (hv : (x : X) = y) :
    HEq x y := by
  subst h
  exact heq_of_eq (Subtype.ext hv)

/-- `trace_transfer_P6X` 不改点。 -/
theorem trace_transfer_point_P6X3 {Hh : ObservedHistory.{u}} {f l f' l' : Fin (Hh.eventCount + 1)}
    (hf : f = f') (hl : l = l') {hle : f ≤ l} {hle' : f' ≤ l'} {x : (Hh.stage l).Carrier}
    {x' : (Hh.stage l').Carrier} (hx : HEq x x') (A : BackwardPointTrace Hh f l hle x)
    (j : Fin (Hh.eventCount + 1)) (h1 : f' ≤ j) (h2 : j ≤ l') :
    (trace_transfer_P6X (hle' := hle') hf hl hx A).point j h1 h2 =
      A.point j (hf.le.trans h1) (h2.trans hl.ge) := by
  subst hf
  subst hl
  obtain rfl := eq_of_heq hx
  rfl

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)

/-- stage 度量版：`(ρ/√c)⁴ |Rm|²` 于重标度 stage 度量（时刻 `t`）= `ρ⁴ |Rm|²` 于原 stage 度量
（时刻 `c t`）。 -/
theorem weighted_stage_rescale_P6X3 (j : Fin (K.eventCount + 1)) (t ρ : ℝ)
    (z : (K.stage j).Carrier) :
    (ρ / Real.sqrt c) ^ 4 * normSq0S ((K.rescale_P6N c hc).toHistory.stageMetric j t) z 4
        (metricRm04At ((K.rescale_P6N c hc).toHistory.stageMetric j t) z) =
      ρ ^ 4 * normSq0S (K.toHistory.stageMetric j (c * t)) z 4
        (metricRm04At (K.toHistory.stageMetric j (c * t)) z) := by
  rw [K.rescale_P6N_stageMetric c hc j t]
  exact weighted_rm_sq_scale_inv_P6X3 _ c hc ρ z

/-- **种子 trace 的 `isRmControlled` 重标度**：半径 `ρ ↦ ρ/√c`。 -/
theorem isRmControlled_rescale_P6X3 {a t : Icc (0 : ℝ) K.toHistory.horizon} (hat : a ≤ t)
    {x : (K.toHistory.stageAt t).Carrier}
    (tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage a) (K.toHistory.activeStage t)
      (K.toHistory.activeStage_mono hat) x) {ρ : ℝ} (hρ : tr.isRmControlled (hat := hat) ρ) :
    (K.seedTrace_rescale_P6X hc hat tr).isRmControlled (hat := K.rescaleTime_mono_P6X hc hat)
      (ρ / Real.sqrt c) := by
  have hpt : ∀ (j : Fin (K.eventCount + 1))
      (h1 : (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc a) ≤ j)
      (h2 : j ≤ (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc t))
      (h1' : K.toHistory.activeStage a ≤ j) (h2' : j ≤ K.toHistory.activeStage t),
      (K.seedTrace_rescale_P6X hc hat tr).point j h1 h2 = tr.point j h1' h2' :=
    fun j h1 h2 _ _ => trace_transfer_point_P6X3 (Hh := (K.rescale_P6N c hc).toHistory)
      (K.activeStage_rescaleTime_P6X hc a).symm (K.activeStage_rescaleTime_P6X hc t).symm
      (K.heq_castRescale_P6X hc t x).symm (K.traceToRescale_P6N c hc tr) j h1 h2
  have ha := K.activeStage_rescaleTime_P6X hc a
  have ht := K.activeStage_rescaleTime_P6X hc t
  refine ⟨fun s hs1 hs2 => ?_, fun i hf hl => ?_⟩
  · have has0 : a ≤ K.unscaleTime_P6X hc s := by
      have h := hs1
      change (a : ℝ) / c ≤ s at h
      rw [div_le_iff₀ hc] at h
      change (a : ℝ) ≤ c * s
      linarith
    have hst0 : K.unscaleTime_P6X hc s ≤ t := by
      have h := hs2
      change (s : ℝ) ≤ (t : ℝ) / c at h
      rw [le_div_iff₀ hc] at h
      change c * (s : ℝ) ≤ t
      linarith
    have key : ∀ (j : Fin (K.eventCount + 1))
        (_ : j = K.toHistory.activeStage (K.unscaleTime_P6X hc s))
        (h1 : K.toHistory.activeStage a ≤ j) (h2 : j ≤ K.toHistory.activeStage t),
        (ρ / Real.sqrt c) ^ 4 * normSq0S ((K.rescale_P6N c hc).toHistory.stageMetric j s)
            (tr.point j h1 h2) 4
            (metricRm04At ((K.rescale_P6N c hc).toHistory.stageMetric j s) (tr.point j h1 h2)) ≤
          1 := by
      intro j hj h1 h2
      subst hj
      exact (K.weighted_stage_rescale_P6X3 hc _ s ρ _).trans_le (hρ.1 _ has0 hst0)
    rw [hpt _ _ _ (ha.ge.trans ((K.rescale_P6N c hc).toHistory.activeStage_mono hs1))
      (((K.rescale_P6N c hc).toHistory.activeStage_mono hs2).trans ht.le)]
    exact key _ (K.activeStage_unscale_P6X hc s) _ _
  · have hf0 : K.toHistory.activeStage a ≤ i.castSucc := ha.ge.trans hf
    have hl0 : i.succ ≤ K.toHistory.activeStage t := hl.trans ht.le
    intro xS
    refine (terminal_weighted_rm_sq_rescale_P6X3 (K.toHistory.event i).terminal c hc ρ xS _
      ?_).trans_le (hρ.2 i hf0 hl0)
    exact heq_of_opens_val_P6X3 ((K.toHistory.event i).incoming.rescale_terminalRegularOpen c hc)
      _ _ (hpt _ _ _ hf0 _)

/-- **`hasSmallParabolicCurvature` 的重标度**：`(t, p, r) ↦ (t/c, p̃, r/√c)`。 -/
theorem hasSmallParabolicCurvature_rescale_P6X3 (t : Icc (0 : ℝ) K.toHistory.horizon)
    (p : (K.toHistory.stageAt t).Carrier) {r : ℝ}
    (h : GC.LongTime.hasSmallParabolicCurvature K.toHistory t p r) :
    GC.LongTime.hasSmallParabolicCurvature (K.rescale_P6N c hc).toHistory (K.rescaleTime_P6X hc t)
      (K.castRescale_P6X hc t p) (r / Real.sqrt c) := by
  obtain ⟨hr, a, hat, ha, htr⟩ := h
  refine ⟨div_pos hr (Real.sqrt_pos.mpr hc), K.rescaleTime_P6X hc a, K.rescaleTime_mono_P6X hc hat,
    ?_, ?_⟩
  · change (a : ℝ) / c = (t : ℝ) / c - (r / Real.sqrt c) ^ 2
    rw [ha, div_pow, Real.sq_sqrt hc.le, sub_div]
  · intro xS hxS
    obtain ⟨x, rfl⟩ : ∃ x, K.castRescale_P6X hc t x = xS :=
      ⟨cast (congrArg (fun j => (K.stage j).Carrier) (K.activeStage_rescaleTime_P6X hc t)) xS,
        by
          unfold castRescale_P6X
          exact (cast_cast _ _ _).trans (cast_eq _ _)⟩
    have hx : x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage t) t) p r := by
      have h1 : riemannianEDistOf ((K.rescale_P6N c hc).toHistory.stageMetric
          ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc t))
          (K.rescaleTime_P6X hc t)) (K.castRescale_P6X hc t p) (K.castRescale_P6X hc t x) <
          ENNReal.ofReal (r / Real.sqrt c) := hxS
      rw [K.edist_castRescale_P6X hc t p x] at h1
      change riemannianEDistOf _ p x < ENNReal.ofReal r
      have hs : 0 < Real.sqrt c⁻¹ := Real.sqrt_pos.mpr (inv_pos.mpr hc)
      have heq : ENNReal.ofReal (r / Real.sqrt c) =
          ENNReal.ofReal (Real.sqrt c⁻¹) * ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_mul hs.le, Real.sqrt_inv, div_eq_mul_inv, mul_comm]
      rw [heq] at h1
      by_contra hn
      exact absurd h1 (not_lt.mpr (mul_le_mul' le_rfl (not_lt.mp hn)))
    obtain ⟨tr, htr'⟩ := htr x hx
    refine ⟨K.seedTrace_rescale_P6X hc hat tr, ?_⟩
    have hc' := K.isRmControlled_rescale_P6X3 hc hat tr htr'
    rwa [mul_div_assoc] at hc'

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse

/-- **(b) 于单个 `A > 0` ⇐ S5 + S11 + `hPNS`**（P6SEL G4 `lateCoreAt_of_normalized_P6X` 的副本；
`hPNS` 前缀多 `∀ k, hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1`，由原尺度种子的 hsmall 经
`hasSmallParabolicCurvature_rescale_P6X3`（`c = r²`，`r/√(r²) = 1`）供给）。 -/
theorem lateCoreAt_of_normalizedS_P6X3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hPN : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
        (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
        (∀ k, hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k =
          metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
        Tendsto L atTop atTop →
        (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
          (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
          ∀ z : ((Kh k).stageAt v).Carrier,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / Real.sqrt (R k)) →
            4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
            (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
      False)
    {A : ℝ} (hA : 0 < A) :
    LargerBallCanonicalLateAt_P6A F ε C1 C2 A := by
  by_contra hcon
  have hk : ∀ k : ℕ, ∃ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (p : ((F.tower.history n).toHistory.stageAt t).Carrier) (r : ℝ)
      (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
      (k : ℝ) + 1 ≤ (t : ℝ) ∧ 2 * r ^ 2 < (t : ℝ) ∧
      hasSmallParabolicCurvature (F.tower.history n).toHistory t p r ∧
      x ∈ riemannianBallOf ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) p (A * r) ∧
      ((k : ℝ) + 1) * (r ^ 2)⁻¹ ≤ metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) x ∧
      ¬ ∃ W : SpatialCanonicalWitness ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) ε C1 C2 x,
        W.capTubeHasNeckChart ε := by
    intro k
    by_contra hk
    refine hcon ⟨(k : ℝ) + 1, (k : ℝ) + 1, by positivity, by positivity, ?_⟩
    intro n _ t p r hT ht hs _ x hx hK
    by_contra hW
    exact hk ⟨n, t, p, r, x, hT, ht, hs, hx, hK, hW⟩
  choose ind Tn pT r x hlate htime hsmall hx hK hW using hk
  have hr : ∀ k, 0 < r k := fun k => (hsmall k).1
  have hseed : ∀ k, ∃ (a : Icc (0 : ℝ) (F.tower.history (ind k)).toHistory.horizon)
      (hat : a ≤ Tn k), (a : ℝ) = (Tn k : ℝ) - r k ^ 2 ∧
      Nonempty (BackwardPointTrace (F.tower.history (ind k)).toHistory
        ((F.tower.history (ind k)).toHistory.activeStage a)
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k))
        ((F.tower.history (ind k)).toHistory.activeStage_mono hat) (pT k)) := fun k => by
    obtain ⟨hrk, a, hat, ha, htr⟩ := hsmall k
    have hp : pT k ∈ riemannianBallOf ((F.tower.history (ind k)).toHistory.stageMetric
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (pT k) (r k) := by
      change riemannianEDistOf _ (pT k) (pT k) < ENNReal.ofReal (r k)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hrk
    obtain ⟨tr, -⟩ := htr (pT k) hp
    exact ⟨a, hat, ha, ⟨tr⟩⟩
  choose aSeed haT hclock hst using hseed
  have hc : ∀ k, 0 < r k ^ 2 := fun k => pow_pos (hr k) 2
  have hsq : ∀ k, Real.sqrt (r k ^ 2) = r k := fun k => Real.sqrt_sq (hr k).le
  have hRx : ∀ k : ℕ, (k : ℝ) + 1 ≤ r k ^ 2 * metricScalarAt
      ((F.tower.history (ind k)).toHistory.stageMetric
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (x k) := by
    intro k
    have := mul_le_mul_of_nonneg_left (hK k) (hc k).le
    rwa [← mul_assoc, mul_comm (r k ^ 2), mul_assoc, mul_inv_cancel₀ (hc k).ne', mul_one] at this
  have hRx' : ∀ k : ℕ, (k : ℝ) + 1 ≤ metricScalarAt
      (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.stageMetric
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.activeStage
          ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
        ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k)) := fun k => by
    rw [(F.tower.history (ind k)).scalar_castRescale_P6X (hc k)]
    exact hRx k
  have hxb : ∀ k, (F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k) ∈
      riemannianBallOf
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.stageMetric
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.activeStage
          ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
        ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (pT k)) (A * 1) := fun k => by
    have h := (F.tower.history (ind k)).ball_castRescale_P6X (hc k) (Tn k) (pT k) (x k) (hx k)
    rwa [hsq k, mul_div_assoc, div_self (hr k).ne'] at h
  have hclock' : ∀ k, (((F.tower.history (ind k)).rescaleTime_P6X (hc k) (aSeed k) :
      Icc (0 : ℝ) ((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.horizon) :
        ℝ) = ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k) : ℝ) - 1 ^ 2 := fun k => by
    change (aSeed k : ℝ) / r k ^ 2 = (Tn k : ℝ) / r k ^ 2 - 1 ^ 2
    rw [hclock k, sub_div, div_self (hc k).ne', one_pow]
  have hsel := ObservedHistory.selection_of_bad_sequence_P6X
    (Kh := fun k => ((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory)
    (fun k => q.rescale_P6N (r k ^ 2) (hc k)) le_rfl le_rfl le_rfl
    (fun k => RetainedCoreHistory.neckRadius_rescale_antitone_P6X (hc k) hanti)
    (fun k => (F.tower.history (ind k)).canonical_rescale_P6X (hc k) (hcan (ind k)))
    (fun k => (F.tower.history (ind k)).derivative_rescale_P6X (hc k)
      (fun v z hlo hhi hR =>
        stageDerivative_of_timeDerivativeSupply_P6X hder (ind k) v z hlo hhi hR))
    (fun k => (F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k))
    (fun k => (F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (pT k))
    (fun _ => 1) A (fun _ => one_pos) hA
    (fun k => (F.tower.history (ind k)).rescaleTime_P6X (hc k) (aSeed k))
    (fun k => (F.tower.history (ind k)).rescaleTime_mono_P6X (hc k) (haT k)) hclock'
    (fun k => (F.tower.history (ind k)).seedTrace_rescale_P6X (hc k) (haT k) (hst k).some)
    (fun k => (F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k)) hxb
    (fun k => lt_of_lt_of_le (by positivity) (hRx' k))
    (fun k hG => (F.tower.history (ind k)).noWitness_castRescale_P6X (hc k) (Tn k) (x k) (hW k)
      hG.1)
    (tendsto_atTop_mono (fun k : ℕ => by rw [one_pow, mul_one]; linarith [hRx' k])
      tendsto_natCast_atTop_atTop)
  obtain ⟨σ, y, R, hsT, has, L, hRdef, hRpos, hRle, -, hL, hbad, hgood, hwin, hwin', hroom,
    hradii⟩ := hsel
  have hsmallR : ∀ k, hasSmallParabolicCurvature
      ((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory
      ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (pT k)) 1 := fun k => by
    have h := (F.tower.history (ind k)).hasSmallParabolicCurvature_rescale_P6X3 (hc k) (Tn k)
      (pT k) (hsmall k)
    rwa [hsq k, div_self (hr k).ne'] at h
  refine hPN ind (fun k => r k ^ 2) hc
    (fun k => (F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k))
    (fun k => (F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (pT k))
    (fun k => by rw [(F.tower.history (ind k)).mul_rescaleTime_P6X (hc k)]; exact hlate k)
    (fun k => (F.tower.history (ind k)).rescaleTime_P6X (hc k) (aSeed k))
    (fun k => (F.tower.history (ind k)).rescaleTime_mono_P6X (hc k) (haT k)) hclock'
    (fun k => ?_) hsmallR
    (fun k => (F.tower.history (ind k)).seedTrace_rescale_P6X (hc k) (haT k) (hst k).some)
    σ y R hsT has L hRdef hRpos (fun k => (hRx' k).trans (hRle k)) hL hbad hgood hwin hwin' hroom
    hradii
  rw [hclock' k]
  change 1 ≤ (Tn k : ℝ) / r k ^ 2 - 1 ^ 2
  rw [le_sub_iff_add_le, le_div_iff₀ (hc k)]
  linarith [htime k]

/-- **(b) 最小合同 ⇐ S5 + S11 + `hPNS`**（`hPNS` 与 `A` 无关）。 -/
theorem canonicalLateCore_of_normalizedS_P6X3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hPN : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
        (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
        (∀ k, hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k =
          metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
        Tendsto L atTop atTop →
        (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
          (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
          ∀ z : ((Kh k).stageAt v).Carrier,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / Real.sqrt (R k)) →
            4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
            (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
      False) :
    CanonicalLateCore_P6X F ε C1 C2 :=
  fun _ hA => lateCoreAt_of_normalizedS_P6X3 hanti hcan hder hPN hA

end GC.LongTime.Ch11
