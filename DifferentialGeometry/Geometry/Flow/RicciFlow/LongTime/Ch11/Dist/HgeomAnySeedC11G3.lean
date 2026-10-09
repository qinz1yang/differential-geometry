import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.PrefixUniformC11G2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EarlierSeedC11G3

/-!
# eventPrefix 层 `hgeom`，K0 种子时刻 `Tk ≥ s` 任意（S-CH11-HDISTC G2b，后缀 `_C11G3`）

P6PFX uniform 版 `exists_hgeom_eventPrefix_uniform_C11G2` 要 `Te = Tk`（K0 种子时刻 = E 层种子终点）；
`Tk > s` 时 E（horizon `t`）上没有该种子。本文件用 G1 `earlier_seed_small_on_half_depth_C11G3` 把 K 层 K0 种子
`(Tk, pk, r)`（trace `seedTraceK`）半深度回推到 `sK = s`（半径 `r/100`，新时钟 `a' = s − (r/100)²`），
E 层种子取 `Te := s`、`aSeed = s − (r/100)²`、`pe ≈ seedTraceK.point s`（`HEq`）：

* 新前提：K 层种子 `(Tk, aK, pk, seedTraceK)`（`aK = Tk − r²`），`sK ≤ Tk`、半深度 `Tk − r²/2 ≤ sK`、`2r² < Tk`；
  E 层 `aSeed = s − (r/100)²`、`pe` 与 `seedTraceK` 在 `s` 处的点 `HEq`（E 层 trace 唯一，无需另给关系）；
* `hwin` / `hlate` **不再是前提**（`R r² → ∞` 推出）；`hsepWK` 的 scale 阈值用新半径 `3/(r/100)²`；
* 结论 = `exists_hgeom_eventPrefix_uniform_C11G2` 的结论逐字（`ℓ₀` 球半径、`hscal` 仍是前提）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **uniform `ε₀`，eventPrefix 层 `hgeom`，任意 `Tk ≥ s` 的 K0 种子（`_C11G3`）**。 -/
theorem exists_hgeom_uniform_anySeed_C11G3 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (ℓ₀ : ℝ), 0 < ℓ₀ → ℓ₀ ≤ 1 →
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ)
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ),
    let Hs : ℕ → ObservedHistory.{u} :=
      fun n => ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory
    ∀ (Tk aK : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haTk : ∀ n, aK n ≤ Tk n)
      (pk : ∀ n, ((K n).toHistory.stageAt (Tk n)).Carrier)
      (seedTraceK : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aK n))
        ((K n).toHistory.activeStage (Tk n)) ((K n).toHistory.activeStage_mono (haTk n)) (pk n))
      (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (sK : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (_hsK : ∀ n, (sK n : ℝ) = s n) (hsTk : ∀ n, sK n ≤ Tk n) (haK : ∀ n, aK n ≤ sK n)
      (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (has : ∀ n, aSeed n ≤ s n)
      (pe : ∀ n, ((Hs n).stageAt (s n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
        ((Hs n).activeStage (s n)) ((Hs n).activeStage_mono (has n)) (pe n))
      (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R r : ℕ → ℝ), (∀ᶠ n in atTop, 0 < R n) →
      (∀ n, HEq (pe n) ((seedTraceK n).point ((K n).toHistory.activeStage (sK n))
        ((K n).toHistory.activeStage_mono (haK n)) ((K n).toHistory.activeStage_mono (hsTk n)))) →
      (∀ n, (Tk n : ℝ) - r n ^ 2 / 2 ≤ (sK n : ℝ)) → (∀ n, 2 * r n ^ 2 < (Tk n : ℝ)) →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tk n) (pk n) (r n)) →
      (∀ n, (aK n : ℝ) = (Tk n : ℝ) - r n ^ 2) →
      (∀ n, (aSeed n : ℝ) = (s n : ℝ) - (r n / 100) ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
        (x : ((K n).toHistory.stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
          (a₀ + τ') x) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
          ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
            τ < s n →
          ∀ z : ((Hs n).stageAt (s n)).Carrier,
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
              ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
            metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z ≤ C * R n) ∧
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
          ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
            (s n : ℝ) - T / R n ≤ v →
          ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
            ((Hs n).activeStage_mono hvs) x,
          ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
            (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
            (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
          ∀ z : ((Hs n).stage e.castSucc).Carrier,
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
                (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
              ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
            metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C * R n)) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (q n)),
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ C : ℝ, 0 ≤ C → ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
          (s n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ ℓ K : ℝ, 0 < ℓ ∧ K * ℓ ^ 2 ≤ 1 ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
          τ < s n →
        ∀ z : ((Hs n).stageAt (s n)).Carrier,
          (riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
              ((seedTrace n).point ((Hs n).activeStage (s n))
                ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (le_refl (s n)))) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          Real.sqrt (normSq0S ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z 4
            (metricRm04At ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z)) ≤ K * R n) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (s n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)), (v : ℝ) < (Hs n).time e.succ →
        ∀ (he : T₀ n ≤ (Hs n).time e.succ) b,
          (seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
              ((recordsK n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) e) he).static
                b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
            tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
              ((recordsK n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) e) he).static
                b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (s n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        ∀ z : ((Hs n).stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
          (riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          ricciTensor ((Hs n).stageMetric e.castSucc t') z ξ ξ ≤
            (3 / (ℓ / Real.sqrt (R n)) ^ 2) *
              ((Hs n).stageMetric e.castSucc t').inner z ξ ξ) := by
  obtain ⟨ε₀, hε₀, hA⟩ := exists_hgeom_eventPrefix_uniform_C11G2.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro ℓ₀ hℓ₀1 hℓ₀2 K j t hjt htj Hs Tk aK haTk pk seedTraceK s sK hsK hsTk haK aSeed has pe
    seedTrace y R r hR hpe hhalf htime hsmallK hclockK hclock hRr a₀ ha₀ hpinK hscal q T₀ recordsK
    hcanK hacc0 hm hDm hsepWK
  have hshift := fun n => GC.LongTime.Ch11.earlier_seed_small_on_half_depth_C11G3 (haTk n) (pk n)
    (r n) (htime n) (hclockK n) (hsmallK n) (seedTraceK n) (sK n) (haK n) (hsTk n) (hhalf n)
  choose a' haa' hav' tr' hclk' hsm' hR2' hpt' using hshift
  have hRr' : Tendsto (fun n => R n * (r n / 100) ^ 2) atTop atTop := by
    refine ((hRr.atTop_div_const (by norm_num : (0 : ℝ) < 10000)).congr fun n => ?_)
    ring
  have hwin' : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (s n : ℝ) - T / R n := by
    intro T hT
    filter_upwards [hR, hRr'.eventually_ge_atTop T] with n hRn hn
    rw [hclock n]
    have : T / R n ≤ (r n / 100) ^ 2 := by
      rw [div_le_iff₀ hRn]
      linarith
    linarith
  have hlate' : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((s n : ℝ) - T / R n) := by
    intro T hT
    filter_upwards [hR, hRr'.eventually_ge_atTop (T + 1)] with n hRn hn
    have h1 : R n * (2 * (r n / 100) ^ 2) < R n * (s n : ℝ) := by
      refine mul_lt_mul_of_pos_left ?_ hRn
      rw [← hsK n]
      exact hR2' n
    have h2 : R n * ((s n : ℝ) - T / R n) = R n * (s n : ℝ) - T := by
      field_simp
    rw [h2]
    linarith
  exact hA ℓ₀ hℓ₀1 hℓ₀2 K j t hjt htj s pe sK
    (fun n => (seedTraceK n).point ((K n).toHistory.activeStage (sK n))
      ((K n).toHistory.activeStage_mono (haK n)) ((K n).toHistory.activeStage_mono (hsTk n)))
    aSeed has seedTrace s (fun n => le_rfl) has y R (fun n => r n / 100) hR
    (fun n => (hsK n).symm) hpe hsm' hclock hRr' hwin' hlate' ha₀ hpinK hscal q T₀ recordsK hcanK
    hacc0 hm hDm hsepWK

/-- **consumer**：`exists_hgeom_uniform_anySeed_C11G3` 给出与种子无关的 uniform `ε₀`（`ℓ₀` 与种子时刻
`Tk` 都不进 `ε₀`），与 `exists_hgeom_eventPrefix_uniform_C11G2` 同一个来源。 -/
example : ∃ ε₀ : ℝ, 0 < ε₀ := by
  obtain ⟨ε₀, hε₀, -⟩ := exists_hgeom_uniform_anySeed_C11G3.{u}
  exact ⟨ε₀, hε₀⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
