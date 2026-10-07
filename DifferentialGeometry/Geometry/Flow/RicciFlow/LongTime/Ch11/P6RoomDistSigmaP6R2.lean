import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionRetainedP6R2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateCoreP6X

/-!
# `hroom` / `hdistσ` 的 producer 与 `CanonicalLateCore_P6X` 链对接（O-CH11-P6REST2 G2，`_P6R2`）

* `hdistσ_of_retained_P6R2`：G1 的 ball ⑧ + `L = √(R₀ r²)/4` + `R₀ ≤ R` + `R₀ r² → ∞` ⇒ closed 主形
  `false_of_selection_eventSlab_late_closed_Cg_P6S3` 的 `hdistσ` binder 逐字（任意 `Aκ ≥ A + 3`；
  `L/√R ≤ r/4`、eventually `1/√R ≤ r`）。
* `lateCoreAt_of_selected_retained_P6R2` / **`canonicalLateCore_of_selected_retained_P6R2`**：
  `canonicalLateCore_of_selected_P6X` 的副本，selection 换成 G1 `selection_of_bad_sequence_retained_P6R2`；
  gap binder `hP6R` = 旧 `hP6` 的全部前件 **再加** `R ≤ ρ(Tn)⁻²`（selector ④，旧链丢掉）、per-n `hroom`、
  per-n ball、主形形 `hdistσ`（`Aκ := A + 3`）。前件更多 ⇒ 新定理强于旧定理（consumer `example`）。
  闭合 `hP6R` 时 `hroom` / `hdistσ` 逐字交给 closed 主形（`K := fun k => F.tower.history (ind k)`、
  `hKh := rfl`），不再是 binder。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **`hdistσ` producer（`_P6R2`）**：selector 的 ball `d_σ(O_σ, y) < (A+1) r`、`L = √(R₀ r²)/4`、
`R₀ ≤ R`、`R₀ r² → ∞` ⇒ eventually `d_σ(O_σ, y) + (L+1)/√R ≤ Aκ r`（`A + 3 ≤ Aκ`）。结论逐字 =
closed 主形 `hdistσ` binder。 -/
theorem hdistσ_of_retained_P6R2 {Kh : ℕ → ObservedHistory.{u}} {A Aκ : ℝ} (hA : 0 < A)
    (hAκ : A + 3 ≤ Aκ)
    {σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon} {y : ∀ n, ((Kh n).stageAt (σ n)).Carrier}
    {Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon} {haT : ∀ n, aSeed n ≤ Tn n}
    {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)}
    {R R0 r L : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hR0 : ∀ n, 0 < R0 n) (hR0R : ∀ n, R0 n ≤ R n)
    (hLdef : ∀ n, L n = Real.sqrt (R0 n * r n ^ 2) / 4)
    (hdiv : Tendsto (fun n => R0 n * r n ^ 2) atTop atTop)
    (hball : ∀ n, y n ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
      ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
        ((Kh n).activeStage_mono (hsT n))) ((A + 1) * r n)) :
    ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n) := by
  filter_upwards [hdiv.eventually_ge_atTop 1] with n hn
  have hn' : 1 ≤ R0 n * r n ^ 2 := hn
  have hrn := hr n
  have hs0 : 0 < Real.sqrt (R0 n) := Real.sqrt_pos.mpr (hR0 n)
  have hss : Real.sqrt (R0 n) ≤ Real.sqrt (R n) := Real.sqrt_le_sqrt (hR0R n)
  have hs : 0 < Real.sqrt (R n) := hs0.trans_le hss
  have hLn : L n = Real.sqrt (R0 n) * r n / 4 := by
    rw [hLdef n, sqrt_mul_sq_P6X (hR0 n).le hrn]
  have h1 : 1 ≤ Real.sqrt (R0 n) * r n := by
    rw [← sqrt_mul_sq_P6X (hR0 n).le hrn]
    have := Real.sqrt_le_sqrt hn'
    rwa [Real.sqrt_one] at this
  have hbound : (L n + 1) / Real.sqrt (R n) ≤ 5 / 4 * r n := by
    rw [div_le_iff₀ hs, hLn]
    have hsr : Real.sqrt (R0 n) * r n ≤ Real.sqrt (R n) * r n :=
      mul_le_mul_of_nonneg_right hss hrn.le
    nlinarith
  have hd : riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
      ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
        ((Kh n).activeStage_mono (hsT n))) (y n) < ENNReal.ofReal ((A + 1) * r n) := hball n
  have hA1 : 0 ≤ (A + 1) * r n := mul_nonneg (by linarith) hrn.le
  calc _ ≤ ENNReal.ofReal ((A + 1) * r n) + ENNReal.ofReal (5 / 4 * r n) :=
        add_le_add hd.le (ENNReal.ofReal_le_ofReal hbound)
    _ = ENNReal.ofReal ((A + 1) * r n + 5 / 4 * r n) :=
        (ENNReal.ofReal_add hA1 (by linarith)).symm
    _ ≤ ENNReal.ofReal (Aκ * r n) := ENNReal.ofReal_le_ofReal (by nlinarith)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse
open scoped ENNReal

universe u

/-- 单个 `A > 1` 处的 (b) ⇐ retained selection 反证（`_P6R2`）：`lateCoreAt_of_selected_P6X` 的副本，
selection 换 G1 retained 版，gap binder `hP6R` 多收 `R ≤ ρ(Tn)⁻²`、per-n `hroom`、per-n ball、`hdistσ`。 -/
theorem lateCoreAt_of_selected_retained_P6R2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    {A : ℝ} (hA : 1 < A)
    (hP6R : ∀ (ind : ℕ → ℕ),
      let Kh : ℕ → ObservedHistory.{u} := fun k => (F.tower.history (ind k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier)
        (r : ℕ → ℝ), (∀ k, 0 < r k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tn k : ℝ)) →
        (∀ k, 2 * r k ^ 2 < (Tn k : ℝ)) →
        (∀ k, hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) (r k)) →
        (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤
          ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) (r k)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - r k ^ 2) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k = metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k * r k ^ 2) →
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
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - r k ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - r k ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => r k / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, R k ≤ (q.neckRadius (Tn k) ^ 2)⁻¹) →
        (∀ k, (Tn k : ℝ) - r k ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
        (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) ((A + 1) * r k)) →
        (∀ᶠ k in atTop,
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * r k)) →
        False) :
    ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
          K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
          ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ε C1 C2 y,
            W.capTubeHasNeckChart ε := by
  by_contra hcon
  have hk : ∀ k : ℕ, ∃ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (p : ((F.tower.history n).toHistory.stageAt t).Carrier) (r : ℝ)
      (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
      (k : ℝ) + 1 ≤ (t : ℝ) ∧ 2 * r ^ 2 < (t : ℝ) ∧
      hasSmallParabolicCurvature (F.tower.history n).toHistory t p r ∧
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) p r ∧
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
    intro n _ t p r hT ht hs hv x hx hK
    by_contra hW
    exact hk ⟨n, t, p, r, x, hT, ht, hs, hv, hx, hK, hW⟩
  choose ind Tn pT r x hlate htime hsmall hvol hx hK hW using hk
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
  have hRx : ∀ k : ℕ, (k : ℝ) + 1 ≤ metricScalarAt ((F.tower.history (ind k)).toHistory.stageMetric
      ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (x k) * r k ^ 2 := by
    intro k
    have h2 : 0 < r k ^ 2 := by have := hr k; positivity
    have := mul_le_mul_of_nonneg_right (hK k) h2.le
    rwa [mul_assoc, inv_mul_cancel₀ h2.ne', mul_one] at this
  have hRpos0 : ∀ k, 0 < metricScalarAt ((F.tower.history (ind k)).toHistory.stageMetric
      ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (x k) := by
    intro k
    have h2 : 0 < r k ^ 2 := by have := hr k; positivity
    have : 0 < ((k : ℝ) + 1) * (r k ^ 2)⁻¹ := by positivity
    exact this.trans_le (hK k)
  have hdiv : Tendsto (fun k => metricScalarAt ((F.tower.history (ind k)).toHistory.stageMetric
      ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (x k) * r k ^ 2)
      atTop atTop :=
    tendsto_atTop_mono (fun k : ℕ => (by linarith [hRx k] : (k : ℝ) ≤ _))
      tendsto_natCast_atTop_atTop
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hsel := ObservedHistory.selection_of_bad_sequence_retained_P6R2
    (Kh := fun k => (F.tower.history (ind k)).toHistory) (fun _ => q) le_rfl le_rfl le_rfl
    (fun _ => hanti) (fun k => hcan (ind k))
    (fun k v z hlo hhi hR =>
      stageDerivative_of_timeDerivativeSupply_P6X hder (ind k) v z hlo hhi hR)
    Tn pT r A hr hA0 aSeed haT hclock (fun k => (hst k).some) x hx hRpos0
    (fun k hG => hW k hG.1) hdiv
  obtain ⟨σ, y, R, hsT, has, L, ⟨hRdef, hRpos, hRle, hQρ, hL, hbad, hgood, hwin, hwin', hroomT,
    hradii⟩, hLdef, hroom, hball⟩ := hsel
  have hRr : ∀ k : ℕ, (k : ℝ) + 1 ≤ R k * r k ^ 2 := fun k => by
    have h2 : 0 ≤ r k ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_right (hRle k) h2
    linarith [hRx k]
  have hdistσ := ObservedHistory.hdistσ_of_retained_P6R2 (Aκ := A + 3) (haT := haT) (hsT := hsT)
    (has := has) hA0 le_rfl hr hRpos0 hRle hLdef hdiv hball
  exact hP6R ind Tn pT r hr hlate htime hsmall hvol aSeed haT hclock (fun k => (hst k).some) σ y R
    hsT has L hRdef hRpos hRr hL hbad hgood hwin hwin' hroomT hradii hQρ hroom hball hdistσ

/-- **G2 主定理：(b) 最小合同 ⇐ native canonical + native time-derivative + retained selection 缺口
`hP6R`（`_P6R2`）**。`A ≤ 2` 借 `max A 2`（`lateCoreAt_mono_P6X`）。`hP6R` 比
`canonicalLateCore_of_selected_P6X` 的 `hP6` 多四个前件：`R ≤ ρ(Tn)⁻²`、per-n `hroom`、per-n ball
`y ∈ B_σ(O_σ, (A+1) r)`、`hdistσ`（`Aκ := A + 3`）——后两个正是 closed 主形
`false_of_selection_eventSlab_late_closed_Cg_P6S3` 的 `hroom` / `hdistσ` binder。 -/
theorem canonicalLateCore_of_selected_retained_P6R2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hP6R : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
      let Kh : ℕ → ObservedHistory.{u} := fun k => (F.tower.history (ind k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier)
        (r : ℕ → ℝ), (∀ k, 0 < r k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tn k : ℝ)) →
        (∀ k, 2 * r k ^ 2 < (Tn k : ℝ)) →
        (∀ k, hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) (r k)) →
        (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤
          ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) (r k)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - r k ^ 2) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k = metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k * r k ^ 2) →
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
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - r k ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - r k ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => r k / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, R k ≤ (q.neckRadius (Tn k) ^ 2)⁻¹) →
        (∀ k, (Tn k : ℝ) - r k ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
        (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) ((A + 1) * r k)) →
        (∀ᶠ k in atTop,
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * r k)) →
        False) :
    CanonicalLateCore_P6X F ε C1 C2 := by
  intro A hA
  have hA2 : 1 < max A 2 := lt_of_lt_of_le one_lt_two (le_max_right _ _)
  exact lateCoreAt_mono_P6X (lateCoreAt_of_selected_retained_P6R2 hanti hcan hder hA2 (hP6R _ hA2))
    hA (le_max_left _ _)

/-- consumer：retained 链严格强于旧链——`canonicalLateCore_of_selected_P6X`（旧 `hP6`）由本文件主定理
推出（`hP6R` 的四个新前件直接丢弃）。 -/
example : type_of% @canonicalLateCore_of_selected_P6X.{u} := by
  intro P g F q ε C1 C2 Ctime hanti hcan hder hP6
  refine canonicalLateCore_of_selected_retained_P6R2 hanti hcan hder ?_
  intro A hA ind Kh Tn pT r hr hlate htime hsmall hvol aSeed haT hclock seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hbad hgood hwin hwin' hroomT hradii _ _ _ _
  exact hP6 A hA ind Tn pT r hr hlate htime hsmall hvol aSeed haT hclock seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hbad hgood hwin hwin' hroomT hradii

end GC.LongTime.Ch11
