import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KDataSuppliedP6D
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionP6X

/-!
# P6 反证顶层：event 内部类的 selected 坏点序列 ⇒ 主形 ⇒ False（O-CH11-P6SEL G1，后缀 `_P6X`）

`false_of_selected_eventInterior_P6X`：主形 `false_of_selection_eventSlab_Kdata_supplied_P6D` 的
`j t yG hjt htj hσ hyG hRn`（event slab 识别）由**位置类** `hpos`
（`exists_strictMono_interior_or_boundary_P6S` 的第一类）经 `eventInterior_data_P6X` 给出；
`hqR` 拆成 `hRlt : n+1 < R n`
（子列重索引，`exists_strictMono_succ_lt_or_bdd_P6X`）与 `hQR : Q n < R n`（K 层数据的导数阈值；发现 F2：
坏点 `R ≤ ρ(σ)⁻²`，故 `Q` 须低于 canonical 阈值）；`hnotK`（records 通用形）由 **`hcwp`**
（"cap-window 点 ⇒ Good"，records 的 standard-cap 接近 ⇒ canonical witness + 导数）与 `hsel` 读出：
坏点若是 `CapWindowPoint` 则 Good，矛盾。

**显式缺口 binder**（本定理不证）：K 层数据 `hinitK hcanon hΛδ hacc hrad hord hδ hρ hslabK`
（P6DATA 已核出全体-events 形对 chain 不成立；P6LATE late 形落地后换底座）、`hQR`、`hcwp`、
Pre841 `d`（κ 线 `pre841Data_of_three_C11KD`）、`hdist`（P6ANCH2 hdistC + (α)）、`hslice`
（P6ANCH2 G3 切片二分）。selection 组 `Tn aSeed … hgood hwin hsel` 由 `selection_of_bad_sequence_P6X` 给。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **event 内部类 selected 坏点序列 ⇒ False（`_P6X`）**：见文件头。 -/
theorem false_of_selected_eventInterior_P6X :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0},
      {K : ℕ → RetainedCoreHistory.{u}} →
      {Q : ℕ → ℝ} → {p₀ : ℕ → CutoffParameters} → {δb ρb : ℕ → ℝ} →
      (hinitK : ∀ n, Nonempty (InitialIdentification P₀ g₀ (K n).toHistory)) →
      (hcanon : ∀ n, (K n).hasCanonicalCutoffRecords (p₀ n) (δb n) (ρb n)) →
      (hΛδ : ∀ n, (p₀ n).recenterConstant * δb n ≤ 1 / 2) →
      (hacc : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p₀ n).modelRadius) →
      (hord : ∀ n : ℕ, n + 2 ≤ (p₀ n).modelOrder) →
      (hδ : ∀ n : ℕ, δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hρ : ∀ n : ℕ, 0 < ρb n ∧
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) * (2 * ρb n ^ 2) ≤ 1) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (hpos : ∀ n, ∃ j : Fin (Kh n).eventCount, (Kh n).time j.castSucc < (σ n : ℝ) ∧
        (σ n : ℝ) < (Kh n).time j.succ) →
      (R : ℕ → ℝ) →
      (hRdef : ∀ n, R n =
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)) →
      (hRpos : ∀ n, 0 < R n) →
      (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n) → (hQR : ∀ n, Q n < R n) →
      (hcwp : ∀ (n : ℕ) (p : CutoffParameters)
        (records : ∀ i, GeometricCutoffRecord (K n).toHistory i p),
        (K n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) records →
        ∀ (j' : Fin (K n).eventCount) (yG' : ((K n).stage j'.castSucc).Carrier),
          HEq (y n) yG' →
          (K n).CapWindowPoint records j'.castSucc yG' (σ n) ((n : ℝ) + 1)
            (1 - 1 / ((n : ℝ) + 2)) →
          (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      (d : GC.LongTime.Ch11.Pre841Data_C11K Kh σ y R hRpos) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (hL : Tendsto L atTop atTop) →
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
          4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
          (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hslice : ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
        Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
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
                      (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False := by
  obtain ⟨η₃, Cup, Lc, hη₃, hCup, hLc, epsW, hepsW, hB⟩ :=
    false_of_selection_eventSlab_Kdata_supplied_P6D.{u}
  refine ⟨η₃, Cup, Lc, hη₃, hCup, hLc, epsW, hepsW,
    fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro P₀ g₀ Ctime K Q p₀ δb ρb hinitK hcanon hΛδ hacc hrad hord hδ hρ hslabK Kh hKh σ y hpos R
    hRdef hRpos hRlt hQR hcwp d Tn aSeed haT hsT has pT seedTrace L hL hgood hwin hdist hslice
    hsel
  subst hKh
  have hev := RetainedCoreHistory.eventInterior_data_P6X σ y hpos
  obtain ⟨j, yG, hjt, htj, hyG, hsc⟩ := hev
  have hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) :=
    fun n => (hRdef n).trans (hsc n)
  have hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) <
      ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) := fun n => by
    rw [← hRn n]
    exact max_lt (hRlt n) (hQR n)
  have hnotK : ∀ (n : ℕ) (p : CutoffParameters)
      (records : ∀ i, GeometricCutoffRecord (K n).toHistory i p),
      (K n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) records →
      ¬ (K n).CapWindowPoint records (j n).castSucc (yG n) (σ n) ((n : ℝ) + 1)
        (1 - 1 / ((n : ℝ) + 2)) :=
    fun n p records hfam hC => hsel n (hcwp n p records hfam (j n) (yG n) (hyG n) hC)
  exact hB' hC1 hC2 hCt (t := fun n => (σ n : ℝ)) hjt htj hinitK hcanon hΛδ hacc hrad hord hδ hρ
    hslabK hqR hnotK _ rfl σ y R (fun _ => rfl) hyG hRn hRpos d Tn aSeed haT hsT has pT seedTrace
    L hL hgood hwin hdist hslice hsel

/-- **consumer（G1）**：坏点序列经 selection（`selection_of_bad_sequence_P6X`）与 `hqR` 重索引
（`exists_strictMono_succ_lt_or_bdd_P6X`）后，要么有子列 `ψ` 使 `n+1 < R(ψ n)` 且主形窗口 `hwin`
沿 `ψ` 成立（进主形的 (U) 支），要么选出点标量沿尾有界（(Bd) 支，D-17 normalization 缺口）。 -/
theorem selected_split_P6X {Kh : ℕ → ObservedHistory.{u}} (q : ℕ → CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : ∀ n, AntitoneOn (q n).neckRadius (Ici 0))
    (hcanonical : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hderivative : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      (Kh n).time ((Kh n).activeStage v) < (v : ℝ) → (v : ℝ) < (Kh n).horizon →
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z ^ 2)
    (Tn : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (r : ℕ → ℝ) (A : ℝ) (hr : ∀ n, 0 < r n) (hA : 0 < A)
    (aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (haSeed : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (x : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (hx : ∀ n, x n ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n))
      (pT n) (A * r n))
    (hR : ∀ n, 0 < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (x n))
    (hbad : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (Tn n) (x n))
    (hdiv : Tendsto (fun n => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n))
      (Tn n)) (x n) * r n ^ 2) atTop atTop) :
    ∃ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (R : ℕ → ℝ),
      (∀ n, 0 < R n) ∧
      ((∃ ψ : ℕ → ℕ, StrictMono ψ ∧ (∀ n : ℕ, (n : ℝ) + 1 < R (ψ n)) ∧
          ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed (ψ n) : ℝ) ≤ σ (ψ n) - T / R (ψ n)) ∨
        ∃ M : ℝ, ∀ᶠ k in atTop, R k ≤ M) := by
  have hsel := selection_of_bad_sequence_P6X q hC1 hC2 hCtime hanti hcanonical hderivative Tn pT
    r A hr hA aSeed haT haSeed seedTrace x hx hR hbad hdiv
  obtain ⟨σ, y, R, hsT, has, L, -, hRpos, -, -, -, -, -, hwin, -, -, -⟩ := hsel
  refine ⟨σ, R, hRpos, ?_⟩
  rcases exists_strictMono_succ_lt_or_bdd_P6X R with ⟨ψ, hψ, hlt⟩ | hbdd
  · exact Or.inl ⟨ψ, hψ, hlt, fun T hT => hψ.tendsto_atTop.eventually (hwin T hT)⟩
  · exact Or.inr hbdd

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
