import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HUVSlabGood_P6L3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaRegionalCenterC11Q4

/-!
# U 侧（hUV）的单点生产：区域 κ（seed 中心）+ 三角 / 窗口算术（O-CH11-P6ANCH3 G2，后缀 `_P6L3`）

* `seed_triangle_P6L3`：`d(O, w) ≤ d_σ + L/(2√R)`、`d(w, x) < Rad/√R(w)`、`R ≤ R(w)`、
  `2 max(Rad, 0) ≤ L` ⇒ `d(O, x) ≤ d_σ + L/√R`（witness 项：slice 时刻 `v` 本身不需要 closure）；
* `window_P6L3`：`v ≥ σ + σ₁/R`、`τ ≥ v − B/R(w)`、`max(B, 0) − σ₁ + 1 ≤ X ≤ L` ⇒ `σ − X/R ≤ τ` 且
  `σ − L²/R ≤ τ`（`hgood` / `hwin` 的时间窗口）；
* **`regionalKappa_of_closure_P6L3`**（R-C11-5 D-8）：KAPPA3 `regionalKappa_of_window_center_C11Q4` 的
  逐 history 结论形（`hκR`，`RegionalKappa_C11Q3` 展开体，ObservedHistory 形）在**中心 `c := O_j`**
  （种子 trace 点本身）、`ρU := d_σ.toReal + (L+1)/√R` 上取值：`hUc` ⇐ seed closure
  `d_τ(O_j, x) ≤ d_σ + L/√R`（`< ρU`），`hdistV` ⇐ `d(O, O) = 0` + `d_σ + (L+1)/√R ≤ A r`。
  即 `U ⊆ B_τ(O_τ, A r)` 直接由 seed closure 给出（D-8 的"U 经 hdistV 放进 B(O_v, A₊r)"取 `c = O`）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u

/-- seed 距离的三角形传递（`_P6L3`）。 -/
theorem seed_triangle_P6L3 (H : ObservedHistory.{u}) (j : Fin H.eventCount) (v : ℝ)
    (O w x : (H.stage j.castSucc).Carrier) (dσ : ℝ≥0∞) {L Rad R Rw : ℝ} (hR : 0 < R)
    (hRw : R ≤ Rw) (hL0 : 0 ≤ L) (hRad : 2 * max Rad 0 ≤ L)
    (hw : riemannianEDistOf ((H.event j).incoming.flow.base.metric v) O w ≤
      dσ + ENNReal.ofReal (L / 2 / Real.sqrt R))
    (hx : riemannianEDistOf ((H.event j).incoming.flow.base.metric v) w x <
      ENNReal.ofReal (Rad / Real.sqrt Rw)) :
    riemannianEDistOf ((H.event j).incoming.flow.base.metric v) O x ≤
      dσ + ENNReal.ofReal (L / Real.sqrt R) := by
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hsRw : Real.sqrt R ≤ Real.sqrt Rw := Real.sqrt_le_sqrt hRw
  have hM : 0 ≤ max Rad 0 := le_max_right _ _
  have h1 : Rad / Real.sqrt Rw ≤ max Rad 0 / Real.sqrt R :=
    (div_le_div_of_nonneg_right (le_max_left _ _) (hsR.le.trans hsRw)).trans
      (div_le_div_of_nonneg_left hM hsR hsRw)
  have h2 : L / 2 / Real.sqrt R + max Rad 0 / Real.sqrt R ≤ L / Real.sqrt R := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hsR.le
  calc riemannianEDistOf ((H.event j).incoming.flow.base.metric v) O x
      ≤ riemannianEDistOf ((H.event j).incoming.flow.base.metric v) O w +
          riemannianEDistOf ((H.event j).incoming.flow.base.metric v) w x :=
        riemannianEDistOf_triangle _ _ _ _
    _ ≤ (dσ + ENNReal.ofReal (L / 2 / Real.sqrt R)) +
          ENNReal.ofReal (max Rad 0 / Real.sqrt R) :=
        add_le_add hw (hx.le.trans (ENNReal.ofReal_le_ofReal h1))
    _ = dσ + ENNReal.ofReal (L / 2 / Real.sqrt R + max Rad 0 / Real.sqrt R) := by
        rw [add_assoc, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal h2)

/-- 时间窗口算术（`_P6L3`）：`max(B, 0) − σ₁ + 1 ≤ X`。 -/
theorem window_P6L3 {σ v τ R Rw B σ₁ X L : ℝ} (hR : 0 < R) (hRw : R ≤ Rw)
    (hv : σ + σ₁ / R ≤ v) (hτ : v - B / Rw ≤ τ) (hX : max B 0 - σ₁ + 1 ≤ X) (hX1 : 1 ≤ X)
    (hL : X ≤ L) : σ - X / R ≤ τ ∧ σ - L ^ 2 / R ≤ τ := by
  have hRw0 : 0 < Rw := hR.trans_le hRw
  have hB : B / Rw ≤ max B 0 / R :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hRw0.le).trans
      (div_le_div_of_nonneg_left (le_max_right _ _) hR hRw)
  have hXR : max B 0 / R - σ₁ / R + 1 / R ≤ X / R := by
    rw [← sub_div, ← add_div]
    exact div_le_div_of_nonneg_right hX hR.le
  have h1R : 0 < 1 / R := by positivity
  have hfirst : σ - X / R ≤ τ := by linarith
  refine ⟨hfirst, ?_⟩
  have hL2 : X ≤ L ^ 2 := by nlinarith
  have : X / R ≤ L ^ 2 / R := div_le_div_of_nonneg_right hL2 hR.le
  linarith

/-- **区域 κ ⇐ seed closure（`_P6L3`，D-8 中心取 `c := O_j`）**：KAPPA3 逐 history 结论形 `hκR`（seed
`(Tn, pT, r)`、`A := Aκ`、`ρ`；结论 = `RegionalKappa_C11Q3` 的展开体，`H = K.toHistory` 时定义等同）+
`[a, t]` 上 `U` 的 seed closure + `d_σ + (L+1)/√R ≤ Aκ r` ⇒ 区域 κ（展开体）。 -/
theorem regionalKappa_of_closure_P6L3 (H : ObservedHistory.{u})
    {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (y : (H.stageAt σ).Carrier) {R L r ρ κ Aκ : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hκR : ∀ (j : Fin H.eventCount) (c : (H.stage j.castSucc).Carrier)
      (U : Set (H.stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn : ℝ) - r ^ 2 / 2 ≤ a → t ≤ (Tn : ℝ) →
      (∀ (τ : Icc (0 : ℝ) H.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        H.time j.castSucc < τ → (τ : ℝ) < H.time j.succ →
        ∀ z ∈ U, ∀ zz cc : (H.stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf (H.stageMetric (H.activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) H.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        H.time j.castSucc < τ → (τ : ℝ) < H.time j.succ →
        ∀ (hav : aSeed ≤ τ) (hvt : τ ≤ Tn), ∀ cc : (H.stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf (H.stageMetric (H.activeStage τ) τ)
              (seedTrace.point (H.activeStage τ) (H.activeStage_mono hav)
                (H.activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r)) →
      ∀ (τ : Icc (0 : ℝ) H.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        H.time j.castSucc < τ → (τ : ℝ) < H.time j.succ →
        ∀ z ∈ U, ∀ zz : (H.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρ → H.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (H.stageAt τ).Carrier
              (H.stageMetric (H.activeStage τ) τ)
              (riemannianBallOf (H.stageMetric (H.activeStage τ) τ) zz b))
    (hdσ : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y +
        ENNReal.ofReal ((L + 1) / Real.sqrt R) ≤ ENNReal.ofReal (Aκ * r))
    (j : Fin H.eventCount) (U : Set (H.stage j.castSucc).Carrier) (a t : ℝ)
    (ha : (Tn : ℝ) - r ^ 2 / 2 ≤ a) (ht : t ≤ (Tn : ℝ))
    (h1 : H.activeStage aSeed ≤ j.castSucc) (h2 : j.castSucc ≤ H.activeStage Tn)
    (hcl : ∀ τ : ℝ, a ≤ τ → τ ≤ t → H.time j.castSucc < τ → τ < H.time j.succ → ∀ x ∈ U,
      riemannianEDistOf ((H.event j).incoming.flow.base.metric τ)
          (seedTrace.point j.castSucc h1 h2) x ≤
        riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y +
          ENNReal.ofReal (L / Real.sqrt R)) :
    ∀ (τ : Icc (0 : ℝ) H.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
      H.time j.castSucc < τ → (τ : ℝ) < H.time j.succ →
      ∀ z ∈ U, ∀ zz : (H.stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρ → H.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (H.stageAt τ).Carrier
            (H.stageMetric (H.activeStage τ) τ)
            (riemannianBallOf (H.stageMetric (H.activeStage τ) τ) zz b) := by
  set dσ := riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
    (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
      (H.activeStage_mono hsT)) y with hdσdef
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hL1 : 0 ≤ (L + 1) / Real.sqrt R := div_nonneg (by linarith) hsR.le
  have hfin : dσ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hdσ)
  have hρU : ENNReal.ofReal (dσ.toReal + (L + 1) / Real.sqrt R) =
      dσ + ENNReal.ofReal ((L + 1) / Real.sqrt R) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hL1, ENNReal.ofReal_toReal hfin]
  have hlt : dσ + ENNReal.ofReal (L / Real.sqrt R) <
      ENNReal.ofReal (dσ.toReal + (L + 1) / Real.sqrt R) := by
    rw [hρU]
    refine ENNReal.add_lt_add_left hfin ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_)
    exact div_lt_div_of_pos_right (by linarith) hsR
  refine hκR j (seedTrace.point j.castSucc h1 h2) U a t (dσ.toReal + (L + 1) / Real.sqrt R) ha ht
    ?_ ?_
  · intro τ haτ hτt hτ1 hτ2 z hz zz cc hzz hcc
    have hact : H.activeStage τ = j.castSucc := H.activeStage_eq_of_slab_P6L3 j τ hτ1.le hτ2
    rw [edist_stage_eq_P6L2 j hact τ cc zz _ z hcc hzz]
    exact (hcl τ haτ hτt hτ1 hτ2 z hz).trans_lt hlt
  · intro τ haτ hτt hτ1 hτ2 hav hvt cc hcc
    have hact : H.activeStage τ = j.castSucc := H.activeStage_eq_of_slab_P6L3 j τ hτ1.le hτ2
    have hO := eq_of_heq ((point_heq_of_eq_P6M2 seedTrace hact (H.activeStage_mono hav)
      (H.activeStage_mono hvt) h1 h2).trans hcc.symm)
    rw [hO, riemannianEDistOf_self, zero_add, hρU]
    exact hdσ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
