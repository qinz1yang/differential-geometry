import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HstayGuardedSlotsP6HS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HstayPrevThreeCaseP6HS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WindowSeedBaseC11WB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HUVSlabGoodCg_P6LS3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceLateCgLocalP6SD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HpinRescaledP6HI

/-!
# guarded 槽当前 slab 部分 ⇐ WSBASE point-anchor（HSTAY-A4 G7，后缀 `_P6HS`）

lead R14：三情形直付 hderivL⋆ / hgradL⋆。当前 slab（`hgradL⋆` 全部、`hderivL⋆` 第二合取）不需要 trace
stay：守卫点 `(t − v′)·max(Λ R_k, R(t, z)) ≤ c⋆`（`Λ := max 4 Cg`）上的 seed localization 由 WSBASE
`windowSeed_pointAnchor_C11WB`（PROVED，无 binder）逐点给（`q := max(ΛR_k, R(t,z))/Λ`、`β := c⋆/Λ`，同
HARNACK `P6HbcadCGuardedP6HK` 的取法；`pa_*` 数值件逐字副本）；
ExitGuard ⇐ `hmargin`（δ := r/√R_k）+ `z ∈ B_t(p′, r/√R_k)`；
HI ⇐ `hpin_rescaled_of_records_P6HI`（全事件 records）。之后 `deriv_of_hgood_slab_Cg_P6SD` /
`gradient_of_hgood_slab_Cg_P6LS3`（hgood 阈值 `4R_k ≤ Cg R_k`）。
前 slab（`hderivL⋆` 第一合取）此处仍经 binder `hstayPrev`（G3 `hstayStar` 限于 `i′⁻ < (i k)⁻`），G8 三情形付。
生成：build-logs/scratch/HSTAY-A4/gen/gen7.py。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn
open ObservedHistory

/-! ## point-anchor 数值件（HARNACK `P6HbcadCGuardedP6HK` 的 `pa_*` / `budget_*` 逐字副本，改后缀） -/

theorem pa_q_ge_P6HS {Cg Rn X : ℝ} (hCg : 0 < Cg) (_hRn : 0 < Rn) :
    Rn ≤ max (Cg * Rn) X / Cg := by
  rw [le_div_iff₀ hCg, mul_comm]
  exact le_max_left _ _

theorem pa_CgL_P6HS {Cg Rn X : ℝ} (hCg : 0 < Cg) : Cg * Rn ≤ Cg * (max (Cg * Rn) X / Cg) := by
  rw [mul_div_cancel₀ _ hCg.ne']
  exact le_max_left _ _

theorem pa_xv_P6HS {Cg Rn X : ℝ} (hCg : 0 < Cg) : X ≤ Cg * (max (Cg * Rn) X / Cg) := by
  rw [mul_div_cancel₀ _ hCg.ne']
  exact le_max_right _ _

theorem pa_window_P6HS {Cg M v τ cs : ℝ} (hCg : 0 < Cg) (hM : 0 < M) (hg : (v - τ) * M ≤ cs) :
    v - cs / Cg / (M / Cg) ≤ τ := by
  have e : cs / Cg / (M / Cg) = cs / M := by field_simp
  rw [e]
  have : v - τ ≤ cs / M := by rw [le_div_iff₀ hM]; linarith
  linarith

theorem pa_lower_P6HS {Rn q β σ σ₁ v X : ℝ} (hRn : 0 < Rn) (hq : Rn ≤ q) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hv : σ + σ₁ / Rn ≤ v) (hX : 0 ≤ X) :
    σ - (X - σ₁ + 1) / Rn ≤ v - β / q := by
  have h1 : β / q ≤ β / Rn := div_le_div_of_nonneg_left hβ0 hRn hq
  have h2 : (X - σ₁ + 1) / Rn = X / Rn - σ₁ / Rn + 1 / Rn := by ring
  have h3 : β / Rn ≤ 1 / Rn := div_le_div_of_nonneg_right hβ1 hRn.le
  have h4 : 0 ≤ X / Rn := div_nonneg hX hRn.le
  linarith

theorem pa_L_P6HS {Rn L σ X σ₁ : ℝ} (hRn : 0 < Rn) (hL : X - σ₁ + 1 ≤ L)
    (hL1 : 1 ≤ X - σ₁ + 1) : σ - L ^ 2 / Rn ≤ σ - (X - σ₁ + 1) / Rn := by
  have e : X - σ₁ + 1 ≤ L ^ 2 := by nlinarith
  have := div_le_div_of_nonneg_right e hRn.le
  linarith

theorem pa_bud_P6HS {Ct Cg : ℝ} (_hCt : 0 ≤ Ct) (hCg : 0 < Cg) :
    Ct * Cg * (1 / (2 * max Ct 1) / Cg) ≤ 1 / 2 := by
  have hm : 0 < max Ct 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have e : Ct * Cg * (1 / (2 * max Ct 1) / Cg) = Ct / (2 * max Ct 1) := by field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith [le_max_left Ct 1]

theorem budget_mono_P6HS {x e : ℝ≥0∞} {a c s : ℝ} (hac : a ≤ c)
    (hx : x ≤ e + ENNReal.ofReal (a / s)) (hs : 0 ≤ s) : x ≤ e + ENNReal.ofReal (c / s) :=
  hx.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hac hs)))

theorem budget_add_P6HS {x y e : ℝ≥0∞} {a b c s : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a / s)
    (hb : 0 ≤ b / s) (habc : a + b ≤ c) (hx : x ≤ e + ENNReal.ofReal (a / s))
    (hy : y ≤ ENNReal.ofReal (b / s)) : x + y ≤ e + ENNReal.ofReal (c / s) := by
  calc x + y ≤ e + ENNReal.ofReal (a / s) + ENNReal.ofReal (b / s) := add_le_add hx hy
    _ = e + ENNReal.ofReal (a / s + b / s) := by rw [add_assoc, ENNReal.ofReal_add ha hb]
    _ ≤ e + ENNReal.ofReal (c / s) := add_le_add le_rfl (ENNReal.ofReal_le_ofReal
      (by rw [← add_div]; exact div_le_div_of_nonneg_right habc hs))

/-- **`hgradL⋆` ⇐ hgood + hmargin（point-anchor）（`_P6HS`，无 stay binder）**：结论 = G2 gate 孪生
`hgradL` 槽逐字（`Cgrad := C2.toNNReal`）；`4 ≤ Cg`。 -/
theorem hgradLStar_of_anchor_P6HS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {Cg : ℝ} (hCg4 : 4 ≤ Cg)
    (hC2 : 0 ≤ C2) {pF : CutoffParameters}
    (recordsAll : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    (hmargin :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
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
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
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
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ (h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc)
            (h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k)) (δ : ℝ), 0 < δ →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            riemannianEDistOf ((Kh k).stageMetric (i k).castSucc t)
                ((seedTrace k).point (i k).castSucc h1 h2) p' ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal δ) :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
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
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
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
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                Cg * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Ctime : ℝ) 1) →
                ∀ ξ : TangentSpace ThreeModel z,
                  |scalarDifferential ((Kh k).event (i k)).incoming.flow v' z ξ| ≤
                    (C2.toNNReal : ℝ) * ((Kh k).event (i k)).incoming.flow.scalar v' z *
                      Real.sqrt (((Kh k).event (i k)).incoming.flow.scalar v' z) *
                      Real.sqrt
                        ((((Kh k).event (i k)).incoming.flow.base.metric v').inner z ξ ξ) := by
  intro T r hT hr ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hma := hmargin ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = max 4 Cg := ⟨_, rfl⟩
  have hΛ4 : (4 : ℝ) ≤ Λ := hΛdef ▸ le_max_left 4 Cg
  have hΛ0 : 0 < Λ := by linarith
  have hρ0 : 0 < localPropagationRadius C2 := localPropagationRadius_pos hC2
  obtain ⟨ρg, hρgdef⟩ : ∃ ρg : ℝ, ρg = localPropagationRadius C2 / Real.sqrt (2 * Λ) :=
    ⟨_, rfl⟩
  have hρg0 : 0 ≤ ρg := by rw [hρgdef]; positivity
  obtain ⟨Cc, hCcdef⟩ : ∃ Cc : ℝ,
      Cc = max (max 1 (6 * Λ)) (2 * Λ / localPropagationRadius C2 ^ 2) := ⟨_, rfl⟩
  obtain ⟨MC, hMCdef⟩ : ∃ MC : ℝ,
      MC = max 1 (2 * Real.sqrt 3 * (Cc / 2 + max Cc (2 * Real.exp 4))) := ⟨_, rfl⟩
  have hMC1 : 1 ≤ MC := by rw [hMCdef]; exact le_max_left _ _
  have hC1c : 1 ≤ Cc := by rw [hCcdef]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hΛC : 6 * Λ ≤ Cc := by rw [hCcdef]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hρC : 2 * Λ ≤ localPropagationRadius C2 ^ 2 * Cc := by
    have e := le_max_right (max 1 (6 * Λ)) (2 * Λ / localPropagationRadius C2 ^ 2)
    rw [← hCcdef, div_le_iff₀ (by positivity)] at e
    linarith only [e, mul_comm Cc (localPropagationRadius C2 ^ 2)]
  have hm1 : (1 : ℝ) ≤ max (Ctime : ℝ) 1 := le_max_right _ _
  have hβ0 : 0 ≤ 1 / (2 * max (Ctime : ℝ) 1) / Λ := by positivity
  have hβ1 : 1 / (2 * max (Ctime : ℝ) 1) / Λ ≤ 1 := by
    rw [div_le_one hΛ0, div_le_iff₀ (by positivity)]
    nlinarith only [hm1, hΛ4]
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRr (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  filter_upwards [hma, hRlim.eventually_ge_atTop (2500 * MC),
    hL.eventually_ge_atTop (2 + 16 * Real.sqrt MC + 2 * ρg + 4 * r), haS 2 two_pos]
    with k hmk hRk hLk haSk
  intro p' q hq hcross
  have hRk0 := hRpos k
  have hsR : 0 < Real.sqrt (R k) := Real.sqrt_pos.2 hRk0
  have hR1 : (1 : ℝ) ≤ R k := by
    have e1 := hRr k
    have e2 : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith only [e1, e2]
  have hσs : (σ k : ℝ) = (Kh k).time (i k).succ := hi k
  have hcs : (Kh k).time (i k).castSucc < (Kh k).time (i k).succ :=
    (Kh k).time_strictMono Fin.castSucc_lt_succ
  have h2R : 0 < 2 / R k := div_pos two_pos hRk0
  have h1R : 0 < 1 / R k := div_pos one_pos hRk0
  have haσ : (aSeed k : ℝ) < σ k := by linarith only [haSk, h2R]
  have hσT : (σ k : ℝ) ≤ Tn k := Subtype.coe_le_coe.mpr (hsT k)
  have h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc :=
    (Kh k).activeStage_le_castSucc_P6HE (i k) (aSeed k) (by rw [← hσs]; exact haσ)
  have h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k) :=
    (Kh k).le_activeStage (Tn k) (i k).castSucc (by rw [← hσs] at hcs; linarith)
  have hδ : 0 < r / Real.sqrt (R k) := div_pos hr hsR
  filter_upwards [hmk p' q hq hcross h1 h2 _ hδ, Ioo_mem_nhdsLT (show max
      ((Kh k).time (i k).castSucc) ((Kh k).time (i k).succ - 1 / R k) < (Kh k).time (i k).succ
      from max_lt hcs (by linarith only [h1R]))] with t hmt ht
  have ht1 : (Kh k).time (i k).castSucc < t := lt_of_le_of_lt (le_max_left _ _) ht.1
  have ht2 : (σ k : ℝ) + -1 / R k ≤ t := by
    have := lt_of_le_of_lt (le_max_right _ _) ht.1
    rw [neg_div]
    linarith only [this, hσs]
  have htσ : t ≤ (σ k : ℝ) := by rw [hσs]; exact ht.2.le
  have hmt' : riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric t)
      ((seedTrace k).point (i k).castSucc h1 h2) p' ≤
      riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k) +
        ENNReal.ofReal (r / Real.sqrt (R k)) := by
    simpa only [ObservedHistory.stageMetric_castSucc_apply] using hmt
  have hL2 : (2 : ℝ) ≤ L k := by
    have := Real.sqrt_nonneg MC
    linarith only [hLk, this, hρg0, hr]
  -- point-anchor 闭包：守卫点上的 stay
  have hcl : ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
      (r / Real.sqrt (R k)), ∀ v' : ℝ,
      (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
        1 / (2 * max (Ctime : ℝ) 1) → v' ≤ t → (Kh k).time (i k).castSucc < v' →
      ((aSeed k : ℝ) ≤ v' ∧ (σ k : ℝ) - L k ^ 2 / R k ≤ v') ∧
      riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric v')
          ((seedTrace k).point (i k).castSucc h1 h2) z ≤
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) +
          ENNReal.ofReal (L k / Real.sqrt (R k)) := by
    intro z hz v' hg hv't hv'1
    rw [← hΛdef] at hg
    have hMpos : 0 < max (Λ * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) :=
      lt_of_lt_of_le (mul_pos hΛ0 hRk0) (le_max_left _ _)
    have hRq := pa_q_ge_P6HS (X := ((Kh k).event (i k)).incoming.flow.scalar t z) hΛ0 hRk0
    have hlow := pa_lower_P6HS (σ := (σ k : ℝ)) (σ₁ := -1) (X := 0) hRk0 hRq hβ0 hβ1 ht2 le_rfl
    have e2 : ((0 : ℝ) - -1 + 1) / R k = 2 / R k := by norm_num
    rw [e2] at hlow
    have hwτ := pa_window_P6HS hΛ0 hMpos hg
    have hav : (aSeed k : ℝ) ≤ t - 1 / (2 * max (Ctime : ℝ) 1) / Λ /
        (max (Λ * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) / Λ) := haSk.trans hlow
    have hL2R : 2 / R k ≤ L k ^ 2 / R k :=
      div_le_div_of_nonneg_right (by nlinarith only [hL2]) hRk0.le
    have hσL : (σ k : ℝ) - L k ^ 2 / R k ≤ t - 1 / (2 * max (Ctime : ℝ) 1) / Λ /
        (max (Λ * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) / Λ) := by
      linarith only [hlow, hL2R]
    have hlate : 1 ≤ R k * (t - 1 / (2 * max (Ctime : ℝ) 1) / Λ /
        (max (Λ * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) / Λ)) := by
      have e1 : (1 : ℝ) ≤ aSeed k := hone k
      nlinarith only [hR1, e1, hav]
    have hRr' : 2500 * max 1 (2 * Real.sqrt 3 * (Cc / 2 + max Cc (2 * Real.exp 4))) ≤
        R k * 1 ^ 2 := by rw [one_pow, mul_one, ← hMCdef]; exact hRk
    have hLc : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (Cc / 2 + max Cc (2 * Real.exp 4)))) *
        max (1 / (2 * max (Ctime : ℝ) 1) / Λ) 0 ≤ L k - 2 * ρg := by
      rw [← hMCdef]
      have e1 : max (1 / (2 * max (Ctime : ℝ) 1) / Λ) 0 ≤ 1 := max_le hβ1 zero_le_one
      have e3 : 16 * Real.sqrt MC * max (1 / (2 * max (Ctime : ℝ) 1) / Λ) 0 ≤
          16 * Real.sqrt MC := mul_le_of_le_one_right (by positivity) e1
      linarith only [e3, hLk, hr]
    have hρL : L k - 2 * ρg + 2 * (localPropagationRadius C2 / Real.sqrt (2 * Λ)) ≤ L k :=
      le_of_eq (by rw [hρgdef]; ring)
    have hzp : riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric t) p' z ≤
        ENNReal.ofReal (r / Real.sqrt (R k)) := le_of_lt hz
    have hxG := budget_add_P6HS hsR.le hδ.le hδ.le
      (show r + r ≤ (L k - 2 * ρg) / 2 by linarith only [hLk, hρg0, Real.sqrt_nonneg MC]) hmt' hzp
    have hd := ObservedHistory.windowSeed_pointAnchor_C11WB hC2 (Kh k) (haT k) (hsT k) (has k)
      (hsm k) (hclock k) (seedTrace k) (le_refl (0 : ℝ))
      (fun τ x => ObservedHistory.hpin_rescaled_of_records_P6HI F recordsAll ind c hc k τ x)
      (y k) hRk0 (hgood k) (i k) h1 h2 ht.2 hRq hΛ0
      ((mul_le_mul_of_nonneg_right hΛ4 hRk0.le).trans (pa_CgL_P6HS hΛ0))
      (pa_bud_P6HS Ctime.coe_nonneg hΛ0) hC1c hΛC hρC hRr' hLc hρL hav htσ hσL hlate z
      ((riemannianEDistOf_triangle _ _ _ _).trans hxG) (pa_xv_P6HS hΛ0) v' hwτ hv't hv'1
    exact ⟨⟨hav.trans hwτ, hσL.trans hwτ⟩, hd⟩
  intro z hz v' hv' hwin hRv' hg ξ
  obtain ⟨⟨haτ, hLτ⟩, hd⟩ := hcl z hz v' hg hv'.2.le hv'.1
  exact (Kh k).gradient_of_hgood_slab_Cg_P6LS3 hC2 (haT k) (hsT k) (has k) (seedTrace k) (y k)
    (R k) (L k) (hgood k) (i k) v' hv'.1 (hv'.2.trans ht.2) haτ (hv'.2.le.trans htσ) hLτ h1 h2 z
    hd ((mul_le_mul_of_nonneg_right hCg4 hRk0.le).trans hRv'.le) ξ

/-- **`hderivL⋆` ⇐ hgood + hmargin + 天花板级供给 `hsupply`（`_P6HS`，无 stay binder）**：当前 slab 用
WSBASE point-anchor；前 slab 用三情形核 `prevDeriv_threeCase_P6HS`。结论 = G2 gate 孪生 `hderivL` 槽逐字
（`Cder := Ctime`）；`4 ≤ Cg`。 -/
theorem hderivLStar_of_anchor_threeCase_P6HS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {Cg : ℝ} (hCg4 : 4 ≤ Cg)
    (hC2 : 0 ≤ C2) {pF : CutoffParameters}
    (recordsAll : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    (hmargin :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
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
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
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
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ (h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc)
            (h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k)) (δ : ℝ), 0 < δ →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            riemannianEDistOf ((Kh k).stageMetric (i k).castSucc t)
                ((seedTrace k).point (i k).castSucc h1 h2) p' ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal δ)
    (hsupply :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
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
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
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
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∃ (Q : ℝ) (pp : CutoffParameters) (T₀ : ℝ)
          (recs : ∀ e : Fin (Kh k).eventCount, T₀ ≤ (Kh k).time e.succ →
            GeometricCutoffRecord (Kh k) e pp),
          0 < Q ∧
          (∀ e : Fin (Kh k).eventCount, e.castSucc ≤ (i k).castSucc →
            ((Kh k).event e).incoming.DerivativeBoundBefore Ctime Q ((Kh k).time e.succ)) ∧
          T₀ ≤ (σ k : ℝ) - 2 / R k ∧
          (∀ e he b, ((recs e he).static b).hasCanonicalWindow) ∧
          pp.modelAccuracy ≤ 1 / 2 ∧ StandardCap.transitionEnd + 10 < pp.modelRadius ∧
          (∀ (e : Fin (Kh k).eventCount) (he : T₀ ≤ (Kh k).time e.succ)
            (w : ((Kh k).stage e.succ).Carrier),
            (∀ b, metricScalarAt ((Kh k).event e).outputMetric w <
              ((recs e he).static b).neck.scale / 2) →
            ¬ ∃ (b : ((Kh k).event e).RetainedBoundaryIndex)
              (x : standardCapWindow pp.modelRadius),
              w = ((recs e he).static b).window x ∧ ‖x.val‖ < pp.modelRadius) ∧
          (∀ (e : Fin (Kh k).eventCount) (he : T₀ ≤ (Kh k).time e.succ) b,
            (σ k : ℝ) - 2 / R k < (Kh k).time e.succ → e.succ ≤ (i k).castSucc →
            max 6 (8 * Q) < ((recs e he).static b).neck.scale)) :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
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
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
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
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            (∀ (first : Fin ((Kh k).eventCount + 1)) (hfl : first ≤ (i k).castSucc),
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
              ∀ (B : BackwardPointTrace (Kh k) first (i k).castSucc hfl z)
                (i' : Fin (Kh k).eventCount) (hf : first ≤ i'.castSucc)
                (hij : i'.castSucc < (i k).castSucc),
              ∀ v' ∈ Ioo ((Kh k).time i'.castSucc) ((Kh k).time i'.succ), t - T / R k ≤ v' →
                Cg * R k < ((Kh k).event i').incoming.flow.scalar v'
                  (B.point i'.castSucc hf hij.le) →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Ctime : ℝ) 1) →
                |derivWithin (fun w' => ((Kh k).event i').incoming.flow.scalar w'
                    (B.point i'.castSucc hf hij.le)) (Iic v') v'| ≤
                  Ctime * ((Kh k).event i').incoming.flow.scalar v'
                    (B.point i'.castSucc hf hij.le) ^ 2) ∧
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                Cg * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Ctime : ℝ) 1) →
                |derivWithin (fun w' => ((Kh k).event (i k)).incoming.flow.scalar w' z)
                    (Iic v') v'| ≤
                  Ctime * ((Kh k).event (i k)).incoming.flow.scalar v' z ^ 2 := by
  intro T r hT hr ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hma := hmargin ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hsu := hsupply ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = max 4 Cg := ⟨_, rfl⟩
  have hΛ4 : (4 : ℝ) ≤ Λ := hΛdef ▸ le_max_left 4 Cg
  have hΛ0 : 0 < Λ := by linarith
  have hρ0 : 0 < localPropagationRadius C2 := localPropagationRadius_pos hC2
  obtain ⟨ρg, hρgdef⟩ : ∃ ρg : ℝ, ρg = localPropagationRadius C2 / Real.sqrt (2 * Λ) :=
    ⟨_, rfl⟩
  have hρg0 : 0 ≤ ρg := by rw [hρgdef]; positivity
  obtain ⟨Cc, hCcdef⟩ : ∃ Cc : ℝ,
      Cc = max (max 1 (6 * Λ)) (2 * Λ / localPropagationRadius C2 ^ 2) := ⟨_, rfl⟩
  obtain ⟨MC, hMCdef⟩ : ∃ MC : ℝ,
      MC = max 1 (2 * Real.sqrt 3 * (Cc / 2 + max Cc (2 * Real.exp 4))) := ⟨_, rfl⟩
  have hMC1 : 1 ≤ MC := by rw [hMCdef]; exact le_max_left _ _
  have hC1c : 1 ≤ Cc := by rw [hCcdef]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hΛC : 6 * Λ ≤ Cc := by rw [hCcdef]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hρC : 2 * Λ ≤ localPropagationRadius C2 ^ 2 * Cc := by
    have e := le_max_right (max 1 (6 * Λ)) (2 * Λ / localPropagationRadius C2 ^ 2)
    rw [← hCcdef, div_le_iff₀ (by positivity)] at e
    linarith only [e, mul_comm Cc (localPropagationRadius C2 ^ 2)]
  have hm1 : (1 : ℝ) ≤ max (Ctime : ℝ) 1 := le_max_right _ _
  have hβ0 : 0 ≤ 1 / (2 * max (Ctime : ℝ) 1) / Λ := by positivity
  have hβ1 : 1 / (2 * max (Ctime : ℝ) 1) / Λ ≤ 1 := by
    rw [div_le_one hΛ0, div_le_iff₀ (by positivity)]
    nlinarith only [hm1, hΛ4]
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRr (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  filter_upwards [hma, hRlim.eventually_ge_atTop (2500 * MC),
    hL.eventually_ge_atTop (2 + 16 * Real.sqrt MC + 2 * ρg + 4 * r), haS 2 two_pos,
    hsu, hL.eventually_ge_atTop (4 * (r + 8 * (1 / (2 * max (Ctime : ℝ) 1)) /
        min (min (1 / 50) (localPropagationRadius C2 / 2))
          (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4))))) +
        8 * localPropagationRadius C2 + 4 * r + 4)]
    with k hmk hRk hLk haSk hsk hLbig
  intro p' q hq hcross
  have hRk0 := hRpos k
  have hsR : 0 < Real.sqrt (R k) := Real.sqrt_pos.2 hRk0
  have hR1 : (1 : ℝ) ≤ R k := by
    have e1 := hRr k
    have e2 : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith only [e1, e2]
  have hσs : (σ k : ℝ) = (Kh k).time (i k).succ := hi k
  have hcs : (Kh k).time (i k).castSucc < (Kh k).time (i k).succ :=
    (Kh k).time_strictMono Fin.castSucc_lt_succ
  have h2R : 0 < 2 / R k := div_pos two_pos hRk0
  have h1R : 0 < 1 / R k := div_pos one_pos hRk0
  have haσ : (aSeed k : ℝ) < σ k := by linarith only [haSk, h2R]
  have hσT : (σ k : ℝ) ≤ Tn k := Subtype.coe_le_coe.mpr (hsT k)
  have h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc :=
    (Kh k).activeStage_le_castSucc_P6HE (i k) (aSeed k) (by rw [← hσs]; exact haσ)
  have h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k) :=
    (Kh k).le_activeStage (Tn k) (i k).castSucc (by rw [← hσs] at hcs; linarith)
  have hδ : 0 < r / Real.sqrt (R k) := div_pos hr hsR
  filter_upwards [hmk p' q hq hcross h1 h2 _ hδ, Ioo_mem_nhdsLT (show max
      ((Kh k).time (i k).castSucc) ((Kh k).time (i k).succ - 1 / R k) < (Kh k).time (i k).succ
      from max_lt hcs (by linarith only [h1R]))] with t hmt ht
  have ht1 : (Kh k).time (i k).castSucc < t := lt_of_le_of_lt (le_max_left _ _) ht.1
  have ht2 : (σ k : ℝ) + -1 / R k ≤ t := by
    have := lt_of_le_of_lt (le_max_right _ _) ht.1
    rw [neg_div]
    linarith only [this, hσs]
  have htσ : t ≤ (σ k : ℝ) := by rw [hσs]; exact ht.2.le
  have hmt' : riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric t)
      ((seedTrace k).point (i k).castSucc h1 h2) p' ≤
      riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k) +
        ENNReal.ofReal (r / Real.sqrt (R k)) := by
    simpa only [ObservedHistory.stageMetric_castSucc_apply] using hmt
  have hL2 : (2 : ℝ) ≤ L k := by
    have := Real.sqrt_nonneg MC
    linarith only [hLk, this, hρg0, hr]
  -- point-anchor 闭包：守卫点上的 stay
  have hcl : ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
      (r / Real.sqrt (R k)), ∀ v' : ℝ,
      (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
        1 / (2 * max (Ctime : ℝ) 1) → v' ≤ t → (Kh k).time (i k).castSucc < v' →
      ((aSeed k : ℝ) ≤ v' ∧ (σ k : ℝ) - L k ^ 2 / R k ≤ v') ∧
      riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric v')
          ((seedTrace k).point (i k).castSucc h1 h2) z ≤
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) +
          ENNReal.ofReal (L k / Real.sqrt (R k)) := by
    intro z hz v' hg hv't hv'1
    rw [← hΛdef] at hg
    have hMpos : 0 < max (Λ * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) :=
      lt_of_lt_of_le (mul_pos hΛ0 hRk0) (le_max_left _ _)
    have hRq := pa_q_ge_P6HS (X := ((Kh k).event (i k)).incoming.flow.scalar t z) hΛ0 hRk0
    have hlow := pa_lower_P6HS (σ := (σ k : ℝ)) (σ₁ := -1) (X := 0) hRk0 hRq hβ0 hβ1 ht2 le_rfl
    have e2 : ((0 : ℝ) - -1 + 1) / R k = 2 / R k := by norm_num
    rw [e2] at hlow
    have hwτ := pa_window_P6HS hΛ0 hMpos hg
    have hav : (aSeed k : ℝ) ≤ t - 1 / (2 * max (Ctime : ℝ) 1) / Λ /
        (max (Λ * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) / Λ) := haSk.trans hlow
    have hL2R : 2 / R k ≤ L k ^ 2 / R k :=
      div_le_div_of_nonneg_right (by nlinarith only [hL2]) hRk0.le
    have hσL : (σ k : ℝ) - L k ^ 2 / R k ≤ t - 1 / (2 * max (Ctime : ℝ) 1) / Λ /
        (max (Λ * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) / Λ) := by
      linarith only [hlow, hL2R]
    have hlate : 1 ≤ R k * (t - 1 / (2 * max (Ctime : ℝ) 1) / Λ /
        (max (Λ * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) / Λ)) := by
      have e1 : (1 : ℝ) ≤ aSeed k := hone k
      nlinarith only [hR1, e1, hav]
    have hRr' : 2500 * max 1 (2 * Real.sqrt 3 * (Cc / 2 + max Cc (2 * Real.exp 4))) ≤
        R k * 1 ^ 2 := by rw [one_pow, mul_one, ← hMCdef]; exact hRk
    have hLc : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (Cc / 2 + max Cc (2 * Real.exp 4)))) *
        max (1 / (2 * max (Ctime : ℝ) 1) / Λ) 0 ≤ L k - 2 * ρg := by
      rw [← hMCdef]
      have e1 : max (1 / (2 * max (Ctime : ℝ) 1) / Λ) 0 ≤ 1 := max_le hβ1 zero_le_one
      have e3 : 16 * Real.sqrt MC * max (1 / (2 * max (Ctime : ℝ) 1) / Λ) 0 ≤
          16 * Real.sqrt MC := mul_le_of_le_one_right (by positivity) e1
      linarith only [e3, hLk, hr]
    have hρL : L k - 2 * ρg + 2 * (localPropagationRadius C2 / Real.sqrt (2 * Λ)) ≤ L k :=
      le_of_eq (by rw [hρgdef]; ring)
    have hzp : riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric t) p' z ≤
        ENNReal.ofReal (r / Real.sqrt (R k)) := le_of_lt hz
    have hxG := budget_add_P6HS hsR.le hδ.le hδ.le
      (show r + r ≤ (L k - 2 * ρg) / 2 by linarith only [hLk, hρg0, Real.sqrt_nonneg MC]) hmt' hzp
    have hd := ObservedHistory.windowSeed_pointAnchor_C11WB hC2 (Kh k) (haT k) (hsT k) (has k)
      (hsm k) (hclock k) (seedTrace k) (le_refl (0 : ℝ))
      (fun τ x => ObservedHistory.hpin_rescaled_of_records_P6HI F recordsAll ind c hc k τ x)
      (y k) hRk0 (hgood k) (i k) h1 h2 ht.2 hRq hΛ0
      ((mul_le_mul_of_nonneg_right hΛ4 hRk0.le).trans (pa_CgL_P6HS hΛ0))
      (pa_bud_P6HS Ctime.coe_nonneg hΛ0) hC1c hΛC hρC hRr' hLc hρL hav htσ hσL hlate z
      ((riemannianEDistOf_triangle _ _ _ _).trans hxG) (pa_xv_P6HS hΛ0) v' hwτ hv't hv'1
    exact ⟨⟨hav.trans hwτ, hσL.trans hwτ⟩, hd⟩
  have hΛCg : Λ = Cg := by rw [hΛdef]; exact max_eq_right hCg4
  refine ⟨?_, ?_⟩
  · intro first hfl z hz B i' hf hij v' hv' hwin hRv' hg
    obtain ⟨Q, pp, T₀, recs, hQ, hslab, hT₀, hcan, hacc, hDm, hnc, hsep⟩ := hsk
    have hsi : i'.succ ≤ (i k).castSucc := by
      rw [Fin.le_def]
      have h := Fin.lt_def.mp hij
      simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢
      omega
    have hlt : v' < t :=
      lt_of_lt_of_le hv'.2 (((Kh k).time_strictMono.monotone hsi).trans ht1.le)
    have hg' := hg
    rw [← hΛdef] at hg'
    have htv : t - v' ≤ 1 / R k := by
      have htv0 : 0 ≤ t - v' := sub_nonneg.mpr hlt.le
      have h3 : (t - v') * (Λ * R k) ≤ 1 / 2 := by
        have hc1 : 1 / (2 * max (Ctime : ℝ) 1) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith only [hm1]
        exact ((mul_le_mul_of_nonneg_left (le_max_left _ _) htv0).trans hg').trans hc1
      have hpos : 0 ≤ (t - v') * R k := mul_nonneg htv0 hRk0.le
      have h4 := mul_le_mul_of_nonneg_right hΛ4 hpos
      rw [le_div_iff₀ hRk0]
      nlinarith only [h3, h4, hpos, hR1]
    have hv'σ : (σ k : ℝ) - 2 / R k ≤ v' := by
      have e2 : 2 / R k = 1 / R k + 1 / R k := by ring
      have e3 : (σ k : ℝ) + -1 / R k = (σ k : ℝ) - 1 / R k := by ring
      linarith only [ht2, htv, e2, e3]
    have ht2' : (σ k : ℝ) - 1 / R k ≤ t := by
      have e3 : (σ k : ℝ) + -1 / R k = (σ k : ℝ) - 1 / R k := by ring
      linarith only [ht2, e3]
    have hthr : Λ * R k < ((Kh k).event i').incoming.flow.scalar v'
        (B.point i'.castSucc hf hij.le) := by rw [hΛCg]; exact hRv'
    have htσl : t < (σ k : ℝ) := by rw [hσs]; exact ht.2
    exact ObservedHistory.prevDeriv_threeCase_P6HS hC2 (Kh k) (haT k) (hsT k) (has k) (hsm k)
      (hclock k) (hone k) (seedTrace k)
      (fun τ x => ObservedHistory.hpin_rescaled_of_records_P6HI F recordsAll ind c hc k τ x)
      (y k) hR1 (hgood k) (i k) hσs h1 h2 hΛ4 hr hLbig haSk ht1 htσl ht2' hmt' z hz B i' hf hij
      v' hv' hg' hthr hQ hslab recs (hT₀.trans hv'σ) (fun _ => rfl) hcan hacc hDm hnc
      (fun e he b hve he4 => hsep e he b (lt_of_le_of_lt hv'σ hve) he4)
  · intro z hz v' hv' hwin hRv' hg
    obtain ⟨⟨haτ, hLτ⟩, hd⟩ := hcl z hz v' hg hv'.2.le hv'.1
    exact (Kh k).deriv_of_hgood_slab_Cg_P6SD (haT k) (hsT k) (has k) (seedTrace k) (y k)
      (R k) (L k) (hgood k) (i k) v' hv'.1 (hv'.2.trans ht.2) haτ (hv'.2.le.trans htσ) hLτ h1 h2 z
      hd ((mul_le_mul_of_nonneg_right hCg4 hRk0.le).trans hRv'.le)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
