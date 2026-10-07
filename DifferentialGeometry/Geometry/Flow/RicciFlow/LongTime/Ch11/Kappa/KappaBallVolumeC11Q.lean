import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaContractsC11Q

/-!
# K6 `controlled_ball_volume_from_reduced_volume` 由树内定理给出（O-CH11-KAPPA G3，后缀 `_C11Q`）

树内 `historyReducedVolumeLocalUpperBound_holds`（`Surgery/ReducedVolume/LocalUpperBound:31`）：
`∃ C₀ > 0, ∀ η > 0, ∃ σ ∈ (0, 1]`，对每个 retained-core history 与每个受控球 `P(x, t, ϱ, −ϱ²)`，
`Ṽ_{(t,x)}(v = σϱ) ≤ C₀/(σϱ)³ · Vol B(x, ϱ) + η`——核心 + 球外 Gaussian 尾部都在树内处理。
它的 `σ` 只依赖 `η`；审稿要求的 `σ_η ϱ² ≤ τ⋆ = θ r²` 用**缩小测试球**得到：对 `λ = min 1 √θ`，在
`B(x, λϱ)`（仍受控）上用树内上界，再 `Vol B(x, λϱ) ≤ Vol B(x, ϱ)`：
`σ_η = (σλ)²`、`C_η = C₀/(σλ)³`，`σ_η ϱ² ≤ λ²ϱ² ≤ θ r²`。

* `controlledBallVolumeFromReducedVolume_holds_C11Q : ∀ θ > 0, K6 θ`——**K6 不再是前提**；
* `localKappaWide_of_seedReducedVolume_C11Q`：K5 ⇒ `LocalKappaWideSupply_C11Q`（同一 `nr`，无 K6 前提）；
* `localKappa_of_K0_to_K5_C11Q`：G1 链去掉 `hK6`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- **K6（树内已证）**：对每个 `θ > 0`，`ControlledBallVolumeFromReducedVolume_C11Q θ` 成立。 -/
theorem controlledBallVolumeFromReducedVolume_holds_C11Q (θ : ℝ) (hθ : 0 < θ) :
    ControlledBallVolumeFromReducedVolume_C11Q.{u} θ := by
  obtain ⟨C₀, hC₀, hupper⟩ := historyReducedVolumeLocalUpperBound_holds.{u}
  intro η hη
  obtain ⟨σ, hσ, hσ1, hU⟩ := hupper η hη
  set lam : ℝ := min 1 (Real.sqrt θ) with hlam
  have hlam0 : 0 < lam := lt_min one_pos (Real.sqrt_pos.2 hθ)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hlamθ : lam ^ 2 ≤ θ := by
    have h := pow_le_pow_left₀ hlam0.le (min_le_right 1 (Real.sqrt θ)) 2
    rwa [Real.sq_sqrt hθ.le] at h
  refine ⟨(σ * lam) ^ 2, C₀ / (σ * lam) ^ 3, by positivity, by positivity, ?_⟩
  intro R t x ϱ r hϱ hϱr hball
  have hsmall : R.toHistory.isParabolicallyRmControlledBall t x (lam * ϱ) :=
    hball.mono_radius R.toHistory (mul_pos hlam0 hϱ) (mul_le_of_le_one_left hϱ.le hlam1)
  have h := hU R t x (lam * ϱ) hsmall
  have hprod : 0 ≤ σ * (lam * ϱ) := by positivity
  have hsqrt : Real.sqrt ((σ * lam) ^ 2 * ϱ ^ 2) = σ * (lam * ϱ) := by
    rw [show (σ * lam) ^ 2 * ϱ ^ 2 = (σ * (lam * ϱ)) ^ 2 by ring]
    exact Real.sqrt_sq hprod
  constructor
  · unfold redVolTau_C11Q
    rw [hsqrt]
    refine h.trans ?_
    have hcoef : C₀ / (σ * (lam * ϱ)) ^ 3 = C₀ / (σ * lam) ^ 3 / ϱ ^ 3 := by
      field_simp
    rw [hcoef]
    gcongr
    exact measure_mono (riemannianBallOf_mono _ _ (mul_le_of_le_one_left hϱ.le hlam1))
  · calc
      (σ * lam) ^ 2 * ϱ ^ 2 ≤ 1 * θ * r ^ 2 := by
        have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
        have hϱ2 : ϱ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hϱ.le hϱr 2
        calc
          (σ * lam) ^ 2 * ϱ ^ 2 = σ ^ 2 * lam ^ 2 * ϱ ^ 2 := by ring
          _ ≤ 1 * θ * r ^ 2 := by gcongr
      _ = θ * r ^ 2 := by ring

/-- **K5 ⇒ 局部 κ（上沿 `L r`）**：G1 的 `localKappaWide_of_reducedVolume_C11Q` 去掉 K6 前提。 -/
theorem localKappaWide_of_seedReducedVolume_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr v : ℝ → ℝ}
    (hK5 : SeedReducedVolumeLower_C11Q F δ α nr v) :
    LocalKappaWideSupply_C11Q F δ α nr :=
  localKappaWide_of_reducedVolume_C11Q hK5 controlledBallVolumeFromReducedVolume_holds_C11Q

/-- **G1 链去掉 `hK6`**：`K0 → K1 → K2 → K3 → K4 → K5 → LocalKappaWideSupply_C11Q`（同一 `nr`）。 -/
theorem localKappa_of_K0_to_K5_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₂ Λ C₄ v : ℝ → ℝ}
    (hK0 : SeedPatchTransport_C11Q.{u})
    (hK1 : ∀ n, AdmissibleLCalculus_C11Q (F.tower.history n))
    (hK2 : (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      LocalizedLCutoffInequality_C11Q F nr C₂)
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hK4 : LocalizedLCutoffInequality_C11Q F nr C₂ → SurgeryActionBarrier_C11Q F δ α nr Λ →
      BoundedReducedLengthNearSeed_C11Q F δ α nr C₄)
    (hK5 : SeedPatchTransport_C11Q.{u} → (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      BoundedReducedLengthNearSeed_C11Q F δ α nr C₄ → SeedReducedVolumeLower_C11Q F δ α nr v) :
    LocalKappaWideSupply_C11Q F δ α nr :=
  localKappa_of_K0_to_K6_C11Q hK0 hK1 hK2 hK3 hK4 hK5
    controlledBallVolumeFromReducedVolume_holds_C11Q

/-- consumer（G3）：K5 ⇒ P6B 的 `hKappaLocal`（同一 `nr`），K6 由树内给出。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr v : ℝ → ℝ}
    (hK5 : SeedReducedVolumeLower_C11Q F δ α nr v) :
    LocalKappaSupply_P6B F δ α nr :=
  (localKappaWide_of_seedReducedVolume_C11Q hK5).toP6B

end GC.LongTime.Ch11
