import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollarJacobianR7E
import DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz
import DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacher

/-!
# O-MY-R7E G3-d：collar level projection `R_c` 与面积不增（generic level）

* `exists_collar_levelField_R7E`：从 carrier 假设（`[lo, hi]` 上 `dρ ≠ 0`、`Hess_G ρ > 0`，
  `{ρ ≤ hi + η}` 紧）造出 level field `X`（`CollarFieldR7E`）及其全部性质的打包（不引入新结构）。
* `collarProj_R7E X hXc ρ c y = D_{(ρ y − c)₊} y`：`{ρ ≤ c}` 上是恒等，`[c, b)` 上推到 level `c`。
* `riemannianDiskArea_collarProj_le_R7E`：`G`-Lipschitz 盘 `V`、像在 `{ρ ≤ hi}`、`{ρ ∘ V = c}` 零测
  ⇒ `A_G(R_c ∘ V) ≤ A_G(V)`。逐点：`ρ ∘ V < c` 处 `R_c ∘ V = V`（局部）；`ρ ∘ V > c` 处链式法则 +
  `collarProjection_mfderiv_le_R7E` + `tangentTwoJacobian_le_of_combinations`（`L = 1`）；
  `V` 不可微处零测（树里 Rademacher `ae_mdifferentiableAt_of_riemannian_lipschitz`）。
* `countable_not_null_level_R7E`：对每个连续 `V`，`{c | {ρ ∘ V = c} 非零测}` 可数（generic level）。
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [T2Space N]

/-- 具体 collar level field 的存在与性质（`[lo, hi]` 是严格凸 collar）。 -/
theorem exists_collar_levelField_R7E (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {lo hi η : ℝ} (hlohi : lo ≤ hi)
    (hη : 0 < η) (hcpt : IsCompact {x | ρ x ≤ hi + η})
    (hcoll : ∀ x, lo ≤ ρ x → ρ x ≤ hi → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun G ρ x v v) :
    ∃ (X : Cₛ^∞⟮𝓘(ℝ, E); E, (TangentSpace 𝓘(ℝ, E) : N → Type _)⟯)
      (_ : IsCompact (tsupport (X : (x : N) → TangentSpace 𝓘(ℝ, E) x)))
      (β : ℝ → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y (X y) = -β (ρ y)) ∧ (∀ r, 0 ≤ β r) ∧
      (∀ r, β r ≤ 1) ∧ (∀ r, lo - ε ≤ r → r ≤ hi + ε → β r = 1) ∧
      (∀ y (w : TangentSpace 𝓘(ℝ, E) y), mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y w = 0 →
        G.inner y (X y) w = 0) ∧
      ∀ x, lo ≤ ρ x → ρ x ≤ hi → ∀ w : TangentSpace 𝓘(ℝ, E) x,
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x w = 0 → PDE.DeTurck.lieDerivMetric G X x w w ≤ 0 := by
  obtain ⟨ε, hε, hεη, hband⟩ := exists_regular_band_R7E G hρ hlohi hη hcpt
    (fun x h1 h2 => (hcoll x h1 h2).1)
  let β := collarProfile_R7E lo hi ε hlohi hε
  have hsupp : ∀ x, ρ x ∈ tsupport β → 0 < normGradSqFun G ρ x := fun x hx =>
    hband x (collarProfile_tsupport_R7E hlohi hε hx).1 (collarProfile_tsupport_R7E hlohi hε hx).2
  let X := collarField_R7E G hρ β.contDiff hsupp
  have hXc : IsCompact (tsupport (X : (x : N) → TangentSpace 𝓘(ℝ, E) x)) := by
    apply hcpt.of_isClosed_subset (isClosed_tsupport _)
    intro x hx
    have h := collarProfile_tsupport_R7E hlohi hε (tsupport_collarField_subset_R7E G hρ
      β.contDiff hsupp hx)
    change ρ x ≤ hi + η
    linarith [h.2]
  refine ⟨X, hXc, β, ε, hε, mfderiv_collarField_R7E G hρ β.contDiff hsupp,
    fun r => β.nonneg' r, fun r => β.le_one, fun r h1 h2 => collarProfile_eq_one_R7E hlohi hε h1 h2,
    inner_collarField_eq_zero_R7E G hρ β.contDiff hsupp, ?_⟩
  intro x h1 h2 w hw
  rw [lieDerivMetric_collarField_R7E G hρ β.contDiff hsupp x w hw]
  have hn : 0 < normGradSqFun G ρ x := hband x (by linarith) (by linarith)
  have hβx : 0 ≤ β (ρ x) := β.nonneg' _
  have hH : 0 ≤ hessFun G ρ x w w := by
    by_cases hw0 : w = 0
    · subst hw0
      simp
    · exact ((hcoll x h1 h2).2 w hw0).le
  have hφ : -β (ρ x) / normGradSqFun G ρ x ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hn.le
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hφ hH]

/-- collar level projection：`R_c y = D_{(ρ y − c)₊} y`。 -/
def collarProj_R7E (X : Cₛ^∞⟮𝓘(ℝ, E); E, (TangentSpace 𝓘(ℝ, E) : N → Type _)⟯)
    (hXc : IsCompact (tsupport (X : (x : N) → TangentSpace 𝓘(ℝ, E) x))) (ρ : N → ℝ) (c : ℝ)
    (y : N) : N :=
  collarFlow_R7E X hXc (max (ρ y - c) 0) y

section Projection

variable (X : Cₛ^∞⟮𝓘(ℝ, E); E, (TangentSpace 𝓘(ℝ, E) : N → Type _)⟯)
  (hXc : IsCompact (tsupport (X : (x : N) → TangentSpace 𝓘(ℝ, E) x)))

theorem continuous_collarProj_R7E {ρ : N → ℝ} (hρc : Continuous ρ) (c : ℝ) :
    Continuous (collarProj_R7E X hXc ρ c) :=
  (continuous_collarFlow_joint_R7E X hXc).comp
    (((hρc.sub continuous_const).max continuous_const).prodMk continuous_id)

theorem collarProj_of_le_R7E {ρ : N → ℝ} {c : ℝ} {y : N} (h : ρ y ≤ c) :
    collarProj_R7E X hXc ρ c y = y := by
  unfold collarProj_R7E
  rw [max_eq_right (by linarith)]
  exact collarFlow_zero_R7E X hXc y

theorem collarProj_of_ge_R7E {ρ : N → ℝ} {c : ℝ} {y : N} (h : c ≤ ρ y) :
    collarProj_R7E X hXc ρ c y = collarFlow_R7E X hXc (ρ y - c) y := by
  unfold collarProj_R7E
  rw [max_eq_left (by linarith)]

theorem collarProj_eventuallyEq_self_R7E {ρ : N → ℝ} (hρc : Continuous ρ) {c : ℝ} {y : N}
    (h : ρ y < c) : collarProj_R7E X hXc ρ c =ᶠ[𝓝 y] id := by
  filter_upwards [(isOpen_lt hρc continuous_const).mem_nhds h] with z hz
  exact collarProj_of_le_R7E X hXc (le_of_lt hz)

theorem collarProj_eventuallyEq_flow_R7E {ρ : N → ℝ} (hρc : Continuous ρ) {c : ℝ} {y : N}
    (h : c < ρ y) :
    collarProj_R7E X hXc ρ c =ᶠ[𝓝 y] fun z => collarFlow_R7E X hXc (ρ z - c) z := by
  filter_upwards [(isOpen_lt continuous_const hρc).mem_nhds h] with z hz
  exact collarProj_of_ge_R7E X hXc (le_of_lt hz)

variable (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
  {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {β : ℝ → ℝ}
  (hdρ : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y (X y) = -β (ρ y))
  (hβ0 : ∀ r, 0 ≤ β r) (hβ1 : ∀ r, β r ≤ 1) {a b : ℝ}
  (hβeq : ∀ r, a ≤ r → r ≤ b → β r = 1)

include hρ hdρ hβ0 hβ1 hβeq in
/-- `c ≤ ρ y ≤ b`、`a ≤ c` ⇒ `ρ (R_c y) = c`。 -/
theorem rho_collarProj_R7E {c : ℝ} (hac : a ≤ c) {y : N} (hcy : c ≤ ρ y) (hyb : ρ y ≤ b) :
    ρ (collarProj_R7E X hXc ρ c y) = c := by
  rw [collarProj_of_ge_R7E X hXc hcy,
    rho_collarFlow_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hyb (by linarith) (by linarith)]
  ring

include hρ hdρ hβ0 hβ1 hβeq in
/-- `ρ ∘ R_c = min ρ c`（`a ≤ c`、`ρ y ≤ b`）。 -/
theorem rho_collarProj_le_R7E {c : ℝ} (hac : a ≤ c) {y : N} (hyb : ρ y ≤ b) :
    ρ (collarProj_R7E X hXc ρ c y) ≤ c := by
  rcases le_total (ρ y) c with h | h
  · rw [collarProj_of_le_R7E X hXc h]
    exact h
  · exact (rho_collarProj_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hac h hyb).le

include hρ hdρ hβ0 hβ1 hβeq in
/-- **面积不增**（generic level）：`G`-Lipschitz 盘 `V`、像在 `{ρ ≤ hi}`（`hi < b`）、
`{ρ ∘ V = c}` 在闭盘上零测、`[lo, hi]` 上 `L_X G ≤ 0` on `ker dρ`（`lo ≤ c`）⇒
`A_G(R_c ∘ V) ≤ A_G(V)`。 -/
theorem riemannianDiskArea_collarProj_le_R7E [T3Space N]
    (hperp : ∀ y (w : TangentSpace 𝓘(ℝ, E) y), mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y w = 0 →
      G.inner y (X y) w = 0)
    {lo hi c : ℝ} (hac : a < c) (hlo : lo ≤ c) (hhi : hi < b)
    (hlie : ∀ x, lo ≤ ρ x → ρ x ≤ hi → ∀ w : TangentSpace 𝓘(ℝ, E) x,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x w = 0 → PDE.DeTurck.lieDerivMetric G X x w w ≤ 0)
    {V : closedDisk → N} {L : ℝ≥0}
    (hV : ∀ z w, riemannianEDistOf G (V z) (V w) ≤ (L : ℝ≥0∞) * edist z w)
    (hVhi : ∀ z, ρ (V z) ≤ hi)
    (hnull : volume ({z : ℂ | ρ (diskExtension V z) = c} ∩ Metric.closedBall 0 1) = 0) :
    riemannianDiskArea G (collarProj_R7E X hXc ρ c ∘ V) ≤ riemannianDiskArea G V := by
  set U : ℂ → N := diskExtension V with hU
  have hUL := diskExtension_riemannian_lipschitz G hV
  have hUc : Continuous U := continuous_of_riemannian_lipschitz G hUL
  have hint : IntegrableOn (riemannianAreaDensity G U) (Metric.closedBall 0 1) :=
    integrable_riemannianDiskAreaDensity G hV
  have hRU : diskExtension (collarProj_R7E X hXc ρ c ∘ V) = collarProj_R7E X hXc ρ c ∘ U := rfl
  unfold riemannianDiskArea riemannianArea
  rw [hRU]
  by_cases hint' : IntegrableOn (riemannianAreaDensity G (collarProj_R7E X hXc ρ c ∘ U))
    (Metric.closedBall 0 1)
  swap
  · rw [integral_undef hint']
    exact integral_nonneg fun z => riemannianAreaDensity_nonneg G U z
  apply setIntegral_mono_ae_restrict hint' hint
  have hdiff : ∀ᵐ z ∂(volume.restrict (Metric.closedBall (0 : ℂ) 1)),
      MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z :=
    ae_restrict_of_ae (ae_mdifferentiableAt_of_riemannian_lipschitz G hUL)
  have hne : ∀ᵐ z ∂(volume.restrict (Metric.closedBall (0 : ℂ) 1)), ρ (U z) ≠ c := by
    rw [ae_iff, Measure.restrict_apply']
    · simpa only [ne_eq, not_not] using hnull
    · exact measurableSet_closedBall
  filter_upwards [hdiff, hne] with z hzd hzc
  have hUz : ρ (U z) ≤ hi := hVhi _
  rcases lt_or_gt_of_ne hzc with hlt | hgt
  · apply le_of_eq
    apply riemannianAreaDensity_congr
    have h := (collarProj_eventuallyEq_self_R7E X hXc hρ.continuous hlt).comp_tendsto
      hUc.continuousAt
    exact h
  · have hev := (collarProj_eventuallyEq_flow_R7E X hXc hρ.continuous hgt).comp_tendsto
      hUc.continuousAt
    rw [riemannianAreaDensity_congr G hev]
    set R : N → N := fun y => collarFlow_R7E X hXc (ρ y - c) y with hR
    have hRd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) R (U z) := by
      have hshift : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞ (fun y : N => (ρ y - c, y)) :=
        (hρ.sub contMDiff_const).prodMk contMDiff_id
      exact (((contMDiff_collarFlow_joint_R7E X hXc).comp hshift) (U z)).mdifferentiableAt
        (by simp)
    have hcomp := mfderiv_comp z hRd hzd
    unfold riemannianAreaDensity
    change tangentTwoJacobian G (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (R ∘ U) z (1 : ℂ))
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (R ∘ U) z Complex.I) ≤ _
    rw [hcomp]
    have hle := tangentTwoJacobian_le_of_combinations G G
      (v := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (1 : ℂ))
      (w := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z Complex.I)
      (v' := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) R (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (1 : ℂ)))
      (w' := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) R (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z Complex.I))
      (L := 1) zero_le_one (fun α γ => by
        rw [one_mul, ← map_smul, ← map_smul, ← map_add]
        apply Real.sqrt_le_sqrt
        exact collarProjection_mfderiv_le_R7E X hXc G hρ hdρ hβ0 hβ1 hβeq hperp hac hgt.le
          (by linarith) (fun x h1 h2 w hw => hlie x (by linarith) (by linarith) w hw) _)
    simp only [one_pow, one_mul] at hle
    exact hle

end Projection

omit [T2Space N] in
/-- generic level：连续盘 `V`，`{c | {ρ ∘ V = c} 在闭盘上非零测}` 可数。 -/
theorem countable_not_null_level_R7E {ρ : N → ℝ} (hρc : Continuous ρ) {V : closedDisk → N}
    (hV : Continuous V) :
    {c : ℝ | volume ({z : ℂ | ρ (diskExtension V z) = c} ∩ Metric.closedBall 0 1) ≠ 0}.Countable :=
    by
  have hg : Measurable fun z : ℂ => ρ (diskExtension V z) :=
    (hρc.comp (hV.comp diskRetraction_lipschitz.continuous)).measurable
  have h := Measure.countable_meas_level_set_pos
    (μ := volume.restrict (Metric.closedBall (0 : ℂ) 1)) hg
  refine h.mono fun c hc => ?_
  change 0 < (volume.restrict (Metric.closedBall (0 : ℂ) 1)) {z | ρ (diskExtension V z) = c}
  rw [Measure.restrict_apply' measurableSet_closedBall]
  exact pos_iff_ne_zero.mpr hc

omit [T2Space N] in
/-- 区间里总有 generic level。 -/
theorem exists_null_level_R7E {ρ : N → ℝ} (hρc : Continuous ρ) {V : closedDisk → N}
    (hV : Continuous V) {c₁ c₂ : ℝ} (h : c₁ < c₂) :
    ∃ c ∈ Ioo c₁ c₂,
      volume ({z : ℂ | ρ (diskExtension V z) = c} ∩ Metric.closedBall 0 1) = 0 := by
  by_contra hcon
  have hsub : Ioo c₁ c₂ ⊆
      {c : ℝ | volume ({z : ℂ | ρ (diskExtension V z) = c} ∩ Metric.closedBall 0 1) ≠ 0} :=
    fun c hc h0 => hcon ⟨c, hc, h0⟩
  have h0 := measure_mono_null hsub ((countable_not_null_level_R7E hρc hV).measure_zero volume)
  rw [Real.volume_Ioo] at h0
  exact absurd h0 (by simp [h])

end DifferentialGeometry.Geometry
