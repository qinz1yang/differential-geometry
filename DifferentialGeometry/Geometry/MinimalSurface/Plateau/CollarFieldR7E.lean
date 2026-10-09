import DifferentialGeometry.Geometry.Metric.LieDerivative.Cartan
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# O-MY-R7E G3-a：collar 的 level 向量场 `X = −β(ρ) ∇ρ / |∇ρ|²`

R7-E 的 collar level projection（R-MY3 确认的 inward level flow）所用的向量场。给定光滑 `ρ`、
collar `[lo, hi]` 上 `dρ ≠ 0`、`{ρ ≤ hi + η}` 紧，取 `ε > 0` 使 band `[lo − 2ε, hi + 2ε]` 上仍
`|∇ρ|² > 0`（`exists_regular_band_R7E`），bump `β`（`[lo − ε, hi + ε]` 上 `= 1`，支撑在
`[lo − 2ε, hi + 2ε]`），令 `X = φ • ∇ρ`，`φ = −β(ρ) / |∇ρ|²`。性质（`exists_collar_field_R7E`）：

* `X` 是紧支撑光滑截面；
* 处处 `dρ(X) = −β(ρ) ∈ [−1, 0]`，band `[lo − ε, hi + ε]` 上 `dρ(X) = −1`（level flow）；
* `X ∥ ∇ρ`：`dρ(w) = 0 ⇒ G(X, w) = 0`；
* Lie 导数（Cartan + Leibniz + `hessFun_eq_cov_grad`）：band 上对 `w ∈ ker dρ`，
  `L_X G(w, w) = −2 Hess ρ(w, w) / |∇ρ|²`——这就是 R-MY3 的 `d/ds |J_s|² = −2 Hess ρ(J_s, J_s)/|∇ρ|²`。
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter Metric
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]

/-- 实轴上的 collar profile `β`：`[lo − ε, hi + ε]` 上 `= 1`，支撑在 `[lo − 2ε, hi + 2ε]`。 -/
def collarProfile_R7E (lo hi ε : ℝ) (hlohi : lo ≤ hi) (hε : 0 < ε) :
    ContDiffBump ((lo + hi) / 2 : ℝ) :=
  ⟨(hi - lo) / 2 + ε, (hi - lo) / 2 + 2 * ε, by linarith, by linarith⟩

theorem collarProfile_eq_one_R7E {lo hi ε : ℝ} (hlohi : lo ≤ hi) (hε : 0 < ε) {s : ℝ}
    (h1 : lo - ε ≤ s) (h2 : s ≤ hi + ε) : collarProfile_R7E lo hi ε hlohi hε s = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [mem_closedBall, Real.dist_eq, abs_le]
  change -((hi - lo) / 2 + ε) ≤ s - (lo + hi) / 2 ∧ s - (lo + hi) / 2 ≤ (hi - lo) / 2 + ε
  constructor <;> linarith

theorem collarProfile_tsupport_R7E {lo hi ε : ℝ} (hlohi : lo ≤ hi) (hε : 0 < ε) {s : ℝ}
    (hs : s ∈ tsupport (collarProfile_R7E lo hi ε hlohi hε)) : lo - 2 * ε ≤ s ∧ s ≤ hi + 2 * ε := by
  rw [ContDiffBump.tsupport_eq, mem_closedBall, Real.dist_eq, abs_le] at hs
  change -((hi - lo) / 2 + 2 * ε) ≤ s - (lo + hi) / 2 ∧ s - (lo + hi) / 2 ≤ (hi - lo) / 2 + 2 * ε
    at hs
  constructor <;> linarith [hs.1, hs.2]

/-- regular band：`[lo, hi]` 上 `dρ ≠ 0`、`{ρ ≤ hi + η}` 紧 ⇒ 存在 `ε`（`2ε ≤ η`）使
`[lo − 2ε, hi + 2ε]` 上 `|∇ρ|² > 0`。 -/
theorem exists_regular_band_R7E (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {lo hi η : ℝ} (hlohi : lo ≤ hi)
    (hη : 0 < η) (hcpt : IsCompact {x | ρ x ≤ hi + η})
    (hreg : ∀ x, lo ≤ ρ x → ρ x ≤ hi → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ 2 * ε ≤ η ∧ ∀ x, lo - 2 * ε ≤ ρ x → ρ x ≤ hi + 2 * ε →
      0 < normGradSqFun G ρ x := by
  let C : Set N := {x | ρ x ≤ hi + η} ∩ {x | normGradSqFun G ρ x = 0}
  have hCc : IsCompact C :=
    hcpt.inter_right (isClosed_eq (normGradSqFun_continuous G hρ) continuous_const)
  have hK : IsCompact (ρ '' C) := hCc.image hρ.continuous
  have hdisj : Icc lo hi ⊆ (ρ '' C)ᶜ := by
    rintro s ⟨hs1, hs2⟩ ⟨x, ⟨_, hx0⟩, rfl⟩
    exact hreg x hs1 hs2 (normGradSqFun_eq_zero_iff.mp hx0)
  obtain ⟨δ₀, hδ₀, hsub⟩ :=
    (isCompact_Icc (a := lo) (b := hi)).exists_cthickening_subset_open hK.isClosed.isOpen_compl
      hdisj
  refine ⟨min (η / 2) (δ₀ / 2), lt_min (by linarith) (by linarith),
    by linarith [min_le_left (η / 2) (δ₀ / 2)], ?_⟩
  intro x h1 h2
  have hε1 : min (η / 2) (δ₀ / 2) ≤ η / 2 := min_le_left _ _
  have hε2 : min (η / 2) (δ₀ / 2) ≤ δ₀ / 2 := min_le_right _ _
  rcases (normGradSqFun_nonneg G ρ x).lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    have hxC : x ∈ C := ⟨by change ρ x ≤ hi + η; linarith, hzero.symm⟩
    have hmem : ρ x ∈ cthickening δ₀ (Icc lo hi) := by
      apply mem_cthickening_of_dist_le (ρ x) (max lo (min (ρ x) hi)) δ₀ (Icc lo hi)
        ⟨le_max_left _ _, max_le hlohi (min_le_right _ _)⟩
      rw [Real.dist_eq, abs_le]
      constructor
      · rcases le_total (ρ x) hi with h | h
        · rw [min_eq_left h]
          rcases le_total lo (ρ x) with h' | h'
          · rw [max_eq_right h']; linarith
          · rw [max_eq_left h']; linarith
        · rw [min_eq_right h, max_eq_right hlohi]; linarith
      · rcases le_total (ρ x) hi with h | h
        · rw [min_eq_left h]
          rcases le_total lo (ρ x) with h' | h'
          · rw [max_eq_right h']; linarith
          · rw [max_eq_left h']; linarith
        · rw [min_eq_right h, max_eq_right hlohi]; linarith
    exact hsub hmem ⟨x, hxC, rfl⟩

/-- 系数 `φ = −β(ρ) / |∇ρ|²` 光滑：`β ∘ ρ` 的支撑落在 `|∇ρ|² > 0` 处。 -/
theorem contMDiff_collarCoeff_R7E (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hsupp : ∀ x, ρ x ∈ tsupport β → 0 < normGradSqFun G ρ x) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => -β (ρ x) / normGradSqFun G ρ x) := by
  intro x
  by_cases hx : ρ x ∈ tsupport β
  · exact ((hβ.contMDiff.comp hρ).neg.contMDiffAt).div₀
      (normGradSqFun_contMDiff G hρ).contMDiffAt (hsupp x hx).ne'
  · have hopen : IsOpen {y | ρ y ∉ tsupport β} :=
      (isClosed_tsupport β).isOpen_compl.preimage hρ.continuous
    refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy]
    simp



/-- collar 向量场 `X = φ • ∇ρ`，`φ = −β(ρ) / |∇ρ|²`（紧支撑光滑截面）。 -/
def collarField_R7E (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hsupp : ∀ x, ρ x ∈ tsupport β → 0 < normGradSqFun G ρ x) :
    Cₛ^∞⟮𝓘(ℝ, E); E, (TangentSpace 𝓘(ℝ, E) : N → Type _)⟯ :=
  ⟨fun x => (-β (ρ x) / normGradSqFun G ρ x) • gradFun G ρ x,
    (contMDiff_collarCoeff_R7E G hρ hβ hsupp).smul_section
      (Connection.gradFun_contMDiff_total_section G hρ)⟩

section Field

variable (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hsupp : ∀ x, ρ x ∈ tsupport β → 0 < normGradSqFun G ρ x)

theorem collarField_apply_R7E (x : N) :
    collarField_R7E G hρ hβ hsupp x = (-β (ρ x) / normGradSqFun G ρ x) • gradFun G ρ x := rfl

theorem beta_eq_zero_of_normGradSq_eq_zero_R7E {G : SmoothRiemannianMetric 𝓘(ℝ, E) N}
    {ρ : N → ℝ} {β : ℝ → ℝ} (hsupp : ∀ x, ρ x ∈ tsupport β → 0 < normGradSqFun G ρ x)
    {x : N} (hx : normGradSqFun G ρ x = 0) : β (ρ x) = 0 := by
  by_contra hne
  have h := hsupp x (subset_tsupport β hne)
  rw [hx] at h
  exact lt_irrefl _ h

/-- `dρ(X) = −β(ρ)`（处处）。 -/
theorem mfderiv_collarField_R7E (x : N) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x (collarField_R7E G hρ hβ hsupp x) = -β (ρ x) := by
  rw [collarField_apply_R7E, map_smul, ← inner_gradFun G ρ x (gradFun G ρ x)]
  change (-β (ρ x) / normGradSqFun G ρ x) * normGradSqFun G ρ x = -β (ρ x)
  by_cases hn : normGradSqFun G ρ x = 0
  · rw [hn, beta_eq_zero_of_normGradSq_eq_zero_R7E hsupp hn]
    simp
  · field_simp

/-- `X ∥ ∇ρ`：`G(X, w) = φ · G(∇ρ, w)`；特别地 `dρ(w) = 0 ⇒ G(X, w) = 0`。 -/
theorem inner_collarField_R7E (x : N) (w : TangentSpace 𝓘(ℝ, E) x) :
    G.inner x (collarField_R7E G hρ hβ hsupp x) w =
      (-β (ρ x) / normGradSqFun G ρ x) * G.inner x (gradFun G ρ x) w := by
  rw [collarField_apply_R7E, map_smul]
  rfl

theorem inner_collarField_eq_zero_R7E (x : N) (w : TangentSpace 𝓘(ℝ, E) x)
    (hw : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x w = 0) :
    G.inner x (collarField_R7E G hρ hβ hsupp x) w = 0 := by
  rw [inner_collarField_R7E, inner_gradFun, hw]
  exact mul_zero (-β (ρ x) / normGradSqFun G ρ x)

theorem tsupport_collarField_subset_R7E :
    tsupport (collarField_R7E G hρ hβ hsupp : (x : N) → TangentSpace 𝓘(ℝ, E) x) ⊆
      ρ ⁻¹' tsupport β := by
  apply closure_minimal _ ((isClosed_tsupport β).preimage hρ.continuous)
  intro x hx
  by_contra hxs
  apply hx
  change (-β (ρ x) / normGradSqFun G ρ x) • gradFun G ρ x = 0
  rw [image_eq_zero_of_notMem_tsupport hxs]
  simp

/-- Lie 导数（Cartan + Leibniz + `hessFun_eq_cov_grad`）：对 `w ∈ ker dρ`，
`L_X G(w, w) = 2 φ Hess ρ(w, w)`，`φ = −β(ρ) / |∇ρ|²`。 -/
theorem lieDerivMetric_collarField_R7E [T2Space N] (x : N) (w : TangentSpace 𝓘(ℝ, E) x)
    (hw : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x w = 0) :
    PDE.DeTurck.lieDerivMetric G (collarField_R7E G hρ hβ hsupp) x w w =
      2 * ((-β (ρ x) / normGradSqFun G ρ x) * hessFun G ρ x w w) := by
  rw [PDE.RicciFlow.Pullback.cartan_formula_for_lie_deriv_metric]
  set φ : N → ℝ := fun y => -β (ρ y) / normGradSqFun G ρ y with hφ
  have hgrad : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun y : N => TotalSpace.mk' E y (gradFun G ρ y)) x :=
    ((Connection.gradFun_contMDiff_total_section G hρ) x).mdifferentiableAt (by simp)
  have hφd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ x :=
    ((contMDiff_collarCoeff_R7E G hρ hβ hsupp) x).mdifferentiableAt (by simp)
  have hleib := (Connection.LeviCivita G).isCovariantDerivativeOnUniv.leibniz
    (σ := fun y : N => gradFun G ρ y) (g := φ) (x := x) hgrad hφd
  have hcov : (Connection.LeviCivita G)
      (collarField_R7E G hρ hβ hsupp : (y : N) → TangentSpace 𝓘(ℝ, E) y) x w =
      φ x • (Connection.LeviCivita G) (fun y : N => gradFun G ρ y) x w +
        mvfderiv 𝓘(ℝ, E) φ x w • gradFun G ρ x := by
    have h := congrArg (fun D => D w) hleib
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] at h
    exact h
  rw [hcov, G.symm x w, map_add, map_smul, map_smul]
  change φ x * G.inner x ((Connection.LeviCivita G) (fun y : N => gradFun G ρ y) x w) w +
      mvfderiv 𝓘(ℝ, E) φ x w * G.inner x (gradFun G ρ x) w +
    (φ x * G.inner x ((Connection.LeviCivita G) (fun y : N => gradFun G ρ y) x w) w +
      mvfderiv 𝓘(ℝ, E) φ x w * G.inner x (gradFun G ρ x) w) = _
  rw [← Connection.hessFun_eq_cov_grad G hρ x w w, inner_gradFun, hw]
  change φ x * hessFun G ρ x w w + mvfderiv 𝓘(ℝ, E) φ x w * 0 +
    (φ x * hessFun G ρ x w w + mvfderiv 𝓘(ℝ, E) φ x w * 0) = _
  ring

end Field

end DifferentialGeometry.Geometry
