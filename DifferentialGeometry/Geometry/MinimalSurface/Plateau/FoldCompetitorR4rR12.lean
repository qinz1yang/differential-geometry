import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TowerEngineR12
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.FoldCompetitorSeamR4C

/-!
# S-MY-R12 G4：R4r `reparametrized_fold_competitor_R12`（由 S-MY-R4C 同胚缩放 chart 证明）

scratch `MYD3/R10R14.lean` 的 R4r 合同 `reparametrized_fold_competitor_MYD3`（`reparametrized fold ⇒
严格更小、同 trace 的 Lipschitz competitor`）在源码树里不是新合同，而是 S-MY-R4C
`exists_better_competitor_of_fold_seam_R4C` 的特例
（`[T2Space M]` + charted ⇒ locally compact ⇒ `T3Space`）：`HasReparametrizedFold_R12 g a U₀` 的 seam
`[p - R, p + R]` 与 sheet `a`、`a ∘ conj`（`ψᵢ` reparametrize 到 `U₀`）在半盘 `closedHalfDisk p R` 上，
而 R4C 要的是 `sourceChart` `χ`（`χ '' D̄ ⊆ D°`）下的 chart sheet。取**同胚缩放**
`χ z = c z`（`‖p‖ + R < c < 1`）：

* `homPD_R12 c`：`PartialDiffeomorph`（`source = univ`），`χ '' D̄ ⊆ D°`；
* 新 seam 点 `p / c`、半径 `R / c`；`χ` 把 `closedHalfDisk (p / c) (R / c)` 映入 `closedHalfDisk p R`；
* sheet `a ∘ χ`、`a ∘ χ ∘ conj = (a ∘ conj) ∘ χ`：`C¹`、differential 单射（`D(F ∘ χ) = c • D F`）；
* `ψᵢ' = ψᵢ ∘ χ`：`C^∞`、differential 双射、`EqOn` 逐点；
* fold 条件：Gram 公式的 inward conormal 对 tangent 向量同时数乘 `c > 0` 不变（齐次度 0），
  所以 `η₊ + η₋ ≠ 0` 原样传递。

于是 `HasReparametrizedFold_R12` 的 R4r 是**已证定理**（`[T2Space M]`；`W = univ`），G2
`prepared_least_area_embedded_R12` 的 `hR4r` 前提可由它 discharge。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

/-- 实数缩放 `z ↦ c • z` 作为 `ℂ` 上的连续线性同构（`c ≠ 0`）。 -/
def homCLE_R12 (c : ℝ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.equivOfInverse (c • ContinuousLinearMap.id ℝ ℂ)
    (c⁻¹ • ContinuousLinearMap.id ℝ ℂ)
    (fun z => by simp [hc]) (fun z => by simp [hc])

theorem homCLE_R12_apply (c : ℝ) (hc : c ≠ 0) (z : ℂ) : homCLE_R12 c hc z = (c : ℂ) * z := by
  simp [homCLE_R12, Complex.real_smul]

/-- 同胚缩放作为 `PartialDiffeomorph`（`source = univ`）。 -/
def homPD_R12 (c : ℝ) (hc : c ≠ 0) : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ :=
  (homCLE_R12 c hc).toDiffeomorph.toPartialDiffeomorph

theorem homPD_R12_apply (c : ℝ) (hc : c ≠ 0) (z : ℂ) : (homPD_R12 c hc : ℂ → ℂ) z = (c : ℂ) * z :=
  homCLE_R12_apply c hc z

theorem homPD_R12_source (c : ℝ) (hc : c ≠ 0) : (homPD_R12 c hc).source = univ := rfl


section Deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem mfderiv_homPD_R12 (c : ℝ) (hc : c ≠ 0) (z v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (homPD_R12 c hc : ℂ → ℂ) z v = (c : ℂ) * v := by
  have h : (homPD_R12 c hc : ℂ → ℂ) = (homCLE_R12 c hc : ℂ →L[ℝ] ℂ) := rfl
  rw [h, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  exact homCLE_R12_apply c hc v

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem partialWithin_comp_homPD_R12 {F : ℂ → M} {H H' : Set ℂ} (c : ℝ) (hc : c ≠ 0) {z : ℂ}
    (hF : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H (homPD_R12 c hc z))
    (hmaps : MapsTo (homPD_R12 c hc : ℂ → ℂ) H' H) (hU : UniqueMDiffWithinAt 𝓘(ℝ, ℂ) H' z)
    (v : ℂ) :
    (partialWithin (E := E) (F ∘ (homPD_R12 c hc : ℂ → ℂ)) H' z v : E) =
      c • (partialWithin (E := E) F H (homPD_R12 c hc z) v : E) := by
  have hχ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (homPD_R12 c hc : ℂ → ℂ) z :=
    ((homPD_R12 c hc).contMDiffOn_toFun.contMDiffAt (by simp [homPD_R12_source])).mdifferentiableAt
      (by simp)
  have hχw : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (homPD_R12 c hc : ℂ → ℂ) H' z :=
    hχ.mdifferentiableWithinAt
  unfold partialWithin
  rw [mfderivWithin_comp z hF hχw hmaps hU, mfderivWithin_eq_mfderiv hU hχ]
  have hv : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (homPD_R12 c hc : ℂ → ℂ) z v = (c : ℂ) * v :=
    mfderiv_homPD_R12 c hc z v
  have hv' : ((c : ℂ) * v) = c • v := (Complex.real_smul).symm
  change (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H (homPD_R12 c hc z))
    ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (homPD_R12 c hc : ℂ → ℂ) z) v) =
      c • (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H (homPD_R12 c hc z)) v
  rw [hv, hv']
  exact map_smul (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H (homPD_R12 c hc z)) c v


/-- Gram 公式的 conormal 对 tangent 向量同时数乘 `c > 0` 不变（齐次度 `0`）。 -/
theorem conormal_formula_smul_R12
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M) (T N : TangentSpace 𝓘(ℝ, E) x) {c : ℝ}
    (hc : 0 < c) :
    (Real.sqrt (g.inner x (c • T) (c • T)) * tangentTwoJacobian g (c • T) (c • N))⁻¹ •
        (g.inner x (c • T) (c • T) • (c • N) - g.inner x (c • T) (c • N) • (c • T)) =
      (Real.sqrt (g.inner x T T) * tangentTwoJacobian g T N)⁻¹ •
        (g.inner x T T • N - g.inner x T N • T) := by
  have hc2 : Real.sqrt (c ^ 2) = c := Real.sqrt_sq hc.le
  have h1 : g.inner x (c • T) (c • T) = c ^ 2 * g.inner x T T := by
    simp only [map_smul, smul_apply, smul_eq_mul]; ring
  have h2 : g.inner x (c • T) (c • N) = c ^ 2 * g.inner x T N := by
    simp only [map_smul, smul_apply, smul_eq_mul]; ring
  have h3 : g.inner x (c • N) (c • N) = c ^ 2 * g.inner x N N := by
    simp only [map_smul, smul_apply, smul_eq_mul]; ring
  have hJ : tangentTwoJacobian g (c • T) (c • N) = c ^ 2 * tangentTwoJacobian g T N := by
    unfold tangentTwoJacobian
    rw [h1, h2, h3]
    have : c ^ 2 * g.inner x T T * (c ^ 2 * g.inner x N N) - (c ^ 2 * g.inner x T N) ^ 2 =
        (c ^ 2) ^ 2 * (g.inner x T T * g.inner x N N - g.inner x T N ^ 2) := by ring
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg c)]
  rw [h1, h2, hJ, Real.sqrt_mul (sq_nonneg _), hc2]
  have hv : (c ^ 2 * g.inner x T T) • c • N - (c ^ 2 * g.inner x T N) • c • T =
      c ^ 3 • (g.inner x T T • N - g.inner x T N • T) := by
    simp only [smul_sub, smul_smul]
    congr 2 <;> ring
  rw [hv, smul_smul]
  congr 1
  have hc0 : c ≠ 0 := hc.ne'
  have : c * Real.sqrt (g.inner x T T) * (c ^ 2 * tangentTwoJacobian g T N) =
      c ^ 3 * (Real.sqrt (g.inner x T T) * tangentTwoJacobian g T N) := by ring
  rw [this, mul_inv]
  field_simp

theorem inwardConormalWithin_comp_homPD_R12
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F : ℂ → M} {H H' : Set ℂ} {c : ℝ} (hc : 0 < c)
    {z : ℂ}
    (h1 : (partialWithin (E := E) (F ∘ (homPD_R12 c hc.ne' : ℂ → ℂ)) H' z 1 : E) =
      c • (partialWithin (E := E) F H (homPD_R12 c hc.ne' z) 1 : E))
    (hI : (partialWithin (E := E) (F ∘ (homPD_R12 c hc.ne' : ℂ → ℂ)) H' z Complex.I : E) =
      c • (partialWithin (E := E) F H (homPD_R12 c hc.ne' z) Complex.I : E)) :
    (inwardConormalWithin g (F ∘ (homPD_R12 c hc.ne' : ℂ → ℂ)) H' z : E) =
      (inwardConormalWithin g F H (homPD_R12 c hc.ne' z) : E) := by
  unfold inwardConormalWithin gramWithin densityWithin
  rw [h1, hI]
  exact conormal_formula_smul_R12 g _ _ _ hc

theorem inwardConormalWithin_comp_homPD_of_mdiff_R12
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F : ℂ → M} {H H' : Set ℂ} {c : ℝ} (hc : 0 < c)
    {z : ℂ} (hF : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H (homPD_R12 c hc.ne' z))
    (hmaps : MapsTo (homPD_R12 c hc.ne' : ℂ → ℂ) H' H)
    (hU : UniqueMDiffWithinAt 𝓘(ℝ, ℂ) H' z) :
    (inwardConormalWithin g (F ∘ (homPD_R12 c hc.ne' : ℂ → ℂ)) H' z : E) =
      (inwardConormalWithin g F H (homPD_R12 c hc.ne' z) : E) :=
  inwardConormalWithin_comp_homPD_R12 g hc (partialWithin_comp_homPD_R12 c hc.ne' hF hmaps hU 1)
    (partialWithin_comp_homPD_R12 c hc.ne' hF hmaps hU Complex.I)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem mfderivWithin_comp_homPD_R12 {F : ℂ → M} {H H' : Set ℂ} {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hF : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H (homPD_R12 c hc.ne' z))
    (hmaps : MapsTo (homPD_R12 c hc.ne' : ℂ → ℂ) H' H)
    (hU : UniqueMDiffWithinAt 𝓘(ℝ, ℂ) H' z) (v : ℂ) :
    (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (F ∘ (homPD_R12 c hc.ne' : ℂ → ℂ)) H' z) v =
      c • (show ℂ →L[ℝ] E from
        mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H (homPD_R12 c hc.ne' z)) v :=
  partialWithin_comp_homPD_R12 c hc.ne' hF hmaps hU v

end Deriv

section HalfDisk

theorem hom_mem_closedHalfDisk_R12 {c : ℝ} (hc : 0 < c) {p R : ℝ} {z : ℂ}
    (hz : z ∈ closedHalfDisk (p / c) (R / c)) : (c : ℂ) * z ∈ closedHalfDisk p R := by
  obtain ⟨him, hd⟩ := hz
  have him' : 0 ≤ z.im := him
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have e : (c : ℂ) * z - (p : ℂ) = (c : ℂ) * (z - ((p / c : ℝ) : ℂ)) := by
    push_cast
    field_simp
  refine ⟨?_, ?_⟩
  · change 0 ≤ ((c : ℂ) * z).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_nonneg hc.le him'
  · rw [Metric.mem_closedBall, dist_eq_norm, e, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hc.le]
    have := Metric.mem_closedBall.mp hd
    rw [dist_eq_norm] at this
    calc c * ‖z - ((p / c : ℝ) : ℂ)‖ ≤ c * (R / c) := mul_le_mul_of_nonneg_left this hc.le
      _ = R := by field_simp

theorem hom_mem_openHalfDisk_R12 {c : ℝ} (hc : 0 < c) {p R : ℝ} {z : ℂ}
    (hz : z ∈ (openHalfDisk (p / c) (R / c) : Set ℂ)) :
    (c : ℂ) * z ∈ (openHalfDisk p R : Set ℂ) := by
  obtain ⟨him, hd⟩ := hz
  have him' : 0 < z.im := him
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have e : (c : ℂ) * z - (p : ℂ) = (c : ℂ) * (z - ((p / c : ℝ) : ℂ)) := by
    push_cast
    field_simp
  refine ⟨?_, ?_⟩
  · change 0 < ((c : ℂ) * z).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos hc him'
  · rw [Metric.mem_ball, dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
    have := Metric.mem_ball.mp hd
    rw [dist_eq_norm] at this
    calc c * ‖z - ((p / c : ℝ) : ℂ)‖ < c * (R / c) := mul_lt_mul_of_pos_left this hc
      _ = R := by field_simp

theorem uniqueMDiffOn_closedHalfDisk_R12 (p : ℝ) {r : ℝ} (hr : 0 < r) :
    UniqueMDiffOn 𝓘(ℝ, ℂ) (closedHalfDisk p r) := by
  apply UniqueDiffOn.uniqueMDiffOn
  apply uniqueDiffOn_convex ((convex_halfSpace_im_ge 0).inter (convex_closedBall (p : ℂ) r))
  have hopen : (openHalfDisk p r : Set ℂ) ⊆ interior (closedHalfDisk p r) := by
    intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    exact mem_of_superset ((openHalfDisk p r).isOpen.mem_nhds hz)
      (fun q hq => ⟨(show 0 < q.im from hq.1).le, Metric.ball_subset_closedBall hq.2⟩)
  refine ⟨(p : ℂ) + (r / 2 : ℂ) * Complex.I, hopen ?_⟩
  constructor
  · change 0 < ((p : ℂ) + (r / 2 : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
      Complex.div_ofNat_re, Complex.ofReal_re, zero_add]
    positivity
  · rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
      norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
    rw [abs_of_pos hr]
    linarith

end HalfDisk

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem contMDiff_homPD_R12 (c : ℝ) (hc : c ≠ 0) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (homPD_R12 c hc : ℂ → ℂ) :=
  (homCLE_R12 c hc).contDiff.contMDiff

theorem bijective_mfderiv_homPD_R12 (c : ℝ) (hc : c ≠ 0) (z : ℂ) :
    Function.Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (homPD_R12 c hc : ℂ → ℂ) z) := by
  have h : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (homPD_R12 c hc : ℂ → ℂ) z : ℂ → ℂ) =
      (homCLE_R12 c hc : ℂ → ℂ) := by
    funext v
    exact (mfderiv_homPD_R12 c hc z v).trans (homCLE_R12_apply c hc v).symm
  have hb : Function.Bijective (homCLE_R12 c hc : ℂ → ℂ) := (homCLE_R12 c hc).bijective
  rw [← h] at hb
  exact hb

theorem homPD_conj_R12 (c : ℝ) (hc : c ≠ 0) (z : ℂ) :
    (homPD_R12 c hc : ℂ → ℂ) (conj z) = conj ((homPD_R12 c hc : ℂ → ℂ) z) := by
  rw [homPD_R12_apply, homPD_R12_apply, map_mul, Complex.conj_ofReal]

theorem inwardConormalWithin_congr_fun_R12
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U V : ℂ → M}
    (S : Set ℂ) (z : ℂ) (h : U = V) :
    (inwardConormalWithin g U S z : E) = (inwardConormalWithin g V S z : E) := by
  subst h
  rfl

theorem inwardConormalWithin_congr_pt_R12
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (S : Set ℂ) {z w : ℂ} (h : z = w) :
    (inwardConormalWithin g U S z : E) = (inwardConormalWithin g U S w : E) := by
  subst h
  rfl

end Main

section Adapter

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- 缩放换元保持 sheet 的 differential 单射。 -/
theorem injective_mfderivWithin_comp_homPD_R12 {F : ℂ → M} {c : ℝ} (hc : 0 < c) {p R : ℝ}
    (hR : 0 < R) (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F (closedHalfDisk p R))
    (hiF : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F (closedHalfDisk p R) z)) :
    ∀ z ∈ closedHalfDisk (p / c) (R / c), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (F ∘ (homPD_R12 c hc.ne' : ℂ → ℂ))
        (closedHalfDisk (p / c) (R / c)) z) := by
  have hmapsC : MapsTo (homPD_R12 c hc.ne' : ℂ → ℂ) (closedHalfDisk (p / c) (R / c))
      (closedHalfDisk p R) := fun z hz => by
    rw [homPD_R12_apply]
    exact hom_mem_closedHalfDisk_R12 hc hz
  intro z hz v w hvw
  have hFd : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F (closedHalfDisk p R)
      (homPD_R12 c hc.ne' z) := (hF.mdifferentiableOn (by simp)) _ (hmapsC hz)
  have hU := uniqueMDiffOn_closedHalfDisk_R12 (p / c) (div_pos hR hc) z hz
  have e1 := mfderivWithin_comp_homPD_R12 (F := F) hc hFd hmapsC hU v
  have e2 := mfderivWithin_comp_homPD_R12 (F := F) hc hFd hmapsC hU w
  have hvw' : (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
      (F ∘ (homPD_R12 c hc.ne' : ℂ → ℂ)) (closedHalfDisk (p / c) (R / c)) z) v =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
      (F ∘ (homPD_R12 c hc.ne' : ℂ → ℂ)) (closedHalfDisk (p / c) (R / c)) z) w := hvw
  rw [e1, e2] at hvw'
  exact hiF _ (hmapsC hz) (smul_right_injective E hc.ne' hvw')

omit [ChartedSpace E M] in
/-- 缩放换元保持 `ψ` 的 differential 双射。 -/
theorem bijective_mfderiv_comp_homPD_R12 {c : ℝ} (hc : 0 < c) {p R : ℝ} {ψ : ℂ → ℂ}
    (hψ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ (openHalfDisk p R))
    (hbψ : ∀ z ∈ (openHalfDisk p R : Set ℂ),
      Function.Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ z)) :
    ∀ z ∈ (openHalfDisk (p / c) (R / c) : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (ψ ∘ (homPD_R12 c hc.ne' : ℂ → ℂ)) z) := by
  intro z hz
  have hmem : (homPD_R12 c hc.ne' : ℂ → ℂ) z ∈ (openHalfDisk p R : Set ℂ) := by
    rw [homPD_R12_apply]
    exact hom_mem_openHalfDisk_R12 hc hz
  have hdψ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ (homPD_R12 c hc.ne' z) :=
    (hψ.contMDiffAt ((openHalfDisk p R).isOpen.mem_nhds hmem)).mdifferentiableAt (by simp)
  have hdχ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (homPD_R12 c hc.ne' : ℂ → ℂ) z :=
    (contMDiff_homPD_R12 c hc.ne').contMDiffAt.mdifferentiableAt (by simp)
  rw [mfderiv_comp z hdψ hdχ]
  exact (hbψ _ hmem).comp (bijective_mfderiv_homPD_R12 c hc.ne' z)

variable [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- fold 和 `η₊ + cast η₋ ≠ 0` 只依赖两个向量在 `E` 里的值。 -/
theorem fold_sum_ne_zero_of_eq_R12 {x y x' y' : M} (u : TangentSpace 𝓘(ℝ, E) x)
    (v : TangentSpace 𝓘(ℝ, E) y) (u' : TangentSpace 𝓘(ℝ, E) x') (v' : TangentSpace 𝓘(ℝ, E) y')
    (hu : (u' : E) = (u : E)) (hv : (v' : E) = (v : E))
    (h : u + tangentSpaceCast 𝓘(ℝ, E) y x v ≠ 0) :
    u' + tangentSpaceCast 𝓘(ℝ, E) y' x' v' ≠ 0 := by
  intro h0
  apply h
  have h1 : (show E from u') + (show E from v') = 0 := h0
  have h2 : (show E from u) + (show E from v) = 0 := by
    rw [← hu, ← hv]
    exact h1
  exact h2

/-- 缩放换元下 sheet 的 conormal 不变（seam 点 `p ↦ p / c`）。 -/
theorem conormal_comp_homPD_one_R12 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F : ℂ → M} {c : ℝ}
    (hc : 0 < c) {p R : ℝ}
    (hR : 0 < R) (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F (closedHalfDisk p R)) :
    (inwardConormalWithin g (F ∘ (homPD_R12 c hc.ne' : ℂ → ℂ))
      (closedHalfDisk (p / c) (R / c)) ((p / c : ℝ) : ℂ) : E) =
      (inwardConormalWithin g F (closedHalfDisk p R) (p : ℂ) : E) := by
  have hRc : 0 < R / c := div_pos hR hc
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hmapsC : MapsTo (homPD_R12 c hc.ne' : ℂ → ℂ) (closedHalfDisk (p / c) (R / c))
      (closedHalfDisk p R) := fun z hz => by
    rw [homPD_R12_apply]
    exact hom_mem_closedHalfDisk_R12 hc hz
  have hp'H : ((p / c : ℝ) : ℂ) ∈ closedHalfDisk (p / c) (R / c) :=
    ⟨by simp, by simpa using hRc.le⟩
  have hU := uniqueMDiffOn_closedHalfDisk_R12 (p / c) hRc _ hp'H
  have hχp' : (homPD_R12 c hc.ne' : ℂ → ℂ) ((p / c : ℝ) : ℂ) = (p : ℂ) := by
    rw [homPD_R12_apply]
    push_cast
    field_simp
  have hFd : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F (closedHalfDisk p R)
      (homPD_R12 c hc.ne' ((p / c : ℝ) : ℂ)) := (hF.mdifferentiableOn (by simp)) _ (hmapsC hp'H)
  exact (inwardConormalWithin_comp_homPD_of_mdiff_R12 g hc hFd hmapsC hU).trans
    (inwardConormalWithin_congr_pt_R12 g F (closedHalfDisk p R) hχp')

/-- 缩放换元把 seam 点处的 fold 条件原样搬到新坐标（`p ↦ p / c`）。 -/
theorem fold_ne_zero_comp_homPD_R12 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {a : C(closedDisk, M)}
    {c : ℝ} (hc : 0 < c) {p R : ℝ} (hR : 0 < R)
    (hs1 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension a) (closedHalfDisk p R))
    (hs2 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension a ∘ conj) (closedHalfDisk p R))
    (hfd : inwardConormalWithin g (diskExtension a) (closedHalfDisk p R) (p : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension a ∘ conj) (p : ℂ)) (diskExtension a (p : ℂ))
        (inwardConormalWithin g (diskExtension a ∘ conj) (closedHalfDisk p R) (p : ℂ)) ≠ 0) :
    inwardConormalWithin g (diskExtension a ∘ (homPD_R12 c hc.ne' : ℂ → ℂ))
        (closedHalfDisk (p / c) (R / c)) ((p / c : ℝ) : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E)
        ((diskExtension a ∘ (homPD_R12 c hc.ne' : ℂ → ℂ) ∘ conj) ((p / c : ℝ) : ℂ))
        ((diskExtension a ∘ (homPD_R12 c hc.ne' : ℂ → ℂ)) ((p / c : ℝ) : ℂ))
        (inwardConormalWithin g (diskExtension a ∘ (homPD_R12 c hc.ne' : ℂ → ℂ) ∘ conj)
          (closedHalfDisk (p / c) (R / c)) ((p / c : ℝ) : ℂ)) ≠ 0 := by
  have hfun : diskExtension a ∘ (homPD_R12 c hc.ne' : ℂ → ℂ) ∘ conj =
      (diskExtension a ∘ conj) ∘ (homPD_R12 c hc.ne' : ℂ → ℂ) := by
    funext z
    simp only [Function.comp_apply, homPD_conj_R12]
  have h1 := conormal_comp_homPD_one_R12 g hc hR hs1
  have h2 := inwardConormalWithin_congr_fun_R12 g (closedHalfDisk (p / c) (R / c))
    ((p / c : ℝ) : ℂ) hfun
  have h3 := conormal_comp_homPD_one_R12 g hc hR hs2
  exact fold_sum_ne_zero_of_eq_R12 _ _ _ _ h1 (h2.trans h3) hfd

/-- **R4r（reparametrized fold ⇒ 严格更小 competitor）。** `HasReparametrizedFold_R12 g a U₀` 的 seam
`[p - R, p + R]` 经同胚缩放 `χ = c •`（`‖p‖ + R < c < 1`，使 `χ '' D̄ ⊆ D°`）搬成 S-MY-R4C
`exists_better_competitor_of_fold_seam_R4C` 的 `sourceChart` 前提表：sheet `a ∘ χ`、`a ∘ conj ∘ χ`，
`ψᵢ' = ψᵢ ∘ χ`，seam 点 `p / c`，fold 条件在缩放下不变。`W = univ`。结论与 scratch
`reparametrized_fold_competitor_MYD3` 逐字相同。 -/
theorem reparametrized_fold_competitor_R12 [FiniteDimensional ℝ E] [T2Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U₀ : ℂ → M} (hU₀ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₀ (Metric.ball (0 : ℂ) 1))
    (hconf₀ : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U₀ z)
    (htension₀ : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U₀ z = 0)
    (a : C(closedDisk, M))
    (haLip : ∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (a z) (a w) ≤ (L : ℝ≥0∞) * edist z w)
    (hfold : HasReparametrizedFold_R12 g a U₀) :
    ∃ v : C(closedDisk, M),
      (∃ K : ℝ≥0, ∀ z w : closedDisk, riemannianEDistOf g (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace a ∧ riemannianDiskArea g v < riemannianDiskArea g a := by
  have hlc : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  have h3 : T3Space M := inferInstance
  obtain ⟨L, hL⟩ := haLip
  obtain ⟨p, R, ψ₁, ψ₂, hR, hpR, hs1, hs2, hi1, hi2, hψ₁, hψ₂, hm₁, hm₂, hb₁, hb₂, he₁, he₂,
    hfd⟩ := hfold
  have hs0 : 0 < ‖(p : ℂ)‖ + R := add_pos_of_nonneg_of_pos (norm_nonneg _) hR
  obtain ⟨c, hsc, hc1⟩ : ∃ c : ℝ, ‖(p : ℂ)‖ + R < c ∧ c < 1 :=
    ⟨(‖(p : ℂ)‖ + R + 1) / 2, by linarith, by linarith⟩
  have hc : 0 < c := hs0.trans hsc
  have hmapsC : MapsTo (homPD_R12 c hc.ne' : ℂ → ℂ) (closedHalfDisk (p / c) (R / c))
      (closedHalfDisk p R) := fun z hz => by
    rw [homPD_R12_apply]
    exact hom_mem_closedHalfDisk_R12 hc hz
  have hmapsO : MapsTo (homPD_R12 c hc.ne' : ℂ → ℂ) (openHalfDisk (p / c) (R / c))
      (openHalfDisk p R) := fun z hz => by
    rw [homPD_R12_apply]
    exact hom_mem_openHalfDisk_R12 hc hz
  have hχsm := contMDiff_homPD_R12 c hc.ne'
  have hχsm1 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 (homPD_R12 c hc.ne' : ℂ → ℂ) Set.univ :=
    (hχsm.of_le (by simp)).contMDiffOn
  have hfun : diskExtension a ∘ (homPD_R12 c hc.ne' : ℂ → ℂ) ∘ conj =
      (diskExtension a ∘ conj) ∘ (homPD_R12 c hc.ne' : ℂ → ℂ) := by
    funext z
    simp only [Function.comp_apply, homPD_conj_R12]
  have hU' : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension a ∘ (homPD_R12 c hc.ne' : ℂ → ℂ))
      (closedHalfDisk (p / c) (R / c)) := hs1.comp (hχsm1.mono (subset_univ _)) hmapsC
  have hUr' : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1
      (diskExtension a ∘ (homPD_R12 c hc.ne' : ℂ → ℂ) ∘ conj) (closedHalfDisk (p / c) (R / c)) := by
    rw [hfun]
    exact hs2.comp (hχsm1.mono (subset_univ _)) hmapsC
  have hi' := injective_mfderivWithin_comp_homPD_R12 hc hR hs1 hi1
  have hir' : ∀ z ∈ closedHalfDisk (p / c) (R / c), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension a ∘ (homPD_R12 c hc.ne' : ℂ → ℂ) ∘ conj)
        (closedHalfDisk (p / c) (R / c)) z) := by
    rw [hfun]
    exact injective_mfderivWithin_comp_homPD_R12 hc hR hs2 hi2
  have hψ₁' : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (ψ₁ ∘ (homPD_R12 c hc.ne' : ℂ → ℂ))
      (openHalfDisk (p / c) (R / c)) := hψ₁.comp hχsm.contMDiffOn hmapsO
  have hψ₂' : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (ψ₂ ∘ (homPD_R12 c hc.ne' : ℂ → ℂ))
      (openHalfDisk (p / c) (R / c)) := hψ₂.comp hχsm.contMDiffOn hmapsO
  have he₁' : EqOn (diskExtension a ∘ (homPD_R12 c hc.ne' : ℂ → ℂ))
      (U₀ ∘ (ψ₁ ∘ (homPD_R12 c hc.ne' : ℂ → ℂ))) (openHalfDisk (p / c) (R / c)) :=
    fun z hz => he₁ (hmapsO hz)
  have he₂' : EqOn (diskExtension a ∘ (homPD_R12 c hc.ne' : ℂ → ℂ) ∘ conj)
      (U₀ ∘ (ψ₂ ∘ (homPD_R12 c hc.ne' : ℂ → ℂ))) (openHalfDisk (p / c) (R / c)) := by
    intro z hz
    have h := he₂ (hmapsO hz)
    change diskExtension a (conj ((homPD_R12 c hc.ne' : ℂ → ℂ) z)) = _ at h
    change diskExtension a ((homPD_R12 c hc.ne' : ℂ → ℂ) (conj z)) = _
    rw [homPD_conj_R12]
    exact h
  have hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ (homPD_R12 c hc.ne').source := fun z _ => by
    rw [homPD_R12_source]
    exact mem_univ z
  have hinside : (homPD_R12 c hc.ne' : ℂ → ℂ) '' Metric.closedBall (0 : ℂ) 1 ⊆
      Metric.ball (0 : ℂ) 1 := by
    rintro _ ⟨z, hz, rfl⟩
    rw [homPD_R12_apply, Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hc.le]
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz
    nlinarith [norm_nonneg z]
  have hpR' : ‖((p / c : ℝ) : ℂ)‖ + R / c < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hc, ← add_div,
      div_lt_one hc]
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hsc
  obtain ⟨v, K, -, -, -, -, -, -, hvL, hvtr, -, hvA⟩ :=
    exists_better_competitor_of_fold_seam_R4C g a hL (W := Set.univ) (Set.subset_univ _)
      (homPD_R12 c hc.ne') hsrc hinside U₀ (ψ₁ ∘ (homPD_R12 c hc.ne' : ℂ → ℂ))
      (ψ₂ ∘ (homPD_R12 c hc.ne' : ℂ → ℂ)) hU₀ hconf₀ htension₀ (div_pos hR hc) hpR' hU' hUr'
      hi' hir' hψ₁' hψ₂' (hm₁.comp hmapsO) (hm₂.comp hmapsO)
      (bijective_mfderiv_comp_homPD_R12 hc hψ₁ hb₁) (bijective_mfderiv_comp_homPD_R12 hc hψ₂ hb₂)
      he₁' he₂' (by rw [interior_univ]; exact Set.mem_univ _)
      (fold_ne_zero_comp_homPD_R12 g hc hR hs1 hs2 hfd)
  exact ⟨v, ⟨K, hvL⟩, hvtr, hvA⟩

end Adapter

end DifferentialGeometry.Geometry
