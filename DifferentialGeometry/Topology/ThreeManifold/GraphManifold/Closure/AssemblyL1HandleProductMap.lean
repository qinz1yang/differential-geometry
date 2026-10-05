import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksProfilesApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1HandleProductRotation
import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Chapter-14 assembly, item L1, step T2′ (handles in product form): the reparametrization map

Lane ASM-L1b2. For an end isometry `A₀`, an angle `α`, two radial profiles `P₀`, `P₁`, a step `β`
(values in `[0, 1]`) and a height profile `φ`, the ambient map
`handleProductMap A₀ α P₀ P₁ β φ (z, t) = (A₀ R_{β t α} (P_{β t} (‖z‖²) • z), φ t)` of `ℝ² × ℝ`
(`R_s = handlePlaneRot s`, `P_b = (1 - b) P₀ + b P₁ = handleProfileMix P₀ P₁ b`):
* the mixed profiles keep `P_b 1 = 1`, `P_b > 0` and `(r P_b (r²))' > 0` on `[0, 1]` (convex
  combinations; the condition is on `r ↦ r P (r²)`, not on `P` alone);
* the map is smooth, its differential is bijective over the closed disk where `φ' ≠ 0` (block
  triangular: the height part is `φ'`, the disk part is the slice `handleDiskMap`);
* every slice `handleDiskMap A P` maps the closed unit disk ONTO itself (`handleDiskMap_surjOn`);
  with `φ` increasing from `0` to `1` the map is a bijection of `closedBall 0 1 ×ˢ [0, 1]`.
The lift to `ClosedCell 2 × Icc 0 1` (`handleLift`) of a smooth ambient map preserving that set is
smooth, and of bijective differential where the ambient differential is bijective (chain rule
through the inclusion, which is a smooth embedding of equal dimension).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1b3M : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASML1b3M : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-! ## Mixed radial profiles -/

/-- The radial profile at the step value `b`: `(1 - b) P₀ + b P₁`. -/
def handleProfileMix (P₀ P₁ : ℝ → ℝ) (b s : ℝ) : ℝ := (1 - b) * P₀ s + b * P₁ s

section Mix

variable {P₀ P₁ : ℝ → ℝ}

theorem contDiff_handleProfileMix (hP₀ : ContDiff ℝ ∞ P₀) (hP₁ : ContDiff ℝ ∞ P₁) (b : ℝ) :
    ContDiff ℝ ∞ (handleProfileMix P₀ P₁ b) :=
  (contDiff_const.mul hP₀).add (contDiff_const.mul hP₁)

theorem handleProfileMix_one (hP₀1 : P₀ 1 = 1) (hP₁1 : P₁ 1 = 1) (b : ℝ) :
    handleProfileMix P₀ P₁ b 1 = 1 := by
  simp only [handleProfileMix, hP₀1, hP₁1]
  ring

theorem convex_comb_pos {b x y : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hx : 0 < x) (hy : 0 < y) :
    0 < (1 - b) * x + b * y := by
  rcases eq_or_lt_of_le hb0 with h | h
  · rw [← h]
    linarith
  · have h1 : 0 ≤ (1 - b) * x := mul_nonneg (by linarith) hx.le
    have h2 : 0 < b * y := mul_pos h hy
    linarith

theorem handleProfileMix_pos {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hP₀pos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P₀ s) (hP₁pos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P₁ s) :
    ∀ s, 0 ≤ s → s ≤ 1 → 0 < handleProfileMix P₀ P₁ b s := fun s hs hs' =>
  convex_comb_pos hb0 hb1 (hP₀pos s hs hs') (hP₁pos s hs hs')

theorem handleProfileMix_mono (hP₀ : ContDiff ℝ ∞ P₀) (hP₁ : ContDiff ℝ ∞ P₁) {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hP₀mono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P₀ (r ^ 2)) r)
    (hP₁mono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P₁ (r ^ 2)) r) :
    ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * handleProfileMix P₀ P₁ b (r ^ 2)) r := by
  intro r hr hr'
  have e : (fun r : ℝ => r * handleProfileMix P₀ P₁ b (r ^ 2)) =
      fun r => (1 - b) * (r * P₀ (r ^ 2)) + b * (r * P₁ (r ^ 2)) := by
    funext r
    simp only [handleProfileMix]
    ring
  have hd0 : HasDerivAt (fun r : ℝ => r * P₀ (r ^ 2)) (deriv (fun r : ℝ => r * P₀ (r ^ 2)) r) r :=
    (hasDerivAt_mul_comp_sq hP₀ r).differentiableAt.hasDerivAt
  have hd1 : HasDerivAt (fun r : ℝ => r * P₁ (r ^ 2)) (deriv (fun r : ℝ => r * P₁ (r ^ 2)) r) r :=
    (hasDerivAt_mul_comp_sq hP₁ r).differentiableAt.hasDerivAt
  have hsum : HasDerivAt (fun r : ℝ => (1 - b) * (r * P₀ (r ^ 2)) + b * (r * P₁ (r ^ 2)))
      ((1 - b) * deriv (fun r : ℝ => r * P₀ (r ^ 2)) r +
        b * deriv (fun r : ℝ => r * P₁ (r ^ 2)) r) r :=
    (hd0.const_mul (1 - b)).add (hd1.const_mul b)
  rw [e, hsum.deriv]
  exact convex_comb_pos hb0 hb1 (hP₀mono r hr hr') (hP₁mono r hr hr')

end Mix

/-! ## The slices map the closed disk onto itself -/

/-- **Surjectivity of a slice.** -/
theorem handleDiskMap_surjOn (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {P : ℝ → ℝ} (hP : ContDiff ℝ ∞ P) (hP1 : P 1 = 1) :
    SurjOn (handleDiskMap A P) (closedBall 0 1) (closedBall 0 1) := by
  intro w hw
  rw [mem_closedBall_zero_iff] at hw
  set u := A.symm w with hu
  have hun : ‖u‖ = ‖w‖ := by rw [hu, LinearIsometryEquiv.norm_map]
  have hcont : ContinuousOn (fun r : ℝ => r * P (r ^ 2)) (Icc 0 1) :=
    (continuous_id.mul (hP.continuous.comp (continuous_pow 2))).continuousOn
  have hivt := intermediate_value_Icc (zero_le_one' ℝ) hcont
  have h01 : ‖u‖ ∈ Icc ((fun r : ℝ => r * P (r ^ 2)) 0) ((fun r : ℝ => r * P (r ^ 2)) 1) := by
    simp only [zero_mul, one_pow, hP1, mul_one]
    exact ⟨norm_nonneg u, hun ▸ hw⟩
  obtain ⟨r, hr, hr'⟩ := hivt h01
  simp only at hr'
  rcases eq_or_ne u 0 with h0 | h0
  · refine ⟨0, by simp, ?_⟩
    have hw0 : w = 0 := by
      have : A u = w := by rw [hu, LinearIsometryEquiv.apply_symm_apply]
      rw [← this, h0, map_zero]
    rw [hw0, handleDiskMap, smul_zero, map_zero]
  · have hnu : 0 < ‖u‖ := norm_pos_iff.mpr h0
    refine ⟨(r / ‖u‖) • u, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_div, abs_norm,
        abs_of_nonneg hr.1, div_mul_cancel₀ _ hnu.ne']
      exact hr.2
    · have hz : ‖(r / ‖u‖) • u‖ = r := by
        rw [norm_smul, Real.norm_eq_abs, abs_div, abs_norm, abs_of_nonneg hr.1,
          div_mul_cancel₀ _ hnu.ne']
      rw [handleDiskMap, hz, smul_smul]
      have hc : P (r ^ 2) * (r / ‖u‖) = 1 := by
        rw [mul_div_assoc', mul_comm, hr', div_self hnu.ne']
      rw [hc, one_smul, hu, LinearIsometryEquiv.apply_symm_apply]

/-! ## The ambient map -/

/-- The ambient handle reparametrization
`(z, t) ↦ (A₀ R_{β t α} (P_{β t} (‖z‖²) • z), φ t)`. -/
def handleProductMap (A₀ : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (α : ℝ)
    (P₀ P₁ β φ : ℝ → ℝ) (p : EuclideanSpace ℝ (Fin 2) × ℝ) : EuclideanSpace ℝ (Fin 2) × ℝ :=
  (handleDiskMap ((handlePlaneRot (β p.2 * α)).trans A₀) (handleProfileMix P₀ P₁ (β p.2)) p.1,
    φ p.2)

section Ambient

variable (A₀ : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (α : ℝ)
  {P₀ P₁ β φ : ℝ → ℝ}

theorem handleProductMap_fst (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    (handleProductMap A₀ α P₀ P₁ β φ p).1 =
      A₀ (handlePlaneRot (β p.2 * α) (handleProfileMix P₀ P₁ (β p.2) (‖p.1‖ ^ 2) • p.1)) :=
  rfl

theorem handleProductMap_snd (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    (handleProductMap A₀ α P₀ P₁ β φ p).2 = φ p.2 :=
  rfl

theorem contDiff_handleProductMap (hP₀ : ContDiff ℝ ∞ P₀) (hP₁ : ContDiff ℝ ∞ P₁)
    (hβ : ContDiff ℝ ∞ β) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (handleProductMap A₀ α P₀ P₁ β φ) := by
  have hb : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => β p.2) := hβ.comp contDiff_snd
  have hn : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => ‖p.1‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp contDiff_fst
  have hmix : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) × ℝ =>
      handleProfileMix P₀ P₁ (β p.2) (‖p.1‖ ^ 2)) :=
    ((contDiff_const.sub hb).mul (hP₀.comp hn)).add (hb.mul (hP₁.comp hn))
  have hrot := contDiff_handlePlaneRot.comp
    ((hb.mul (contDiff_const (c := α))).prodMk (hmix.smul contDiff_fst))
  exact (A₀.toContinuousLinearEquiv.contDiff.comp hrot).prodMk (hφ.comp contDiff_snd)

/-- **The differential of the ambient map is bijective** over the closed disk, where `β ∈ [0, 1]`
and `φ' ≠ 0`. -/
theorem bijective_fderiv_handleProductMap (hP₀ : ContDiff ℝ ∞ P₀) (hP₁ : ContDiff ℝ ∞ P₁)
    (hP₀pos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P₀ s) (hP₁pos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P₁ s)
    (hP₀mono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P₀ (r ^ 2)) r)
    (hP₁mono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P₁ (r ^ 2)) r)
    (hβ : ContDiff ℝ ∞ β) (hφ : ContDiff ℝ ∞ φ) {p : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hp : ‖p.1‖ ≤ 1) (hb0 : 0 ≤ β p.2) (hb1 : β p.2 ≤ 1) (hφp : deriv φ p.2 ≠ 0) :
    Bijective (fderiv ℝ (handleProductMap A₀ α P₀ P₁ β φ) p) := by
  set F := handleProductMap A₀ α P₀ P₁ β φ with hFdef
  have hFd : HasFDerivAt F (fderiv ℝ F p) p :=
    ((contDiff_handleProductMap A₀ α hP₀ hP₁ hβ hφ).differentiable (by simp) p).hasFDerivAt
  set D := fderiv ℝ F p with hD
  -- the height part
  have h2 : HasFDerivAt (fun q => (F q).2)
      ((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp D) p :=
    hasFDerivAt_snd.comp p hFd
  have h2' : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => φ q.2)
      (deriv φ p.2 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ) p :=
    ((hφ.differentiable (by simp) p.2).hasDerivAt).comp_hasFDerivAt p hasFDerivAt_snd
  have e2 := h2.unique h2'
  -- the disk part of the slice
  set A := (handlePlaneRot (β p.2 * α)).trans A₀
  set P := handleProfileMix P₀ P₁ (β p.2)
  have hP : ContDiff ℝ ∞ P := contDiff_handleProfileMix hP₀ hP₁ _
  have hin := hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2
  have hF' : HasFDerivAt F D (p.1, p.2) := hFd
  have h1 := hasFDerivAt_fst.comp p.1 (hF'.comp p.1 hin)
  have hfun : (Prod.fst ∘ F ∘ fun z => (z, p.2)) = handleDiskMap A P := rfl
  rw [hfun] at h1
  have h1' : HasFDerivAt (handleDiskMap A P) (fderiv ℝ (handleDiskMap A P) p.1) p.1 :=
    ((contDiff_handleDiskMap A hP).differentiable (by simp) p.1).hasFDerivAt
  have e1 := h1.unique h1'
  have hslice := bijective_fderiv_handleDiskMap A hP
    (handleProfileMix_pos hb0 hb1 hP₀pos hP₁pos)
    (handleProfileMix_mono hP₀ hP₁ hb0 hb1 hP₀mono hP₁mono) hp
  have hinj : Injective D := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨v, s⟩ hv
    have hs : s = 0 := by
      have h := DFunLike.congr_fun e2 (v, s)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd'] at h
      rw [hv, Prod.snd_zero] at h
      change 0 = deriv φ p.2 * s at h
      exact (mul_eq_zero.mp h.symm).resolve_left hφp
    subst hs
    have h := DFunLike.congr_fun e1 v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.coe_fst'] at h
    rw [hv, Prod.fst_zero] at h
    have hv0 : v = 0 := hslice.1 (by rw [← h, map_zero])
    rw [hv0, Prod.mk_zero_zero]
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := D.toLinearMap)).mp hinj⟩

/-- The ambient map preserves the closed solid cylinder. -/
theorem handleProductMap_mapsTo (hP₀ : ContDiff ℝ ∞ P₀) (hP₁ : ContDiff ℝ ∞ P₁)
    (hP₀1 : P₀ 1 = 1) (hP₁1 : P₁ 1 = 1)
    (hP₀pos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P₀ s) (hP₁pos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P₁ s)
    (hP₀mono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P₀ (r ^ 2)) r)
    (hP₁mono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P₁ (r ^ 2)) r)
    (hβ0 : ∀ t, 0 ≤ β t) (hβ1 : ∀ t, β t ≤ 1) (hφ : MapsTo φ (Icc 0 1) (Icc 0 1)) :
    MapsTo (handleProductMap A₀ α P₀ P₁ β φ) (closedBall 0 1 ×ˢ Icc 0 1)
      (closedBall 0 1 ×ˢ Icc 0 1) := by
  rintro ⟨z, t⟩ ⟨hz, ht⟩
  refine ⟨?_, hφ ht⟩
  rw [mem_closedBall_zero_iff] at hz ⊢
  exact norm_handleDiskMap_le_one _ (contDiff_handleProfileMix hP₀ hP₁ _)
    (handleProfileMix_one hP₀1 hP₁1 _) (handleProfileMix_pos (hβ0 t) (hβ1 t) hP₀pos hP₁pos)
    (handleProfileMix_mono hP₀ hP₁ (hβ0 t) (hβ1 t) hP₀mono hP₁mono) hz

/-- The ambient map is injective on the closed solid cylinder. -/
theorem handleProductMap_injOn (hP₀ : ContDiff ℝ ∞ P₀) (hP₁ : ContDiff ℝ ∞ P₁)
    (hP₀pos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P₀ s) (hP₁pos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P₁ s)
    (hP₀mono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P₀ (r ^ 2)) r)
    (hP₁mono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P₁ (r ^ 2)) r)
    (hβ0 : ∀ t, 0 ≤ β t) (hβ1 : ∀ t, β t ≤ 1) (hφ : StrictMonoOn φ (Icc 0 1)) :
    InjOn (handleProductMap A₀ α P₀ P₁ β φ) (closedBall 0 1 ×ˢ Icc 0 1) := by
  rintro ⟨z, t⟩ ⟨hz, ht⟩ ⟨z', t'⟩ ⟨hz', ht'⟩ h
  have htt : t = t' := hφ.injOn ht ht' (congrArg Prod.snd h)
  subst htt
  have hzz : z = z' := handleDiskMap_injOn _ (contDiff_handleProfileMix hP₀ hP₁ _)
    (handleProfileMix_pos (hβ0 t) (hβ1 t) hP₀pos hP₁pos)
    (handleProfileMix_mono hP₀ hP₁ (hβ0 t) (hβ1 t) hP₀mono hP₁mono) hz hz' (congrArg Prod.fst h)
  rw [hzz]

/-- The ambient map sends the closed solid cylinder ONTO itself. -/
theorem handleProductMap_surjOn (hP₀ : ContDiff ℝ ∞ P₀) (hP₁ : ContDiff ℝ ∞ P₁)
    (hP₀1 : P₀ 1 = 1) (hP₁1 : P₁ 1 = 1) (hφ : ContinuousOn φ (Icc 0 1)) (hφ0 : φ 0 = 0)
    (hφ1 : φ 1 = 1) :
    SurjOn (handleProductMap A₀ α P₀ P₁ β φ) (closedBall 0 1 ×ˢ Icc 0 1)
      (closedBall 0 1 ×ˢ Icc 0 1) := by
  rintro ⟨w, u⟩ ⟨hw, hu⟩
  obtain ⟨t, ht, htu⟩ := intermediate_value_Icc (zero_le_one' ℝ) hφ
    (by rw [hφ0, hφ1]; exact hu)
  obtain ⟨z, hz, hzw⟩ := handleDiskMap_surjOn ((handlePlaneRot (β t * α)).trans A₀)
    (contDiff_handleProfileMix hP₀ hP₁ (β t)) (handleProfileMix_one hP₀1 hP₁1 _) hw
  exact ⟨(z, t), ⟨hz, ht⟩, Prod.ext hzw htu⟩

end Ambient

/-! ## Lifting ambient maps to the handle model `ClosedCell 2 × Icc 0 1` -/

/-- The inclusion of the handle model into `ℝ² × ℝ`. -/
def handleVal (q : ClosedCell 2 × Icc (0 : ℝ) 1) : EuclideanSpace ℝ (Fin 2) × ℝ :=
  ((q.1 : EuclideanSpace ℝ (Fin 2)), (q.2 : ℝ))

theorem isSmoothEmbedding_handleVal :
    IsSmoothEmbedding ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ handleVal := by
  change IsSmoothEmbedding ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
    (Prod.map Subtype.val Subtype.val)
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  let _ : ChartedSpace (EuclideanHalfSpace (1 + 1)) (ClosedCell (1 + 1)) :=
    DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1
  let _ : IsManifold (𝓡∂ (1 + 1)) ∞ (ClosedCell (1 + 1)) :=
    DifferentialGeometry.Topology.Handle.closedCellIsManifold 1
  exact (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 1).prodMap
    (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1))

theorem bijective_mfderiv_handleVal (q : ClosedCell 2 × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) handleVal q) :=
  DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt
    ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) handleVal q
    (isSmoothEmbedding_handleVal.isImmersion.isImmersionAt q) (by simp)

theorem handleVal_mem (q : ClosedCell 2 × Icc (0 : ℝ) 1) :
    handleVal q ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ Icc (0 : ℝ) 1 :=
  ⟨mem_closedBall_zero_iff.mpr q.1.2, q.2.2⟩

theorem injective_handleVal : Injective handleVal := by
  rintro ⟨z, t⟩ ⟨z', t'⟩ h
  simp only [handleVal, Prod.mk.injEq] at h
  rw [Subtype.ext h.1, Subtype.ext h.2]

/-- The lift of an ambient map preserving the closed solid cylinder. -/
def handleLift (F : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2) × ℝ)
    (hF : MapsTo F (closedBall 0 1 ×ˢ Icc 0 1) (closedBall 0 1 ×ˢ Icc 0 1))
    (q : ClosedCell 2 × Icc (0 : ℝ) 1) : ClosedCell 2 × Icc (0 : ℝ) 1 :=
  (⟨(F (handleVal q)).1, mem_closedBall_zero_iff.mp (hF (handleVal_mem q)).1⟩,
    ⟨(F (handleVal q)).2, (hF (handleVal_mem q)).2⟩)

section Lift

variable {F : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2) × ℝ}
  (hF : MapsTo F (closedBall 0 1 ×ˢ Icc 0 1) (closedBall 0 1 ×ˢ Icc 0 1))

theorem handleVal_handleLift (q : ClosedCell 2 × Icc (0 : ℝ) 1) :
    handleVal (handleLift F hF q) = F (handleVal q) :=
  rfl

theorem handleVal_comp_handleLift : handleVal ∘ handleLift F hF = F ∘ handleVal :=
  rfl

theorem contMDiff_handleLift (hFs : ContDiff ℝ ∞ F) :
    ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) ((𝓡∂ 2).prod (𝓡∂ 1)) ∞ (handleLift F hF) := by
  have hc : Continuous (fun q => F (handleVal q)) :=
    hFs.continuous.comp isSmoothEmbedding_handleVal.contMDiff.continuous
  apply (ContMDiff.iff_comp_isImmersion isSmoothEmbedding_handleVal.isImmersion).mpr
  refine ⟨((continuous_fst.comp hc).subtype_mk _).prodMk ((continuous_snd.comp hc).subtype_mk _),
    ?_⟩
  rw [handleVal_comp_handleLift]
  exact hFs.contMDiff.comp isSmoothEmbedding_handleVal.contMDiff

theorem bijective_mfderiv_handleLift (hFs : ContDiff ℝ ∞ F) (q : ClosedCell 2 × Icc (0 : ℝ) 1)
    (hD : Bijective (fderiv ℝ F (handleVal q))) :
    Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) ((𝓡∂ 2).prod (𝓡∂ 1)) (handleLift F hF) q) := by
  have hι := isSmoothEmbedding_handleVal
  have hR := contMDiff_handleLift hF hFs
  have h1 : mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
      (handleVal ∘ handleLift F hF) q =
      (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) handleVal
        (handleLift F hF q)).comp
        (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) ((𝓡∂ 2).prod (𝓡∂ 1)) (handleLift F hF) q) :=
    mfderiv_comp q (hι.contMDiff.mdifferentiableAt (by simp)) (hR.mdifferentiableAt (by simp))
  have hFm : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) F (handleVal q) (fderiv ℝ F (handleVal q)) :=
    (hFs.differentiable (by simp) _).hasFDerivAt.hasMFDerivAt
  have h2 := (hFm.comp q (hι.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt).mfderiv
  rw [← handleVal_comp_handleLift hF, h1] at h2
  have hcomp : Bijective ((mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
      handleVal (handleLift F hF q)).comp
      (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) ((𝓡∂ 2).prod (𝓡∂ 1)) (handleLift F hF) q)) := by
    rw [h2]
    exact hD.comp (bijective_mfderiv_handleVal q)
  exact ((bijective_mfderiv_handleVal _).of_comp_iff' _).mp hcomp

theorem injective_handleLift (hinj : InjOn F (closedBall 0 1 ×ˢ Icc 0 1)) :
    Injective (handleLift F hF) := fun q q' h =>
  injective_handleVal (hinj (handleVal_mem q) (handleVal_mem q')
    (by rw [← handleVal_handleLift hF, ← handleVal_handleLift hF, h]))

theorem surjective_handleLift (hsurj : SurjOn F (closedBall 0 1 ×ˢ Icc 0 1)
    (closedBall 0 1 ×ˢ Icc 0 1)) : Surjective (handleLift F hF) := by
  intro q
  obtain ⟨p, hp, hpq⟩ := hsurj (handleVal_mem q)
  refine ⟨(⟨p.1, mem_closedBall_zero_iff.mp hp.1⟩, ⟨p.2, hp.2⟩), injective_handleVal ?_⟩
  rw [handleVal_handleLift]
  exact hpq

end Lift

end GC.GraphManifold.Assembly
