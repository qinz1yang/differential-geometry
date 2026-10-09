import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CorneredStraighteningR13
import DifferentialGeometry.Topology.PlanarJordan.SmoothSchoenflies
import DifferentialGeometry.Topology.PlanarJordan.InnermostDisk
import DifferentialGeometry.Topology.Manifold.AddCircle.SmoothEmbedding

/-!
# O-MY-R13 G3（无 corner 情形）：smooth Jordan 子盘的 bi-Lipschitz straightening，与无 corner 的 R13

lead 裁决（方案 A 第一步）：`Cr = ∅` 的 G3 经 tree 的 `PlanarJordan.smooth_schoenflies`（光滑嵌入圆周
⇒ 全平面 diffeomorphism `Φ`，`Φ(D̄) = closure (inside (range f))`）。

* **`cornered_disk_straightening_smooth_R13`**：`IsCorneredJordanDisk_R13 Ω c ∅` ⇒ ∃ `Fs`（全平面
  `C^∞`、`fderiv` 处处单射），`Fs` 在 `D̄` 上 bi-Lipschitz、`BijOn Fs D̄ Ω`、`BijOn Fs S¹ ∂Ω`。
  证明：`γ = e ∘ c`（`e : ℂ ≃ₗᵢ ℝ²`）经 `AddCircle.isSmoothEmbedding_periodic_lift` 是光滑嵌入；
  smooth Schoenflies 给 `Φ`；`Ω` 的拓扑 Schoenflies 同胚 `Ψ`（定义里给的）与 `Φ` 在 `S¹` 上的像相同 ⇒
  `Φ(D̄) = e(Ω)`（`image_closedBall_eq_of_image_sphere_eq`）；`Fs = e⁻¹ ∘ Φ ∘ e`，`D̄` 紧凸 ⇒ Lipschitz，
  `Fs⁻¹` 光滑 ⇒ 在紧集 `Ω` 上 Lipschitz。
* `cornered_disk_straightening_noCorner_R13`：MYD3 `cornered_disk_straightening_MYD3` 在 `Cr = ∅` 时的
  逐字形（单侧光滑 + `fderivWithin` 单射）。
* **`IsMorreyDisk.not_transverse_smooth_R13`**（consumer）：`Ω₁ Ω₂` 都无 corner 时 R13 **无条件**成立
  （G3-smooth ×2 → G5 → G6b）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry Complex
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

/-- `ℂ ≅ ℝ²`（`Schoenflies.Plane`）的标准 isometry。 -/
abbrev planeEquiv_R13 : ℂ ≃ₗᵢ[ℝ] Schoenflies.Plane := Complex.orthonormalBasisOneI.repr

theorem planeEquiv_image_closedBall_R13 :
    planeEquiv_R13 '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall 0 1 := by
  simp

theorem planeEquiv_image_sphere_R13 :
    planeEquiv_R13 '' Metric.sphere (0 : ℂ) 1 = Metric.sphere 0 1 := by
  simp

/-- `C¹` 映射在紧集上 Lipschitz。 -/
theorem exists_lipschitzOnWith_of_contDiff_R13 {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) {K : Set ℂ}
    (hK : IsCompact K) : ∃ L : ℝ≥0, LipschitzOnWith L f K :=
  (hf.of_le (by simp)).locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hK

/-- **G3（无 corner）**：smooth Jordan 子盘有全平面光滑、导数处处单射的 bi-Lipschitz straightening。 -/
theorem cornered_disk_straightening_smooth_R13 {Ω : Set ℂ} {c : ℝ → ℂ}
    (hΩ : IsCorneredJordanDisk_R13 Ω c ∅) :
    ∃ Fs : ℂ → ℂ, BilipschitzOn_R13 Fs (Metric.closedBall 0 1) ∧
      BijOn Fs (Metric.closedBall 0 1) Ω ∧ BijOn Fs (Metric.sphere 0 1) (frontier Ω) ∧
      ContDiff ℝ ∞ Fs ∧ ∀ z, Function.Injective (fderiv ℝ Fs z) := by
  set e := planeEquiv_R13 with hedef
  obtain ⟨hcpt, ⟨Ψ, hΨ⟩, hfr, hcont, hper, hinj, -, hreg, -⟩ := hΩ
  have hreg' : ∀ t, ContDiffAt ℝ ∞ c t ∧ deriv c t ≠ 0 := fun t => hreg t (by simp)
  have hc : ContDiff ℝ ∞ c := contDiff_iff_contDiffAt.mpr fun t => (hreg' t).1
  -- 光滑嵌入的圆周
  let γ : ℝ → Schoenflies.Plane := fun t => e (c t)
  have hγ : ContDiff ℝ ∞ γ := e.contDiff.comp hc
  have hγp : Function.Periodic γ 1 := fun t => by
    change e (c (t + 1)) = e (c t)
    rw [hper t]
  have hγi : InjOn γ (Ico (0 : ℝ) 1) := fun s hs t ht hst => hinj hs ht (e.injective hst)
  have hγd : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0 := by
    intro t _
    have hd : HasDerivAt γ (e (deriv c t)) t :=
      e.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt t
        ((hreg' t).1.differentiableAt (by simp)).hasDerivAt
    rw [hd.deriv]
    exact fun h => (hreg' t).2 (e.injective (h.trans (map_zero e).symm))
  have hemb := AddCircle.isSmoothEmbedding_periodic_lift hγ hγp hγi hγd
  obtain ⟨Φ, hΦs, -, -⟩ := PlanarJordan.smooth_schoenflies hemb
  have hrange : range hγp.lift = e '' frontier Ω := by
    rw [hfr]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      induction x using QuotientAddGroup.induction_on with
      | H t => exact ⟨c t, mem_range_self t, rfl⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨(t : AddCircle (1 : ℝ)), rfl⟩
  -- 拓扑 Schoenflies 同胚搬到 `ℝ²`
  let G : Schoenflies.Plane ≃ₜ Schoenflies.Plane :=
    (e.symm.toHomeomorph.trans Ψ).trans e.toHomeomorph
  have hGimg : ∀ S : Set ℂ, G '' (e '' S) = e '' (Ψ '' S) := by
    intro S
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨Ψ x, ⟨x, hx, rfl⟩, by simp [G]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp [G]⟩
  have hΨfr : Ψ '' Metric.sphere (0 : ℂ) 1 = frontier Ω := by
    rw [← hΨ, ← Ψ.image_frontier, frontier_closedBall _ one_ne_zero]
  have hGs : G '' Metric.sphere 0 1 = e '' frontier Ω := by
    rw [← planeEquiv_image_sphere_R13, hGimg, hΨfr]
  have hΦG : Φ.toHomeomorph '' Metric.closedBall 0 1 = G '' Metric.closedBall 0 1 :=
    PlanarJordan.image_closedBall_eq_of_image_sphere_eq Φ.toHomeomorph G 0 0 one_pos one_pos
      (by rw [Diffeomorph.coe_toHomeomorph, hΦs, hGs, hrange])
  have hΦDe : Φ '' Metric.closedBall 0 1 = e '' Ω := by
    have h := hΦG
    rw [Diffeomorph.coe_toHomeomorph, ← planeEquiv_image_closedBall_R13, hGimg, hΨ] at h
    rw [← planeEquiv_image_closedBall_R13]
    exact h
  -- `Fs = e⁻¹ ∘ Φ ∘ e`
  let Fs : ℂ → ℂ := fun z => e.symm (Φ (e z))
  let Gs : ℂ → ℂ := fun z => e.symm (Φ.symm (e z))
  have hGF : ∀ z, Gs (Fs z) = z := fun z => by simp [Fs, Gs]
  have hFs : ContDiff ℝ ∞ Fs := e.symm.contDiff.comp (Φ.contDiff.comp e.contDiff)
  have hGs : ContDiff ℝ ∞ Gs := e.symm.contDiff.comp (Φ.symm.contDiff.comp e.contDiff)
  have hFinj : Function.Injective Fs := fun x y h => by rw [← hGF x, h, hGF y]
  have himg : ∀ S : Set ℂ, Fs '' S = e.symm '' (Φ '' (e '' S)) := fun S => by
    simp only [Fs, image_image]
  have hFD : Fs '' Metric.closedBall 0 1 = Ω := by
    rw [himg, planeEquiv_image_closedBall_R13, hΦDe, image_image]
    simp
  have hFS : Fs '' Metric.sphere 0 1 = frontier Ω := by
    rw [himg, planeEquiv_image_sphere_R13, hΦs, hrange, image_image]
    simp
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_of_contDiff_R13 hFs (isCompact_closedBall 0 1)
  obtain ⟨J, hJ⟩ := exists_lipschitzOnWith_of_contDiff_R13 hGs hcpt
  have hFmaps : MapsTo Fs (Metric.closedBall 0 1) Ω := fun z hz => hFD ▸ mem_image_of_mem Fs hz
  refine ⟨Fs, ⟨max K J, fun x hx y hy => ⟨?_, ?_⟩⟩, ?_, ?_, hFs, ?_⟩
  · exact (hK.dist_le_mul x hx y hy).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left K J) dist_nonneg)
  · have h := hJ.dist_le_mul _ (hFmaps hx) _ (hFmaps hy)
    rw [hGF, hGF] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right K J) dist_nonneg)
  · rw [← hFD]; exact hFinj.injOn.bijOn_image
  · rw [← hFS]; exact hFinj.injOn.bijOn_image
  · intro z v w hvw
    have hcomp : (fderiv ℝ Gs (Fs z)).comp (fderiv ℝ Fs z) = ContinuousLinearMap.id ℝ ℂ := by
      rw [← fderiv_comp z ((hGs.differentiable (by simp)) (Fs z))
        ((hFs.differentiable (by simp)) z)]
      have : Gs ∘ Fs = id := funext hGF
      rw [this, fderiv_id]
    have h := congrArg (fderiv ℝ Gs (Fs z)) hvw
    simpa [← ContinuousLinearMap.comp_apply, hcomp] using h

/-- MYD3 `cornered_disk_straightening_MYD3` 在 `Cr = ∅` 时的逐字形（单侧光滑 + `fderivWithin` 单射）。 -/
theorem cornered_disk_straightening_noCorner_R13 {Ω : Set ℂ} {c : ℝ → ℂ}
    (hΩ : IsCorneredJordanDisk_R13 Ω c ∅) (t₀ : ℝ) :
    ∃ Fs : ℂ → ℂ, BilipschitzOn_R13 Fs (Metric.closedBall 0 1) ∧
      BijOn Fs (Metric.closedBall 0 1) Ω ∧ BijOn Fs (Metric.sphere 0 1) (frontier Ω) ∧
      ∃ ξ₀ ∈ Metric.sphere (0 : ℂ) 1, Fs ξ₀ = c t₀ ∧ ∃ δ > 0,
        ContDiffOn ℝ ∞ Fs (Metric.ball ξ₀ δ ∩ Metric.closedBall 0 1) ∧
        ∀ z ∈ Metric.ball ξ₀ δ ∩ Metric.closedBall 0 1,
          Function.Injective (fderivWithin ℝ Fs (Metric.closedBall 0 1) z) := by
  obtain ⟨Fs, hB, hbij, hs, hsm, hi⟩ := cornered_disk_straightening_smooth_R13 hΩ
  have hct : c t₀ ∈ frontier Ω := by rw [hΩ.2.2.1]; exact mem_range_self t₀
  obtain ⟨ξ₀, hξ₀, hFξ⟩ := hs.surjOn hct
  refine ⟨Fs, hB, hbij, hs, ξ₀, hξ₀, hFξ, 1, one_pos, hsm.contDiffOn, fun z hz => ?_⟩
  rw [(hsm.differentiable (by simp) z).fderivWithin
    (uniqueDiffOn_convex (convex_closedBall 0 1)
      ⟨0, by rw [interior_closedBall _ one_ne_zero]; simp⟩ z hz.2)]
  exact hi z

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- **R13，无 corner 情形（无条件）**：`Ω₁ Ω₂` 都是无 corner 的 Jordan 子盘时，MYD2 R13 的几何前提
（`b` bi-Lipschitz 边界配对、`U ∘ b = U`、`b ∘ c₂` 分段光滑且在 `t₀` 光滑）⇒ `(dU_{b w}, −dU_w)` 不满射。
G3-smooth（两次）→ G5 → G6b。 -/
theorem IsMorreyDisk.not_transverse_smooth_R13
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) {Uext : ℂ → M} (hUext : SmoothDiskExtension (E := E) u Uext)
    (hiU : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    (hdim : Module.finrank ℝ E = 3)
    {Ω₁ Ω₂ : Set ℂ} {c₁ c₂ : ℝ → ℂ}
    (h₁ : IsCorneredJordanDisk_R13 Ω₁ c₁ ∅) (h₂ : IsCorneredJordanDisk_R13 Ω₂ c₂ ∅)
    (hsub₁ : Ω₁ ⊆ Metric.ball (0 : ℂ) 1) (hsub₂ : Ω₂ ⊆ Metric.ball (0 : ℂ) 1)
    {b : ℂ → ℂ} (hb : BilipschitzOn_R13 b (frontier Ω₂))
    (hbij : BijOn b (frontier Ω₂) (frontier Ω₁))
    (hbpw : ∃ Cb : Finset ℝ, ∀ t, (∀ s ∈ Cb, ∀ m : ℤ, t ≠ s + m) → ContDiffAt ℝ ∞ (b ∘ c₂) t)
    (hfb : ∀ w ∈ frontier Ω₂, diskExtension u (b w) = diskExtension u w)
    (t₀ : ℝ) (hbt₀ : ContDiffAt ℝ ∞ (b ∘ c₂) t₀) :
    ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (b (c₂ t₀))).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (c₂ t₀)))) := by
  obtain ⟨F₁, hF₁, hF₁b, hF₁s, hF₁sm, hF₁i⟩ := cornered_disk_straightening_smooth_R13 h₁
  obtain ⟨F₂, hF₂, hF₂b, hF₂s, hF₂sm, hF₂i⟩ := cornered_disk_straightening_smooth_R13 h₂
  have hw : c₂ t₀ ∈ frontier Ω₂ := by rw [h₂.2.2.1]; exact mem_range_self t₀
  obtain ⟨ξ₂, hξ₂, hF₂ξ⟩ := hF₂s.surjOn hw
  obtain ⟨ξ₁, hξ₁, hF₁ξ⟩ := hF₁s.surjOn (hbij.mapsTo hw)
  exact hu.not_transverse_cornered_of_straightening_R13 hUext hiU hdim h₁ h₂ hsub₁ hsub₂ hb hbij
    hbpw hfb (by simp) hbt₀ hF₁ hF₁b hF₁s hξ₁ hF₁ξ isOpen_univ (mem_univ _) hF₁sm.contDiffOn
    (fun z _ => hF₁i z) hF₂ hF₂b hF₂s hξ₂ hF₂ξ isOpen_univ (mem_univ _) hF₂sm.contDiffOn
    (fun z _ => hF₂i z)

end DifferentialGeometry.Geometry
