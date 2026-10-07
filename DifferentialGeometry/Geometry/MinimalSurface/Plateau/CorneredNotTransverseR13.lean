import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CorneredExchangeR13
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CorneredSeamChartR13
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.FoldCompetitorSeamR4C
import DifferentialGeometry.Geometry.MinimalSurface.Boundary.ConormalTangentPlane

/-!
# O-MY-R13 G6c：R13 本体（cornered paired source disks 不横截），以 R13-S 的 Schoenflies 映射为输入

外审 R13（D-24 YES，source-domain parametrized-area 替换，允许 `Ω₁ = Ω₂`）：`u` Morrey 极小、`D°` 上 immersed，
`Ω₁ Ω₂ ⊆ D°` 是 cornered Jordan 子盘，`b : ∂Ω₂ → ∂Ω₁` 边界双射、`U ∘ b = U`；`w = c₂ t₀` 是 `∂Ω₂` 的非 corner
点。若有 R13-S 的 bi-Lipschitz Schoenflies 映射 `B`（`BijOn B Ω₂ Ω₁`、`B = b` on `∂Ω₂`，在 `w` 附近 `Ω₂` 一侧
`C^∞`、`fderivWithin` 单射——即 MYD3 `bilipschitz_schoenflies_seam_MYD3` 的结论），则
`(dU_{b w}, −dU_w)` **不**满射。

证明：
1. G6a：exchange disk `v`（`Ω₂` 上 `U ∘ B`、`interior Ω₂` 外 `u`），`A(v) = A(u)`，`v` 也面积极小。
2. G6b：`w` 处 seam chart `χ`（上半在 `Ω₂` 外、下半在 `Ω₂` 里，像落在 `B` 的光滑区与 `D°` 内）。
3. R4C `fold_seam_conormal_sum_eq_zero_of_minimal_R4C`（`ψ₁ = χ`、`ψ₂ = B ∘ χ ∘ conj`，
   `U₀ = U`）⇒ seam 点 `η₊ + η₋ = 0`。
4. `mfderivWithin_range_eq_of_conormal_sum_eq_zero`（tree，`Boundary/ConormalTangentPlane`）
   ⇒ 两个 sheet 的切平面相同（共同 seam 切向由两 sheet 在实轴上相等推出：`seam_tangent_eq_of_real_R13`）⇒
   `range dU_w ⊆ range dU_{b w}` ⇒ `range (dU_{b w}, −dU_w) ⊆ range dU_{b w}`，维数 `≤ 2 < 3`。

本文件不含 R13-S 的 G3（cornered straightening）/ G5（拼装）：`B` 作为显式函数与性质参数输入。

* `mfderivWithin_comp_eq_R13`：`mfderivWithin (U ∘ G) S z = mfderiv U (G z) ∘ fderivWithin G S z`。
* `seam_tangent_eq_of_real_R13`：两 sheet 在实轴段上相等 ⇒ `D₁ 1 = D₂ 1`。
* **`IsMorreyDisk.not_transverse_cornered_of_schoenflies_R13`**（G6c 主定理）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry Complex
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff Manifold NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- 链式法则（target 为流形、source map 为 `ℂ → ℂ`）：
`mfderivWithin (U ∘ G) S z = mfderiv U (G z) ∘ fderivWithin G S z`。 -/
theorem mfderivWithin_comp_eq_R13 {U : ℂ → M} {G : ℂ → ℂ} {S : Set ℂ} {z : ℂ}
    (hS : UniqueDiffWithinAt ℝ S z) (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (G z))
    (hG : DifferentiableWithinAt ℝ G S z) :
    (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U ∘ G) S z) =
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (G z)).comp (fderivWithin ℝ G S z) := by
  have hG' : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) G S z :=
    hG.hasFDerivWithinAt.hasMFDerivWithinAt.mdifferentiableWithinAt
  have hS' : UniqueMDiffWithinAt 𝓘(ℝ, ℂ) S z := hS.uniqueMDiffWithinAt
  rw [mfderiv_comp_mfderivWithin z hU hG' hS', mfderivWithin_eq_fderivWithin]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- 两个 sheet 在实轴段 `[−a, a]`（`⊆ S`）上相等 ⇒ 在 `0` 处沿实方向的导数相等。 -/
theorem seam_tangent_eq_of_real_R13 {F₁ F₂ : ℂ → M} {S : Set ℂ} {a : ℝ} (ha : 0 < a)
    (hseg : ∀ x : ℝ, x ∈ Icc (-a) a → (x : ℂ) ∈ S)
    (hd₁ : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ S 0)
    (hd₂ : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ S 0)
    (heq : ∀ x : ℝ, x ∈ Icc (-a) a → F₁ x = F₂ x) :
    (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ S 0) 1 =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ S 0) 1 := by
  have hγ : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun x : ℝ => (x : ℂ)) (Icc (-a) a) 0
      ofRealCLM := ofRealCLM.hasFDerivAt.hasFDerivWithinAt.hasMFDerivWithinAt
  have hmaps : Icc (-a) a ⊆ (fun x : ℝ => (x : ℂ)) ⁻¹' S := fun x hx => hseg x hx
  have h₁ := HasMFDerivWithinAt.comp (0 : ℝ) (by simpa using hd₁.hasMFDerivWithinAt) hγ hmaps
  have h₂ := HasMFDerivWithinAt.comp (0 : ℝ) (by simpa using hd₂.hasMFDerivWithinAt) hγ hmaps
  have h₂' := h₂.congr_mono (f₁ := F₁ ∘ fun x : ℝ => (x : ℂ)) (fun x hx => heq x hx)
    (heq 0 ⟨by linarith, ha.le⟩) subset_rfl
  have huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (-a) a) (0 : ℝ) :=
    (uniqueDiffOn_Icc (by linarith) 0 ⟨by linarith, ha.le⟩).uniqueMDiffWithinAt
  have h := congrArg (fun L : ℝ →L[ℝ] E => L 1) (huniq.eq h₁ h₂')
  exact h

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- `EqOn` 的两个映射在 `H` 内一点的 `mfderivWithin` 相同（R4C 同名 private 引理的公开重证）。 -/
theorem mfderivWithin_congr_R13 {F G : ℂ → M} {H : Set ℂ} (heq : EqOn F G H) {z : ℂ}
    (hz : z ∈ H) :
    (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H z) =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) G H z) := by
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) heq hz
  ext w
  simpa only [ContinuousLinearMap.comp_apply] using!
    congrArg (fun D : ℂ →L[ℝ] E => D w) hd

/-- `C^∞` partial diffeomorphism 在 source 点的 `fderiv` 双射。 -/
theorem bijective_fderiv_partialDiffeomorph_R13
    (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞) {x : ℂ} (hx : x ∈ χ.source) :
    Function.Bijective (fderiv ℝ (χ : ℂ → ℂ) x) := by
  have h := ((χ.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ hx).mfderivToContinuousLinearEquiv
    (by simp)).bijective
  change Function.Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (χ : ℂ → ℂ) x) at h
  rw [mfderiv_eq_fderiv] at h
  exact h

/-- `ℂ →L[ℝ] ℂ` 单射 ⇒ 双射。 -/
theorem bijective_of_injective_R13 {L : ℂ →L[ℝ] ℂ} (h : Function.Injective L) :
    Function.Bijective L :=
  ⟨h, LinearMap.injective_iff_surjective (f := L.toLinearMap).mp h⟩

variable [T3Space M]

/-- **G6c 主定理（R13 本体，以 R13-S 的 Schoenflies 映射 `B` 为输入）。**  `u` Morrey 极小、`D°` 上
immersed、`dim E = 3`；`Ω₁ Ω₂ ⊆ D°` cornered Jordan 子盘（允许相交、允许相等）；`b : ∂Ω₂ → ∂Ω₁` 双射、
`U ∘ b = U`；`t₀` 不是 `Ω₂` 的 corner；`B` 是 bi-Lipschitz 双射 `Ω₂ → Ω₁`、`B = b` on `∂Ω₂`，在
`w = c₂ t₀` 附近 `Ω₂` 一侧 `C^∞`、`fderivWithin` 单射（MYD3 `bilipschitz_schoenflies_seam_MYD3` 的结论形）。
则 `(dU_{b w}, −dU_w)` 不满射。 -/
theorem IsMorreyDisk.not_transverse_cornered_of_schoenflies_R13
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) {Uext : ℂ → M} (hUext : SmoothDiskExtension (E := E) u Uext)
    (hiU : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    (hdim : Module.finrank ℝ E = 3)
    {Ω₁ Ω₂ : Set ℂ} {c₁ c₂ : ℝ → ℂ} {C₁ C₂ : Finset ℝ}
    (h₁ : IsCorneredJordanDisk_R13 Ω₁ c₁ C₁) (h₂ : IsCorneredJordanDisk_R13 Ω₂ c₂ C₂)
    (hsub₁ : Ω₁ ⊆ Metric.ball (0 : ℂ) 1) (hsub₂ : Ω₂ ⊆ Metric.ball (0 : ℂ) 1)
    {b : ℂ → ℂ} (hbij : BijOn b (frontier Ω₂) (frontier Ω₁))
    (hfb : ∀ w ∈ frontier Ω₂, diskExtension u (b w) = diskExtension u w)
    {t₀ : ℝ} (ht₀ : ∀ s ∈ C₂, ∀ m : ℤ, t₀ ≠ s + m)
    {B : ℂ → ℂ} (hB : BilipschitzOn_R13 B Ω₂) (hBK : BijOn B Ω₂ Ω₁)
    (hBb : EqOn B b (frontier Ω₂)) {δ : ℝ} (hδ : 0 < δ)
    (hBs : ContDiffOn ℝ ∞ B (Metric.ball (c₂ t₀) δ ∩ Ω₂))
    (hBi : ∀ z ∈ Metric.ball (c₂ t₀) δ ∩ Ω₂, Function.Injective (fderivWithin ℝ B Ω₂ z)) :
    ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (b (c₂ t₀))).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (c₂ t₀)))) := by
  intro htrans
  set U : ℂ → M := diskExtension u with hUdef
  set w : ℂ := c₂ t₀ with hwdef
  have hwfr : w ∈ frontier Ω₂ := by rw [h₂.2.2.1]; exact mem_range_self t₀
  have hwΩ : w ∈ Ω₂ := h₂.1.isClosed.frontier_subset hwfr
  have hUs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (Metric.ball 0 1) := hu.smoothInterior
  have hUd : ∀ y ∈ Metric.ball (0 : ℂ) 1, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U y := fun y hy =>
    (hUs.contMDiffAt (Metric.isOpen_ball.mem_nhds hy)).mdifferentiableAt (by simp)
  -- (1) exchange disk
  obtain ⟨-, v, L, hvLip, hvtr, -, hvin, hvout, -, hvmin⟩ :=
    exists_minimal_exchange_cornered_R13 hu hUext h₁ h₂ hsub₁ hsub₂ hbij hfb hB hBK hBb
      (W := Set.univ) (subset_univ _)
  -- (2) seam chart
  obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball w (hsub₂ hwΩ)
  obtain ⟨χ, hsrc, himg, hχ0, hup, hdn, hdnint⟩ :=
    exists_seam_chart_R13 h₂ ht₀ (δ := min δ δ₀) (lt_min hδ hδ₀)
  have hχball : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, χ z ∈ Metric.ball (0 : ℂ) 1 := fun z hz =>
    hδ₀sub (Metric.ball_subset_ball (min_le_right _ _) (himg ⟨z, hz, rfl⟩))
  have hχδ : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, χ z ∈ Metric.ball w δ := fun z hz =>
    Metric.ball_subset_ball (min_le_left _ _) (himg ⟨z, hz, rfl⟩)
  have hinside : χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 := by
    rintro _ ⟨z, hz, rfl⟩
    exact hχball z hz
  have hχD : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, χ z ∈ Metric.closedBall (0 : ℂ) 1 :=
    fun z hz => Metric.ball_subset_closedBall (hχball z hz)
  -- half disks
  set S : Set ℂ := closedHalfDisk 0 (1 / 2) with hSdef
  have hSD : ∀ z ∈ S, z ∈ Metric.closedBall (0 : ℂ) 1 ∧ 0 ≤ z.im := by
    intro z hz
    refine ⟨?_, hz.1⟩
    have h := hz.2
    rw [Metric.mem_closedBall, ofReal_zero, dist_zero_right] at h
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hSDc : ∀ z ∈ S, conj z ∈ Metric.closedBall (0 : ℂ) 1 ∧ (conj z).im ≤ 0 := by
    intro z hz
    obtain ⟨h1, h2⟩ := hSD z hz
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj]
      simpa using h1
    · rw [conj_im]
      linarith
  have hOS : (openHalfDisk 0 (1 / 2) : Set ℂ) ⊆ S :=
    fun z hz => ⟨(show 0 < z.im from hz.1).le, Metric.ball_subset_closedBall hz.2⟩
  have hSuniq : ∀ z ∈ S, UniqueDiffWithinAt ℝ S z := by
    intro z hz
    refine uniqueDiffOn_convex ((convex_halfSpace_im_ge 0).inter (convex_closedBall _ _))
      ⟨(Complex.I / 4), ?_⟩ z hz
    apply interior_mono hOS
    rw [(openHalfDisk 0 (1 / 2)).isOpen.interior_eq]
    refine ⟨by simp, ?_⟩
    rw [Metric.mem_ball, ofReal_zero, dist_zero_right, norm_div, Complex.norm_I]
    norm_num
  -- sheet identities
  have hF₁ : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ z.im →
      diskExtension v (χ z) = U (χ z) := by
    intro z hz him
    let q : closedDisk := ⟨χ z, hχD z hz⟩
    exact (diskExtension_coe v q).trans
      ((hvout q (hup z hz him)).trans (diskExtension_coe u q).symm)
  have hF₂ : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, z.im ≤ 0 →
      diskExtension v (χ z) = U (B (χ z)) := by
    intro z hz him
    let q : closedDisk := ⟨χ z, hχD z hz⟩
    exact (diskExtension_coe v q).trans (hvin q (hdn z hz him))
  -- second sheet reparametrization `G₂ = B ∘ χ ∘ conj`
  let G₂ : ℂ → ℂ := fun z => B (χ (conj z))
  have hχcd : ContDiffOn ℝ ∞ (χ : ℂ → ℂ) χ.source :=
    contMDiffOn_iff_contDiffOn.mp χ.contMDiffOn_toFun
  have hmapsc : MapsTo (fun z => χ (conj z)) S (Metric.ball w δ ∩ Ω₂) := by
    intro z hz
    obtain ⟨h1, h2⟩ := hSDc z hz
    exact ⟨hχδ _ h1, hdn _ h1 h2⟩
  have hχconj : ContDiffOn ℝ ∞ (fun z => χ (conj z)) S :=
    hχcd.comp conjCLE.contDiff.contDiffOn (fun z hz => hsrc (hSDc z hz).1)
  have hG₂cd : ContDiffOn ℝ ∞ G₂ S := hBs.comp hχconj hmapsc
  have hG₂ball : MapsTo G₂ S (Metric.ball (0 : ℂ) 1) := fun z hz =>
    hsub₁ (hBK.mapsTo (hmapsc hz).2)
  -- derivative of `G₂` within `S`
  have hG₂deriv : ∀ z ∈ S, Function.Injective (fderivWithin ℝ G₂ S z) := by
    intro z hz
    have hy := hmapsc hz
    have hBd : DifferentiableWithinAt ℝ B Ω₂ (χ (conj z)) := by
      have h := (hBs _ hy).differentiableWithinAt (by simp)
      rw [inter_comm] at h
      exact (differentiableWithinAt_inter (Metric.isOpen_ball.mem_nhds hy.1)).mp h
    have hχs : conj z ∈ χ.source := hsrc (hSDc z hz).1
    have hχd : HasFDerivAt (fun z => χ (conj z))
        ((fderiv ℝ (χ : ℂ → ℂ) (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ)) z := by
      have hd : DifferentiableAt ℝ (χ : ℂ → ℂ) (conj z) :=
        (hχcd.contDiffAt (χ.open_source.mem_nhds hχs)).differentiableAt (by simp)
      exact hd.hasFDerivAt.comp z conjCLE.hasFDerivAt
    have hcomp := hBd.hasFDerivWithinAt.comp z hχd.hasFDerivWithinAt
      (fun z hz => (hmapsc hz).2)
    have hfd : fderivWithin ℝ G₂ S z = (fderivWithin ℝ B Ω₂ (χ (conj z))).comp
        ((fderiv ℝ (χ : ℂ → ℂ) (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ)) :=
      hcomp.fderivWithin (hSuniq z hz)
    rw [hfd]
    exact (hBi _ hy).comp ((bijective_fderiv_partialDiffeomorph_R13 χ hχs).injective.comp
      conjCLE.injective)
  -- sheets on `S`
  have hF₁S : EqOn (diskExtension v ∘ χ) (U ∘ χ) S := fun z hz =>
    hF₁ z (hSD z hz).1 (hSD z hz).2
  have hF₂S : EqOn (diskExtension v ∘ χ ∘ conj) (U ∘ G₂) S := fun z hz =>
    hF₂ (conj z) (hSDc z hz).1 (hSDc z hz).2
  have hχS : MapsTo (χ : ℂ → ℂ) S (Metric.ball (0 : ℂ) 1) := fun z hz => hχball z (hSD z hz).1
  have hUχ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (U ∘ χ) S :=
    hUs.comp (χ.contMDiffOn_toFun.mono fun z hz => hsrc (hSD z hz).1) hχS
  have hUG₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (U ∘ G₂) S :=
    hUs.comp (contMDiffOn_iff_contDiffOn.mpr hG₂cd) hG₂ball
  have hU1 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension v ∘ χ) S :=
    (hUχ.of_le (by simp)).congr hF₁S
  have hUr1 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension v ∘ χ ∘ conj) S :=
    (hUG₂.of_le (by simp)).congr hF₂S
  -- derivative formulas on `S`
  have hD₁ : ∀ z ∈ S, (show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension v ∘ χ) S z) =
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (χ z)).comp (fderiv ℝ (χ : ℂ → ℂ) z) := by
    intro z hz
    have hχs : z ∈ χ.source := hsrc (hSD z hz).1
    have hχd : DifferentiableAt ℝ (χ : ℂ → ℂ) z :=
      (hχcd.contDiffAt (χ.open_source.mem_nhds hχs)).differentiableAt (by simp)
    rw [mfderivWithin_congr_R13 hF₁S hz,
      mfderivWithin_comp_eq_R13 (hSuniq z hz) (hUd _ (hχS hz)) hχd.differentiableWithinAt,
      hχd.fderivWithin (hSuniq z hz)]
  have hD₂ : ∀ z ∈ S, (show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension v ∘ χ ∘ conj) S z) =
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (G₂ z)).comp (fderivWithin ℝ G₂ S z) := by
    intro z hz
    rw [mfderivWithin_congr_R13 hF₂S hz,
      mfderivWithin_comp_eq_R13 (hSuniq z hz) (hUd _ (hG₂ball hz))
        ((hG₂cd z hz).differentiableWithinAt (by simp))]
  have hi₁ : ∀ z ∈ S, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension v ∘ χ) S z) := by
    intro z hz
    have h : Function.Injective ((show ℂ →L[ℝ] E from
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (χ z)).comp (fderiv ℝ (χ : ℂ → ℂ) z)) :=
      (hiU _ (hχS hz)).comp
        (bijective_fderiv_partialDiffeomorph_R13 χ (hsrc (hSD z hz).1)).injective
    rw [← hD₁ z hz] at h
    exact h
  have hi₂ : ∀ z ∈ S, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension v ∘ χ ∘ conj) S z) := by
    intro z hz
    have h : Function.Injective ((show ℂ →L[ℝ] E from
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (G₂ z)).comp (fderivWithin ℝ G₂ S z)) :=
      (hiU _ (hG₂ball hz)).comp (hG₂deriv z hz)
    rw [← hD₂ z hz] at h
    exact h
  -- open half disk data
  have hψ₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (χ : ℂ → ℂ) (openHalfDisk 0 (1 / 2)) :=
    χ.contMDiffOn_toFun.mono fun z hz => hsrc (hSD z (hOS hz)).1
  have hψ₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G₂ (openHalfDisk 0 (1 / 2)) :=
    (contMDiffOn_iff_contDiffOn.mpr hG₂cd).mono hOS
  have hbij₁ : ∀ z ∈ (openHalfDisk 0 (1 / 2) : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (χ : ℂ → ℂ) z) := fun z hz =>
    ((χ.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (hsrc (hSD z (hOS hz)).1)).mfderivToContinuousLinearEquiv (by simp)).bijective
  have hbij₂ : ∀ z ∈ (openHalfDisk 0 (1 / 2) : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) G₂ z) := by
    intro z hz
    have hSn : S ∈ 𝓝 z := mem_of_superset ((openHalfDisk 0 (1 / 2)).isOpen.mem_nhds hz) hOS
    have h := hG₂deriv z (hOS hz)
    rw [fderivWithin_of_mem_nhds hSn] at h
    rw [mfderiv_eq_fderiv]
    exact bijective_of_injective_R13 h
  -- R4C：exchange disk 是极小盘 ⇒ seam 点 `η₊ + η₋ = 0`
  have hsum := fold_seam_conormal_sum_eq_zero_of_minimal_R4C g v hvLip (W := Set.univ)
    (subset_univ _) (fun v' h1 _ h3 => hvmin v' h1 h3) χ hsrc hinside U (χ : ℂ → ℂ) G₂ hUs
    hu.conformal hu.harmonic (p := 0) (R := 1 / 2) (by norm_num) (by norm_num) hU1 hUr1 hi₁ hi₂
    hψ₁ hψ₂ (fun z hz => hχS (hOS hz)) (fun z hz => hG₂ball (hOS hz)) hbij₁ hbij₂
    (hF₁S.mono hOS) (hF₂S.mono hOS) (by simp)
  -- 两 sheet 切平面相同
  have h0S : (0 : ℂ) ∈ S := ⟨by simp, by simp⟩
  have hsame : (show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension v ∘ χ) S 0) 1 =
      (show ℂ →L[ℝ] E from
        mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension v ∘ χ ∘ conj) S 0) 1 := by
    refine seam_tangent_eq_of_real_R13 (a := 1 / 2) (by norm_num) ?_
      ((hU1 0 h0S).mdifferentiableWithinAt (by simp))
      ((hUr1 0 h0S).mdifferentiableWithinAt (by simp)) ?_
    · intro x hx
      refine ⟨by simp, ?_⟩
      rw [Metric.mem_closedBall, ofReal_zero, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, abs_le]
      exact hx
    · intro x _
      change diskExtension v (χ x) = diskExtension v (χ (conj (x : ℂ)))
      rw [Complex.conj_ofReal]
  rw [ofReal_zero] at hsum
  have hrange := mfderivWithin_range_eq_of_conormal_sum_eq_zero g (hi₁ 0 h0S) (hi₂ 0 h0S)
    hsame hsum
  rw [hD₁ 0 h0S, hD₂ 0 h0S] at hrange
  have hχ0' : (χ : ℂ → ℂ) 0 = w := hχ0
  have hG₂0 : G₂ 0 = b w := by
    change B (χ (conj 0)) = b w
    rw [map_zero, hχ0']
    exact hBb hwfr
  rw [hχ0', hG₂0] at hrange
  -- `range dU_w ⊆ range dU_{b w}`
  set A : ℂ →L[ℝ] E := (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (b w)) with hAdef
  set C : ℂ →L[ℝ] E := (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U w) with hCdef
  have hCA : ∀ y, ∃ x, A x = C y := by
    intro y
    obtain ⟨y', hy'⟩ :=
      (bijective_fderiv_partialDiffeomorph_R13 χ (x := 0) (hsrc (by simp))).surjective y
    have hmem : C y ∈ LinearMap.range (C.comp (fderiv ℝ (χ : ℂ → ℂ) 0)).toLinearMap := by
      refine ⟨y', ?_⟩
      change C (fderiv ℝ (χ : ℂ → ℂ) 0 y') = C y
      rw [hy']
    rw [hrange] at hmem
    obtain ⟨x, hx⟩ := hmem
    exact ⟨fderivWithin ℝ G₂ S 0 x, hx⟩
  have htop : LinearMap.range A.toLinearMap = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro e
    obtain ⟨⟨x, y⟩, hxy⟩ := htrans e
    obtain ⟨x', hx'⟩ := hCA y
    refine ⟨x - x', ?_⟩
    change A (x - x') = e
    rw [map_sub, hx', ← hxy]
    change A x - C y = A x + -(C y)
    abel
  have h1 := LinearMap.finrank_range_le A.toLinearMap
  rw [htop, finrank_top, hdim, Complex.finrank_real_complex] at h1
  norm_num at h1

end DifferentialGeometry.Geometry
