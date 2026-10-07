import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CorneredRadialSeamR13
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CorneredSeamChartR13

/-!
# O-MY-R13 G5：bi-Lipschitz Schoenflies（seam 光滑），由 cornered straightening 数据拼装

MYD3 合同 `bilipschitz_schoenflies_seam_MYD3`（`R10R14.lean:367`）：`B = F₁ ∘ E_β ∘ F₂⁻¹`，
`β = F₁⁻¹ ∘ b ∘ F₂`（D-25/27）。本文件**由 straightening 数据** `F₁ F₂`（G3 的输出形）拼出 `B`：

* 全局部分（`B` bi-Lipschitz、`BijOn B Ω₂ Ω₁`、`B = b` on `∂Ω₂`）只用 `Fᵢ` 的 bi-Lipschitz 双射性 + G1。
* seam 部分（`B` 在 `w = c₂ t₀` 附近 `Ω₂` 一侧 `C^∞`、`fderivWithin` 单射）用：`Fᵢ` 在选定点的**开**邻域上
  `C^∞`、`fderiv` 单射（局部逆 `exists_local_inverse_R13`）；`F₂(e^{it})` 沿 `∂Ω₂` 的光滑重参数化
  `F₂(e^{it}) = c₂(s(t))`（经 G6b 的 tube chart）；`(b ∘ c₂)′(t₀) ≠ 0` 由 `b` 的 lower Lipschitz bound 与
  `c₂′(t₀) ≠ 0` 推出（外审 R-MY3 的说明，`norm_deriv_le_of_lower_lipschitz_R13`）；再用 G2 的 radial extension
  seam smoothness（开集版 `radial_extension_seam_smooth_open_R13`）。

偏差（记录）：MYD3 G3 的 straightening 只要求在 `ball ξ₀ δ ∩ D̄` 上（单侧）光滑；这里要求在 `ξ₀` 的一个**开**
邻域上光滑、`fderiv` 单射（单侧 → 开邻域需要 Seeley/Whitney 型延拓或单侧 IFT，tree 中没有现成的；
任何经 smooth collar 的构造自然给出开邻域版）。`B` 的结论与 MYD3 G5 逐字同形。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Complex
open scoped Topology ContDiff Manifold NNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

/-! ## bi-Lipschitz 代数 -/

/-- bi-Lipschitz 的复合（`MapsTo`）。 -/
theorem BilipschitzOn_R13.comp_R13 {f g : ℂ → ℂ} {S T : Set ℂ} (hg : BilipschitzOn_R13 g T)
    (hf : BilipschitzOn_R13 f S) (hST : MapsTo f S T) : BilipschitzOn_R13 (g ∘ f) S := by
  obtain ⟨K₁, hK₁⟩ := hf
  obtain ⟨K₂, hK₂⟩ := hg
  refine ⟨K₂ * K₁, fun x hx y hy => ⟨?_, ?_⟩⟩
  · have h1 := (hK₁ x hx y hy).1
    have h2 := (hK₂ _ (hST hx) _ (hST hy)).1
    calc dist (g (f x)) (g (f y)) ≤ K₂ * dist (f x) (f y) := h2
      _ ≤ K₂ * (K₁ * dist x y) := mul_le_mul_of_nonneg_left h1 K₂.coe_nonneg
      _ = ((K₂ * K₁ : ℝ≥0) : ℝ) * dist x y := by push_cast; ring
  · have h1 := (hK₁ x hx y hy).2
    have h2 := (hK₂ _ (hST hx) _ (hST hy)).2
    calc dist x y ≤ K₁ * dist (f x) (f y) := h1
      _ ≤ K₁ * (K₂ * dist (g (f x)) (g (f y))) := mul_le_mul_of_nonneg_left h2 K₁.coe_nonneg
      _ = ((K₂ * K₁ : ℝ≥0) : ℝ) * dist ((g ∘ f) x) ((g ∘ f) y) := by
        simp only [Function.comp_apply]; push_cast; ring

/-- bi-Lipschitz 双射 `S → T` 的逆 `invFunOn f S` 在 `T` 上 bi-Lipschitz，且 `BijOn _ T S`。 -/
theorem BilipschitzOn_R13.inv_R13 {f : ℂ → ℂ} {S T : Set ℂ} (hf : BilipschitzOn_R13 f S)
    (hbij : BijOn f S T) :
    BilipschitzOn_R13 (Function.invFunOn f S) T ∧ BijOn (Function.invFunOn f S) T S := by
  obtain ⟨K, hK⟩ := hf
  have hmaps : MapsTo (Function.invFunOn f S) T S := hbij.surjOn.mapsTo_invFunOn
  have hright : ∀ y ∈ T, f (Function.invFunOn f S y) = y :=
    fun y hy => hbij.surjOn.rightInvOn_invFunOn hy
  refine ⟨⟨K, fun x hx y hy => ?_⟩, hbij.symm hbij.invOn_invFunOn.symm⟩
  have h := hK _ (hmaps hx) _ (hmaps hy)
  rw [hright x hx, hright y hy] at h
  exact ⟨h.2, h.1⟩

/-- `f` 在 `S` 上单射、`f x = y`、`x ∈ S` ⇒ `invFunOn f S y = x`。 -/
theorem invFunOn_eq_of_injOn_R13 {f : ℂ → ℂ} {S : Set ℂ} (hf : InjOn f S) {x : ℂ} (hx : x ∈ S) :
    Function.invFunOn f S (f x) = x :=
  hf.leftInvOn_invFunOn hx

/-- `F` 在 `D̄` 上单射、`BijOn F S¹ ∂Ω` ⇒ `BijOn (invFunOn F D̄) ∂Ω S¹`。 -/
theorem bijOn_invFunOn_sphere_R13 {F : ℂ → ℂ} {Ω : Set ℂ}
    (hinj : InjOn F (Metric.closedBall 0 1)) (hs : BijOn F (Metric.sphere 0 1) (frontier Ω)) :
    BijOn (Function.invFunOn F (Metric.closedBall 0 1)) (frontier Ω) (Metric.sphere 0 1) := by
  have hSD : Metric.sphere (0 : ℂ) 1 ⊆ Metric.closedBall 0 1 := Metric.sphere_subset_closedBall
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨ξ, hξ, rfl⟩ := hs.surjOn hy
    rw [invFunOn_eq_of_injOn_R13 hinj (hSD hξ)]
    exact hξ
  · intro y hy y' hy' hyy'
    obtain ⟨ξ, hξ, rfl⟩ := hs.surjOn hy
    obtain ⟨ξ', hξ', rfl⟩ := hs.surjOn hy'
    rw [invFunOn_eq_of_injOn_R13 hinj (hSD hξ), invFunOn_eq_of_injOn_R13 hinj (hSD hξ')] at hyy'
    rw [hyy']
  · intro ξ hξ
    exact ⟨F ξ, hs.mapsTo hξ, invFunOn_eq_of_injOn_R13 hinj (hSD hξ)⟩

/-- 边界映射 `β = F₁⁻¹ ∘ b ∘ F₂`（`F₁⁻¹ = invFunOn F₁ D̄`）。 -/
def schoenfliesBoundary_R13 (F₁ F₂ b : ℂ → ℂ) (ξ : ℂ) : ℂ :=
  Function.invFunOn F₁ (Metric.closedBall 0 1) (b (F₂ ξ))

/-- Schoenflies 映射 `B = F₁ ∘ E_β ∘ F₂⁻¹`。 -/
def schoenfliesMap_R13 (F₁ F₂ b : ℂ → ℂ) (y : ℂ) : ℂ :=
  F₁ (radialExtension_R13 (schoenfliesBoundary_R13 F₁ F₂ b)
    (Function.invFunOn F₂ (Metric.closedBall 0 1) y))

/-- **全局拼装**：`β` 是 `S¹` 的 bi-Lipschitz 双射；`B` 是 `Ω₂ → Ω₁` 的 bi-Lipschitz 双射，`B = b` on
`∂Ω₂`。 -/
theorem schoenfliesMap_global_R13 {Ω₁ Ω₂ : Set ℂ} {F₁ F₂ b : ℂ → ℂ}
    (hF₁ : BilipschitzOn_R13 F₁ (Metric.closedBall 0 1))
    (hF₁b : BijOn F₁ (Metric.closedBall 0 1) Ω₁)
    (hF₁s : BijOn F₁ (Metric.sphere 0 1) (frontier Ω₁))
    (hF₂ : BilipschitzOn_R13 F₂ (Metric.closedBall 0 1))
    (hF₂b : BijOn F₂ (Metric.closedBall 0 1) Ω₂)
    (hF₂s : BijOn F₂ (Metric.sphere 0 1) (frontier Ω₂))
    (hb : BilipschitzOn_R13 b (frontier Ω₂)) (hbij : BijOn b (frontier Ω₂) (frontier Ω₁)) :
    BilipschitzOn_R13 (schoenfliesBoundary_R13 F₁ F₂ b) (Metric.sphere 0 1) ∧
      BijOn (schoenfliesBoundary_R13 F₁ F₂ b) (Metric.sphere 0 1) (Metric.sphere 0 1) ∧
      BilipschitzOn_R13 (schoenfliesMap_R13 F₁ F₂ b) Ω₂ ∧
      BijOn (schoenfliesMap_R13 F₁ F₂ b) Ω₂ Ω₁ ∧
      EqOn (schoenfliesMap_R13 F₁ F₂ b) b (frontier Ω₂) := by
  have hSD : Metric.sphere (0 : ℂ) 1 ⊆ Metric.closedBall 0 1 := Metric.sphere_subset_closedBall
  have hfr₁ : frontier Ω₁ ⊆ Ω₁ := by
    intro y hy
    obtain ⟨ξ, hξ, rfl⟩ := hF₁s.surjOn hy
    exact hF₁b.mapsTo (hSD hξ)
  obtain ⟨hF₁i, hF₁ib⟩ := hF₁.inv_R13 hF₁b
  obtain ⟨hF₂i, hF₂ib⟩ := hF₂.inv_R13 hF₂b
  have hF₁is : BijOn (Function.invFunOn F₁ (Metric.closedBall 0 1)) (frontier Ω₁)
      (Metric.sphere 0 1) := bijOn_invFunOn_sphere_R13 hF₁b.injOn hF₁s
  have hβbij : BijOn (schoenfliesBoundary_R13 F₁ F₂ b) (Metric.sphere 0 1) (Metric.sphere 0 1) :=
    hF₁is.comp (hbij.comp hF₂s)
  have hβ : BilipschitzOn_R13 (schoenfliesBoundary_R13 F₁ F₂ b) (Metric.sphere 0 1) :=
    (hF₁i.mono hfr₁).comp_R13 (hb.comp_R13 (hF₂.mono hSD) hF₂s.mapsTo)
      (hbij.mapsTo.comp hF₂s.mapsTo)
  obtain ⟨hE, hEb, hEs⟩ := radial_extension_bilipschitz_R13 hβ hβbij
  refine ⟨hβ, hβbij, ?_, ?_, ?_⟩
  · exact hF₁.comp_R13 (hE.comp_R13 hF₂i hF₂ib.mapsTo) (hEb.mapsTo.comp hF₂ib.mapsTo)
  · exact hF₁b.comp (hEb.comp hF₂ib)
  · intro y hy
    obtain ⟨ξ, hξ, rfl⟩ := hF₂s.surjOn hy
    have h1 : Function.invFunOn F₂ (Metric.closedBall 0 1) (F₂ ξ) = ξ :=
      invFunOn_eq_of_injOn_R13 hF₂b.injOn (hSD hξ)
    change F₁ (radialExtension_R13 (schoenfliesBoundary_R13 F₁ F₂ b)
      (Function.invFunOn F₂ (Metric.closedBall 0 1) (F₂ ξ))) = b (F₂ ξ)
    rw [h1, hEs hξ]
    exact hF₁b.surjOn.rightInvOn_invFunOn (hfr₁ (hbij.mapsTo (hF₂s.mapsTo hξ)))

/-! ## 局部逆、导数下界、弧重参数化、开集版 G2 -/

/-- `ℂ →L[ℝ] ℂ` 单射 ⇒ 满射。 -/
theorem surjective_of_injective_R13 {L : ℂ →L[ℝ] ℂ} (h : Function.Injective L) :
    Function.Surjective L :=
  LinearMap.injective_iff_surjective (f := L.toLinearMap).mp h

/-- `C^∞` partial diffeomorphism 在 source 点的 `fderiv` 单射。 -/
theorem fderiv_injective_of_partialDiffeomorph_R13
    (Ψ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞) {x : ℂ} (hx : x ∈ Ψ.source) :
    Function.Injective (fderiv ℝ (Ψ : ℂ → ℂ) x) := by
  have h := ((Ψ.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ hx).mfderivToContinuousLinearEquiv
    (by simp)).bijective
  change Function.Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Ψ : ℂ → ℂ) x) at h
  rw [mfderiv_eq_fderiv] at h
  exact h.injective

/-- **局部逆**：`F : D̄ → Ω` bi-Lipschitz 双射，在 `ξ ∈ D̄` 的开邻域 `V` 上 `C^∞`、`fderiv` 单射 ⇒
`F ξ` 的开邻域 `N` 上有 `C^∞` 局部逆 `φ`（`fderiv` 单射、`φ N ⊆ V`、`F ∘ φ = id`、`φ (F ξ) = ξ`），且在
`N ∩ Ω` 上 `φ = invFunOn F D̄`。 -/
theorem exists_local_inverse_R13 {F : ℂ → ℂ} {Ω : Set ℂ}
    (hF : BilipschitzOn_R13 F (Metric.closedBall 0 1)) (hFb : BijOn F (Metric.closedBall 0 1) Ω)
    {ξ : ℂ} (hξ : ξ ∈ Metric.closedBall (0 : ℂ) 1) {V : Set ℂ} (hV : IsOpen V) (hξV : ξ ∈ V)
    (hFs : ContDiffOn ℝ ∞ F V) (hFi : ∀ z ∈ V, Function.Injective (fderiv ℝ F z)) :
    ∃ N : Set ℂ, IsOpen N ∧ F ξ ∈ N ∧ ∃ φ : ℂ → ℂ,
      (∀ y ∈ N, ContDiffAt ℝ ∞ φ y ∧ Function.Injective (fderiv ℝ φ y)) ∧ MapsTo φ N V ∧
      (∀ y ∈ N, F (φ y) = y) ∧ φ (F ξ) = ξ ∧
      ∀ y ∈ N ∩ Ω, φ y = Function.invFunOn F (Metric.closedBall 0 1) y := by
  have hFd : DifferentiableAt ℝ F ξ :=
    (hFs.contDiffAt (hV.mem_nhds hξV)).differentiableAt (by simp)
  have hinj := hFi ξ hξV
  have hinv : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F ξ).IsInvertible := by
    rw [mfderiv_eq_fderiv]
    exact ⟨(LinearEquiv.ofBijective (fderiv ℝ F ξ).toLinearMap
      ⟨hinj, surjective_of_injective_R13 hinj⟩).toContinuousLinearEquiv, rfl⟩
  obtain ⟨Ψ, hξΨ, hΨ⟩ :=
    DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
      hV hξV (contMDiffOn_iff_contDiffOn.mpr hFs) hinv
  have hleft : ∀ x ∈ Ψ.source, Ψ.symm (Ψ x) = x := fun x hx => Ψ.toPartialEquiv.left_inv hx
  have hright : ∀ y ∈ Ψ.target, Ψ (Ψ.symm y) = y := fun y hy => Ψ.toPartialEquiv.right_inv hy
  obtain ⟨⟨K, hK⟩, -⟩ := hF.inv_R13 hFb
  obtain ⟨ρ', hρ', hρ'sub⟩ := Metric.isOpen_iff.mp (Ψ.open_source.inter hV) ξ ⟨hξΨ, hξV⟩
  have hK1 : (0 : ℝ) < K + 1 := by positivity
  set ρ : ℝ := ρ' / (K + 1) with hρdef
  have hρ : 0 < ρ := div_pos hρ' hK1
  have hsymm : ContinuousOn (Ψ.symm : ℂ → ℂ) Ψ.target :=
    Ψ.symm.contMDiffOn_toFun.continuousOn
  refine ⟨(Ψ.target ∩ (Ψ.symm : ℂ → ℂ) ⁻¹' (Ψ.source ∩ V)) ∩ Metric.ball (F ξ) ρ,
    (hsymm.isOpen_inter_preimage Ψ.open_target (Ψ.open_source.inter hV)).inter
      Metric.isOpen_ball, ?_, Ψ.symm, ?_, ?_, ?_, ?_, ?_⟩
  · have hFΨ : F ξ = Ψ ξ := hΨ hξΨ
    refine ⟨⟨?_, ?_⟩, Metric.mem_ball_self hρ⟩
    · rw [hFΨ]; exact Ψ.toPartialEquiv.map_source hξΨ
    · change Ψ.symm (F ξ) ∈ Ψ.source ∩ V
      rw [hFΨ, hleft ξ hξΨ]
      exact ⟨hξΨ, hξV⟩
  · intro y hy
    have hyt : y ∈ Ψ.symm.source := hy.1.1
    refine ⟨(contMDiffOn_iff_contDiffOn.mp Ψ.symm.contMDiffOn_toFun).contDiffAt
      (Ψ.symm.open_source.mem_nhds hyt), fderiv_injective_of_partialDiffeomorph_R13 Ψ.symm hyt⟩
  · intro y hy
    exact hy.1.2.2
  · intro y hy
    have h1 : Ψ.symm y ∈ Ψ.source := hy.1.2.1
    change F (Ψ.symm y) = y
    rw [hΨ h1]
    exact hright y hy.1.1
  · rw [hΨ hξΨ, hleft ξ hξΨ]
  · intro y hy
    obtain ⟨⟨hyt, -⟩, hyb⟩ := hy.1
    set x := Function.invFunOn F (Metric.closedBall 0 1) y with hxdef
    have hxD : x ∈ Metric.closedBall (0 : ℂ) 1 := hFb.surjOn.mapsTo_invFunOn hy.2
    have hFx : F x = y := hFb.surjOn.rightInvOn_invFunOn hy.2
    have hξx : Function.invFunOn F (Metric.closedBall 0 1) (F ξ) = ξ :=
      invFunOn_eq_of_injOn_R13 hFb.injOn hξ
    have hd : dist x ξ ≤ K * dist y (F ξ) := by
      have h := (hK y hy.2 (F ξ) (hFb.mapsTo hξ)).1
      rwa [hξx] at h
    have hdx : dist x ξ < ρ' := by
      have hy' : dist y (F ξ) < ρ := hyb
      calc dist x ξ ≤ K * dist y (F ξ) := hd
        _ ≤ K * ρ := mul_le_mul_of_nonneg_left hy'.le K.coe_nonneg
        _ < ρ' := by
          rw [hρdef, mul_div_assoc']
          rw [div_lt_iff₀ hK1]
          nlinarith [K.coe_nonneg]
    have hxs : x ∈ Ψ.source := (hρ'sub (Metric.mem_ball.mpr hdx)).1
    have hΨx : Ψ x = y := (hΨ hxs).symm.trans hFx
    change Ψ.symm y = x
    rw [← hΨx, hleft x hxs]

/-- **导数下界**（外审 R-MY3：`(b∘c₂)′(t₀) ≠ 0` 由 lower Lipschitz + `c₂` regular 推出）：
`‖g s − g t₀‖ ≤ K ‖f s − f t₀‖` 对所有 `s` ⇒ `‖g′(t₀)‖ ≤ K ‖f′(t₀)‖`。 -/
theorem norm_deriv_le_of_lower_lipschitz_R13 {f g : ℝ → ℂ} {t₀ : ℝ} {D v : ℂ} {K : ℝ}
    (hf : HasDerivAt f D t₀) (hg : HasDerivAt g v t₀)
    (hK : ∀ s, ‖g s - g t₀‖ ≤ K * ‖f s - f t₀‖) : ‖v‖ ≤ K * ‖D‖ := by
  have hf' := (hasDerivAt_iff_tendsto_slope.mp hf).norm
  have hg' := (hasDerivAt_iff_tendsto_slope.mp hg).norm
  refine le_of_tendsto_of_tendsto' hg' (hf'.const_mul K) fun s => ?_
  simp only [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs]
  calc |s - t₀|⁻¹ * ‖g s - g t₀‖ ≤ |s - t₀|⁻¹ * (K * ‖f s - f t₀‖) :=
        mul_le_mul_of_nonneg_left (hK s) (inv_nonneg.mpr (abs_nonneg _))
    _ = K * (|s - t₀|⁻¹ * ‖f s - f t₀‖) := by ring

/-- **弧重参数化**：`γ` 落在 `∂Ω` 里、在 `t₂` 附近 `C^∞`、`γ t₂ = c t₀`（`t₀` 非 corner）⇒ 存在
`0 < ε ≤ ε₀` 与在 `ball t₂ ε` 上 `C^∞` 的 `s`，`s t₂ = t₀`，`γ t = c (s t)`（经 G6b 的 tube chart：
`s t = t₀ + re (Φ⁻¹ (γ t))`）。 -/
theorem exists_arc_reparam_R13 {Ω : Set ℂ} {c : ℝ → ℂ} {Cr : Finset ℝ}
    (h : IsCorneredJordanDisk_R13 Ω c Cr) {t₀ : ℝ} (ht₀ : ∀ s ∈ Cr, ∀ m : ℤ, t₀ ≠ s + m)
    {γ : ℝ → ℂ} {t₂ ε₀ : ℝ} (hε₀ : 0 < ε₀) (hγ : ∀ t, γ t ∈ frontier Ω)
    (hγs : ContDiffOn ℝ ∞ γ (Metric.ball t₂ ε₀)) (hγt : γ t₂ = c t₀) :
    ∃ ε > 0, ε ≤ ε₀ ∧ ∃ s : ℝ → ℝ, ContDiffOn ℝ ∞ s (Metric.ball t₂ ε) ∧ s t₂ = t₀ ∧
      ∀ t ∈ Metric.ball t₂ ε, γ t = c (s t) := by
  obtain ⟨Φ, h0, hΦ⟩ := h.exists_seamTube_partialDiffeomorph ht₀
  have hleft : ∀ x ∈ Φ.source, Φ.symm (Φ x) = x := fun x hx => Φ.toPartialEquiv.left_inv hx
  have hΘ0 : seamTube_R13 c t₀ 0 = c t₀ := by simpa using seamTube_ofReal_R13 c t₀ 0
  have hΦ0 : Φ 0 = c t₀ := (hΦ h0).symm.trans hΘ0
  obtain ⟨r₀, hr₀, hr₀s⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Φ.open_source.mem_nhds h0)
  obtain ⟨κ, hκ, hloc⟩ := h.exists_local_boundary t₀ hr₀
  have hT : Φ.target ∩ Metric.ball (c t₀) κ ∈ 𝓝 (γ t₂) := by
    rw [hγt]
    refine (Φ.open_target.inter Metric.isOpen_ball).mem_nhds ⟨?_, Metric.mem_ball_self hκ⟩
    rw [← hΦ0]
    exact Φ.toPartialEquiv.map_source h0
  have hγc : ContinuousAt γ t₂ :=
    (hγs.contDiffAt (Metric.ball_mem_nhds t₂ hε₀)).continuousAt
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.mem_nhds_iff.mp (hγc hT)
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, min_le_left _ _, fun t => t₀ + (Φ.symm (γ t)).re, ?_, ?_, ?_⟩
  · have hmaps : MapsTo γ (Metric.ball t₂ (min ε₀ ε₁)) Φ.target := fun t ht =>
      (hε₁sub (Metric.ball_subset_ball (min_le_right _ _) ht)).1
    have hsymm : ContDiffOn ℝ ∞ (Φ.symm : ℂ → ℂ) Φ.target :=
      contMDiffOn_iff_contDiffOn.mp Φ.symm.contMDiffOn_toFun
    have hc := (reCLM.contDiff.comp_contDiffOn
      (hsymm.comp (hγs.mono (Metric.ball_subset_ball (min_le_left _ _))) hmaps))
    exact contDiffOn_const.add hc
  · change t₀ + (Φ.symm (γ t₂)).re = t₀
    rw [hγt, ← hΦ0, hleft 0 h0, zero_re, add_zero]
  · intro t ht
    obtain ⟨hγT, hγκ⟩ := hε₁sub (Metric.ball_subset_ball (min_le_right _ _) ht)
    obtain ⟨x, hx, hxc⟩ := hloc (γ t) (hγ t) hγκ
    have hxs : (x : ℂ) ∈ Φ.source := hr₀s (by
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact hx.le)
    have hΦx : Φ (x : ℂ) = γ t := ((hΦ hxs).symm.trans (seamTube_ofReal_R13 c t₀ x)).trans hxc.symm
    change γ t = c (t₀ + (Φ.symm (γ t)).re)
    rw [← hΦx, hleft _ hxs, ofReal_re, hΦx]
    exact hxc

/-- **开集版 G2**：`β` 沿角参数在 `t₀` 附近 `C^∞`、导数非零、`MapsTo β S¹ S¹` ⇒ `E_β` 在 `e^{it₀}` 的一个
**开**球上逐点 `C^∞` 且 `fderiv` 单射（G2 证明的开集部分）。 -/
theorem radial_extension_seam_smooth_open_R13 {β : ℂ → ℂ} {t₀ ε : ℝ} (hε : 0 < ε)
    (hβS : MapsTo β (Metric.sphere 0 1) (Metric.sphere 0 1))
    (hβs : ContDiffOn ℝ ∞ (fun t : ℝ => β (exp (t * I))) (Ioo (t₀ - ε) (t₀ + ε)))
    (hβ' : deriv (fun t : ℝ => β (exp (t * I))) t₀ ≠ 0) :
    ∃ δ > 0, ∀ z ∈ Metric.ball (exp (t₀ * I)) δ,
      ContDiffAt ℝ ∞ (radialExtension_R13 β) z ∧
        Function.Injective (fderiv ℝ (radialExtension_R13 β) z) := by
  set g : ℝ → ℂ := fun t => β (exp (t * I)) with hgdef
  have hIoo : Ioo (t₀ - ε) (t₀ + ε) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hcont : ContinuousAt (deriv g) t₀ :=
    (hβs.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).continuousAt hIoo
  have hev : ∀ᶠ t in 𝓝 t₀, deriv g t ≠ 0 ∧ t ∈ Ioo (t₀ - ε) (t₀ + ε) :=
    (hcont.eventually_ne hβ').and hIoo
  obtain ⟨ε₁, hε₁, hε₁g⟩ := Metric.eventually_nhds_iff.mp hev
  have hξ₀ : ‖exp (t₀ * I)‖ = 1 := norm_exp_ofReal_mul_I t₀
  have hθc : ContinuousAt (seamAngle_R13 t₀) (exp (t₀ * I)) :=
    (contDiffAt_seamAngle_R13 t₀ (by simp)).continuousAt
  obtain ⟨δ₁, hδ₁, hδ₁θ⟩ := Metric.continuousAt_iff.mp hθc ε₁ hε₁
  refine ⟨min δ₁ (1 / 2), lt_min hδ₁ (by norm_num), fun z hz => ?_⟩
  rw [Metric.mem_ball, lt_min_iff] at hz
  have hzn : ‖z - exp (t₀ * I)‖ < 1 / 2 := by rw [← dist_eq_norm]; exact hz.2
  have h1 : ‖z - exp (t₀ * I)‖ < 1 := hzn.trans (by norm_num)
  have h0 : z ≠ 0 := by
    rintro rfl
    rw [zero_sub, norm_neg, hξ₀] at hzn
    norm_num at hzn
  have hθ := hδ₁θ hz.1
  rw [seamAngle_self_R13] at hθ
  obtain ⟨hd, hI⟩ := hε₁g hθ
  have hCD := contDiffAt_radialExtension_seam_R13 hβs h1 h0 hI
  have hgd : DifferentiableAt ℝ g (seamAngle_R13 t₀ z) :=
    ((hβs.contDiffAt (isOpen_Ioo.mem_nhds hI)).differentiableAt (by simp))
  exact ⟨hCD, injective_fderiv_radialExtension_R13 hβS h0 (hCD.differentiableAt (by simp))
    (exp_seamAngle_R13 t₀ h0) hgd hd⟩

/-- `f` 在有限 corner 集 `Cb + ℤ` 之外 `C^∞`、在 `t₀` 也 `C^∞` ⇒ 在 `t₀` 的一个球上处处 `C^∞`。 -/
theorem exists_ball_contDiffAt_of_finite_R13 {f : ℝ → ℂ} {t₀ : ℝ} (Cb : Finset ℝ)
    (hpw : ∀ t, (∀ s ∈ Cb, ∀ m : ℤ, t ≠ s + m) → ContDiffAt ℝ ∞ f t)
    (ht₀ : ContDiffAt ℝ ∞ f t₀) : ∃ ε > 0, ∀ t ∈ Metric.ball t₀ ε, ContDiffAt ℝ ∞ f t := by
  classical
  let Cb' : Finset ℝ := Cb.filter fun s => ∀ m : ℤ, t₀ ≠ s + m
  obtain ⟨ε, hε, hnc⟩ := IsCorneredJordanDisk_R13.exists_ball_noncorner Cb'
    (fun s hs => (Finset.mem_filter.mp hs).2)
  refine ⟨min ε (1 / 2), lt_min hε (by norm_num), fun t ht => ?_⟩
  by_cases htt : t = t₀
  · rw [htt]; exact ht₀
  apply hpw
  intro s hs m hm
  by_cases hs' : ∀ m : ℤ, t₀ ≠ s + m
  · exact hnc t (Metric.ball_subset_ball (min_le_left _ _) ht) s
      (Finset.mem_filter.mpr ⟨hs, hs'⟩) m hm
  · push Not at hs'
    obtain ⟨m₀, hm₀⟩ := hs'
    have hd : |((m : ℝ) - m₀)| < 1 / 2 := by
      have h := Metric.mem_ball.mp (Metric.ball_subset_ball (min_le_right _ _) ht)
      rw [Real.dist_eq, hm, hm₀] at h
      convert h using 2
      ring
    have : m = m₀ := by
      have h1 : (m : ℝ) - m₀ < 1 := by linarith [(abs_lt.mp hd).2]
      have h2 : (-1 : ℝ) < m - m₀ := by linarith [(abs_lt.mp hd).1]
      have h1' : m - m₀ < 1 := by exact_mod_cast h1
      have h2' : -1 < m - m₀ := by exact_mod_cast h2
      omega
    exact htt (hm.trans (this ▸ hm₀.symm))

/-- **G5（由 straightening 数据拼装）**：`F₂`（`Ω₂` 的 straightening，在 `ξ₂`（`F₂ ξ₂ = c₂ t₀`）的开邻域
`V₂` 上 `C^∞`、`fderiv` 单射）与 `F₁`（`Ω₁` 的 straightening，在 `ξ₁`（`F₁ ξ₁ = b (c₂ t₀)`）的开邻域上同样
光滑）给出 MYD3 `bilipschitz_schoenflies_seam_MYD3` 的结论：`B = F₁ ∘ E_β ∘ F₂⁻¹` bi-Lipschitz、
`BijOn B Ω₂ Ω₁`、`B = b` on `∂Ω₂`，且在 `c₂ t₀` 附近 `Ω₂` 一侧 `C^∞`、`fderivWithin` 单射。 -/
theorem bilipschitz_schoenflies_seam_of_straightening_R13
    {Ω₁ Ω₂ : Set ℂ} {c₂ : ℝ → ℂ} {C₂ : Finset ℝ} (h₂ : IsCorneredJordanDisk_R13 Ω₂ c₂ C₂)
    {b : ℂ → ℂ} (hb : BilipschitzOn_R13 b (frontier Ω₂))
    (hbij : BijOn b (frontier Ω₂) (frontier Ω₁))
    (hbpw : ∃ Cb : Finset ℝ, ∀ t, (∀ s ∈ Cb, ∀ m : ℤ, t ≠ s + m) → ContDiffAt ℝ ∞ (b ∘ c₂) t)
    {t₀ : ℝ} (ht₀ : ∀ s ∈ C₂, ∀ m : ℤ, t₀ ≠ s + m) (hbt₀ : ContDiffAt ℝ ∞ (b ∘ c₂) t₀)
    {F₁ : ℂ → ℂ} (hF₁ : BilipschitzOn_R13 F₁ (Metric.closedBall 0 1))
    (hF₁b : BijOn F₁ (Metric.closedBall 0 1) Ω₁)
    (hF₁s : BijOn F₁ (Metric.sphere 0 1) (frontier Ω₁))
    {ξ₁ : ℂ} (hξ₁ : ξ₁ ∈ Metric.sphere (0 : ℂ) 1) (hF₁ξ : F₁ ξ₁ = b (c₂ t₀))
    {V₁ : Set ℂ} (hV₁ : IsOpen V₁) (hξV₁ : ξ₁ ∈ V₁) (hF₁sm : ContDiffOn ℝ ∞ F₁ V₁)
    (hF₁i : ∀ z ∈ V₁, Function.Injective (fderiv ℝ F₁ z))
    {F₂ : ℂ → ℂ} (hF₂ : BilipschitzOn_R13 F₂ (Metric.closedBall 0 1))
    (hF₂b : BijOn F₂ (Metric.closedBall 0 1) Ω₂)
    (hF₂s : BijOn F₂ (Metric.sphere 0 1) (frontier Ω₂))
    {ξ₂ : ℂ} (hξ₂ : ξ₂ ∈ Metric.sphere (0 : ℂ) 1) (hF₂ξ : F₂ ξ₂ = c₂ t₀)
    {V₂ : Set ℂ} (hV₂ : IsOpen V₂) (hξV₂ : ξ₂ ∈ V₂) (hF₂sm : ContDiffOn ℝ ∞ F₂ V₂)
    (hF₂i : ∀ z ∈ V₂, Function.Injective (fderiv ℝ F₂ z)) :
    ∃ B : ℂ → ℂ, BilipschitzOn_R13 B Ω₂ ∧ BijOn B Ω₂ Ω₁ ∧ EqOn B b (frontier Ω₂) ∧
      ∃ δ > 0, ContDiffOn ℝ ∞ B (Metric.ball (c₂ t₀) δ ∩ Ω₂) ∧
        ∀ z ∈ Metric.ball (c₂ t₀) δ ∩ Ω₂, Function.Injective (fderivWithin ℝ B Ω₂ z) := by
  classical
  set w : ℂ := c₂ t₀ with hwdef
  set β : ℂ → ℂ := schoenfliesBoundary_R13 F₁ F₂ b with hβdef
  obtain ⟨-, hβbij, hBL, hBb, hBeq⟩ :=
    schoenfliesMap_global_R13 hF₁ hF₁b hF₁s hF₂ hF₂b hF₂s hb hbij
  refine ⟨schoenfliesMap_R13 F₁ F₂ b, hBL, hBb, hBeq, ?_⟩
  have hSD : Metric.sphere (0 : ℂ) 1 ⊆ Metric.closedBall 0 1 := Metric.sphere_subset_closedBall
  have hfr₁ : frontier Ω₁ ⊆ Ω₁ := by
    intro y hy
    obtain ⟨ξ, hξ, rfl⟩ := hF₁s.surjOn hy
    exact hF₁b.mapsTo (hSD hξ)
  have hwfr : w ∈ frontier Ω₂ := by rw [h₂.2.2.1]; exact mem_range_self t₀
  -- 局部逆
  obtain ⟨N₂, hN₂, hwN₂, φ₂, hφ₂, hφ₂V, hFφ₂, hφ₂w, hφ₂c⟩ :=
    exists_local_inverse_R13 hF₂ hF₂b (hSD hξ₂) hV₂ hξV₂ hF₂sm hF₂i
  rw [hF₂ξ] at hwN₂ hφ₂w
  obtain ⟨N₁, hN₁, hbwN₁, φ₁, hφ₁, -, -, hφ₁bw, hφ₁c⟩ :=
    exists_local_inverse_R13 hF₁ hF₁b (hSD hξ₁) hV₁ hξV₁ hF₁sm hF₁i
  rw [hF₁ξ] at hbwN₁ hφ₁bw
  -- 角参数
  set t₂ : ℝ := arg ξ₂ with ht₂def
  have hξ₂e : exp (t₂ * I) = ξ₂ := by
    have h := norm_mul_exp_arg_mul_I ξ₂
    rwa [mem_sphere_zero_iff_norm.mp hξ₂, ofReal_one, one_mul] at h
  have hexp : ContDiff ℝ ∞ (fun t : ℝ => exp (t * I)) :=
    (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)).comp (ofRealCLM.contDiff.mul contDiff_const)
  have hexpS : ∀ t : ℝ, exp (t * I) ∈ Metric.sphere (0 : ℂ) 1 := fun t => by
    rw [mem_sphere_zero_iff_norm, norm_exp_ofReal_mul_I]
  obtain ⟨ε₀, hε₀, hε₀sub⟩ := Metric.mem_nhds_iff.mp
    (hexp.continuous.continuousAt (x := t₂) |>.preimage_mem_nhds
      (by rw [hξ₂e]; exact hV₂.mem_nhds hξV₂))
  -- 边界曲线 `γ t = F₂ (e^{it})`
  set γ : ℝ → ℂ := fun t => F₂ (exp (t * I)) with hγdef
  have hγfr : ∀ t, γ t ∈ frontier Ω₂ := fun t => hF₂s.mapsTo (hexpS t)
  have hγs : ContDiffOn ℝ ∞ γ (Metric.ball t₂ ε₀) :=
    hF₂sm.comp hexp.contDiffOn fun t ht => hε₀sub ht
  have hγt : γ t₂ = c₂ t₀ := by
    change F₂ (exp (t₂ * I)) = c₂ t₀
    rw [hξ₂e, hF₂ξ]
  obtain ⟨ε₁, hε₁, hε₁le, sp, hsp, hspt, hγsp⟩ := exists_arc_reparam_R13 h₂ ht₀ hε₀ hγfr hγs hγt
  -- `b ∘ c₂` 在 `t₀` 附近 `C^∞`
  obtain ⟨Cb, hCb⟩ := hbpw
  obtain ⟨εb, hεb, hbsm⟩ := exists_ball_contDiffAt_of_finite_R13 Cb hCb hbt₀
  have hspc : ContinuousAt sp t₂ := (hsp.contDiffAt (Metric.ball_mem_nhds t₂ hε₁)).continuousAt
  have hbcc : ContinuousAt (b ∘ c₂ ∘ sp) t₂ := by
    have h1 : ContinuousAt (b ∘ c₂) (sp t₂) := by
      rw [hspt]; exact hbt₀.continuousAt
    exact h1.comp hspc
  have hbN : b (c₂ (sp t₂)) ∈ N₁ := by rw [hspt]; exact hbwN₁
  obtain ⟨ε₂, hε₂, hε₂sub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (Filter.inter_mem (Metric.ball_mem_nhds t₂ hε₁)
      (hspc.preimage_mem_nhds (by rw [hspt]; exact Metric.ball_mem_nhds t₀ hεb)))
      (hbcc.preimage_mem_nhds (hN₁.mem_nhds hbN)))
  have hball₂ : ∀ t ∈ Metric.ball t₂ ε₂, t ∈ Metric.ball t₂ ε₁ ∧ sp t ∈ Metric.ball t₀ εb ∧
      b (c₂ (sp t)) ∈ N₁ := fun t ht => ⟨(hε₂sub ht).1.1, (hε₂sub ht).1.2, (hε₂sub ht).2⟩
  -- `g t = β (e^{it}) = φ₁ (b (c₂ (sp t)))`
  have hgeq : ∀ t ∈ Metric.ball t₂ ε₂, β (exp (t * I)) = φ₁ (b (c₂ (sp t))) := by
    intro t ht
    obtain ⟨h1, -, h3⟩ := hball₂ t ht
    have hγ' : γ t = c₂ (sp t) := hγsp t h1
    have hmem : b (c₂ (sp t)) ∈ N₁ ∩ Ω₁ := by
      refine ⟨h3, hfr₁ (hbij.mapsTo ?_)⟩
      rw [← hγ']
      exact hγfr t
    rw [hφ₁c _ hmem]
    change Function.invFunOn F₁ (Metric.closedBall 0 1) (b (γ t)) = _
    rw [hγ']
  have hhsm : ∀ t ∈ Metric.ball t₂ ε₂, ContDiffAt ℝ ∞ (fun t => φ₁ (b (c₂ (sp t)))) t := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hball₂ t ht
    have hspa : ContDiffAt ℝ ∞ sp t := hsp.contDiffAt (Metric.isOpen_ball.mem_nhds h1)
    exact (hφ₁ _ h3).1.comp t ((hbsm _ h2).comp t hspa)
  have hβs : ContDiffOn ℝ ∞ (fun t : ℝ => β (exp (t * I))) (Ioo (t₂ - ε₂) (t₂ + ε₂)) := by
    intro t ht
    rw [← Real.ball_eq_Ioo] at ht
    refine ((hhsm t ht).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with t' ht'
    exact hgeq t' ht'
  -- `(b∘c₂)′(t₀) ≠ 0`（lower Lipschitz）
  have hc₂d : DifferentiableAt ℝ c₂ t₀ :=
    (h₂.2.2.2.2.2.2.2.1 t₀ ht₀).1.differentiableAt (by simp)
  have hc₂' : deriv c₂ t₀ ≠ 0 := (h₂.2.2.2.2.2.2.2.1 t₀ ht₀).2
  have hbcd : DifferentiableAt ℝ (b ∘ c₂) t₀ := hbt₀.differentiableAt (by simp)
  have hD : deriv (b ∘ c₂) t₀ ≠ 0 := by
    obtain ⟨K, hK⟩ := hb
    have hle := norm_deriv_le_of_lower_lipschitz_R13 (K := K) hbcd.hasDerivAt hc₂d.hasDerivAt
      (fun s => by
        have hs : c₂ s ∈ frontier Ω₂ := by rw [h₂.2.2.1]; exact mem_range_self s
        have h := (hK _ hs _ hwfr).2
        rw [dist_eq_norm, dist_eq_norm] at h
        exact h)
    intro h0
    rw [h0, norm_zero, mul_zero] at hle
    exact hc₂' (norm_le_zero_iff.mp hle)
  -- `sp′(t₂) ≠ 0`
  have hspd : DifferentiableAt ℝ sp t₂ :=
    (hsp.contDiffAt (Metric.ball_mem_nhds t₂ hε₁)).differentiableAt (by simp)
  have hsp' : deriv sp t₂ ≠ 0 := by
    have hF₂d : DifferentiableAt ℝ F₂ ξ₂ :=
      (hF₂sm.contDiffAt (hV₂.mem_nhds hξV₂)).differentiableAt (by simp)
    have hexpd : HasDerivAt (fun t : ℝ => exp (t * I)) (ξ₂ * I) t₂ := by
      have h := ((hasDerivAt_id t₂).ofReal_comp.mul_const I).cexp
      simpa [hξ₂e] using h
    have hγd : HasDerivAt γ (fderiv ℝ F₂ ξ₂ (ξ₂ * I)) t₂ := by
      have hF : HasFDerivAt F₂ (fderiv ℝ F₂ ξ₂) (exp (t₂ * I)) := by
        rw [hξ₂e]; exact hF₂d.hasFDerivAt
      exact HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => exp (t * I)) t₂ hF hexpd
    have hcs : HasDerivAt (c₂ ∘ sp) (deriv sp t₂ • deriv c₂ t₀) t₂ := by
      have hc : HasDerivAt c₂ (deriv c₂ t₀) (sp t₂) := by rw [hspt]; exact hc₂d.hasDerivAt
      exact hc.scomp t₂ hspd.hasDerivAt
    have heq : γ =ᶠ[𝓝 t₂] c₂ ∘ sp := by
      filter_upwards [Metric.ball_mem_nhds t₂ hε₁] with t ht
      exact hγsp t ht
    have hu := hγd.unique (hcs.congr_of_eventuallyEq heq)
    intro h0
    rw [h0, zero_smul] at hu
    have hξI : ξ₂ * I = 0 := hF₂i ξ₂ hξV₂ (hu.trans (map_zero _).symm)
    have hξ0 : ξ₂ ≠ 0 := by
      rintro rfl
      simp at hξ₂
    exact mul_ne_zero hξ0 I_ne_zero hξI
  -- `deriv g t₂ ≠ 0`
  have hβ' : deriv (fun t : ℝ => β (exp (t * I))) t₂ ≠ 0 := by
    have heq : (fun t : ℝ => β (exp (t * I))) =ᶠ[𝓝 t₂] fun t => φ₁ (b (c₂ (sp t))) := by
      filter_upwards [Metric.ball_mem_nhds t₂ hε₂] with t ht
      exact hgeq t ht
    rw [heq.deriv_eq]
    have hbc : HasDerivAt (b ∘ c₂) (deriv (b ∘ c₂) t₀) (sp t₂) := by
      rw [hspt]; exact hbcd.hasDerivAt
    have h1 : HasDerivAt ((b ∘ c₂) ∘ sp) (deriv sp t₂ • deriv (b ∘ c₂) t₀) t₂ :=
      hbc.scomp t₂ hspd.hasDerivAt
    have hφ₁d : HasFDerivAt φ₁ (fderiv ℝ φ₁ (b w)) (((b ∘ c₂) ∘ sp) t₂) := by
      change HasFDerivAt φ₁ _ (b (c₂ (sp t₂)))
      rw [hspt]
      exact ((hφ₁ _ hbwN₁).1.differentiableAt (by simp)).hasFDerivAt
    have h2 := HasFDerivAt.comp_hasDerivAt (f := (b ∘ c₂) ∘ sp) t₂ hφ₁d h1
    rw [show (fun t => φ₁ (b (c₂ (sp t)))) = φ₁ ∘ ((b ∘ c₂) ∘ sp) from rfl, h2.deriv]
    intro h0
    have h3 := (hφ₁ _ hbwN₁).2 (h0.trans (map_zero _).symm)
    exact smul_ne_zero hsp' hD h3
  -- 开集版 G2：`E_β` 在 `ξ₂` 的开球上光滑、导数单射
  obtain ⟨δE, hδE, hE⟩ := radial_extension_seam_smooth_open_R13 hε₂ hβbij.mapsTo hβs hβ'
  rw [hξ₂e] at hE
  set E : ℂ → ℂ := radialExtension_R13 β with hEdef
  have hEξ₂ : E ξ₂ = ξ₁ := by
    rw [hEdef, radialExtension_eqOn_sphere_R13 β hξ₂]
    change Function.invFunOn F₁ (Metric.closedBall 0 1) (b (F₂ ξ₂)) = ξ₁
    rw [hF₂ξ, ← hF₁ξ]
    exact invFunOn_eq_of_injOn_R13 hF₁b.injOn (hSD hξ₁)
  have hEc : ContinuousAt E ξ₂ := (hE ξ₂ (Metric.mem_ball_self hδE)).1.continuousAt
  obtain ⟨δa, hδa, hδasub⟩ := Metric.mem_nhds_iff.mp
    (hEc.preimage_mem_nhds (by rw [hEξ₂]; exact hV₁.mem_nhds hξV₁))
  have hφ₂cont : ContinuousAt φ₂ w := (hφ₂ w hwN₂).1.continuousAt
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hN₂.mem_nhds hwN₂)
    (hφ₂cont.preimage_mem_nhds (by rw [hφ₂w]; exact Metric.ball_mem_nhds ξ₂ (lt_min hδE hδa))))
  have hpt : ∀ y ∈ Metric.ball w δ, y ∈ N₂ ∧ φ₂ y ∈ Metric.ball ξ₂ δE ∧ E (φ₂ y) ∈ V₁ := by
    intro y hy
    obtain ⟨h1, h2⟩ := hδsub hy
    have h2' : φ₂ y ∈ Metric.ball ξ₂ (min δE δa) := h2
    exact ⟨h1, Metric.ball_subset_ball (min_le_left _ _) h2',
      hδasub (Metric.ball_subset_ball (min_le_right _ _) h2')⟩
  -- 局部模型 `B̃ = F₁ ∘ E_β ∘ φ₂`
  set Bt : ℂ → ℂ := fun y => F₁ (E (φ₂ y)) with hBtdef
  have hBt : ∀ y ∈ Metric.ball w δ, ContDiffAt ℝ ∞ Bt y ∧ Function.Injective (fderiv ℝ Bt y) := by
    intro y hy
    obtain ⟨h1, h2, h3⟩ := hpt y hy
    have hF₁a : ContDiffAt ℝ ∞ F₁ (E (φ₂ y)) := hF₁sm.contDiffAt (hV₁.mem_nhds h3)
    have hEa := hE _ h2
    have hφa := hφ₂ y h1
    refine ⟨hF₁a.comp y (hEa.1.comp y hφa.1), ?_⟩
    have hd1 : DifferentiableAt ℝ F₁ (E (φ₂ y)) := hF₁a.differentiableAt (by simp)
    have hd2 : DifferentiableAt ℝ E (φ₂ y) := hEa.1.differentiableAt (by simp)
    have hd3 : DifferentiableAt ℝ φ₂ y := hφa.1.differentiableAt (by simp)
    have hcomp : fderiv ℝ Bt y =
        (fderiv ℝ F₁ (E (φ₂ y))).comp ((fderiv ℝ E (φ₂ y)).comp (fderiv ℝ φ₂ y)) := by
      change fderiv ℝ (F₁ ∘ (E ∘ φ₂)) y = _
      rw [fderiv_comp y hd1 (hd2.comp y hd3), fderiv_comp y hd2 hd3]
      rfl
    rw [hcomp]
    exact (hF₁i _ h3).comp (hEa.2.comp hφa.2)
  have heqB : ∀ y ∈ Metric.ball w δ ∩ Ω₂, schoenfliesMap_R13 F₁ F₂ b y = Bt y := by
    intro y hy
    change F₁ (E (Function.invFunOn F₂ (Metric.closedBall 0 1) y)) = F₁ (E (φ₂ y))
    rw [hφ₂c y ⟨(hpt y hy.1).1, hy.2⟩]
  refine ⟨δ, hδ, fun y hy => ((hBt y hy.1).1.contDiffWithinAt).congr
    (fun y' hy' => heqB y' hy') (heqB y hy), ?_⟩
  intro y hy
  have hev : schoenfliesMap_R13 F₁ F₂ b =ᶠ[𝓝[Ω₂] y] Bt := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hy.1)] with y' h1 h2
    exact heqB y' ⟨h2, h1⟩
  rw [hev.fderivWithin_eq (heqB y hy)]
  have huniq : UniqueDiffWithinAt ℝ Ω₂ y := by
    have h1 := (hpt y hy.1).1
    have hxD : φ₂ y ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [hφ₂c y ⟨h1, hy.2⟩]
      exact hF₂b.surjOn.mapsTo_invFunOn hy.2
    have hxV : φ₂ y ∈ V₂ := hφ₂V h1
    have hFx : F₂ (φ₂ y) = y := hFφ₂ y h1
    have hd : DifferentiableAt ℝ F₂ (φ₂ y) :=
      (hF₂sm.contDiffAt (hV₂.mem_nhds hxV)).differentiableAt (by simp)
    have hDu : UniqueDiffWithinAt ℝ (Metric.closedBall (0 : ℂ) 1) (φ₂ y) :=
      uniqueDiffOn_convex (convex_closedBall 0 1)
        ⟨0, by rw [interior_closedBall _ one_ne_zero]; simp⟩ _ hxD
    have h := hd.hasFDerivAt.hasFDerivWithinAt.uniqueDiffWithinAt hDu
      (surjective_of_injective_R13 (hF₂i _ hxV)).denseRange
    rwa [hF₂b.image_eq, hFx] at h
  rw [((hBt y hy.1).1.differentiableAt (by simp)).fderivWithin huniq]
  exact (hBt y hy.1).2

end DifferentialGeometry.Geometry
