import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskLiftDiffeoAT
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothTraceLift
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk

/-!
# S-A08-ATTAIN G1：嵌入的 Morrey 盘 ⇒ `isExteriorSpanningDisk`（精确迹）

`IsMorreyDisk.trace` 只给弱 Jordan trace：`diskTrace u = γ ∘ σ`，`σ` 弱单调。
在显式嵌入性假设下（`SmoothDiskExtension u U`、`IsEmbedding u`、`dU` 在闭盘上单射）：

1. `DiskWeakJordanTrace.exists_smooth_signed_lift`：`σ` 有 smooth lift `ψ`；
2. `deriv_lift_ne_zero_AT`：`U (exp (2π i t)) = γ (ψ t)` 对 `t` 求导，`dU` 单射 ⇒ `ψ' ≠ 0`；
3. `exists_disk_diffeomorph_of_lift_AT`：由 lift 造 `Φ : ℂ ≃ₘ ℂ`，`Φ (exp (2π i t)) = exp (2π i ψ t)`；
4. `σ` 单射（`u` 嵌入）+ 满射（lift 的 IVT）⇒ `σ` 是同胚；取 `φ := Φ.symm` 的限制，
   则 `u ∘ φ` 的 trace 恰为 `γ`，光滑延拓 `U ∘ Φ.symm` 的导数仍单射
   （沿用 `isExteriorSpanningDisk.comp_smooth_disk_reparametrization`）；
5. 面积不变：`isExteriorSpanningDisk.area_comp_reparametrization`（`φ`、`φ.symm` 在闭盘上 Lipschitz）。

不引入新结构：嵌入性只作为显式存在性假设 `hemb`。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.Geometry.MinimalSurface

/-- `ℂ` 的 diffeomorphism `Φ` 若保持 closed ball，则限制出 `closedDisk` 的同胚 `φ`，
且 `φ`、`φ.symm` 都是 Lipschitz。 -/
theorem exists_closedDisk_homeomorph_of_diffeomorph_AT (Φ : ℂ ≃ₘ[ℝ] ℂ)
    (hΦ : Φ '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall 0 1) :
    ∃ φ : closedDisk ≃ₜ closedDisk, (∀ z : closedDisk, Φ z = (φ z : ℂ)) ∧
      (∃ K : ℝ≥0, LipschitzWith K φ) ∧ ∃ L : ℝ≥0, LipschitzWith L φ.symm := by
  have hmem : ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) 1 → Φ z ∈ Metric.closedBall (0 : ℂ) 1 :=
    fun z hz => hΦ ▸ mem_image_of_mem Φ hz
  have hmem' : ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) 1 →
      Φ.symm z ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    rw [← hΦ] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    simpa using hx
  have hlip : ∀ F : ℂ → ℂ, ContDiff ℝ ∞ F → ∃ K : ℝ≥0,
      LipschitzOnWith K F (Metric.closedBall (0 : ℂ) 1) := fun F hF =>
    hF.contDiffOn.exists_lipschitzOnWith (by simp) (convex_closedBall _ _)
      (isCompact_closedBall _ _)
  let φ : closedDisk ≃ₜ closedDisk :=
    { toFun := fun z => ⟨Φ z, hmem z z.property⟩
      invFun := fun z => ⟨Φ.symm z, hmem' z z.property⟩
      left_inv := fun z => Subtype.ext (Φ.symm_apply_apply z)
      right_inv := fun z => Subtype.ext (Φ.apply_symm_apply z)
      continuous_toFun := (Φ.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (Φ.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨φ, fun z => rfl, ?_, ?_⟩
  · obtain ⟨K, hK⟩ := hlip Φ Φ.contMDiff.contDiff
    exact ⟨K, (hK.to_restrict).subtype_mk _⟩
  · obtain ⟨L, hL⟩ := hlip Φ.symm Φ.symm.contMDiff.contDiff
    exact ⟨L, (hL.to_restrict).subtype_mk _⟩


/-- `t ↦ exp (2π i t)` 的导数不为零（作为 `mfderiv` 作用在 `1` 上）。 -/
theorem mfderiv_diskBoundary_lift_ne_zero_AT (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun s : ℝ => (diskBoundary (s : loopCircle) : ℂ)) t 1 ≠ 0 := by
  have hfun : (fun s : ℝ => (diskBoundary (s : loopCircle) : ℂ)) =
      fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I) :=
    funext diskBoundary_coe
  have hd : HasDerivAt (fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) *
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) t := by
    have h1 : HasDerivAt (fun s : ℝ => ((2 * Real.pi * s : ℝ) : ℂ)) ((2 * Real.pi : ℝ) : ℂ) t := by
      have := (hasDerivAt_id t).const_mul (2 * Real.pi)
      simpa using this.ofReal_comp
    exact (h1.mul_const Complex.I).cexp
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ (fun s : ℝ => (diskBoundary (s : loopCircle) : ℂ)) t 1 ≠ 0
  rw [fderiv_apply_one_eq_deriv, hfun, hd.deriv]
  refine mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero ?_ Complex.I_ne_zero)
  exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)


section Lift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- 弱 Jordan trace 的 smooth lift `ψ` 处处有 `ψ' ≠ 0`：`u` 有光滑延拓 `U` 且 `dU` 在边界单射，
`U (exp (2π i t)) = γ (ψ t)`，对 `t` 求导即得。 -/
theorem deriv_lift_ne_zero_AT {γ : freeLoop M} (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {u : C(closedDisk, M)} {U : ℂ → M} (hU : SmoothDiskExtension (E := E) u U)
    (hinj : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    {σ : C(loopCircle, loopCircle)} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hlift : ∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle))
    (htrace : diskTrace u = γ.comp σ) (t : ℝ) : deriv ψ t ≠ 0 := by
  intro hzero
  let b : ℝ → ℂ := fun s => (diskBoundary (s : loopCircle) : ℂ)
  have hb : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ b := diskBoundary_lift_contMDiff
  have hbt : b t ∈ Metric.closedBall (0 : ℂ) 1 := (diskBoundary (t : loopCircle)).property
  obtain ⟨heq, N, hN, hDN, hUs⟩ := hU
  have hUd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (b t) :=
    (hUs.contMDiffAt (hN.mem_nhds (hDN hbt))).mdifferentiableAt (by simp)
  have hc : (fun s : ℝ => U (b s)) = (fun s : ℝ => γ (s : loopCircle)) ∘ ψ := by
    funext s
    have h1 := heq (diskBoundary (s : loopCircle))
    have h2 := congrArg (fun f : freeLoop M => f (s : loopCircle)) htrace
    change u (diskBoundary (s : loopCircle)) = γ (σ (s : loopCircle)) at h2
    change U (b s) = γ (ψ s : loopCircle)
    rw [h1, h2, hlift]
  have hγc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => γ (s : loopCircle)) := hγ.smooth
  have hcomp1 := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℂ)) (I'' := 𝓘(ℝ, E)) t hUd
    (hb.mdifferentiableAt (x := t) (by simp))
  have hcomp2 := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, E)) t
    (hγc.mdifferentiableAt (x := ψ t) (by simp)) (hψ.contMDiff.mdifferentiableAt (x := t) (by simp))
  have hψ1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ψ t 1 = 0 := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ ψ t 1 = 0
    rw [fderiv_apply_one_eq_deriv, hzero]
  have hev : (fun s : ℝ => U (b s)) =ᶠ[nhds t] (fun s : ℝ => γ (s : loopCircle)) ∘ ψ :=
    Filter.Eventually.of_forall (congrFun hc)
  have he := hev.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
  have hfin : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (b t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) b t 1) = 0 := by
    have h := DFunLike.congr_fun (hcomp1.symm.trans (he.trans hcomp2)) 1
    rw [ContinuousLinearMap.comp_apply] at h
    exact h.trans ((congrArg (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) (ψ t))
      hψ1).trans (map_zero _))
  exact mfderiv_diskBoundary_lift_ne_zero_AT t
    (hinj _ hbt (hfin.trans (map_zero _).symm))


/-- `diskBoundary` 是单射。 -/
theorem diskBoundary_injective_AT :
    Function.Injective (diskBoundary : loopCircle → closedDisk) := by
  intro θ θ' h
  have h1 : ((diskBoundary θ : closedDisk) : ℂ) = ((diskBoundary θ' : closedDisk) : ℂ) :=
    congrArg Subtype.val h
  exact AddCircle.injective_toCircle one_ne_zero (Subtype.ext h1)

/-- 带符号的单调 lift `ψ`（`ψ (t+1) = ψ t ± 1`）是满射。 -/
theorem surjective_of_lift_sign_AT {ψ : ℝ → ℝ} (hc : Continuous ψ)
    (hsign : (Monotone ψ ∧ ∀ t, ψ (t + 1) = ψ t + 1) ∨
      (Antitone ψ ∧ ∀ t, ψ (t + 1) = ψ t - 1)) : Function.Surjective ψ := by
  rcases hsign with ⟨_, hp⟩ | ⟨_, hp⟩
  · exact surjective_of_periodic_lift_AT hc hp
  · intro y
    obtain ⟨t, ht⟩ := surjective_of_periodic_lift_AT (g := fun t => -ψ t) hc.neg
      (fun t => by simp only [hp]; ring) (-y)
    exact ⟨t, by simpa using ht⟩

/-- **精确迹 reparametrization 的几何数据**。`u` 有弱 Jordan trace（`diskTrace u = γ ∘ σ`）、
光滑延拓 `U` 且 `dU` 在闭盘上单射、`u` 是嵌入时：`σ` 是 `loopCircle` 的同胚，
且存在 `ℂ` 的 diffeomorphism `Φ`（保 closed ball）使其限制 `φ` 在边界上是 `σ⁻¹`。 -/
theorem exists_exactTrace_reparametrization_AT {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)}
    (hwj : DiskWeakJordanTrace γ u) {U : ℂ → M} (hU : SmoothDiskExtension (E := E) u U)
    (hemb : Topology.IsEmbedding u)
    (hinj : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    ∃ (σ : C(loopCircle, loopCircle)) (ψc : loopCircle ≃ₜ loopCircle)
      (φ : closedDisk ≃ₜ closedDisk) (Φ : ℂ ≃ₘ[ℝ] ℂ),
      diskTrace u = γ.comp σ ∧ (∀ θ, σ (ψc θ) = θ) ∧ (∀ z : closedDisk, Φ z = (φ z : ℂ)) ∧
      (∀ θ, φ (diskBoundary θ) = diskBoundary (ψc θ)) ∧
      (∃ K : ℝ≥0, LipschitzWith K φ) ∧ ∃ L : ℝ≥0, LipschitzWith L φ.symm := by
  obtain ⟨σ, ψ, hψs, hlift, htrace, hsign⟩ :=
    hwj.exists_smooth_signed_lift hγ hU.smoothUpToBoundary
  have hder := deriv_lift_ne_zero_AT hγ hU hinj hψs hlift htrace
  obtain ⟨Φ₀, hΦ₀b, hΦ₀B⟩ := exists_disk_diffeomorph_of_lift_AT hψs hder hsign
  have hΦB : Φ₀.symm '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall 0 1 := by
    conv_lhs => rw [← hΦ₀B]
    rw [Set.image_image]
    simp
  obtain ⟨φ, hΦφ, hK, hL⟩ := exists_closedDisk_homeomorph_of_diffeomorph_AT Φ₀.symm hΦB
  have hσinj : Function.Injective σ := by
    have h1 : Function.Injective (γ ∘ σ) := by
      have : (γ ∘ σ : loopCircle → M) = u ∘ diskBoundary := by
        funext θ
        exact (congrArg (fun f : freeLoop M => f θ) htrace).symm
      rw [this]
      exact hemb.injective.comp diskBoundary_injective_AT
    exact Function.Injective.of_comp h1
  have hσsurj : Function.Surjective σ := by
    intro θ
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective θ
    obtain ⟨t, ht⟩ := surjective_of_lift_sign_AT hψs.continuous hsign s
    exact ⟨(t : loopCircle), by rw [← hlift, ht]⟩
  let σh : loopCircle ≃ₜ loopCircle :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective σ ⟨hσinj, hσsurj⟩) σ.continuous
  have hσh : ∀ θ, σ (σh.symm θ) = θ := fun θ => σh.apply_symm_apply θ
  refine ⟨σ, σh.symm, φ, Φ₀.symm, htrace, hσh, fun z => hΦφ z, fun θ => ?_, hK, hL⟩
  apply Subtype.ext
  rw [← hΦφ]
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (σh.symm θ)
  have hx : (diskBoundary θ : ℂ) = Φ₀ (diskBoundary (σh.symm θ) : ℂ) := by
    rw [← ht, hΦ₀b, hlift, ht, hσh]
  rw [hx, Φ₀.symm_apply_apply]

end Lift


section G1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M]

/-- **G1.**  嵌入的 Morrey 盘 ⇒ 精确迹的 exterior spanning disk，且面积不变。
`hemb` 是 O-A08 的 `hMY` 所隔离的嵌入性义务（光滑延拓、`IsEmbedding u`、闭盘上 `dU` 单射）。 -/
theorem isExteriorSpanningDisk_of_morrey_AT
    (g : SmoothRiemannianMetric (𝓡 3) M) {W : Set M} {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γ) {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) (hrange : Set.range u ⊆ W)
    (hint : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → u z ∈ interior W)
    (hfront : Set.range γ ⊆ frontier W)
    (hemb : ∃ U : ℂ → M, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U ∧
      Topology.IsEmbedding u ∧ ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z)) :
    ∃ u' : C(closedDisk, M), isExteriorSpanningDisk W γ u' ∧
      riemannianDiskArea g u' = riemannianDiskArea g u := by
  obtain ⟨U, hU, hemb', hinj⟩ := hemb
  obtain ⟨σ, ψc, φ, Φ, htrace, hσψ, hΦφ, hbd, ⟨K, hK⟩, ⟨L, hL⟩⟩ :=
    exists_exactTrace_reparametrization_AT hγ hu.trace hU hemb' hinj
  have hE : isExteriorSpanningDisk W (γ.comp σ) u :=
    ⟨htrace, fun _ ⟨θ, hθ⟩ => hfront ⟨σ θ, hθ⟩, hemb', hrange, hint, U, hU, hinj⟩
  have hE' := hE.comp_smooth_disk_reparametrization φ ψc Φ hΦφ hbd
  have hγeq : (γ.comp σ).comp ⟨ψc, ψc.continuous⟩ = γ := by
    ext θ
    exact congrArg γ (hσψ θ)
  rw [hγeq] at hE'
  exact ⟨u.comp ⟨φ, φ.continuous⟩, hE', hE.area_comp_reparametrization g φ hK hL⟩

/-- Consumer of G1：嵌入的 Morrey 盘的面积给出 `leastExteriorDiskArea` 的上界
（G1 的 `u'` 属于 exterior class，面积等于 `u` 的面积）。 -/
theorem leastExteriorDiskArea_le_of_morrey_AT
    (g : SmoothRiemannianMetric (𝓡 3) M) {W : Set M} {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γ) {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) (hrange : Set.range u ⊆ W)
    (hint : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → u z ∈ interior W)
    (hfront : Set.range γ ⊆ frontier W)
    (hemb : ∃ U : ℂ → M, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U ∧
      Topology.IsEmbedding u ∧ ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z)) :
    leastExteriorDiskArea g W γ ≤ riemannianDiskArea g u := by
  obtain ⟨u', hu', harea⟩ := isExteriorSpanningDisk_of_morrey_AT g hγ hu hrange hint hfront hemb
  rw [← harea]
  exact leastExteriorDiskArea_le g W γ u' hu'

end G1

end DifferentialGeometry.Geometry.MinimalSurface
