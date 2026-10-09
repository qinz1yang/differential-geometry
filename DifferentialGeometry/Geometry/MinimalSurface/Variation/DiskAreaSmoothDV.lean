import DifferentialGeometry.Analysis.ODE.AreaUpperBarrierDV
import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskAreaTwoParameterDV
import DifferentialGeometry.Geometry.Measure.Area.Positivity
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# G3（S-A10-DERIV）：`Ā(t) = Area_{G t}(Φ_t ∘ u)` 在 `t₀` 邻域上 `C^∞`

假设与 G2 相同（去掉 conformal / harmonic），再加 closed disk 上的 immersion
（`Function.Injective (mfderiv … U z)`，正是 `isExteriorSpanningDisk` 的最后一个合取项）。
证明：`Ā(t) = ∫_{closedBall} riemannianAreaDensity (H t) U`，`H t = Φ_t^* G t`，被积函数
`√(E G - F²)` 在 `(t, z)` 上联合 `C^∞`（Gram 行列式在 `{t₀} × closedBall` 上为正，tube lemma
给出 `t` 的开邻域），再用 smooth cutoff + `contDiffOn_convolution_left_with_param` 得到
参数积分的 `C^∞`。没有新 def / structure。
-/

set_option autoImplicit false
noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter MeasureTheory Metric
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold Convolution

namespace DifferentialGeometry.Geometry

/-- 参数积分的 `C^∞`：`ρ` 在开集 `V ×ˢ W`（`closedBall 0 1 ⊆ W`）上 `C^∞` ⇒
`t ↦ ∫_{closedBall 0 1} ρ (t, z)` 在 `V` 上 `C^∞`（smooth cutoff + convolution with param）。 -/
theorem contDiffOn_setIntegral_closedBall_DV {ρ : ℝ × ℂ → ℝ} {V : Set ℝ} {W : Set ℂ}
    (hV : IsOpen V) (hW : IsOpen W) (hBW : Metric.closedBall (0 : ℂ) 1 ⊆ W)
    (hρ : ContDiffOn ℝ ∞ ρ (V ×ˢ W)) :
    ContDiffOn ℝ ∞ (fun t : ℝ => ∫ z in Metric.closedBall (0 : ℂ) 1, ρ (t, z)) V := by
  obtain ⟨δ, hδ, hcth⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hW hBW
  rw [cthickening_closedBall hδ.le zero_le_one (0 : ℂ)] at hcth
  let c : ContDiffBump (0 : ℂ) := ⟨1, δ + 1, one_pos, by linarith⟩
  have hsupp : ∀ x : ℂ, x ∉ Metric.closedBall (0 : ℂ) (δ + 1) → c x = 0 := by
    intro x hx
    by_contra h
    have : x ∈ Function.support c := h
    rw [c.support_eq] at this
    exact hx (Metric.ball_subset_closedBall this)
  let g : ℝ → ℂ → ℝ := fun p x => c x * ρ (p, x)
  have hg : ContDiffOn ℝ ∞ (↿g) (V ×ˢ univ) := by
    have hopen : IsOpen (V ×ˢ (univ : Set ℂ)) := hV.prod isOpen_univ
    intro q hq
    refine (ContDiffAt.contDiffWithinAt ?_)
    by_cases hx : q.2 ∈ Metric.closedBall (0 : ℂ) (δ + 1)
    · have hqW : q ∈ V ×ˢ W := ⟨hq.1, hcth hx⟩
      have h1 : ContDiffAt ℝ ∞ ρ q := hρ.contDiffAt ((hV.prod hW).mem_nhds hqW)
      exact ((c.contDiff.contDiffAt (x := q.2)).comp q contDiffAt_snd).mul h1
    · have hxo : (Metric.closedBall (0 : ℂ) (δ + 1))ᶜ ∈ 𝓝 q.2 :=
        Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx
      have hev : (↿g) =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
        have : (fun p : ℝ × ℂ => p.2) ⁻¹' (Metric.closedBall (0 : ℂ) (δ + 1))ᶜ ∈ 𝓝 q :=
          continuous_snd.continuousAt.preimage_mem_nhds hxo
        filter_upwards [this] with p hp
        simp [Function.HasUncurry.uncurry, g, hsupp p.2 hp]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hconv := contDiffOn_convolution_left_with_param_comp (μ := (volume : Measure ℂ))
    (ContinuousLinearMap.mul ℝ ℝ) (v := fun _ : ℝ => (0 : ℂ)) contDiffOn_const
    (f := (Metric.closedBall (0 : ℂ) 1).indicator (fun _ => (1 : ℝ))) (g := g)
    (k := Metric.closedBall (0 : ℂ) (δ + 1)) hV (isCompact_closedBall _ _)
    (fun p x _ hx => by simp [g, hsupp x hx])
    ((locallyIntegrable_const (1 : ℝ)).indicator measurableSet_closedBall) hg
  refine hconv.congr ?_
  intro p hp
  simp only [convolution_def, ContinuousLinearMap.mul_apply', zero_sub]
  have h1 : ∀ x : ℂ, g p x * (Metric.closedBall (0 : ℂ) 1).indicator (fun _ => (1 : ℝ)) (-x) =
      (Metric.closedBall (0 : ℂ) 1).indicator (g p) x := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : ℂ) 1
    · have hx' : -x ∈ Metric.closedBall (0 : ℂ) 1 := by simpa using hx
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · have hx' : -x ∉ Metric.closedBall (0 : ℂ) 1 := by simpa using hx
      simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
  simp_rw [h1]
  rw [integral_indicator measurableSet_closedBall]
  refine setIntegral_congr_fun measurableSet_closedBall fun x hx => ?_
  simp [g, c.one_of_mem_closedBall (by simpa using (show x ∈ Metric.closedBall (0 : ℂ) 1 from hx))]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

omit [CompactSpace M] in
/-- G3 主定理（不需要 `M` 紧）：在 immersion 假设下，`t ↦ riemannianDiskArea (G t) (Φ t ∘ u)` 在 `t₀` 的某个开邻域
上 `C^∞`。 -/
theorem SmoothDiskExtension.exists_contDiffOn_area_two_parameter_DV
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : IsOpen T) (hT₀ : t₀ ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    (hinj : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    ∃ V : Set ℝ, IsOpen V ∧ t₀ ∈ V ∧
      ContDiffOn ℝ ∞ (fun t => riemannianDiskArea (G t)
        ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u)) V := by
  obtain ⟨heq, s, hs, hDs, hU⟩ := hu
  have hu' : SmoothDiskExtension (E := E) u U := ⟨heq, s, hs, hDs, hU⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hT.mem_nhds hT₀) ht₀)
  have hi : t₀ ∈ Ioo (t₀ - r) (t₀ + r) := ⟨by linarith, by linarith⟩
  let D' := RealTimeInterval.openInterval (t₀ - r) (t₀ + r) t₀ hi
  have hsub : D'.carrier ⊆ T ∩ D.regular := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    change t₀ - r < t ∧ t < t₀ + r at ht
    constructor <;> linarith [ht.1, ht.2]
  let H : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M := fun t => Diffeomorph.pullbackMetric (G t) (Φ t)
  have hH : MetricFamilySmoothOn D' H :=
    metricFamilySmoothOn_parameterPullback hG hT hΦ D' rfl hsub
  have hH₀ : H t₀ = G t₀ := by
    simp only [H, hΦ₀, Diffeomorph.pullbackMetric_refl]
  have hpair (v w : ℂ) :=
    contDiffOn_metricFamilyDiskPairing hH D'.regular_isOpen subset_rfl hs hU v w
  let P : ℂ → ℂ → ℝ × ℂ → ℝ := fun v w q =>
    (H q.1).inner (U q.2) (diskMapPartial U q.2 v) (diskMapPartial U q.2 w)
  let det : ℝ × ℂ → ℝ := fun q => P 1 1 q * P Complex.I Complex.I q - P 1 Complex.I q ^ 2
  have hdet : ContDiffOn ℝ ∞ det (D'.regular ×ˢ s) :=
    ((hpair 1 1).mul (hpair Complex.I Complex.I)).sub ((hpair 1 Complex.I).pow 2)
  have hρ : ∀ q : ℝ × ℂ, riemannianAreaDensity (H q.1) U q.2 = Real.sqrt (det q) := fun q => rfl
  have hdetpos : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 < det (t₀, z) := by
    intro z hz
    have h := riemannianAreaDensity_pos_of_injective_mfderiv (H t₀) (hinj z hz)
    rw [hρ (t₀, z)] at h
    exact Real.sqrt_pos.mp h
  have hopen : IsOpen ((D'.regular ×ˢ s) ∩ det ⁻¹' Ioi 0) :=
    hdet.continuousOn.isOpen_inter_preimage (D'.regular_isOpen.prod hs) isOpen_Ioi
  have hsub2 : ({t₀} : Set ℝ) ×ˢ Metric.closedBall (0 : ℂ) 1 ⊆
      (D'.regular ×ˢ s) ∩ det ⁻¹' Ioi 0 := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have ht' : t = t₀ := ht
    subst ht'
    exact ⟨⟨hi, hDs hz⟩, hdetpos z hz⟩
  obtain ⟨V, W, hV, hW, hV₀, hBW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_closedBall (0 : ℂ) 1) hopen hsub2
  have hρsm : ContDiffOn ℝ ∞ (fun q : ℝ × ℂ => Real.sqrt (det q)) (V ×ˢ W) := by
    refine (hdet.mono (fun q hq => (hVW hq).1)).sqrt (fun q hq => (hVW hq).2.ne')
  have hint := contDiffOn_setIntegral_closedBall_DV hV hW hBW hρsm
  have hV₀' : t₀ ∈ V := hV₀ rfl
  refine ⟨V, hV, hV₀', hint.congr ?_⟩
  intro t _
  rw [← hu'.area_pullback (G t) (Φ t), riemannianDiskArea_eq_of_extension _ u U heq, riemannianArea]
  rfl

/-- G3 的 consumer（固定类型 `M` 上的 IMS09 装配，用到 G1 + G2 + G3）：
`A` 是任意实函数，`Ā s = Area_{G s}(Φ_s ∘ u)` 在 `t₀` 附近（`S` 内）支配 `A`，且 `u` 在 `t₀` 取到
`A t₀`；若一阶导数 `m - f < b`，则 `hasLocalSmoothUpperBarrier A S t₀ b`。 -/
theorem SmoothDiskExtension.hasLocalSmoothUpperBarrier_of_area_two_parameter_DV
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : IsOpen T) (hT₀ : t₀ ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z)
    (hharm : ∀ z ∈ Metric.ball 0 1, diskMapTension (G t₀) U z = 0)
    (hinj : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    {A : ℝ → ℝ} {S : Set ℝ}
    (hdom : ∀ᶠ s in 𝓝 t₀, s ∈ S → A s ≤ riemannianDiskArea (G s)
      ((⟨Φ s, (Φ s).contMDiff.continuous⟩ : C(M, M)).comp u))
    (hmin : A t₀ = riemannianDiskArea (G t₀) u) {b : ℝ}
    (hb : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
      (∫ θ in -Real.pi..Real.pi,
        (G t₀).inner (U (circleMap 0 1 θ))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U (circleMap 0 1 θ))) t₀ 1)
          (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
            Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ))) < b) :
    DifferentialGeometry.Analysis.hasLocalSmoothUpperBarrier A S t₀ b := by
  obtain ⟨V, hV, hV₀, hsm⟩ := hu.exists_contDiffOn_area_two_parameter_DV hG ht₀ hT hT₀ hΦ hΦ₀ hinj
  have hd := (hu.hasDerivAt_area_two_parameter_DV hG ht₀ hT hT₀ hΦ hΦ₀ hconf hharm).2.2
  obtain ⟨O, hOsub, hO, hO₀⟩ := _root_.mem_nhds_iff.mp hdom
  have hcomp : (⟨Φ t₀, (Φ t₀).contMDiff.continuous⟩ : C(M, M)).comp u = u := by
    ext z
    simp [hΦ₀]
  refine DifferentialGeometry.Analysis.hasLocalSmoothUpperBarrier_of_smooth_majorant_DV
    (hV.inter hO) ⟨hV₀, hO₀⟩ (hsm.mono inter_subset_left) ?_ ?_ hd hb
  · rw [hmin, hcomp]
  · intro s hs
    exact hOsub hs.1.2 hs.2

end DifferentialGeometry.Geometry
