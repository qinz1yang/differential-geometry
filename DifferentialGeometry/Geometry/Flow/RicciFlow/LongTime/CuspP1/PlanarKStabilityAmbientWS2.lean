import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ConformalCoefficientIM6
import DifferentialGeometry.Geometry.Curvature.ConformalScalarPlaneWS2
import DifferentialGeometry.Geometry.Curvature.RicciRestriction

/-!
# S-W-STAB-2 G5：逐盘的 ambient 版共形 stability（O-W-IMS06 G16 的 (a)(b)(c) 一步到位）

`U ⊆ X` 开，`G` 是 `U` 上度量，`_HC2` 的 locality `G = g.restrictOpen U`（在 `q z` 的邻域，
`z ∈ closedDisk`），`q` 是 `G` 下的 Morrey disk、`Q` 其光滑延拓、`Q` 在开盘上浸入。则
`λ := diskConformalFactor_IM6 g (ι ∘ q)`（ambient 度量 `g` 下的 `g(∂₁, ∂₁)`）：

* `λ` 在开盘上 `C^∞`、`> 0`；
* `∃ VJ`（`C^∞`），`VJ z ≤ −Δ(log λ)(z)/(2λ(z)) − R_g(diskExtension (ι ∘ q) z)/2`（`z` 在开盘）；
* `∀ Ω ⊆ ball`，`∀ ψ ∈ C_c^∞(Ω)`，`0 ≤ ∫_Ω ‖dψ‖² + λ·VJ·ψ²`。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace MeasureTheory
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.MinimalSurface
open GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X] [T3Space X]

/-- `G = g.restrictOpen U` 在 `y` 的邻域 ⇒ `metricScalarAt G y = metricScalarAt g ↑y`。 -/
theorem metricScalarAt_eq_of_locality_WS2 (g : SmoothRiemannianMetric 𝓘(ℝ, E) X)
    {U : TopologicalSpace.Opens X} (G : SmoothRiemannianMetric 𝓘(ℝ, E) U) {y : U}
    (hloc : ∀ᶠ y' : U in 𝓝 y, G.inner y' = (g.restrictOpen U).inner y') :
    metricScalarAt G y = metricScalarAt g (y : X) := by
  obtain ⟨V, hVsub, hVo, hyV⟩ := mem_nhds_iff.mp hloc
  let V' : TopologicalSpace.Opens U := ⟨V, hVo⟩
  have hres : G.restrictOpen V' = (g.restrictOpen U).restrictOpen V' := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [SmoothRiemannianMetric.restrictOpen_inner, SmoothRiemannianMetric.restrictOpen_inner]
    have h := hVsub x.2
    exact congrArg (fun B => B v w) h
  have h1 := DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen G V'
    ⟨y, hyV⟩
  have h2 := DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen
    (g.restrictOpen U) V' ⟨y, hyV⟩
  have h3 := DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen g U y
  rw [hres] at h1
  exact h1.symm.trans (h2.trans h3)

end GC.LongTime.CuspP1

namespace DifferentialGeometry.Geometry

open GC.LongTime.CuspP1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X] [T3Space X]

/-- **G5 逐盘 ambient 共形 stability.**  `_HC2` 的逐盘版：`G = g.restrictOpen U` locality +
`IsMorreyDisk G γ q` + `Q` 在开盘上浸入 + `Q z ∈ interior W` ⇒ ambient 度量下的平面形式
`VJ ≤ −Δ(log λ)/(2λ) − R_g/2` 与 `0 ≤ ∫_Ω ‖dψ‖² + λ·VJ·ψ²`，`λ = diskConformalFactor_IM6 g (ι ∘ q)`。
定向 `o` 取 ambient `X` 上的，限制到 `U`。 -/
theorem IsMorreyDisk.stability_inequality_conformal_ambient_WS2
    (hdim : Module.finrank ℝ E = 3) (g : SmoothRiemannianMetric 𝓘(ℝ, E) X)
    {U : TopologicalSpace.Opens X} (G : SmoothRiemannianMetric 𝓘(ℝ, E) U) {γ : freeLoop U}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {q : C(closedDisk, U)} (hu : IsMorreyDisk G γ q)
    {Q : ℂ → U} (hQ : SmoothDiskExtension (E := E) q Q) (W : Set U) (hW : Set.range q ⊆ W)
    (o : DifferentialGeometry.ManifoldOrientation 𝓘(ℝ, E) X 3)
    (hinj : ∀ z ∈ Metric.ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hint : ∀ z ∈ Metric.ball (0 : ℂ) 1, Q z ∈ interior W)
    (hloc : ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z), G.inner y = (g.restrictOpen U).inner y) :
    let lam := diskConformalFactor_IM6 g
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q)
    ContDiffOn ℝ ∞ lam (Metric.ball (0 : ℂ) 1) ∧ (∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < lam z) ∧
    ∃ VJ : ℂ → ℝ, ContDiffOn ℝ ∞ VJ (Metric.ball (0 : ℂ) 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, VJ z ≤ -Laplacian.laplacian (fun p => Real.log (lam p)) z /
          (2 * lam z) - metricScalarAt g (diskExtension
            ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z) / 2) ∧
      ∀ Ω : Set ℂ, Ω ⊆ Metric.ball (0 : ℂ) 1 → ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ →
        HasCompactSupport ψ → tsupport ψ ⊆ Ω →
        0 ≤ ∫ x in Ω, (‖fderiv ℝ ψ x‖ ^ 2 + lam x * VJ x * ψ x ^ 2) := by
  intro lam
  let D : TopologicalSpace.Opens ℂ := ⟨Metric.ball (0 : ℂ) 1, Metric.isOpen_ball⟩
  have hQs := hQ.contMDiff_unitBall_WS
  have hQi := injective_mfderiv_unitBall_WS hinj
  have hconf : ∀ z ∈ D, DiskMapConformalAt G Q z :=
    fun z hz => hu.conformal_of_extension hQ z hz
  obtain ⟨hlamC, hlamP⟩ := conformalFactor_data_WS2 G D hQs hQi hconf
  obtain ⟨VJ, hC, hb, hs⟩ := hu.stability_inequality_conformal_planar_WS2 hdim hγ hQ W hW
    (o.restrictOpen U) D subset_rfl hQs hQi hint
  have hcoef : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapConformalCoefficient G Q z = lam z :=
    fun z hz => coefficient_eq_diskConformalFactor_IM6 g G hQ hloc hz
  refine ⟨hlamC.congr (fun z hz => (hcoef z hz).symm),
    fun z hz => (hcoef z hz) ▸ hlamP z hz, VJ, hC, fun z hz => ?_, ?_⟩
  · have h1 := hb z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz
    have hev : diskExtension ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) =ᶠ[𝓝 z]
        (Subtype.val ∘ Q) :=
      diskExtension_eventuallyEq_of_extension_IM6 (fun w => congrArg Subtype.val (hQ.1 w)) hz
    have hpt : diskExtension ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z =
        ((Q z : U) : X) := hev.eq_of_nhds
    have hQz : Q z = q ⟨z, hz'⟩ := hQ.1 ⟨z, hz'⟩
    have hscal : metricScalarAt G (Q z) = metricScalarAt g ((Q z : U) : X) := by
      apply metricScalarAt_eq_of_locality_WS2 g G
      have h := hloc ⟨z, hz'⟩
      rwa [← hQz] at h
    have hlog : (fun p => Real.log (diskMapConformalCoefficient G Q p)) =ᶠ[𝓝 z]
        (fun p => Real.log (lam p)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with p hp
      rw [hcoef p hp]
    rw [(InnerProductSpace.laplacian_congr_nhds hlog).eq_of_nhds, hcoef z hz,
      ← metricScalar_eq_scal G, hscal] at h1
    rwa [hpt]
  · intro Ω hΩ ψ hψ hψc hψΩ
    refine hstab_of_coefficient_IM6 g G hQ hloc VJ ?_ Ω hΩ ψ hψ hψc hψΩ
    intro Ω' hΩ' ψ' hψ' hψc' hψΩ'
    have h := (hs ψ' hψ' hψc' (hψΩ'.trans hΩ')).2
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω')] at h
    · exact h
    · intro x hx
      have hx' : x ∉ tsupport ψ' := fun hh => hx (hψΩ' hh)
      obtain ⟨h1, h2⟩ := fderiv_eq_zero_of_notMem_tsupport_WS2 hx'
      simp [h1, h2]

/-- 单积分 `∫_Ω ‖dψ‖² + w ψ²` ⇒ 分量形 `∫_Ω ((∂₁ψ)² + (∂_Iψ)²) + ∫_Ω w ψ²`
（`Ω ⊆ N`，`w` 在 `N` 上连续）。 -/
theorem planar_components_of_single_WS2 {N : TopologicalSpace.Opens ℂ} {Ω : Set ℂ}
    (hΩ : Ω ⊆ (N : Set ℂ)) {w : ℂ → ℝ} (hw : ContinuousOn w (N : Set ℂ)) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω)
    (h : 0 ≤ ∫ x in Ω, (‖fderiv ℝ ψ x‖ ^ 2 + w x * ψ x ^ 2)) :
    0 ≤ (∫ x in Ω, ((fderiv ℝ ψ x 1) ^ 2 + (fderiv ℝ ψ x Complex.I) ^ 2)) +
      ∫ x in Ω, w x * ψ x ^ 2 := by
  have hI1 := (integrable_gradSq_WS2 hψ hc).integrableOn (s := Ω)
  have hI2 := (integrable_weight_sq_WS2 hψ hc (hs.trans hΩ) hw).integrableOn (s := Ω)
  have e : (∫ x in Ω, ((fderiv ℝ ψ x 1) ^ 2 + (fderiv ℝ ψ x Complex.I) ^ 2)) =
      ∫ x in Ω, ‖fderiv ℝ ψ x‖ ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun x => (norm_sq_complex_clm_WS2 _).symm)
  rw [e, ← integral_add hI1 hI2]
  exact h

/-- **G5 consumer：EIG / O-W-IMS06 的分量形 `hstab`.**  `IsMorreyDisk.stability_inequality_
conformal_ambient_WS2` 的单积分结论拆成 `∫_Ω ((∂₁ψ)² + (∂_Iψ)²) + ∫_Ω λ·VJ·ψ² ≥ 0`
（任意 `Ω ⊆ ball`，不要求开）。 -/
theorem IsMorreyDisk.stability_components_ambient_WS2
    (hdim : Module.finrank ℝ E = 3) (g : SmoothRiemannianMetric 𝓘(ℝ, E) X)
    {U : TopologicalSpace.Opens X} (G : SmoothRiemannianMetric 𝓘(ℝ, E) U) {γ : freeLoop U}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {q : C(closedDisk, U)} (hu : IsMorreyDisk G γ q)
    {Q : ℂ → U} (hQ : SmoothDiskExtension (E := E) q Q) (W : Set U) (hW : Set.range q ⊆ W)
    (o : DifferentialGeometry.ManifoldOrientation 𝓘(ℝ, E) X 3)
    (hinj : ∀ z ∈ Metric.ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hint : ∀ z ∈ Metric.ball (0 : ℂ) 1, Q z ∈ interior W)
    (hloc : ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z), G.inner y = (g.restrictOpen U).inner y) :
    let lam := diskConformalFactor_IM6 g
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q)
    ∃ VJ : ℂ → ℝ, ContDiffOn ℝ ∞ VJ (Metric.ball (0 : ℂ) 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, VJ z ≤ -Laplacian.laplacian (fun p => Real.log (lam p)) z /
          (2 * lam z) - metricScalarAt g (diskExtension
            ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z) / 2) ∧
      ∀ Ω : Set ℂ, Ω ⊆ Metric.ball (0 : ℂ) 1 → ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ →
        HasCompactSupport ψ → tsupport ψ ⊆ Ω →
        0 ≤ (∫ x in Ω, ((fderiv ℝ ψ x 1) ^ 2 + (fderiv ℝ ψ x Complex.I) ^ 2)) +
          ∫ x in Ω, lam x * VJ x * ψ x ^ 2 := by
  intro lam
  obtain ⟨hlamC, -, VJ, hC, hb, hs⟩ :=
    hu.stability_inequality_conformal_ambient_WS2 hdim g G hγ hQ W hW o hinj hint hloc
  refine ⟨VJ, hC, hb, fun Ω hΩ ψ hψ hc hts => ?_⟩
  exact planar_components_of_single_WS2 (N := ⟨Metric.ball (0 : ℂ) 1, Metric.isOpen_ball⟩) hΩ
    ((hlamC.mul hC).continuousOn) hψ hc hts (hs Ω hΩ ψ hψ hc hts)

end DifferentialGeometry.Geometry

end
