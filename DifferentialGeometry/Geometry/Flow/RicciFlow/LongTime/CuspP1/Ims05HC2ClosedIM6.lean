import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ConformalCoefficientIM6
import DifferentialGeometry.Geometry.Curvature.ConformalScalarPlaneWS2
import DifferentialGeometry.Geometry.Curvature.Closure
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.MinimalSurface.Variation.ParamStabilityMorreyWS

/-!
# c3 闭合：逐盘 IMS05′，`_HC2` 形 Morrey 盘无显式义务（O-W-IMS06 G16，后缀 `_IM6`）

S-W-STAB-2 逐盘版 `IsMorreyDisk.stability_inequality_conformal_planar_WS2`（`U` 上度量 `G`、
`λ_G = diskMapConformalCoefficient G Q`、`scalarCurv G (Q z)`、全平面积分）经 ambient 换写喂 G9
`ims05_radius_bound_HC2_of_normStability_IM6`：
* `λ_G = diskConformalFactor_IM6 g (ι∘q)` 在开盘上（G15），`Δ log λ` 经 `laplacian_congr_nhds`；
* `scalarCurv G (Q z) = metricScalarAt G (Q z)`（`metricScalar_eq_scal`）
  `= metricScalarAt (g.restrictOpen U) (Q z)`（`_HC2` locality + `metricScalarAt_eq_of_eqOn_closure`）
  `= metricScalarAt g (ι (Q z))`（`metricScalarAt_restrictOpen`）；
* `∫ x` ↔ `∫ x in Ω`（`tsupport ψ ⊆ Ω` 外被积函数为 0）。
主定理 `ims05_radius_bound_HC2_closed_IM6`：在 postStage 上，`_HC2` 判据的条款（光滑嵌入边界环、
`IsMorreyDisk G γU q`、locality、`⊆ W`、内部 `⊆ interior W`、内部浸入）⇒ 对一切 `σ > 0`，`ι∘q` 的
S-W-NECK G4 形 `hIMS05`。**无显式义务。**
-/

set_option autoImplicit false
noncomputable section

open Set Filter Manifold MeasureTheory TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.CuspP1

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- `_HC2` locality ⇒ `U` 上 `G` 与 `g.restrictOpen U` 的标量曲率在 `q` 的像上相等。 -/
theorem metricScalarAt_eq_of_locality_IM6 (t : ℝ)
    {U : Opens (postStage F.observation t).Carrier} (G : SmoothRiemannianMetric (𝓡 3) U)
    {y : U} (hloc : ∀ᶠ y' : U in 𝓝 y,
      G.inner y' = ((postMetric F.observation t).restrictOpen U).inner y') :
    metricScalarAt G y = metricScalarAt ((postMetric F.observation t).restrictOpen U) y := by
  set S : Set U := {y' | G.inner y' = ((postMetric F.observation t).restrictOpen U).inner y'}
    with hS
  let V : Opens U := ⟨interior S, isOpen_interior⟩
  have hyV : y ∈ (V : Set U) := mem_interior_iff_mem_nhds.mpr hloc
  have : SecondCountableTopology (postStage F.observation t).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) _
  have : LocallyCompactSpace (postStage F.observation t).Carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) _
  have : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  have : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  refine metricScalarAt_eq_of_eqOn_closure G _ V (fun y' hy' v w => ?_) y (subset_closure hyV)
  have h : y' ∈ S := interior_subset hy'
  exact congrArg (fun A => A v w) h

/-- **c3 闭合（G16 主定理）**：`_HC2` 形 Morrey 盘 ⇒ 对一切 `σ > 0`，`ι∘q` 的 NECK G4 形 `hIMS05`。 -/
theorem ims05_radius_bound_HC2_closed_IM6 (t : ℝ)
    (U : Opens (postStage F.observation t).Carrier) (G : SmoothRiemannianMetric (𝓡 3) U)
    (γU : freeLoop U) (q : C(closedDisk, U)) (W : Set (postStage F.observation t).Carrier)
    (hsm : IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU)
    (hMor : IsMorreyDisk G γU q)
    (hloc : ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
      G.inner y = ((postMetric F.observation t).restrictOpen U).inner y)
    (hW : range ((⟨Subtype.val, continuous_subtype_val⟩ :
      C(U, (postStage F.observation t).Carrier)).comp q) ⊆ W)
    (hint : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
      ((⟨Subtype.val, continuous_subtype_val⟩ :
        C(U, (postStage F.observation t).Carrier)).comp q) z ∈ interior W)
    (himm : ∀ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q →
      ∀ z ∈ Metric.ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z))
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ diskEDist_NK (postMetric F.observation t)
        ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(U, (postStage F.observation t).Carrier)).comp q) z₀ z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK (postMetric F.observation t)
        ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(U, (postStage F.observation t).Carrier)).comp q) z₀ z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK (postMetric F.observation t)
        ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(U, (postStage F.observation t).Carrier)).comp q) z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt (postMetric F.observation t) (diskExtension
          ((⟨Subtype.val, continuous_subtype_val⟩ :
            C(U, (postStage F.observation t).Carrier)).comp q) w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)) := by
  have hd3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  obtain ⟨Q, hQ⟩ := hMor.exists_smooth_extension G hd3 hsm
  have hQs := hQ.contMDiff_unitBall_WS
  have hQi := injective_mfderiv_unitBall_WS (himm Q hQ)
  set ι : C(U, (postStage F.observation t).Carrier) := ⟨Subtype.val, continuous_subtype_val⟩
    with hιdef
  have hW' : Set.range q ⊆ Subtype.val ⁻¹' W := by
    rintro _ ⟨z, rfl⟩
    exact hW ⟨z, rfl⟩
  have hint' : ∀ p ∈ Metric.ball (0 : ℂ) 1, Q p ∈ interior (Subtype.val ⁻¹' W) := by
    intro p hp
    have hpc : p ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hp
    have hn := hint ⟨p, hpc⟩ (by simpa only [Metric.mem_ball, dist_zero_right] using hp)
    have hQp : Q p = q ⟨p, hpc⟩ := hQ.1 ⟨p, hpc⟩
    rw [mem_interior]
    refine ⟨Subtype.val ⁻¹' interior W, preimage_mono interior_subset,
      isOpen_interior.preimage continuous_subtype_val, ?_⟩
    rw [hQp]
    exact hn
  let o3 : DifferentialGeometry.ManifoldOrientation (𝓡 3) U 3 :=
    { dimension_eq := by simp
      orientation := ((postStage F.observation t).orientation.restrictOpen U).orientation
      locally_constant :=
        ((postStage F.observation t).orientation.restrictOpen U).locally_constant }
  obtain ⟨VJ, hC, hb, hs⟩ := hMor.stability_inequality_conformal_planar_WS2 hd3 hsm hQ _ hW' o3
    ⟨Metric.ball (0 : ℂ) 1, Metric.isOpen_ball⟩ subset_rfl hQs hQi hint'
  have hlamEq : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapConformalCoefficient G Q z =
      diskConformalFactor_IM6 (postMetric F.observation t) (ι.comp q) z :=
    fun z hz => coefficient_eq_diskConformalFactor_IM6 _ G hQ hloc hz
  have hVJle : ∀ z ∈ Metric.ball (0 : ℂ) 1, VJ z ≤
      -Laplacian.laplacian (fun p => Real.log (diskConformalFactor_IM6
        (postMetric F.observation t) (ι.comp q) p)) z /
        (2 * diskConformalFactor_IM6 (postMetric F.observation t) (ι.comp q) z) -
        metricScalarAt (postMetric F.observation t) (diskExtension (ι.comp q) z) / 2 := by
    intro z hz
    have h1 := hb z hz
    have hev : (fun p => Real.log (diskMapConformalCoefficient G Q p)) =ᶠ[𝓝 z]
        (fun p => Real.log (diskConformalFactor_IM6 (postMetric F.observation t)
          (ι.comp q) p)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with p hp
      rw [hlamEq p hp]
    have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz
    have hQz : Q z = q ⟨z, hz'⟩ := hQ.1 ⟨z, hz'⟩
    have hR : scalarCurv G (Q z) =
        metricScalarAt (postMetric F.observation t) (diskExtension (ι.comp q) z) := by
      rw [← metricScalar_eq_scal, metricScalarAt_eq_of_locality_IM6 t G
        (by rw [hQz]; exact hloc ⟨z, hz'⟩),
        DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen]
      congr 1
      have hd := diskExtension_coe (ι.comp q) ⟨z, hz'⟩
      change diskExtension (ι.comp q) z = (q ⟨z, hz'⟩ : (postStage F.observation t).Carrier)
        at hd
      rw [hd, hQz]
    rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds, hlamEq z hz, hR] at h1
    exact h1
  have hstabG : ∀ Ω : Set ℂ, Ω ⊆ Metric.ball (0 : ℂ) 1 →
      ∀ ψ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
        0 ≤ ∫ x in Ω,
          (‖fderiv ℝ ψ x‖ ^ 2 + diskMapConformalCoefficient G Q x * VJ x * ψ x ^ 2) := by
    intro Ω hΩ ψ hψ hψc hψΩ
    have h := (hs ψ hψ hψc (hψΩ.trans hΩ)).2
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)] at h
    · exact h
    · intro x hx
      have hx' : x ∉ tsupport ψ := fun hh => hx (hψΩ hh)
      obtain ⟨h1, h2⟩ := fderiv_eq_zero_of_notMem_tsupport_WS2 hx'
      simp [h1, h2]
  exact ims05_radius_bound_HC2_of_normStability_IM6 (postMetric F.observation t) G hMor hloc hQ
    (himm Q hQ) VJ hC hVJle (hstab_of_coefficient_IM6 _ G hQ hloc VJ hstabG) hσ

variable {K : ℕ} {cores : PersistentHyperbolicCores F K}

/-- **O-W-ASSEMBLY-2 `h6` 的晚期形（逐字）**：Top meridian、晚期 `s`（实际对一切 `s ≥ start`）、
HT-L 判据的全部条款（含 `DiskWeakJordanTrace`；c3 本身不用它）⇒ 对一切 `σ > 0` 的 `hIMS05`。 -/
theorem h6_of_HC2_closed_IM6 (M : PrescribedCuspMeridianTop_CPQ cores) :
    ∃ T₁ : ℝ, ∀ (s : ℝ) (hs : M.exterior.start ≤ s), T₁ ≤ s →
    ∀ (U : TopologicalSpace.Opens (postStage F.observation s).Carrier)
      (G : SmoothRiemannianMetric (𝓡 3) U) (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      IsMorreyDisk G γU q →
      (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
        G.inner y = ((postMetric F.observation s).restrictOpen U).inner y) →
      DiskWeakJordanTrace (M.transported s hs)
        ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(U, (postStage F.observation s).Carrier)).comp q) →
      range ((⟨Subtype.val, continuous_subtype_val⟩ :
        C(U, (postStage F.observation s).Carrier)).comp q) ⊆ M.exterior.region s →
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
        ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(U, (postStage F.observation s).Carrier)).comp q) z ∈
          interior (M.exterior.region s)) →
      (∀ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q →
        ∀ z ∈ Metric.ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z)) →
      ∀ σ : ℝ, 0 < σ → ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
        IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ diskEDist_NK (postMetric F.observation s)
          ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(U, (postStage F.observation s).Carrier)).comp q) z₀ z ≤ ENNReal.ofReal r} →
        (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK (postMetric F.observation s)
          ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(U, (postStage F.observation s).Carrier)).comp q) z₀ z = ENNReal.ofReal r) →
        (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK (postMetric F.observation s)
          ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(U, (postStage F.observation s).Carrier)).comp q) z₀ z ≤ ENNReal.ofReal r →
          ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt (postMetric F.observation s) (diskExtension
            ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(U, (postStage F.observation s).Carrier)).comp q) w)) →
        r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)) :=
  ⟨M.exterior.start, fun s _ _ U G γU q hsm hMor hloc _ hW hint himm _ hσ =>
    ims05_radius_bound_HC2_closed_IM6 s U G γU q (M.exterior.region s) hsm hMor hloc hW hint
      himm hσ⟩

end GC.LongTime.CuspP1
