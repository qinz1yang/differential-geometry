import DifferentialGeometry.Geometry.Curvature.IntegralNegTraceRicci_GB
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricLocality_GB
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PositiveTrace
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalDiskNonconstant
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.AngleTrace
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.BoundaryRegularity

set_option autoImplicit false

/-!
# IMS09：open target 里的 Morrey 盘 ⇒ ambient 积分不等式（车道 S-A10-GAUSS，G4，后缀 `_GB`）

`_HC` 给出的 Morrey 盘 `q : C(closedDisk, Ω)`（`Ω = {ρ < a}` open，`G` = canonical positive-domain
metric，`IsMorreyDisk G γU q`，local metric clause：`G.inner = ((Gfam t).restrictOpen Ω).inner` 在 `q z`
的邻域上）。本文件在**通用** open target `Ω ⊆ N`（`N` compact）上证明：

* `htrace`：`IsMorreyDisk.exists_smooth_extension` ⇒ `IsMorreyDisk.exists_conformal_minimizing_disk`
  （`v = q` 或 `v = q ∘ reflection`，面积不变）⇒ `exists_angle_parameter` 得到光滑单调 `φ` 与
  `Q ∘ circleMap 0 1 = γU ∘ φ`；
* `hnon`：`IsConformalMinimizingDisk.nonconstant`（γU smooth embedded ⇒ 非常值）；
* 共形 / 调和：经 local metric clause（G4 的 `DiskMetricLocality_GB`）与 `restrictOpen` 搬到 ambient；
* 然后套 G3 `integral_metricVariationDensity_le_scalarShift_GB`。

不加新假设：`hderiv`（`∂_t g = −2 Ric` 在盘像点）与 `hR`（scalar lower bound）逐点陈述在 `q` 的像上。
-/

noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory Filter
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
  [CompactSpace N] [T2Space N]

theorem IsMorreyDisk.exists_ambient_integral_bound_GB
    (hdim : Module.finrank ℝ E = 3) (Ω : TopologicalSpace.Opens N)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) Ω) (Gfam : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {t c : ℝ} {γU : freeLoop Ω} {q : C(closedDisk, Ω)}
    (hsm : IsSmoothEmbeddedLoop (E := E) γU) (hMor : IsMorreyDisk G γU q)
    (hloc : ∀ z : closedDisk, ∀ᶠ y : Ω in 𝓝 (q z),
      G.inner y = ((Gfam t).restrictOpen Ω).inner y)
    (hderiv : ∀ w : closedDisk, ∀ X Y : E,
      HasDerivAt (fun r : ℝ => (Gfam r).inner ((q w : Ω) : N) X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, E)) (Gfam t) ((q w : Ω) : N) X Y) t)
    (hR : ∀ w : closedDisk,
      -3 / (2 * (t + c)) ≤ metricScalarAt (I := 𝓘(ℝ, E)) (Gfam t) ((q w : Ω) : N)) :
    ∃ (v : C(closedDisk, Ω)) (Q : ℂ → Ω) (φ : ℝ → ℝ),
      (v = q ∨ v = q.comp ⟨diskReflection, diskReflection.continuous⟩) ∧
      riemannianDiskArea G v = riemannianDiskArea G q ∧
      SmoothDiskExtension (E := E) v Q ∧ ContDiff ℝ ∞ φ ∧ Monotone φ ∧
      (Subtype.val ∘ Q) ∘ circleMap 0 1 =
        (fun s : ℝ => ((γU (s : loopCircle) : Ω) : N)) ∘ φ ∧
      riemannianDiskArea (Gfam t) (fun w => ((v w : Ω) : N)) = riemannianDiskArea G q ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskMapMetricVariationDensity Gfam t (Subtype.val ∘ Q) z) ≤
        3 * riemannianDiskArea G q / (4 * (t + c)) - 2 * Real.pi +
          ∫ θ in -Real.pi..Real.pi, diskMapTraceBoundaryDensity (Gfam t) (Subtype.val ∘ Q)
            (fun s : ℝ => ((γU (s : loopCircle) : Ω) : N)) φ θ := by
  obtain ⟨Q₀, hQ₀⟩ := hMor.exists_smooth_extension G hdim hsm
  obtain ⟨v, σ, Q, hv, harea, hCMD⟩ := hMor.exists_conformal_minimizing_disk G hdim hsm ⟨Q₀, hQ₀⟩
  obtain ⟨φ, hφ, hm, -, hl⟩ := hCMD.positiveTrace.exists_angle_parameter
  have htr := hCMD.extension.angle_trace hCMD.trace hl
  obtain ⟨hQv, N₀, hN₀, hDN₀, hQsm⟩ := hCMD.extension
  have hext : SmoothDiskExtension (E := E) v Q := ⟨hQv, N₀, hN₀, hDN₀, hQsm⟩
  -- 像集与 local metric clause 对 `v`
  have hvq : ∀ w : closedDisk, ∃ w' : closedDisk, v w = q w' := by
    rcases hv with rfl | rfl
    · exact fun w => ⟨w, rfl⟩
    · exact fun w => ⟨diskReflection w, rfl⟩
  have hlocv : ∀ w : closedDisk, ∀ᶠ y : Ω in 𝓝 (v w),
      G.inner y = ((Gfam t).restrictOpen Ω).inner y := by
    intro w
    obtain ⟨w', hw'⟩ := hvq w
    rw [hw']
    exact hloc w'
  have hpt : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ a b : TangentSpace 𝓘(ℝ, E) (Q z),
      G.inner (Q z) a b = ((Gfam t).restrictOpen Ω).inner (Q z) a b := by
    intro z hz a b
    have hQz : Q z = v ⟨z, hz⟩ := hQv ⟨z, hz⟩
    have h : G.inner (Q z) = ((Gfam t).restrictOpen Ω).inner (Q z) := by
      rw [hQz]
      exact (hlocv ⟨z, hz⟩).self_of_nhds
    exact congrArg (fun A => A a b) h
  have hev : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ᶠ y : Ω in 𝓝 (Q z),
      ∀ a b : TangentSpace 𝓘(ℝ, E) y,
        G.inner y a b = ((Gfam t).restrictOpen Ω).inner y a b := by
    intro z hz
    have hQz : Q z = v ⟨z, hz⟩ := hQv ⟨z, hz⟩
    rw [hQz]
    filter_upwards [hlocv ⟨z, hz⟩] with y hy a b
    exact congrArg (fun A => A a b) hy
  let ι : C(Ω, N) := ⟨Subtype.val, continuous_subtype_val⟩
  have hextA : SmoothDiskExtension (E := E) (ι.comp v) (Subtype.val ∘ Q) :=
    hext.comp ι contMDiff_subtype_val
  have hconfA : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      DiskMapConformalAt (Gfam t) (Subtype.val ∘ Q) z := by
    intro z hz
    refine (diskMapConformalAt_restrictOpen (Gfam t) Ω Q z).mp ?_
    exact (diskMapConformalAt_congr_of_metric_GB G _ (hpt z hz)).mp (hCMD.conformal z hz)
  have hharmA : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      diskMapTension (Gfam t) (Subtype.val ∘ Q) z = 0 := by
    intro z hz'
    have hz := Metric.ball_subset_closedBall hz'
    have hcont : ContinuousAt Q z := hQsm.continuousOn.continuousAt (hN₀.mem_nhds (hDN₀ hz))
    rw [← diskMapTension_restrictOpen (Gfam t) Ω Q z hcont,
      ← diskMapTension_congr_of_metric_eventuallyEq_GB (U := Q) (z := z) G _ (hev z hz)]
    exact hCMD.harmonic z hz
  have hnonA : ¬ ∃ c : N, ∀ z : closedDisk, (ι.comp v) z = c := by
    rintro ⟨c, hc⟩
    exact hCMD.nonconstant hsm ⟨v (diskBoundary 0), fun z => Subtype.ext ((hc z).trans (hc _).symm)⟩
  have hγA : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => ((γU (s : loopCircle) : Ω) : N)) :=
    contMDiff_subtype_val.comp hsm.smooth
  have hiA : ∀ s : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => ((γU (s : loopCircle) : Ω) : N)) s (1 : ℝ) ≠ 0 := by
    intro s
    have h := DifferentialGeometry.Topology.mfderiv_subtypeVal_comp (I := 𝓘(ℝ, ℝ))
      (J := 𝓘(ℝ, E)) Ω (fun s : ℝ => γU (s : loopCircle)) s
    exact fun h0 => hsm.immersed s (by
      have h1 := congrArg (fun L => L (1 : ℝ)) h
      exact h1.symm.trans h0)
  have htrA : (Subtype.val ∘ Q) ∘ circleMap 0 1 =
      (fun s : ℝ => ((γU (s : loopCircle) : Ω) : N)) ∘ φ := by
    funext θ
    exact congrArg Subtype.val (congrFun htr θ)
  have hpts : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∃ w' : closedDisk,
      (Subtype.val ∘ Q) z = ((q w' : Ω) : N) := by
    intro z hz
    obtain ⟨w', hw'⟩ := hvq ⟨z, hz⟩
    have hQz : Q z = v ⟨z, hz⟩ := hQv ⟨z, hz⟩
    exact ⟨w', by simp only [Function.comp_apply]; rw [hQz, hw']⟩
  have hderivA : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ X Y : E,
      HasDerivAt (fun r : ℝ => (Gfam r).inner ((Subtype.val ∘ Q) z) X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, E)) (Gfam t) ((Subtype.val ∘ Q) z) X Y) t := by
    intro z hz X Y
    obtain ⟨w', hw'⟩ := hpts z hz
    rw [hw']
    exact hderiv w' X Y
  have hRA : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      -3 / (2 * (t + c)) ≤ metricScalarAt (I := 𝓘(ℝ, E)) (Gfam t) ((Subtype.val ∘ Q) z) := by
    intro z hz
    obtain ⟨w', hw'⟩ := hpts z hz
    rw [hw']
    exact hR w'
  have hptv : ∀ w : closedDisk, ∀ a b : TangentSpace 𝓘(ℝ, E) (v w),
      G.inner (v w) a b = ((Gfam t).restrictOpen Ω).inner (v w) a b := by
    intro w a b
    exact congrArg (fun A => A a b) (hlocv w).self_of_nhds
  have hareaG : riemannianDiskArea ((Gfam t).restrictOpen Ω) v = riemannianDiskArea G v := by
    unfold riemannianDiskArea riemannianArea
    refine setIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)
    have hz' : diskExtension v z = v ⟨z, hz⟩ := diskExtension_coe v ⟨z, hz⟩
    exact riemannianAreaDensity_congr_of_metric_GB (U := diskExtension v) (z := z) _ _
      (fun a b => by rw [hz']; exact (hptv ⟨z, hz⟩ a b).symm)
  have hareaA : riemannianDiskArea (Gfam t) (fun w => ((v w : Ω) : N)) =
      riemannianDiskArea G q := by
    have h := riemannianDiskArea_restrictOpen (Gfam t) Ω v
    exact h.symm.trans (hareaG.trans harea)
  have key := DifferentialGeometry.Geometry.integral_metricVariationDensity_le_scalarShift_GB
    Gfam hdim hextA hderivA hconfA hharmA hnonA hγA hiA hφ hm htrA hRA
  refine ⟨v, Q, φ, hv, harea, hext, hφ, hm, htrA, hareaA, ?_⟩
  have hk : riemannianDiskArea (Gfam t) ⇑(ι.comp v) = riemannianDiskArea G q := hareaA
  rw [hk] at key
  exact key

end DifferentialGeometry.Geometry
