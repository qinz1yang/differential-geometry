import DifferentialGeometry.Geometry.Curvature.MorreyOpenTarget_GB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterImportedDefs

set_option autoImplicit false

/-!
# `_HC` 实例：confined Morrey 盘的 IMS09 积分不等式（车道 S-A10-GAUSS，G4，后缀 `_GB`）

`PrescribedCuspMeridianTop_CPQ.exists_eventual_confined_morrey_disk_HC` 的结论体里，下面这些
条款被**逐字**当作显式参数（`a ha ρ hρ`、`U/δ/G/ι` 的 `let`、`γU q`、`IsSmoothEmbeddedLoop γU`、
`IsMorreyDisk G γU q`、local metric clause）：range / interior / ρ-sign / boundary /
`DiskWeakJordanTrace` 条款对积分不等式不需要，所以不出现（`obtain` 出来的多余条款不必丢给本定理）。

本文件只 import 无未证项的 `P2AdapterImportedDefs`（`cutoff_P2A`、`canonicalPositiveDomainMetric_P2A`、
`barrier_P2A`），**不** import `P2AdapterImportedMorreyHC`（经未证 mirrors）；`_HC` 的类型对齐
`example` 在单独的、不登记的 consumer 文件里。

结论：`v`（`= q` 或 `q ∘ reflection`，面积相同）、光滑延拓 `Q`、光滑单调 `φ`（精确迹
`Q ∘ circleMap = γU ∘ φ`，即消掉 `htrace`；`hnon` 由 `γU` smooth embedded 自动）与
`∫_D diskMapMetricVariationDensity ≤ 3·Area/(4(t+c)) − 2π + ∫ k_g dℓ`（ambient 度量族 `Gfam`，
`Gfam t = postMetric F.observation t`，`c = H.scalarShift`）。
-/

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace MeasureTheory
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime GC.LongTime.CuspP1
open scoped Manifold ContDiff Topology

namespace GC.LongTime

universe u

theorem AnalyticSurgeryProfile.integral_bound_of_confined_morrey_HC_GB
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ' : ℝ → ℝ}
    (H : AnalyticSurgeryProfile F δ') {t : ℝ} (ht0 : 0 ≤ t)
    (Gfam : ℝ → SmoothRiemannianMetric ThreeModel (postStage F.observation t).Carrier)
    (hGt : Gfam t = postMetric F.observation t)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      IsMorreyDisk G γU q →
      (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
        G.inner y = ((postMetric F.observation t).restrictOpen U).inner y ∧
          barrier_P2A a (ρ (y : (postStage F.observation t).Carrier)) =
            ρ (y : (postStage F.observation t).Carrier)) →
      (∀ w : closedDisk, ∀ X Y : EuclideanSpace ℝ (Fin 3),
        HasDerivAt
          (fun r : ℝ => (Gfam r).inner ((q w : U) : (postStage F.observation t).Carrier) X Y)
          (-2 * ricciTensor (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (Gfam t)
            ((q w : U) : (postStage F.observation t).Carrier) X Y) t) →
      ∃ (v : C(closedDisk, U)) (Q : ℂ → U) (φ : ℝ → ℝ),
        (v = q ∨ v = q.comp ⟨diskReflection, diskReflection.continuous⟩) ∧
        riemannianDiskArea G v = riemannianDiskArea G q ∧
        SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) v Q ∧ ContDiff ℝ ∞ φ ∧ Monotone φ ∧
        (Subtype.val ∘ Q) ∘ circleMap 0 1 =
          (fun s : ℝ => ((γU (s : loopCircle) : U) : (postStage F.observation t).Carrier)) ∘ φ ∧
        riemannianDiskArea (postMetric F.observation t)
            (fun w => ((v w : U) : (postStage F.observation t).Carrier)) =
          riemannianDiskArea G q ∧
        (∫ z in Metric.closedBall (0 : ℂ) 1,
            diskMapMetricVariationDensity Gfam t (Subtype.val ∘ Q) z) ≤
          3 * riemannianDiskArea G q / (4 * (t + H.scalarShift)) - 2 * Real.pi +
            ∫ θ in -Real.pi..Real.pi,
              diskMapTraceBoundaryDensity (postMetric F.observation t) (Subtype.val ∘ Q)
                (fun s : ℝ => ((γU (s : loopCircle) : U) : (postStage F.observation t).Carrier))
                φ θ := by
  intro U δ hδ hU G γU q hsm hMor hloc hderiv
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hloc' : ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
      G.inner y = ((Gfam t).restrictOpen U).inner y := by
    intro z
    rw [hGt]
    exact (hloc z).mono fun y hy => hy.1
  have hR : ∀ w : closedDisk, -3 / (2 * (t + H.scalarShift)) ≤
      metricScalarAt (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (Gfam t)
        ((q w : U) : (postStage F.observation t).Carrier) := by
    intro w
    rw [hGt]
    exact H.scalar_lower t ht0 _
  obtain ⟨v, Q, φ, hv, harea, hext, hφ, hm, htr, hA, hbound⟩ :=
    IsMorreyDisk.exists_ambient_integral_bound_GB (E := EuclideanSpace ℝ (Fin 3)) hdim U G Gfam
      (c := H.scalarShift) hsm hMor hloc' hderiv hR
  refine ⟨v, Q, φ, hv, harea, hext, hφ, hm, htr, ?_, hbound.trans_eq ?_⟩
  · rw [← hGt]
    exact hA
  · rw [hGt]

end GC.LongTime
