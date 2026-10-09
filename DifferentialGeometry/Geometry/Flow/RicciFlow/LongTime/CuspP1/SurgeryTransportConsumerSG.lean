import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryTransportSG
import DifferentialGeometry.Geometry.MinimalSurface.WeakDiskTransportK8

/-!
# G2 的 consumer：手术时刻 transport 对齐 `smoothCompetitor_transport_K8`（S-A14-SURGERY）

`exists_tpw_nonmetric_SG` 给出 Route W 的 TPW packet 的非度量字段（`K₀` 开、`ContMDiffOn`、
`MapsTo (K₀ ∩ region s) (region t)`、`φ ∘ transported s = transported t`）；
`smoothCompetitor_transport_K8`（S-A14-KERNEL）再要 `hmetric`
（`φ^* g_t ≤ c · g_s` on `K₀`，sheet SG-5 的 C⁰ metric 连续性）。
下面的 `example` 把 `φ` 与 `K₀` 原样喂给 kernel，`hmetric` 只作为 `example` 的局部参数
（type alignment；不是新前提，不进任何定理）。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime GC.LongTime.CuspP1
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MinimalSurface
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
    (cores : PersistentHyperbolicCores F K) (M : PrescribedCuspMeridian cores) {τ₀ : ℝ}
    (hτ₀ : M.exterior.start < τ₀) :
    ∃ (a b : ℝ) (hE : ∀ t ∈ Icc a b, M.exterior.start ≤ t), a < τ₀ ∧ τ₀ < b ∧
      ∀ (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (c : ℝ), 0 < c →
        ∃ (K₀ : Set (postStage F.observation s).Carrier)
          (φ : (postStage F.observation s).Carrier → (postStage F.observation t).Carrier),
          IsOpen K₀ ∧ ((∀ p ∈ K₀, ∀ w : TangentSpace (𝓡 3) p,
            (postMetric F.observation t).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
              (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤ c * (postMetric F.observation s).inner p w w) →
          ∀ v : C(closedDisk, (postStage F.observation s).Carrier),
            DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v →
            DiskWeakJordanTrace (M.transported s (hE s hs)) v →
            range v ⊆ M.exterior.region s → range v ⊆ K₀ →
            ∃ w : C(closedDisk, (postStage F.observation t).Carrier), (∀ z, w z = φ (v z)) ∧
              (DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) w ∧
                DiskWeakJordanTrace (M.transported t (hE t ht)) w ∧
                range w ⊆ M.exterior.region t) ∧
              riemannianDiskArea (postMetric F.observation t) w ≤
                c * riemannianDiskArea (postMetric F.observation s) v) := by
  obtain ⟨a, b, hE, hτa, hτb, hall⟩ := exists_tpw_nonmetric_SG cores M hτ₀
  refine ⟨a, b, hE, hτa, hτb, fun s hs t ht c hc => ?_⟩
  obtain ⟨K₀, φ, hK, hφ, hW, hγ⟩ := hall s hs t ht
  exact ⟨K₀, φ, hK, fun hmetric v hvs hv hvW hvK =>
    smoothCompetitor_transport_K8 (postMetric F.observation s) (postMetric F.observation t) hc hK
      hφ hW hγ hmetric hvs hv hvW hvK⟩

end GC.LongTime.CuspP1
