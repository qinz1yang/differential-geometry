import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryTpwTopWA
import DifferentialGeometry.Geometry.MinimalSurface.WeakDiskTransportK8

/-!
# `exists_tpw_Top_WA` 的 consumer：对齐 `smoothCompetitor_transport_K8`（S-A14-SURGERY，G4）

对任意消费者选取的紧 `KD ⊆ D`（取 `K₀ := ι_s '' interior KD`），`exists_tpw_Top_WA` 的五个字段
逐字是 `smoothCompetitor_transport_K8` 的 `hK hφ hW hγ hmetric`（`c = e^ε`）。下面的 `example`
把它们喂给 kernel：`range v ⊆ K₀` 的光滑 Morrey 类竞争者经 `P_{s→τ₀}` 变成 `τ₀` 时刻的竞争者，
面积至多乘 `e^ε`。
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
    (cores : PersistentHyperbolicCores F K) (M : PrescribedCuspMeridianTop_CPQ cores) {τ₀ : ℝ}
    (hτ₀ : M.exterior.start < τ₀) :
    ∃ (a b : ℝ) (hE : ∀ t ∈ Icc a b, M.exterior.start ≤ t) (hτab : τ₀ ∈ Icc a b),
      a < τ₀ ∧ τ₀ < b ∧
      ∀ ε : ℝ, 0 < ε → ∃ η > 0, ∀ (s : ℝ) (hs : s ∈ Icc a b), s < τ₀ → |s - τ₀| < η →
        ∃ (K₀ : Set (postStage F.observation s).Carrier)
          (φ : (postStage F.observation s).Carrier → (postStage F.observation τ₀).Carrier),
          IsOpen K₀ ∧
          ∀ v : C(closedDisk, (postStage F.observation s).Carrier),
            DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v →
            DiskWeakJordanTrace (M.transported s (hE s hs)) v →
            range v ⊆ M.exterior.region s → range v ⊆ K₀ →
            ∃ w : C(closedDisk, (postStage F.observation τ₀).Carrier), (∀ z, w z = φ (v z)) ∧
              (DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) w ∧
                DiskWeakJordanTrace (M.transported τ₀ (hE τ₀ hτab)) w ∧
                range w ⊆ M.exterior.region τ₀) ∧
              riemannianDiskArea (postMetric F.observation τ₀) w ≤
                Real.exp ε * riemannianDiskArea (postMetric F.observation s) v := by
  obtain ⟨N, Fs, Ls, hFL, J, hJh, hst, hτJ, a, b, hJab, hτab, hE, Φ, C, hτa, hτb, hJo, ⟨w₀⟩,
    hCc, hsm, hself, hcoc, hsupp, hleft, hright, hall⟩ := exists_tpw_Top_WA cores M hτ₀
  refine ⟨a, b, hE, hτab, hτa, hτb, fun ε hε => ?_⟩
  obtain ⟨η, hη, h⟩ := hall {w₀} isCompact_singleton ε hε
  refine ⟨η, hη, fun s hs hlt hd => ?_⟩
  obtain ⟨hK, hφ, hW, hγ, hmet⟩ := h s hs hlt hd w₀
  refine ⟨_, windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s τ₀ (hJab hs) hτJ w₀, hK,
    fun v hvs hv hvW hvK => ?_⟩
  exact smoothCompetitor_transport_K8 (postMetric F.observation s) (postMetric F.observation τ₀)
    (Real.exp_pos ε) hK hφ hW hγ (fun p hp w => hmet p (image_mono interior_subset hp) w)
    hvs hv hvW hvK

end GC.LongTime.CuspP1
