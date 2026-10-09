import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MorreyIntegralBoundHC_GB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterImportedMorreyHC

set_option autoImplicit false

/-!
# G4 consumer：`_HC` 的 `obtain` 结果直接喂 `integral_bound_of_confined_morrey_HC_GB`
（车道 S-A10-GAUSS，后缀 `_GB`）

**UNREGISTERED**：本模块 import `P2AdapterImportedMorreyHC`（经 `P2AdapterImportedTop` 的 3 个文档化
未证 mirrors），和 `P2AdapterImported*` 家族同一例外——不要登记进 root aggregate，也不要被家族外的
模块 import。本文件里没有任何命名声明（只有 `example`），所以 audit 不含它；
`MorreyIntegralBoundHC_GB` 本身只依赖无未证项的 `P2AdapterImportedDefs`，可登记。

`example` 做的事：`obtain` 出 `_HC` 结论体的全部条款，把 `a ha ρ hρ γU q hsm hMor hloc` **不加转换**
地喂给 G4 定理，只需要额外给 Ricci flow 方程 `hder`（`∂_t g = −2 Ric`，显式参数）与度量族 `Gfam`
（`Gfam t t = postMetric F.observation t`）。
-/

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

example (M : PrescribedCuspMeridianTop_CPQ cores) {δ' : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ')
    (tmin : ℝ)
    (Gfam : ∀ t : ℝ, ℝ → SmoothRiemannianMetric ThreeModel (postStage F.observation t).Carrier)
    (hGt : ∀ t, Gfam t t = postMetric F.observation t)
    (hder : ∀ t : ℝ, ∀ x : (postStage F.observation t).Carrier, ∀ X Y : EuclideanSpace ℝ (Fin 3),
      HasDerivAt (fun r : ℝ => (Gfam t r).inner x X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (Gfam t t) x X Y) t) :
    True := by
  obtain ⟨a, ha, T₀, h₀, -, h1, hHC⟩ := M.exists_eventual_confined_morrey_disk_HC tmin
  obtain ⟨ρ, hρ, hreg, hcpt, hcvx, γU, q, hγ, hsm, hMor, hrange, hint, hneg, hbd, hweak, hloc⟩ :=
    hHC T₀ le_rfl T₀ le_rfl
  have key := H.integral_bound_of_confined_morrey_HC_GB (by linarith) (Gfam T₀) (hGt T₀) a ha ρ hρ
    γU q hsm hMor hloc (fun w X Y => hder T₀ _ X Y)
  obtain ⟨v, Q, φ, hv, harea, hext, hφ, hm, htr, hA, hbound⟩ := key
  trivial

end GC.LongTime.CuspP1
