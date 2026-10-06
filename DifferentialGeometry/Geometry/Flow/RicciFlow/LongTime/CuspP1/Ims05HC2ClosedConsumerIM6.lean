import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.Ims05HC2ClosedIM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RetainedConfinementWA2

/-!
# G16 consumer：`h6_of_HC2_closed_IM6` 逐字填入 O-W-ASSEMBLY-2 的 `h6`（O-W-IMS06 G16，后缀 `_IM6`）

`range_subset_of_retained_bands_WA2`（CuspP1/RetainedConfinementWA2.lean）的 `h6` 前提由 G16 的晚期形
无转换地给出（`T₁ ≤ s` 时）；其余前提照原样传入。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- consumer：在 ASSEMBLY-2 `range_subset_of_retained_bands_WA2` 里用 G16 供给 `h6`（晚期 `s`）；
其余前提成为 λ-参数。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) {s : ℝ} (hs : M.exterior.start ≤ s)
    (hTs : (h6_of_HC2_closed_IM6 M).choose ≤ s) {ιb : Type}
    (e Nb : ιb → Set (postStage F.observation s).Carrier)
    (Zb : ιb → (postStage F.observation s).Carrier → ℝ)
    (Us V K₀ ι₀ : Set (postStage F.observation s).Carrier) :=
  range_subset_of_retained_bands_WA2 M hs e Nb Zb (Us := Us) (V := V) (K₀ := K₀) (ι₀ := ι₀)
    (h6 := (h6_of_HC2_closed_IM6 M).choose_spec s hs hTs)

end GC.LongTime.CuspP1
