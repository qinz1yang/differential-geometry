import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.MGLThickC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.MGLVolumeC12X

set_option autoImplicit false

/-!
# MGL 真证明：总装（O-C12X-MGLB G3，后缀 `_C12X`）

`exists_thick_ball_volume_lower_C12X` 的陈述逐字 = `MGLAdmission.lean` 的
`exists_thick_ball_volume_lower_MGL`（open 行照抄）。证明：

* (A) `exists_thick_uniformization_C12X`（O-C12X-MGLA）：一致 `ε > 0`，每个 `H` 的 uniformization
  数据 `(Γ, e)` 与一个 `ε`-thick 点 `x`；
* (B) `exists_ballVolume_lower_of_thick_C12X`（本 lane）：只依赖 `ε` 的 `c > 0`，
  `ofReal c ≤ ballVolume H.metric (e (π[Γ] x)) 1`；
* `a := 1`：`y ∈ B(p, 1)` ⇒ `B(p, 1) ⊆ B(y, 2)`（Riemannian 距离三角不等式），测度单调。
-/

noncomputable section

open DifferentialGeometry
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Hyperbolic
open scoped ENNReal

namespace GC.LongTime.Ch11.External

universe u

/-- `y ∈ B(p, 1)` ⇒ `B(p, 1) ⊆ B(y, 2)`。 -/
private theorem mglB_ball_one_subset_ball_two (H : FiniteVolumeHyperbolicModel.{u})
    {p y : H.Carrier} (hy : y ∈ riemannianBallOf H.metric p 1) :
    riemannianBallOf H.metric p 1 ⊆ riemannianBallOf H.metric y 2 := by
  intro z hz
  have hyp : riemannianEDistOf H.metric y p < ENNReal.ofReal 1 := by
    rw [riemannianEDistOf_comm]
    exact hy
  have hpz : riemannianEDistOf H.metric p z < ENNReal.ofReal 1 := hz
  change riemannianEDistOf H.metric y z < ENNReal.ofReal 2
  calc riemannianEDistOf H.metric y z
      ≤ riemannianEDistOf H.metric y p + riemannianEDistOf H.metric p z :=
        riemannianEDistOf_triangle _ _ _ _
    _ < ENNReal.ofReal 1 + ENNReal.ofReal 1 := ENNReal.add_lt_add hyp hpz
    _ = ENNReal.ofReal 2 := by
      rw [← ENNReal.ofReal_add zero_le_one zero_le_one]
      norm_num

/-- **hMGL 的真证明**：陈述逐字 = `exists_thick_ball_volume_lower_MGL`。 -/
theorem exists_thick_ball_volume_lower_C12X :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ H : FiniteVolumeHyperbolicModel.{u}, ∃ x : H.Carrier,
      ∀ y ∈ riemannianBallOf H.metric x a, ENNReal.ofReal c ≤ ballVolume H.metric y 2 := by
  obtain ⟨ε, hε, hA⟩ := exists_thick_uniformization_C12X.{u}
  obtain ⟨c, hc, hB⟩ := exists_ballVolume_lower_of_thick_C12X.{u} hε
  refine ⟨1, c, one_pos, hc, fun H => ?_⟩
  obtain ⟨Γ, _, _, e, he, hmetric, x, hx⟩ := hA H
  refine ⟨e (Quotient.mk _ x), fun y hy => (hB H Γ e he hmetric x hx).trans ?_⟩
  exact MeasureTheory.measure_mono (mglB_ball_one_subset_ball_two H hy)

end GC.LongTime.Ch11.External
