import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryData
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSpec

/-!
# Closed triangle blocks with hyperbolic base: the shape and the model

Lane B3c (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §0).
For charts `C` of a closed triangle block with `orbChi < 0` the hole orders satisfy
`1/p₁ + 1/p₂ + 1/p₃ < 1` (`sum_inv_holeOrder_of_hyp`), so they give CF's hyperbolic
`CompactShape` with the outer cone third (`closedHypShape`). The model `closedConnectionModel` is
`H² × ℝ` when `euler = 0` and `SL₂~` otherwise (`closedConnectionModel_of_hyp`), in both cases with
base curvature `-1`; its connection curvature is `0`, resp. `1`.
-/

set_option autoImplicit false

noncomputable section

open GC.Geometry GC.Endpoint

universe u

namespace GC.Seifert

namespace SeifertData

variable (d : SeifertData)

theorem closedConnectionModel_of_hyp (hχ : d.orbChi < 0) :
    d.closedConnectionModel = if d.euler = 0 then .hyperbolicProduct else .universalSL2 := by
  simp [closedConnectionModel, not_lt.mpr hχ.le, hχ.ne]

theorem closedConnectionModel_hyp_cases (hχ : d.orbChi < 0) :
    d.closedConnectionModel = .hyperbolicProduct ∨ d.closedConnectionModel = .universalSL2 := by
  rw [d.closedConnectionModel_of_hyp hχ]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem closedConnectionModel_baseCurvature_of_hyp (hχ : d.orbChi < 0) :
    d.closedConnectionModel.baseCurvature = -1 := by
  rcases d.closedConnectionModel_hyp_cases hχ with h | h <;> rw [h] <;> rfl

theorem closedConnectionModel_baseCurvature_le_of_hyp (hχ : d.orbChi < 0) :
    d.closedConnectionModel.baseCurvature ≤ 0 := by
  rw [d.closedConnectionModel_baseCurvature_of_hyp hχ]
  norm_num

theorem closedConnectionModel_connectionCurvature_of_hyp (hχ : d.orbChi < 0) :
    d.closedConnectionModel.connectionCurvature = if d.euler = 0 then 0 else 1 := by
  rw [d.closedConnectionModel_of_hyp hχ]
  split_ifs <;> rfl

end SeifertData

namespace SeifertBlockCharts

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)

theorem sum_inv_holeOrder_of_hyp (hχ : d.orbChi < 0) :
    (1 / (C.holeOrder hc h3 1 : ℝ) + 1 / C.holeOrder hc h3 2 + 1 / C.holeOrder hc h3 0) < 1 := by
  have h := C.orbChi_eq_holes hc h3
  rw [Fin.sum_univ_three] at h
  have hq : (1 / (C.holeOrder hc h3 1 : ℚ) + 1 / C.holeOrder hc h3 2 +
      1 / C.holeOrder hc h3 0) < 1 := by linarith
  have := (Rat.cast_lt (K := ℝ)).mpr hq
  push_cast at this
  exact this

def closedHypShape (hχ : d.orbChi < 0) : CompactShape where
  curv := .hyperbolic
  p₁ := C.holeOrder hc h3 1
  p₂ := C.holeOrder hc h3 2
  p₃ := C.holeOrder hc h3 0
  two_le_p₁ := C.two_le_holeOrder hc h3 1
  two_le_p₂ := C.two_le_holeOrder hc h3 2
  two_le_p₃ := C.two_le_holeOrder hc h3 0
  angle_cond := Or.inl ⟨rfl, C.sum_inv_holeOrder_of_hyp hc h3 hχ⟩

theorem closedHypShape_curv (hχ : d.orbChi < 0) :
    (C.closedHypShape hc h3 hχ).curv = .hyperbolic := rfl

end SeifertBlockCharts

end GC.Seifert
