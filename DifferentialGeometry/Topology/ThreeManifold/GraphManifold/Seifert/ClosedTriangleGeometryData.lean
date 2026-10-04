import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockCharts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclid
import DifferentialGeometry.Geometry.Thurston.Models.ConeModel

/-!
# Closed triangle blocks: cone data by hole and the model

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§0). Seifert data with no port and three cones have no normal filling, `k = 3` and three fillings
(`normals_eq_nil_of_closedTriangle`, `k_eq_three_of_closedTriangle`). For charts `C` of such a
block, `C.closedHoleEquiv` names the fillings by their holes (`port_closedHoleEquiv`): hole `0` is
the outer circle, holes `1`, `2` are centred at `3/2`, `-3/2`. The hole data `holeOrder`,
`holeTwist`, `holeA`, `holeB` satisfy `2 ≤ p`, `gcd (p, q) = 1` and the Bézout identity of the
chart matrix, and `orbChi = ∑ 1/pⱼ - 1`, `euler = -∑ qⱼ/pⱼ` (`orbChi_eq_holes`,
`euler_eq_holes`). `closedConnectionModel` reads the sign of `orbChi` and whether `euler = 0`;
its Thurston model is `closedTable` (`closedConnectionModel_thurston`), it is never hyperbolic, and
its base is flat exactly when `orbChi = 0`, in which case the hole orders give CF's
`EuclidShape` with the outer cone third (`closedEuclidShape`).
-/

set_option autoImplicit false

noncomputable section

open GC.Geometry GC.Endpoint

universe u

namespace GC.Seifert

namespace SeifertData

variable (d : SeifertData)

theorem normals_eq_nil_of_closedTriangle (hc : d.ports = 0) (h3 : d.cones.length = 3) :
    d.normals = [] := by
  have h := d.ports_add_length_add_length
  have hk := d.k_le_three
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem k_eq_three_of_closedTriangle (hc : d.ports = 0) (h3 : d.cones.length = 3) : d.k = 3 := by
  have h := d.ports_add_length_add_length
  have hk := d.k_le_three
  omega

theorem fillingCount_eq_cones_of_closedTriangle (hc : d.ports = 0) (h3 : d.cones.length = 3) :
    d.fillingCount = d.cones.length := by
  simp [fillingCount, d.normals_eq_nil_of_closedTriangle hc h3]

theorem fillingSlope_of_closedTriangle (hc : d.ports = 0) (h3 : d.cones.length = 3)
    (m : Fin d.fillingCount) :
    d.fillingSlope m =
      ((d.cones[Fin.cast (d.fillingCount_eq_cones_of_closedTriangle hc h3) m].1 : ℤ),
        d.cones[Fin.cast (d.fillingCount_eq_cones_of_closedTriangle hc h3) m].2) := by
  have hm : m = Fin.castAdd d.normals.length
      (Fin.cast (d.fillingCount_eq_cones_of_closedTriangle hc h3) m) := Fin.ext rfl
  conv_lhs => rw [hm]
  rw [fillingSlope, Fin.append_left]

def closedConnectionModel : ConnectionModel :=
  if 0 < d.orbChi then .spherical
  else if d.orbChi = 0 then (if d.euler = 0 then .euclidean else .nil)
  else if d.euler = 0 then .hyperbolicProduct else .universalSL2

theorem closedConnectionModel_thurston (hc : d.ports = 0) (h3 : d.cones.length = 3) :
    d.closedConnectionModel.thurston = closedTable ⟨d, hc⟩ := by
  unfold closedConnectionModel closedTable
  by_cases hχ : 0 < d.orbChi
  · simp [hχ, d.euler_ne_zero_of_three_cones hc h3 hχ, ConnectionModel.thurston]
  · by_cases h0 : d.orbChi = 0 <;> by_cases he : d.euler = 0 <;>
      simp [hχ, h0, he, ConnectionModel.thurston]

theorem closedConnectionModel_thurston_ne_hyperbolic :
    d.closedConnectionModel.thurston ≠ .hyperbolic :=
  ConnectionModel.thurston_ne_hyperbolic _

theorem closedConnectionModel_baseCurvature_eq_zero_iff :
    d.closedConnectionModel.baseCurvature = 0 ↔ d.orbChi = 0 := by
  unfold closedConnectionModel
  by_cases hχ : 0 < d.orbChi
  · simp [hχ, hχ.ne', ConnectionModel.baseCurvature]
  · by_cases h0 : d.orbChi = 0 <;> by_cases he : d.euler = 0 <;>
      simp [hχ, h0, he, ConnectionModel.baseCurvature]

theorem closedConnectionModel_of_flat (h0 : d.orbChi = 0) :
    d.closedConnectionModel = if d.euler = 0 then .euclidean else .nil := by
  simp [closedConnectionModel, h0]

end SeifertData

namespace SeifertBlockCharts

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)

def closedHoleEquiv : Fin 3 ≃ Fin d.fillingCount :=
  (finCongr (d.k_eq_three_of_closedTriangle hc h3).symm).trans (C.port.symm.trans
    ((Equiv.sumCongr (finCongr hc) (Equiv.refl _)).trans (Equiv.emptySum (Fin 0) _)))

theorem port_closedHoleEquiv (j : Fin 3) :
    C.port (.inr (C.closedHoleEquiv hc h3 j)) =
      Fin.cast (d.k_eq_three_of_closedTriangle hc h3).symm j := by
  set k := Fin.cast (d.k_eq_three_of_closedTriangle hc h3).symm j with hk
  have hdef : C.closedHoleEquiv hc h3 j =
      Equiv.emptySum (Fin 0) _ ((Equiv.sumCongr (finCongr hc) (Equiv.refl _)) (C.port.symm k)) :=
    rfl
  rcases hx : C.port.symm k with i | m
  · exact (Fin.cast hc i).elim0
  · rw [hdef, hx]
    change C.port (.inr m) = k
    rw [← hx, Equiv.apply_symm_apply]

def holeOrder (j : Fin 3) : ℕ := (d.fillingSlope (C.closedHoleEquiv hc h3 j)).1.toNat

def holeTwist (j : Fin 3) : ℤ := (d.fillingSlope (C.closedHoleEquiv hc h3 j)).2

def holeA (j : Fin 3) : ℤ := C.a (C.closedHoleEquiv hc h3 j)

def holeB (j : Fin 3) : ℤ := C.b (C.closedHoleEquiv hc h3 j)

theorem holeOrder_cast (j : Fin 3) :
    ((C.holeOrder hc h3 j : ℕ) : ℤ) = (d.fillingSlope (C.closedHoleEquiv hc h3 j)).1 := by
  have := d.fillingSlope_fst_pos (C.closedHoleEquiv hc h3 j)
  unfold holeOrder
  omega

theorem gcd_holeOrder_holeTwist (j : Fin 3) :
    Int.gcd (C.holeOrder hc h3 j : ℤ) (C.holeTwist hc h3 j) = 1 := by
  rw [C.holeOrder_cast hc h3 j, holeTwist]
  exact d.isPrimitive_fillingSlope _

theorem holeBezout (j : Fin 3) :
    (C.holeOrder hc h3 j : ℤ) * C.holeB hc h3 j - C.holeA hc h3 j * C.holeTwist hc h3 j = 1 := by
  rw [C.holeOrder_cast hc h3 j]
  exact C.bezout _

theorem matrix_closedHoleEquiv (j : Fin 3) :
    (C.matrix (C.closedHoleEquiv hc h3 j) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-(C.holeOrder hc h3 j : ℤ), C.holeA hc h3 j; -C.holeTwist hc h3 j, C.holeB hc h3 j] := by
  rw [C.matrix_eq, C.holeOrder_cast hc h3 j]
  rfl

private theorem sum_cones_eq_holes (f : ℕ × ℤ → ℚ) :
    (d.cones.map f).sum = ∑ j : Fin 3, f (d.cones[Fin.cast
      (d.fillingCount_eq_cones_of_closedTriangle hc h3) (C.closedHoleEquiv hc h3 j)]) := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  let e : Fin 3 ≃ Fin d.cones.length := (C.closedHoleEquiv hc h3).trans
    (finCongr (d.fillingCount_eq_cones_of_closedTriangle hc h3))
  exact (e.sum_comp (fun i => f d.cones[i])).symm

theorem cone_eq_hole (j : Fin 3) :
    d.cones[Fin.cast (d.fillingCount_eq_cones_of_closedTriangle hc h3)
      (C.closedHoleEquiv hc h3 j)] = (C.holeOrder hc h3 j, C.holeTwist hc h3 j) := by
  have h1 := C.holeOrder_cast hc h3 j
  have h2 : C.holeTwist hc h3 j = (d.fillingSlope (C.closedHoleEquiv hc h3 j)).2 := rfl
  rw [d.fillingSlope_of_closedTriangle hc h3] at h1 h2
  ext
  · have h1' : ((d.cones[Fin.cast (d.fillingCount_eq_cones_of_closedTriangle hc h3)
        (C.closedHoleEquiv hc h3 j)].1 : ℕ) : ℤ) = (C.holeOrder hc h3 j : ℤ) := h1.symm
    exact_mod_cast h1'
  · exact h2.symm

theorem two_le_holeOrder (j : Fin 3) : 2 ≤ C.holeOrder hc h3 j := by
  have h := d.two_le_of_mem_cones _ (List.getElem_mem
    (h := (Fin.cast (d.fillingCount_eq_cones_of_closedTriangle hc h3)
      (C.closedHoleEquiv hc h3 j)).isLt))
  rw [show d.cones[(Fin.cast (d.fillingCount_eq_cones_of_closedTriangle hc h3)
      (C.closedHoleEquiv hc h3 j) : ℕ)] = _ from C.cone_eq_hole hc h3 j] at h
  exact h

theorem orbChi_eq_holes :
    d.orbChi = ∑ j : Fin 3, 1 / (C.holeOrder hc h3 j : ℚ) - 1 := by
  rw [SeifertData.orbChi, hc, C.sum_cones_eq_holes hc h3]
  simp only [C.cone_eq_hole hc h3, Fin.sum_univ_three, Nat.cast_zero, sub_zero]
  ring

theorem euler_eq_holes :
    d.euler = -∑ j : Fin 3, (C.holeTwist hc h3 j : ℚ) / C.holeOrder hc h3 j := by
  rw [SeifertData.euler, d.normals_eq_nil_of_closedTriangle hc h3, C.sum_cones_eq_holes hc h3]
  simp only [C.cone_eq_hole hc h3, List.map_nil, List.sum_nil, add_zero]

theorem sum_inv_holeOrder_of_flat (h0 : d.orbChi = 0) :
    (1 / (C.holeOrder hc h3 1 : ℝ) + 1 / C.holeOrder hc h3 2 + 1 / C.holeOrder hc h3 0) = 1 := by
  have h := C.orbChi_eq_holes hc h3
  rw [h0, Fin.sum_univ_three] at h
  have hq : (1 / (C.holeOrder hc h3 1 : ℚ) + 1 / C.holeOrder hc h3 2 +
      1 / C.holeOrder hc h3 0) = 1 := by linarith
  have := congrArg (fun x : ℚ => (x : ℝ)) hq
  push_cast at this
  exact this

def closedEuclidShape (h0 : d.orbChi = 0) : EuclidShape where
  p₁ := C.holeOrder hc h3 1
  p₂ := C.holeOrder hc h3 2
  p₃ := C.holeOrder hc h3 0
  two_le_p₁ := C.two_le_holeOrder hc h3 1
  two_le_p₂ := C.two_le_holeOrder hc h3 2
  two_le_p₃ := C.two_le_holeOrder hc h3 0
  sum_inv := C.sum_inv_holeOrder_of_flat hc h3 h0

end SeifertBlockCharts

end GC.Seifert
