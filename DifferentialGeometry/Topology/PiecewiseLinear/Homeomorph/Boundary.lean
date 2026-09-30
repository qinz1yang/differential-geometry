import DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph.Basic
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.Homeomorph.SmallPerturbation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section HomeomorphInto

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]

variable {f : M → N} {K : Set M}

theorem IsPLHomeomorphInto.image_frontier [T2Space M] [T2Space N]
    (hf : IsPLHomeomorphInto n f K) (hK : IsOpen K) {P : Set M}
    (hP : IsCompact P) (hPK : P ⊆ K) : f '' frontier P = frontier (f '' P) := by
  let C : Set K := Subtype.val ⁻¹' P
  have hPrange : P ⊆ range (Subtype.val : K → M) := by
    simpa only [Subtype.range_coe] using hPK
  have hC : IsCompact C := Topology.IsInducing.subtypeVal.isCompact_preimage' hP hPrange
  have hCP : Subtype.val '' C = P := image_preimage_eq_of_subset hPrange
  have hsub := image_frontier_of_continuous_injective_isOpenMap_of_isCompact continuous_subtype_val Subtype.val_injective
    hK.isOpenMap_subtype_val hC
  rw [hCP] at hsub
  have hinj : Function.Injective (K.domRestrict f) := by
    intro x y hxy
    exact Subtype.ext (hf.injOn x.property y.property hxy)
  have hmain := image_frontier_of_continuous_injective_isOpenMap_of_isCompact hf.continuousOn.domRestrict hinj
    (hf.isOpenMap_domRestrict hK) hC
  have himage : (K.domRestrict f) '' C = f '' P := by
    rw [← hCP, image_image]
    rfl
  rw [himage] at hmain
  rw [← hsub, image_image]
  exact hmain

end HomeomorphInto

theorem IsPLHomeomorphInto.image_polyhedralBoundary {m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] [T2Space M] [T2Space N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N]
    {f : M → N} {U P : Set M} (hf : IsPLHomeomorphInto (m + 1) f U) (hU : IsOpen U)
    (hP : IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P) (hPU : P ⊆ U) :
    f '' polyhedralBoundary (m + 1) P hP = frontier (f '' P) := by
  rw [← frontier_eq_polyhedralBoundary hP]
  exact hf.image_frontier hU hP.isCompact hPU

end DifferentialGeometry.Topology.PiecewiseLinear
