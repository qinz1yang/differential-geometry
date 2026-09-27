/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairBoundaryOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.ChartImagePLCell
import DifferentialGeometry.Topology.PiecewiseLinear.ChartTameNestedCells

open Set Filter
open scoped Topology Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.LocalDegree

theorem IsPLHomeomorphInto.isPLHomeomorphOn_chart_conjugate
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {S : Set M} {K : M → M} (hK : IsPLHomeomorphInto n K S) (hKim : K '' S = S)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ (plGroupoid n).maximalAtlas M) (hSc : S ⊆ c.source)
    (hB : IsPolyhedron (c '' S)) :
    IsPLHomeomorphOn (c ∘ K ∘ c.symm) (c '' S) (c '' S) := by
  have hBt : c '' S ⊆ c.target := image_subset_iff.mpr fun _ hx => c.map_source (hSc hx)
  have hback := c.symm_image_image_of_subset_source hSc
  have hi := isPLHomeomorphInto_symm_of_mem_maximalAtlas hc hB hBt
  have him : MapsTo c.symm (c '' S) S := fun _ hx => hback ▸ mem_image_of_mem c.symm hx
  have hKm : MapsTo K S S := fun _ hx => hKim ▸ mem_image_of_mem K hx
  have hci : IsPLOn n n c S := by
    rw [← hback]
    exact hi.isPLOn_inverse fun _ hx => c.right_inv (hBt hx)
  have hpl : IsPiecewiseAffineOn (c ∘ K ∘ c.symm) (c '' S) :=
    isPLOn_iff_isPiecewiseAffineOn.mp
      (hci.comp_of_mapsTo (hK.isPLOn.comp_of_mapsTo hi.isPLOn him) (hKm.comp him))
  have hbi : BijOn c.symm (c '' S) S := ⟨him, c.symm.injOn.mono hBt, hback.ge⟩
  have hbK : BijOn K S S := ⟨hKm, hK.injOn, hKim.ge⟩
  have hbc : BijOn c S (c '' S) := (c.injOn.mono hSc).bijOn_image
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hB hpl (hbc.comp (hbK.comp hbi))

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]

theorem isPLCirclePositive_chart_iff_chartOrientationParity_eq_zero_of_cell_pair
    {P PB Q QB D J : Set M} (hP : IsPLCellOn 3 P PB) (hQ : IsPLCellOn 3 Q QB)
    (hD : IsPLCellOn 2 D J) (hmeet : P ∩ Q = D) (hDP : D ⊆ PB) (hDQ : D ⊆ QB)
    {K : M → M} (hK : IsPLHomeomorphInto 3 K (P ∪ Q)) (hKim : K '' (P ∪ Q) = P ∪ Q)
    (hKP : K '' P = P) (hKQ : K '' Q = Q)
    {c : OpenPartialHomeomorph M E3} (hc : c ∈ (plGroupoid 3).maximalAtlas M)
    (hPc : P ⊆ c.source) (hQc : Q ⊆ c.source)
    (L : OpenPartialHomeomorph M M) (hLs : L.source = interior (P ∪ Q))
    (hL : ∀ x, L x = K x) {y : M} (hy : y ∈ L.source)
    (hyc : y ∈ c.source) (hLyc : L y ∈ c.source) :
    IsPLCirclePositive (c '' J) (c ∘ K ∘ c.symm) ↔
      chartOrientationParity c (L ≫ₕ c) y hyc ⟨hy, hLyc⟩ = 0 := by
  have hSc := union_subset hPc hQc
  have hDc : D ⊆ c.source := (hDP.trans hP.boundary_subset).trans hPc
  obtain ⟨hP₀, hPB₀⟩ := hP.isPLBall_image_chart hc hPc
  obtain ⟨hQ₀, hQB₀⟩ := hQ.isPLBall_image_chart hc hQc
  obtain ⟨r, hr, hJ₀⟩ := hD.exists_isPLHomeomorphOn_image_chart hc hDc
  have hmeet₀ : c '' P ∩ c '' Q = c '' D := by
    rw [← c.injOn.image_inter hPc hQc, hmeet]
  have hDP₀ : c '' D ⊆ frontier (c '' P) := by rw [← hPB₀]; exact image_mono hDP
  have hDQ₀ : c '' D ⊆ frontier (c '' Q) := by rw [← hQB₀]; exact image_mono hDQ
  have hpoly : IsPolyhedron (c '' (P ∪ Q)) := by
    rw [image_union]
    exact hP₀.isPolyhedron.union hQ₀.isPolyhedron
  let k := c ∘ K ∘ c.symm
  have hk := hK.isPLHomeomorphOn_chart_conjugate hKim hc hSc hpoly
  rw [image_union] at hk
  have hkeq : EqOn (k ∘ c) (c ∘ K) (P ∪ Q) := by
    intro x hx
    change c (K (c.symm (c x))) = c (K x)
    rw [c.left_inv (hSc hx)]
  have hkP : k '' (c '' P) = c '' P := by
    rw [← image_comp, (hkeq.mono subset_union_left).image_eq, image_comp, hKP]
  have hkQ : k '' (c '' Q) = c '' Q := by
    rw [← image_comp, (hkeq.mono subset_union_right).image_eq, image_comp, hKQ]
  have hyO : y ∈ interior (P ∪ Q) := hLs ▸ hy
  have himage : c '' interior (P ∪ Q) ⊆ interior (c '' (P ∪ Q)) :=
    interior_maximal (image_mono interior_subset)
      (c.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hSc))
  have hcyO : c y ∈ interior (c '' P ∪ c '' Q) := by
    rw [← image_union]
    exact himage ⟨y, hyO, rfl⟩
  have hlocal := isPLCirclePositive_iff_orientationParity_eq_zero_of_ball_pair
    hP₀ hQ₀ hr hmeet₀ hDP₀ hDQ₀ hk hkP hkQ hcyO
  have hpar : chartOrientationParity c (L ≫ₕ c) y hyc ⟨hy, hLyc⟩ =
      embeddingOrientationParity isOpen_interior
        (hk.isPiecewiseAffineOn.continuousOn.mono interior_subset)
        (hk.bijOn.injOn.mono interior_subset) ⟨c y, hcyO⟩ := by
    unfold chartOrientationParity
    apply embeddingOrientationParity_congr
    exact Filter.Eventually.of_forall fun x => congrArg c (hL (c.symm x))
  rw [hJ₀]
  exact hlocal.trans (by rw [hpar])

end DifferentialGeometry.Topology.PiecewiseLinear
