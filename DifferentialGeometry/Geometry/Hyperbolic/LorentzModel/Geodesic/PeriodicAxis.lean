import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.Axis
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Projection
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegionNeighborhoods
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.EquivariantMaps.Existence

noncomputable section

namespace DifferentialGeometry.AxisGeometry

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open HyperbolicAction (poMulAction)
open AsymptoticRays (rayTo)
open OrbifoldStrata (closedSmallSubgroup)
open OrbifoldThinRegions (thinRegion)

variable {n : ℕ} (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))

theorem smul_rayTo_of_mem_axis (g : PO n 1) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hη : (poBoundaryMulAction hn).smul g η = η)
    {y : HUpper n} (hy : y ∈ axis ξ η) (t : ℝ) :
    (poMulAction hn).smul g (rayTo y ξ t) =
      rayTo y ξ (t + Real.log (BusemannCocycle.poConfFactor hn g ξ)) := by
  obtain ⟨s, rfl⟩ := (axis_eq_range_rayTo ξ η hne) ▸ hy
  rw [HorosphereProjection.rayTo_add, HorosphereProjection.rayTo_add,
    BoundaryStabilizer.smul_axis_ray hn g ξ η hne hξ hη]
  congr 1
  ring

theorem exists_nonzero_shift_sq_of_pair_preserving
    (ξ η : BoundaryH n) (hne : ξ ≠ η) (a : Γ) (ha : a ^ 2 ≠ 1)
    (hpair : (poBoundaryMulAction hn).smul (a : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (a : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n)))
    {y : HUpper n} (hy : y ∈ axis ξ η) :
    letI := EquivariantMap.subAction hn Γ
    IsCancelSMul Γ (HUpper n) →
    ∃ τ : ℝ, τ = Real.log (BusemannCocycle.poConfFactor hn ((a : PO n 1) ^ 2) ξ) ∧
      τ ≠ 0 ∧ |τ| ≤ 2 * dist ((poMulAction hn).smul (a : PO n 1) y) y ∧
      ∀ t : ℝ, (poMulAction hn).smul ((a : PO n 1) ^ 2) (rayTo y ξ t) = rayTo y ξ (t + τ) := by
  let := EquivariantMap.subAction hn Γ
  intro hfree
  let := hfree
  let := poBoundaryMulAction hn
  have hfix : (a : PO n 1) ^ 2 • ξ = ξ ∧ (a : PO n 1) ^ 2 • η = η := by
    rcases boundary_pair_cases hn a ξ η hne hpair with h | h
    · change (a : PO n 1) • ξ = ξ ∧ (a : PO n 1) • η = η at h
      simp only [pow_two, mul_smul, h.1, h.2, and_self]
    · change (a : PO n 1) • ξ = η ∧ (a : PO n 1) • η = ξ at h
      simp only [pow_two, mul_smul, h.1, h.2, and_self]
  let τ := Real.log (BusemannCocycle.poConfFactor hn ((a : PO n 1) ^ 2) ξ)
  have hshift (t : ℝ) :
      (poMulAction hn).smul ((a : PO n 1) ^ 2) (rayTo y ξ t) = rayTo y ξ (t + τ) :=
    smul_rayTo_of_mem_axis hn _ ξ η hne hfix.1 hfix.2 hy t
  have hz : (poMulAction hn).smul ((a : PO n 1) ^ 2) y = rayTo y ξ τ := by
    simpa only [AsymptoticRays.rayTo_zero, zero_add] using hshift 0
  have hτ : τ ≠ 0 := by
    intro hzero
    have hfixed : (a ^ 2) • y = y := by
      change (poMulAction hn).smul ((a : PO n 1) ^ 2) y = y
      rw [hz, hzero, AsymptoticRays.rayTo_zero]
    exact ha (IsCancelSMul.eq_one_of_smul hfixed)
  have hdist : dist ((poMulAction hn).smul ((a : PO n 1) ^ 2) y) y = |τ| := by
    rw [hz]
    exact (dist_comm _ _).trans (AsymptoticRays.dist_rayTo_self y ξ τ)
  refine ⟨τ, rfl, hτ, ?_, hshift⟩
  rw [← hdist]
  let := poMulAction hn
  calc
    dist ((a : PO n 1) ^ 2 • y) y ≤
        dist ((a : PO n 1) ^ 2 • y) ((a : PO n 1) • y) + dist ((a : PO n 1) • y) y :=
      dist_triangle _ _ _
    _ = dist ((a : PO n 1) • y) y + dist ((a : PO n 1) • y) y := by
      rw [pow_two, mul_smul, HyperbolicAction.po_dist_smul hn]
    _ = _ := (two_mul _).symm

theorem exists_short_shift_sq_of_mem_axial_thinRegion
    {r : ℝ} (ξ η : BoundaryH n) (hne : ξ ≠ η) {y : HUpper n}
    (hy : y ∈ axis ξ η) (hthin : y ∈ thinRegion hn Γ r {ξ, η})
    (htorsion : ∀ a : Γ, IsOfFinOrder a → a = 1) :
    letI := EquivariantMap.subAction hn Γ
    IsCancelSMul Γ (HUpper n) →
    ∃ (a : Γ) (τ : ℝ), a ≠ 1 ∧ a ^ 2 ≠ 1 ∧
      dist ((poMulAction hn).smul (a : PO n 1) y) y ≤ r ∧
      τ = Real.log (BusemannCocycle.poConfFactor hn ((a : PO n 1) ^ 2) ξ) ∧
      τ ≠ 0 ∧ |τ| ≤ 2 * r ∧
      ∀ t : ℝ, (poMulAction hn).smul ((a : PO n 1) ^ 2) (rayTo y ξ t) = rayTo y ξ (t + τ) := by
  let := EquivariantMap.subAction hn Γ
  intro hfree
  obtain ⟨a, ha, hshort⟩ := OrbifoldThinRegions.exists_short_ne_one_of_mem_thinRegion hn Γ hthin
  have ha2 : a ^ 2 ≠ 1 := fun h => ha (htorsion a
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, h⟩))
  let b : closedSmallSubgroup hn Γ r y := ⟨a, Subgroup.subset_closure ⟨a.property, hshort⟩⟩
  have hpair : (poBoundaryMulAction hn).smul (a : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (a : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n)) :=
    ⟨hthin.2.invariant b (by simp), hthin.2.invariant b (by simp)⟩
  obtain ⟨τ, hτeq, hτ, hbound, hshift⟩ :=
    exists_nonzero_shift_sq_of_pair_preserving hn Γ ξ η hne a ha2 hpair hy hfree
  exact ⟨a, τ, ha, ha2, hshort, hτeq, hτ, hbound.trans (mul_le_mul_of_nonneg_left hshort (by norm_num)), hshift⟩

end DifferentialGeometry.AxisGeometry
