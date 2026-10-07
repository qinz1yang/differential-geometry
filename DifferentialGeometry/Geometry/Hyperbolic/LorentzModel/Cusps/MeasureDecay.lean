import DifferentialGeometry.Analysis.Integration.Measure.CylindricalEnd
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Ends

noncomputable section

open scoped Topology ENNReal

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)
open Busemann (busemann horosphere horoball)
open AsymptoticRays (rayTo)

variable {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r : ℝ}
  (D : FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ : D.centers)

local notation "P" => endStabilizer hn Γ (Set.singleton ξ.val)
local notation "πP" => Quotient.mk
  (@MulAction.orbitRel P (HUpper n) _ (EquivariantMap.subAction hn P))
local notation "πΓ" => Quotient.mk
  (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))
local notation "QΓ" => @MulAction.orbitRel.Quotient Γ (HUpper n) _
  (EquivariantMap.subAction hn Γ)

private local instance : MeasurableSpace QΓ := borel QΓ
private local instance : BorelSpace QΓ := ⟨rfl⟩

theorem horoballCylinderMap_image_tail {R : ℝ} (hR : 0 ≤ R) :
    (D.horoballCylinderMap hΓ ξ) '' {p | R ≤ p.2.val} =
      πΓ '' horoball ξ.val (D.level ξ - R) := by
  apply Set.Subset.antisymm
  · rintro q ⟨⟨⟨s, p, hp, rfl⟩, t⟩, ht, rfl⟩
    rw [D.horoballCylinderMap_apply_mk hΓ ξ p hp t]
    refine ⟨rayTo p ξ.val t.val, ?_, rfl⟩
    change busemann ξ.val (rayTo p ξ.val t.val) ≤ D.level ξ - R
    rw [HorosphereProjection.busemann_rayTo, show busemann ξ.val p = D.level ξ from hp]
    exact sub_le_sub_left ht _
  · rintro q ⟨p, hp, rfl⟩
    have hp' : busemann ξ.val p ≤ D.level ξ - R := hp
    let y : πP '' horoball ξ.val (D.level ξ) := ⟨πP p, ⟨p, by
      change busemann ξ.val p ≤ D.level ξ
      linarith, rfl⟩⟩
    refine ⟨D.horoballQuotientHomeomorph hΓ ξ y, ?_, ?_⟩
    · change R ≤ D.level ξ - busemann ξ.val p
      linarith
    · change D.horoballQuotientInclusion ξ
        ((D.horoballQuotientHomeomorph hΓ ξ).symm
          (D.horoballQuotientHomeomorph hΓ ξ y)) = πΓ p
      rw [Homeomorph.symm_apply_apply]
      rfl

theorem tendsto_measure_horoballCylinderMap_tail
    (μ : MeasureTheory.Measure QΓ) [MeasureTheory.IsFiniteMeasure μ] :
    Filter.Tendsto (fun R : ℝ => μ ((D.horoballCylinderMap hΓ ξ) '' {p | R ≤ p.2.val}))
      Filter.atTop (𝓝 0) :=
  (D.horoballCylinderMap_isClosedEmbedding hΓ ξ).tendsto_measure_image_cylinder_tail μ
    (MeasureTheory.measure_ne_top _ _)

include hΓ in
theorem tendsto_measure_horoball_sub_level
    (μ : MeasureTheory.Measure QΓ) [MeasureTheory.IsFiniteMeasure μ] :
    Filter.Tendsto (fun R : ℝ => μ (πΓ '' horoball ξ.val (D.level ξ - R)))
      Filter.atTop (𝓝 0) := by
  apply (D.tendsto_measure_horoballCylinderMap_tail hΓ ξ μ).congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
  rw [D.horoballCylinderMap_image_tail hΓ ξ hR]

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
