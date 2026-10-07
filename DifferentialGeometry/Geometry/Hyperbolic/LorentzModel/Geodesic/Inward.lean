import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.RadialFlow
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegions

noncomputable section

namespace DifferentialGeometry.AxisGeometry

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open HyperbolicAction (poMulAction)
open HyperbolicConvexity (geodFromTo)

variable {n : ℕ}

theorem cosh_displacement_axisRadialFlow (hn : 1 ≤ n) (g : PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n))) (t : ℝ) (y : HUpper n) :
    Real.cosh (dist ((poMulAction hn).smul g (axisRadialFlow ξ η hne t y))
      (axisRadialFlow ξ η hne t y)) =
      Real.cosh (dist ((poMulAction hn).smul g (axisFoot ξ η hne y)) (axisFoot ξ η hne y)) +
        Real.exp t ^ 2 * (Real.cosh (dist ((poMulAction hn).smul g y) y) -
          Real.cosh (dist ((poMulAction hn).smul g (axisFoot ξ η hne y)) (axisFoot ξ η hne y))) := by
  by_cases hy : axisFoot ξ η hne y = y
  · have hym : y ∈ axis ξ η := hy ▸ axisFoot_mem ξ η hne y
    rw [axisRadialFlow_eq_self_of_mem_axis ξ η hne t hym, hy, sub_self, mul_zero, add_zero]
  · have he := cosh_displacement_normal_geod hn g ξ η hne hpair y hy
      (dist (axisRadialFlow ξ η hne t y) (axisFoot ξ η hne y))
    rw [← axisRadialFlow_eq_normal_geod ξ η hne t y hy] at he
    have hs := sinh_dist_axisFoot_axisRadialFlow ξ η hne t y
    rw [axisFoot_axisRadialFlow, dist_comm y (axisFoot ξ η hne y)] at hs
    have hd : Real.sinh (dist (axisFoot ξ η hne y) y) ≠ 0 :=
      (Real.sinh_pos_iff.mpr (dist_pos.mpr hy)).ne'
    rw [hs, mul_div_cancel_right₀ _ hd] at he
    exact he

theorem monotone_displacement_axisRadialFlow (hn : 1 ≤ n) (g : PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n))) (y : HUpper n) :
    Monotone (fun t : ℝ => dist ((poMulAction hn).smul g (axisRadialFlow ξ η hne t y))
      (axisRadialFlow ξ η hne t y)) := by
  intro s t hst
  have hproj := Real.cosh_strictMonoOn.monotoneOn dist_nonneg dist_nonneg
    (displacement_axisFoot_le hn g ξ η hne hpair y)
  have hcoeff : 0 ≤ Real.cosh (dist ((poMulAction hn).smul g y) y) -
      Real.cosh (dist ((poMulAction hn).smul g (axisFoot ξ η hne y)) (axisFoot ξ η hne y)) :=
    sub_nonneg.mpr hproj
  have hexp : Real.exp s ^ 2 ≤ Real.exp t ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos s).le (Real.exp_le_exp.mpr hst) 2
  apply (Real.cosh_strictMonoOn.le_iff_le dist_nonneg dist_nonneg).mp
  rw [cosh_displacement_axisRadialFlow hn g ξ η hne hpair,
    cosh_displacement_axisRadialFlow hn g ξ η hne hpair]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hexp hcoeff)

theorem displacement_axisRadialFlow_le_of_nonpos (hn : 1 ≤ n) (g : PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n)))
    {t : ℝ} (ht : t ≤ 0) (y : HUpper n) :
    dist ((poMulAction hn).smul g (axisRadialFlow ξ η hne t y)) (axisRadialFlow ξ η hne t y) ≤
      dist ((poMulAction hn).smul g y) y := by
  simpa only [axisRadialFlow_zero] using (monotone_displacement_axisRadialFlow hn g ξ η hne hpair y) ht

theorem monotoneOn_displacement_normal_geod (hn : 1 ≤ n) (g : PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n)))
    (y : HUpper n) (hy : axisFoot ξ η hne y ≠ y) :
    MonotoneOn (fun t : ℝ => dist ((poMulAction hn).smul g
      (geodFromTo (axisFoot ξ η hne y) y hy t)) (geodFromTo (axisFoot ξ η hne y) y hy t))
        (Set.Ici 0) := by
  intro s hs t ht hst
  have hden : 0 < Real.sinh (dist (axisFoot ξ η hne y) y) :=
    Real.sinh_pos_iff.mpr (dist_pos.mpr hy)
  have hratio : Real.sinh s / Real.sinh (dist (axisFoot ξ η hne y) y) ≤
      Real.sinh t / Real.sinh (dist (axisFoot ξ η hne y) y) :=
    div_le_div_of_nonneg_right (Real.sinh_le_sinh.mpr hst) hden.le
  have hratio0 : 0 ≤ Real.sinh s / Real.sinh (dist (axisFoot ξ η hne y) y) :=
    div_nonneg (Real.sinh_nonneg_iff.mpr hs) hden.le
  have hsquare := pow_le_pow_left₀ hratio0 hratio 2
  have hproj := Real.cosh_strictMonoOn.monotoneOn dist_nonneg dist_nonneg
    (displacement_axisFoot_le hn g ξ η hne hpair y)
  apply (Real.cosh_strictMonoOn.le_iff_le dist_nonneg dist_nonneg).mp
  rw [cosh_displacement_normal_geod hn g ξ η hne hpair,
    cosh_displacement_normal_geod hn g ξ η hne hpair]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsquare (sub_nonneg.mpr hproj))

end DifferentialGeometry.AxisGeometry

namespace DifferentialGeometry.OrbifoldThinRegions

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH)
open AxisGeometry (axisFoot axisRadialFlow)
open OrbifoldStrata (closedSmallSubgroup closedSmallSubgroup_le)
open ElementaryEnds (HasEnds)

variable {n : ℕ}

theorem closedSmallSubgroup_le_axisRadialFlow (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (r : ℝ) (ξ η : BoundaryH n) (hne : ξ ≠ η) (y : HUpper n)
    (hends : HasEnds hn (closedSmallSubgroup hn Γ r y) {ξ, η}) {t : ℝ} (ht : t ≤ 0) :
    closedSmallSubgroup hn Γ r y ≤ closedSmallSubgroup hn Γ r (axisRadialFlow ξ η hne t y) := by
  apply Subgroup.closure_mono
  intro g hg
  have hm : g ∈ closedSmallSubgroup hn Γ r y := Subgroup.subset_closure hg
  exact ⟨hg.1, (AxisGeometry.displacement_axisRadialFlow_le_of_nonpos hn g ξ η hne
    ⟨hends.invariant ⟨g, hm⟩ (by simp), hends.invariant ⟨g, hm⟩ (by simp)⟩ ht y).trans hg.2⟩

theorem closedSmallSubgroup_le_axisFoot (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (r : ℝ) (ξ η : BoundaryH n) (hne : ξ ≠ η) (y : HUpper n)
    (hends : HasEnds hn (closedSmallSubgroup hn Γ r y) {ξ, η}) :
    closedSmallSubgroup hn Γ r y ≤ closedSmallSubgroup hn Γ r (axisFoot ξ η hne y) := by
  apply Subgroup.closure_mono
  intro g hg
  have hm : g ∈ closedSmallSubgroup hn Γ r y := Subgroup.subset_closure hg
  exact ⟨hg.1, (AxisGeometry.displacement_axisFoot_le hn g ξ η hne
    ⟨hends.invariant ⟨g, hm⟩ (by simp), hends.invariant ⟨g, hm⟩ (by simp)⟩ y).trans hg.2⟩

theorem axisRadialFlow_mem_thinRegion_of_nonpos (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    {y : HUpper n} (hy : y ∈ thinRegion hn Γ r {ξ, η}) {t : ℝ} (ht : t ≤ 0)
    (hgeom : BoundaryStabilizer.ElementaryGeometry hn
      (closedSmallSubgroup hn Γ r (axisRadialFlow ξ η hne t y))) :
    axisRadialFlow ξ η hne t y ∈ thinRegion hn Γ r {ξ, η} := by
  let _ := hy.1
  have hle := closedSmallSubgroup_le_axisRadialFlow hn Γ r ξ η hne y hy.2 ht
  refine ⟨Infinite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle), ?_⟩
  exact hy.2.of_le (hΓ.mono (closedSmallSubgroup_le hn Γ r _)) hle hgeom

theorem axisFoot_mem_thinRegion (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    {y : HUpper n} (hy : y ∈ thinRegion hn Γ r {ξ, η})
    (hgeom : BoundaryStabilizer.ElementaryGeometry hn (closedSmallSubgroup hn Γ r (axisFoot ξ η hne y))) :
    axisFoot ξ η hne y ∈ thinRegion hn Γ r {ξ, η} := by
  let _ := hy.1
  have hle := closedSmallSubgroup_le_axisFoot hn Γ r ξ η hne y hy.2
  refine ⟨Infinite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle), ?_⟩
  exact hy.2.of_le (hΓ.mono (closedSmallSubgroup_le hn Γ r _)) hle hgeom

end DifferentialGeometry.OrbifoldThinRegions
