import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.AxialProduct
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.GraphRegion
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.AxialGraphChart

noncomputable section

open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.HorosphereProjection

open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH)
open AsymptoticRays (rayTo)
open Busemann (busemann)

variable {n : ℕ}

theorem busemann_rayTo_neg_half (p : HUpper n) (ξ : BoundaryH n) (t : ℝ) :
    busemann ξ (rayTo p ξ (-t / 2)) = busemann ξ p + t / 2 := by
  rw [busemann_rayTo]
  ring

theorem hasDerivAt_busemann_rayTo_neg_half (p : HUpper n) (ξ : BoundaryH n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => busemann ξ (rayTo p ξ (-s / 2))) (1 / 2) t := by
  simp_rw [busemann_rayTo_neg_half]
  exact ((hasDerivAt_id t).div_const 2).const_add _

end DifferentialGeometry.HorosphereProjection

namespace DifferentialGeometry.AxisGeometry

open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH)
open HyperbolicConvexity (geodFromTo)

variable {n : ℕ}

theorem dist_axisFoot_normal_geod_add_half
    (ξ η : BoundaryH n) (hne : ξ ≠ η) (p : HUpper n) (hp : axisFoot ξ η hne p ≠ p)
    {t : ℝ} (ht : 0 ≤ dist (axisFoot ξ η hne p) p + t / 2) :
    let c := geodFromTo (axisFoot ξ η hne p) p hp (dist (axisFoot ξ η hne p) p + t / 2)
    dist c (axisFoot ξ η hne c) = dist (axisFoot ξ η hne p) p + t / 2 := by
  exact (AxialThinCompactness.dist_normal_axisFoot ξ η hne p hp _).trans (abs_of_nonneg ht)

theorem hasDerivAt_log_sinh_dist_axisFoot_normal_geod_add_half
    (ξ η : BoundaryH n) (hne : ξ ≠ η) (p : HUpper n) (hp : axisFoot ξ η hne p ≠ p)
    {t : ℝ} (ht : 0 < dist (axisFoot ξ η hne p) p + t / 2) :
    let c := fun s : ℝ =>
      geodFromTo (axisFoot ξ η hne p) p hp (dist (axisFoot ξ η hne p) p + s / 2)
    HasDerivAt (fun s => Real.log (Real.sinh (dist (c s) (axisFoot ξ η hne (c s)))))
      (Real.cosh (dist (axisFoot ξ η hne p) p + t / 2) /
        (2 * Real.sinh (dist (axisFoot ξ η hne p) p + t / 2))) t := by
  let r := dist (axisFoot ξ η hne p) p
  have hd : HasDerivAt (fun s : ℝ => r + s / 2) (1 / 2) t :=
    ((hasDerivAt_id t).div_const 2).const_add r
  have hlog := hd.sinh.log (Real.sinh_pos_iff.mpr ht).ne'
  have heq : (fun s : ℝ => Real.log (Real.sinh (dist
      (geodFromTo (axisFoot ξ η hne p) p hp (r + s / 2))
      (axisFoot ξ η hne (geodFromTo (axisFoot ξ η hne p) p hp (r + s / 2))))))
      =ᶠ[𝓝 t] (fun s : ℝ => Real.log (Real.sinh (r + s / 2))) := by
    have hpos : ∀ᶠ s : ℝ in 𝓝 t, 0 < r + s / 2 :=
      (isOpen_lt continuous_const (continuous_const.add (continuous_id.div_const 2))).mem_nhds ht
    filter_upwards [hpos] with s hs
    rw [dist_axisFoot_normal_geod_add_half ξ η hne p hp hs.le]
  have hcoef : Real.cosh (r + t / 2) * (1 / 2) / Real.sinh (r + t / 2) =
      Real.cosh (r + t / 2) / (2 * Real.sinh (r + t / 2)) := by ring
  rw [hcoef] at hlog
  exact hlog.congr_of_eventuallyEq heq

theorem normal_geod_eq_axisRadialFlow
    (ξ η : BoundaryH n) (hne : ξ ≠ η) (p : HUpper n) (hp : axisFoot ξ η hne p ≠ p)
    {r : ℝ} (hr : 0 < r) :
    geodFromTo (axisFoot ξ η hne p) p hp r =
      axisRadialFlow ξ η hne
        (Real.log (Real.sinh r) - Real.log (Real.sinh (dist (axisFoot ξ η hne p) p))) p := by
  let t := Real.log (Real.sinh r) - Real.log (Real.sinh (dist (axisFoot ξ η hne p) p))
  have hs := sinh_dist_axisFoot_axisRadialFlow ξ η hne t p
  rw [axisFoot_axisRadialFlow, dist_comm p (axisFoot ξ η hne p)] at hs
  have hpos := Real.sinh_pos_iff.mpr (dist_pos.mpr hp)
  have hexp : Real.exp t * Real.sinh (dist (axisFoot ξ η hne p) p) = Real.sinh r := by
    rw [show t = Real.log (Real.sinh r) - Real.log (Real.sinh (dist (axisFoot ξ η hne p) p)) from rfl,
      Real.exp_sub, Real.exp_log (Real.sinh_pos_iff.mpr hr), Real.exp_log hpos,
      div_mul_cancel₀ _ hpos.ne']
  rw [hexp] at hs
  have hd : dist (axisRadialFlow ξ η hne t p) (axisFoot ξ η hne p) = r := by
    have h := congrArg Real.arsinh hs
    simpa only [Real.arsinh_sinh] using h
  rw [axisRadialFlow_eq_normal_geod ξ η hne t p hp, hd]

end DifferentialGeometry.AxisGeometry

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open Hyperbolic (HUpper)
open ProjectiveOrthogonalGroup (PO)
open CuspCrossSections (endStabilizer)

variable {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r : ℝ}
  (D : FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ : D.centers)

local notation "P" => endStabilizer hn Γ (Set.singleton ξ.val)
local notation "πP" => Quotient.mk (@MulAction.orbitRel P (HUpper n) _ (EquivariantMap.subAction hn P))

theorem hasDerivAt_horosphereHeightHomeomorph_snd_rayTo_neg_half (p : HUpper n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (D.horosphereHeightHomeomorph hΓ ξ
      (πP (AsymptoticRays.rayTo p ξ.val (-s / 2)))).2) (1 / 2) t := by
  exact HorosphereProjection.hasDerivAt_busemann_rayTo_neg_half p ξ.val t

theorem horosphereHeightHomeomorph_rayTo_neg_half (p : HUpper n) (t : ℝ) :
    D.horosphereHeightHomeomorph hΓ ξ (πP (AsymptoticRays.rayTo p ξ.val (-t / 2))) =
      ((D.horosphereHeightHomeomorph hΓ ξ (πP p)).1, Busemann.busemann ξ.val p + t / 2) := by
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg πP (HorosphereProjection.retract_rayTo ξ.val (D.level ξ) p (-t / 2))
  · exact HorosphereProjection.busemann_rayTo_neg_half p ξ.val t

theorem horosphereGraphChart_symm_apply_rayTo_neg_half (p : HUpper n) (t : ℝ)
    (hp : AsymptoticRays.rayTo p ξ.val (-t / 2) ∈
      interior (OrbifoldThinRegions.thinRegion hn Γ r (Set.singleton ξ.val))) :
    (D.horosphereGraphChart hΓ ξ).symm
      (Quotient.mk (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))
        (AsymptoticRays.rayTo p ξ.val (-t / 2))) =
      ((D.horosphereHeightHomeomorph hΓ ξ (πP p)).1, Busemann.busemann ξ.val p + t / 2) := by
  let c := AsymptoticRays.rayTo p ξ.val (-t / 2)
  let E := D.horosphereHeightHomeomorph hΓ ξ
  let A := D.horosphereGraphChart hΓ ξ
  have hsource : E (πP c) ∈ A.source := by
    change E.symm (E (πP c)) ∈
      πP '' interior (OrbifoldThinRegions.thinRegion hn Γ r (Set.singleton ξ.val))
    rw [E.symm_apply_apply]
    exact ⟨c, hp, rfl⟩
  have he : A (E (πP c)) =
      Quotient.mk (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ)) c := by
    rw [horosphereGraphChart_apply, E.symm_apply_apply]
    rfl
  rw [← he, A.left_inv hsource]
  exact horosphereHeightHomeomorph_rayTo_neg_half D hΓ ξ p t

theorem eventually_horosphereGraphChart_symm_rayTo_neg_half (p : HUpper n)
    (hp : p ∈ interior (OrbifoldThinRegions.thinRegion hn Γ r (Set.singleton ξ.val))) :
    ∀ᶠ t : ℝ in 𝓝 0, (D.horosphereGraphChart hΓ ξ).symm
      (Quotient.mk (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))
        (AsymptoticRays.rayTo p ξ.val (-t / 2))) =
      (((D.horosphereGraphChart hΓ ξ).symm
        (Quotient.mk (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ)) p)).1,
        Busemann.busemann ξ.val p + t / 2) := by
  have hc : Continuous (fun t : ℝ => AsymptoticRays.rayTo p ξ.val (-t / 2)) :=
    (HorosphereProjection.continuous_rayTo ξ.val).comp
      (continuous_const.prodMk (continuous_id.neg.div_const 2))
  have hzero : AsymptoticRays.rayTo p ξ.val (-(0 : ℝ) / 2) = p := by
    rw [neg_zero, zero_div, AsymptoticRays.rayTo_zero]
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, AsymptoticRays.rayTo p ξ.val (-t / 2) ∈
      interior (OrbifoldThinRegions.thinRegion hn Γ r (Set.singleton ξ.val)) := by
    have h := hc.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds (hzero ▸ hp))
    exact h
  have hbase := horosphereGraphChart_symm_apply_rayTo_neg_half D hΓ ξ p 0
    (by simpa only [neg_zero, zero_div, AsymptoticRays.rayTo_zero] using hp)
  rw [neg_zero, zero_div, AsymptoticRays.rayTo_zero, add_zero] at hbase
  filter_upwards [hmem] with t ht
  rw [hbase]
  exact horosphereGraphChart_symm_apply_rayTo_neg_half D hΓ ξ p t ht

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

namespace DifferentialGeometry.AxisGeometry

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open HyperbolicConvexity (geodFromTo)

variable (m : ℕ) (Γ : Subgroup (PO (m + 1) 1))

private local instance : MulAction Γ (HUpper (m + 1)) := EquivariantMap.subAction (by omega) Γ

local notation "Q" => MulAction.orbitRel.Quotient Γ (HUpper (m + 1))
local notation "q" => Quotient.mk (MulAction.orbitRel Γ (HUpper (m + 1)))

variable (ξ η : BoundaryH (m + 1)) (hne : ξ ≠ η)
  (hpair : ∀ γ : Γ,
    (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) ξ ∈ ({ξ, η} : Set (BoundaryH (m + 1))) ∧
    (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) η ∈ ({ξ, η} : Set (BoundaryH (m + 1))))

theorem normal_geod_add_half_mem_axisOffCore (p : HUpper (m + 1)) (hp : axisFoot ξ η hne p ≠ p)
    {t : ℝ} (ht : 0 < dist (axisFoot ξ η hne p) p + t / 2) :
    q (geodFromTo (axisFoot ξ η hne p) p hp (dist (axisFoot ξ η hne p) p + t / 2)) ∈
      axisOffCore m Γ ξ η hne hpair := by
  intro hmem
  have hz := (quotientAxisDistance_eq_zero_iff_mem_image_axis m Γ ξ η hne hpair _).mpr hmem
  rw [quotientAxisDistance_mk, dist_axisFoot_normal_geod_add_half ξ η hne p hp ht.le] at hz
  exact ht.ne' hz

variable [DiscreteTopology Γ] [IsCancelSMul Γ (HUpper (m + 1))]

theorem axisProductDiffeomorph_snd_normal_geod_add_half
    (p : HUpper (m + 1)) (hp : axisFoot ξ η hne p ≠ p)
    {t : ℝ} (ht : 0 < dist (axisFoot ξ η hne p) p + t / 2) :
    (axisProductDiffeomorph m Γ ξ η hne hpair
      ⟨q (geodFromTo (axisFoot ξ η hne p) p hp (dist (axisFoot ξ η hne p) p + t / 2)),
        normal_geod_add_half_mem_axisOffCore m Γ ξ η hne hpair p hp ht⟩).2 =
      Real.log (Real.sinh (dist (axisFoot ξ η hne p) p + t / 2)) := by
  rw [axisProductDiffeomorph_snd]
  change Real.log (Real.sinh (dist _ (axisFoot ξ η hne _))) = _
  rw [dist_axisFoot_normal_geod_add_half ξ η hne p hp ht.le]

theorem axisProductDiffeomorph_axisOffCoreFlow
    (z : axisOffCore m Γ ξ η hne hpair) (t : ℝ) :
    axisProductDiffeomorph m Γ ξ η hne hpair (axisOffCoreFlow m Γ ξ η hne hpair t z) =
      ((axisProductDiffeomorph m Γ ξ η hne hpair z).1,
        (axisProductDiffeomorph m Γ ξ η hne hpair z).2 + t) := by
  apply Prod.ext
  · apply Subtype.ext
    rw [axisProductDiffeomorph_fst_val, axisProductDiffeomorph_fst_val,
      axisLogSinhRadius_axisOffCoreFlow]
    change quotientAxisRadialFlow m Γ ξ η hne hpair
      (-(axisLogSinhRadius m Γ ξ η hne hpair z + t))
      (quotientAxisRadialFlow m Γ ξ η hne hpair t z.val) = _
    rw [quotientAxisRadialFlow_add]
    congr 1
    ring
  · exact axisLogSinhRadius_axisOffCoreFlow m Γ ξ η hne hpair t z

theorem axisProductDiffeomorph_normal_geod_add_half
    (p : HUpper (m + 1)) (hp : axisFoot ξ η hne p ≠ p)
    (z : axisOffCore m Γ ξ η hne hpair) (hz : z.val = q p)
    {t : ℝ} (ht : 0 < dist (axisFoot ξ η hne p) p + t / 2) :
    axisProductDiffeomorph m Γ ξ η hne hpair
      ⟨q (geodFromTo (axisFoot ξ η hne p) p hp (dist (axisFoot ξ η hne p) p + t / 2)),
        normal_geod_add_half_mem_axisOffCore m Γ ξ η hne hpair p hp ht⟩ =
      ((axisProductDiffeomorph m Γ ξ η hne hpair z).1,
        Real.log (Real.sinh (dist (axisFoot ξ η hne p) p + t / 2))) := by
  let a := Real.log (Real.sinh (dist (axisFoot ξ η hne p) p + t / 2)) -
    Real.log (Real.sinh (dist (axisFoot ξ η hne p) p))
  have he : (⟨q (geodFromTo (axisFoot ξ η hne p) p hp (dist (axisFoot ξ η hne p) p + t / 2)),
      normal_geod_add_half_mem_axisOffCore m Γ ξ η hne hpair p hp ht⟩ : axisOffCore m Γ ξ η hne hpair) =
      axisOffCoreFlow m Γ ξ η hne hpair a z := by
    apply Subtype.ext
    change q (geodFromTo (axisFoot ξ η hne p) p hp
      (dist (axisFoot ξ η hne p) p + t / 2)) =
      quotientAxisRadialFlow m Γ ξ η hne hpair a z.val
    rw [hz, quotientAxisRadialFlow_mk, normal_geod_eq_axisRadialFlow ξ η hne p hp ht]
  rw [he, axisProductDiffeomorph_axisOffCoreFlow]
  apply Prod.ext
  · rfl
  change (axisProductDiffeomorph m Γ ξ η hne hpair z).2 + a = _
  rw [axisProductDiffeomorph_snd]
  change Real.log (Real.sinh (quotientAxisDistance m Γ ξ η hne hpair z.val)) + a = _
  rw [hz, quotientAxisDistance_mk, dist_comm p (axisFoot ξ η hne p)]
  dsimp only [a]
  ring

end DifferentialGeometry.AxisGeometry

namespace DifferentialGeometry.OrbifoldThinRegions

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open CuspCrossSections (endStabilizer)
open AxisGeometry (quotientAxisDistance quotientAxisRadialFlow axisProductDiffeomorph axisOffCore)

variable (m : ℕ) (Γ : Subgroup (PO (m + 1) 1)) [DiscreteTopology Γ]
  (ξ η : BoundaryH (m + 1)) (hne : ξ ≠ η)

local notation "hn" => Nat.succ_le_succ (Nat.zero_le m)
local notation "P" => endStabilizer hn Γ (Set.insert ξ (Set.singleton η))

omit [DiscreteTopology Γ] in
private theorem radialStabilizer_pair (γ : P) :
    (poBoundaryMulAction hn).smul (γ : PO (m + 1) 1) ξ ∈ ({ξ, η} : Set (BoundaryH (m + 1))) ∧
      (poBoundaryMulAction hn).smul (γ : PO (m + 1) 1) η ∈ ({ξ, η} : Set (BoundaryH (m + 1))) := by
  have he := (ElementaryEnds.mem_setStabilizer hn {ξ, η} γ).mp γ.property.2
  exact ⟨he ▸ Set.mem_image_of_mem _ (by simp), he ▸ Set.mem_image_of_mem _ (by simp)⟩

local notation "hP" => radialStabilizer_pair m Γ ξ η

private local instance : MulAction Γ (HUpper (m + 1)) := EquivariantMap.subAction hn Γ
private local instance : MulAction P (HUpper (m + 1)) := EquivariantMap.subAction hn P
private local instance : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp
  ((isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ)).mono
    (show P ≤ Γ from inf_le_left))
private local instance : ContinuousConstSMul Γ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩
private local instance : ContinuousConstSMul P (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩
private local instance : ProperlyDiscontinuousSMul Γ (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction hn Γ
    (isDiscrete_iff_discreteTopology.mpr inferInstance)
private local instance : ProperlyDiscontinuousSMul P (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction hn P
    ((isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ)).mono
      (show P ≤ Γ from inf_le_left))

variable [IsCancelSMul Γ (HUpper (m + 1))]

private local instance : IsCancelSMul P (HUpper (m + 1)) :=
  EquivariantMap.isCancelSMul_subAction hn (show P ≤ Γ from inf_le_left)

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "Q" => MulAction.orbitRel.Quotient Γ (HUpper (m + 1))
local notation "QP" => MulAction.orbitRel.Quotient P (HUpper (m + 1))
local notation "π" => Quotient.mk (MulAction.orbitRel Γ (HUpper (m + 1)))
local notation "πP" => Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))
local notation "R" => quotientAxisDistance m P ξ η hne hP
local notation "S" => {z : QP // R z = Real.arsinh 1}
local notation "O" => axisOffCore m P ξ η hne hP
local notation "K" => 𝓘(ℝ, Fin m → ℝ)
local notation "J" => ModelWithCorners.prod K 𝓘(ℝ, ℝ)
local notation "j" => EquivariantMap.quotientInclusion («P» := P) (Γ := Γ) hn inf_le_left
local notation "d" => axisProductDiffeomorph m P ξ η hne hP
local notation "a" => Function.uncurry (axialGraphAmbientPoint m Γ ξ η hne)

private local instance : ChartedSpace (Fin m → ℝ) S :=
  AxisGeometry.axisSectionChartedSpace m P ξ η hne hP

private local instance : IsManifold K ∞ S := AxisGeometry.axisSection_isManifold m P ξ η hne hP

theorem eventually_axialGraphPartialDiffeomorph_symm_normal_geod_add_half
    (hm : 1 ≤ m) (r : ℝ) (p : HUpper (m + 1))
    (hp : AxisGeometry.axisFoot ξ η hne p ≠ p)
    (hthin : p ∈ interior (thinRegion hn Γ r {ξ, η})) :
    let r₀ := dist (AxisGeometry.axisFoot ξ η hne p) p
    let c := fun t : ℝ => HyperbolicConvexity.geodFromTo (AxisGeometry.axisFoot ξ η hne p) p hp (r₀ + t / 2)
    let A := axialGraphPartialDiffeomorph m Γ ξ η hne hm r
    ∀ᶠ t : ℝ in 𝓝 0, A.symm (π (c t)) =
      ((A.symm (π p)).1, Real.log (Real.sinh (r₀ + t / 2))) := by
  let r₀ := dist (AxisGeometry.axisFoot ξ η hne p) p
  let c := fun t : ℝ => HyperbolicConvexity.geodFromTo (AxisGeometry.axisFoot ξ η hne p) p hp (r₀ + t / 2)
  let A := axialGraphPartialDiffeomorph m Γ ξ η hne hm r
  have hzero : c 0 = p := by
    dsimp only [c, r₀]
    rw [zero_div, add_zero, HyperbolicConvexity.geodFromTo_dist]
  have hc : Continuous c :=
    (HyperbolicConvexity.continuous_geodFromTo hp).comp
      (continuous_const.add (continuous_id.div_const 2))
  have hr : 0 < r₀ := dist_pos.mpr hp
  have hrad : ∀ᶠ t : ℝ in 𝓝 0, 0 < r₀ + t / 2 :=
    (isOpen_lt continuous_const (continuous_const.add (continuous_id.div_const 2))).mem_nhds
      (by change 0 < r₀ + (0 : ℝ) / 2; simpa only [zero_div, add_zero] using hr)
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, c t ∈ interior (thinRegion hn Γ r {ξ, η}) :=
    hc.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds (hzero ▸ hthin))
  have hpO : πP p ∈ O := by
    intro haxis
    have hz := (AxisGeometry.quotientAxisDistance_eq_zero_iff_mem_image_axis m P ξ η hne hP (πP p)).mpr haxis
    exact hp ((dist_eq_zero.mp hz).symm)
  let z : O := ⟨πP p, hpO⟩
  have hoff : p ∉ AxisGeometry.axis ξ η := fun haxis => hp (AxisGeometry.axisFoot_eq_self ξ η hne haxis)
  have hbase : A.symm (π p) = d z :=
    axialGraphPartialDiffeomorph_symm_apply_mk m Γ ξ η hne hm r p hoff hthin
  filter_upwards [hrad, hmem] with t ht hct
  have hcO := AxisGeometry.normal_geod_add_half_mem_axisOffCore m P ξ η hne hP p hp ht
  have hcoff : c t ∉ AxisGeometry.axis ξ η := fun haxis => hcO ⟨c t, haxis, rfl⟩
  have hcur : A.symm (π (c t)) = d ⟨πP (c t), hcO⟩ :=
    axialGraphPartialDiffeomorph_symm_apply_mk m Γ ξ η hne hm r (c t) hcoff hct
  change A.symm (π (c t)) = ((A.symm (π p)).1, Real.log (Real.sinh (r₀ + t / 2)))
  rw [hcur, hbase]
  exact AxisGeometry.axisProductDiffeomorph_normal_geod_add_half m P ξ η hne hP p hp z rfl ht

end DifferentialGeometry.OrbifoldThinRegions
