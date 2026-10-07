import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.TubeLevel
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.GeodesicSegment
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.UpperSheet
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.RadialQuotient

noncomputable section

namespace DifferentialGeometry.AxisGeometry

open Hyperbolic (HUpper LorVec lorB tc)
open HyperbolicBoundary (BoundaryH)
open AsymptoticRays (rayTo dirTo)

variable {n : ℕ}

private theorem exists_isometryEquiv_image_axis
    (ξ η : BoundaryH n) (hne : ξ ≠ η) :
    ∃ (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
      (A : HUpper n ≃ᵢ Hyperboloid (EuclideanSpace ℝ (Fin n))),
      A '' axis ξ η = Set.range (Hyperboloid.geodesicLine Hyperboloid.origin (0, u)
        (by simp [lorentzForm_apply, hu]) (by simp [lorentzForm_apply])) := by
  let b := ElementaryGroups.boundaryPairPoint ξ η hne
  let J := Hyperboloid.hUpperIsometryEquiv n
  let v : ℝ × EuclideanSpace ℝ (Fin n) :=
    (tc (dirTo b ξ), WithLp.toLp 2 (fun j => dirTo b ξ (Sum.inl j)))
  have hv : lorentzForm (EuclideanSpace ℝ (Fin n)) v v = 1 := by
    have hd := AsymptoticRays.lorB_dirTo_self b ξ
    simpa only [v, lorentzForm_apply, PiLp.inner_apply, Real.inner_apply,
      Hyperbolic.lorB, Hyperbolic.sdot, mul_comm] using hd
  have ho : lorentzForm (EuclideanSpace ℝ (Fin n)) ((J b).time, (J b).space) v = 0 := by
    have hd := AsymptoticRays.lorB_dirTo_left b ξ
    rw [Hyperbolic.lorB_comm] at hd
    simpa only [v, J, lorentzForm_apply, Hyperboloid.hUpperIsometryEquiv_time,
      PiLp.inner_apply, Real.inner_apply,
      Hyperboloid.hUpperIsometryEquiv_space_apply, Hyperbolic.lorB, Hyperbolic.sdot,
      Hyperbolic.tc, mul_comm] using hd
  have hJray (t : ℝ) : J (rayTo b ξ t) = Hyperboloid.geodesicLine (J b) v hv ho t := by
    apply Hyperboloid.ext
    apply PiLp.ext
    intro j
    rfl
  let B := (Hyperboloid.boost (J b)).symm
  let w := Hyperboloid.lorentzExtension B v
  have hb : B (J b) = Hyperboloid.origin := by
    simpa only [Hyperboloid.boost_origin] using (Hyperboloid.boost (J b)).symm_apply_apply Hyperboloid.origin
  have hw : lorentzForm (EuclideanSpace ℝ (Fin n)) w w = 1 := by
    dsimp only [w]
    rw [(Hyperboloid.lorentzExtension B).map_app]
    exact hv
  have hwo : lorentzForm (EuclideanSpace ℝ (Fin n)) ((B (J b)).time, (B (J b)).space) w = 0 := by
    rw [← Hyperboloid.lorentzExtension_apply B (J b)]
    change lorentzForm (EuclideanSpace ℝ (Fin n))
      (Hyperboloid.lorentzExtension B ((J b).time, (J b).space))
      (Hyperboloid.lorentzExtension B v) = 0
    rw [(Hyperboloid.lorentzExtension B).map_app]
    exact ho
  have ht : w.1 = 0 := by
    rw [hb] at hwo
    simpa only [lorentzForm_apply, Hyperboloid.origin_time, Hyperboloid.origin_space,
      inner_zero_left, one_mul, zero_sub, neg_eq_zero] using hwo
  have hu : ‖w.2‖ = 1 := by
    rw [lorentzForm_apply, ht, zero_mul, sub_zero, real_inner_self_eq_norm_sq] at hw
    nlinarith [norm_nonneg w.2]
  let d := Hyperboloid.geodesicLine (Hyperboloid.origin : Hyperboloid (EuclideanSpace ℝ (Fin n)))
    (0, w.2) (by simp [lorentzForm_apply, hu]) (by simp [lorentzForm_apply])
  let A := J.trans B
  have hline (t : ℝ) : A (rayTo b ξ t) = d t := by
    change B (J (rayTo b ξ t)) = d t
    rw [hJray]
    apply Hyperboloid.ext
    have hh := congrArg Hyperboloid.space (Hyperboloid.isometryEquiv_geodesicLine B (J b) v hv ho t)
    simpa only [d, Hyperboloid.geodesicLine_space, hb, Hyperboloid.origin_space,
      smul_zero, zero_add] using hh
  refine ⟨w.2, hu, A, ?_⟩
  rw [axis_eq_range_rayTo ξ η hne]
  ext y
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, (hline t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨rayTo b ξ t, ⟨t, rfl⟩, hline t⟩

theorem isPathConnected_setOf_dist_axisFoot_eq
    (hdim : 3 ≤ n) (ξ η : BoundaryH n) (hne : ξ ≠ η) (R : ℝ) (hR : 0 ≤ R) :
    IsPathConnected {x : HUpper n | dist x (axisFoot ξ η hne x) = R} := by
  obtain ⟨u, hu, A, hA⟩ := exists_isometryEquiv_image_axis ξ η hne
  have hfoot (x : HUpper n) : A (axisFoot ξ η hne x) = Hyperboloid.lineProjection u hu (A x) := by
    apply Hyperboloid.eq_lineProjection_of_dist_le u hu (A x)
    · rw [← hA]
      exact Set.mem_image_of_mem A (axisFoot_mem ξ η hne x)
    · have hp := Hyperboloid.lineProjection_mem_range u hu (A x)
      rw [← hA] at hp
      obtain ⟨z, hz, heq⟩ := hp
      have hd := dist_axisFoot_le ξ η hne x z hz
      rw [← A.dist_eq x (axisFoot ξ η hne x), ← A.dist_eq x z, heq] at hd
      exact hd
  have himage : A.symm '' {x : Hyperboloid (EuclideanSpace ℝ (Fin n)) |
      dist x (Hyperboloid.lineProjection u hu x) = R} =
      {x : HUpper n | dist x (axisFoot ξ η hne x) = R} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change dist (A.symm z) (axisFoot ξ η hne (A.symm z)) = R
      rw [← A.dist_eq, hfoot, A.apply_symm_apply]
      exact hz
    · intro hx
      refine ⟨A x, ?_, A.symm_apply_apply x⟩
      change dist (A x) (Hyperboloid.lineProjection u hu (A x)) = R
      rw [← hfoot, A.dist_eq]
      exact hx
  rw [← himage]
  exact (Hyperboloid.isPathConnected_setOf_dist_lineProjection_eq_of_finrank
    (by simpa using hdim) u hu R hR).image A.symm.continuous

section Quotient

open ProjectiveOrthogonalGroup (PO)
open HyperbolicBoundary (poBoundaryMulAction)

variable (m : ℕ) (Γ : Subgroup (PO (m + 1) 1))

private local instance : MulAction Γ (HUpper (m + 1)) := EquivariantMap.subAction (by omega) Γ

local notation "Q" => MulAction.orbitRel.Quotient Γ (HUpper (m + 1))
local notation "q" => Quotient.mk (MulAction.orbitRel Γ (HUpper (m + 1)))

theorem isPathConnected_setOf_quotientAxisDistance_eq
    (hdim : 2 ≤ m) (ξ η : BoundaryH (m + 1)) (hne : ξ ≠ η)
    (hpair : ∀ γ : Γ,
      (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) ξ ∈
        ({ξ, η} : Set (BoundaryH (m + 1))) ∧
      (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) η ∈
        ({ξ, η} : Set (BoundaryH (m + 1))))
    (R : ℝ) (hR : 0 ≤ R) :
    IsPathConnected {z : Q | quotientAxisDistance m Γ ξ η hne hpair z = R} := by
  have himage : q '' {x : HUpper (m + 1) | dist x (axisFoot ξ η hne x) = R} =
      {z : Q | quotientAxisDistance m Γ ξ η hne hpair z = R} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · induction z using Quotient.inductionOn with
      | _ x => exact fun hx => ⟨x, hx, rfl⟩
  rw [← himage]
  exact (isPathConnected_setOf_dist_axisFoot_eq (by omega) ξ η hne R hR).image continuous_quotient_mk'

end Quotient

end DifferentialGeometry.AxisGeometry
