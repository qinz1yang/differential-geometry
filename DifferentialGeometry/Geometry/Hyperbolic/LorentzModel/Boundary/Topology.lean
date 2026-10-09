/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.BoundaryTopology

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.HyperbolicAction
open DifferentialGeometry.HyperbolicFaithful
open DifferentialGeometry.HyperbolicBoundary
open Matrix Filter

variable {n : ℕ}

instance : TopologicalSpace (BoundaryH n) := TopologicalSpace.induced BoundaryH.val inferInstance

theorem isEmbedding_val : Topology.IsEmbedding (BoundaryH.val : BoundaryH n → LorVec n) :=
  ⟨⟨rfl⟩, fun _ _ h => BoundaryH.ext h⟩

instance : T2Space (BoundaryH n) := isEmbedding_val.t2Space

instance : SecondCountableTopology (BoundaryH n) := isEmbedding_val.secondCountableTopology

noncomputable def spatial (v : BoundaryH n) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm fun i => v.val (Sum.inl i)

theorem spatial_apply (v : BoundaryH n) (i : Fin n) :
    (spatial v : EuclideanSpace ℝ (Fin n)) i = v.val (Sum.inl i) := rfl

theorem sdot_self_of_boundary (v : BoundaryH n) : sdot v.val v.val = 1 := by
  have h0 := v.is_null
  have h1 : lorB v.val v.val = sdot v.val v.val - 1 := by
    simp only [lorB]
    rw [v.tc_eq]
    ring
  linarith

theorem norm_spatial (v : BoundaryH n) : ‖spatial v‖ = 1 := by
  have hsum : (∑ i : Fin n, ‖(spatial v : EuclideanSpace ℝ (Fin n)) i‖ ^ 2) = 1 := by
    have h1 : ∀ i : Fin n, ‖(spatial v : EuclideanSpace ℝ (Fin n)) i‖ ^ 2
        = v.val (Sum.inl i) * v.val (Sum.inl i) := by
      intro i
      rw [spatial_apply, Real.norm_eq_abs, sq_abs, pow_two]
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    exact sdot_self_of_boundary v
  rw [PiLp.norm_eq_of_L2, hsum, Real.sqrt_one]

noncomputable def toSphere (v : BoundaryH n) : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨spatial v, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_spatial v⟩

noncomputable def fromSphere (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    BoundaryH n := by
  refine ⟨Sum.elim (fun i => (u.val : EuclideanSpace ℝ (Fin n)) i) (fun _ => (1 : ℝ)), ?_, rfl⟩
  have hu : ‖u.val‖ = 1 := by
    have h := u.prop
    rwa [Metric.mem_sphere, dist_zero_right] at h
  have hsum : (∑ i : Fin n, ‖(u.val : EuclideanSpace ℝ (Fin n)) i‖ ^ 2) = 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hu
    rw [PiLp.norm_eq_of_L2, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)] at h
    simpa using h
  have h2 : ∀ i : Fin n, (u.val : EuclideanSpace ℝ (Fin n)) i * u.val i = ‖u.val i‖ ^ 2 := by
    intro i
    rw [Real.norm_eq_abs, sq_abs, pow_two]
  have hsd : sdot (Sum.elim (fun i => (u.val : EuclideanSpace ℝ (Fin n)) i) (fun _ => (1 : ℝ)))
      (Sum.elim (fun i => (u.val : EuclideanSpace ℝ (Fin n)) i) (fun _ => (1 : ℝ))) = 1 := by
    change (∑ i : Fin n, (u.val : EuclideanSpace ℝ (Fin n)) i * u.val i) = 1
    rw [Finset.sum_congr rfl (fun i _ => h2 i)]
    exact hsum
  have htc : tc (Sum.elim (fun i => (u.val : EuclideanSpace ℝ (Fin n)) i) (fun _ => (1 : ℝ)))
      = 1 := rfl
  change lorB _ _ = 0
  simp only [lorB]
  rw [hsd, htc]
  norm_num

theorem continuous_spatial :
    Continuous (spatial : BoundaryH n → EuclideanSpace ℝ (Fin n)) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi_iff.mpr fun i =>
    (continuous_apply (Sum.inl i)).comp continuous_induced_dom)

theorem continuous_toSphere :
    Continuous (toSphere : BoundaryH n → Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  continuous_spatial.subtype_mk _

theorem continuous_fromSphere :
    Continuous (fromSphere : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → BoundaryH n) := by
  apply continuous_induced_rng.mpr
  rw [continuous_pi_iff]
  intro a
  rcases a with i | k
  · exact (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val
  · exact continuous_const

noncomputable def sphereHomeomorph :
    BoundaryH n ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 where
  toFun := toSphere
  invFun := fromSphere
  left_inv v := by
    apply BoundaryH.ext
    funext a
    rcases a with i | k
    · rfl
    · have hk0 : k = 0 := Subsingleton.elim k 0
      subst hk0
      change (1 : ℝ) = v.val (Sum.inr 0)
      exact v.tc_eq.symm
  right_inv u := by
    apply Subtype.ext
    change spatial (fromSphere u) = u.val
    apply (WithLp.equiv 2 (Fin n → ℝ)).injective
    funext i
    rfl
  continuous_toFun := continuous_toSphere
  continuous_invFun := continuous_fromSphere

instance compactSpaceBoundaryH : CompactSpace (BoundaryH n) := by
  have : CompactSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  exact sphereHomeomorph.symm.compactSpace

theorem continuous_actB (A : LorGrp n) : Continuous (actB A : BoundaryH n → BoundaryH n) := by
  apply continuous_induced_rng.mpr
  have hmv : Continuous fun v : BoundaryH n => matOf A *ᵥ v.val :=
    Continuous.matrix_mulVec continuous_const continuous_induced_dom
  have htc : Continuous fun v : BoundaryH n => tc (matOf A *ᵥ v.val) :=
    (continuous_apply (Sum.inr 0)).comp hmv
  have hne : ∀ v : BoundaryH n, tc (matOf A *ᵥ v.val) ≠ 0 :=
    fun v => tc_matOf_mulVec_ne_zero A v
  exact (htc.inv₀ hne).smul hmv

noncomputable def actBHomeomorph (A : LorGrp n) : BoundaryH n ≃ₜ BoundaryH n where
  toEquiv := MulAction.toPerm A
  continuous_toFun := continuous_actB A
  continuous_invFun := continuous_actB A⁻¹

theorem po_boundary_homeomorph (hn : 1 ≤ n) (g : PO n 1) :
    ∃ φ : BoundaryH n ≃ₜ BoundaryH n,
      ∀ v : BoundaryH n, φ v = (poBoundaryMulAction hn).smul g v := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) g
  exact ⟨actBHomeomorph A, fun v => (po_boundary_smul_mk hn A v).symm⟩

section Convergence

def ConvergesToBoundary (x : ℕ → HUpper n) (ξ : BoundaryH n) : Prop :=
  Filter.Tendsto (fun m => (tc (x m).val)⁻¹ • (x m).val) Filter.atTop (nhds ξ.val)

theorem convergesToBoundary_smul (hn : 1 ≤ n) (g : PO n 1) {x : ℕ → HUpper n}
    {ξ : BoundaryH n} (hx : ConvergesToBoundary x ξ) :
    ConvergesToBoundary (fun m => (poMulAction hn).smul g (x m))
      ((poBoundaryMulAction hn).smul g ξ) := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) g
  have key : ∀ m : ℕ,
      (tc (((poMulAction hn).smul ⟦A⟧ (x m)).val))⁻¹ • ((poMulAction hn).smul ⟦A⟧ (x m)).val
        = boundaryRep (matOf A *ᵥ ((tc (x m).val)⁻¹ • (x m).val)) := by
    intro m
    set y := x m with hydef
    set w := matOf A *ᵥ y.val with hwdef
    have htcy : 0 < tc y.val := y.future
    have htcw : tc w ≠ 0 := matOf_mulVec_ne_tc A y.is_unit
    change (tc (upperize w))⁻¹ • (upperize w) = boundaryRep (matOf A *ᵥ ((tc y.val)⁻¹ • y.val))
    rw [Matrix.mulVec_smul]
    rw [boundaryRep_smul _ (inv_ne_zero (ne_of_gt htcy))]
    change boundaryRep (upperize w) = boundaryRep w
    unfold upperize
    by_cases hw : 0 < tc w
    · rw [ite_eq_left hw]
    · rw [ite_eq_right hw]
      exact boundaryRep_neg w
  have hlin : Continuous fun u : LorVec n => matOf A *ᵥ u :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hAt : ContinuousAt (fun u : LorVec n => boundaryRep (matOf A *ᵥ u)) ξ.val := by
    have h1 : ContinuousAt (fun u : LorVec n => tc (matOf A *ᵥ u)) ξ.val :=
      ((continuous_apply (Sum.inr 0)).comp hlin).continuousAt
    have h2 : tc (matOf A *ᵥ ξ.val) ≠ 0 := tc_matOf_mulVec_ne_zero A ξ
    exact (h1.inv₀ h2).smul hlin.continuousAt
  change Filter.Tendsto (fun m => (tc (((poMulAction hn).smul ⟦A⟧ (x m)).val))⁻¹ •
      (((poMulAction hn).smul ⟦A⟧ (x m)).val)) Filter.atTop
    (nhds (((poBoundaryMulAction hn).smul ⟦A⟧ ξ).val))
  exact (hAt.tendsto.comp hx).congr' (Filter.Eventually.of_forall fun m => (key m).symm)

end Convergence

section GeodesicRays

noncomputable def spatialEmbed (u : EuclideanSpace ℝ (Fin n)) : LorVec n :=
  Sum.elim (fun i => u i) (fun _ => (0 : ℝ))

theorem spatialEmbed_inl (u : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    spatialEmbed u (Sum.inl i) = u i := rfl

theorem spatialEmbed_inr (u : EuclideanSpace ℝ (Fin n)) (k : Fin 1) :
    spatialEmbed u (Sum.inr k) = 0 := rfl

theorem tc_spatialEmbed (u : EuclideanSpace ℝ (Fin n)) : tc (spatialEmbed u) = 0 := rfl

theorem sdot_spatialEmbed (u v : EuclideanSpace ℝ (Fin n)) :
    sdot (spatialEmbed u) (spatialEmbed v) = ∑ i : Fin n, u i * v i := rfl

theorem sdot_eTime_spatialEmbed (u : EuclideanSpace ℝ (Fin n)) :
    sdot (eTime : LorVec n) (spatialEmbed u) = 0 := by
  change (∑ i : Fin n, (eTime : LorVec n) (Sum.inl i) * (spatialEmbed u) (Sum.inl i)) = 0
  simp [eTime_apply_inl]

noncomputable def geodesicRay (ξ : BoundaryH n) (t : ℝ) : HUpper n where
  val := Real.cosh t • eTime + Real.sinh t • spatialEmbed (spatial ξ)
  is_unit := by
    set u := spatialEmbed (spatial ξ) with hudef
    have hu1 : lorB u u = 1 := by
      rw [hudef]
      have hsd : sdot (spatialEmbed (spatial ξ)) (spatialEmbed (spatial ξ)) = 1 := by
        rw [sdot_spatialEmbed]
        have h2 : ∀ i : Fin n, (spatial ξ : EuclideanSpace ℝ (Fin n)) i * (spatial ξ) i
            = ξ.val (Sum.inl i) * ξ.val (Sum.inl i) := fun i => by rw [spatial_apply]
        rw [Finset.sum_congr rfl (fun i _ => h2 i)]
        exact sdot_self_of_boundary ξ
      change sdot (spatialEmbed (spatial ξ)) (spatialEmbed (spatial ξ))
          - tc (spatialEmbed (spatial ξ)) * tc (spatialEmbed (spatial ξ)) = 1
      rw [tc_spatialEmbed, hsd]
      norm_num
    have hAA : lorB (Real.cosh t • (eTime : LorVec n)) (Real.cosh t • (eTime : LorVec n))
        = - (Real.cosh t * Real.cosh t) := by
      rw [lorB_smul_left, lorB_smul_right, lorB_eTime]
      ring
    have hAB : lorB (Real.cosh t • (eTime : LorVec n)) (Real.sinh t • u) = 0 := by
      rw [lorB_smul_left, lorB_smul_right]
      have hx : lorB (eTime : LorVec n) u = 0 := by
        rw [hudef]
        change sdot (eTime : LorVec n) (spatialEmbed (spatial ξ))
            - tc (eTime : LorVec n) * tc (spatialEmbed (spatial ξ)) = 0
        rw [sdot_eTime_spatialEmbed, tc_eTime, tc_spatialEmbed]
        norm_num
      rw [hx, mul_zero, mul_zero]
    have hBA : lorB (Real.sinh t • u) (Real.cosh t • (eTime : LorVec n)) = 0 := by
      rw [lorB_comm]
      exact hAB
    have hBB : lorB (Real.sinh t • u) (Real.sinh t • u) = Real.sinh t * Real.sinh t := by
      rw [lorB_smul_left, lorB_smul_right, hu1, mul_one]
    have hmain : lorB (Real.cosh t • (eTime : LorVec n) + Real.sinh t • u)
        (Real.cosh t • (eTime : LorVec n) + Real.sinh t • u) = Real.sinh t ^ 2 - Real.cosh t ^ 2 := by
      rw [lorB_add_left, lorB_add_right, lorB_add_right, hAA, hAB, hBA, hBB]
      ring
    rw [hmain]
    have hcosh := Real.cosh_sq_sub_sinh_sq t
    linarith
  future := by
    show 0 < tc (Real.cosh t • eTime + Real.sinh t • spatialEmbed (spatial ξ))
    rw [tc_add, tc_smul, tc_smul, tc_eTime, tc_spatialEmbed, mul_one, mul_zero, add_zero]
    exact Real.cosh_pos t

theorem geodesicRay_radial (ξ : BoundaryH n) (t : ℝ) :
    (tc ((geodesicRay ξ t).val))⁻¹ • ((geodesicRay ξ t).val)
      = eTime + (Real.sinh t / Real.cosh t) • spatialEmbed (spatial ξ) := by
  have htc : tc ((geodesicRay ξ t).val) = Real.cosh t := by
    change tc (Real.cosh t • eTime + Real.sinh t • spatialEmbed (spatial ξ)) = Real.cosh t
    rw [tc_add, tc_smul, tc_smul, tc_eTime, tc_spatialEmbed, mul_one, mul_zero, add_zero]
  rw [htc]
  change (Real.cosh t)⁻¹ • (Real.cosh t • eTime + Real.sinh t • spatialEmbed (spatial ξ)) = _
  rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ (ne_of_gt (Real.cosh_pos t)),
    one_smul]
  congr 1
  rw [div_eq_mul_inv]
  congr 1
  exact mul_comm _ _

theorem tendsto_geodesicRay (ξ : BoundaryH n) :
    ConvergesToBoundary (fun m => geodesicRay ξ (m : ℝ)) ξ := by
  have hval : ξ.val = eTime + spatialEmbed (spatial ξ) := by
    funext a
    rcases a with i | k
    · rw [Pi.add_apply, eTime_apply_inl, spatialEmbed_inl, spatial_apply, zero_add]
    · have hk0 : k = 0 := Subsingleton.elim k 0
      subst hk0
      rw [Pi.add_apply, eTime_apply_inr, spatialEmbed_inr, add_zero]
      exact ξ.tc_eq
  have hexp : Filter.Tendsto (fun m : ℕ => Real.exp (-2 * (m : ℝ))) Filter.atTop (nhds 0) := by
    have h1 : ∀ m : ℕ, Real.exp (-2 * (m : ℝ)) = (Real.exp (-2)) ^ m := by
      intro m
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hr1 : Real.exp (-2) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_strictMono (by norm_num)
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-2)).le hr1
    exact h2.congr' (Filter.Eventually.of_forall fun m => (h1 m).symm)
  have hlim : Filter.Tendsto (fun m : ℕ => Real.sinh (m : ℝ) / Real.cosh (m : ℝ))
      Filter.atTop (nhds 1) := by
    have h2 : Filter.Tendsto (fun m : ℕ => (1 - Real.exp (-2 * (m : ℝ))) /
        (1 + Real.exp (-2 * (m : ℝ)))) Filter.atTop (nhds ((1 - 0) / (1 + 0))) :=
      (tendsto_const_nhds.sub hexp).div (tendsto_const_nhds.add hexp) (by norm_num)
    have h3 : ∀ m : ℕ, Real.sinh (m : ℝ) / Real.cosh (m : ℝ)
        = (1 - Real.exp (-2 * (m : ℝ))) / (1 + Real.exp (-2 * (m : ℝ))) := by
      intro m
      have he : Real.exp (m : ℝ) ≠ 0 := (Real.exp_pos _).ne'
      have hee : Real.exp (m : ℝ) * Real.exp (m : ℝ) ≠ 0 := mul_ne_zero he he
      have hrr : Real.exp (-2 * (m : ℝ)) = (Real.exp (m : ℝ) * Real.exp (m : ℝ))⁻¹ := by
        rw [show (-2 : ℝ) * (m : ℝ) = -((m : ℝ) + (m : ℝ)) from by ring, Real.exp_neg,
          Real.exp_add]
      rw [Real.sinh_eq, Real.cosh_eq, hrr, Real.exp_neg]
      field_simp
    have h4 : ((1 : ℝ) - 0) / (1 + 0) = 1 := by norm_num
    rw [h4] at h2
    exact h2.congr' (Filter.Eventually.of_forall fun m => (h3 m).symm)
  have hlim2 : Filter.Tendsto (fun m : ℕ => eTime +
      (Real.sinh (m : ℝ) / Real.cosh (m : ℝ)) • spatialEmbed (spatial ξ))
      Filter.atTop (nhds (eTime + (1 : ℝ) • spatialEmbed (spatial ξ))) :=
    tendsto_const_nhds.add (hlim.smul tendsto_const_nhds)
  rw [one_smul, ← hval] at hlim2
  unfold ConvergesToBoundary
  exact hlim2.congr' (Filter.Eventually.of_forall fun m => (geodesicRay_radial ξ m).symm)

end GeodesicRays

end DifferentialGeometry.BoundaryTopology
