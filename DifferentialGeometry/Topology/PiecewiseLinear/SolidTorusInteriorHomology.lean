/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Integral
import DifferentialGeometry.Topology.PiecewiseLinear.NontrivialKernelInSolidTorus

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem IsTopologicalSolidTorus.integralSingularHomologyMap_interior_injective
    {S : Set E3} (hS : IsTopologicalSolidTorus S) :
    Function.Injective (integralSingularHomologyMap 1
      (⟨Set.inclusion (interior_subset : interior S ⊆ S),
        continuous_inclusion interior_subset⟩ : C(interior S, S))) := by
  obtain ⟨φ⟩ := hS
  let i : C(interior S, S) :=
    ⟨Set.inclusion interior_subset, continuous_inclusion interior_subset⟩
  let qS : C(S, Metric.sphere (0 : E2) 1) :=
    ⟨fun x => (φ x).2, continuous_snd.comp φ.continuous⟩
  let q : C(interior S, Metric.sphere (0 : E2) 1) := qS.comp i
  have h0 : (0 : E2) ∈ Metric.closedBall (0 : E2) 1 :=
    Metric.mem_closedBall_self zero_le_one
  let j : C(Metric.sphere (0 : E2) 1, interior S) :=
    ⟨fun θ => ⟨φ.symm (⟨0, h0⟩, θ),
      mem_interior_of_homeomorph_closedBall_prod_sphere φ _ θ (by simp)⟩,
      (continuous_subtype_val.comp (φ.symm.continuous.comp
        (continuous_const.prodMk continuous_id))).subtype_mk _⟩
  have hball (t : unitInterval) (x : interior S) :
      (1 - (t : ℝ)) • ((φ (i x)).1 : E2) ∈ Metric.closedBall (0 : E2) 1 := by
    have h1 := mem_closedBall_zero_iff.mp (φ (i x)).1.2
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr t.2.2)]
    nlinarith [t.2.1, t.2.2, norm_nonneg ((φ (i x)).1 : E2)]
  have hint (t : unitInterval) (x : interior S) :
      (φ.symm (⟨_, hball t x⟩, (φ (i x)).2) : E3) ∈ interior S := by
    rcases eq_or_lt_of_le t.2.1 with ht | ht
    · have hv : (⟨(1 - (t : ℝ)) • ((φ (i x)).1 : E2), hball t x⟩ :
          Metric.closedBall (0 : E2) 1) = (φ (i x)).1 :=
        Subtype.ext (by simp [← ht])
      rw [hv, Prod.mk.eta, φ.symm_apply_apply]
      exact x.2
    · apply mem_interior_of_homeomorph_closedBall_prod_sphere
      have h1 := mem_closedBall_zero_iff.mp (φ (i x)).1.2
      rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr t.2.2)]
      nlinarith [mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr h1)]
  let F : ContinuousMap.Homotopy (ContinuousMap.id (interior S)) (j.comp q) :=
    { toFun := fun p => ⟨φ.symm (⟨_, hball p.1 p.2⟩, (φ (i p.2)).2), hint p.1 p.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk (continuous_subtype_val.comp (φ.symm.continuous.comp
          (Continuous.prodMk (Continuous.subtype_mk ?_ _) ?_))) _
        · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
            (continuous_subtype_val.comp (continuous_fst.comp
              (φ.continuous.comp (i.continuous.comp continuous_snd))))
        · exact continuous_snd.comp (φ.continuous.comp (i.continuous.comp continuous_snd))
      map_zero_left := fun x => by
        apply Subtype.ext
        have hv : (⟨(1 - ((0 : unitInterval) : ℝ)) • ((φ (i x)).1 : E2),
            hball 0 x⟩ : Metric.closedBall (0 : E2) 1) = (φ (i x)).1 :=
          Subtype.ext (by simp)
        change (φ.symm (⟨_, hball 0 x⟩, (φ (i x)).2) : E3) = x
        rw [hv, Prod.mk.eta, φ.symm_apply_apply]
        rfl
      map_one_left := fun x => by
        apply Subtype.ext
        have hv : (⟨(1 - ((1 : unitInterval) : ℝ)) • ((φ (i x)).1 : E2),
            hball 1 x⟩ : Metric.closedBall (0 : E2) 1) = ⟨0, h0⟩ :=
          Subtype.ext (by simp)
        change (φ.symm (⟨_, hball 1 x⟩, (φ (i x)).2) : E3) =
          φ.symm (⟨0, h0⟩, (φ (i x)).2)
        rw [hv] }
  have hleft : (integralSingularHomologyMap 1 j).comp
      (integralSingularHomologyMap 1 q) = LinearMap.id := by
    rw [← integralSingularHomologyMap_comp,
      ← integralSingularHomologyMap_homotopic 1 ⟨F⟩,
      integralSingularHomologyMap_id]
  change Function.Injective (integralSingularHomologyMap 1 i)
  intro a b hab
  have hq : integralSingularHomologyMap 1 q a = integralSingularHomologyMap 1 q b := by
    change integralSingularHomologyMap 1 (qS.comp i) a =
      integralSingularHomologyMap 1 (qS.comp i) b
    rw [integralSingularHomologyMap_comp]
    exact congrArg (integralSingularHomologyMap 1 qS) hab
  have hj := congrArg (integralSingularHomologyMap 1 j) hq
  simpa only [← LinearMap.comp_apply, hleft, LinearMap.id_apply] using hj

end DifferentialGeometry.Topology.PiecewiseLinear
