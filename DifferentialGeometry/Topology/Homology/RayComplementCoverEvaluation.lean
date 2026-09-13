import DifferentialGeometry.Topology.Homology.ContractibleCoverOneEvaluation
import DifferentialGeometry.Topology.Homology.TotallyDisconnectedZero

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Metric Module

namespace DifferentialGeometry.Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def raySet (v : E) : Set E := Set.range fun t : Ioi (0 : ℝ) => (t : ℝ) • v

theorem mem_raySet_iff {v : E} (hv : v ≠ 0) {x : E} :
    x ∈ raySet v ↔ x ∈ (Submodule.span ℝ {v} : Submodule ℝ E) ∧ 0 < inner ℝ x v := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v), ?_⟩
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact mul_pos t.property (pow_pos (norm_pos_iff.mpr hv) 2)
  · rintro ⟨hx, hpos⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hc : 0 < c := by
      have h : c * ‖v‖ ^ 2 = inner ℝ (c • v) v := by
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      nlinarith [norm_pos_iff.mpr hv]
    exact ⟨⟨c, hc⟩, rfl⟩

def rayUnit {v : E} (hv : v ≠ 0) : sphere (0 : E) 1 :=
  ⟨‖v‖⁻¹ • v, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩

theorem compl_raySet_eq_preimage {v : E} (hv : v ≠ 0) :
    ({x : ({0}ᶜ : Set E) | (x : E) ∉ raySet v}) =
      (homeomorphUnitSphereProd E) ⁻¹'
        (({rayUnit hv}ᶜ : Set (sphere (0 : E) 1)) ×ˢ Set.univ) := by
  ext x
  simp only [Set.mem_ofPred_eq, mem_preimage, mem_prod, mem_compl_iff, mem_singleton_iff, mem_univ,
    and_true, homeomorphUnitSphereProd_apply_fst_coe, Subtype.ext_iff]
  constructor
  · intro hx hc
    refine hx ⟨⟨‖(x : E)‖ * ‖v‖⁻¹, mul_pos (norm_pos_iff.mpr x.property)
      (inv_pos.mpr (norm_pos_iff.mpr hv))⟩, ?_⟩
    have h2 := congrArg (fun y : E => ‖(x : E)‖ • y) hc
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (norm_pos_iff.mpr x.property)), one_smul] at h2
    have h3 : (↑(rayUnit hv) : E) = ‖v‖⁻¹ • v := rfl
    change (‖(x : E)‖ * ‖v‖⁻¹) • v = (x : E)
    conv_rhs => rw [h2, h3]
    rw [smul_smul]
  · intro hx ht
    obtain ⟨t, ht'⟩ := ht
    refine hx ?_
    have ht0 : (t : ℝ) ≠ 0 := ne_of_gt t.property
    have hnorm : ‖(t : ℝ) • v‖ = (t : ℝ) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos t.property]
    have key : ‖(t : ℝ) • v‖⁻¹ • ((t : ℝ) • v) = (‖v‖⁻¹ : ℝ) • v := by
      rw [hnorm, smul_smul]
      congr 1
      field_simp
    rw [← ht']
    simpa [rayUnit] using key

section Evaluation

variable {X : Type u} [TopologicalSpace X]

theorem integralHomologyOneContractibleCoverEquiv_apply_functional [PathConnectedSpace X]
    (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (φ : integralSingularHomology 0 (subspaceIntersection A B) →ₗ[ℤ] ℤ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X 1)
    (hz : z ≫ (integralSingularChains X).d 1 0 = 0)
    (zA : integralSingularCoefficients ⟶ (integralSingularChains A).X 1)
    (zB : integralSingularCoefficients ⟶ (integralSingularChains B).X 1)
    (hsplit : zA ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f 1 +
      zB ≫ (integralSingularChainMap (singularSubspaceInclusion B)).f 1 = z)
    (a : integralSingularCoefficients ⟶
      (integralSingularChains (subspaceIntersection A B)).X 0)
    (ha : a ≫ (integralSingularChainMap
        (singularSubspaceInclusion (subspaceIntersection A B))).f 0 =
      zB ≫ (integralSingularChains B).d 1 0) :
    φ (((integralHomologyOneContractibleCoverEquiv A B hA hB hcover)
        (((integralSingularChains X).liftCycles z 0
          ((ComplexShape.down ℕ).next_eq' (by simp)) hz ≫
          (integralSingularChains X).homologyπ 1) (ULift.up 1)) :
        integralSingularHomology 0 (subspaceIntersection A B))) =
      φ (((integralSingularChains (subspaceIntersection A B)).liftCycles a 0
        ChainComplex.next_nat_zero (by rw [(integralSingularChains
          (subspaceIntersection A B)).shape 0 0 (by simp), comp_zero]) ≫
        (integralSingularChains (subspaceIntersection A B)).homologyπ 0) (ULift.up 1)) := by
  rw [integralHomologyOneContractibleCoverEquiv_liftCycles_apply A B hA hB hcover z hz zA zB
    hsplit a ha]

theorem integralHomologyContractibleCoverEquiv_apply_functional (n : ℕ)
    (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (φ : integralSingularHomology (n + 1) (subspaceIntersection A B) →ₗ[ℤ] ℤ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 2))
    (hz : z ≫ (integralSingularChains X).d (n + 2) (n + 1) = 0)
    (zA : integralSingularCoefficients ⟶ (integralSingularChains A).X (n + 2))
    (zB : integralSingularCoefficients ⟶ (integralSingularChains B).X (n + 2))
    (hsplit : zA ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 2) +
      zB ≫ (integralSingularChainMap (singularSubspaceInclusion B)).f (n + 2) = z)
    (a : integralSingularCoefficients ⟶
      (integralSingularChains (subspaceIntersection A B)).X (n + 1))
    (hac : a ≫ (integralSingularChains (subspaceIntersection A B)).d (n + 1) n = 0)
    (ha : a ≫ (integralSingularChainMap
        (singularSubspaceInclusion (subspaceIntersection A B))).f (n + 1) =
      zB ≫ (integralSingularChains B).d (n + 2) (n + 1)) :
    φ (integralHomologyContractibleCoverEquiv n A B hA hB hcover
        (((integralSingularChains X).liftCycles z (n + 1)
          ((ComplexShape.down ℕ).next_eq' (by rfl)) hz ≫
          (integralSingularChains X).homologyπ (n + 2)) (ULift.up 1))) =
      φ (((integralSingularChains (subspaceIntersection A B)).liftCycles a n
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hac ≫
        (integralSingularChains (subspaceIntersection A B)).homologyπ (n + 1))
        (ULift.up 1)) := by
  rw [integralHomologyContractibleCoverEquiv_liftCycles_apply n A B hA hB hcover z hz zA zB
    hsplit a hac ha]

end Evaluation

end DifferentialGeometry.Topology
