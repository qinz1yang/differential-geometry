import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def IsHPolytope (C : Set E) : Prop :=
  IsCompact C ∧ ∃ (ι : Type) (_ : Finite ι) (l : ι → E →ₗ[ℝ] ℝ) (c : ι → ℝ),
    C = {x | ∀ i, l i x ≤ c i}

namespace IsHPolytope

variable {C D : Set E}

theorem isCompact (hC : IsHPolytope C) : IsCompact C := hC.1

theorem isClosed (hC : IsHPolytope C) : IsClosed C := hC.1.isClosed

theorem univ_of_subsingleton [Subsingleton E] : IsHPolytope (univ : Set E) :=
  ⟨isCompact_univ, Empty, inferInstance, fun i => i.elim, fun i => i.elim, by
    ext x
    simp⟩

theorem inter (hC : IsHPolytope C) (hD : IsHPolytope D) : IsHPolytope (C ∩ D) := by
  obtain ⟨hCc, ι, hι, l, c, rfl⟩ := hC
  obtain ⟨hDc, κ, hκ, m, d, rfl⟩ := hD
  have := hι
  have := hκ
  refine ⟨hCc.inter_right hDc.isClosed, ι ⊕ κ, inferInstance, Sum.elim l m, Sum.elim c d, ?_⟩
  ext x
  simp [Sum.forall]

theorem inter_preimage [FiniteDimensional ℝ E] (hC : IsHPolytope C) {D : Set F}
    (hD : IsHPolytope D) (A : E →ᵃ[ℝ] F) : IsHPolytope (C ∩ A ⁻¹' D) := by
  obtain ⟨hCc, ι, hι, l, c, rfl⟩ := hC
  obtain ⟨hDc, κ, hκ, m, d, rfl⟩ := hD
  have := hι
  have := hκ
  have hA : ∀ y, A y = A.linear y + A 0 := fun y => by simpa using A.map_vadd 0 y
  refine ⟨hCc.inter_right (hDc.isClosed.preimage A.continuous_of_finiteDimensional),
    ι ⊕ κ, inferInstance, Sum.elim l fun j => (m j).comp A.linear,
    Sum.elim c fun j => d j - m j (A 0), ?_⟩
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, Sum.forall, Sum.elim_inl, Sum.elim_inr,
    LinearMap.comp_apply]
  refine and_congr Iff.rfl (forall_congr' fun j => ?_)
  rw [hA x, map_add]
  constructor <;> intro h <;> linarith

theorem image_affineEquiv [FiniteDimensional ℝ E] (hC : IsHPolytope C) (T : E ≃ᵃ[ℝ] F) :
    IsHPolytope (T '' C) := by
  obtain ⟨hCc, ι, hι, l, c, rfl⟩ := hC
  have := hι
  have hT : Continuous T := by simpa using T.toAffineMap.continuous_of_finiteDimensional
  have hS : ∀ y, T.symm y = T.symm.linear y + T.symm 0 := fun y => by
    simpa using T.symm.map_vadd 0 y
  refine ⟨hCc.image hT, ι, inferInstance, fun i => (l i).comp (T.symm.linear : F →ₗ[ℝ] E),
    fun i => c i - l i (T.symm 0), ?_⟩
  ext y
  simp only [mem_image, mem_ofPred_eq, LinearMap.comp_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    have hx' := hx i
    have h1 : T.symm.linear (T x) = x - T.symm 0 := by
      have h := hS (T x)
      rw [T.symm_apply_apply] at h
      exact eq_sub_of_add_eq h.symm
    rw [h1, map_sub]
    linarith
  · intro hy
    refine ⟨T.symm y, fun i => ?_, T.apply_symm_apply y⟩
    have h := hy i
    rw [hS y, map_add]
    linarith

end IsHPolytope

theorem exists_isHPolytope_subset_mem_nhds [FiniteDimensional ℝ E] {x : E} {U : Set E}
    (hU : U ∈ 𝓝 x) : ∃ C : Set E, IsHPolytope C ∧ C ⊆ U ∧ C ∈ 𝓝 x := by
  let L := (Module.finBasis ℝ E).equivFunL
  have hpre : L.symm ⁻¹' U ∈ 𝓝 (L x) :=
    L.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨L ⁻¹' Metric.closedBall (L x) (r / 2), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← L.image_symm_eq_preimage]
    exact (isCompact_closedBall _ _).image L.symm.continuous
  · let Lℓ : E →ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := L.toLinearEquiv
    refine ⟨Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ E), inferInstance,
      Sum.elim (fun i => (LinearMap.proj i).comp Lℓ) (fun i => -((LinearMap.proj i).comp Lℓ)),
      Sum.elim (fun i => L x i + r / 2) (fun i => r / 2 - L x i), ?_⟩
    ext y
    simp only [mem_preimage, Metric.mem_closedBall, mem_ofPred_eq, Sum.forall, Sum.elim_inl,
      Sum.elim_inr, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.neg_apply, Lℓ,
      LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
    rw [dist_pi_le_iff (by positivity)]
    simp only [Real.dist_eq, abs_le]
    constructor
    · intro h
      exact ⟨fun i => by linarith [(h i).2], fun i => by linarith [(h i).1]⟩
    · rintro ⟨h1, h2⟩ i
      exact ⟨by linarith [h2 i], by linarith [h1 i]⟩
  · intro y hy
    have hy' : L y ∈ Metric.ball (L x) r := Metric.closedBall_subset_ball (by linarith) hy
    simpa using hball hy'
  · exact L.continuous.continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ (by positivity))

end DifferentialGeometry.Topology.PiecewiseLinear
