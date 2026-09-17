import DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import DifferentialGeometry.Topology.Manifold.AddCircle.DiffeomorphLift
import DifferentialGeometry.Topology.Embedding.PeriodicCurveIsotopy
import DifferentialGeometry.Topology.Embedding.Sphere
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionInterior
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Topology.Homeomorph.Ball

open Set Metric
open scoped ContDiff Manifold

namespace Circle

theorem exists_diffeomorph_extension
    (Q : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞) :
    ∃ D : ℂ ≃ₘ[ℝ] ℂ, (∀ x : Circle, D x = Q x) ∧ D 0 = 0 ∧
      D '' closedBall (0 : ℂ) 1 = closedBall 0 1 := by
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  let A := AddCircle.diffeomorphCircle
  let ψ := (A.trans Q).trans A.symm
  obtain ⟨g, hgp, hgd, hψ⟩ := AddCircle.exists_increasing_diffeomorphism_lift_or_neg ψ
  let f : AddCircle (1 : ℝ) → ℂ := fun θ => A θ
  have hA : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 1) ∞ A :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      A.isLocalDiffeomorph A.injective
  have hf : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ f := by
    exact (isSmoothEmbedding_coe_sphere (E := ℂ) (n := 1)).comp_of_boundarylessManifold hA (by simp)
  obtain ⟨Φ, _, _, _, htrack, K, _, hK, hfix⟩ :=
    DifferentialGeometry.Topology.PeriodicCurve.exists_compactly_supported_ambient_isotopy_of_increasing_lift
      hf g.contMDiff.contDiff hgp hgd isOpen_compl_singleton
      (show range f ⊆ ({0} : Set ℂ)ᶜ from by
        rintro _ ⟨θ, rfl⟩
        exact ne_zero_of_mem_unit_sphere (A θ))
  have hΦzero (t : ℝ) : Φ t 0 = 0 := (hfix t).1 (by
    intro hz
    exact hK hz rfl)
  have htrack1 (x : ℝ) : Φ 1 (f (x : AddCircle (1 : ℝ))) = f (g x : AddCircle (1 : ℝ)) := by
    simpa only [sub_self, zero_mul, one_mul, zero_add] using htrack 1 ⟨zero_le_one, le_rfl⟩ x
  have hext : ∃ D : ℂ ≃ₘ[ℝ] ℂ, (∀ x : Circle, D x = Q x) ∧ D 0 = 0 := by
    rcases hψ with hψ | hψ
    · refine ⟨Φ 1, ?_, hΦzero 1⟩
      intro x
      obtain ⟨θ, rfl⟩ := A.surjective x
      obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
      have h := congrArg A (hψ t)
      change A (A.symm (Q (A (t : AddCircle (1 : ℝ)))) ) = A (g t : AddCircle (1 : ℝ)) at h
      rw [A.apply_symm_apply] at h
      exact (htrack1 t).trans (congrArg (Subtype.val : Circle → ℂ) h.symm)
    · refine ⟨(Φ 1).trans Complex.conjCLE.toDiffeomorph, ?_, ?_⟩
      rotate_left
      · change starRingEnd ℂ (Φ 1 0) = 0
        rw [hΦzero]
        simp
      intro x
      obtain ⟨θ, rfl⟩ := A.surjective x
      obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
      have h := congrArg A (hψ t)
      change A (A.symm (Q (A (t : AddCircle (1 : ℝ))))) = A (-(g t : AddCircle (1 : ℝ))) at h
      rw [A.apply_symm_apply] at h
      change starRingEnd ℂ (Φ 1 (f (t : AddCircle (1 : ℝ)))) = (Q (A (t : AddCircle (1 : ℝ))) : ℂ)
      rw [htrack1, h]
      change starRingEnd ℂ (AddCircle.homeomorphCircle one_ne_zero (g t : AddCircle (1 : ℝ)) : ℂ) =
        (AddCircle.homeomorphCircle one_ne_zero (-(g t : AddCircle (1 : ℝ))) : ℂ)
      rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_neg]
      exact (Circle.coe_inv_eq_conj _).symm
  obtain ⟨D, hD, hD0⟩ := hext
  refine ⟨D, hD, hD0, ?_⟩
  apply D.toHomeomorph.image_closedBall_of_image_sphere_eq_of_map_center
    zero_lt_one zero_lt_one ?_ hD0
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change D x ∈ sphere 0 1
    rw [hD ⟨x, hx⟩]
    exact (Q ⟨x, hx⟩).property
  · intro hz
    obtain ⟨x, hx⟩ := Q.surjective ⟨z, hz⟩
    exact ⟨x.val, x.property, (hD x).trans (congrArg Subtype.val hx)⟩

end Circle

namespace EuclideanGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 1 + 1)]

theorem exists_diffeomorph_extension_circle
    (Q : Diffeomorph (𝓡 1) (𝓡 1) (sphere (0 : E) 1) (sphere (0 : E) 1) ∞) :
    ∃ D : E ≃ₘ[ℝ] E, (∀ x : sphere (0 : E) 1, D x = Q x) ∧ D 0 = 0 ∧
      D '' closedBall (0 : E) 1 = closedBall 0 1 := by
  let _ : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ 1
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  let A : ℂ ≃ₗᵢ[ℝ] E := Complex.isometryOfOrthonormal
    ((stdOrthonormalBasis ℝ E).reindex (finCongr (Fact.out : Module.finrank ℝ E = 1 + 1)))
  let f : Circle → E := fun x => A x
  have hf : Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E) ∞ f :=
    ⟨(isSmoothEmbedding_coe_sphere (E := ℂ) (n := 1)).isImmersion.isLocalDiffeomorphOn_comp_of_ne_zero
      (fun y => A.toContinuousLinearEquiv.toDiffeomorph.isLocalDiffeomorph y.val) (by simp),
      A.toHomeomorph.isEmbedding.comp .subtypeVal⟩
  have hg := isSmoothEmbedding_coe_sphere (E := E) (n := 1)
  have hfg : range f = range (Subtype.val : sphere (0 : E) 1 → E) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨A x, by rw [mem_sphere_zero_iff_norm, A.norm_map]; exact Circle.norm_coe x⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨⟨A.symm x, ?_⟩, A.apply_symm_apply x⟩
      change A.symm x.val ∈ sphere (0 : ℂ) 1
      rw [mem_sphere_zero_iff_norm]
      rw [A.symm.norm_map]
      exact mem_sphere_zero_iff_norm.mp x.property
  let C := hf.diffeomorphOfRangeEq hg hfg
  have hC (x : Circle) : (C x).val = A x := hf.comp_diffeomorphOfRangeEq hg hfg x
  obtain ⟨D, hD, hD0, _⟩ := Circle.exists_diffeomorph_extension ((C.trans Q).trans C.symm)
  let AD := A.toContinuousLinearEquiv.toDiffeomorph
  let F := (AD.symm.trans D).trans AD
  have hF (x : sphere (0 : E) 1) : F x = (Q x).val := by
    obtain ⟨y, rfl⟩ := C.surjective x
    change A (D (A.symm (C y).val)) = (Q (C y)).val
    rw [hC, A.symm_apply_apply, hD y]
    change A (C.symm (Q (C y))).val = (Q (C y)).val
    rw [← hC, C.apply_symm_apply]
  have hF0 : F 0 = 0 := by
    change A (D (A.symm 0)) = 0
    rw [map_zero, hD0, map_zero]
  refine ⟨F, hF, hF0, ?_⟩
  apply F.toHomeomorph.image_closedBall_of_image_sphere_eq_of_map_center
    zero_lt_one zero_lt_one ?_ hF0
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change F x ∈ sphere 0 1
    rw [hF ⟨x, hx⟩]
    exact (Q ⟨x, hx⟩).property
  · intro hz
    obtain ⟨x, hx⟩ := Q.surjective ⟨z, hz⟩
    exact ⟨x.val, x.property, (hF x).trans (congrArg Subtype.val hx)⟩

end EuclideanGeometry
