import DifferentialGeometry.Analysis.ODE.Flow.Planar.IdentityTangentGerm
import DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_compact_diffeomorph_realizing_germ_up_to_derivative
    {f : E → E} {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (A : E ≃L[ℝ] E)
    (hA : HasFDerivAt f (A : E →L[ℝ] E) 0)
    {V : Set E} (hV : IsOpen V) (h0V : f 0 ∈ V) :
    ∃ J : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ᶠ x in 𝓝 (0 : E), J (A x + f 0) = f x) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ V ∧
        ∀ y, y ∉ K → J y = y ∧ J.symm y = y := by
  let W : Set E := A.symm ⁻¹' U ∩ (fun y ↦ y + f 0) ⁻¹' V
  have hW : IsOpen W := (hU.preimage A.symm.continuous).inter
    (hV.preimage (continuous_id.add continuous_const))
  have h0W : (0 : E) ∈ W := by simp [W, h0U, h0V]
  let g : E → E := fun y ↦ f (A.symm y) - f 0
  have hg : ContDiffOn ℝ ∞ g W :=
    (hf.comp A.symm.contDiff.contDiffOn (fun _ hy ↦ hy.1)).sub contDiffOn_const
  have hg0 : g 0 = 0 := by simp [g]
  have hd : HasFDerivAt g (ContinuousLinearMap.id ℝ E) 0 := by
    have hA' : HasFDerivAt f (A : E →L[ℝ] E) (A.symm 0) := by simpa using hA
    have hd' := (hA'.comp 0 A.symm.hasFDerivAt).sub_const (f 0)
    simpa only [ContinuousLinearEquiv.coe_comp_coe_symm, Function.comp_def] using hd'
  obtain ⟨D, _, _, _, hgerm, _, K, hK, hKW, hfix⟩ :=
    exists_compact_isotopy_realizing_identity_tangent_germ hW h0W hg hg0 hd
  let T := DifferentialGeometry.Topology.translateDiffeomorph (f 0)
  let J := (T.symm.trans (D 1)).trans T
  have hJ (x : E) : J x = D 1 (x - f 0) + f 0 := by
    change D 1 (x + -(f 0)) + f 0 = _
    rw [← sub_eq_add_neg]
  have hJfix (y : E) (hy : y ∉ (fun x ↦ x + f 0) '' K) : J y = y := by
    have hyK : y - f 0 ∉ K := fun h ↦ hy ⟨y - f 0, h, sub_add_cancel _ _⟩
    rw [hJ, (hfix 1 (y - f 0) hyK).1, sub_add_cancel]
  refine ⟨J, ?_, (fun x ↦ x + f 0) '' K,
    hK.image (continuous_id.add continuous_const), ?_, ?_⟩
  · have ht : Tendsto A (𝓝 (0 : E)) (𝓝 0) := by simpa using A.continuous.tendsto 0
    filter_upwards [hgerm.comp_tendsto ht] with x hx
    change D 1 (A x) = g (A x) at hx
    rw [hJ, add_sub_cancel_right, hx]
    simp only [g, A.symm_apply_apply, sub_add_cancel]
  · rintro y ⟨x, hx, rfl⟩
    exact (hKW hx).2
  · intro y hy
    refine ⟨hJfix y hy, ?_⟩
    apply J.injective
    exact (J.apply_symm_apply y).trans (hJfix y hy).symm

theorem exists_compact_diffeomorph_straightening_partialDiffeomorph
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (h0 : (0 : E) ∈ φ.source)
    {V : Set E} (hV : IsOpen V) (h0V : φ 0 ∈ V) :
    ∃ A : E ≃L[ℝ] E, (A : E →L[ℝ] E) = fderiv ℝ φ 0 ∧
      ∃ J : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        (∀ᶠ x in 𝓝 (0 : E), J (A x + φ 0) = φ x) ∧
        ∃ K : Set E, IsCompact K ∧ K ⊆ V ∧
          ∀ y, y ∉ K → J y = y ∧ J.symm y = y := by
  let A : E ≃L[ℝ] E :=
    (φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ h0).mfderivToContinuousLinearEquiv (by simp)
  have hAe : (A : E →L[ℝ] E) = fderiv ℝ φ 0 := by
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ 0 = _
    exact mfderiv_eq_fderiv
  have hA : HasFDerivAt φ (A : E →L[ℝ] E) 0 := by
    rw [hAe]
    exact ((φ.contMDiffOn.contDiffOn.contDiffAt (φ.open_source.mem_nhds h0)).differentiableAt
      (by simp)).hasFDerivAt
  exact ⟨A, hAe, exists_compact_diffeomorph_realizing_germ_up_to_derivative
    φ.open_source h0 φ.contMDiffOn.contDiffOn A hA hV h0V⟩

end DifferentialGeometry.Analysis
