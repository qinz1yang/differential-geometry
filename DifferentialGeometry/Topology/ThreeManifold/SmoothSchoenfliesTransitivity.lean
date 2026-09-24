import DifferentialGeometry.Topology.SphereSeparation.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFilling
import DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenfliesRoundSphere

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.ThreeManifold

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => Metric.sphere (0 : ℝ³) 1

private noncomputable def translationDiffeomorph (v : ℝ³) : ℝ³ ≃ₘ[ℝ] ℝ³ where
  toFun x := x + v
  invFun y := y - v
  left_inv x := by simp
  right_inv y := by simp
  contMDiff_toFun := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : ℝ³ => x + v)
    apply ContDiff.contMDiff
    fun_prop
  contMDiff_invFun := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun y : ℝ³ => y - v)
    apply ContDiff.contMDiff
    fun_prop

private theorem isSmoothEmbedding_translate_sphereTwo_subtype (v : ℝ³) :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun x : S² => (x : ℝ³) + v) :=
  isSmoothEmbedding_sphereTwo_subtype.postcomp_diffeomorph (translationDiffeomorph v)

theorem exists_diffeomorph_image_range_of_smoothSchoenfliesThree
    (h : SphereSeparation.smoothSchoenfliesThree) {e₁ e₂ : S² → ℝ³}
    (he₁ : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (he₂ : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₂) :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' Set.range e₁ = Set.range e₂ := by
  obtain ⟨Φ₁, hΦ₁⟩ :=
    SphereSeparation.exists_global_diffeomorph_of_smoothSchoenflies h e₁ he₁
  obtain ⟨Φ₂, hΦ₂⟩ :=
    SphereSeparation.exists_global_diffeomorph_of_smoothSchoenflies h e₂ he₂
  refine ⟨Φ₁.symm.trans Φ₂, ?_⟩
  have hsymm : Φ₁.symm '' Set.range e₁ = S² := by
    rw [← hΦ₁]
    exact Equiv.symm_image_image Φ₁.toEquiv S²
  rw [Diffeomorph.coe_trans, Set.image_comp, hsymm, hΦ₂]

theorem smoothSchoenfliesThree_of_exists_diffeomorph_image_range
    (h : ∀ (e₁ e₂ : S² → ℝ³),
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁ →
        Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₂ →
          ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' Set.range e₁ = Set.range e₂) :
    SphereSeparation.smoothSchoenfliesThree := by
  refine SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph.mpr ?_
  intro e he
  obtain ⟨Φ, hΦ⟩ := h (Subtype.val : S² → ℝ³) e isSmoothEmbedding_sphereTwo_subtype he
  rw [Subtype.range_coe] at hΦ
  exact ⟨Φ, hΦ⟩

theorem exists_diffeomorph_image_compactSide_of_smoothSchoenfliesThree
    (h : SphereSeparation.smoothSchoenfliesThree) {e₁ e₂ : S² → ℝ³}
    (he₁ : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (he₂ : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₂) :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³,
      Φ '' (SphereSeparation.jordanBrouwer_openThreeSpace e₁ he₁
              (Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞)).compactSide =
        (SphereSeparation.jordanBrouwer_openThreeSpace e₂ he₂
              (Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞)).compactSide := by
  obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_image_range_of_smoothSchoenfliesThree h he₁ he₂
  let ψ : Diffeomorph (𝓘(ℝ, ℝ³)) (𝓘(ℝ, ℝ³)) ℝ³ ℝ³ ∞ := Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞
  let d₁ := SphereSeparation.jordanBrouwer_openThreeSpace e₁ he₁ ψ
  let d₂ := SphereSeparation.jordanBrouwer_openThreeSpace e₂ he₂ ψ
  have huniq : d₂.compactSide = (d₁.toSphereSides.image Φ.toHomeomorph).compactSide :=
    ((d₁.toSphereSides.image Φ.toHomeomorph).side_sets_unique_of_core_properties
      d₂.compactSide d₂.endSide d₂.isOpen_compactSide d₂.isOpen_endSide
      d₂.isConnected_compactSide d₂.isConnected_endSide d₂.disjoint
      (by rw [d₂.union_eq_compl, ← hΦ]; rfl) d₂.isCompact_closure_compactSide
      d₂.not_isCompact_closure_endSide).1
  refine ⟨Φ, ?_⟩
  change ⇑Φ '' d₁.compactSide = d₂.compactSide
  rw [huniq, SphereSeparation.SphereSides.image_compactSide, Diffeomorph.coe_toHomeomorph]

theorem not_exists_linearIsometryEquiv_image_translate_sphere (v : ℝ³) (hv : v ≠ 0) :
    ¬ ∃ Φ : ℝ³ ≃ₗᵢ[ℝ] ℝ³,
        Φ '' S² = Set.range (fun x : S² => (x : ℝ³) + v) := by
  rintro ⟨Φ, hΦ⟩
  have hnorm : ∀ y ∈ Set.range (fun x : S² => (x : ℝ³) + v), ‖y‖ = 1 := by
    rintro y hy
    rw [← hΦ] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [Φ.norm_map]
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  let u : S² := ⟨(‖v‖⁻¹ : ℝ) • v, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact norm_smul_inv_norm hv⟩
  have hu := hnorm ((u : ℝ³) + v) ⟨u, rfl⟩
  have hsub : (u : ℝ³) + v = ((‖v‖⁻¹ : ℝ) + 1) • v := by
    simp [u, add_smul, one_smul]
  have hnormu : ‖(u : ℝ³) + v‖ = 1 + ‖v‖ := by
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    field_simp
  rw [hnormu] at hu
  linarith [norm_pos_iff.mpr hv]

theorem not_forall_exists_linearIsometryEquiv_image_sphere :
    ¬ ∀ (e : S² → ℝ³), Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e →
        ∃ Φ : ℝ³ ≃ₗᵢ[ℝ] ℝ³, Φ '' S² = Set.range e := by
  intro h
  obtain ⟨u, hsu⟩ :=
    (NormedSpace.sphere_nonempty (x := (0 : ℝ³)) (r := (1 : ℝ))).mpr zero_le_one
  have hnormu : ‖(u : ℝ³)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hsu
  have hu : (u : ℝ³) ≠ 0 := by
    rw [← norm_ne_zero_iff, hnormu]
    norm_num
  exact not_exists_linearIsometryEquiv_image_translate_sphere (u : ℝ³) hu
    (h (fun x : S² => (x : ℝ³) + (u : ℝ³)) (isSmoothEmbedding_translate_sphereTwo_subtype _))

end DifferentialGeometry.Topology.ThreeManifold
