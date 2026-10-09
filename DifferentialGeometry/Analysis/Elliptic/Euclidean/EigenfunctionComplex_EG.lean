import DifferentialGeometry.Analysis.Elliptic.Euclidean.EigenfunctionPositive_EG
import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian

/-!
# The positive first Dirichlet eigenfunction on a domain in `ℂ` (S-W-EIG, G3)

Transfer of `exists_positive_first_eigenfunction_EG` along the isometry
`Complex.orthonormalBasisOneI.repr : ℂ ≃ₗᵢ[ℝ] ℝ²`.  The conformal coordinate of a Morrey disk is a
point of `ℂ` and `|∇φ|² = (∂ₓφ)² + (∂ᵧφ)² = (fderiv φ z 1)² + (fderiv φ z I)²`, so the statement is
the weighted problem `-Δ₀ u + W u = μ ρ u` with `ρ = λ`, `W = λ(K_Σ - q)` of the blueprint.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace InnerProductSpace ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- The orthonormal-basis identification `ℂ ≃ₗᵢ[ℝ] ℝ²`, `z ↦ (re z, im z)`. -/
def cplxEquiv_EG : ℂ ≃ₗᵢ[ℝ] E2 := Complex.orthonormalBasisOneI.repr

theorem cplxEquiv_symm_single_zero_EG :
    cplxEquiv_EG.symm (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = 1 := by
  simp [cplxEquiv_EG]

theorem cplxEquiv_symm_single_one_EG :
    cplxEquiv_EG.symm (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) = Complex.I := by
  simp [cplxEquiv_EG]

theorem setIntegral_cplxEquiv_EG (Ω : Set ℂ) (G : ℂ → ℝ) :
    (∫ x in cplxEquiv_EG '' Ω, G (cplxEquiv_EG.symm x)) = ∫ z in Ω, G z := by
  have h := cplxEquiv_EG.symm.measurePreserving.setIntegral_preimage_emb
    cplxEquiv_EG.symm.toHomeomorph.measurableEmbedding G Ω
  have hset : cplxEquiv_EG '' Ω = cplxEquiv_EG.symm ⁻¹' Ω := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨cplxEquiv_EG.symm x, hx, by simp⟩
  rw [hset]
  exact h

theorem laplacian_cplxEquiv_EG (u : ℂ → ℝ) (x : E2) :
    Laplacian.laplacian (u ∘ cplxEquiv_EG.symm) x = Laplacian.laplacian u (cplxEquiv_EG.symm x) :=
  LinearIsometryEquiv.laplacian_comp cplxEquiv_EG.symm u x

theorem sumsq_fderiv_cplx_EG (φ : ℂ → ℝ) (x : E2)
    (hφ : DifferentiableAt ℝ φ (cplxEquiv_EG.symm x)) :
    (∑ i : Fin 2, (fderiv ℝ (φ ∘ cplxEquiv_EG.symm) x (EuclideanSpace.single i 1)) ^ 2) =
      (fderiv ℝ φ (cplxEquiv_EG.symm x) 1) ^ 2 +
        (fderiv ℝ φ (cplxEquiv_EG.symm x) Complex.I) ^ 2 := by
  let L : E2 →L[ℝ] ℂ := cplxEquiv_EG.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hL : HasFDerivAt cplxEquiv_EG.symm L x := L.hasFDerivAt
  have h : fderiv ℝ (φ ∘ cplxEquiv_EG.symm) x = (fderiv ℝ φ (cplxEquiv_EG.symm x)).comp L :=
    (hφ.hasFDerivAt.comp x hL).fderiv
  have hL0 : L (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = 1 := cplxEquiv_symm_single_zero_EG
  have hL1 : L (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) = Complex.I :=
    cplxEquiv_symm_single_one_EG
  rw [Fin.sum_univ_two, h]
  simp only [ContinuousLinearMap.comp_apply, hL0, hL1]

theorem integral_sumsq_cplx_EG (Ω : Set ℂ) (φ : ℂ → ℝ) (hφ : Differentiable ℝ φ) :
    (∫ x in cplxEquiv_EG '' Ω, ∑ i : Fin 2,
        (fderiv ℝ (φ ∘ cplxEquiv_EG.symm) x (EuclideanSpace.single i 1)) ^ 2) =
      ∫ z in Ω, ((fderiv ℝ φ z 1) ^ 2 + (fderiv ℝ φ z Complex.I) ^ 2) := by
  rw [← setIntegral_cplxEquiv_EG Ω]
  apply integral_congr_ae
  filter_upwards with x
  exact sumsq_fderiv_cplx_EG φ x (hφ _)

theorem tsupport_comp_cplx_EG (φ' : E2 → ℝ) :
    tsupport (φ' ∘ cplxEquiv_EG) = cplxEquiv_EG ⁻¹' tsupport φ' := by
  rw [tsupport, tsupport, Function.support_comp_eq_preimage]
  exact (cplxEquiv_EG.toHomeomorph.preimage_closure (Function.support φ')).symm

theorem tsupport_comp_symm_cplx_EG (φ : ℂ → ℝ) :
    tsupport (φ ∘ cplxEquiv_EG.symm) = cplxEquiv_EG.symm ⁻¹' tsupport φ := by
  rw [tsupport, tsupport, Function.support_comp_eq_preimage]
  exact (cplxEquiv_EG.symm.toHomeomorph.preimage_closure (Function.support φ)).symm

theorem exists_positive_first_eigenfunction_complex_EG
    {Ω U : Set ℂ} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΩc : IsPreconnected Ω)
    (hne : Ω.Nonempty) (hU : IsOpen U) (hΩU : closure Ω ⊆ U) {ρ W : ℂ → ℝ}
    (hρs : ContDiffOn ℝ (⊤ : ℕ∞) ρ U) (hWs : ContDiffOn ℝ (⊤ : ℕ∞) W U)
    (hρpos : ∀ z ∈ closure Ω, 0 < ρ z)
    (hstab : ∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      0 ≤ (∫ z in Ω, ((fderiv ℝ φ z 1) ^ 2 + (fderiv ℝ φ z Complex.I) ^ 2)) +
        ∫ z in Ω, W z * φ z ^ 2) :
    ∃ (u : ℂ → ℝ) (μ : ℝ), ContDiffOn ℝ (⊤ : ℕ∞) u Ω ∧ (∀ z ∈ Ω, 0 < u z) ∧ 0 ≤ μ ∧
      (∫ z in Ω, ρ z * u z ^ 2) = 1 ∧
      (∀ z ∈ Ω, -Laplacian.laplacian u z + W z * u z = μ * ρ z * u z) ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        μ * (∫ z in Ω, ρ z * φ z ^ 2) ≤
          (∫ z in Ω, ((fderiv ℝ φ z 1) ^ 2 + (fderiv ℝ φ z Complex.I) ^ 2)) +
            ∫ z in Ω, W z * φ z ^ 2 := by
  classical
  let T := cplxEquiv_EG
  let Ω' : Set E2 := T '' Ω
  let U' : Set E2 := T '' U
  have hΩ' : IsOpen Ω' := T.toHomeomorph.isOpenMap Ω hΩ
  have hU' : IsOpen U' := T.toHomeomorph.isOpenMap U hU
  have hΩb' : Bornology.IsBounded Ω' := T.isometry.lipschitzWith.isBounded_image hΩb
  have hΩc' : IsPreconnected Ω' := hΩc.image T T.continuous.continuousOn
  have hne' : Ω'.Nonempty := hne.image T
  have hclosure : closure Ω' = T '' closure Ω := (T.toHomeomorph.image_closure Ω).symm
  have hcl : closure Ω' ⊆ U' := by
    rw [hclosure]
    exact image_mono hΩU
  let ρ' : E2 → ℝ := ρ ∘ T.symm
  let W' : E2 → ℝ := W ∘ T.symm
  have hmaps : Set.MapsTo T.symm U' U := by
    rintro x ⟨z, hz, rfl⟩
    simpa using hz
  have hρ's : ContDiffOn ℝ (⊤ : ℕ∞) ρ' U' := hρs.comp T.symm.contDiff.contDiffOn hmaps
  have hW's : ContDiffOn ℝ (⊤ : ℕ∞) W' U' := hWs.comp T.symm.contDiff.contDiffOn hmaps
  have hρ'pos : ∀ x ∈ closure Ω', 0 < ρ' x := by
    intro x hx
    rw [hclosure] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    simpa [ρ', T] using hρpos z hz
  have hstab' : ∀ φ' : E2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ' → HasCompactSupport φ' →
      tsupport φ' ⊆ Ω' → 0 ≤ (∫ x in Ω', ∑ i : Fin 2,
        (fderiv ℝ φ' x (EuclideanSpace.single i 1)) ^ 2) + ∫ x in Ω', W' x * φ' x ^ 2 := by
    intro φ' h1 h2 h3
    let φ : ℂ → ℝ := φ' ∘ T
    have hφ1 : ContDiff ℝ (⊤ : ℕ∞) φ := h1.comp T.contDiff
    have hφ2 : HasCompactSupport φ := h2.comp_homeomorph T.toHomeomorph
    have hφ3 : tsupport φ ⊆ Ω := by
      rw [tsupport_comp_cplx_EG]
      intro z hz
      obtain ⟨y, hy, hyz⟩ := h3 hz
      have : y = z := T.injective hyz
      rwa [this] at hy
    have h := hstab φ hφ1 hφ2 hφ3
    have hφ'eq : φ ∘ T.symm = φ' := by
      ext x
      simp [φ]
    have e1 := integral_sumsq_cplx_EG Ω φ (hφ1.differentiable (by simp))
    rw [hφ'eq] at e1
    have e2 : (∫ x in Ω', W' x * φ' x ^ 2) = ∫ z in Ω, W z * φ z ^ 2 := by
      rw [← setIntegral_cplxEquiv_EG Ω]
      apply integral_congr_ae
      filter_upwards with x
      simp [W', φ, T]
    rw [e1, e2]
    exact h
  obtain ⟨ũ, μ, hu0, hũ, hpos, hμ, hN, hEq, hmin⟩ :=
    exists_positive_first_eigenfunction_EG hΩ' hΩb' hΩc' hne' hU' hcl hρ's hW's hρ'pos hstab'
  have hΩ'mem : ∀ z ∈ Ω, T z ∈ Ω' := fun z hz => ⟨z, hz, rfl⟩
  have hũT : (ũ ∘ T) ∘ T.symm = ũ := by
    ext x
    simp
  refine ⟨ũ ∘ T, μ, hũ.comp T.contDiff.contDiffOn hΩ'mem, fun z hz => hpos (T z) (hΩ'mem z hz),
    hμ, ?_, ?_, ?_⟩
  · rw [← hN, ← setIntegral_cplxEquiv_EG Ω]
    apply integral_congr_ae
    filter_upwards with x
    simp [ρ', T]
  · intro z hz
    have h := hEq (T z) (hΩ'mem z hz)
    have hl := laplacian_cplxEquiv_EG (ũ ∘ T) (T z)
    rw [hũT, T.symm_apply_apply] at hl
    rw [hl] at h
    simpa [W', ρ', T] using h
  · intro φ hφ1 hφ2 hφ3
    let φ' : E2 → ℝ := φ ∘ T.symm
    have h1 : ContDiff ℝ (⊤ : ℕ∞) φ' := hφ1.comp T.symm.contDiff
    have h2 : HasCompactSupport φ' := hφ2.comp_homeomorph T.symm.toHomeomorph
    have hset : T '' Ω = T.symm ⁻¹' Ω := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨T.symm x, hx, by simp⟩
    have h3 : tsupport φ' ⊆ Ω' := by
      rw [tsupport_comp_symm_cplx_EG]
      change T.symm ⁻¹' tsupport φ ⊆ T '' Ω
      rw [hset]
      exact Set.preimage_mono hφ3
    have hmem : DeGiorgi.MemW01p 2 φ' Ω' := DeGiorgi.smoothTest_memH01 hΩ' ⟨h1, h2, h3⟩
    have h := hmin φ' hmem (DeGiorgi.smoothTestWitness hΩ' ⟨h1, h2, h3⟩)
    have e0 : (∫ x in Ω', ‖(DeGiorgi.smoothTestWitness hΩ' ⟨h1, h2, h3⟩).weakGrad x‖ ^ 2) =
        ∫ x in Ω', ∑ i : Fin 2, (fderiv ℝ φ' x (EuclideanSpace.single i 1)) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      simp [DeGiorgi.smoothTestWitness, DeGiorgi.smoothGradField, EuclideanSpace.norm_sq_eq]
    have e1 := integral_sumsq_cplx_EG Ω φ (hφ1.differentiable (by simp))
    have e2 : (∫ x in Ω', W' x * φ' x ^ 2) = ∫ z in Ω, W z * φ z ^ 2 := by
      rw [← setIntegral_cplxEquiv_EG Ω]
      apply integral_congr_ae
      filter_upwards with x
      simp [W', φ', T]
    have e3 : (∫ x in Ω', ρ' x * φ' x ^ 2) = ∫ z in Ω, ρ z * φ z ^ 2 := by
      rw [← setIntegral_cplxEquiv_EG Ω]
      apply integral_congr_ae
      filter_upwards with x
      simp [ρ', φ', T]
    rw [e0, e1, e2, e3] at h
    exact h

end DifferentialGeometry.Analysis.Sobolev.Euclidean
