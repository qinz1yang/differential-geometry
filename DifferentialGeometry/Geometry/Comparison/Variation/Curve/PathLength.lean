import DifferentialGeometry.Geometry.Comparison.Variation.Curve.ArcLength
import Mathlib.Geometry.Manifold.Riemannian.PathELength

noncomputable section

open Bundle Manifold Set Filter MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma continuousOn_velocityWithin_totalSpace_C1
    {η : ℝ → M} {a b : ℝ} (hab : a < b)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc a b)) :
    ContinuousOn
      (fun t : ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)) : TangentBundle I M))
      (Set.Icc a b) := by
  have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc a b) := by
    intro x hx
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact (uniqueDiffOn_Icc hab) x hx
  have hTan := hη.continuousOn_tangentMapWithin (le_refl 1) hUnique
  have hLift : Continuous (fun t : ℝ =>
      (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have h_homeo :
        Continuous ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
          ModelProd ℝ ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous
    exact h_homeo.comp (continuous_id.prodMk continuous_const)
  have hMaps : Set.MapsTo (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc a b) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc a b)) := by
    intro t ht
    simpa using ht
  have hComp : ContinuousOn
      (fun t : ℝ => tangentMapWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b)
        (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc a b) :=
    hTan.comp hLift.continuousOn hMaps
  refine hComp.congr ?_
  intro t _ht
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma continuousOn_g_speedSq_velocityWithin
    (g : SmoothRiemannianMetric I M) {η : ℝ → M} {a b : ℝ}
    (hVW : ContinuousOn
      (fun t : ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)) : TangentBundle I M))
      (Set.Icc a b)) :
    ContinuousOn
      (fun t : ℝ =>
        g.inner (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)))
      (Set.Icc a b) := by
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have h := ContinuousOn.inner_bundle (F := E) (B := M)
    (E := (TangentSpace I : M → Type _))
    (b := η)
    (v := fun t : ℝ => mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
    (w := fun t : ℝ => mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
    (s := Set.Icc a b) hVW hVW
  refine h.congr ?_
  intro t _ht
  rfl

lemma speedSqrt_integrableOn_Icc_of_C1
    (g : SmoothRiemannianMetric I M) {η : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc a b)) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.sqrt
        (g.inner (η t)
          (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))))
      (Set.Icc a b) MeasureTheory.volume := by
  classical
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · subst hab_eq
    rw [Set.Icc_self, MeasureTheory.integrableOn_singleton_iff]
    exact Or.inr (by simp)
  · have hVW := continuousOn_velocityWithin_totalSpace_C1 (I := I) (M := M)
      hab_lt hη
    have hSpeedSq := continuousOn_g_speedSq_velocityWithin (I := I) (M := M) g hVW
    have hSqrtW : ContinuousOn
        (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))))
        (Set.Icc a b) :=
      Real.continuous_sqrt.comp_continuousOn hSpeedSq
    have hIntW : MeasureTheory.IntegrableOn
        (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))))
        (Set.Icc a b) MeasureTheory.volume :=
      hSqrtW.integrableOn_Icc
    have hAgree : ∀ t ∈ Set.Ioo a b,
        Real.sqrt
            (g.inner (η t)
              (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
              (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)))
          = Real.sqrt
            (g.inner (η t)
              (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))) := by
      intro t ht
      have hmem : Set.Icc a b ∈ nhds t :=
        Icc_mem_nhds ht.1 ht.2
      rw [mfderivWithin_of_mem_nhds hmem]
    have hae : (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))))
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc a b)]
        (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)))) := by
      have hIoo_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
          t ∈ Set.Ioo a b := by
        rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
        exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
      filter_upwards [hIoo_ae] with t ht
      exact hAgree t ht
    exact hIntW.congr hae

section ENorm

variable [(x : M) → ENorm (TangentSpace I x)]

theorem pathELength_eq_arcLength_of_enorm_eq
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγint : IntegrableOn (fun t : ℝ => Real.sqrt
      (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) (Ioo a b))
    (hEnorm : ∀ t ∈ Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ =
      ENNReal.ofReal (Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    pathELength I γ a b = ENNReal.ofReal (Variation.arcLength (I := I) g γ a b) := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  unfold Variation.arcLength
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal hγint
      (ae_of_all _ (fun _ => Real.sqrt_nonneg _))]
  exact setLIntegral_congr_fun measurableSet_Ioo hEnorm

theorem riemannianEDist_le_arcLength_of_enorm_eq
    [(x : M) → ENormSMulClass ℝ (TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hEnorm : ∀ t ∈ Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ =
      ENNReal.ofReal (Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    riemannianEDist I (γ a) (γ b) ≤ ENNReal.ofReal (Variation.arcLength (I := I) g γ a b) := by
  exact (riemannianEDist_le_pathELength hγ rfl rfl hab).trans_eq
    (pathELength_eq_arcLength_of_enorm_eq (I := I) g hab
      ((speedSqrt_integrableOn_Icc_of_C1 (I := I) g hab hγ).mono_set Ioo_subset_Icc_self)
      hEnorm)

end ENorm

theorem pathELength_eq_arcLength
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b)
    (hγ_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.sqrt
        (g.inner (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) (Set.Icc a b) MeasureTheory.volume)
    (hEnorm : ∀ t ∈ Set.Icc a b,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ
          = ENNReal.ofReal (Real.sqrt
              (g.inner (γ t)
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    pathELength I γ a b
      = ENNReal.ofReal
        (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) := by
  exact pathELength_eq_arcLength_of_enorm_eq (I := I) g hab
    (hγ_int.mono_set Ioo_subset_Icc_self) (fun t ht => hEnorm t (Ioo_subset_Icc_self ht))

section RiemannianBundle

variable [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem pathELength_eq_arcLength_riemannianBundle
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b)
    (hγ_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.sqrt
        (g.inner (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) (Set.Icc a b) MeasureTheory.volume)
    (hEnorm : ∀ t ∈ Set.Icc a b,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ
          = ENNReal.ofReal (Real.sqrt
              (g.inner (γ t)
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    pathELength I γ a b
      = ENNReal.ofReal
        (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) := by
  exact pathELength_eq_arcLength_of_enorm_eq (I := I) g hab
    (hγ_int.mono_set Ioo_subset_Icc_self) (fun t ht => hEnorm t (Ioo_subset_Icc_self ht))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDist_le_arcLength
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc a b))
    (hEnorm : ∀ t ∈ Set.Icc a b,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ
          = ENNReal.ofReal (Real.sqrt
              (g.inner (γ t)
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    riemannianEDist I (γ a) (γ b)
      ≤ ENNReal.ofReal
        (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) := by
  exact riemannianEDist_le_arcLength_of_enorm_eq (I := I) g hab hγ
    (fun t ht => hEnorm t (Ioo_subset_Icc_self ht))

end RiemannianBundle

end DifferentialGeometry.Geometry.Riemannian.Geodesic
