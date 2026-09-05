import DifferentialGeometry.Analysis.Calculus.Seminorm.Radial
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.VectorBundle.Riemannian

open Bundle Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J 1 N]

theorem Manifold.norm_sub_le_pathELength_comp_of_radial_bound
    [(x : N) → ENorm (TangentSpace J x)]
    (g : Bundle.ContinuousRiemannianMetric E (TangentSpace J : N → Type _))
    (hEnorm : ∀ (x : N) (v : TangentSpace J x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (F : V → N) {η : ℝ → V} {a b : ℝ}
    (hab : a ≤ b) (hη : ContDiffOn ℝ 1 η (Icc a b))
    (hF : ∀ x ∈ Icc a b, ContMDiffAt 𝓘(ℝ, V) J 1 F (η x))
    (hrad : ∀ x ∈ Ioo a b, ∀ v : V,
      Inner.inner ℝ (η x) v ≤ ‖η x‖ * Real.sqrt
        (g.inner (F (η x)) (mfderiv 𝓘(ℝ, V) J F (η x) v)
          (mfderiv 𝓘(ℝ, V) J F (η x) v))) :
    ENNReal.ofReal (‖η b‖ - ‖η a‖) ≤ Manifold.pathELength J (F ∘ η) a b := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · simp
  let γ : ℝ → N := F ∘ η
  let φ : ℝ → ℝ := fun t => Real.sqrt (g.inner (γ t)
    (mfderivWithin 𝓘(ℝ, ℝ) J γ (Icc a b) t 1)
    (mfderivWithin 𝓘(ℝ, ℝ) J γ (Icc a b) t 1))
  have hηm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, V) 1 η (Icc a b) := hη.contMDiffOn
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) J 1 γ (Icc a b) := by
    intro x hx
    exact (hF x hx).comp_contMDiffWithinAt x (hηm x hx)
  have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Icc a b) := fun x hx => by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact (uniqueDiffOn_Icc hab_lt) x hx
  have hLift : Continuous (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hMaps : MapsTo
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Icc a b) (Bundle.TotalSpace.proj ⁻¹' (Icc a b)) := fun _ ht => ht
  have hVel : ContinuousOn (fun t : ℝ =>
      TotalSpace.mk' E (E := (TangentSpace J : N → Type _)) (γ t)
        (mfderivWithin 𝓘(ℝ, ℝ) J γ (Icc a b) t 1)) (Icc a b) :=
    ((hγ.continuousOn_tangentMapWithin le_rfl hUnique).comp
      hLift.continuousOn hMaps).congr (fun _ _ => rfl)
  have hφc : ContinuousOn φ (Icc a b) := by
    intro t ht
    have h : ContinuousWithinAt (fun s => TotalSpace.mk' ℝ
        (E := Bundle.Trivial N ℝ) (γ s) (g.inner (γ s)
          (mfderivWithin 𝓘(ℝ, ℝ) J γ (Icc a b) s 1)
          (mfderivWithin 𝓘(ℝ, ℝ) J γ (Icc a b) s 1))) (Icc a b) t :=
      (g.continuous.continuousAt.comp_continuousWithinAt (hγ.continuousOn t ht)).clm_bundle_apply₂
        (F₁ := E) (F₂ := E) (hVel t ht) (hVel t ht)
    simp only [FiberBundle.continuousWithinAt_totalSpace] at h
    exact Real.continuous_sqrt.continuousAt.comp_continuousWithinAt h.2
  have hφint : IntervalIntegrable φ volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hφc
  have hφ_eq : ∀ t ∈ Ioo a b, φ t = Real.sqrt (g.inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) J γ t 1) (mfderiv 𝓘(ℝ, ℝ) J γ t 1)) := by
    intro t ht
    simp only [φ]
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  have hbound : ‖η b‖ - ‖η a‖ ≤ ∫ t in a..b, φ t := by
    apply hη.norm_sub_le_integral_of_inner_deriv_le hab hφint
      (fun _ _ => Real.sqrt_nonneg _)
    intro t ht
    have hηdiff : DifferentiableAt ℝ η t :=
      ((hη.differentiableOn one_ne_zero) t (Ioo_subset_Icc_self ht)).differentiableAt
        (Icc_mem_nhds ht.1 ht.2)
    have hchain : mfderiv 𝓘(ℝ, ℝ) J γ t 1 =
        mfderiv 𝓘(ℝ, V) J F (η t) (deriv η t) := by
      have hc := mfderiv_comp t
        ((hF t (Ioo_subset_Icc_self ht)).mdifferentiableAt one_ne_zero)
        hηdiff.mdifferentiableAt
      have h := congrArg (fun D : ℝ →L[ℝ] E => D 1) hc
      change mfderiv 𝓘(ℝ, ℝ) J (F ∘ η) t (1 : ℝ) =
        (mfderiv 𝓘(ℝ, V) J F (η t)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) η t 1) at h
      simpa only [γ, mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! h
    rw [hφ_eq t ht, hchain]
    exact hrad t ht (deriv η t)
  apply (ENNReal.ofReal_le_ofReal hbound).trans
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal
      (((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hφint).mono_set Ioo_subset_Icc_self)
      (by filter_upwards with t; exact Real.sqrt_nonneg _)]
  apply setLIntegral_mono_ae' measurableSet_Ioo
  filter_upwards with t ht
  rw [hφ_eq t ht]
  exact (hEnorm (γ t) (mfderiv 𝓘(ℝ, ℝ) J γ t 1)).symm.le
