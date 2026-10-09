import DifferentialGeometry.Geometry.Comparison.Variation.TailNormBounds
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic


noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open Bundle Filter Set
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped ContDiff Manifold Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem exists_uniform_smooth_interval_variation_with_geodesic_endpoint_norm_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
      {I : ModelWithCorners ℝ E H} [I.Boundaryless]
      {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [T2Space M],
      ∀ (g : SmoothRiemannianMetric I M)
      (gamma beta : ℝ → M) (c b : ℝ), c < b →
      ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma →
      IsGeodesicAt (I := I) g beta 0 → beta 0 = gamma b →
      ∃ f : ℝ → ℝ → M,
        IsSmoothVariation (I := I) f ∧
        (∀ t ∈ Icc c b, f 0 =ᶠ[𝓝 t] gamma) ∧
        (∀ u, f u =ᶠ[𝓝 c] gamma) ∧
        (fun u ↦ f u b) =ᶠ[𝓝 (0 : ℝ)] beta ∧
        ∃ chi : ℝ → ℝ, ContDiff ℝ ∞ chi ∧
          chi =ᶠ[𝓝 c] 0 ∧ chi b = 1 ∧
          (∀ t, 0 ≤ chi t ∧ chi t ≤ 1) ∧
        ∃ V : ∀ t, TangentSpace I (f 0 t),
          ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
            (fun t ↦ (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
              (f 0 t) (V t) : TangentBundle I M)) ∧
          (∀ t ∈ Icc c b, covDerivAlong (I := I) g (f 0) V t = 0) ∧
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f 0 b) (V b) : TangentBundle I M) =
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (beta 0) (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)) : TangentBundle I M) ∧
          (∀ t ∈ Icc c b,
            g.inner (f 0 t) (V t) (V t) =
              g.inner (beta 0) (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))) ∧
        let Y : ∀ t, TangentSpace I (f 0 t) :=
          fun t ↦ mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) 0 (1 : ℝ)
        (∀ t ∈ Icc c b, Y t = (chi t * ((t - c) / (b - c))) • V t) ∧
        (∀ t ∈ Icc c b,
          covDerivAlong (I := I) g (f 0) Y t =
            (deriv chi t * ((t - c) / (b - c)) + chi t / (b - c)) • V t) ∧
        (∀ t ∈ Icc c b,
          Real.sqrt (g.inner (f 0 t) (Y t) (Y t)) ≤
            Real.sqrt (g.inner (beta 0)
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)))) ∧
        (∀ t ∈ Icc c b,
          Real.sqrt (g.inner (f 0 t)
            (covDerivAlong (I := I) g (f 0) Y t)
            (covDerivAlong (I := I) g (f 0) Y t)) ≤
            C / (b - c) * Real.sqrt (g.inner (beta 0)
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)))) := by
  obtain ⟨C, hC, hproducer⟩ :=
    exists_uniform_smooth_tail_variation_with_geodesic_endpoint_norm_bounds
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ H _ I _ M _ _ _ _ g gamma beta c b hcb hgamma hbeta hbeta0
  let delta : ℝ → M := fun t ↦ gamma (c + t)
  have hdelta : ContMDiff 𝓘(ℝ, ℝ) I ∞ delta :=
    hgamma.comp (contMDiff_const.add contMDiff_id)
  have hbetaDelta : beta 0 = delta (b - c) := by
    simpa only [delta, add_sub_cancel] using hbeta0
  obtain ⟨f, hf, hcenter, hfix, hterminal, chi, hchi, hchiGerm, hchiEnd,
      hchiRange, V, hVtotal, hVpar, hVterminal, hVnorm, hY, hDY, hYbound, hDYbound⟩ :=
    hproducer g delta beta (b - c) (sub_pos.mpr hcb) hdelta hbeta hbetaDelta
  let F : ℝ → ℝ → M := fun u t ↦ f u (t - c)
  let Y : ∀ t, TangentSpace I (f 0 t) :=
    fun t ↦ mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) 0 (1 : ℝ)
  have hcentral : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (f 0) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  have hsub (t : ℝ) (ht : t ∈ Icc c b) : t - c ∈ Icc (0 : ℝ) (b - c) := by
    constructor <;> linarith [ht.1, ht.2]
  have hshift (Z : ∀ t, TangentSpace I (f 0 t))
      (hZ : ∀ t, DifferentiableAt ℝ (chartRepAt (I := I) (f 0) Z t) t)
      (t : ℝ) :
      (covDerivAlong (I := I) g (F 0) (fun s ↦ Z (s - c)) t : E) =
        (covDerivAlong (I := I) g (f 0) Z (t - c) : E) := by
    have hd : HasDerivAt (fun s : ℝ ↦ s - c) 1 t := (hasDerivAt_id t).sub_const c
    have hc := covDerivAlong_comp (I := I) g (f 0) Z (fun s ↦ s - c) t
      (hcentral.mdifferentiableAt (by norm_num)) (hZ (t - c)) hd.differentiableAt
    simpa only [F, hd.deriv, one_smul] using hc
  have hVdiff (t : ℝ) : DifferentiableAt ℝ
      (chartRepAt (I := I) (f 0) V t) t :=
    chartRepAt_differentiableAt_of_total_contMDiffAt (I := I)
      (hVtotal.contMDiffAt.of_le (by
        change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top))
  have hYdiff (t : ℝ) : DifferentiableAt ℝ
      (chartRepAt (I := I) (f 0) Y t) t :=
    variationField_chartRep_differentiableAt (I := I) f hf t
  have hchiShift (t : ℝ) : deriv (fun s ↦ chi (s - c)) t = deriv chi (t - c) := by
    have hd := (hchi.differentiable (by simp) (t - c)).hasDerivAt.comp t
      ((hasDerivAt_id t).sub_const c)
    have hdv := hd.deriv
    simp only [Function.comp_def, id_eq, mul_one] at hdv
    exact hdv
  refine ⟨F, ?_, ?_, ?_, ?_, (fun t ↦ chi (t - c)),
    hchi.comp (contDiff_id.sub contDiff_const), ?_, hchiEnd,
    (fun t ↦ hchiRange (t - c)), (fun t ↦ V (t - c)), ?_, ?_, hVterminal,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact hf.comp (contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const))
  · intro t ht
    have heq := (hcenter (t - c) (hsub t ht)).comp_tendsto
      (continuous_id.sub continuous_const).continuousAt
    filter_upwards [heq] with s hs
    change f 0 (s - c) = gamma (c + (s - c)) at hs
    rw [show c + (s - c) = s by ring] at hs
    exact hs
  · intro u
    have heq := (hfix u).comp_tendsto
      (show Tendsto (fun t : ℝ ↦ t - c) (𝓝 c) (𝓝 (0 : ℝ)) from by
        simpa only [id_eq, sub_self] using
          (continuousAt_id.sub_const c : ContinuousAt (fun t : ℝ ↦ t - c) c))
    filter_upwards [heq] with s hs
    change f u (s - c) = gamma (c + (s - c)) at hs
    rw [show c + (s - c) = s by ring] at hs
    exact hs
  · exact hterminal
  · exact hchiGerm.comp_tendsto (by
      simpa only [id_eq, sub_self] using
        (continuousAt_id.sub_const c : ContinuousAt (fun t : ℝ ↦ t - c) c))
  · exact hVtotal.comp (contMDiff_id.sub contMDiff_const)
  · intro t ht
    exact (hshift V hVdiff t).trans (hVpar (t - c) (hsub t ht))
  · intro t ht
    exact hVnorm (t - c) (hsub t ht)
  · intro t ht
    exact hY (t - c) (hsub t ht)
  · intro t ht
    change (covDerivAlong (I := I) g (F 0) (fun s ↦ Y (s - c)) t : E) = _
    rw [hshift Y hYdiff t, hchiShift t]
    exact hDY (t - c) (hsub t ht)
  · intro t ht
    exact hYbound (t - c) (hsub t ht)
  · intro t ht
    change Real.sqrt (g.inner (F 0 t)
      (covDerivAlong (I := I) g (F 0) (fun s ↦ Y (s - c)) t)
      (covDerivAlong (I := I) g (F 0) (fun s ↦ Y (s - c)) t)) ≤ _
    rw [hshift Y hYdiff t]
    exact hDYbound (t - c) (hsub t ht)

theorem exists_smooth_interval_variation_with_geodesic_endpoint_norm_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : SmoothRiemannianMetric I M)
      (gamma beta : ℝ → M) (c b : ℝ), c < b →
      ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma →
      IsGeodesicAt (I := I) g beta 0 → beta 0 = gamma b →
      ∃ f : ℝ → ℝ → M,
        IsSmoothVariation (I := I) f ∧
        (∀ t ∈ Icc c b, f 0 =ᶠ[𝓝 t] gamma) ∧
        (∀ u, f u =ᶠ[𝓝 c] gamma) ∧
        (fun u ↦ f u b) =ᶠ[𝓝 (0 : ℝ)] beta ∧
        ∃ chi : ℝ → ℝ, ContDiff ℝ ∞ chi ∧
          chi =ᶠ[𝓝 c] 0 ∧ chi b = 1 ∧
          (∀ t, 0 ≤ chi t ∧ chi t ≤ 1) ∧
        ∃ V : ∀ t, TangentSpace I (f 0 t),
          ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
            (fun t ↦ (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
              (f 0 t) (V t) : TangentBundle I M)) ∧
          (∀ t ∈ Icc c b, covDerivAlong (I := I) g (f 0) V t = 0) ∧
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f 0 b) (V b) : TangentBundle I M) =
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (beta 0) (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)) : TangentBundle I M) ∧
          (∀ t ∈ Icc c b,
            g.inner (f 0 t) (V t) (V t) =
              g.inner (beta 0) (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))) ∧
        let Y : ∀ t, TangentSpace I (f 0 t) :=
          fun t ↦ mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) 0 (1 : ℝ)
        (∀ t ∈ Icc c b, Y t = (chi t * ((t - c) / (b - c))) • V t) ∧
        (∀ t ∈ Icc c b,
          covDerivAlong (I := I) g (f 0) Y t =
            (deriv chi t * ((t - c) / (b - c)) + chi t / (b - c)) • V t) ∧
        (∀ t ∈ Icc c b,
          Real.sqrt (g.inner (f 0 t) (Y t) (Y t)) ≤
            Real.sqrt (g.inner (beta 0)
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)))) ∧
        (∀ t ∈ Icc c b,
          Real.sqrt (g.inner (f 0 t)
            (covDerivAlong (I := I) g (f 0) Y t)
            (covDerivAlong (I := I) g (f 0) Y t)) ≤
            C / (b - c) * Real.sqrt (g.inner (beta 0)
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)))) := by
  obtain ⟨C, hC, hproducer⟩ :=
    exists_uniform_smooth_interval_variation_with_geodesic_endpoint_norm_bounds
  exact ⟨C, hC, hproducer⟩

end DifferentialGeometry.Geometry.Riemannian.Variation

end
