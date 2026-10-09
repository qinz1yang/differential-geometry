import DifferentialGeometry.Geometry.Comparison.Variation.ExponentialTail
import DifferentialGeometry.Analysis.Calculus.Cutoff.IntervalCutoffEstimate
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion


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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem variation_velocity_mul_parameter
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f) (a t : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f (a * u) t) 0 (1 : ℝ) : E) =
      a • (mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) 0 (1 : ℝ) : E) := by
  have hcurve : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (fun u ↦ f u t) :=
    hf.comp (contMDiff_id.prodMk contMDiff_const)
  let A : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) →L[ℝ]
      TangentSpace 𝓘(ℝ, ℝ) (a * 0) :=
    modelLinearMapToTangent
      (x := (0 : ℝ)) (y := a * 0) (A := a • ContinuousLinearMap.id ℝ ℝ)
  have hscale : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun u : ℝ ↦ a * u) 0 A :=
    HasFDerivAt.hasMFDerivAt_model ((hasFDerivAt_id (0 : ℝ)).const_mul a)
  have hcomp := (hcurve.mdifferentiableAt (by norm_num)).hasMFDerivAt.comp 0 hscale
  have hmodel := congrArg tangentLinearMapToModel hcomp.mfderiv
  rw [tangentLinearMapToModel_comp] at hmodel
  have hA : tangentLinearMapToModel A = a • ContinuousLinearMap.id ℝ ℝ :=
    tangentLinearMapToModel_modelLinearMapToTangent
  rw [hA] at hmodel
  have happ := congrArg (fun L : ℝ →L[ℝ] E ↦ L 1) hmodel
  have hraw :
      (mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f (a * u) t) 0 (1 : ℝ) : E) =
        a • (mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) (a * 0) (1 : ℝ) : E) := by
    simp only [tangentLinearMapToModel_apply,
      tangentSpaceModelContinuousLinearEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_symm_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      Function.comp_apply, smul_apply, map_smul] at happ
    exact happ
  have hpoint :
      (mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) (a * 0) (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) 0 (1 : ℝ) : E) :=
    congrArg (fun x : ℝ ↦ (mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) x (1 : ℝ) : E))
      (mul_zero a)
  exact hraw.trans (congrArg (fun z : E ↦ a • z) hpoint)

theorem exists_uniform_smooth_tail_variation_with_geodesic_endpoint_norm_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
      {I : ModelWithCorners ℝ E H} [I.Boundaryless]
      {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [T2Space M],
      ∀ (g : SmoothRiemannianMetric I M)
      (gamma beta : ℝ → M) (L : ℝ), 0 < L →
      ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma →
      IsGeodesicAt (I := I) g beta 0 → beta 0 = gamma L →
      ∃ f : ℝ → ℝ → M,
        IsSmoothVariation (I := I) f ∧
        (∀ t ∈ Icc (0 : ℝ) L, f 0 =ᶠ[𝓝 t] gamma) ∧
        (∀ u, f u =ᶠ[𝓝 (0 : ℝ)] gamma) ∧
        (fun u ↦ f u L) =ᶠ[𝓝 (0 : ℝ)] beta ∧
        ∃ chi : ℝ → ℝ, ContDiff ℝ ∞ chi ∧
          chi =ᶠ[𝓝 (0 : ℝ)] 0 ∧ chi L = 1 ∧
          (∀ t, 0 ≤ chi t ∧ chi t ≤ 1) ∧
        ∃ V : ∀ t, TangentSpace I (f 0 t),
          ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
            (fun t ↦ (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
              (f 0 t) (V t) : TangentBundle I M)) ∧
          (∀ t ∈ Icc (0 : ℝ) L, covDerivAlong (I := I) g (f 0) V t = 0) ∧
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f 0 L) (V L) : TangentBundle I M) =
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (beta 0) (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)) : TangentBundle I M) ∧
          (∀ t ∈ Icc (0 : ℝ) L,
            g.inner (f 0 t) (V t) (V t) =
              g.inner (beta 0) (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))) ∧
        let Y : ∀ t, TangentSpace I (f 0 t) :=
          fun t ↦ mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) 0 (1 : ℝ)
        (∀ t ∈ Icc (0 : ℝ) L, Y t = (chi t * (t / L)) • V t) ∧
        (∀ t ∈ Icc (0 : ℝ) L,
          covDerivAlong (I := I) g (f 0) Y t =
            (deriv chi t * (t / L) + chi t / L) • V t) ∧
        (∀ t ∈ Icc (0 : ℝ) L,
          Real.sqrt (g.inner (f 0 t) (Y t) (Y t)) ≤
            Real.sqrt (g.inner (beta 0)
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)))) ∧
        (∀ t ∈ Icc (0 : ℝ) L,
          Real.sqrt (g.inner (f 0 t)
            (covDerivAlong (I := I) g (f 0) Y t)
            (covDerivAlong (I := I) g (f 0) Y t)) ≤
            C / L * Real.sqrt (g.inner (beta 0)
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)))) := by
  obtain ⟨D, hD, hstep⟩ := DifferentialGeometry.Analysis.exists_uniform_smooth_interval_step
  refine ⟨4 * D + 1, by positivity, ?_⟩
  intro E _ _ _ H _ I _ M _ _ _ _ g gamma beta L hL hgamma hbeta hbeta0
  obtain ⟨chi, hchi, _hchiMono, hchiRange, hchiZero, hchiOne, hchiDeriv⟩ :=
    hstep (L / 4) (L / 2) (by linarith)
  have hchiL : chi L = 1 := hchiOne L (by linarith)
  have hchiGerm : chi =ᶠ[𝓝 (0 : ℝ)] 0 := by
    filter_upwards [Iio_mem_nhds (by positivity : (0 : ℝ) < L / 4)] with t ht
    exact hchiZero t ht.le
  have hchiBound (t : ℝ) : |chi t| ≤ 1 := by
    rw [abs_of_nonneg (hchiRange t).1]
    exact (hchiRange t).2
  have hchiDerivBound (t : ℝ) : |deriv chi t| ≤ 4 * D / L := by
    have heq : D / (L / 2 - L / 4) = 4 * D / L := by
      rw [show L / 2 - L / 4 = L / 4 by ring,
        div_div_eq_mul_div, mul_comm D 4]
    exact (hchiDeriv t).trans_eq heq
  let v : TangentSpace I (gamma L) := mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)
  obtain ⟨Gamma, V, hVtotal, hGamma, hGammaGerm, hterminalV,
      _hVdiff, hVpar, hVnorm, W, hWtotal, hWradial, hWcov,
      K, hKcompact, hWmem⟩ :=
    exists_smooth_parallel_field_with_terminal g gamma hgamma L hL v
  obtain ⟨_eta, f0, _hetaSmooth, _hetaId, _hetaBound, hf0, hfcentral,
      hfField, _hfFix, hfTerminal⟩ :=
    exists_clamped_geodesic_variation_on_compactCarrier
      g Gamma (fun t ↦ (W t : E)) L univ K hWtotal hKcompact
      (fun t _ ↦ hWmem t) (mem_univ L)
  have hWL : (W L : E) = (v : E) := by
    rw [hWradial L ⟨hL.le, le_rfl⟩]
    have hVL : (V L : E) = (v : E) :=
      congrArg (fun q : TangentBundle I M ↦ q.snd) hterminalV
    simpa [hL.ne'] using hVL
  have hbetaGamma : beta 0 = Gamma L :=
    hbeta0.trans (hGamma L ⟨hL.le, le_rfl⟩).symm
  obtain ⟨B, hBproj, hBint, hB0⟩ :=
    exists_centered_lift_of_isGeodesicAt g beta (Gamma L) (W L)
      hbeta hbetaGamma hWL.symm
  have hterminal : (fun u ↦ f0 u L) =ᶠ[𝓝 (0 : ℝ)] beta :=
    hfTerminal beta B hBproj hBint hB0
  let f : ℝ → ℝ → M := fun u t ↦ f0 (chi t * u) t
  let Y : ∀ t, TangentSpace I (f 0 t) :=
    fun t ↦ mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) 0 (1 : ℝ)
  have hf : IsSmoothVariation (I := I) f := by
    have hchiM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (8 : ℕ) chi :=
      hchi.contMDiff.of_le (by
        change ((8 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
    exact hf0.comp (((hchiM.comp contMDiff_snd).mul contMDiff_fst).prodMk contMDiff_snd)
  have hcentral : f 0 = Gamma := by
    funext t
    simp only [f, mul_zero, hfcentral]
  have hY (t : ℝ) : (Y t : E) = chi t • (W t : E) := by
    exact (variation_velocity_mul_parameter (I := I) f0 hf0 (chi t) t).trans
      (congrArg (fun z : E ↦ chi t • z) (hfField t (mem_univ t)))
  have hnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      g.inner (Gamma t) (V t) (V t) =
        g.inner (beta 0) (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)) := by
    exact (hVnorm t ht).trans
      (congrArg (fun x : M ↦ g.inner x (v : E) (v : E)) hbeta0.symm)
  have hcov (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      (covDerivAlong (I := I) g (f 0) Y t : E) =
        (deriv chi t * (t / L) + chi t / L) • (V t : E) := by
    have htransport := covDerivAlong_congr_curve (I := I) (t := t) g
      (γ := f 0) (γ' := Gamma) Y (fun s ↦ chi s • W s)
      (Filter.Eventually.of_forall fun s ↦ congrFun hcentral s)
      (Filter.Eventually.of_forall hY)
    have hWdiff := chartRepAt_differentiableAt_of_total_contMDiffAt (I := I)
      (gamma := Gamma) (V := W) (t := t)
      (hWtotal.contMDiffAt.of_le (by norm_num : (2 : ℕ∞ω) ≤ 8))
    rw [htransport, covDerivAlong_smulFun g Gamma chi W t
      (hchi.differentiable (by simp) t) hWdiff,
      hWradial t ht, hWcov t ht, smul_smul, smul_smul, ← add_smul]
    congr 1
    ring
  refine ⟨f, hf, ?_, ?_, ?_, chi, hchi, hchiGerm, hchiL, hchiRange,
    (fun t ↦ (V t : E)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hfGamma : f 0 =ᶠ[𝓝 t] Gamma :=
      Filter.Eventually.of_forall fun s ↦ congrFun hcentral s
    exact hfGamma.trans (hGammaGerm t ht)
  · intro u
    filter_upwards [hchiGerm, hGammaGerm 0 ⟨le_rfl, hL.le⟩] with t ht hGt
    simp only [f, ht, Pi.zero_apply, zero_mul, hfcentral, hGt]
  · simpa only [f, hchiL, one_mul] using hterminal
  · have hVbase :
        (fun t ↦ (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f 0 t) (V t : E) : TangentBundle I M)) =
        (fun t ↦ (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (Gamma t) (V t) : TangentBundle I M)) := by
      funext t
      apply TotalSpace.ext
      · exact congrFun hcentral t
      · rfl
    rw [hVbase]
    exact hVtotal
  · intro t ht
    have htransport := covDerivAlong_congr_curve (I := I) (t := t) g
      (γ := f 0) (γ' := Gamma) (fun s ↦ (V s : E)) V
      (Filter.Eventually.of_forall fun s ↦ congrFun hcentral s)
      (Filter.Eventually.of_forall fun _ ↦ rfl)
    exact htransport.trans (hVpar t ht)
  · apply TotalSpace.ext
    · exact (congrFun hcentral L).trans hbetaGamma.symm
    · have hVL : (V L : E) = (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ) : E) :=
        congrArg (fun q : TangentBundle I M ↦ q.snd) hterminalV
      change HEq (V L : E) (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ) : E)
      exact heq_of_eq hVL
  · intro t ht
    rw [congrFun hcentral t]
    exact hnorm t ht
  · intro t ht
    exact (hY t).trans (by
      rw [hWradial t ht, smul_smul]
      rfl)
  · exact hcov
  · intro t ht
    change Real.sqrt (g.inner (f 0 t) (Y t) (Y t)) ≤ _
    rw [hY t, congrFun hcentral t, hWradial t ht, smul_smul,
      sqrt_inner_smul, hnorm t ht]
    have hratio : 0 ≤ t / L ∧ t / L ≤ 1 :=
      ⟨div_nonneg ht.1 hL.le, (div_le_one hL).mpr ht.2⟩
    have hcoef : |chi t * (t / L)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hratio.1]
      exact (mul_le_of_le_one_left hratio.1 (hchiBound t)).trans hratio.2
    exact (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)).trans_eq (one_mul _)
  · intro t ht
    change Real.sqrt (g.inner (f 0 t)
      (covDerivAlong (I := I) g (f 0) Y t)
      (covDerivAlong (I := I) g (f 0) Y t)) ≤ _
    rw [hcov t ht, congrFun hcentral t, sqrt_inner_smul, hnorm t ht]
    have hratio : 0 ≤ t / L ∧ t / L ≤ 1 :=
      ⟨div_nonneg ht.1 hL.le, (div_le_one hL).mpr ht.2⟩
    have hcoef : |deriv chi t * (t / L) + chi t / L| ≤ (4 * D + 1) / L := by
      calc
        _ ≤ |deriv chi t * (t / L)| + |chi t / L| := abs_add_le _ _
        _ = |deriv chi t| * (t / L) + |chi t| / L := by
          rw [abs_mul, abs_of_nonneg hratio.1, abs_div, abs_of_pos hL]
        _ ≤ 4 * D / L + 1 / L := by
          apply add_le_add
          · exact (mul_le_mul (hchiDerivBound t) hratio.2
              hratio.1 (by positivity)).trans_eq (mul_one _)
          · exact div_le_div_of_nonneg_right (hchiBound t) hL.le
        _ = (4 * D + 1) / L := (add_div _ _ _).symm
    exact mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)

theorem exists_smooth_tail_variation_with_geodesic_endpoint_norm_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : SmoothRiemannianMetric I M)
      (gamma beta : ℝ → M) (L : ℝ), 0 < L →
      ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma →
      IsGeodesicAt (I := I) g beta 0 → beta 0 = gamma L →
      ∃ f : ℝ → ℝ → M,
        IsSmoothVariation (I := I) f ∧
        (∀ t ∈ Icc (0 : ℝ) L, f 0 =ᶠ[𝓝 t] gamma) ∧
        (∀ u, f u =ᶠ[𝓝 (0 : ℝ)] gamma) ∧
        (fun u ↦ f u L) =ᶠ[𝓝 (0 : ℝ)] beta ∧
        ∃ chi : ℝ → ℝ, ContDiff ℝ ∞ chi ∧
          chi =ᶠ[𝓝 (0 : ℝ)] 0 ∧ chi L = 1 ∧
          (∀ t, 0 ≤ chi t ∧ chi t ≤ 1) ∧
        ∃ V : ∀ t, TangentSpace I (f 0 t),
          ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
            (fun t ↦ (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
              (f 0 t) (V t) : TangentBundle I M)) ∧
          (∀ t ∈ Icc (0 : ℝ) L, covDerivAlong (I := I) g (f 0) V t = 0) ∧
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f 0 L) (V L) : TangentBundle I M) =
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (beta 0) (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)) : TangentBundle I M) ∧
          (∀ t ∈ Icc (0 : ℝ) L,
            g.inner (f 0 t) (V t) (V t) =
              g.inner (beta 0) (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))) ∧
        let Y : ∀ t, TangentSpace I (f 0 t) :=
          fun t ↦ mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) 0 (1 : ℝ)
        (∀ t ∈ Icc (0 : ℝ) L, Y t = (chi t * (t / L)) • V t) ∧
        (∀ t ∈ Icc (0 : ℝ) L,
          covDerivAlong (I := I) g (f 0) Y t =
            (deriv chi t * (t / L) + chi t / L) • V t) ∧
        (∀ t ∈ Icc (0 : ℝ) L,
          Real.sqrt (g.inner (f 0 t) (Y t) (Y t)) ≤
            Real.sqrt (g.inner (beta 0)
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)))) ∧
        (∀ t ∈ Icc (0 : ℝ) L,
          Real.sqrt (g.inner (f 0 t)
            (covDerivAlong (I := I) g (f 0) Y t)
            (covDerivAlong (I := I) g (f 0) Y t)) ≤
            C / L * Real.sqrt (g.inner (beta 0)
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)))) := by
  obtain ⟨C, hC, hproducer⟩ :=
    exists_uniform_smooth_tail_variation_with_geodesic_endpoint_norm_bounds
  exact ⟨C, hC, hproducer⟩

end DifferentialGeometry.Geometry.Riemannian.Variation

end
