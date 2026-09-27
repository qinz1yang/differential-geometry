import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Manifold MeasureTheory Bundle TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.Geometry.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance (U : Opens E) : MeasurableSpace U := borel U
private local instance (U : Opens E) : BorelSpace U := ⟨rfl⟩
private local instance (U : Opens E) : LocallyCompactSpace U := U.isOpen.locallyCompactSpace

private def openParam (U : Opens E) (x : U) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E U 1 where
  toPartialEquiv := (chartAt E x).symm.toPartialEquiv
  open_source := (chartAt E x).open_target
  open_target := (chartAt E x).open_source
  contMDiffOn_toFun := contMDiffOn_chart_symm
  contMDiffOn_invFun := contMDiffOn_chart

omit [FiniteDimensional ℝ E] in
private theorem openParam_target (U : Opens E) (x : U) : (openParam U x).target = univ := by
  change ((OpenPartialHomeomorph.refl E).subtypeRestr (s := U) ⟨x⟩).source = univ
  rw [OpenPartialHomeomorph.subtypeRestr_source]
  rfl

private def pullParam {U : Opens E} (D : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ U)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E U 1) :
    PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
  Ψ.trans ({ toEquiv := D.symm.toEquiv
             contMDiff_toFun := D.symm.contMDiff.of_le (by norm_num)
             contMDiff_invFun := D.contMDiff.of_le (by norm_num) } : U ≃ₘ^1⟮𝓘(ℝ, E), I⟯ M).toPartialDiffeomorph

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem pullParam_source {U : Opens E} (D : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ U)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E U 1) :
    (pullParam D Ψ).source = Ψ.source := by
  change Ψ.source ∩ Ψ ⁻¹' univ = Ψ.source
  simp only [preimage_univ, inter_univ]

private theorem pullParam_density [T2Space M] {U : Opens E}
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) U) (D : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ U)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E U 1)
    {w : E} (hw : w ∈ Ψ.source) :
    paramDensity (Diffeomorph.pullbackMetricCross g D) (pullParam D Ψ) w =
      paramDensity g Ψ w := by
  have he : (D ∘ pullParam D Ψ : E → U) = Ψ := funext fun z => D.apply_symm_apply (Ψ z)
  have hd := congrArg (β := E →L[ℝ] E) (fun f : E → U => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f w) he
  rw [mfderiv_comp w (D.contMDiff.mdifferentiableAt (by decide))
    ((pullParam D Ψ).mdifferentiableAt (by norm_num) (by rwa [pullParam_source]))] at hd
  rw [paramDensity_apply, paramDensity_apply]
  congr 2
  ext i j
  simp only [paramGramMatrix_apply, Diffeomorph.pullbackMetricCross_inner]
  have hv (v : E) : mfderiv I 𝓘(ℝ, E) D (pullParam D Ψ w)
      (mfderiv 𝓘(ℝ, E) I (pullParam D Ψ) w v) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ w v :=
    congrArg (fun L => L v) hd
  rw [hv, hv]
  exact congrArg (fun x => g.inner x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))) (congrFun he w)

omit [IsManifold I ∞ M] in
private theorem diffeo_sigmaCompact {U : Opens E} (D : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ U) :
    SigmaCompactSpace M := by
  let : SecondCountableTopology M := D.toHomeomorph.secondCountableTopology
  let : LocallyCompactSpace M := D.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  infer_instance

theorem riemannianVolumeMeasure_pullbackOpen_preimage {U : Opens E}
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) U) (D : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ U)
    {S : Set U} (hS : MeasurableSet S) :
    letI : T2Space M := D.toHomeomorph.isEmbedding.t2Space
    letI : SigmaCompactSpace M := diffeo_sigmaCompact D
    riemannianVolumeMeasure I M (Diffeomorph.pullbackMetricCross g D) (D ⁻¹' S) =
      riemannianVolumeMeasure 𝓘(ℝ, E) U g S := by
  let : T2Space M := D.toHomeomorph.isEmbedding.t2Space
  let : SecondCountableTopology M := D.toHomeomorph.secondCountableTopology
  let : LocallyCompactSpace M := D.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp only [preimage_empty, measure_empty]
  let Ψ := openParam U x
  have htarget : S ⊆ Ψ.target := by rw [show Ψ.target = univ from openParam_target U x]; exact subset_univ S
  let K := Ψ.symm '' S
  have hK : MeasurableSet K := measurableSet_symm_image_param Ψ hS htarget
  have hsource : K ⊆ Ψ.source := by
    rintro w ⟨y, hy, rfl⟩
    exact Ψ.toPartialEquiv.map_target (htarget hy)
  have himage : (pullParam D Ψ) '' K = D ⁻¹' S := by
    ext p
    constructor
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      change D (D.symm (Ψ (Ψ.symm y))) ∈ S
      have he : Ψ (Ψ.symm y) = y := Ψ.toPartialEquiv.right_inv (htarget hy)
      rw [D.apply_symm_apply, he]
      exact hy
    · intro hp
      refine ⟨Ψ.symm (D p), ⟨D p, hp, rfl⟩, ?_⟩
      change D.symm (Ψ (Ψ.symm (D p))) = p
      have he : Ψ (Ψ.symm (D p)) = D p := Ψ.toPartialEquiv.right_inv (htarget hp)
      rw [he, D.symm_apply_apply]
  rw [← himage, riemannianVolumeMeasure_image_param_eq _ _ hK
    (by simpa only [pullParam_source] using hsource)]
  rw [riemannianVolumeMeasure_param_target_eq g Ψ hS htarget]
  apply setLIntegral_congr_fun hK
  intro w hw
  exact congrArg ENNReal.ofReal (pullParam_density g D Ψ (hsource hw))

end DifferentialGeometry.Geometry.Measure
