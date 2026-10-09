import DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set MeasureTheory TopologicalSpace
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Integral.Measure

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩
private local instance (U : Opens M) : MeasurableSpace U := borel U
private local instance (U : Opens M) : BorelSpace U := ⟨rfl⟩
private local instance (V : Opens N) : MeasurableSpace V := borel V
private local instance (V : Opens N) : BorelSpace V := ⟨rfl⟩

theorem setLIntegral_image_partialDiffeomorph
    (Phi : PartialDiffeomorph I J M N ∞)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (U : Opens M) (hU : (U : Set M) ⊆ Phi.source)
    (hmetric : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (Phi x) (mfderiv I J Phi x v) (mfderiv I J Phi x w))
    {A : Set M} (hA : MeasurableSet A) (hAU : A ⊆ U) (f : N → ℝ≥0∞) :
    ∫⁻ y in Phi '' A, f y ∂riemannianVolumeMeasure (I := J) (M := N) h =
      ∫⁻ x in A, f (Phi x) ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  let V : Opens N := ⟨Phi '' (U : Set M), image_opens_isOpen Phi hU⟩
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen J V.isOpen)
  let e : U ≃ₘ⟮I, J⟯ V := PartialDiffeomorph.toOpensDiffeo Phi hU
  have hpull : g.restrictOpen U = Diffeomorph.pullbackMetricCross (h.restrictOpen V) e := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    change g.inner (x : M) v w = h.inner (Phi x) (mfderiv I J e x v) (mfderiv I J e x w)
    rw [PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU,
      PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU]
    exact hmetric x x.property v w
  have himage : MeasurableSet (Phi '' A) := by
    have hv : MeasurableEmbedding (Subtype.val : V → N) :=
      V.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding (mα := borel V)
    have he : MeasurableEmbedding (e : U → V) := e.toHomeomorph.measurableEmbedding
    have hm := hv.measurableSet_image.mpr
      (he.measurableSet_image.mpr ((continuous_subtype_val : Continuous (Subtype.val : U → M)).measurable hA))
    have hset : (Subtype.val : V → N) '' (e '' ((Subtype.val : U → M) ⁻¹' A)) = Phi '' A := by
      ext y
      constructor
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨e ⟨x, hAU hx⟩, ⟨⟨x, hAU hx⟩, hx, rfl⟩, rfl⟩
    rwa [hset] at hm
  have hpre : e.symm ⁻¹' (Subtype.val ⁻¹' A) = (Subtype.val : V → N) ⁻¹' (Phi '' A) := by
    ext y
    constructor
    · intro hy
      exact ⟨(e.symm y : M), hy, congrArg Subtype.val (e.apply_symm_apply y)⟩
    · rintro ⟨x, hx, heq⟩
      have hxy : e (⟨x, hAU hx⟩ : U) = y := Subtype.ext heq
      have hxy' : e.symm y = (⟨x, hAU hx⟩ : U) := by
        rw [← hxy, e.symm_apply_apply]
      change (e.symm y : M) ∈ A
      rw [hxy']
      exact hx
  have he : MeasurableEmbedding (e.symm : V → U) := e.symm.toHomeomorph.measurableEmbedding
  have hchange := he.lintegral_map
    (μ := (riemannianVolumeMeasure (I := J) (M := V) (h.restrictOpen V)).restrict
      (e.symm ⁻¹' (Subtype.val ⁻¹' A)))
    (fun x : U => f (Phi (x : M)))
  rw [← he.restrict_map,
    ← riemannianVolumeMeasure_pullback_cross (h.restrictOpen V) e, ← hpull, hpre] at hchange
  have hfun (y : V) : f (Phi (e.symm y : M)) = f (y : N) :=
    congrArg f (congrArg Subtype.val (e.apply_symm_apply y))
  simp only [hfun] at hchange
  rw [Geometry.Measure.setLIntegral_restrictOpen g U hA hAU (fun x => f (Phi x))] at hchange
  rw [Geometry.Measure.setLIntegral_restrictOpen h V himage (image_mono hAU) f] at hchange
  exact hchange.symm

end DifferentialGeometry.Integral.Measure
