import DifferentialGeometry.Geometry.Thurston.Regressions
import DifferentialGeometry.Geometry.Metric.Completeness.ProperMap
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryFlat

/-!
# Metric and model descent along folds

Surjective local diffeomorphisms descend compatible smooth metrics and model atlases.
Local ambient isometries preserving the fold on open neighbourhoods give fibre compatibility.
Target completeness is supplied separately, either by compactness or a proper function with
bounded differential. The nonhyperbolic assembly includes a flat interval-block regression.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry
open scoped Manifold ContDiff Topology

namespace GC.Geometry

variable {E H X M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
  [TopologicalSpace M] [ChartedSpace H M] [hM : IsManifold I ∞ M] [hT2M : T2Space M]

theorem HasThurstonAtlas.foldRestrictOpen {g : SmoothRiemannianMetric I X}
    {k : ThurstonModel} (hg : HasThurstonAtlas g k) (N : TopologicalSpace.Opens X) :
    HasThurstonAtlas (g.restrictOpen N) k :=
  hg.restrictOpen N

omit hM hT2M in
theorem metricFiberCompatible_of_foldPairs [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I X)
    (N : TopologicalSpace.Opens X) (F : N → M) (hF : IsLocalDiffeomorph I I ∞ F)
    (hpair : ∀ y y' : N, F y = F y' → ∃ γ : X ≃ₘ⟮I, I⟯ X,
      Diffeomorph.pullbackMetric g γ = g ∧ γ (y : X) = (y' : X) ∧
        ∃ U : TopologicalSpace.Opens X, (y : X) ∈ U ∧
          ∃ hUN : (U : Set X) ⊆ N, ∃ hmaps : Set.MapsTo γ (U : Set X) N,
            ∀ z : U, F ⟨γ (z : X), hmaps z.property⟩ =
              F ⟨(z : X), hUN z.property⟩) :
    metricFiberCompatible (g.restrictOpen N) F hF := by
  intro y y' hyy
  obtain ⟨γ, hmetric, hγ, U, hyU, hUN, hmaps, hdeck⟩ := hpair y y' hyy
  let u : U := ⟨(y : X), hyU⟩
  let Ψ : U → N := fun z => ⟨γ (z : X), hmaps z.property⟩
  let ι : U → N := TopologicalSpace.Opens.inclusion hUN
  have hΨ : ContMDiff I I ∞ Ψ := by
    apply (ContMDiff.subtypeVal_comp_iff N Ψ).1
    exact γ.contMDiff.comp (contMDiff_subtype_val (U := U))
  have hΨu : Ψ u = y' := Subtype.ext hγ
  have hιu : ι u = y := rfl
  have hΨder (v : TangentSpace I y) :
      mfderiv I I Ψ u v = mfderiv I I γ (y : X) v := by
    have hval := mfderiv_comp_apply u
      ((contMDiff_subtype_val (I := I) (n := ∞) (U := N)).mdifferentiableAt (by decide))
      (hΨ.mdifferentiableAt (by decide)) v
    have hamb := mfderiv_comp_apply u
      (γ.contMDiff.mdifferentiableAt (by decide))
      ((contMDiff_subtype_val (I := I) (n := ∞) (U := U)).mdifferentiableAt (by decide)) v
    erw [mfderiv_subtype_val_apply] at hval hamb
    exact hval.symm.trans hamb
  have hchain (v : TangentSpace I y) :
      mfderiv I I F y' (mfderiv I I γ (y : X) v) = mfderiv I I F y v := by
    have heq : F ∘ Ψ = F ∘ ι := funext hdeck
    have hleft := mfderiv_comp_apply u
      (hF.contMDiff.mdifferentiableAt (by decide))
      (hΨ.mdifferentiableAt (by decide)) v
    have hright := mfderiv_comp_apply u
      (hF.contMDiff.mdifferentiableAt (by decide))
      ((contMDiff_inclusion (I := I) (n := ∞) hUN).mdifferentiableAt (by decide)) v
    rw [heq] at hleft
    rw [hΨder, hΨu] at hleft
    erw [mfderiv_opens_incl] at hright
    change mfderiv I I (F ∘ ι) u v = mfderiv I I F y v at hright
    exact hleft.symm.trans hright
  let A := hF.mfderivToContinuousLinearEquiv infty_ne_zero y
  let B := hF.mfderivToContinuousLinearEquiv infty_ne_zero y'
  have hinv (v : E) : B.symm v = mfderiv I I γ (y : X) (A.symm v) := by
    apply B.injective
    erw [B.apply_symm_apply]
    change v = mfderiv I I F y' (mfderiv I I γ (y : X) (A.symm v))
    rw [hchain]
    exact (A.apply_symm_apply v).symm
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [cast_localPushInner_apply, localPushInner_apply]
  have hcast (a b : M) (hab : a = b) (D : E ≃L[ℝ] TangentSpace I a) :
      (hab ▸ D : E ≃L[ℝ] TangentSpace I b) = D := by
    cases hab
    rfl
  erw [hcast]
  change (g.restrictOpen N).inner y (A.symm v) (A.symm w) =
    (g.restrictOpen N).inner y' (B.symm v) (B.symm w)
  rw [SmoothRiemannianMetric.restrictOpen_inner, SmoothRiemannianMetric.restrictOpen_inner]
  erw [hinv, hinv]
  have hiso := Diffeomorph.pullbackMetric_inner g γ (y : X) (A.symm v) (A.symm w)
  rw [hmetric, hγ] at hiso
  exact hiso

def foldMetric (g : SmoothRiemannianMetric I X) (F : X → M)
    (hF : IsLocalDiffeomorph I I ∞ F) (hsurj : Function.Surjective F)
    (hcompat : metricFiberCompatible g F hF) : SmoothRiemannianMetric I M :=
  descendedMetric g F hF hsurj hcompat

theorem foldMetric_pullback (g : SmoothRiemannianMetric I X) (F : X → M)
    (hF : IsLocalDiffeomorph I I ∞ F) (hsurj : Function.Surjective F)
    (hcompat : metricFiberCompatible g F hF) :
    localPullMetric (foldMetric g F hF hsurj hcompat) F hF = g :=
  localPullMetric_descendedMetric g F hF hsurj hcompat

theorem foldMetric_atlas (g : SmoothRiemannianMetric I X) (F : X → M)
    (hF : IsLocalDiffeomorph I I ∞ F) (hsurj : Function.Surjective F)
    (hcompat : metricFiberCompatible g F hF) {k : ThurstonModel}
    (hg : HasThurstonAtlas g k) : HasThurstonAtlas (foldMetric g F hF hsurj hcompat) k :=
  hg.descend hF hsurj (foldMetric_pullback g F hF hsurj hcompat)

theorem foldMetric_complete_of_compact [CompactSpace M] (g : SmoothRiemannianMetric I X)
    (F : X → M) (hF : IsLocalDiffeomorph I I ∞ F) (hsurj : Function.Surjective F)
    (hcompat : metricFiberCompatible g F hF) :
    RiemannianMetricComplete (foldMetric g F hF hsurj hcompat) :=
  RiemannianMetricComplete.of_compact _

theorem foldMetric_complete_of_proper [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I X) (F : X → M) (hF : IsLocalDiffeomorph I I ∞ F)
    (hsurj : Function.Surjective F) (hcompat : metricFiberCompatible g F hF)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 1 f) (hp : IsProperMap f)
    {C : NNReal} (hC : 0 < C)
    (hb : ∀ y : X, ∀ v : TangentSpace I y,
      ‖mfderiv I 𝓘(ℝ) (f ∘ F) y v‖ ≤ C * Real.sqrt (g.inner y v v)) :
    RiemannianMetricComplete (foldMetric g F hF hsurj hcompat) := by
  apply RiemannianMetricComplete.of_isProperMap_of_mfderiv_bound _ hf hp hC
  intro x v
  obtain ⟨y, rfl⟩ := hsurj x
  let D := hF.mfderivToContinuousLinearEquiv infty_ne_zero y
  have hD : mfderiv I I F y (D.symm v) = v := D.apply_symm_apply v
  have hder := mfderiv_comp_apply y (hf.mdifferentiableAt (by decide))
    (hF.contMDiff.mdifferentiableAt (by decide)) (D.symm v)
  rw [hD] at hder
  have hbound := hb y (D.symm v)
  rw [hder] at hbound
  have hinner := congrArg
    (fun metric : SmoothRiemannianMetric I X => metric.inner y (D.symm v) (D.symm v))
    (foldMetric_pullback g F hF hsurj hcompat)
  rw [localPullMetric_inner, hD] at hinner
  rw [← hinner] at hbound
  exact hbound

def GeometricStructure.ofFold [SigmaCompactSpace M] (g : SmoothRiemannianMetric I X)
    {k : ThurstonModel} (hg : HasThurstonAtlas g k) (hk : k ≠ .hyperbolic)
    (F : X → M) (hF : IsLocalDiffeomorph I I ∞ F) (hsurj : Function.Surjective F)
    (hcompat : metricFiberCompatible g F hF)
    (hcomplete : RiemannianMetricComplete (foldMetric g F hF hsurj hcompat)) :
    GeometricStructure I M where
  model := k
  metric := foldMetric g F hF hsurj hcompat
  complete := hcomplete
  atlas := foldMetric_atlas g F hF hsurj hcompat hg
  hyperbolic_finite_volume := fun hmodel => (hk hmodel).elim

theorem GeometricStructure.ofFold_model [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I X) {k : ThurstonModel} (hg : HasThurstonAtlas g k)
    (hk : k ≠ .hyperbolic) (F : X → M) (hF : IsLocalDiffeomorph I I ∞ F)
    (hsurj : Function.Surjective F) (hcompat : metricFiberCompatible g F hF)
    (hcomplete : RiemannianMetricComplete (foldMetric g F hF hsurj hcompat)) :
    (GeometricStructure.ofFold g hg hk F hF hsurj hcompat hcomplete).model = k :=
  rfl

theorem foldMetric_eq_pullback (g : SmoothRiemannianMetric I X) (Φ : M ≃ₘ⟮I, I⟯ X)
    (hcompat : metricFiberCompatible g Φ.symm Φ.symm.isLocalDiffeomorph) :
    foldMetric g Φ.symm Φ.symm.isLocalDiffeomorph Φ.symm.surjective hcompat =
      Diffeomorph.pullbackMetricCross g Φ := by
  apply localPullMetric_injective_of_surjective Φ.symm Φ.symm.isLocalDiffeomorph
    Φ.symm.surjective
  rw [foldMetric_pullback, ← Diffeomorph.pullbackMetricCross_eq_localPullMetric]
  exact (Diffeomorph.pullbackMetricCross_symm_eq_iff
    (g := g) (Φ := Φ)).mp rfl |>.symm

end GC.Geometry

namespace GC.Seifert

open GC.Geometry GC.Endpoint
universe u

def T2Interval.interiorGeometryOfFold {W : CompactCarrier.{u}} (B : T2Interval W) :
    B.presentation.cutCarrier.InteriorGeometry
      (B.presentation.components.piece (B.piece none)) := by
  letI := DifferentialGeometry.Manifold.interiorChartedSpace
    B.presentation.cutCarrier.model ∞
    (M := B.presentation.cutCarrier.pieceInterior
      (B.presentation.components.piece (B.piece none)))
  letI := DifferentialGeometry.Manifold.interiorIsManifold
    B.presentation.cutCarrier.model ∞
    (M := B.presentation.cutCarrier.pieceInterior
      (B.presentation.components.piece (B.piece none)))
  let Φ := (DifferentialGeometry.Manifold.interiorAtlasDiffeomorph
    B.presentation.cutCarrier.model ∞).symm.trans B.interiorDiffeo
  have hcompat : metricFiberCompatible torusTimesLineGeometry.metric Φ.symm
      Φ.symm.isLocalDiffeomorph := by
    intro x y hxy
    have heq := Φ.symm.injective hxy
    subst y
    rfl
  have hcomplete : RiemannianMetricComplete
      (foldMetric torusTimesLineGeometry.metric Φ.symm Φ.symm.isLocalDiffeomorph
        Φ.symm.surjective hcompat) := by
    rw [foldMetric_eq_pullback]
    exact DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_pullbackMetricCross
      torusTimesLineGeometry.complete Φ
  exact GeometricStructure.ofFold torusTimesLineGeometry.metric torusTimesLineGeometry.atlas
    (by decide) Φ.symm Φ.symm.isLocalDiffeomorph Φ.symm.surjective hcompat hcomplete

theorem T2Interval.interiorGeometryOfFold_model {W : CompactCarrier.{u}} (B : T2Interval W) :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace
      B.presentation.cutCarrier.model ∞
      (M := B.presentation.cutCarrier.pieceInterior
        (B.presentation.components.piece (B.piece none)))
    letI := DifferentialGeometry.Manifold.interiorIsManifold
      B.presentation.cutCarrier.model ∞
      (M := B.presentation.cutCarrier.pieceInterior
        (B.presentation.components.piece (B.piece none)))
    B.interiorGeometryOfFold.model = B.interiorGeometry.model :=
  rfl

end GC.Seifert
