import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {D : RealTimeInterval}

theorem continuousOn_lDensity
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (gamma : ℝ → M) {s : Set ℝ}
    (hs : IsOpen s) (hG : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hR : ContinuousOn (fun q : ℝ × M => S.scalar q.1 q.2) (D.carrier ×ˢ univ))
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma s)
    (hback : MapsTo (fun tau : ℝ => T - tau) s D.carrier) :
    ContinuousOn (lDensity S T gamma) s := by
  have hunit : Continuous (fun tau : ℝ =>
      (⟨tau, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hvelWithin : ContinuousOn
      (fun tau : ℝ => tangentMapWithin 𝓘(ℝ, ℝ) I gamma s
        (⟨tau, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) s :=
    (hgamma.continuousOn_tangentMapWithin le_rfl hs.uniqueMDiffOn).comp
      hunit.continuousOn (fun _ htau => htau)
  have hvelOn : ContinuousOn
      (fun tau : ℝ => tangentMap 𝓘(ℝ, ℝ) I gamma
        (⟨tau, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) s := by
    refine hvelWithin.congr ?_
    intro tau htau
    simp only [tangentMapWithin, tangentMap, mfderivWithin_of_isOpen hs htau]
  let timeLift : s → D.carrier := fun tau => ⟨T - tau.1, hback tau.2⟩
  let velocityLift : s → TangentBundle I M := fun tau =>
    tangentMap 𝓘(ℝ, ℝ) I gamma
      (⟨tau.1, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)
  have htime : Continuous timeLift :=
    (continuous_const.sub continuous_subtype_val).subtype_mk _
  have hvel : Continuous velocityLift :=
    continuousOn_iff_continuous_domRestrict.mp hvelOn
  have hquad := metricTimeBundleQuad_cont_of_metricFamilySmoothOn
    S.family.metric hG (K := D.carrier) Subset.rfl
  have hspeed : ContinuousOn (lSpeedSq S T gamma) s := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply (hquad.comp (htime.prodMk hvel)).congr
    intro tau
    rfl
  have hpair : ContinuousOn (fun tau : ℝ => (T - tau, gamma tau)) s :=
    (continuous_const.sub continuous_id).continuousOn.prodMk hgamma.continuousOn
  have hmaps : MapsTo (fun tau : ℝ => (T - tau, gamma tau)) s (D.carrier ×ˢ univ) :=
    fun _ htau => ⟨hback htau, mem_univ _⟩
  have hscalar : ContinuousOn (fun tau : ℝ => S.scalar (T - tau) (gamma tau)) s := by
    simpa only [Function.comp_def] using hR.comp hpair hmaps
  change ContinuousOn (fun tau : ℝ =>
    Real.sqrt tau * (S.scalar (T - tau) (gamma tau) + lSpeedSq S T gamma tau)) s
  exact Real.continuous_sqrt.continuousOn.mul (hscalar.add hspeed)

theorem aestronglyMeasurable_lDensity
    (S : SolutionOn (I := I) (M := M) D) (T a b : ℝ) (gamma : ℝ → M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hR : ContinuousOn (fun q : ℝ × M => S.scalar q.1 q.2) (D.carrier ×ˢ univ))
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Ioo a b))
    (hback : MapsTo (fun tau : ℝ => T - tau) (Ioo a b) D.carrier) :
    AEStronglyMeasurable (lDensity S T gamma) (volume.restrict (Ioc a b)) := by
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact (continuousOn_lDensity S T gamma isOpen_Ioo hG hR hgamma hback).aestronglyMeasurable
    measurableSet_Ioo

end DifferentialGeometry.PDE.RicciFlow.Perelman
