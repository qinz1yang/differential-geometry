import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Graphical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductProjection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SobolevExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicGaugeLocalExistence
import DifferentialGeometry.Geometry.Metric.Family.Stationary

noncomputable section

open scoped Manifold ContDiff
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

open DifferentialGeometry.Geometry.Curvature

theorem exists_smooth_parametric_curve_of_graph
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (F₀ : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, F), F⟯) :
    ∃ T : ℝ, 0 < T ∧ ∃ c : CurveMap (AddCircle (1 : ℝ) × F),
      c.SmoothOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (Icc 0 T) ∧
      c.ImmersedOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (Icc 0 T) ∧
      (∀ z, c z 0 = (z, F₀ z)) ∧
      ∀ x t, t ∈ Icc 0 T →
        c.velocity (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (Icc 0 T) x t =
          c.speed (fun _ => AddCircle.flatMetric.prod
            (euclideanMetric (E := F))) x t ^ (-2 : ℤ) •
            c.Dx (fun _ => AddCircle.flatMetric.prod
              (euclideanMetric (E := F))) c.X x t := by
  let c₀ : SmoothImmersion (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
      (M := AddCircle (1 : ℝ) × F) :=
    { map := fun z => (z, F₀ z)
      smooth := AddCircle.contMDiff_coe.prodMk (F₀.contMDiff.comp AddCircle.contMDiff_coe)
      immersed := by
        intro x hzero
        erw [mfderiv_prodMk (AddCircle.contMDiff_coe.mdifferentiableAt (by decide))
          ((F₀.contMDiff.comp AddCircle.contMDiff_coe).mdifferentiableAt (by decide))] at hzero
        apply AddCircle.parameterTangent_ne_zero (x : AddCircle (1 : ℝ))
        exact (AddCircle.parameterTangent_coe x).trans (congrArg Prod.fst hzero) }
  let g : SmoothRiemannianMetric (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
      (AddCircle (1 : ℝ) × F) :=
    AddCircle.flatMetric.prod (euclideanMetric (E := F))
  have hg : MetricFamilySmoothOn (RealTimeInterval.univ 0) (fun _ => g) :=
    metricFamilySmoothOn_stationary g (RealTimeInterval.univ 0)
  exact SmoothImmersion.exists_parametric_solution_prod_of_compact c₀ (fun _ => g)
    (mem_univ 0) hg

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem parabolic_equation_congr
    {c d : CurveMap M} {J : Set ℝ} {g : ℝ → SmoothRiemannianMetric I M}
    (h : ∀ x t, t ∈ J → c.lift x t = d.lift x t)
    {x t : ℝ} (ht : t ∈ J)
    (heq : c.velocity (I := I) J x t = c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t) :
    d.velocity (I := I) J x t = d.speed g x t ^ (-2 : ℤ) • d.Dx g d.X x t := by
  have htime : mfderivWithin 𝓘(ℝ, ℝ) I (c.lift x) J t =
      mfderivWithin 𝓘(ℝ, ℝ) I (d.lift x) J t :=
    mfderivWithin_congr (fun r hr => h x r hr) (h x t ht)
  have hs : (fun y => c.lift y t) = fun y => d.lift y t := funext fun y => h y t ht
  simp only [velocity, speed, Dx, X] at heq ⊢
  rw [htime, hs, h x t ht] at heq
  exact heq

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_smooth_graph_parabolic_curve_of_smooth
    (F₀ : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, F), F⟯) :
    ∃ T : ℝ, 0 < T ∧ ∃ f : CurveMap F,
      (∀ z, f z 0 = F₀ z) ∧
      (graph f).SmoothOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (Icc 0 T) ∧
      (graph f).ImmersedOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (Icc 0 T) ∧
      ∀ x t, t ∈ Icc 0 T →
        (graph f).velocity (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (Icc 0 T) x t =
          (graph f).speed (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := F)))
            x t ^ (-2 : ℤ) •
          (graph f).Dx (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := F)))
            (graph f).X x t := by
  obtain ⟨T, hT, c, hc, hi, hinit, heq⟩ := exists_smooth_parametric_curve_of_graph F₀
  have hfirst : ∀ z t, t ∈ Icc 0 T → (c z t).1 = z :=
    fst_eq_id_of_parabolic_equation c (fun _ => euclideanMetric (E := F)) hc
      (fun z => congrArg Prod.fst (hinit z))
      (fun x t => c.speed (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := F)))
        x t ^ (-2 : ℤ))
      (fun x t _ => zpow_nonneg (c.speed_nonneg _ x t) _)
      (fun x t ht => heq x t ⟨ht.1.le, ht.2.le⟩)
  let f : CurveMap F := fun z t => (c z t).2
  have hagree (x t : ℝ) (ht : t ∈ Icc 0 T) :
      c.lift x t = (graph f).lift x t := by
    apply Prod.ext
    · exact hfirst (x : AddCircle (1 : ℝ)) t ht
    · rfl
  have hgraph : (graph f).SmoothOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (Icc 0 T) :=
    hc.congr (fun p hp => (hagree p.1 p.2 hp.2).symm)
  refine ⟨T, hT, f, ?_, hgraph, ?_, ?_⟩
  · intro z
    exact congrArg Prod.snd (hinit z)
  · intro x t ht
    have hs : (fun y => (graph f).lift y t) = fun y => c.lift y t :=
      funext fun y => (hagree y t ht).symm
    unfold X
    rw [hs]
    exact hi x t ht
  · intro x t ht
    exact parabolic_equation_congr hagree ht (heq x t ht)

theorem exists_graph_curve_shortening_reparametrization_of_smooth
    (F₀ : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, F), F⟯) :
    ∃ T : ℝ, 0 < T ∧ ∃ f : CurveMap F,
      (∀ z, f z 0 = F₀ z) ∧
      (graph f).SmoothOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (Icc 0 T) ∧
      (graph f).ImmersedOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (Icc 0 T) ∧
      (∀ x t, t ∈ Icc 0 T →
        (graph f).velocity (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (Icc 0 T) x t =
          (graph f).speed (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := F)))
            x t ^ (-2 : ℤ) •
          (graph f).Dx (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := F)))
            (graph f).X x t) ∧
      ∃ φ : CircleReparametrization (Icc 0 T),
        (∀ z, φ.map 0 z = z) ∧
        IsSolutionOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
          (fun z t => graph f (φ.map t z) t)
          (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := F))) (Icc 0 T) := by
  obtain ⟨T, hT, f, hinit, hc, hi, heq⟩ := exists_smooth_graph_parabolic_curve_of_smooth F₀
  let g : SmoothRiemannianMetric (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (AddCircle (1 : ℝ) × F) :=
    AddCircle.flatMetric.prod (euclideanMetric (E := F))
  have hg := DifferentialGeometry.Geometry.Curvature.metricFamilySmoothOn_stationary g
    (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.univ 0)
  have hgeo := isGeometricSolutionOn_of_parabolicGauge hg (uniqueDiffOn_Icc hT)
    (subset_univ _) hc hi heq
  obtain ⟨φ, hφ, hsol⟩ := hgeo.exists_reparametrization_isSolutionOn hg hT (subset_univ _)
  exact ⟨T, hT, f, hinit, hc, hi, heq, φ, hφ, hsol⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
