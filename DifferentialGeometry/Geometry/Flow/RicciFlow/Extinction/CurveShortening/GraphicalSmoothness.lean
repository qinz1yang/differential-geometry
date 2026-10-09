import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolutionLift
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.Uniqueness
import DifferentialGeometry.Analysis.Calculus.TimeJet.SpatialDerivatives
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

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

open DifferentialGeometry.Analysis.Parabolic

private theorem smooth_graph_lift_classical_facts
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : CurveMap E) {T : ℝ} (hT : 0 < T)
    (hf : (graph f).SmoothOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (Icc 0 T))
    (heq : ∀ x t, t ∈ Icc 0 T →
      (graph f).velocity (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (Icc 0 T) x t =
        (graph f).speed (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := E)))
          x t ^ (-2 : ℤ) •
        (graph f).Dx (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := E)))
          (graph f).X x t) :
    let G := fun t x => f.lift x t
    ContDiffOn ℝ ∞ (Function.uncurry G) (Icc 0 T ×ˢ univ) ∧
      (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (G t)) ∧
      ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (G p.1)) p.2) (Icc 0 T ×ˢ univ) ∧
      (∀ t, Function.Periodic (G t) 1) ∧
      ∀ t ∈ Ioo 0 T, ∀ x,
        HasDerivAt (fun s => G s x)
          (graphDiffusionCoefficient (deriv (G t) x) • deriv (deriv (G t)) x) t := by
  intro G
  have hsp : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f.lift p.1 p.2)
      (univ ×ˢ Icc 0 T) := by
    have hmd : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
        (fun p : ℝ × ℝ => f.lift p.1 p.2) (univ ×ˢ Icc 0 T) :=
      fun p hp => (hf p hp).snd
    exact hmd.contDiffOn
  have hG : ContDiffOn ℝ ∞ (Function.uncurry G) (Icc 0 T ×ˢ univ) :=
    hsp.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hp => ⟨hp.2, hp.1⟩)
  have hslice (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ 2 (G t) := by
    apply contDiffOn_univ.mp
    exact (hsp.of_le (WithTop.coe_le_coe.mpr le_top : (2 : ℕ∞ω) ≤ ∞)).comp
      (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ _ => ⟨mem_univ _, ht⟩)
  have hfirst := DifferentialGeometry.Analysis.contDiffOn_deriv_fst isOpen_univ
    (uniqueDiffOn_Icc hT) hsp
  have hsecond := DifferentialGeometry.Analysis.contDiffOn_deriv_fst isOpen_univ
    (uniqueDiffOn_Icc hT) hfirst
  have hsecondSwap : ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (G p.1)) p.2)
      (Icc 0 T ×ˢ univ) :=
    hsecond.continuousOn.comp (continuous_snd.prodMk continuous_fst).continuousOn
      (fun _ hp => ⟨hp.2, hp.1⟩)
  refine ⟨hG, hslice, hsecondSwap, ?_, ?_⟩
  · intro t x
    change f ((x + 1 : ℝ) : AddCircle (1 : ℝ)) t = f (x : AddCircle (1 : ℝ)) t
    rw [AddCircle.coe_add_period]
  · intro t ht x
    have htcc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
    have htime : ContDiffOn ℝ ∞ (fun s => G s x) (Icc 0 T) :=
      hG.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hs => ⟨hs, mem_univ _⟩)
    have hdiff : DifferentiableWithinAt ℝ (f (x : AddCircle (1 : ℝ))) (Icc 0 T) t :=
      htime.differentiableOn (by simp) t htcc
    have hderiv := (graph_parabolic_equation_iff f (Icc 0 T) x t
      ((uniqueDiffOn_Icc hT) t htcc) hdiff (hslice t htcc).contDiffAt).mp (heq x t htcc)
    have hwithin := hdiff.hasDerivWithinAt
    rw [hderiv] at hwithin
    exact hwithin.hasDerivAt (Icc_mem_nhds ht.1 ht.2)


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem graph_smoothOn_congr_on_interval
    {f g : CurveMap E} {T : ℝ}
    (hf : (graph f).SmoothOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (Icc 0 T))
    (heq : ∀ z t, t ∈ Icc 0 T → g z t = f z t) :
    (graph g).SmoothOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (Icc 0 T) := by
  apply hf.congr
  intro p hp
  exact congrArg (fun y => ((p.1 : AddCircle (1 : ℝ)), y))
    (heq (p.1 : AddCircle (1 : ℝ)) p.2 hp.2)

private theorem reparametrization_isSolutionOn_congr_on_interval
    {f g : CurveMap E} {T τ : ℝ} (hτ : 0 < τ) (hτT : τ ≤ T)
    (heq : ∀ z t, t ∈ Icc 0 τ → g z t = f z t)
    (φ : CircleReparametrization (Icc 0 T))
    (hφ : IsSolutionOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
      (fun z t => graph f (φ.map t z) t)
      (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := E))) (Icc 0 T)) :
    IsSolutionOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
      (fun z t => graph g ((φ.restrict (Icc_subset_Icc le_rfl hτT)).map t z) t)
      (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := E))) (Icc 0 τ) := by
  have hres := hφ.mono_Icc le_rfl hτT hτ
  apply isSolutionOn_congr (c := fun z t => graph f (φ.map t z) t) _ hres
  intro x t ht
  exact congrArg (fun y => (φ.map t (x : AddCircle (1 : ℝ)), y))
    (heq (φ.map t (x : AddCircle (1 : ℝ))) t ht)



theorem exists_smooth_graph_reparametrization_of_classical_solution
    (F₀ : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, E), E⟯)
    (F : ℝ → ℝ → E) {S : ℝ} (hS : 0 < S)
    (hper : ∀ t, Function.Periodic (F t) 1)
    (hinit : ∀ x, F 0 x = F₀ (x : AddCircle (1 : ℝ)))
    (hcont : ContinuousOn (Function.uncurry F) (Icc 0 S ×ˢ Icc 0 1))
    (hspace : ∀ t ∈ Ioo 0 S, ContDiff ℝ 2 (F t))
    (hslope : ContinuousOn (fun p : ℝ × ℝ => deriv (F p.1) p.2) (Icc 0 S ×ˢ Icc 0 1))
    (hpde : ∀ t ∈ Ioo 0 S, ∀ x, HasDerivAt (fun s => F s x)
      (DifferentialGeometry.Analysis.Parabolic.graphDiffusionCoefficient (deriv (F t) x) •
        deriv (deriv (F t)) x) t) :
    let c : CurveMap E := fun z t => (hper t).lift z
    ∃ T : ℝ, 0 < T ∧
      let τ := min S T
      0 < τ ∧ τ ≤ S ∧
      (∀ x t, c.lift x t = F t x) ∧
      (∀ z, c z 0 = F₀ z) ∧
      ContDiffOn ℝ ∞ (Function.uncurry F) (Icc 0 τ ×ˢ univ) ∧
      (graph c).SmoothOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (Icc 0 τ) ∧
      ∃ φ : CircleReparametrization (Icc 0 τ),
        (∀ z, φ.map 0 z = z) ∧
        IsSolutionOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
          (fun z t => graph c (φ.map t z) t)
          (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := E))) (Icc 0 τ) ∧
        (∀ z, graph c (φ.map 0 z) 0 = (z, F₀ z)) ∧
        ∀ t ∈ Icc 0 τ,
          range (fun z => graph c (φ.map t z) t) = range (fun z => (z, (hper t).lift z)) := by
  intro c
  obtain ⟨T, hT, f, hfinit, hfsmooth, hfimm, hfeq, φ, hφinit, hφsol⟩ :=
    exists_graph_curve_shortening_reparametrization_of_smooth F₀
  let τ := min S T
  have hτ : 0 < τ := lt_min hS hT
  have hτS : τ ≤ S := min_le_left _ _
  have hτT : τ ≤ T := min_le_right _ _
  have hsubS : Icc (0 : ℝ) τ ⊆ Icc 0 S := Icc_subset_Icc le_rfl hτS
  have hsubT : Icc (0 : ℝ) τ ⊆ Icc 0 T := Icc_subset_Icc le_rfl hτT
  have hdesc (x t : ℝ) : c.lift x t = F t x := (hper t).lift_coe x
  have hcinit (z : AddCircle (1 : ℝ)) : c z 0 = F₀ z := by
    induction z using QuotientAddGroup.induction_on with
    | H x => exact (hdesc x 0).trans (hinit x)
  obtain ⟨hfcont, hfC2, hfsecond, hfper, hfpde⟩ :=
    smooth_graph_lift_classical_facts f hT hfsmooth hfeq
  have hsame : ∀ t ∈ Icc 0 τ, ∀ x, F t x = f.lift x t := by
    apply DifferentialGeometry.Analysis.Parabolic.graphical_curve_shortening_unique
      F (fun t x => f.lift x t) hτ.le
    · intro t ht
      exact hper t
    · intro t ht x
      simp only [lift, AddCircle.coe_add_period]
    · exact hcont.mono (prod_mono hsubS Subset.rfl)
    · exact hfcont.continuousOn.mono (prod_mono hsubT (subset_univ _))
    · intro t ht
      exact hspace t ⟨ht.1, ht.2.trans_le hτS⟩
    · intro t ht
      exact hfC2 t (hsubT ⟨ht.1.le, ht.2.le⟩)
    · intro t ht x
      exact hpde t ⟨ht.1, ht.2.trans_le hτS⟩ x
    · intro t ht x
      exact hfpde t ⟨ht.1, ht.2.trans_le hτT⟩ x
    · exact hslope.mono (prod_mono hsubS Subset.rfl)
    · exact hfsecond.mono (prod_mono hsubT (subset_univ _))
    · intro x
      exact (hinit x).trans (hfinit (x : AddCircle (1 : ℝ))).symm
  have hcircle : ∀ z t, t ∈ Icc 0 τ → c z t = f z t := by
    intro z t ht
    induction z using QuotientAddGroup.induction_on with
    | H x => exact (hdesc x t).trans (hsame t ht x)
  let ψ := φ.restrict hsubT
  have hψinit : ∀ z, ψ.map 0 z = z := hφinit
  have hψsol := reparametrization_isSolutionOn_congr_on_interval hτ hτT hcircle φ hφsol
  refine ⟨T, hT, hτ, hτS, hdesc, hcinit, ?_, ?_, ψ, hψinit, hψsol, ?_, ?_⟩
  · apply (hfcont.mono (prod_mono hsubT Subset.rfl)).congr
    intro p hp
    exact hsame p.1 hp.1 p.2
  · exact graph_smoothOn_congr_on_interval
      (hfsmooth.mono (prod_mono Subset.rfl hsubT)) hcircle
  · intro z
    rw [hψinit]
    exact congrArg (fun y => (z, y)) (hcinit z)
  · intro t ht
    exact (ψ.map t).surjective.range_comp (fun z => graph c z t)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
