import DifferentialGeometry.Analysis.Calculus.Sard
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Curve.Reparametrization
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.TwoParameterFields
import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section
open Bundle Manifold Set Filter MeasureTheory Topology
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

theorem smooth_critical_values_null {m n : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin m))) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) :
    volume (F '' {x | x ∈ U ∧ ¬Function.Surjective (fderiv ℝ F x)}) = 0 := by
  rcases lt_trichotomy m n with hlt | heq | hgt
  · refine measure_mono_null (image_mono ?_) (ContDiffOn.addHaar_image_eq_zero_of_finrank_lt
      (F := EuclideanSpace ℝ (Fin n)) volume hU (hF.of_le (by norm_num)) ?_)
    · rintro x ⟨hxU, -⟩
      exact hxU
    · rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
      exact hlt
  · subst heq
    refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (f' := fun x => fderiv ℝ F x) volume ?_ ?_
    · intro x hx
      exact (hF.differentiableOn (by norm_num)).differentiableAt
        (hU.mem_nhds hx.1) |>.hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      by_contra hdet
      have hker : (fderiv ℝ F x).ker = ⊥ := by
        by_contra h
        exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
      exact hx.2 ((LinearMap.injective_iff_surjective).mp (LinearMap.ker_eq_bot.mp hker))
  · sorry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def immersionSecondFundamental {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (x : U) (X Y : EuclideanSpace ℝ (Fin m)) : TangentSpace I (F x) := by
  have a : TangentSpace I (F x) := by
    simpa only [zero_smul, add_zero] using
      covDerivAlong g (fun t : ℝ => F ((x : EuclideanSpace ℝ (Fin m)) + t • X))
        (fun t => mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F
          ((x : EuclideanSpace ℝ (Fin m)) + t • X) Y) 0
  exact a - mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x
    ((metricCov h) (fun _ : U => Y) x X)

theorem local_immersion_gauss [I.Boundaryless] [T2Space M]
    {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (hF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F U)
    (himm : ∀ x ∈ U, Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x))
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (hinduced : ∀ (x : U) (X Y : EuclideanSpace ℝ (Fin m)),
      h.inner x X Y = g.inner (F x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x X)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x Y))
    (x : U) (X Y Z W : EuclideanSpace ℝ (Fin m)) :
    metricRm04StandardAt h x X Y Z W =
      metricRm04StandardAt g (F x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x X)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x Y)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x Z)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x W) +
      g.inner (F x) (immersionSecondFundamental U F g h x X W)
        (immersionSecondFundamental U F g h x Y Z) -
      g.inner (F x) (immersionSecondFundamental U F g h x X Z)
        (immersionSecondFundamental U F g h x Y W) := by
  sorry

theorem smooth_manifold_critical_values_null_in_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SecondCountableTopology M]
    {n : ℕ} {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H'} [J.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    (F : M → N) (S : Set M) (hS : IsOpen S) (hF : ContMDiffOn I J ∞ F S)
    (q : N) :
    volume ((extChartAt J q ∘ F) ''
      {x | x ∈ S ∧ F x ∈ (chartAt H' q).source ∧
        ¬Function.Surjective (mfderiv I J F x)}) = 0 := by
  classical
  by_cases hdim : Module.finrank ℝ E < n
  · obtain ⟨P, hPc, hP⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun p : M => (chartAt H p).source) (fun p => (chartAt H p).open_source)
    have hcover : (⋃ p ∈ P, (chartAt H p).source) = univ := by
      rw [hP]
      exact iUnion_eq_univ_iff.mpr fun x => ⟨x, mem_chart_source H x⟩
    set T : Set M := {x | x ∈ S ∧ F x ∈ (chartAt H' q).source ∧
      ¬Function.Surjective (mfderiv I J F x)}
    have key : ∀ p ∈ P,
        volume ((extChartAt J q ∘ F) '' (T ∩ (chartAt H p).source)) = 0 := by
      intro p hp
      set B : Set M := (S ∩ F ⁻¹' (chartAt H' q).source) ∩ (chartAt H p).source
      have hBopen : IsOpen B :=
        IsOpen.inter
          (hF.continuousOn.isOpen_inter_preimage hS (chartAt H' q).open_source)
          (chartAt H p).open_source
      have hBsub : B ⊆ (chartAt H p).source := fun x hx => hx.2
      have hBsubE : B ⊆ (extChartAt I p).source := by
        intro x hx
        rw [extChartAt_source]
        exact hBsub hx
      have hBsubS : B ⊆ S := fun x hx => hx.1.1
      have hBmap : ∀ x ∈ B, F x ∈ (chartAt H' q).source := fun x hx => hx.1.2
      set V : Set E := (extChartAt I p) '' B
      have hVsub : V ⊆ (extChartAt I p).target := by
        rintro _ ⟨x, hx, rfl⟩
        exact (extChartAt I p).map_source (hBsubE hx)
      have hVopen : IsOpen V := by
        have hopen := (continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
          (isOpen_extChartAt_target (I := I) p) hBopen
        rw [← PartialEquiv.image_source_inter_eq' (extChartAt I p) B,
          Set.inter_eq_right.mpr hBsubE] at hopen
        exact hopen
      have hBsymm : B = (extChartAt I p).symm '' V := by
        ext x
        constructor
        · intro hx
          exact ⟨extChartAt I p x, ⟨x, hx, rfl⟩, (extChartAt I p).left_inv (hBsubE hx)⟩
        · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          rw [(extChartAt I p).left_inv (hBsubE hz)]
          exact hz
      have hBmem : ∀ y ∈ V, (extChartAt I p).symm y ∈ B := by
        intro y hy
        rw [hBsymm]
        exact ⟨y, hy, rfl⟩
      have hsymm : ContMDiffOn 𝓘(ℝ, E) I 1 (extChartAt I p).symm V :=
        ((contMDiffOn_extChartAt_symm (I := I) (n := ∞) p).of_le (by norm_num)).mono hVsub
      have hcomp : ContMDiffOn 𝓘(ℝ, E) J 1 (F ∘ (extChartAt I p).symm) V :=
        (hF.of_le (by norm_num)).comp hsymm fun y hy => hBsubS (hBmem y hy)
      have hchart : ContMDiffOn J 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 (extChartAt J q)
          (chartAt H' q).source :=
        (contMDiffOn_extChartAt (I := J) (n := ∞) (x := q)).of_le (by norm_num)
      have hfinal : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
          (fun y => extChartAt J q (F ((extChartAt I p).symm y))) V :=
        hchart.comp hcomp fun y hy => hBmap _ (hBmem y hy)
      have hcd : ContDiffOn ℝ 1 (fun y => extChartAt J q (F ((extChartAt I p).symm y)))
          V := contMDiffOn_iff_contDiffOn.mp hfinal
      have hnull := ContDiffOn.addHaar_image_eq_zero_of_finrank_lt
        (F := EuclideanSpace ℝ (Fin n)) volume hVopen hcd
        (by rw [finrank_euclideanSpace_fin]; exact hdim)
      refine measure_mono_null ?_ hnull
      rintro z ⟨x, hx, rfl⟩
      have hxB : x ∈ B := ⟨⟨hx.1.1, hx.1.2.1⟩, hx.2⟩
      refine ⟨extChartAt I p x, ⟨x, hxB, rfl⟩, ?_⟩
      simp only [Function.comp_apply]
      rw [(extChartAt I p).left_inv (hBsubE hxB)]
    have hunion : volume
        (⋃ p ∈ P, (extChartAt J q ∘ F) '' (T ∩ (chartAt H p).source)) = 0 :=
      (measure_biUnion_null_iff hPc).mpr key
    refine measure_mono_null ?_ hunion
    rintro z ⟨x, hx, rfl⟩
    have hxP : x ∈ ⋃ p ∈ P, (chartAt H p).source := by rw [hcover]; trivial
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hxP
    exact mem_iUnion₂.mpr ⟨p, hp, x, ⟨hx, hxp⟩, rfl⟩
  · sorry

section SliceSmoothness

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem slice_smul_contMDiff (gamma : ℝ → M)
    (V : ∀ x, TangentSpace I (gamma x))
    (f : ℝ → ℝ) (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (gamma x) (V x))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (gamma x) (f x • V x)) := by
  intro x
  have hv := (contMDiffAt_totalSpace.mp (hV x))
  rw [contMDiffAt_totalSpace]
  refine ⟨hv.1, ?_⟩
  let e := trivializationAt E (TangentSpace I) (gamma x)
  have he : gamma x ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (gamma x)
  have hnear : ∀ᶠ y in 𝓝 x, gamma y ∈ e.baseSet :=
    hv.1.continuousAt (e.open_baseSet.mem_nhds he)
  apply ((hf x).smul hv.2).congr_of_eventuallyEq
  filter_upwards [hnear] with y hy
  exact (e.linear ℝ hy).2 (f y) (V y)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem slice_inner_contDiff (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (V W : ∀ x, TangentSpace I (gamma x))
    (hg : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (gamma x) (V x)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (gamma x) (W x))) :
    ContDiff ℝ ∞ (fun x => g.inner (gamma x) (V x) (W x)) := by
  have htotal : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun x => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
        (gamma x) (g.inner (gamma x) (V x) (W x))) := by
    apply ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    · exact g.contMDiff.comp hg
    · exact hV
    · exact hW
  apply contMDiff_iff_contDiff.mp
  intro x
  have hx := htotal x
  simp only [contMDiffAt_totalSpace] at hx
  exact hx.2

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem slice_velocity_contMDiff (gamma : ℝ → M)
    (hg : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (gamma x) (mfderiv 𝓘(ℝ, ℝ) I gamma x (1 : ℝ))) := by
  have hunit : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x : ℝ => TotalSpace.mk' ℝ
        (E := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) x (1 : ℝ)) := by
    intro x
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_const (c := (1 : ℝ)))
  change ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
    (tangentMap 𝓘(ℝ, ℝ) I gamma ∘ fun x : ℝ =>
      TotalSpace.mk' ℝ (E := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) x (1 : ℝ))
  exact (hg.contMDiff_tangentMap (le_refl _)).comp hunit

omit [CompleteSpace E] in
private theorem slice_covAlong_contMDiff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (V : ∀ x, TangentSpace I (gamma x))
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (gamma x) (V x))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (gamma x) (covDerivAlong g gamma V x)) := by
  have htwo := cov_fst_smooth g (fun x _ : ℝ => gamma x) (fun x _ => V x)
    (hV.comp contMDiff_fst)
  exact htwo.comp (contMDiff_id.prodMk (contMDiff_const (c := (0 : ℝ))))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
private theorem slice_space_smooth (c : CurveMap M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x => c.lift x t) :=
  contMDiffOn_univ.mp (CurveMap.space_slice_contMDiffOn c J hc t ht)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem CurveMap.speed_contDiff (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M)
    (J : Set ℝ) (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    ContDiff ℝ ∞ (fun x => c.speed g x t) := by
  have hg := slice_space_smooth c J hc t ht
  have hX := slice_velocity_contMDiff (fun x => c.lift x t) hg
  have hsq := slice_inner_contDiff (g t) (fun x => c.lift x t)
    (fun x => c.X x t) (fun x => c.X x t) hg hX hX
  exact hsq.sqrt (fun x => ne_of_gt ((g t).pos _ _ (hi x t ht)))

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem CurveMap.unitTangent_contMDiff (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (c.lift x t) (c.unitTangent g x t)) := by
  have hg := slice_space_smooth c J hc t ht
  have hX := slice_velocity_contMDiff (fun x => c.lift x t) hg
  have hs := c.speed_contDiff g J hc hi t ht
  exact slice_smul_contMDiff (fun x => c.lift x t) (fun x => c.X x t)
    (fun x => (c.speed g x t)⁻¹)
    (hs.inv (fun x => ne_of_gt (c.speed_pos g hi x t ht))).contMDiff hX

omit [CompleteSpace E] in
theorem CurveMap.curvatureVector_contMDiff
    [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (c.lift x t) (c.curvatureVector g x t)) := by
  have hg := slice_space_smooth c J hc t ht
  have hs := c.speed_contDiff g J hc hi t ht
  have hDT := slice_covAlong_contMDiff (g t) (fun x => c.lift x t)
    (fun x => c.unitTangent g x t) (c.unitTangent_contMDiff g J hc hi t ht)
  exact slice_smul_contMDiff (fun x => c.lift x t)
    (fun x => c.Dx g (c.unitTangent g) x t) (fun x => (c.speed g x t)⁻¹)
    (hs.inv (fun x => ne_of_gt (c.speed_pos g hi x t ht))).contMDiff hDT

omit [CompleteSpace E] in
theorem CurveMap.curvatureSq_contDiff
    [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContDiff ℝ ∞ (fun x => c.curvatureSq g x t) := by
  have hg := slice_space_smooth c J hc t ht
  have hH := c.curvatureVector_contMDiff g J hc hi t ht
  have hsq := slice_inner_contDiff (g t) (fun x => c.lift x t)
    (fun x => c.curvatureVector g x t) (fun x => c.curvatureVector g x t) hg hH hH
  simpa only [CurveMap.curvatureSq, CurveMap.normSq] using hsq

end SliceSmoothness

namespace CurveMap

omit [TopologicalSpace M] in
theorem lift_add_period (c : CurveMap M) (t : ℝ) :
    Function.Periodic (fun x => c.lift x t) 1 :=
  fun x => congrArg (fun z => c z t) (AddCircle.coe_add_period (1 : ℝ) x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem X_add_period (c : CurveMap M) (t x : ℝ)
    (h : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) (x + 1)) :
    c.X (I := I) (x + 1) t = c.X (I := I) x t := by
  have hd := DifferentialGeometry.Geometry.mfderiv_comp_add_apply_one
    (I := I) (γ := fun y => c.lift y t) x 1 h
  have hper : (fun y => c.lift (y + 1) t) = fun y => c.lift y t :=
    funext (fun y => c.lift_add_period t y)
  rw [hper] at hd
  exact hd.symm

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_add_period (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M) (t x : ℝ)
    (h : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) (x + 1)) :
    c.speed g (x + 1) t = c.speed g x t := by
  have hl : c.lift (x + 1) t = c.lift x t := c.lift_add_period t x
  have hX : c.X (I := I) (x + 1) t = c.X (I := I) x t := c.X_add_period t x h
  change Real.sqrt ((g t).inner (c.lift (x + 1) t) (c.X (I := I) (x + 1) t)
      (c.X (I := I) (x + 1) t)) =
    Real.sqrt ((g t).inner (c.lift x t) (c.X (I := I) x t) (c.X (I := I) x t))
  rw [hl, hX]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem unitTangent_add_period (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M)
    (t x : ℝ) (h : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) (x + 1)) :
    c.unitTangent g (x + 1) t = c.unitTangent g x t := by
  have hs : c.speed g (x + 1) t = c.speed g x t := c.speed_add_period g t x h
  have hX : c.X (I := I) (x + 1) t = c.X (I := I) x t := c.X_add_period t x h
  simp only [CurveMap.unitTangent, hs, hX]
  rfl

omit [CompleteSpace E] in
theorem Dx_add_period [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (t x : ℝ) (V : c.Field (I := I))
    (hVper : Function.Periodic (fun y => V y t) 1)
    (hVsmooth : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun y => TotalSpace.mk' E (c.lift y t) (V y t)))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) (x + 1)) :
    c.Dx g V (x + 1) t = c.Dx g V x t := by
  have hVdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun y => c.lift y t) (fun y => V y t) (x + 1)) (x + 1) :=
    differentiableAt_chartRepAt_of_contMDiff_two
      (hVsmooth.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) (x + 1)
  have hφ : DifferentiableAt ℝ (fun s : ℝ => s + 1) x := differentiableAt_id.add_const 1
  have hcomp := covDerivAlong_comp (g t) (fun y => c.lift y t) (fun y => V y t)
    (fun s : ℝ => s + 1) x hγ hVdiff hφ
  have hF : (fun s => c.lift (s + 1) t) = fun s => c.lift s t :=
    funext (fun s => c.lift_add_period t s)
  have hW : (fun s => V (s + 1) t) = fun s => V s t := funext (fun s => hVper s)
  rw [hF, hW] at hcomp
  have hd : deriv (fun s : ℝ => s + 1) x = 1 := by simp
  rw [hd, one_smul] at hcomp
  exact hcomp.symm


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
private theorem slice_mdifferentiableAt (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (y : ℝ) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I (fun z => c.lift z t) y :=
  (slice_space_smooth c J hc t ht).mdifferentiableAt (by norm_num)

omit [CompleteSpace E] in
private theorem curvatureSq_add_period [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (x : ℝ) :
    c.curvatureSq g (x + 1) t = c.curvatureSq g x t := by
  have hγ : ∀ y, MDifferentiableAt 𝓘(ℝ, ℝ) I (fun z => c.lift z t) y :=
    fun y => slice_mdifferentiableAt c J hc t ht y
  have hs : c.speed g (x + 1) t = c.speed g x t := c.speed_add_period g t x (hγ (x + 1))
  have hD : c.Dx g (c.unitTangent g) (x + 1) t = c.Dx g (c.unitTangent g) x t :=
    c.Dx_add_period g t x (c.unitTangent g)
      (fun y => c.unitTangent_add_period g t y (hγ (y + 1)))
      (c.unitTangent_contMDiff g J hc hi t ht) (hγ (x + 1))
  have hH : c.curvatureVector g (x + 1) t = c.curvatureVector g x t := by
    change (c.speed g (x + 1) t)⁻¹ • c.Dx g (c.unitTangent g) (x + 1) t =
      (c.speed g x t)⁻¹ • c.Dx g (c.unitTangent g) x t
    rw [hs, hD]
    rfl
  have hl : c.lift (x + 1) t = c.lift x t := c.lift_add_period t x
  change (g t).inner (c.lift (x + 1) t) (c.curvatureVector g (x + 1) t)
      (c.curvatureVector g (x + 1) t) =
    (g t).inner (c.lift x t) (c.curvatureVector g x t) (c.curvatureVector g x t)
  rw [hH, hl]

omit [CompleteSpace E] in
theorem curvatureSq_speed_periodic [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    Function.Periodic (fun x => c.curvatureSq g x t * c.speed g x t) 1 :=
  fun x => by
    change c.curvatureSq g (x + 1) t * c.speed g (x + 1) t =
      c.curvatureSq g x t * c.speed g x t
    rw [curvatureSq_add_period g c J hc hi t ht x,
      c.speed_add_period g t x (slice_mdifferentiableAt c J hc t ht (x + 1))]

end CurveMap


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
