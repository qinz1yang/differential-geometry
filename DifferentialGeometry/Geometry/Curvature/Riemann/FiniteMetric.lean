import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.SectionalTransition
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.SectionalPlane
import DifferentialGeometry.Bundle.Hom
import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : ℕ∞ω}

private def pullbackCoefficients
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (f : E → M) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let D : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I f x
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (f x)
  B.bilinearComp D D

private theorem source_mfderiv_contMDiffAt {f : E → M} {x : E}
    (hf : ContMDiffAt 𝓘(ℝ, E) I 3 f x) :
    ContMDiffAt 𝓘(ℝ, E) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y => (⟨f y, mfderiv 𝓘(ℝ, E) I f y⟩ :
        TotalSpace (E →L[ℝ] E)
          (fun m => Bundle.Trivial M E m →L[ℝ] TangentSpace I m))) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨hf.of_le (by norm_num), ?_⟩
  have hd := hf.mfderiv_const (m := 2) (by norm_num)
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with y
  ext v
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_def]
  rfl

private theorem contDiffOn_pullbackCoefficients
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hn : (2 : ℕ∞ω) ≤ n) {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 3 f U) :
    ContDiffOn ℝ 2 (pullbackCoefficients g f) U := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro x hx
  have hfx := (hf x hx).contMDiffAt (hU.mem_nhds hx)
  have hD := source_mfderiv_contMDiffAt hfx
  have hG := (g.contMDiff.of_le hn).contMDiffAt.comp x
    (hfx.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3))
  have hB := hG.clm_bundle_bilinearComp
    (U₁ := TangentSpace I) (U₂ := TangentSpace I) (U₃ := Bundle.Trivial M ℝ)
    (U₄ := Bundle.Trivial M E) (U₅ := Bundle.Trivial M E) hD hD
  have h := (contMDiffAt_totalSpace.mp hB).2.contDiffAt
  refine (h.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [] with y
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, Trivialization.continuousLinearMapAt_apply]
  rfl

private theorem pullbackCoefficients_symm
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (f : E → M) (x v w : E) :
    pullbackCoefficients g f x v w = pullbackCoefficients g f x w v :=
  g.symm (f x) _ _

private theorem isCoercive_pullbackCoefficients [FiniteDimensional ℝ E]
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    {f : E → M} {x : E} (hf : Function.Injective (mfderiv 𝓘(ℝ, E) I f x)) :
    IsCoercive (pullbackCoefficients g f x) := by
  apply ContinuousLinearMap.isCoercive_of_posDef
  intro v hv
  apply g.pos
  intro hzero
  apply hv
  apply hf
  exact hzero.trans (map_zero (mfderiv 𝓘(ℝ, E) I f x)).symm

private theorem isCoercive_chartCoefficients [FiniteDimensional ℝ E]
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M 3) {y : E} (hy : y ∈ φ.source) :
    IsCoercive (pullbackCoefficients g φ y) := by
  exact isCoercive_pullbackCoefficients g
    ((φ.isLocalDiffeomorphAt _ _ _ hy).mfderivToContinuousLinearEquiv (by norm_num)).injective

private theorem chartCoefficients_transition
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (φ ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 3)
    {y : E} (hy : y ∈ (φ.trans ψ.symm).source) :
    pullbackCoefficients g φ y =
      (pullbackCoefficients g ψ ((φ.trans ψ.symm) y)).bilinearComp
        (fderiv ℝ (φ.trans ψ.symm) y) (fderiv ℝ (φ.trans ψ.symm) y) := by
  let T := φ.trans ψ.symm
  have hT : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) T y :=
    T.mdifferentiableAt (by norm_num) hy
  have hψ : MDifferentiableAt 𝓘(ℝ, E) I ψ (T y) :=
    ψ.mdifferentiableAt (by norm_num) (ψ.map_target hy.2)
  have heq : ψ ∘ T =ᶠ[𝓝 y] φ := by
    filter_upwards [T.open_source.mem_nhds hy] with z hz
    exact ψ.right_inv hz.2
  have hd : (mfderiv 𝓘(ℝ, E) I ψ (T y) : E →L[ℝ] E).comp (fderiv ℝ T y) =
      (mfderiv 𝓘(ℝ, E) I φ y : E →L[ℝ] E) := by
    have hc := (mfderiv_comp y hψ hT).symm.trans heq.mfderiv_eq
    rw [mfderiv_eq_fderiv] at hc
    ext v
    exact congrArg (fun L => L v) hc
  have hr : ψ (T y) = φ y := ψ.right_inv hy.2
  ext v w
  change (g.inner (φ y) : E →L[ℝ] E →L[ℝ] ℝ)
      (mfderiv 𝓘(ℝ, E) I φ y v) (mfderiv 𝓘(ℝ, E) I φ y w) =
    (g.inner (ψ (T y)) : E →L[ℝ] E →L[ℝ] ℝ)
      (((mfderiv 𝓘(ℝ, E) I ψ (T y) : E →L[ℝ] E).comp (fderiv ℝ T y)) v)
      (((mfderiv 𝓘(ℝ, E) I ψ (T y) : E →L[ℝ] E).comp (fderiv ℝ T y)) w)
  rw [hd, hr]
  rfl

omit [IsManifold I 1 M] in
private theorem chartDerivative_transition
    (e f : PartialDiffeomorph I 𝓘(ℝ, E) M E 3)
    {p : M} (he : p ∈ e.source) (hf : p ∈ f.source) :
    (fderiv ℝ (e.symm.trans f) (e p)).comp
        (mfderiv I 𝓘(ℝ, E) e p : E →L[ℝ] E) =
      (mfderiv I 𝓘(ℝ, E) f p : E →L[ℝ] E) := by
  let T := e.symm.trans f
  have hep : e p ∈ T.source := by
    refine ⟨e.map_source he, ?_⟩
    change e.symm (e p) ∈ f.source
    exact Eq.mpr (congrArg (fun q : M => q ∈ f.source) (e.left_inv he)) hf
  have heq : T ∘ e =ᶠ[𝓝 p] f := by
    filter_upwards [e.open_source.mem_nhds he] with q hq
    exact congrArg f (e.left_inv hq)
  have hc := (mfderiv_comp p (T.mdifferentiableAt (by norm_num) hep)
    (e.mdifferentiableAt (by norm_num) he)).symm.trans heq.mfderiv_eq
  rw [mfderiv_eq_fderiv] at hc
  ext v
  exact congrArg (fun L => L v) hc

private theorem coefficientSectional_congr [FiniteDimensional ℝ E]
    {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (h : b =ᶠ[𝓝 x] c) (v w : E) :
    DifferentialGeometry.Analysis.coefficientSectional b x v w =
      DifferentialGeometry.Analysis.coefficientSectional c x v w := by
  have hG : DifferentialGeometry.Analysis.coefficientGram b =ᶠ[𝓝 x]
      DifferentialGeometry.Analysis.coefficientGram c :=
    h.mono fun y hy => congrArg (DifferentialGeometry.Analysis.coefficientGramCLM E) hy
  unfold DifferentialGeometry.Analysis.coefficientSectional
    DifferentialGeometry.Analysis.coefficientRm04
  rw [DifferentialGeometry.Analysis.jet2_congr_of_eventuallyEq hG, h.eq_of_nhds]

private theorem pullbackCoefficients_comp
    {H' N : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N] {m : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J m E (TangentSpace J : N → Type _))
    {f : M → N} {φ : E → M} {y : E}
    (hf : MDifferentiableAt I J f (φ y)) (hφ : MDifferentiableAt 𝓘(ℝ, E) I φ y)
    (hmetric : ∀ v w : TangentSpace I (φ y),
      g.inner (φ y) v w = h.inner (f (φ y)) (mfderiv I J f (φ y) v)
        (mfderiv I J f (φ y) w)) :
    pullbackCoefficients g φ y = pullbackCoefficients h (f ∘ φ) y := by
  ext v w
  change g.inner (φ y) (mfderiv 𝓘(ℝ, E) I φ y v) (mfderiv 𝓘(ℝ, E) I φ y w) =
    h.inner (f (φ y)) (mfderiv 𝓘(ℝ, E) J (f ∘ φ) y v)
      (mfderiv 𝓘(ℝ, E) J (f ∘ φ) y w)
  rw [hmetric, mfderiv_comp y hf hφ]
  rfl

private theorem pullbackCoefficients_congr
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    {f h : E → M} {y : E} (heq : f =ᶠ[𝓝 y] h) :
    pullbackCoefficients g f y = pullbackCoefficients g h y := by
  have hd : (mfderiv 𝓘(ℝ, E) I f y : E →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, E) I h y : E →L[ℝ] E) := by
    ext v
    exact congrArg (fun L => L v) (heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := I))
  ext v w
  change (g.inner (f y) : E →L[ℝ] E →L[ℝ] ℝ)
      (mfderiv 𝓘(ℝ, E) I f y v) (mfderiv 𝓘(ℝ, E) I f y w) =
    (g.inner (h y) : E →L[ℝ] E →L[ℝ] ℝ)
      (mfderiv 𝓘(ℝ, E) I h y v) (mfderiv 𝓘(ℝ, E) I h y w)
  rw [hd, heq.eq_of_nhds]

private theorem chartCoefficients_pullback
    {H' N : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N] {m : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J m E (TangentSpace J : N → Type _))
    (f : PartialDiffeomorph I J M N 3) (ψ : PartialDiffeomorph J 𝓘(ℝ, E) N E 3)
    (hmetric : ∀ q ∈ f.source, ∀ v w : TangentSpace I q,
      g.inner q v w = h.inner (f q) (mfderiv I J f q v) (mfderiv I J f q w))
    {p : M} (hp : p ∈ f.source) (hψ : f p ∈ ψ.source) :
    pullbackCoefficients g (f.trans ψ).symm =ᶠ[𝓝 (ψ (f p))]
      pullbackCoefficients h ψ.symm := by
  let e := f.trans ψ
  have hep : p ∈ e.source := ⟨hp, hψ⟩
  have heyp : ψ (f p) ∈ e.target := e.map_source hep
  filter_upwards [e.open_target.mem_nhds heyp] with y hy
  have hfy : e.symm y ∈ f.source := f.map_target hy.2
  have hcomp := pullbackCoefficients_comp g h
    (f.mdifferentiableAt (by norm_num) hfy)
    (e.symm.mdifferentiableAt (by norm_num) hy) (hmetric (e.symm y) hfy)
  have heq : f ∘ e.symm =ᶠ[𝓝 y] ψ.symm := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact f.right_inv hz.2
  exact hcomp.trans (pullbackCoefficients_congr h heq)

private theorem chartSectional_transition [FiniteDimensional ℝ E]
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hn : (2 : ℕ∞ω) ≤ n)
    (φ ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 3)
    {y : E} (hy : y ∈ (φ.trans ψ.symm).source) (v w : E) :
    DifferentialGeometry.Analysis.coefficientSectional (pullbackCoefficients g φ) y v w =
      DifferentialGeometry.Analysis.coefficientSectional (pullbackCoefficients g ψ)
        ((φ.trans ψ.symm) y) (fderiv ℝ (φ.trans ψ.symm) y v)
          (fderiv ℝ (φ.trans ψ.symm) y w) := by
  let T := φ.trans ψ.symm
  apply DifferentialGeometry.Analysis.coefficientSectional_transition
    T.open_source ψ.open_source
    (contDiffOn_pullbackCoefficients g hn ψ.open_source ψ.contMDiffOn)
    (fun z _ => pullbackCoefficients_symm g ψ z)
    (fun _ hz => isCoercive_chartCoefficients g ψ hz)
    T.contMDiffOn.contDiffOn (fun _ hz => ψ.map_target hz.2)
    (fun _ hz => DifferentialGeometry.Analysis.isInvertible_fderiv_of_contDiffOn
      T.toOpenPartialHomeomorph (by norm_num : (3 : ℕ∞ω) ≠ 0)
      T.contMDiffOn.contDiffOn T.symm.contMDiffOn.contDiffOn hz)
    (fun z hz u t => congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B u t)
      (chartCoefficients_transition g φ ψ hz)) hy

private theorem chartSectional_eq [FiniteDimensional ℝ E]
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hn : (2 : ℕ∞ω) ≤ n) (e f : PartialDiffeomorph I 𝓘(ℝ, E) M E 3)
    {p : M} (he : p ∈ e.source) (hf : p ∈ f.source) (v w : TangentSpace I p) :
    DifferentialGeometry.Analysis.coefficientSectional (pullbackCoefficients g e.symm)
        (e p) (mfderiv I 𝓘(ℝ, E) e p v) (mfderiv I 𝓘(ℝ, E) e p w) =
      DifferentialGeometry.Analysis.coefficientSectional (pullbackCoefficients g f.symm)
        (f p) (mfderiv I 𝓘(ℝ, E) f p v) (mfderiv I 𝓘(ℝ, E) f p w) := by
  let T := e.symm.trans f
  have hep : e p ∈ T.source := by
    refine ⟨e.map_source he, ?_⟩
    change e.symm (e p) ∈ f.source
    exact Eq.mpr (congrArg (fun q : M => q ∈ f.source) (e.left_inv he)) hf
  have hr : T (e p) = f p := congrArg f (e.left_inv he)
  have hd := chartDerivative_transition e f he hf
  have hv : fderiv ℝ T (e p) (mfderiv I 𝓘(ℝ, E) e p v) =
      mfderiv I 𝓘(ℝ, E) f p v := congrArg (fun L : E →L[ℝ] E => L v) hd
  have hw : fderiv ℝ T (e p) (mfderiv I 𝓘(ℝ, E) e p w) =
      mfderiv I 𝓘(ℝ, E) f p w := congrArg (fun L : E →L[ℝ] E => L w) hd
  have h := chartSectional_transition g hn e.symm f.symm hep
    (mfderiv I 𝓘(ℝ, E) e p v) (mfderiv I 𝓘(ℝ, E) e p w)
  change DifferentialGeometry.Analysis.coefficientSectional (pullbackCoefficients g e.symm)
      (e p) (mfderiv I 𝓘(ℝ, E) e p v) (mfderiv I 𝓘(ℝ, E) e p w) =
    DifferentialGeometry.Analysis.coefficientSectional (pullbackCoefficients g f.symm)
      (T (e p)) (fderiv ℝ T (e p) (mfderiv I 𝓘(ℝ, E) e p v))
        (fderiv ℝ T (e p) (mfderiv I 𝓘(ℝ, E) e p w)) at h
  rw [hr, hv, hw] at h
  exact h

def sectionalCurvature [FiniteDimensional ℝ E]
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (p : M) (v w : TangentSpace I p) : ℝ :=
  DifferentialGeometry.Analysis.coefficientSectional
    (pullbackCoefficients g (extChartAt I p).symm) (extChartAt I p p)
    (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p v)
    (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p w)

@[simp]
theorem sectionalCurvature_zero_left [FiniteDimensional ℝ E]
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (p : M) (w : TangentSpace I p) : g.sectionalCurvature p 0 w = 0 := by
  let b := pullbackCoefficients g (extChartAt I p).symm
  let D : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I p) p
  change DifferentialGeometry.Analysis.coefficientSectional b (extChartAt I p p) (D 0) (D w) = 0
  rw [D.map_zero]
  simp [DifferentialGeometry.Analysis.coefficientSectional]

@[simp]
theorem sectionalCurvature_zero_right [FiniteDimensional ℝ E]
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p) : g.sectionalCurvature p v 0 = 0 := by
  let b := pullbackCoefficients g (extChartAt I p).symm
  let D : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I p) p
  change DifferentialGeometry.Analysis.coefficientSectional b (extChartAt I p p) (D v) (D 0) = 0
  rw [D.map_zero]
  simp [DifferentialGeometry.Analysis.coefficientSectional]

theorem sectionalCurvature_eq_zero_of_not_linearIndependent [FiniteDimensional ℝ E]
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (p : M) (v w : TangentSpace I p) (hdep : ¬LinearIndependent ℝ ![v, w]) :
    g.sectionalCurvature p v w = 0 := by
  by_cases hv : v = 0
  · rw [hv]
    exact sectionalCurvature_zero_left g p w
  · obtain ⟨a, ha⟩ : ∃ a : ℝ, a • v = w := by
      simpa only [LinearIndependent.pair_iff' hv, not_forall, not_not] using hdep
    rw [← ha]
    let b := pullbackCoefficients g (extChartAt I p).symm
    let D : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I p) p
    let x := extChartAt I p p
    let u : E := v
    change DifferentialGeometry.Analysis.coefficientSectional b x (D u) (D (a • u)) = 0
    rw [D.map_smul]
    have hden : b x (D u) (D u) * b x (a • D u) (a • D u) -
        (b x (D u) (a • D u)) ^ 2 = 0 := by
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
      ring
    unfold DifferentialGeometry.Analysis.coefficientSectional
    rw [hden, div_zero]

end

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 3 M]
  {n : ℕ∞ω}

theorem sectionalCurvature_eq_of_span_eq [FiniteDimensional ℝ E] [I.Boundaryless]
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hn : (2 : ℕ∞ω) ≤ n) (p : M) {v w v' w' : TangentSpace I p}
    (hspan : Submodule.span ℝ ({v', w'} : Set (TangentSpace I p)) =
      Submodule.span ℝ ({v, w} : Set (TangentSpace I p))) :
    g.sectionalCurvature p v' w' = g.sectionalCurvature p v w := by
  by_cases hvw : LinearIndependent ℝ ![v', w']
  · let φ := DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 p
    have hp : φ p ∈ φ.symm.source := φ.map_source (mem_extChartAt_source p)
    have hreg := contDiffOn_pullbackCoefficients g hn φ.symm.open_source φ.symm.contMDiffOn
    have hco := isCoercive_chartCoefficients g φ.symm hp
    have h := DifferentialGeometry.Analysis.coefficientSectional_eq_of_span_eq
      ((hreg (φ p) hp).contDiffAt (φ.symm.open_source.mem_nhds hp))
      (Filter.Eventually.of_forall (fun y => pullbackCoefficients_symm g φ.symm y))
      hco hvw hspan
    unfold sectionalCurvature
    rw [mfderiv_extChartAt_self]
    change DifferentialGeometry.Analysis.coefficientSectional
        (pullbackCoefficients g φ.symm) (φ p) v' w' =
      DifferentialGeometry.Analysis.coefficientSectional
        (pullbackCoefficients g φ.symm) (φ p) v w
    exact h
  · have hdep : ¬LinearIndependent ℝ ![v, w] := fun h =>
      hvw (DifferentialGeometry.Analysis.linearIndependent_pair_of_span_eq h hspan.symm)
    rw [sectionalCurvature_eq_zero_of_not_linearIndependent g p v' w' hvw,
      sectionalCurvature_eq_zero_of_not_linearIndependent g p v w hdep]

theorem sectionalCurvature_eq_coefficientSectional [FiniteDimensional ℝ E] [I.Boundaryless]
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hn : (2 : ℕ∞ω) ≤ n) (e : PartialDiffeomorph I 𝓘(ℝ, E) M E 3)
    {p : M} (hp : p ∈ e.source) (v w : TangentSpace I p) :
    g.sectionalCurvature p v w =
      DifferentialGeometry.Analysis.coefficientSectional
        (fun y => (g.inner (e.symm y) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
          (mfderiv 𝓘(ℝ, E) I e.symm y : E →L[ℝ] E)
          (mfderiv 𝓘(ℝ, E) I e.symm y : E →L[ℝ] E))
        (e p) (mfderiv I 𝓘(ℝ, E) e p v) (mfderiv I 𝓘(ℝ, E) e p w) := by
  exact chartSectional_eq g hn
    (DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 p) e
    (mem_extChartAt_source p) hp v w

theorem sectionalCurvature_eq_of_partialDiffeomorph_pullback
    [FiniteDimensional ℝ E] [I.Boundaryless]
    {H' N : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 3 N]
    {m : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J m E (TangentSpace J : N → Type _))
    (hn : (2 : ℕ∞ω) ≤ n) (hm : (2 : ℕ∞ω) ≤ m)
    (f : PartialDiffeomorph I J M N 3)
    (hmetric : ∀ q ∈ f.source, ∀ v w : TangentSpace I q,
      g.inner q v w = h.inner (f q) (mfderiv I J f q v) (mfderiv I J f q w))
    {p : M} (hp : p ∈ f.source) (v w : TangentSpace I p) :
    g.sectionalCurvature p v w =
      h.sectionalCurvature (f p) (mfderiv I J f p v) (mfderiv I J f p w) := by
  let ψ := DifferentialGeometry.PartialDiffeomorph.extChartAt J 3 (f p)
  let e := f.trans ψ
  have hψ : f p ∈ ψ.source := mem_extChartAt_source (f p)
  have hep : p ∈ e.source := ⟨hp, hψ⟩
  have hcoeff := chartCoefficients_pullback g h f ψ hmetric hp hψ
  have hd : (mfderiv I 𝓘(ℝ, E) e p : E →L[ℝ] E) =
      (mfderiv J 𝓘(ℝ, E) ψ (f p) : E →L[ℝ] E).comp
        (mfderiv I J f p : E →L[ℝ] E) :=
    mfderiv_comp p (ψ.mdifferentiableAt (by norm_num) hψ)
      (f.mdifferentiableAt (by norm_num) hp)
  rw [sectionalCurvature_eq_coefficientSectional g hn e hep,
    sectionalCurvature_eq_coefficientSectional h hm ψ hψ]
  change DifferentialGeometry.Analysis.coefficientSectional
      (pullbackCoefficients g e.symm) (ψ (f p))
      (mfderiv I 𝓘(ℝ, E) e p v) (mfderiv I 𝓘(ℝ, E) e p w) =
    DifferentialGeometry.Analysis.coefficientSectional
      (pullbackCoefficients h ψ.symm) (ψ (f p))
      (mfderiv J 𝓘(ℝ, E) ψ (f p) (mfderiv I J f p v))
      (mfderiv J 𝓘(ℝ, E) ψ (f p) (mfderiv I J f p w))
  rw [hd]
  exact coefficientSectional_congr hcoeff _ _

theorem sectionalCurvature_eq_of_pullback [FiniteDimensional ℝ E] [I.Boundaryless]
    {H' N : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 3 N]
    {m : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J m E (TangentSpace J : N → Type _))
    (hn : (2 : ℕ∞ω) ≤ n) (hm : (2 : ℕ∞ω) ≤ m) (f : M ≃ₘ^3⟮I, J⟯ N)
    (hmetric : ∀ q, ∀ v w : TangentSpace I q,
      g.inner q v w = h.inner (f q) (mfderiv I J f q v) (mfderiv I J f q w))
    (p : M) (v w : TangentSpace I p) :
    g.sectionalCurvature p v w =
      h.sectionalCurvature (f p) (mfderiv I J f p v) (mfderiv I J f p w) := by
  exact sectionalCurvature_eq_of_partialDiffeomorph_pullback g h hn hm
    f.toPartialDiffeomorph (fun q _ => hmetric q) (Set.mem_univ p) v w

end Bundle.ContMDiffRiemannianMetric
