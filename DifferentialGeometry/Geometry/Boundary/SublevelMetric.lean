import DifferentialGeometry.Topology.Morse.SublevelBoundaryDiffeomorph
import DifferentialGeometry.Topology.Morse.LevelSetInclusion
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Boundary.Metric.Induced
import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Topology.Morse.CriticalPoints

namespace DifferentialGeometry.Topology.Morse

open Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]

def sublevelMetric [T2Space M] (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace (m + 1)) (SublevelSpace f a) := by
  letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
  exact g.pullback (fun y => y.1) (contMDiff_manifoldSublevelEuclideanInclusion I f a hf hreg)
    (fun x => (mfderiv_manifoldSublevelEuclideanInclusion_bijective I f a hf hreg x).injective)

@[simp]
theorem sublevelMetric_inner [T2Space M] (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    ∀ x v w, (sublevelMetric I g f a hf hreg).inner x v w =
      g.inner x.1
        (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I (fun y => y.1) x v)
        (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I (fun y => y.1) x w) :=
  fun _ _ _ => rfl

end

end DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.Morse

open Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]

def levelSetMetric [T2Space M] (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldLevelSetChartedSpace I f a hf hreg
    letI := manifoldLevelSetIsManifold I f a hf hreg
    SmoothRiemannianMetric 𝓘(ℝ, MorseModel m) (LevelSetSpace f a) := by
  letI := manifoldLevelSetChartedSpace I f a hf hreg
  letI := manifoldLevelSetIsManifold I f a hf hreg
  exact g.pullback (fun y => y.1) (contMDiff_levelSetInclusion I f a hf hreg)
    (mfderiv_manifoldLevelSetInclusion_injective I f a hf hreg)

@[simp]
theorem levelSetMetric_inner [T2Space M] (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldLevelSetChartedSpace I f a hf hreg
    letI := manifoldLevelSetIsManifold I f a hf hreg
    ∀ x v w, (levelSetMetric I g f a hf hreg).inner x v w =
      g.inner x.1 (mfderiv 𝓘(ℝ, MorseModel m) I (fun y => y.1) x v)
        (mfderiv 𝓘(ℝ, MorseModel m) I (fun y => y.1) x w) := fun _ _ _ => rfl

theorem inducedMetric_sublevelMetric_inner [T2Space M] (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    letI := manifoldLevelSetChartedSpace I f a hf hreg
    letI := manifoldLevelSetIsManifold I f a hf hreg
    ∀ x v w, (inducedMetric (sublevelMetric I g f a hf hreg)).inner x v w =
      (levelSetMetric I g f a hf hreg).inner (manifoldSublevelBoundaryDiffeomorph I f a hf hreg x)
        (mfderiv (HasSmoothBoundary.boundaryModel (modelWithCornersEuclideanHalfSpace (m + 1)))
          𝓘(ℝ, MorseModel m) (manifoldSublevelBoundaryDiffeomorph I f a hf hreg) x v)
        (mfderiv (HasSmoothBoundary.boundaryModel (modelWithCornersEuclideanHalfSpace (m + 1)))
          𝓘(ℝ, MorseModel m) (manifoldSublevelBoundaryDiffeomorph I f a hf hreg) x w) := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let := manifoldSublevelEuclidean_isManifold I f a hf hreg
  let := manifoldLevelSetChartedSpace I f a hf hreg
  let := manifoldLevelSetIsManifold I f a hf hreg
  intro x v w
  let Φ := manifoldSublevelBoundaryDiffeomorph I f a hf hreg
  have hb := (boundaryInclusion_contMDiff (I := modelWithCornersEuclideanHalfSpace (m + 1))
    (M := SublevelSpace f a) x).mdifferentiableAt (by simp)
  have hi := (contMDiff_manifoldSublevelEuclideanInclusion I f a hf hreg x.1).mdifferentiableAt (by simp)
  have hl := (contMDiff_levelSetInclusion I f a hf hreg).contMDiffAt
    (x := Φ x) |>.mdifferentiableAt (by simp)
  have hΦ := (Φ.contMDiff x).mdifferentiableAt (by simp)
  have heq : (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
      (fun y : SublevelSpace f a => y.1) x.1).comp (boundaryInclusionMfderiv x) =
      (mfderiv 𝓘(ℝ, MorseModel m) I (fun y : LevelSetSpace f a => y.1) (Φ x)).comp
        (mfderiv (HasSmoothBoundary.boundaryModel (modelWithCornersEuclideanHalfSpace (m + 1)))
          𝓘(ℝ, MorseModel m) Φ x) := by
    have hleft := mfderiv_comp x hi hb
    have hright := mfderiv_comp x hl hΦ
    change mfderiv
      (HasSmoothBoundary.boundaryModel (modelWithCornersEuclideanHalfSpace (m + 1))) I
      (fun y : BoundaryManifold (modelWithCornersEuclideanHalfSpace (m + 1))
        (SublevelSpace f a) => y.1.1) x = _ at hleft hright
    exact hleft.symm.trans hright
  rw [inducedMetric_inner_apply, sublevelMetric_inner, levelSetMetric_inner]
  have hev := congrArg (fun L => L v) heq
  have hew := congrArg (fun L => L w) heq
  exact congrArg₂ (fun v w => g.inner x.1.1 v w) hev hew

theorem inducedMetric_sublevelMetric_eq_pullback [T2Space M] (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    letI := manifoldLevelSetChartedSpace I f a hf hreg
    letI := manifoldLevelSetIsManifold I f a hf hreg
    inducedMetric (sublevelMetric I g f a hf hreg) =
      (levelSetMetric I g f a hf hreg).pullback
        (manifoldSublevelBoundaryDiffeomorph I f a hf hreg)
        (manifoldSublevelBoundaryDiffeomorph I f a hf hreg).contMDiff
        (fun x => ((manifoldSublevelBoundaryDiffeomorph I f a hf hreg).mfderivToContinuousLinearEquiv
          (by simp) x).injective) := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let := manifoldSublevelEuclidean_isManifold I f a hf hreg
  let := manifoldLevelSetChartedSpace I f a hf hreg
  let := manifoldLevelSetIsManifold I f a hf hreg
  apply SmoothRiemannianMetric.ext_inner
  exact inducedMetric_sublevelMetric_inner I g f a hf hreg

end

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem levelSetMetric_transContinuousLinearEquiv_inner
    (g : SmoothRiemannianMetric I M) {m : ℕ} (e : E ≃L[ℝ] MorseModel (m + 1))
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    let J := I.transContinuousLinearEquiv e
    let hfJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ f :=
      (e.contMDiff_transContinuousLinearEquiv_left).mpr hf
    let hregJ : ∀ x : M, f x = a → ¬ IsCriticalPointAt J f x := fun x hx hc =>
      hreg x hx ((isCriticalPointAt_transContinuousLinearEquiv_iff I e f x).mp hc)
    letI := manifoldLevelSetChartedSpace J f a hfJ hregJ
    letI := manifoldLevelSetIsManifold J f a hfJ hregJ
    ∀ (x : LevelSetSpace f a) (v w : TangentSpace 𝓘(ℝ, MorseModel m) x),
      (levelSetMetric J (g.transContinuousLinearEquiv e) f a hfJ hregJ).inner x v w =
        g.inner x.1 (mfderiv 𝓘(ℝ, MorseModel m) I (Subtype.val : LevelSetSpace f a → M) x v)
          (mfderiv 𝓘(ℝ, MorseModel m) I (Subtype.val : LevelSetSpace f a → M) x w) := by
  let J := I.transContinuousLinearEquiv e
  let hfJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ f :=
    (e.contMDiff_transContinuousLinearEquiv_left).mpr hf
  let hregJ : ∀ x : M, f x = a → ¬ IsCriticalPointAt J f x := fun x hx hc =>
    hreg x hx ((isCriticalPointAt_transContinuousLinearEquiv_iff I e f x).mp hc)
  let := manifoldLevelSetChartedSpace J f a hfJ hregJ
  let := manifoldLevelSetIsManifold J f a hfJ hregJ
  change ∀ (x : LevelSetSpace f a) (v w : TangentSpace 𝓘(ℝ, MorseModel m) x),
    (levelSetMetric J (g.transContinuousLinearEquiv e) f a hfJ hregJ).inner x v w =
      g.inner x.1 (mfderiv 𝓘(ℝ, MorseModel m) I (Subtype.val : LevelSetSpace f a → M) x v)
        (mfderiv 𝓘(ℝ, MorseModel m) I (Subtype.val : LevelSetSpace f a → M) x w)
  intro x v w
  have hid : MDifferentiableAt J I id x.1 :=
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm.contMDiff.mdifferentiableAt
      (by simp)
  have hi := (contMDiff_levelSetInclusion J f a hfJ hregJ).mdifferentiableAt (x := x) (by simp)
  have hD (z : TangentSpace 𝓘(ℝ, MorseModel m) x) :
      mfderiv J I id x.1 (mfderiv 𝓘(ℝ, MorseModel m) J (Subtype.val : LevelSetSpace f a → M) x z) =
        mfderiv 𝓘(ℝ, MorseModel m) I (Subtype.val : LevelSetSpace f a → M) x z :=
    (mfderiv_comp_apply x hid hi z).symm
  rw [levelSetMetric_inner, SmoothRiemannianMetric.transContinuousLinearEquiv_inner, hD, hD]

end

end DifferentialGeometry.Topology.Morse
