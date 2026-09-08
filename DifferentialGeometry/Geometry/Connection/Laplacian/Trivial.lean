import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle
import DifferentialGeometry.Geometry.Connection.Trivial
import DifferentialGeometry.Geometry.Operator.GradientRegularity
import Mathlib.Analysis.InnerProductSpace.Trace

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem rawBundleConnLap_trivial_eq_laplacian [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    rawBundleConnLap g (CovariantDerivative.trivial I M ℝ) f x =
      laplacian (LeviCivita g) g f x := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let targetNorm : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let _ : ∀ y : M, SeminormedAddCommGroup (TangentSpace I y) :=
    fun y => (targetNorm y).toSeminormedAddCommGroup
  let _ : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) := fun y => Bundle.instInnerProductSpaceReal y
  let frame : Fin (Module.finrank ℝ E) → TangentSpace I x := fun i => smoothOrthoFrame g x i x
  have hframe : Orthonormal ℝ frame := by
    rw [orthonormal_iff_ite]
    intro i j
    let _ : NeZero (Module.finrank ℝ E) := ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
    exact smoothOrthoFrame_orthonormal_at_center g x i j
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  let b := OrthonormalBasis.mk hframe
    ((hframe.linearIndependent.span_eq_top_of_card_eq_finrank' hcard).ge)
  rw [laplacian, divergence, LinearMap.trace_eq_sum_inner _ b, rawBundleConnLap_def]
  apply Finset.sum_congr rfl
  intro i _
  let _ : NeZero (Module.finrank ℝ E) := ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
  have hX := (smoothOrthoFrame_smooth g x i).mdifferentiableAt (x := x) (by simp)
  have hfSection : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) 2 (T% f) x :=
    (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) x).mpr hf
  have hθ := ((CovariantDerivative.trivial_contMDiff I M ℝ ∞).contMDiffAt
    (m := 1) hfSection (by norm_num)).mdifferentiableAt one_ne_zero
  change MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
    (fun y => (⟨y, mvfderiv I f y⟩ : TotalSpace (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ))) x at hθ
  have hpair := cotangentCov_dualPairing (LeviCivita g) hθ hX (frame i)
  have hflat : metricFlat g (gradientFun g f) = mvfderiv I f := by
    funext y
    ext v
    exact inner_gradientFun g f y v
  have hdual := cotangentCov_metricDuality g ((gradientFun_contMDiffAt_one g hf).mdifferentiableAt one_ne_zero)
    (frame i) (frame i)
  rw [hflat] at hdual
  change mvfderiv I (fun y => mvfderiv I f y (smoothOrthoFrame g x i y)) x (frame i) -
    mvfderiv I f x (LeviCivita g (smoothOrthoFrame g x i) x (frame i)) = _
  rw [hpair, hdual, add_sub_cancel_right]
  change g.inner x _ (frame i) = g.inner x (b i) _
  have hb : b i = frame i := congrFun (OrthonormalBasis.coe_mk _ _) i
  rw [hb, g.symm]
  rfl

end DifferentialGeometry.Geometry.Connection
