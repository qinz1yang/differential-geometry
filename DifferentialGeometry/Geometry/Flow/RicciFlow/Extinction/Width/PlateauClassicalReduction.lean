import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.AreaBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ConformalDiskFromMorrey
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.InteriorConstDiskWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauClassicalExistence

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Extinction

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

def HasMinimizingSpanningConformalDisk (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q) : Prop :=
  ∃ u : InteriorSmoothDisk (I := I) (Q := Q),
    u.IsConformal g ∧ u.IsHarmonic g ∧
      IsSignedWeaklyMonotoneTrace u.map γ.toContinuousLoop ∧
      IntegrableOn (diskJacobian g u.map) (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ w : LipschitzDisk g,
        IsSignedWeaklyMonotoneTrace w.map γ.toContinuousLoop →
          diskArea g u.map ≤ diskArea g w.map) ∧
      ∀ w : SmoothDisk (I := I) (Q := Q),
        IsSignedWeaklyMonotoneTrace w.map γ.toContinuousLoop →
          diskArea g u.map ≤ diskArea g w.map

theorem hasConformalMinimizingInteriorDisk_of_hasMinimizingSpanningConformalDisk
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (h : HasMinimizingSpanningConformalDisk (I := I) (Q := Q) g γ) :
    HasConformalMinimizingInteriorDisk (I := I) (Q := Q) g γ := by
  obtain ⟨u, hconf, hharm, htrace, hfinite, hminL, hminS⟩ := h
  exact ⟨u, hconf, hharm, htrace, hfinite,
    fun w hw => hminL w (isSignedWeaklyMonotoneTrace_of_diskTrace_eq (u := ⇑w.map) hw),
    fun w hw => hminS w (isSignedWeaklyMonotoneTrace_of_diskTrace_eq (u := ⇑w.map) hw)⟩

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
theorem diskLocalTension_const (g : SmoothRiemannianMetric I Q) (q : Q) (z : ℂ) :
    diskLocalTension g (fun _ : ℂ => q) z = 0 := by
  have heq (v : ℂ) :
      covDerivAlong g (fun _ : ℝ => q)
        (fun t : ℝ => mfderiv 𝓘(ℝ, ℂ) I (fun _ : ℂ => q) (z + t • v) v) 0 = 0 := by
    have hfield : (fun t : ℝ =>
        (mfderiv 𝓘(ℝ, ℂ) I (fun _ : ℂ => q) (z + t • v) v : TangentSpace I q)) =
        fun _ : ℝ => (0 : TangentSpace I q) := by
      funext t
      exact congrArg (fun L : ℂ →L[ℝ] TangentSpace I q => L v) mfderiv_const
    rw [hfield]
    exact covDerivAlong_zero g (fun _ : ℝ => q) 0
  change _ + _ = (0 : TangentSpace I q)
  rw [heq 1, heq Complex.I]
  simp

theorem interiorSmoothDiskConst_isHarmonic (g : SmoothRiemannianMetric I Q) (q : Q) :
    (interiorSmoothDiskConst (I := I) (Q := Q) q).IsHarmonic g := by
  intro z hz F
  have hgerm : F.map =ᶠ[𝓝 (z : ℂ)] (fun _ : ℂ => q) := by
    filter_upwards [F.isOpen_domain.mem_nhds F.mem_domain,
      Metric.isOpen_ball.mem_nhds hz] with w hwd hwb
    rw [F.agrees ⟨hwd, Metric.ball_subset_closedBall hwb⟩]
    simpa using congrFun (interiorSmoothDiskConst_diskExtension (I := I) (Q := Q) q) w
  exact (diskLocalTension_congr_germ g F.map (fun _ : ℂ => q) (z : ℂ) hgerm).trans
    (diskLocalTension_const (I := I) (Q := Q) g q (z : ℂ))

omit [FiniteDimensional ℝ E] in
theorem diskJacobian_const (g : SmoothRiemannianMetric I Q) (q : Q) (z : ℂ) :
    diskJacobian g (fun _ : Disk => q) z = 0 := by
  have hconst : diskExtension (fun _ : Disk => q) = fun _ : ℂ => q := by
    funext w
    rw [diskExtension]
    split_ifs <;> rfl
  rw [diskJacobian, hconst, parametricJacobian]
  split_ifs with h
  · have hzero : (fun i j : Fin 2 => g.inner q
        (mfderivWithin 𝓘(ℝ, ℂ) I (fun _ : ℂ => q)
          (Metric.closedBall (0 : ℂ) 1) z (diskBasis i))
        (mfderivWithin 𝓘(ℝ, ℂ) I (fun _ : ℂ => q)
          (Metric.closedBall (0 : ℂ) 1) z (diskBasis j))) =
        (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
      have hzj (j : Fin 2) : (mfderivWithin 𝓘(ℝ, ℂ) I (fun _ : ℂ => q)
          (Metric.closedBall (0 : ℂ) 1) z (diskBasis j) : E) = 0 :=
        congrArg (fun L : ℂ →L[ℝ] TangentSpace I q => L (diskBasis j)) mfderivWithin_const
      funext i j
      rw [hzj i, hzj j]
      simp
    rw [hzero, Matrix.det_zero]
    simp
  · rfl

theorem hasMinimizingSpanningConformalDisk_constLoops (g : SmoothRiemannianMetric I Q)
    (q : Q) :
    HasMinimizingSpanningConformalDisk (I := I) (Q := Q) g
      (regularLoopConst (I := I) (Q := Q) q) := by
  have hmap : ⇑(interiorSmoothDiskConst (I := I) (Q := Q) q).map = (fun _ : Disk => q) := rfl
  have hzero : diskArea g (fun _ : Disk => q) = 0 := by
    rw [diskArea_eq_riemannianDiskArea]
    exact Geometry.riemannianDiskArea_const g q
  refine ⟨interiorSmoothDiskConst (I := I) (Q := Q) q,
    interiorSmoothDiskConst_isConformal (I := I) (Q := Q) g q,
    interiorSmoothDiskConst_isHarmonic (I := I) (Q := Q) g q, ?_, ?_, ?_, ?_⟩
  · rw [regularLoopConst_toContinuousLoop]
    exact interiorSmoothDiskConst_isSignedWeaklyMonotoneTrace (I := I) (Q := Q) q
  · have hzeroJ : diskJacobian g (fun _ : Disk => q) = fun _ : ℂ => 0 :=
      funext (diskJacobian_const g q)
    rw [hmap, hzeroJ]
    exact integrableOn_zero
  · intro w _
    rw [hmap, hzero]
    exact diskArea_nonneg g w.map
  · intro w _
    rw [hmap, hzero]
    exact diskArea_nonneg g w.map

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
