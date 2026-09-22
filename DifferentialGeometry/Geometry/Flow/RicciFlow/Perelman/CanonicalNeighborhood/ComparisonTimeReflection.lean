import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Scaling

section
set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open Surgery.Topology (ThreeSpace)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N]
  {h : ℝ → SmoothRiemannianMetric I N} {g : ℝ → SmoothRiemannianMetric I3 M}
  {F : N → M} {U : Set N}

def MetricComparisonOn.reflectTime
    {times : Set ℝ} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn h g F U times order eps)
    (tau : ℝ) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J)
    (hmap : MapsTo (fun s => tau - s) J times)
    (hdiff : ∀ b s, s ∈ J → ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace I y,
      DifferentiableWithinAt ℝ (fun r => C.jet b r y v) times (tau - s)) :
    MetricComparisonOn (fun s => h (tau - s)) (fun s => g (tau - s)) F U J order eps where
  pullback s := C.pullback (tau - s)
  pullback_eq s y hy v := C.pullback_eq (tau - s) y hy v
  jet b s := (-1 : ℝ) ^ b • C.jet b (tau - s)
  jet_zero := by
    intro s y v
    simp only [pow_zero, one_smul, C.jet_zero]
  jet_succ := by
    intro b s hs y hy v
    have hd : HasDerivWithinAt (fun r => C.jet b r y v)
        (C.jet (b + 1) (tau - s) y v) times (tau - s) := by
      rw [C.jet_succ b _ (hmap hs) y hy v]
      exact (hdiff b s hs y hy v).hasDerivWithinAt
    have ht : HasDerivAt (fun r : ℝ => tau - r) (-1) s := (hasDerivAt_id s).const_sub tau
    have hh := ((hd.scomp s ht.hasDerivWithinAt hmap).const_mul ((-1 : ℝ) ^ b)).derivWithin (hJ s hs)
    simpa only [ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply,
      smul_eq_mul, Function.comp_def, pow_succ, mul_assoc] using hh.symm
  equivalence s hs y hy v := C.equivalence _ (hmap hs) y hy v
  close := by
    intro a b hab s hs y hy
    rw [tensor02CovDerivNormWith_smul]
    simpa only [abs_pow, abs_neg, abs_one, one_pow, one_mul] using C.close a b hab _ (hmap hs) y hy

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
