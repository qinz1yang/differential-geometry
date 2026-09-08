import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeDerivativeEquation

noncomputable section

open MeasureTheory Filter Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet.MaximalRegularity

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]
variable {g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M}
variable {a T : ℝ}

theorem maximalRegularityDuhamelMap_exists_timeH1_deriv_of_nonautonomous_equation
    (hT : 0 < T) (u₀ : DirichletHs g (a + 1))
    (f : timeL2 (DirichletHs g a) T)
    (v : timeH1 (DirichletHs g (a + 2)) T)
    (hv : v.toFunL2 = maximalRegularityDuhamelSolField a hT u₀ f)
    (F : timeH1 (DirichletHs g a) T)
    (A : ℝ → DirichletHs g (a + 2) →L[ℝ] DirichletHs g a)
    (hA : ContDiffOn ℝ 1 A (Icc (0 : ℝ) T))
    (hAm : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hf : f = timeOp A hAm C hC (maximalRegularityDuhamelSolField a hT u₀ f) + F.toFunL2) :
    let u := maximalRegularityDuhamelMap a hT u₀ f
    ∃ w : timeH1 (DirichletHs g a) T,
      w.toFunL2 = u.deriv ∧
      (∀ t ∈ Icc (0 : ℝ) T, w.toFun t =
        dirichletHsLaplacian g a (v.toFun t) + A t (v.toFun t) + F.toFun t) ∧
      (w.deriv =ᵐ[timeMeasure T] fun t =>
        dirichletHsLaplacian g a (v.deriv t) +
          _root_.deriv A t (v.toFun t) + A t (v.deriv t) + F.deriv t) ∧
      ContDiffOn ℝ 1 u.toFun (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u.toFun
        (dirichletHsLaplacian g a (v.toFun t) + A t (v.toFun t) + F.toFun t)
          (Icc (0 : ℝ) T) t) := by
  intro u
  let L := dirichletHsLaplacian g a
  let B : ℝ → DirichletHs g (a + 2) →L[ℝ] DirichletHs g a := fun t => L + A t
  have hB : ContDiffOn ℝ 1 B (Icc (0 : ℝ) T) := contDiffOn_const.add hA
  have hBm : AEStronglyMeasurable B (timeMeasure T) := aestronglyMeasurable_const.add hAm
  let D : NNReal := ‖L‖₊ + C
  have hD : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (D : ℝ) := by
    filter_upwards [hC] with t ht
    exact (norm_add_le L (A t)).trans (add_le_add_right ht ‖L‖)
  have hop (q : timeL2 (DirichletHs g (a + 2)) T) :
      timeDirichletHsLaplacian g a q + timeOp A hAm C hC q = timeOp B hBm D hD q := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (timeDirichletHsLaplacian g a q) (timeOp A hAm C hC q),
      timeDirichletHsLaplacian_coeFn q, timeOp_apply_ae A hAm C hC q,
      timeOp_apply_ae B hBm D hD q] with t hs hl ha hb
    rw [hs, Pi.add_apply, hl, ha, hb]
    rfl
  have heq : u.deriv = timeOp B hBm D hD v.toFunL2 + F.toFunL2 := by
    have hu := maximalRegularityDuhamelMap_timeDeriv_eq hT u₀ f
    change u.deriv = _ at hu
    calc
      u.deriv = timeDirichletHsLaplacian g a
          (maximalRegularityDuhamelSolField a hT u₀ f) + f := hu
      _ = timeDirichletHsLaplacian g a (maximalRegularityDuhamelSolField a hT u₀ f) +
          (timeOp A hAm C hC (maximalRegularityDuhamelSolField a hT u₀ f) + F.toFunL2) :=
        congrArg (fun z => timeDirichletHsLaplacian g a
          (maximalRegularityDuhamelSolField a hT u₀ f) + z) hf
      _ = _ := by rw [← add_assoc, hop, ← hv]
  obtain ⟨w, hw, hwp, hwd, hC1, hpoint⟩ :=
    u.exists_timeH1_deriv_of_eq_timeOp v F B hB hBm D hD heq
  refine ⟨w, hw, ?_, ?_, hC1, ?_⟩
  · intro t ht
    exact hwp t ht
  · filter_upwards [hwd] with t ht
    rw [ht]
    simp only [B, deriv_const_add, add_apply]
    dsimp only [L]
    abel
  · intro t ht
    exact hpoint t ht

end DifferentialGeometry.Analysis.Parabolic.Dirichlet.MaximalRegularity
