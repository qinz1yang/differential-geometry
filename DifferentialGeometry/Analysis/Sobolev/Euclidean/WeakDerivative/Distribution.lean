import DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives
import Mathlib.Analysis.Distribution.Distribution

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem integrable_mul_fderiv_apply_of_memLp
    {Ω : Set E} {w : E → ℝ} (hw : MemLp w 2 (volume.restrict Ω))
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (i : Fin d) :
    Integrable (fun x => w x * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
      (volume.restrict Ω) := by
  have hdφ : MemLp (fun x : E => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) 2
      (volume.restrict Ω) :=
    (((hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const).memLp_of_hasCompactSupport
        (hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))).restrict _
  exact MemLp.integrable_mul hw hdφ

noncomputable def weakPartialDistribution
    (Ω : TopologicalSpace.Opens E) (w : E → ℝ) (i : Fin d) :
    Distribution Ω ℝ ⊤ :=
  let T : Distribution Ω ℝ ⊤ :=
    ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℝ) ℝ
      {S : Set (TestFunction Ω ℝ ⊤) | IsCompact S}
      (TestFunction.integralAgainstBilinCLM (n := ⊤) (ContinuousLinearMap.lsmul ℝ ℝ)
        (volume.restrict (Ω : Set E)) w)
  Distribution.lineDerivCLM (k := ⊤) (n := ⊤) (EuclideanSpace.single i 1) T

omit [NeZero d] in
@[simp] theorem weakPartialDistribution_apply_of_memLp
    {Ω : TopologicalSpace.Opens E} {w : E → ℝ}
    (hw : MemLp w 2 (volume.restrict (Ω : Set E))) (i : Fin d)
    (φ : TestFunction Ω ℝ ⊤) :
    weakPartialDistribution Ω w i φ =
      -∫ x in Ω, w x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
  have hwloc : LocallyIntegrable w (volume.restrict (Ω : Set E)) :=
    hw.locallyIntegrable (by norm_num)
  have hwon : LocallyIntegrableOn w (Ω : Set E)
      (volume.restrict (Ω : Set E)) := hwloc.locallyIntegrableOn _
  rw [weakPartialDistribution, Distribution.lineDerivCLM_apply]
  simp only [ContinuousLinearMap.toUniformConvergenceCLM_apply]
  rw [TestFunction.integralAgainstBilinCLM_eq_integral hwon]
  have hφd : Differentiable ℝ (φ : E → ℝ) := φ.contDiff.differentiable (by simp)
  simp only [TestFunction.lineDerivCLM_apply, top_add, le_refl, if_true,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change lineDeriv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1) * w x =
    w x * (fderiv ℝ (φ : E → ℝ) x) (EuclideanSpace.single i 1)
  rw [hφd.differentiableAt.lineDeriv_eq_fderiv]
  ring

end DifferentialGeometry.Analysis.Sobolev.Euclidean
