import DifferentialGeometry.Analysis.Sobolev.Euclidean.Trace.Coordinates
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Trace.BoundaryConvergence

noncomputable section

open MeasureTheory Set Filter
open DifferentialGeometry.Topology
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "μV" => volume.restrict (Metric.ball (0 : V) 1)

theorem integral_weakGrad_snd_mul_add_eq_of_tendsto_diskTrace
    (u : ℕ → C(closedDisk, ℝ)) {η : C(loopCircle, ℝ)}
    (htrace : Tendsto (fun n => diskTrace (u n)) atTop (𝓝 η))
    {K : ℕ → ℝ≥0}
    (hLip : ∀ n, LipschitzWith (K n)
      (fun x : V => Geometry.diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
    (hf : ∀ n, DeGiorgi.MemW1pWitness 2
      (fun x : V => Geometry.diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x))
      (Metric.ball (0 : V) 1))
    {v : V → ℝ} (hv : DeGiorgi.MemW1pWitness 2 v (Metric.ball (0 : V) 1))
    (hrep : ∀ n, (fun x => (hf n).weakGrad x 1) =ᵐ[μV]
      (fun x => fderiv ℝ (fun y : V => Geometry.diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) x (EuclideanSpace.single 1 1)))
    (hlim : Tendsto (fun n => eLpNorm (fun x : V => Geometry.diskExtension (u n)
      (Complex.orthonormalBasisOneI.repr.symm x) - v x) 2 μV) atTop (𝓝 0))
    (hweak : ∀ z : Lp V 2 μV,
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hf n)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness hv) z)))
    {L : ℝ≥0} {g : ℝ × ℝ → ℝ} (hg : LipschitzWith L g) :
    (∫ x in Metric.ball (0 : V) 1,
      hv.weakGrad x 1 * g (euclideanPlaneProdEquiv x) +
        v x * fderiv ℝ g (euclideanPlaneProdEquiv x) (0, 1)) =
      ∫ x in Ioo (-1 : ℝ) 1,
        η (Geometry.semicircleBoundaryParameter true x) * g (x, Real.sqrt (1 - x ^ 2)) -
        η (Geometry.semicircleBoundaryParameter false x) * g (x, -Real.sqrt (1 - x ^ 2)) := by
  have he (p : ℝ × ℝ) :
      Complex.orthonormalBasisOneI.repr.symm (euclideanPlaneProdEquiv.symm p) =
        (⟨p.1, p.2⟩ : ℂ) := by
    apply Complex.equivRealProdCLM.injective
    change euclideanPlaneProdEquiv (euclideanPlaneProdEquiv.symm p) = p
    exact euclideanPlaneProdEquiv.apply_symm_apply p
  refine integral_weakGrad_snd_mul_add_eq_boundary_of_tendsto_disk hLip hf hv hrep hlim hweak
    ?_ ?_ hg
  · simpa only [he, Bool.false_eq_true, ↓reduceIte] using
      Geometry.tendstoUniformlyOn_diskExtension_semicircle_of_tendsto_diskTrace htrace false
  · simpa only [he, ↓reduceIte] using
      Geometry.tendstoUniformlyOn_diskExtension_semicircle_of_tendsto_diskTrace htrace true

end DifferentialGeometry.Analysis

end

noncomputable section

open MeasureTheory Set Filter ContinuousMap
open DifferentialGeometry.Topology
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "μV" => volume.restrict (Metric.ball (0 : V) 1)

theorem integral_weakGrad_snd_mul_add_eq_of_tendsto_scalar_diskTrace
    {W : Type*} [TopologicalSpace W]
    (P : C(W, ℝ)) (u : ℕ → C(closedDisk, W))
    {η : C(loopCircle, W)} (htrace : Tendsto (fun n => diskTrace (u n)) atTop (𝓝 η))
    {K : ℕ → ℝ≥0}
    (hLip : ∀ n, LipschitzWith (K n) (fun x : V =>
      Geometry.diskExtension (P.comp (u n)) (Complex.orthonormalBasisOneI.repr.symm x)))
    (hf : ∀ n, DeGiorgi.MemW1pWitness 2
      (fun x : V => Geometry.diskExtension (P.comp (u n))
        (Complex.orthonormalBasisOneI.repr.symm x)) (Metric.ball (0 : V) 1))
    {v : V → ℝ} (hv : DeGiorgi.MemW1pWitness 2 v (Metric.ball (0 : V) 1))
    (hrep : ∀ n, (fun x => (hf n).weakGrad x 1) =ᵐ[μV]
      (fun x => fderiv ℝ (fun y : V => Geometry.diskExtension (P.comp (u n))
        (Complex.orthonormalBasisOneI.repr.symm y)) x (EuclideanSpace.single 1 1)))
    (hlim : Tendsto (fun n => eLpNorm (fun x : V =>
      Geometry.diskExtension (P.comp (u n)) (Complex.orthonormalBasisOneI.repr.symm x) - v x) 2 μV)
      atTop (𝓝 0))
    (hweak : ∀ z : Lp V 2 μV,
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hf n)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness hv) z)))
    {L : ℝ≥0} {g : ℝ × ℝ → ℝ} (hg : LipschitzWith L g) :
    (∫ x in Metric.ball (0 : V) 1,
      hv.weakGrad x 1 * g (euclideanPlaneProdEquiv x) +
        v x * fderiv ℝ g (euclideanPlaneProdEquiv x) (0, 1)) =
      ∫ x in Ioo (-1 : ℝ) 1,
        P (η (Geometry.semicircleBoundaryParameter true x)) * g (x, Real.sqrt (1 - x ^ 2)) -
        P (η (Geometry.semicircleBoundaryParameter false x)) * g (x, -Real.sqrt (1 - x ^ 2)) := by
  have htrace' : Tendsto (fun n => diskTrace (P.comp (u n))) atTop (𝓝 (P.comp η)) :=
    ((continuous_postcomp P).tendsto η).comp htrace
  exact integral_weakGrad_snd_mul_add_eq_of_tendsto_diskTrace
    (fun n => P.comp (u n)) htrace' hLip hf hv hrep hlim hweak hg

end DifferentialGeometry.Analysis

end
