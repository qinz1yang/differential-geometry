import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialSource

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem ae_memWkp_two_of_spatial_weak_partials
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {Ω : Set E}
    (hΩ : IsOpen Ω)
    (f : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (Df : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (DDf : Fin d → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (hDf : ∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => Df k (t, x)) (fun x => f (t, x)) Ω)
    (hDDf : ∀ k l, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv l
      (fun x => DDf k l (t, x)) (fun x => Df k (t, x)) Ω) :
    ∀ᵐ t ∂μ, MemWkp 2 2 (fun x => f (t, x)) Ω := by
  have hf : MemLp (f : Z × E → ℝ) 2 (μ.prod (volume.restrict Ω)) := Lp.memLp f
  have hDf' : ∀ k, MemLp (Df k : Z × E → ℝ) 2
      (μ.prod (volume.restrict Ω)) := fun k => Lp.memLp (Df k)
  have hDDf' : ∀ k l, MemLp (DDf k l : Z × E → ℝ) 2
      (μ.prod (volume.restrict Ω)) := fun k l => Lp.memLp (DDf k l)
  exact ae_memWkp_two_of_hasWeakPartialDeriv (p := (2 : ℝ≥0∞))
    (by norm_num) hΩ hf hDf' hDDf' hDf hDDf

end DifferentialGeometry.Analysis.Sobolev.Euclidean
