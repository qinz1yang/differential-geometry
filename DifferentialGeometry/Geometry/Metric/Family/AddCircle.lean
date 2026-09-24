import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Geometry.Metric.AddCircle
import DifferentialGeometry.Geometry.Metric.Conformal.Basic
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Topology.Manifold.AddCircle.PeriodicExtension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

open Bundle Filter Set
open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold Topology

namespace AddCircle

theorem exists_metricFamilySmoothOn_extension_of_positive_periodic
    {a b : ℝ} {q : ℝ × ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q ((univ : Set ℝ) ×ˢ Icc a b))
    (hper : ∀ t ∈ Icc a b, Function.Periodic (fun x => q (x, t)) 1)
    (hpos : ∀ x : ℝ, ∀ t ∈ Icc a b, 0 < q (x, t)) :
    ∃ g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)),
      (∀ D : RealTimeInterval, MetricFamilySmoothOn D g) ∧
        ∀ t ∈ Icc a b, ∀ x : ℝ,
          (g t).inner (x : AddCircle (1 : ℝ))
            (parameterTangent (x : AddCircle (1 : ℝ)))
            (parameterTangent (x : AddCircle (1 : ℝ))) = q (x, t) := by
  have hswap : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => q (p.2, p.1))
      (Icc a b ×ˢ (univ : Set ℝ)) :=
    hq.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hp => ⟨hp.2, hp.1⟩)
  have hlog : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Real.log (q (p.2, p.1)))
      (Icc a b ×ˢ (univ : Set ℝ)) :=
    hswap.log (fun p hp => (hpos p.2 p.1 hp.1).ne')
  have hlogper : ∀ t ∈ Icc a b,
      Function.Periodic (fun x => Real.log (q (x, t))) 1 := by
    intro t ht x
    exact congrArg Real.log (hper t ht x)
  obtain ⟨γ, hγ, hγeq⟩ := exists_contMDiff_extension_of_periodic hlog hlogper
  let u : ℝ → C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯ := fun t =>
    ⟨fun z => γ (t, z) / 2,
      (hγ.comp (contMDiff_const.prodMk contMDiff_id)).div_const 2⟩
  let g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) :=
    fun t => DifferentialGeometry.conformalMetric flatMetric (u t)
  have hscale : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × AddCircle (1 : ℝ) => Real.exp (2 * (γ p / 2))) :=
    Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul (hγ.div_const 2))
  refine ⟨g, ?_, ?_⟩
  · intro D
    apply metricFamilySmoothOn_of_contMDiffOn
    exact (hscale.smul_bundle (flatMetric.contMDiff.comp contMDiff_snd)).contMDiffOn
  · intro t ht x
    change Real.exp (2 * (γ (t, (x : AddCircle (1 : ℝ))) / 2)) *
      flatMetric.inner (x : AddCircle (1 : ℝ))
        (parameterTangent (x : AddCircle (1 : ℝ)))
        (parameterTangent (x : AddCircle (1 : ℝ))) = q (x, t)
    rw [flatMetric_parameterTangent_unit, mul_one, hγeq t ht x]
    rw [show 2 * (Real.log (q (x, t)) / 2) = Real.log (q (x, t)) by ring]
    exact Real.exp_log (hpos x t ht)

theorem exists_metricFamilySmoothOn_extension_of_periodic_sq
    {a b : ℝ} {v : ℝ × ℝ → ℝ}
    (hv : ContDiffOn ℝ ∞ v ((univ : Set ℝ) ×ˢ Icc a b))
    (hper : ∀ t ∈ Icc a b, Function.Periodic (fun x => v (x, t)) 1)
    (hne : ∀ x : ℝ, ∀ t ∈ Icc a b, v (x, t) ≠ 0) :
    ∃ g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)),
      (∀ D : RealTimeInterval, MetricFamilySmoothOn D g) ∧
        ∀ t ∈ Icc a b, ∀ x : ℝ,
          (g t).inner (x : AddCircle (1 : ℝ))
            (parameterTangent (x : AddCircle (1 : ℝ)))
            (parameterTangent (x : AddCircle (1 : ℝ))) = v (x, t) ^ 2 := by
  apply exists_metricFamilySmoothOn_extension_of_positive_periodic (hv.pow 2)
  · intro t ht x
    exact congrArg (fun s : ℝ => s ^ 2) (hper t ht x)
  · intro x t ht
    exact sq_pos_of_ne_zero (hne x t ht)

end AddCircle
