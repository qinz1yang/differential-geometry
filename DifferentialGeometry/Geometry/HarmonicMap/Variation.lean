import DifferentialGeometry.Analysis.Sobolev.Euclidean.Composition
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Variation
import DifferentialGeometry.Geometry.Metric.Pullback.Retraction
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

noncomputable section

open Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {d n : ℕ}

local notation "P" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin n)

theorem exists_retracted_affine_variation_memW1p_energy_eq
    (g : SmoothRiemannianMetric I M) {Φ : M → F} {r : F → M} {U V : Set F}
    (hΦ : ContMDiff I 𝓘(ℝ, F) 1 Φ) (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) I 1 r U) (hleft : Function.LeftInverse r Φ)
    (hV : IsOpen V) (hΦV : range Φ ⊆ V) (hVU : V ⊆ U)
    (T : F → F) (hT : ContDiff ℝ 1 T) {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ T y‖ ≤ C) (hTV : EqOn T (Φ ∘ r) V)
    {Ω : Set P} (hΩ : IsOpen Ω) {f : P → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ range Φ)
    {c : P} {a : ℝ} (hball : Metric.closedBall c a ⊆ Ω)
    {φ : P → F} (hφ : ContDiff ℝ ∞ φ)
    (hφB : tsupport φ ⊆ Metric.ball c a) (t : ℝ)
    (htV : ∀ᵐ x ∂volume.restrict (Metric.ball c a), f x + t • φ x ∈ V) :
    ∃ hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => T (f x + t • φ x) i)
        (Metric.ball c a),
      (∀ x j, DeGiorgi.weakGradientColumn hw x j =
        fderiv ℝ T (f x + t • φ x)
          (DeGiorgi.weakGradientColumn hf x j +
            t • fderiv ℝ φ x (EuclideanSpace.single j 1))) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball c a), T (f x + t • φ x) ∈ range Φ) ∧
      (∀ᵐ x ∂volume.restrict Ω, x ∉ tsupport φ → T (f x + t • φ x) = f x) ∧
      (∃ b : ℝ, b < a ∧ tsupport φ ⊆ Metric.ball c b ∧
        ∀ᵐ x ∂volume.restrict Ω, x ∉ Metric.ball c b → T (f x + t • φ x) = f x) ∧
      ∀ᵐ x ∂volume.restrict (Metric.ball c a), ∀ j : Fin d,
        pullbackMetricCoefficients g r (T (f x + t • φ x))
          (DeGiorgi.weakGradientColumn hw x j) (DeGiorgi.weakGradientColumn hw x j) =
        pullbackMetricCoefficients g r (f x + t • φ x)
          (DeGiorgi.weakGradientColumn hf x j +
            t • fderiv ℝ φ x (EuclideanSpace.single j 1))
          (DeGiorgi.weakGradientColumn hf x j +
            t • fderiv ℝ φ x (EuclideanSpace.single j 1)) := by
  have hφs : HasCompactSupport φ :=
    (isCompact_closedBall c a).of_isClosed_subset (isClosed_tsupport φ)
      (hφB.trans Metric.ball_subset_closedBall)
  let haff := DeGiorgi.componentAffineVariationWitness hΩ hf hφ hφs t
  obtain ⟨hw, hgrad⟩ := Analysis.Sobolev.Euclidean.exists_memW1pWitnesses_comp_contDiff_on_ball
    hΩ haff T hT hC hball
  have hcolumn (x : P) (j : Fin d) : DeGiorgi.weakGradientColumn hw x j =
      fderiv ℝ T (f x + t • φ x)
        (DeGiorgi.weakGradientColumn hf x j +
          t • fderiv ℝ φ x (EuclideanSpace.single j 1)) := by
    rw [← DeGiorgi.weakGradientColumn_componentAffineVariationWitness hΩ hf hφ hφs t x j]
    ext i
    exact hgrad i x j
  have hmetric {y : F} (hy : y ∈ V) (v w : F) :
      pullbackMetricCoefficients g r (T y)
        (fderiv ℝ T y v) (fderiv ℝ T y w) = pullbackMetricCoefficients g r y v w := by
    have heq : T =ᶠ[𝓝 y] Φ ∘ r := hTV.eventuallyEq_of_mem (hV.mem_nhds hy)
    rw [heq.eq_of_nhds, heq.fderiv_eq]
    exact pullbackMetricCoefficients_fderiv_retraction_of_contMDiffOn g
      hΦ hU hr (hΦV.trans hVU) hleft (hVU hy) v w
  have houtside : ∀ᵐ x ∂volume.restrict Ω,
      x ∉ tsupport φ → T (f x + t • φ x) = f x := by
    filter_upwards [hfK] with x hx
    intro hxφ
    rw [DeGiorgi.affineVariation_eq_of_notMem_tsupport t hxφ, hTV (hΦV hx)]
    obtain ⟨p, hp⟩ := hx
    rw [← hp]
    exact congrArg Φ (hleft p)
  refine ⟨hw, hcolumn, ?_, houtside, ?_, ?_⟩
  · filter_upwards [htV] with x hx
    rw [hTV hx]
    exact mem_range_self (r (f x + t • φ x))
  · obtain ⟨b, hba, hφb⟩ := exists_lt_subset_ball (isClosed_tsupport φ) hφB
    refine ⟨b, hba, hφb, ?_⟩
    filter_upwards [houtside] with x hx
    intro hxb
    exact hx (fun hx' => hxb (hφb hx'))
  · filter_upwards [htV] with x hx
    intro j
    rw [hcolumn x j]
    exact hmetric hx _ _

end DifferentialGeometry.Geometry

end
