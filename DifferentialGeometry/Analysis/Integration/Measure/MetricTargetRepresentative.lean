import DifferentialGeometry.Topology.MetricSpace.DistanceContinuity

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace DifferentialGeometry.Topology

variable {A X ι : Type*} [PseudoMetricSpace A] [MeasurableSpace A]
  {μ : Measure A} [Measure.IsOpenPosMeasure μ]
  [MetricSpace X] [CompleteSpace X] [Countable ι]

theorem exists_uniformContinuous_ae_eq_of_truncated_distance_modulus
    {a : ι → X} (ha : DenseRange a) (f : A → X) (w : ι → A → ℝ)
    (hw : ∀ i, w i =ᵐ[μ] (fun x => min (dist (f x) (a i)) 1))
    {ω : ℝ → ℝ} (hω : Tendsto ω (𝓝 (0 : ℝ)) (𝓝 0))
    (hmod : ∀ i x y, |w i x - w i y| ≤ ω (dist x y)) :
    ∃ F : A → X, UniformContinuous F ∧ F =ᵐ[μ] f := by
  let S : Set A := {x | ∀ i, w i x = min (dist (f x) (a i)) 1}
  have hSae : ∀ᵐ x ∂μ, x ∈ S := ae_all_iff.mpr hw
  have hSdense : Dense S := Measure.dense_of_ae hSae
  let fS : S → X := fun x => f x
  have hfS : UniformContinuous fS :=
    uniformContinuous_of_dense_truncated_distance_modulus ha hω (fun i x y => by
      change |min (dist (f x) (a i)) 1 - min (dist (f y) (a i)) 1| ≤ ω (dist x y)
      rw [← x.property i, ← y.property i]
      exact hmod i x y)
  refine ⟨hSdense.extend fS, hSdense.uniformContinuous_extend hfS, ?_⟩
  filter_upwards [hSae] with x hx
  exact hSdense.extend_of_ind hfS ⟨x, hx⟩

end DifferentialGeometry.Topology

end

end

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace DifferentialGeometry.Topology

variable {A X ι : Type*} [PseudoMetricSpace A] [MeasurableSpace A] [BorelSpace A]
  {μ : Measure A} [Measure.IsOpenPosMeasure μ]
  [MetricSpace X] [CompleteSpace X] [Countable ι]

theorem exists_continuousOn_ae_eq_of_truncated_distance_modulus_on_open
    {Ω : Set A} (hΩ : IsOpen Ω) {a : ι → X} (ha : DenseRange a)
    (f : A → X) (w : ι → A → ℝ)
    (hw : ∀ i, w i =ᵐ[μ.restrict Ω] (fun x => min (dist (f x) (a i)) 1))
    {ω : ℝ → ℝ} (hω : Tendsto ω (𝓝 (0 : ℝ)) (𝓝 0))
    (hmod : ∀ i, ∀ x ∈ Ω, ∀ y ∈ Ω, |w i x - w i y| ≤ ω (dist x y)) :
    ∃ F : A → X, ContinuousOn F Ω ∧ F =ᵐ[μ.restrict Ω] f := by
  classical
  let ν : Measure Ω := μ.comap Subtype.val
  let : Measure.IsOpenPosMeasure ν := Measure.IsOpenPosMeasure.comap μ hΩ.isOpenEmbedding_subtypeVal
  have hwae (i : ι) : (fun x : Ω => w i x) =ᵐ[ν]
      (fun x : Ω => min (dist (f x) (a i)) 1) :=
    (ae_restrict_iff_subtype hΩ.measurableSet).mp (hw i)
  obtain ⟨F, hF, hFeq⟩ := exists_uniformContinuous_ae_eq_of_truncated_distance_modulus
    (μ := ν) ha (fun x : Ω => f x) (fun i x => w i x) hwae hω
    (fun i x y => hmod i x x.property y y.property)
  let G : A → X := fun x => if h : x ∈ Ω then F ⟨x, h⟩ else f x
  have hG : ContinuousOn G Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (fun x : Ω => G x) = F := by
      funext x
      simp only [G, dif_pos x.property]
    exact hF.continuous.congr (fun x => (congrFun heq x).symm)
  refine ⟨G, hG, ?_⟩
  apply (ae_restrict_iff_subtype hΩ.measurableSet).mpr
  filter_upwards [hFeq] with x hx
  simpa only [G, dif_pos x.property] using hx

end DifferentialGeometry.Topology

end

end
