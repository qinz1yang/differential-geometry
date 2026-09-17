import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleLocalComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuousInjective

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem exists_continuousOn_scalar_composition_of_order
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    {σ : ℝ} (hσ : σ = (k : ℝ) + 1)
    (F : (ι → ℝ) → ℝ) {U : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    {X : Type*} [TopologicalSpace X] {s : Set X}
    (u : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 σ))
    (hu : ContinuousOn u s) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by rw [hσ]; norm_num : (1 : ℝ) ≤ σ)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    (∀ t ∈ s, range (scalarH1PiToContinuous g (P (u t))) ⊆ U) →
    ∃ v : X → TensorHs g 0 0 σ, ContinuousOn v s ∧
      ∀ t ∈ s, ∀ x, scalarH1ToContinuous g (J (v t)) x =
        F (scalarH1PiToContinuous g (P (u t)) x) := by
  classical
  subst σ
  intro J P hRange
  have hex (t : X) : ∃ v : TensorHs g 0 0 ((k : ℝ) + 1),
      t ∈ s → ∀ x, scalarH1ToContinuous g (J v) x =
        F (scalarH1PiToContinuous g (P (u t)) x) := by
    by_cases ht : t ∈ s
    · obtain ⟨r, hr, C, N, _, _, hEval, _⟩ :=
        exists_scalarHs_composition_on_ball g k F hF hU (u t) (hRange t ht)
      exact ⟨N ⟨u t, Metric.mem_ball_self hr⟩, fun _ => hEval _⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  choose v hv using hex
  refine ⟨v, ?_, hv⟩
  intro t ht
  obtain ⟨r, hr, C, N, hN, _, hEval, _⟩ :=
    exists_scalarHs_composition_on_ball g k F hF hU (u t) (hRange t ht)
  let f : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)) →
      TensorHs g 0 0 ((k : ℝ) + 1) := fun w =>
    if hw : w ∈ Metric.ball (u t) r then N ⟨w, hw⟩ else 0
  have hf : ContinuousOn f (Metric.ball (u t) r) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (Metric.ball (u t) r).domRestrict f = N := by
      funext w
      change (if hw : (w : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) ∈
        Metric.ball (u t) r then N ⟨w, hw⟩ else 0) = N w
      rw [dif_pos w.property]
    rw [heq]
    exact hN.continuous
  have hm : u ⁻¹' Metric.ball (u t) r ∈ 𝓝[s] t :=
    (hu t ht).preimage_mem_nhdsWithin (Metric.ball_mem_nhds _ hr)
  have hc := (hf (u t) (Metric.mem_ball_self hr)).comp_of_preimage_mem_nhdsWithin
    (hu t ht) hm
  apply hc.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [self_mem_nhdsWithin, hm] with z hz hball
  change u z ∈ Metric.ball (u t) r at hball
  change v z = f (u z)
  change v z = if hw : u z ∈ Metric.ball (u t) r then N ⟨u z, hw⟩ else 0
  rw [dif_pos hball]
  apply tensorHsInclusion_injective (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)
  apply scalarH1ToContinuous_injective g
  exact ContinuousMap.ext (fun x => (hv z hz x).trans (hEval ⟨u z, hball⟩ x).symm)


theorem exists_continuousOn_scalarHs_composition
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (ι → ℝ) → ℝ) {U : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    {X : Type*} [TopologicalSpace X] {s : Set X}
    (u : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)))
    (hu : ContinuousOn u s) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    (∀ t ∈ s, range (scalarH1PiToContinuous g (P (u t))) ⊆ U) →
    ∃ v : X → TensorHs g 0 0 ((k : ℝ) + 1), ContinuousOn v s ∧
      ∀ t ∈ s, ∀ x, scalarH1ToContinuous g (J (v t)) x =
        F (scalarH1PiToContinuous g (P (u t)) x) := by
  exact exists_continuousOn_scalar_composition_of_order g k rfl F hF hU u hu

theorem exists_continuousOn_scalarH2_composition
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (ι → ℝ) → ℝ) {U : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    {X : Type*} [TopologicalSpace X] {s : Set X}
    (u : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 2))
    (hu : ContinuousOn u s) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    (∀ t ∈ s, range (scalarH1PiToContinuous g (P (u t))) ⊆ U) →
    ∃ v : X → TensorHs g 0 0 2, ContinuousOn v s ∧
      ∀ t ∈ s, ∀ x, scalarH1ToContinuous g (J (v t)) x =
        F (scalarH1PiToContinuous g (P (u t)) x) := by
  exact exists_continuousOn_scalar_composition_of_order g 1 (by norm_num) F hF hU u hu

end AddCircle
