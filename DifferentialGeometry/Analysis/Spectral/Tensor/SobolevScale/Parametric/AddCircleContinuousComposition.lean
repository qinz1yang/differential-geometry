import Mathlib.Topology.UniformSpace.HeineCantor
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

theorem tendsto_scalarHs_composition
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (ι → ℝ) → ℝ) {U : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    {X : Type*} {l : Filter X}
    (u : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)))
    (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)))
    (v : X → TensorHs g 0 0 ((k : ℝ) + 1)) (v0 : TensorHs g 0 0 ((k : ℝ) + 1))
    (hu : Tendsto u l (𝓝 u0)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    range (scalarH1PiToContinuous g (P u0)) ⊆ U →
    (∀ᶠ z in l, ∀ x, scalarH1ToContinuous g (J (v z)) x =
      F (scalarH1PiToContinuous g (P (u z)) x)) →
    (∀ x, scalarH1ToContinuous g (J v0) x =
      F (scalarH1PiToContinuous g (P u0) x)) →
    Tendsto v l (𝓝 v0) := by
  classical
  intro J P hRange hEval hEval0
  obtain ⟨r, hr, C, N, hN, _, hNeval, _⟩ :=
    exists_scalarHs_composition_on_ball g k F hF hU u0 hRange
  let f : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)) →
      TensorHs g 0 0 ((k : ℝ) + 1) := fun w =>
    if hw : w ∈ Metric.ball u0 r then N ⟨w, hw⟩ else 0
  have hf : ContinuousOn f (Metric.ball u0 r) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (Metric.ball u0 r).domRestrict f = N := by
      funext w
      change (if hw : (w : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) ∈
        Metric.ball u0 r then N ⟨w, hw⟩ else 0) = N w
      rw [dif_pos w.property]
    rw [heq]
    exact hN.continuous
  have hfc : ContinuousAt f u0 :=
    (hf u0 (Metric.mem_ball_self hr)).continuousAt (Metric.ball_mem_nhds u0 hr)
  have hfu : Tendsto (fun z => f (u z)) l (𝓝 (f u0)) := hfc.tendsto.comp hu
  have heq0 : f u0 = v0 := by
    change (if hw : u0 ∈ Metric.ball u0 r then N ⟨u0, hw⟩ else 0) = v0
    rw [dif_pos (Metric.mem_ball_self hr)]
    apply tensorHsInclusion_injective (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)
    apply scalarH1ToContinuous_injective g
    exact ContinuousMap.ext (fun x =>
      (hNeval ⟨u0, Metric.mem_ball_self hr⟩ x).trans (hEval0 x).symm)
  rw [heq0] at hfu
  apply hfu.congr'
  filter_upwards [hu.eventually (Metric.ball_mem_nhds u0 hr), hEval] with z hz hez
  change u z ∈ Metric.ball u0 r at hz
  change (if hw : u z ∈ Metric.ball u0 r then N ⟨u z, hw⟩ else 0) = v z
  rw [dif_pos hz]
  apply tensorHsInclusion_injective (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)
  apply scalarH1ToContinuous_injective g
  exact ContinuousMap.ext (fun x => (hNeval ⟨u z, hz⟩ x).trans (hez x).symm)

end AddCircle

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem tendstoUniformlyOn_scalarHs_composition_of_isCompact_image
    {ι X A : Type*} [Fintype ι] {l : Filter X} {s : Set A}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (ι → ℝ) → ℝ) {U : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (u : X → A → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)))
    (u₀ : A → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)))
    (v : X → A → TensorHs g 0 0 ((k : ℝ) + 1))
    (v₀ : A → TensorHs g 0 0 ((k : ℝ) + 1))
    (hK : IsCompact (u₀ '' s))
    (hu : TendstoUniformlyOn u u₀ l s) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    (∀ t ∈ s, range (scalarH1PiToContinuous g (P (u₀ t))) ⊆ U) →
    (∀ᶠ x in l, ∀ t ∈ s, ∀ z, scalarH1ToContinuous g (J (v x t)) z =
      F (scalarH1PiToContinuous g (P (u x t)) z)) →
    (∀ t ∈ s, ∀ z, scalarH1ToContinuous g (J (v₀ t)) z =
      F (scalarH1PiToContinuous g (P (u₀ t)) z)) →
    TendstoUniformlyOn v v₀ l s := by
  classical
  intro J P hRange hEval hEval₀
  let E := PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))
  let H := TensorHs g 0 0 ((k : ℝ) + 1)
  let Rel : E → H → Prop := fun w y =>
    ∀ z, scalarH1ToContinuous g (J y) z = F (scalarH1PiToContinuous g (P w) z)
  let N : E → H := fun w => if hw : ∃ y, Rel w y then Classical.choose hw else 0
  have hN_eq (w : E) (y : H) (hy : Rel w y) : N w = y := by
    have hex : ∃ y, Rel w y := ⟨y, hy⟩
    change (if hw : ∃ y, Rel w y then Classical.choose hw else 0) = y
    rw [dif_pos hex]
    apply tensorHsInclusion_injective (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)
    apply scalarH1ToContinuous_injective g
    exact ContinuousMap.ext (fun z => (Classical.choose_spec hex z).trans (hy z).symm)
  have hN_eval (w : E) (hw : range (scalarH1PiToContinuous g (P w)) ⊆ U) :
      Rel w (N w) := by
    obtain ⟨r, hr, C, M, _, _, hM, _⟩ :=
      exists_scalarHs_composition_on_ball g k F hF hU w hw
    have hMw : Rel w (M ⟨w, Metric.mem_ball_self hr⟩) := hM _
    rw [hN_eq w _ hMw]
    exact hMw
  have hN_cont (w : E) (hw : range (scalarH1PiToContinuous g (P w)) ⊆ U) :
      ContinuousAt N w := by
    obtain ⟨r, hr, C, M, _, _, hM, _⟩ :=
      exists_scalarHs_composition_on_ball g k F hF hU w hw
    change Tendsto N (𝓝 w) (𝓝 (N w))
    apply tendsto_scalarHs_composition g k F hF hU id w N (N w) tendsto_id hw
      _ (hN_eval w hw)
    filter_upwards [Metric.ball_mem_nhds w hr] with w' hw'
    have hMw : Rel w' (M ⟨w', hw'⟩) := hM _
    rw [hN_eq w' _ hMw]
    exact hMw
  intro V hV
  have hUV := hK.uniformContinuousAt_of_continuousAt N
    (by
      rintro w ⟨t, ht, rfl⟩
      exact hN_cont (u₀ t) (hRange t ht)) hV
  filter_upwards [hu _ hUV, hEval] with x hx hEx t ht
  have hpair := hx t ht (mem_image_of_mem u₀ ht)
  rw [hN_eq (u₀ t) (v₀ t) (hEval₀ t ht), hN_eq (u x t) (v x t) (hEx t ht)] at hpair
  exact hpair

end AddCircle
