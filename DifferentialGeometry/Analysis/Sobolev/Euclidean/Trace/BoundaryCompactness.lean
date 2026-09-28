import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone.Oscillation
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Trace.Crosscut
import DifferentialGeometry.Analysis.Complex.CircleArc
import DifferentialGeometry.Analysis.Integration.Integral.IsometricDerivative
import DifferentialGeometry.Analysis.Complex.CircleRotation
import Mathlib.Topology.MetricSpace.Equicontinuity
import DifferentialGeometry.Topology.LoopSpace.CircleMetric
import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone.Closure
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences

noncomputable section

open Set MeasureTheory
open scoped NNReal
open DifferentialGeometry.Topology DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry

private theorem exists_pos_boundary_oscillation_lt_of_energy_bound_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (γ : C(loopCircle, E)) (hγ : _root_.Topology.IsEmbedding γ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (f : ℂ → E) (K : ℝ≥0), LipschitzWith K f →
      (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ f z‖ ^ 2) ≤ B →
      ∀ σ : C(loopCircle, loopCircle), IsWeaklyMonotoneOnce σ →
      σ 0 = 0 → σ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle) →
      σ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle) →
      (∀ t : ℝ, f (circleMap 0 1 (2 * Real.pi * t)) = γ (σ (t : loopCircle))) →
      ∀ (t₀ s : ℝ), s ∈ Icc (t₀ - δ) (t₀ + δ) →
      ∀ (t : ℝ), t ∈ Icc (t₀ - δ) (t₀ + δ) →
        dist (γ (σ (s : loopCircle))) (γ (σ (t : loopCircle))) < ε := by
  obtain ⟨η, hη, hηbound⟩ := exists_pos_dist_comp_lt_of_three_fixed_points γ hγ hε
  obtain ⟨r, hr, hrbound⟩ := exists_radius_circle_arc_oscillation_lt_of_energy_bound
    (E := E) (R := 1 / 2) (by norm_num) hB hη
  refine ⟨r / (2 * Real.pi), div_pos hr.1 (by positivity), ?_⟩
  intro f K hf henergy σ hσ h0 h1 h2 htrace t₀ s hs t ht
  let d : ℝ := t₀ - 1 / 2
  let e : ℂ ≃ₗᵢ[ℝ] ℂ := rotation (Circle.exp (2 * Real.pi * d))
  let F : ℂ → E := f ∘ e
  have hF : LipschitzWith K F := by
    simpa only [mul_one] using hf.comp e.isometry.lipschitzWith
  have hFenergy : (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ F z‖ ^ 2) ≤ B := by
    rw [e.integral_norm_fderiv_sq_comp_closedBall f 1]
    exact henergy
  have hFtrace (v : ℝ) : F (circleMap 0 1 (2 * Real.pi * v)) =
      γ (σ ((d + v : ℝ) : loopCircle)) := by
    dsimp only [F, Function.comp_apply, e]
    rw [rotation_exp_circleMap]
    convert htrace (d + v) using 1
    congr 2
    ring
  have hfi : IntegrableOn (fun z : ℂ => ‖fderiv ℝ F z‖ ^ 2)
      (Metric.closedBall (0 : ℂ) 1) := by
    apply (integrableOn_const (C := (K : ℝ) ^ 2)
      (isCompact_closedBall (0 : ℂ) 1).measure_ne_top).mono'
      ((measurable_fderiv ℝ F).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) K.coe_nonneg).2 (norm_fderiv_le_of_lipschitz ℝ hF)
  have henergy' : (∫ z in Metric.closedBall (-1 : ℂ) (1 / 2) ∩
      Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ F z‖ ^ 2) ≤ B := by
    apply le_trans _ hFenergy
    exact setIntegral_mono_set hfi (Filter.Eventually.of_forall fun z => sq_nonneg _)
      (Filter.Eventually.of_forall fun z hz => hz.2)
  obtain ⟨ρ, hρ, hosc⟩ := hrbound (Metric.closedBall (0 : ℂ) 1)
    measurableSet_closedBall (-1) F K hF henergy'
  have hρ0 : 0 < ρ := hr.1.trans hρ.1
  have hρ1 : ρ < 1 := hρ.2.trans (by norm_num)
  let a := Real.arccos (ρ / 2)
  have ha0 : 0 ≤ a := Real.arccos_nonneg _
  have hapi : a ≤ Real.pi := Real.arccos_le_pi _
  have hcl := hosc (-a) ⟨by linarith, by linarith [Real.pi_pos]⟩
    a ⟨by linarith [Real.pi_pos], hapi⟩ (by linarith)
    (fun θ hθ => Complex.circleMap_neg_one_mem_closedBall ρ hρ0.le (by linarith) hθ)
  have hab : (d + (1 - a / Real.pi)) - (d + a / Real.pi) ≤ 1 / 3 := by
    have h := Real.one_sub_two_mul_arccos_div_pi_lt_one_third hρ1
    calc
      (d + (1 - a / Real.pi)) - (d + a / Real.pi) = 1 - 2 * Real.arccos (ρ / 2) / Real.pi := by
        dsimp only [a]
        ring
      _ ≤ 1 / 3 := h.le
  have hend : dist (γ (σ (((d + (1 - a / Real.pi) : ℝ)) : loopCircle)))
      (γ (σ ((d + a / Real.pi : ℝ) : loopCircle))) < η := by
    rw [← hFtrace, ← hFtrace, dist_eq_norm]
    have he1 := circleMap_neg_one_neg_arccos (by linarith : -2 ≤ ρ) (by linarith : ρ ≤ 2)
    have he2 := circleMap_neg_one_arccos (by linarith : -2 ≤ ρ) (by linarith : ρ ≤ 2)
    change ‖F (circleMap (-1) ρ (-Real.arccos (ρ / 2))) -
      F (circleMap (-1) ρ (Real.arccos (ρ / 2)))‖ < η at hcl
    rw [he1, he2] at hcl
    convert hcl using 2
    congr 1 <;> dsimp only [a] <;> field_simp
  have hsin : s ∈ Icc (d + a / Real.pi) (d + (1 - a / Real.pi)) := by
    have hs' : s - d ∈ Icc (1 / 2 - r / (2 * Real.pi)) (1 / 2 + r / (2 * Real.pi)) := by
      constructor <;> dsimp only [d] <;> linarith [hs.1, hs.2]
    have h := Real.Icc_subset_arccos_div_pi hρ.1.le hρ0.le (by linarith) hs'
    constructor <;> dsimp only [a] <;> linarith [h.1, h.2]
  have htin : t ∈ Icc (d + a / Real.pi) (d + (1 - a / Real.pi)) := by
    have ht' : t - d ∈ Icc (1 / 2 - r / (2 * Real.pi)) (1 / 2 + r / (2 * Real.pi)) := by
      constructor <;> dsimp only [d] <;> linarith [ht.1, ht.2]
    have h := Real.Icc_subset_arccos_div_pi hρ.1.le hρ0.le (by linarith) ht'
    constructor <;> dsimp only [a] <;> linarith [h.1, h.2]
  exact hηbound σ hσ h0 h1 h2 (d + a / Real.pi) (d + (1 - a / Real.pi)) hab hend s
    hsin t htin


theorem exists_pos_boundary_oscillation_lt_of_energy_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (γ : C(loopCircle, E)) (hγ : _root_.Topology.IsEmbedding γ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (f : ℂ → E) (K : ℝ≥0), LipschitzWith K f →
      (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ f z‖ ^ 2) ≤ B →
      ∀ σ : C(loopCircle, loopCircle), IsWeaklyMonotoneOnce σ →
      σ 0 = 0 → σ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle) →
      σ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle) →
      (∀ t : ℝ, f (circleMap 0 1 (2 * Real.pi * t)) = γ (σ (t : loopCircle))) →
      ∀ x y : loopCircle, dist x y < δ → dist (γ (σ x)) (γ (σ y)) < ε := by
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_boundary_oscillation_lt_of_energy_bound_at γ hγ hB hε
  refine ⟨δ, hδ, ?_⟩
  intro f K hf henergy σ hσ h0 h1 h2 htrace x y hxy
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk_surjective y
  have hnorm : ‖x - y‖ < δ := by simpa only [dist_eq_norm] using hxy
  obtain ⟨z, hz, hznorm⟩ := QuotientAddGroup.norm_lt_iff.mp hnorm
  have hzabs : |z| < δ := by simpa only [Real.norm_eq_abs] using hznorm
  have hzv : ((v + z : ℝ) : loopCircle) = x := by
    rw [AddCircle.coe_add, hv, hz]
    abel
  have h := hbound f K hf henergy σ hσ h0 h1 h2 htrace v (v + z)
    (by constructor <;> linarith [(abs_lt.mp hzabs).1, (abs_lt.mp hzabs).2]) v
    (by constructor <;> linarith)
  simpa only [hzv, hv] using h

theorem uniform_equicontinuous_boundary_trace_of_energy_bound
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (γ : C(loopCircle, E)) (hγ : _root_.Topology.IsEmbedding γ)
    {B : ℝ} (hB : 0 ≤ B) (f : ι → ℂ → E) (K : ι → ℝ≥0)
    (hf : ∀ i, LipschitzWith (K i) (f i))
    (henergy : ∀ i, (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (f i) z‖ ^ 2) ≤ B)
    (σ : ι → C(loopCircle, loopCircle)) (hσ : ∀ i, IsWeaklyMonotoneOnce (σ i))
    (h0 : ∀ i, σ i 0 = 0)
    (h1 : ∀ i, σ i ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle))
    (h2 : ∀ i, σ i ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle))
    (htrace : ∀ i (t : ℝ), f i (circleMap 0 1 (2 * Real.pi * t)) = γ (σ i (t : loopCircle))) :
    UniformEquicontinuous (fun i x => γ (σ i x)) := by
  apply Metric.uniformEquicontinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_boundary_oscillation_lt_of_energy_bound γ hγ hB hε
  exact ⟨δ, hδ, fun x y hxy i =>
    hbound (f i) (K i) (hf i) (henergy i) (σ i) (hσ i) (h0 i) (h1 i) (h2 i) (htrace i) x y hxy⟩


theorem uniform_equicontinuous_circle_restriction_of_normalized_trace_energy_bound
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (γ : C(loopCircle, E)) (hγ : _root_.Topology.IsEmbedding γ)
    {B : ℝ} (hB : 0 ≤ B) (f : ι → ℂ → E) (K : ι → ℝ≥0)
    (hf : ∀ i, LipschitzWith (K i) (f i))
    (henergy : ∀ i, (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (f i) z‖ ^ 2) ≤ B)
    (σ : ι → C(loopCircle, loopCircle)) (hσ : ∀ i, IsWeaklyMonotoneOnce (σ i))
    (h0 : ∀ i, σ i 0 = 0)
    (h1 : ∀ i, σ i ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle))
    (h2 : ∀ i, σ i ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle))
    (htrace : ∀ i (t : ℝ), f i (circleMap 0 1 (2 * Real.pi * t)) = γ (σ i (t : loopCircle))) :
    UniformEquicontinuous (fun i (z : Circle) => f i z) := by
  have hbdry := uniform_equicontinuous_boundary_trace_of_energy_bound γ hγ hB f K hf henergy
    σ hσ h0 h1 h2 htrace
  have hident (i : ι) (x : loopCircle) : f i (AddCircle.toCircle x : ℂ) = γ (σ i x) := by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
    simpa only [AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one, circleMap_zero,
      Complex.ofReal_one, one_mul] using htrace i v
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hinv (z : Circle) : AddCircle.toCircle (e.symm z) = z := by
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact e.apply_symm_apply z
  apply Metric.uniformEquicontinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Metric.uniformEquicontinuous_iff.mp hbdry ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy i
  have hdist : dist (e.symm x) (e.symm y) < δ :=
    (show dist (e.symm x) (e.symm y) ≤ dist x y by
      simpa only [NNReal.coe_one, one_mul] using circle_parameter_lipschitz.dist_le_mul x y).trans_lt hxy
  have h := hbound (e.symm x) (e.symm y) hdist i
  rw [← hident, ← hident, hinv, hinv] at h
  exact h

end DifferentialGeometry.Geometry

end

noncomputable section

open Set Filter MeasureTheory ContinuousMap
open scoped Topology NNReal BoundedContinuousFunction
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

private theorem uniform_equicontinuous_of_comp_embedding
    {ι M : Type*} [PseudoMetricSpace M] (γ : C(loopCircle, M))
    (hγ : _root_.Topology.IsEmbedding γ) (σ : ι → C(loopCircle, loopCircle))
    (h : UniformEquicontinuous (fun i x => γ (σ i x))) :
    UniformEquicontinuous (fun i x => σ i x) := by
  let : CompactSpace (range γ) := isCompact_iff_compactSpace.mp (isCompact_range γ.continuous)
  have hinv := CompactSpace.uniformContinuous_of_continuous hγ.toHomeomorph.symm.continuous
  apply Metric.uniformEquicontinuous_iff.mpr
  intro ε hε
  obtain ⟨η, hη, hηbound⟩ := Metric.uniformContinuous_iff.mp hinv ε hε
  obtain ⟨δ, hδ, hδbound⟩ := Metric.uniformEquicontinuous_iff.mp h η hη
  refine ⟨δ, hδ, fun x y hxy i => ?_⟩
  have hdist : dist (hγ.toHomeomorph (σ i x)) (hγ.toHomeomorph (σ i y)) < η :=
    hδbound x y hxy i
  simpa only [Homeomorph.symm_apply_apply] using hηbound hdist

private theorem exists_subseq_tendsto_of_equicontinuous_circle
    (σ : ℕ → C(loopCircle, loopCircle))
    (hσ : Equicontinuous (fun n x => σ n x)) :
    ∃ (τ : C(loopCircle, loopCircle)) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (σ ∘ φ) atTop (𝓝 τ) := by
  classical
  let F : ℕ → loopCircle →ᵇ loopCircle := fun n => BoundedContinuousFunction.mkOfCompact (σ n)
  have hF : Equicontinuous ((↑) : range F → loopCircle → loopCircle) := by
    have heq : ((↑) : range F → loopCircle → loopCircle) =
        (fun n x => σ n x) ∘ (fun v : range F => Classical.choose v.property) := by
      funext v x
      exact congrArg (fun f : loopCircle →ᵇ loopCircle => f x)
        (Classical.choose_spec v.property).symm
    rw [heq]
    exact hσ.comp _
  have hc : IsCompact (closure (range F)) :=
    BoundedContinuousFunction.arzela_ascoli univ isCompact_univ (range F)
      (fun _ _ _ => mem_univ _) hF
  obtain ⟨τ, _, φ, hφ, hlim⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  refine ⟨τ.toContinuousMap, φ, hφ, ?_⟩
  exact ((isometryEquivBoundedOfCompact loopCircle loopCircle).symm.continuous.tendsto τ).comp hlim

theorem exists_subseq_tendsto_normalized_boundary_of_energy_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (γ : C(loopCircle, E)) (hγ : _root_.Topology.IsEmbedding γ)
    {B : ℝ} (f : ℕ → ℂ → E) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n))
    (henergy : ∀ n, (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (f n) z‖ ^ 2) ≤ B)
    (σ : ℕ → C(loopCircle, loopCircle)) (hσ : ∀ n, IsWeaklyMonotoneOnce (σ n))
    (h0 : ∀ n, σ n 0 = 0)
    (h1 : ∀ n, σ n ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle))
    (h2 : ∀ n, σ n ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle))
    (htrace : ∀ n (t : ℝ), f n (circleMap 0 1 (2 * Real.pi * t)) = γ (σ n (t : loopCircle))) :
    ∃ (τ : C(loopCircle, loopCircle)) (φ : ℕ → ℕ),
      StrictMono φ ∧ IsWeaklyMonotoneOnce τ ∧
      τ 0 = 0 ∧ τ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle) ∧
      τ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle) ∧
      Tendsto (σ ∘ φ) atTop (𝓝 τ) ∧
      TendstoUniformly (fun n (t : loopCircle) =>
        f (φ n) (AddCircle.toCircle t : ℂ)) (fun t => γ (τ t)) atTop := by
  have hB : 0 ≤ B := (integral_nonneg fun z => sq_nonneg ‖fderiv ℝ (f 0) z‖).trans (henergy 0)
  have he := uniform_equicontinuous_boundary_trace_of_energy_bound γ hγ hB f K hf henergy
    σ hσ h0 h1 h2 htrace
  obtain ⟨τ, φ, hφ, hlim⟩ := exists_subseq_tendsto_of_equicontinuous_circle σ
    (uniform_equicontinuous_of_comp_embedding γ hγ σ he).equicontinuous
  have hfixed (t : loopCircle) (ht : ∀ n, σ n t = t) : τ t = t := by
    have hl := ((continuous_eval_const t).tendsto τ).comp hlim
    have heq : (fun n => (σ ∘ φ) n t) = fun _ : ℕ => t := by
      funext n
      exact ht (φ n)
    change Tendsto (fun n => (σ ∘ φ) n t) atTop (𝓝 (τ t)) at hl
    rw [heq] at hl
    exact tendsto_nhds_unique hl tendsto_const_nhds
  refine ⟨τ, φ, hφ, IsWeaklyMonotoneOnce.of_tendsto
    (Eventually.of_forall fun n => hσ (φ n)) hlim,
    hfixed 0 h0, hfixed _ h1, hfixed _ h2, hlim, ?_⟩
  have htraceLim : Tendsto (fun n => γ.comp (σ (φ n))) atTop (𝓝 (γ.comp τ)) :=
    ((continuous_postcomp γ).tendsto τ).comp hlim
  have huniform := ContinuousMap.tendsto_iff_tendstoUniformly.mp htraceLim
  have heq : (fun n (t : loopCircle) => f (φ n) (AddCircle.toCircle t : ℂ)) =
      fun n t => γ (σ (φ n) t) := by
    funext n t
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
    simpa only [AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one, circleMap_zero,
      Complex.ofReal_one, one_mul] using htrace (φ n) v
  rw [heq]
  exact huniform

end DifferentialGeometry.Geometry

end
