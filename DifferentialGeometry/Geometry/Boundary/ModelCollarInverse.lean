import DifferentialGeometry.Analysis.Calculus.Inverse.OneSidedTransverseInverse
import DifferentialGeometry.Geometry.Boundary.ModelDefiningFunction
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem exists_modelBoundary_inverse_of_one_sided
    {f : hI.boundaryE × ℝ → E} {V : Set hI.boundaryE} {p : hI.boundaryE} {ρ : ℝ} {v : E}
    (hV : IsOpen V) (hp : p ∈ V) (hρ : 0 < ρ)
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ Icc 0 ρ))
    (hzero : ∀ x ∈ V, f (x, 0) = modelBoundaryParam I x)
    (hderiv : HasDerivWithinAt (fun t ↦ f (p, t)) v (Icc 0 ρ) 0)
    (hinward : ∃ (w : hI.boundaryE) (c : ℝ), 0 < c ∧
      v = fderiv ℝ (modelBoundaryParam I) p w + c • hI.inwardCoordE) :
    ∃ e : OpenPartialHomeomorph (hI.boundaryE × ℝ) E,
      (p, 0) ∈ e.source ∧ e.source ⊆ V ×ˢ Ioo (-ρ) ρ ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ z ∈ e.source, 0 ≤ z.2 → e z = f z) ∧
      (∀ z ∈ e.source, e z ∈ range I ↔ 0 ≤ z.2) ∧
      (∀ z ∈ e.source, e z ∈ interior (range I) ↔ 0 < z.2) ∧
      ∀ z ∈ e.source, e z ∈ frontier (range I) ↔ z.2 = 0 := by
  obtain ⟨A, hA, hpA, r, hr, _, hrange, hinterior, hfrontier, hdr⟩ :=
    exists_modelBoundary_definingFunction I p
  obtain ⟨w, c, hc, hvc⟩ := hinward
  have hvnormal : fderiv ℝ r (modelBoundaryParam I p) v = c := by rw [hvc, hdr]
  have htrans : v ∉ range (fderiv ℝ (modelBoundaryParam I) p) := by
    rintro ⟨w', hw'⟩
    have hh := hdr w' 0
    simp only [zero_smul, add_zero, hw', hvnormal] at hh
    exact hc.ne' hh
  obtain ⟨e, hpe, heV, he, hi, heq⟩ := DifferentialGeometry.Analysis.exists_localInverse_of_one_sided_transverse_family
    hV hp hρ hf hzero (injective_fderiv_modelBoundaryParam I p) hI.finrank_boundaryE_succ hderiv htrans
  have hezero : e (p, 0) = modelBoundaryParam I p := (heq _ hpe le_rfl).trans (hzero p hp)
  have hed : HasDerivWithinAt (fun t ↦ e (p, t)) v (Icc 0 ρ) 0 := by
    apply hderiv.congr_of_eventuallyEq
    · filter_upwards [(continuousAt_const.prodMk continuousAt_id).continuousWithinAt.preimage_mem_nhdsWithin
        (e.open_source.mem_nhds hpe), self_mem_nhdsWithin] with t ht htime
      exact heq (p, t) ht htime.1
    · exact heq _ hpe le_rfl
  have het : HasDerivAt (fun t ↦ e (p, t)) (fderiv ℝ e (p, 0) (0, 1)) 0 :=
    ((he.contDiffAt (e.open_source.mem_nhds hpe)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_const 0 p).prodMk (hasDerivAt_id 0))
  have htime : fderiv ℝ e (p, 0) (0, 1) = v :=
    (het.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hρ 0 ⟨le_rfl, hρ.le⟩)).symm.trans
      (hed.derivWithin (uniqueDiffOn_Icc hρ 0 ⟨le_rfl, hρ.le⟩))
  let D₀ := e.source ∩ e ⁻¹' A
  have hD₀ : IsOpen D₀ := e.isOpen_inter_preimage hA
  have hpD₀ : (p, (0 : ℝ)) ∈ D₀ := ⟨hpe, by change e (p, 0) ∈ A; rwa [hezero]⟩
  let q : hI.boundaryE × ℝ → ℝ := r ∘ e
  have hq : ContDiffOn ℝ ∞ q D₀ := hr.comp (he.mono inter_subset_left) (fun z hz ↦ hz.2)
  have hpos : 0 < fderiv ℝ q (p, 0) (0, 1) := by
    have hd₁ := (hr.contDiffAt (hA.mem_nhds (hezero ▸ hpA))).differentiableAt (by simp)
    have hd₂ := (he.contDiffAt (e.open_source.mem_nhds hpe)).differentiableAt (by simp)
    change 0 < fderiv ℝ (r ∘ e) (p, 0) (0, 1)
    rw [fderiv_comp (p, 0) hd₁ hd₂, ContinuousLinearMap.comp_apply, htime, hezero, hvnormal]
    exact hc
  let Ω := D₀ ∩ {z | 0 < fderiv ℝ q z (0, 1)}
  have hΩ : IsOpen Ω :=
    ((hq.continuousOn_fderiv_of_isOpen hD₀ (by simp)).clm_apply continuousOn_const).isOpen_inter_preimage
      hD₀ isOpen_Ioi
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds ⟨hpD₀, hpos⟩)
  let D := Metric.ball p δ ×ˢ Ioo (-δ) δ
  have hD : IsOpen D := Metric.isOpen_ball.prod isOpen_Ioo
  have hDΩ : D ⊆ Ω := by
    intro z hz
    apply hδΩ
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff, abs_lt]
    exact ⟨hz.1, hz.2⟩
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_neg_of_pos hδ, hδ⟩
  have hqzero : ∀ x ∈ Metric.ball p δ, q (x, 0) = 0 := by
    intro x hx
    have hxΩ := hDΩ (show (x, (0 : ℝ)) ∈ D from ⟨hx, h0⟩)
    have hxeq := (heq _ hxΩ.1.1 le_rfl).trans (hzero x (heV hxΩ.1.1).1)
    apply (hfrontier _ hxΩ.1.2).mp
    rw [hxeq]
    exact range_modelBoundaryParam I ▸ mem_range_self x
  have hmono : ∀ x ∈ Metric.ball p δ, StrictMonoOn (fun t ↦ q (x, t)) (Ioo (-δ) δ) := by
    intro x hx
    have hdt : ∀ t ∈ Ioo (-δ) δ,
        HasDerivAt (fun s ↦ q (x, s)) (fderiv ℝ q (x, t) (0, 1)) t := by
      intro t ht
      exact ((hq.contDiffAt (hD₀.mem_nhds (hDΩ (show (x, t) ∈ D from ⟨hx, ht⟩)).1)).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · exact fun t ht ↦ (hdt t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      rw [(hdt t ht).deriv]
      exact (hDΩ (show (x, t) ∈ D from ⟨hx, ht⟩)).2
  let e' := e.restrOpen D hD
  have hpD : (p, (0 : ℝ)) ∈ D := ⟨Metric.mem_ball_self hδ, h0⟩
  refine ⟨e', ⟨hpe, hpD⟩, (fun z hz ↦ heV hz.1), he.mono inter_subset_left,
    hi.mono inter_subset_left, (fun z hz ht ↦ heq z hz.1 ht), ?_, ?_, ?_⟩
  · intro z hz
    change e z ∈ range I ↔ _
    rw [hrange _ (hDΩ hz.2).1.2]
    change (0 ≤ q z) ↔ 0 ≤ z.2
    have hh := (hmono z.1 hz.2.1).le_iff_le h0 hz.2.2
    simpa only [hqzero z.1 hz.2.1] using hh
  · intro z hz
    change e z ∈ interior (range I) ↔ _
    rw [hinterior _ (hDΩ hz.2).1.2]
    change (0 < q z) ↔ 0 < z.2
    have hh := (hmono z.1 hz.2.1).lt_iff_lt h0 hz.2.2
    simpa only [hqzero z.1 hz.2.1] using hh
  · intro z hz
    change e z ∈ frontier (range I) ↔ _
    rw [hfrontier _ (hDΩ hz.2).1.2]
    change q z = 0 ↔ z.2 = 0
    have hh : q z = q (z.1, 0) ↔ z.2 = 0 := (hmono z.1 hz.2.1).injOn.eq_iff hz.2.2 h0
    simpa only [hqzero z.1 hz.2.1] using hh

end DifferentialGeometry.Geometry.Boundary
