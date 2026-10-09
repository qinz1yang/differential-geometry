import DifferentialGeometry.Geometry.Boundary.ModelExtension
import DifferentialGeometry.Geometry.Boundary.ModelDefiningFunction
import DifferentialGeometry.Analysis.ODE.Flow.GlobalSliceSmoothness
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem exists_inward_localFlow_of_model
    {v : E → E} {U : Set E} {p : hI.boundaryE}
    (hU : IsOpen U) (hpU : modelBoundaryParam I p ∈ U)
    (hv : ContDiffOn ℝ ∞ v (U ∩ range I))
    (hinward : ∃ (w : hI.boundaryE) (c : ℝ), 0 < c ∧
      v (modelBoundaryParam I p) = fderiv ℝ (modelBoundaryParam I) p w + c • hI.inwardCoordE) :
    ∃ ε > 0, ∃ V : Set E, IsOpen V ∧ modelBoundaryParam I p ∈ V ∧ V ⊆ U ∧
      ∃ Φ : E × ℝ → E,
        (∀ z ∈ V, Φ (z, 0) = z) ∧ ContDiffOn ℝ ∞ Φ (V ×ˢ Ioo (-ε) ε) ∧
        (∀ z ∈ V ∩ range I, ∀ t ∈ Ico 0 ε,
          Φ (z, t) ∈ U ∩ range I ∧ HasDerivAt (fun s ↦ Φ (z, s)) (v (Φ (z, t))) t) ∧
        ∀ z ∈ V ∩ range I, ∀ t ∈ Ioo 0 ε, Φ (z, t) ∈ interior (range I) := by
  have hpB : modelBoundaryParam I p ∈ frontier (range I) :=
    range_modelBoundaryParam I ▸ mem_range_self p
  have hpR : modelBoundaryParam I p ∈ range I := I.isClosed_range.closure_subset hpB.1
  obtain ⟨W, hW, hpW, hWU, g, hg, hgeq⟩ :=
    exists_contDiffOn_extension_of_model I hU hpU hpB hv
  obtain ⟨A, hA, hpA, ρ, hρ, _, hρrange, hρinterior, _, hdρ⟩ :=
    exists_modelBoundary_definingFunction I p
  let D := A ∩ W
  have hD : IsOpen D := hA.inter hW
  have hder : ContinuousOn (fun z ↦ fderiv ℝ ρ z (g z)) D :=
    ((hρ.continuousOn_fderiv_of_isOpen hA (by simp)).mono inter_subset_left).clm_apply
      (hg.continuousOn.mono inter_subset_right)
  let Ω := D ∩ {z | 0 < fderiv ℝ ρ z (g z)}
  have hΩ : IsOpen Ω := hder.isOpen_inter_preimage hD isOpen_Ioi
  have hpΩ : modelBoundaryParam I p ∈ Ω := by
    refine ⟨⟨hpA, hpW⟩, ?_⟩
    obtain ⟨w, c, hc, hvc⟩ := hinward
    change 0 < fderiv ℝ ρ (modelBoundaryParam I p) (g (modelBoundaryParam I p))
    rw [hgeq ⟨hpW, hpR⟩, hvc, hdρ]
    exact hc
  obtain ⟨ε, hε, hflow⟩ := DifferentialGeometry.Analysis.ODE.Flow.exists_flow_on hΩ
    (hg.mono (fun z hz ↦ hz.1.2)) isCompact_singleton (singleton_subset_iff.mpr hpΩ)
  obtain ⟨V, hV, hpV, Φ, hzero, hΦ, hΦderiv, hΦΩ⟩ :=
    hflow (modelBoundaryParam I p) (mem_singleton _)
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hVΩ : V ⊆ Ω := by
    intro z hz
    have hzΩ : Φ (z, 0) ∈ Ω := hΦΩ ⟨hz, h0⟩
    simpa only [hzero z hz] using hzΩ
  have hheight : ∀ z ∈ V, ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun s ↦ ρ (Φ (z, s)))
        (fderiv ℝ ρ (Φ (z, t)) (g (Φ (z, t)))) t := by
    intro z hz t ht
    have hr : DifferentiableAt ℝ ρ (Φ (z, t)) :=
      (hρ.contDiffAt (hA.mem_nhds (hΦΩ ⟨hz, ht⟩).1.1)).differentiableAt (by simp)
    exact hr.hasFDerivAt.comp_hasDerivAt t (hΦderiv z hz t ht)
  have hmono : ∀ z ∈ V, StrictMonoOn (fun t ↦ ρ (Φ (z, t))) (Ioo (-ε) ε) := by
    intro z hz
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · intro t ht
      exact (hheight z hz t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      rw [(hheight z hz t ht).deriv]
      exact (hΦΩ ⟨hz, ht⟩).2
  have hnonneg : ∀ z ∈ V ∩ range I, ∀ t ∈ Ico 0 ε, 0 ≤ ρ (Φ (z, t)) := by
    intro z hz t ht
    have hstart := (hρrange z (hVΩ hz.1).1.1).1 hz.2
    have hle := (hmono z hz.1).monotoneOn h0
      (show t ∈ Ioo (-ε) ε from ⟨by linarith [ht.1], ht.2⟩) ht.1
    rw [hzero z hz.1] at hle
    exact hstart.trans hle
  refine ⟨ε, hε, V, hV, hpV, fun z hz ↦ hWU (hVΩ hz).1.2,
    Φ, hzero, hΦ, ?_, ?_⟩
  · intro z hz t ht
    have ht' : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], ht.2⟩
    have hWΦ : Φ (z, t) ∈ W := (hΦΩ ⟨hz.1, ht'⟩).1.2
    have hRΦ := (hρrange _ (hΦΩ ⟨hz.1, ht'⟩).1.1).2 (hnonneg z hz t ht)
    refine ⟨⟨hWU hWΦ, hRΦ⟩, ?_⟩
    rw [← hgeq ⟨hWΦ, hRΦ⟩]
    exact hΦderiv z hz.1 t ht'
  · intro z hz t ht
    have ht' : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], ht.2⟩
    apply (hρinterior _ (hΦΩ ⟨hz.1, ht'⟩).1.1).2
    have hlt := hmono z hz.1 h0 ht' ht.1
    dsimp only at hlt
    rw [hzero z hz.1] at hlt
    exact lt_of_le_of_lt ((hρrange z (hVΩ hz.1).1.1).1 hz.2) hlt

end DifferentialGeometry.Geometry.Boundary
