import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} [IsManifold I n M]

theorem exists_contMDiff_curve_with_velocity (hn : 1 ≤ n)
    {x : M} (hx : I.IsInteriorPoint x) (v : TangentSpace I x)
    {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc (-ε) ε) ∧
      MapsTo γ (Icc (-ε) ε) U ∧
      (⟨γ 0, mfderiv 𝓘(ℝ, ℝ) I γ 0
        ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)⟩ : TangentBundle I M) = ⟨x, v⟩ := by
  have : IsManifold I 1 M := IsManifold.of_le hn
  let e := extChartAt I x
  let a : E := v
  let c : ℝ → E := fun t => e x + t • a
  let γ : ℝ → M := fun t => e.symm (c t)
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) n c :=
    contMDiff_const.add (contMDiff_id.smul contMDiff_const)
  have hc0 : c 0 = e x := by simp [c]
  have htarget : e.target ∈ 𝓝 (e x) :=
    mem_of_superset (isOpen_interior.mem_nhds (I.isInteriorPoint_iff.mp hx)) interior_subset
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I n e.symm (e x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt htarget
  have hγ0 : γ 0 = x := by
    change e.symm (c 0) = x
    rw [hc0, e.left_inv (mem_extChartAt_source x)]
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ 0 :=
    hsymm.comp_of_eq hc.contMDiffAt hc0
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ e.target ∧ γ t ∈ U := by
    have ht : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ e.target :=
      hc.continuous.continuousAt (by simpa only [hc0] using htarget)
    have hu := hγ.continuousAt (by simpa only [hγ0] using hU)
    exact ht.and hu
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hsub : Icc (-(δ / 2)) (δ / 2) ⊆ Metric.ball (0 : ℝ) δ := by
    intro t ht
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨δ / 2, half_pos hδ, γ, ?_, ?_, ?_⟩
  · exact (contMDiffOn_extChartAt_symm x).comp hc.contMDiffOn
      (fun t ht => (hδsub (hsub ht)).1)
  · exact fun t ht => (hδsub (hsub ht)).2
  · have hrange : range I ∈ 𝓝 (e x) :=
      mem_of_superset htarget (extChartAt_target_subset_range x)
    have hDsymm : mfderiv 𝓘(ℝ, E) I e.symm (e x) = ContinuousLinearMap.id ℝ E := by
      rw [← mfderivWithin_of_mem_nhds hrange]
      exact mfderivWithin_range_extChartAt_symm
    have hDc : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0
        ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) = a := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ c 0 (1 : ℝ) = a
      have h := (hasFDerivAt_const (𝕜 := ℝ) (e x) (0 : ℝ)).add
        ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const a)
      change HasFDerivAt c _ 0 at h
      rw [h.fderiv]
      simp
    have hDγ : (mfderiv 𝓘(ℝ, ℝ) I γ 0 : ℝ →L[ℝ] E) (1 : ℝ) = a := by
      rw [show γ = e.symm ∘ c from rfl,
        mfderiv_comp 0 (by
          simpa only [hc0] using hsymm.mdifferentiableAt (zero_lt_one.trans_le hn).ne')
          (hc.mdifferentiable (zero_lt_one.trans_le hn).ne' 0), hc0, hDsymm]
      exact hDc
    exact TotalSpace.ext hγ0 (heq_of_eq hDγ)
