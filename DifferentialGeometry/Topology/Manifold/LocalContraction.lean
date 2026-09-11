import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

open Set Filter
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} [IsManifold I n M]

theorem exists_contMDiff_local_contraction_of_isInteriorPoint
    {x₀ : M} (hx : I.IsInteriorPoint x₀) :
    ∃ (U : TopologicalSpace.Opens M) (hx₀ : x₀ ∈ U) (Γ : ℝ → U → M),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I n
        (fun q : ℝ × U => Γ q.1 q.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
      (∀ x : U, Γ 0 x = x₀) ∧ (∀ x : U, Γ 1 x = x) ∧
      (∀ t : ℝ, Γ t ⟨x₀, hx₀⟩ = x₀) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : U, Γ t x ∈ U := by
  let e := extChartAt I x₀
  have htarget : e.target ∈ 𝓝 (e x₀) :=
    mem_of_superset (isOpen_interior.mem_nhds (I.isInteriorPoint_iff.mp hx)) interior_subset
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp htarget
  let U : TopologicalSpace.Opens M :=
    ⟨e.source ∩ e ⁻¹' Metric.ball (e x₀) r,
      isOpen_extChartAt_preimage' (I := I) x₀ Metric.isOpen_ball⟩
  have hx₀ : x₀ ∈ U := ⟨mem_extChartAt_source x₀, Metric.mem_ball_self hr⟩
  let c : ℝ → U → E := fun t x => (1 - t) • e x₀ + t • e x
  let Γ : ℝ → U → M := fun t x => e.symm (c t x)
  have hcball (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : U) :
      c t x ∈ Metric.ball (e x₀) r :=
    (convex_ball (e x₀) r) (Metric.mem_ball_self hr) x.property.2
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  have hecoord : ContMDiff I 𝓘(ℝ, E) n (fun x : U => e x) := by
    have h := (contMDiffOn_extChartAt (I := I) (x := x₀) (n := n)).comp
      ((contMDiff_subtype_val (U := U)).contMDiffOn (s := univ))
      (fun x _ => by
        change (x : M) ∈ (chartAt H x₀).source
        rw [← extChartAt_source I x₀]
        exact x.property.1)
    rwa [contMDiffOn_univ] at h
  have hc : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) n
      (fun q : ℝ × U => c q.1 q.2) :=
    ((contMDiff_const.sub contMDiff_fst).smul contMDiff_const).add
      (contMDiff_fst.smul (hecoord.comp contMDiff_snd))
  refine ⟨U, hx₀, Γ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (contMDiffOn_extChartAt_symm (I := I) (n := n) x₀).comp hc.contMDiffOn
      (fun q hq => hball (hcball q.1 hq.1 q.2))
  · intro x
    simpa only [Γ, c, sub_zero, one_smul, zero_smul, add_zero] using
      e.left_inv (mem_extChartAt_source x₀)
  · intro x
    simpa only [Γ, c, sub_self, zero_smul, one_smul, zero_add] using e.left_inv x.property.1
  · intro t
    have hc₀ : c t ⟨x₀, hx₀⟩ = e x₀ := by
      dsimp only [c]
      rw [← add_smul, sub_add_cancel, one_smul]
    exact (congrArg e.symm hc₀).trans (e.left_inv (mem_extChartAt_source x₀))
  · intro t ht x
    have hct := hball (hcball t ht x)
    refine ⟨e.map_target hct, ?_⟩
    change e (e.symm (c t x)) ∈ Metric.ball (e x₀) r
    rw [e.right_inv hct]
    exact hcball t ht x

theorem exists_contMDiff_local_contraction [BoundarylessManifold I M] (x₀ : M) :
    ∃ (U : TopologicalSpace.Opens M) (hx₀ : x₀ ∈ U) (Γ : ℝ → U → M),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I n
        (fun q : ℝ × U => Γ q.1 q.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
      (∀ x : U, Γ 0 x = x₀) ∧ (∀ x : U, Γ 1 x = x) ∧
      (∀ t : ℝ, Γ t ⟨x₀, hx₀⟩ = x₀) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : U, Γ t x ∈ U :=
  exists_contMDiff_local_contraction_of_isInteriorPoint BoundarylessManifold.isInteriorPoint
