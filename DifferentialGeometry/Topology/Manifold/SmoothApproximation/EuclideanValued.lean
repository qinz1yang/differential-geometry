import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteOrder
import DifferentialGeometry.Analysis.Calculus.SmoothApproximation.FiniteSupported
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction
import Mathlib.Geometry.Manifold.WhitneyEmbedding

/-!
# Smooth approximation of `C^k` maps from a compact manifold to a normed space (W1a)

`exists_smooth_seq_chart_tendsto_of_contMDiff_normedSpace`: on a compact Hausdorff manifold `A`
with a boundaryless model, every `C^k` map `f : A → F` into a finite-dimensional normed space is
the uniform limit of smooth maps `fs j`, and in every extended chart of `A` the coordinate
expressions converge in `C^k` (`MapCPConvergenceOn … k`) on every compact subset of the chart
target.

Route (no partition of unity): a Whitney embedding `e : A → ℝ^N` with a smooth retraction `r`
on an open neighbourhood `U` of `e(A)`; `f ∘ r` is `C^k` on `U`; a cutoff equal to `1` near
`e(A)` and one mollification on `ℝ^N` give smooth `g j → χ • (f ∘ r)` in `C^k` uniformly; then
`fs j = g j ∘ e`, and in a chart `f ∘ φ⁻¹ = (χ • (f ∘ r)) ∘ (e ∘ φ⁻¹)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ∞ A]
  [T2Space A] [CompactSpace A]

/-- **W1a.** A `C^k` map from a compact boundaryless manifold to a finite-dimensional normed
space is the uniform limit of smooth maps whose coordinate expressions in every extended chart
converge in `C^k` on every compact subset of the chart target. -/
theorem exists_smooth_seq_chart_tendsto_of_contMDiff_normedSpace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (k : ℕ) {f : A → F} (hf : ContMDiff I 𝓘(ℝ, F) k f) :
    ∃ fs : ℕ → A → F, (∀ j, ContMDiff I 𝓘(ℝ, F) ∞ (fs j)) ∧ TendstoUniformly fs f atTop ∧
      ∀ (p : A) (K : Set E), IsCompact K → K ⊆ (extChartAt I p).target →
        MapCPConvergenceOn K k (fun j y => fs j ((extChartAt I p).symm y))
          (fun y => f ((extChartAt I p).symm y)) := by
  rcases isEmpty_or_nonempty A with hA | hA
  · refine ⟨fun _ => f, fun _ x => isEmptyElim x, ?_, fun p => isEmptyElim p⟩
    rw [Metric.tendstoUniformly_iff]
    exact fun _ _ => Eventually.of_forall fun _ x => isEmptyElim x
  obtain ⟨N, e, he, hemb, hi⟩ := exists_embedding_euclidean_of_compact (I := I) (M := A)
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction he hemb.isEmbedding hi
  have hS : IsCompact (range e) := isCompact_range he.continuous
  obtain ⟨χ, hχ, hχc, hχone, hχU, -⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hS hU heU
  have hfr : ContDiffOn ℝ k (fun z => f (r z)) U :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (hr.of_le (by exact_mod_cast le_top)))
  set G : EuclideanSpace ℝ (Fin N) → F := fun z => χ z • f (r z) with hGdef
  have hG : ContDiff ℝ k G := by
    apply contDiffOn_univ.mp
    exact DifferentialGeometry.Analysis.contDiffOn_cutoff_smul hU
      (hχ.of_le (by exact_mod_cast le_top)) hχU (by simpa only [univ_inter] using hfr)
  have hGc : HasCompactSupport G := hχc.smul_right
  have hGe : ∀ x, G (e x) = f x := by
    intro x
    have h1 : χ (e x) = 1 :=
      (hχone.filter_mono (nhds_le_nhdsSet (mem_range_self x))).self_of_nhds
    simp only [hGdef, h1, one_smul, hleft x]
  obtain ⟨-, -, -, -, g, hg, -, hconv⟩ :=
    DifferentialGeometry.Analysis.exists_smooth_approx_supported_in_open_of_contDiff k hG hGc
      isOpen_univ (subset_univ _)
  have hgk : ∀ n, ContDiff ℝ ((k : ℕ∞) : WithTop ℕ∞) (g n) := fun n =>
    (hg n).of_le (by exact_mod_cast le_top)
  have hgG : MapCPConvergenceOn univ k g G :=
    mapCPConvergenceOn_of_tendstoUniformly hgk hG fun j hj => (hconv j hj).tendstoUniformlyOn
  have hunif : TendstoUniformly g G atTop :=
    tendstoUniformlyOn_univ.mp (tendstoUniformlyOn_of_cPConvergence (hgG.mono_order (Nat.zero_le k)))
  refine ⟨fun n x => g n (e x), fun n => (hg n).contMDiff.comp he, ?_, ?_⟩
  · have h := hunif.comp e
    have hfe : G ∘ e = f := funext hGe
    rw [hfe] at h
    exact h
  · intro p K hK hKt
    have hT : ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞) (fun y => e ((extChartAt I p).symm y))
        (extChartAt I p).target :=
      (contMDiffOn_iff_contDiffOn.mp (he.comp_contMDiffOn (contMDiffOn_extChartAt_symm p))).of_le
        (by exact_mod_cast le_top)
    have h := MapCPConvergenceOn.comp_contDiffOn_right (isOpen_extChartAt_target p) isOpen_univ
      hK hKt hT (mapsTo_univ _ _) (hgG.mono_set (subset_univ _))
      (fun n => (hgk n).contDiffOn) hG.contDiffOn
    simpa only [hGe] using h

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
