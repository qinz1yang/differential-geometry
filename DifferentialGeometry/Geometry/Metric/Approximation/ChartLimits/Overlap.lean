import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Separation.Basic

set_option autoImplicit false
noncomputable section
open Set Filter Topology Manifold Metric
open scoped ContDiff NNReal
open DifferentialGeometry.CheegerGromovCompactness (MapCPConvergenceOn mapDerivNorm)
namespace GC.MetricGeometry

theorem exists_countable_open_cover_with_property
    {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    {O : Set E} (P : Set E → Prop)
    (hlocal : ∀ x ∈ O, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧ P U) :
    ∃ S : Set (Set E), S.Countable ∧
      (∀ U ∈ S, IsOpen U ∧ U ⊆ O ∧ P U) ∧ ⋃₀ S = O := by
  let A : Set (Set E) := {U | IsOpen U ∧ U ⊆ O ∧ P U}
  have hAO : ⋃₀ A = O := by
    apply subset_antisymm
    · rintro x ⟨U, hU, hx⟩
      exact hU.2.1 hx
    · intro x hx
      obtain ⟨U, hU, hxU, hUO, hP⟩ := hlocal x hx
      exact ⟨U, ⟨hU, hUO, hP⟩, hxU⟩
  obtain ⟨S, hS, hSA, hUnion⟩ := TopologicalSpace.isOpen_sUnion_countable A (fun U hU => hU.1)
  exact ⟨S, hS, fun U hU => hSA hU, hUnion.trans hAO⟩

private theorem mapCPConvergenceOn_biUnion_finset
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (t : Finset ι) {D : ι → Set E} {p : ℕ} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : ∀ k ∈ t, MapCPConvergenceOn (D k) p Φ Φinf) :
    MapCPConvergenceOn (⋃ k ∈ t, D k) p Φ Φinf := by
  intro ε hε
  have hev : ∀ k ∈ t, ∀ᶠ m in atTop, ∀ r : ℕ, r ≤ p → ∀ x ∈ D k,
      mapDerivNorm r (Φ m) Φinf x ≤ ε := by
    intro k hk
    obtain ⟨m0, hm0⟩ := h k hk ε hε
    exact eventually_atTop.mpr ⟨m0, hm0⟩
  obtain ⟨m0, hm0⟩ := eventually_atTop.mp ((eventually_all_finset t).mpr hev)
  refine ⟨m0, fun m hm r hr x hx => ?_⟩
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
  exact hm0 m hm k hk r hr x hxk

theorem mapCPConvergenceOn_of_isCompact_subset_sUnion
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set (Set E)} (hSo : ∀ U ∈ S, IsOpen U) {p : ℕ} {Φ : ℕ → E → F} {Φinf : E → F}
    (hloc : ∀ U ∈ S, ∀ D : Set E, IsCompact D → D ⊆ U → MapCPConvergenceOn D p Φ Φinf)
    {Q : Set E} (hQ : IsCompact Q) (hQS : Q ⊆ ⋃₀ S) :
    MapCPConvergenceOn Q p Φ Φinf := by
  have hcov : Q ⊆ ⋃ U : S, (U : Set E) := by
    intro x hx
    obtain ⟨U, hU, hxU⟩ := hQS hx
    exact mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover (fun U : S => (U : Set E))
    (fun U => hSo U U.property) hcov
  obtain ⟨D, hDc, hDU, hQD⟩ := hQ.finite_compact_cover t (fun U : S => (U : Set E))
    (fun U _ => hSo U U.property) ht
  rw [hQD]
  exact mapCPConvergenceOn_biUnion_finset t
    (fun U _ => hloc U U.property (D U) (hDc U) (hDU U))

theorem pullbackMetricCoefficients_eq_bilinearComp_transition
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : DifferentialGeometry.SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (a b : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞)
    {u : E} (hu : u ∈ (a.trans b.symm).source) :
    DifferentialGeometry.Geometry.pullbackMetricCoefficients g a u =
      (DifferentialGeometry.Geometry.pullbackMetricCoefficients g b (b.symm (a u))).bilinearComp
        (fderiv ℝ (fun v => b.symm (a v)) u) (fderiv ℝ (fun v => b.symm (a v)) u) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact (DifferentialGeometry.Geometry.pullbackMetricCoefficients_fderiv_symm g b
    (a.mdifferentiableAt (by simp) hu.1) hu.2 v w).symm

end GC.MetricGeometry
