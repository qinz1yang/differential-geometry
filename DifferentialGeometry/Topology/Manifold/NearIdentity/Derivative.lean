import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff Topology

theorem injOn_of_dist_le {M : Type*} [MetricSpace M] {N : Type*} [PseudoMetricSpace N]
    {F : M → N} {s : Set M} {K : Real}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ K * dist (F x) (F y)) : Set.InjOn F s := by
  intro x hx y hy hFxy
  have hle : dist x y ≤ K * dist (F x) (F y) := h x hx y hy
  rw [hFxy, dist_self, mul_zero] at hle
  exact dist_le_zero.mp hle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [MetricSpace M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    [PseudoMetricSpace N]

omit [CompleteSpace E] [I.Boundaryless]
    [IsManifold I ∞ M] [IsManifold I ∞ N] in
theorem is_local_diffeomorph_on_and_inj_on_of_dist_le {F : M → N} {U : Set M} {K : Real}
    (hloc : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U)
    (hdisp : ∀ x ∈ U, ∀ y ∈ U, dist x y ≤ K * dist (F x) (F y)) :
    IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U ∧ Set.InjOn F U :=
  ⟨hloc, injOn_of_dist_le hdisp⟩

omit [MetricSpace M] [PseudoMetricSpace N] in
theorem hlocOn_of_chartNeumann {F : M → N} {U : Set M} (n : ℕ) (hn : 1 ≤ n) (hU : IsOpen U)
    (hf : ContMDiffOn I I (n : ℕ∞) F U)
    (hneu : ∀ y ∈ U, ‖ContinuousLinearMap.id ℝ E -
        fderiv ℝ (writtenInExtChartAt I I y F) (extChartAt I y y)‖ < 1) :
    IsLocalDiffeomorphOn I I (n : ℕ∞) F U := by
  have hle : ((n : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hne : ((n : ℕ∞) : WithTop ℕ∞) ≠ ∞ := by exact_mod_cast (ENat.natCast_ne_top n)
  have : IsManifold I ((n : ℕ∞) : WithTop ℕ∞) M := IsManifold.of_le hle
  have : IsManifold I ((n : ℕ∞) : WithTop ℕ∞) N := IsManifold.of_le hle
  exact Coordinates.contMDiffOn_isLocalDiffeomorphOn (by exact_mod_cast hn) hne hU hf
    (fun y hy => Coordinates.isInvertible_of_norm_id_sub_lt (hneu y hy))

omit [CompleteSpace E] [MetricSpace M]
    [PseudoMetricSpace N] in
theorem chartRep_differentiableAt {F : M → N} {U : Set M} (x₀ : M)
    (hU : IsOpen U) (hUsub : U ⊆ (extChartAt I x₀).source)
    (hf : ContMDiffOn I I (∞ : WithTop ℕ∞) F U)
    (hFsub : ∀ y ∈ U, F y ∈ (extChartAt I (F x₀)).source) :
    ∀ z ∈ (extChartAt I x₀) '' U,
      DifferentiableAt ℝ (writtenInExtChartAt I I x₀ F) z := by
  rintro z ⟨y, hy, rfl⟩
  have hyz : (extChartAt I x₀).symm (extChartAt I x₀ y) = y :=
    PartialEquiv.left_inv _ (hUsub hy)
  have h1 : ContMDiffAt 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) ((extChartAt I x₀).symm)
      (extChartAt I x₀ y) :=
    (contMDiffOn_extChartAt_symm x₀).contMDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds ((extChartAt I x₀).map_source (hUsub hy)))
  have h2 : ContMDiffAt I I (∞ : WithTop ℕ∞) F ((extChartAt I x₀).symm (extChartAt I x₀ y)) := by
    rw [hyz]; exact hf.contMDiffAt (hU.mem_nhds hy)
  have h3 : ContMDiffAt I 𝓘(ℝ, E) (∞ : WithTop ℕ∞) (extChartAt I (F x₀))
      (F ((extChartAt I x₀).symm (extChartAt I x₀ y))) := by
    rw [hyz]
    exact (contMDiffOn_extChartAt (I := I) (x := F x₀) (n := (∞ : WithTop ℕ∞))).contMDiffAt
      ((chartAt H (F x₀)).open_source.mem_nhds
        (extChartAt_source (I := I) (F x₀) ▸ hFsub y hy))
  have hcomp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) (∞ : WithTop ℕ∞)
      (writtenInExtChartAt I I x₀ F) (extChartAt I x₀ y) :=
    (h3.comp _ h2).comp _ h1
  have hcd : ContDiffAt ℝ (∞ : WithTop ℕ∞) (writtenInExtChartAt I I x₀ F)
      (extChartAt I x₀ y) := contMDiffAt_iff_contDiffAt.mp hcomp
  exact hcd.differentiableAt (by exact_mod_cast (by simp : (⊤ : ℕ∞) ≠ 0))

omit [MetricSpace M] [PseudoMetricSpace N] in
theorem hlocOn_of_chartNeumann_infty {F : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I I (∞ : WithTop ℕ∞) F U)
    (hneu : ∀ y ∈ U, ‖ContinuousLinearMap.id ℝ E -
        fderiv ℝ (writtenInExtChartAt I I y F) (extChartAt I y y)‖ < 1) :
    IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U :=
  Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty hU hf
    (fun y hy => Coordinates.isInvertible_of_norm_id_sub_lt (hneu y hy))

theorem hlocHinj_of_chartNeumann
    {E₀ : Type uE} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [CompleteSpace E₀]
    {H₀ : Type uH} [TopologicalSpace H₀]
    {I₀ : ModelWithCorners ℝ E₀ H₀} [I₀.Boundaryless]
    {M₀ : Type u} [TopologicalSpace M₀] [ChartedSpace H₀ M₀]
    [IsManifold I₀ ∞ M₀]
    {N₀ : Type u} [TopologicalSpace N₀] [ChartedSpace H₀ N₀]
    [IsManifold I₀ ∞ N₀]
    {F : M₀ → N₀} {U : Set M₀} (x₀ : M₀) {ε : ℝ} (hε : ε < 1)
    (hU : IsOpen U) (hUsub : U ⊆ (extChartAt I₀ x₀).source)
    (hconv : Convex ℝ ((extChartAt I₀ x₀) '' U))
    (hf : ContMDiffOn I₀ I₀ (∞ : WithTop ℕ∞) F U)
    (hFsub : ∀ y ∈ U, F y ∈ (extChartAt I₀ (F x₀)).source)
    (hneu : ∀ y ∈ U, ‖ContinuousLinearMap.id ℝ E₀ -
        fderiv ℝ (writtenInExtChartAt I₀ I₀ y F) (extChartAt I₀ y y)‖ < 1)
    (hneu₀ : ∀ z ∈ (extChartAt I₀ x₀) '' U, ‖ContinuousLinearMap.id ℝ E₀ -
        fderiv ℝ (writtenInExtChartAt I₀ I₀ x₀ F) z‖ ≤ ε) :
    IsLocalDiffeomorphOn I₀ I₀ (∞ : WithTop ℕ∞) F U ∧ Set.InjOn F U := by
  have hloc : IsLocalDiffeomorphOn I₀ I₀ (∞ : WithTop ℕ∞) F U :=
    Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty hU hf
      (fun y hy => Coordinates.isInvertible_of_norm_id_sub_lt (hneu y hy))
  have hdiff : ∀ z ∈ (extChartAt I₀ x₀) '' U,
      DifferentiableAt ℝ (writtenInExtChartAt I₀ I₀ x₀ F) z := by
    rintro z ⟨y, hy, rfl⟩
    have hyz : (extChartAt I₀ x₀).symm (extChartAt I₀ x₀ y) = y :=
      PartialEquiv.left_inv _ (hUsub hy)
    have h1 : ContMDiffAt 𝓘(ℝ, E₀) I₀ (∞ : WithTop ℕ∞) ((extChartAt I₀ x₀).symm)
        (extChartAt I₀ x₀ y) :=
      (contMDiffOn_extChartAt_symm x₀).contMDiffAt
        ((isOpen_extChartAt_target x₀).mem_nhds ((extChartAt I₀ x₀).map_source (hUsub hy)))
    have h2 : ContMDiffAt I₀ I₀ (∞ : WithTop ℕ∞) F
        ((extChartAt I₀ x₀).symm (extChartAt I₀ x₀ y)) := by
      rw [hyz]
      exact hf.contMDiffAt (hU.mem_nhds hy)
    have h3 : ContMDiffAt I₀ 𝓘(ℝ, E₀) (∞ : WithTop ℕ∞) (extChartAt I₀ (F x₀))
        (F ((extChartAt I₀ x₀).symm (extChartAt I₀ x₀ y))) := by
      rw [hyz]
      exact (contMDiffOn_extChartAt (I := I₀) (x := F x₀)
        (n := (∞ : WithTop ℕ∞))).contMDiffAt
        ((chartAt H₀ (F x₀)).open_source.mem_nhds
          (extChartAt_source (I := I₀) (F x₀) ▸ hFsub y hy))
    have hcomp : ContMDiffAt 𝓘(ℝ, E₀) 𝓘(ℝ, E₀) (∞ : WithTop ℕ∞)
        (writtenInExtChartAt I₀ I₀ x₀ F) (extChartAt I₀ x₀ y) :=
      (h3.comp _ h2).comp _ h1
    have hcd : ContDiffAt ℝ (∞ : WithTop ℕ∞) (writtenInExtChartAt I₀ I₀ x₀ F)
        (extChartAt I₀ x₀ y) := contMDiffAt_iff_contDiffAt.mp hcomp
    exact hcd.differentiableAt (by exact_mod_cast (by simp : (⊤ : ℕ∞) ≠ 0))
  have hinjChart : Set.InjOn (writtenInExtChartAt I₀ I₀ x₀ F)
      ((extChartAt I₀ x₀) '' U) :=
    Coordinates.injOn_of_fderiv_near_id hconv hε hdiff hneu₀
  exact ⟨hloc, Coordinates.injOn_of_writtenInExtChart (I := I₀) (J := I₀)
    x₀ hUsub hinjChart⟩


end CheegerGromovCompactness
end DifferentialGeometry
