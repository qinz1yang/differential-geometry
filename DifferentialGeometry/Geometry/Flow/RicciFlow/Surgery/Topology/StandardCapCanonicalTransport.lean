import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolutionRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D} {eps C1 C2 : ℝ} {x : M} {t : ℝ}

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.sub_inv_scalar_mem_carrier (nk : StrongNeck S eps x t) :
    t - (S.scalar t x)⁻¹ ∈ D.carrier :=
  nk.time_domain ⟨le_rfl, sub_le_self _ (inv_nonneg.mpr nk.Q_pos.le)⟩

theorem CanonicalWitness.exists_backward_window_or_isCompact_connectedComponent
    (K : CanonicalWitness S eps C1 C2 x t) :
    (∃ y, 0 < S.scalar t y ∧ t - (S.scalar t y)⁻¹ ∈ D.carrier) ∨
      IsCompact (connectedComponent x) := by
  cases K.alternative with
  | neck data =>
    exact Or.inl ⟨x, data.strong.Q_pos, data.strong.sub_inv_scalar_mem_carrier⟩
  | cap data _ =>
    let nk := data.chain.necks ⟨0, data.chain.count_pos⟩
    exact Or.inl ⟨_, nk.Q_pos, nk.sub_inv_scalar_mem_carrier⟩
  | positive whole data _ =>
    right
    rw [← whole]
    cases data with
    | sphere F hs ht =>
      have hc : IsCompact (F.toPartialEquiv '' F.source) := by
        rw [hs]
        exact isCompact_univ.image_of_continuousOn (hs ▸ F.contMDiffOn_toFun.continuousOn)
      rwa [F.toPartialEquiv.image_source_eq_target, ht] at hc
    | projective Z _ F hs ht =>
      have hc : IsCompact (F.toPartialEquiv '' F.source) := by
        rw [hs]
        exact isCompact_univ.image_of_continuousOn (hs ▸ F.contMDiffOn_toFun.continuousOn)
      rwa [F.toPartialEquiv.image_source_eq_target, ht] at hc
  | round whole data =>
    right
    rw [← whole]
    let _ := data.topology
    let _ := data.charted
    let _ := data.compact
    have hc : IsCompact (data.map.toPartialEquiv '' data.map.source) := by
      rw [data.source_eq]
      exact isCompact_univ.image_of_continuousOn
        (data.source_eq ▸ data.map.contMDiffOn_toFun.continuousOn)
    rwa [data.map.toPartialEquiv.image_source_eq_target, data.target_eq] at hc

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

theorem PartialStandardSolution.isEmpty_canonicalWitness_of_time_mul_scalar_lt
    (S : PartialStandardSolution) {eps C1 C2 t : ℝ} (x : EuclideanSpace ℝ (Fin 3))
    (h : ∀ y, t * S.toSolutionOn.scalar t y < 1) :
    IsEmpty (CanonicalWitness S.toSolutionOn eps C1 C2 x t) := by
  refine ⟨fun K => ?_⟩
  rcases K.exists_backward_window_or_isCompact_connectedComponent with ⟨y, hy, hmem⟩ | hc
  · have h0 := ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos _).mp hmem).1
    have hinv : (S.toSolutionOn.scalar t y)⁻¹ ≤ t := by linarith
    have hmul := mul_le_mul_of_nonneg_right hinv hy.le
    rw [inv_mul_cancel₀ hy.ne'] at hmul
    linarith [h y]
  · have hsub : (univ : Set (EuclideanSpace ℝ (Fin 3))) ⊆ connectedComponent x :=
      isPreconnected_univ.subset_connectedComponent (mem_univ x)
    exact noncompact_univ (EuclideanSpace ℝ (Fin 3))
      (hc.of_isClosed_subset isClosed_univ hsub)

theorem PartialStandardSolution.isEmpty_canonicalWitness_at_zero
    (S : PartialStandardSolution) {eps C1 C2 : ℝ} (x : EuclideanSpace ℝ (Fin 3)) :
    IsEmpty (CanonicalWitness S.toSolutionOn eps C1 C2 x 0) :=
  S.isEmpty_canonicalWitness_of_time_mul_scalar_lt x (fun y => by simp)

theorem PartialStandardSolution.exists_pos_time_isEmpty_canonicalWitness
    (S : PartialStandardSolution) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ t ∈ Icc 0 θ, ∀ (x : EuclideanSpace ℝ (Fin 3)) (eps C1 C2 : ℝ),
      IsEmpty (CanonicalWitness S.toSolutionOn eps C1 C2 x t) := by
  obtain ⟨b, hb, hbT⟩ := exists_finite_lifetime_window S.lifetime S.lifetime_pos
  obtain ⟨K, hK, hcurv⟩ := S.curvature_bound b hb.le hbT
  refine ⟨min b (1 / (9 * K + 1)), lt_min hb (by positivity), ?_⟩
  intro t ht x eps C1 C2
  apply S.isEmpty_canonicalWitness_of_time_mul_scalar_lt x
  intro y
  rcases ht.1.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    exact one_pos
  have hR : S.toSolutionOn.scalar t y ≤ 9 * K := by
    have hrm := hcurv t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩ y
    rw [metricRm04_apply] at hrm
    have habs := scalar_abs_le_rm (S.metric t) y
    have hdim : (Module.finrank ℝ (TangentSpace (𝓡 3) y) : ℝ) = 3 := by
      rw [show Module.finrank ℝ (TangentSpace (𝓡 3) y) = 3 from finrank_euclideanSpace_fin]
      norm_num
    rw [hdim] at habs
    change metricScalarAt (S.metric t) y ≤ 9 * K
    have hle : (3 : ℝ) ^ 2 *
        Real.sqrt (normSq0S (S.metric t) y 4 (metricRm04At (S.metric t) y)) ≤ 9 * K := by
      nlinarith
    exact (le_abs_self _).trans (habs.trans hle)
  have htθ : t * (9 * K + 1) ≤ 1 := by
    have h1 := ht.2.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at h1
  have htR := mul_le_mul_of_nonneg_left hR hpos.le
  nlinarith

end DifferentialGeometry.PDE.RicciFlow
