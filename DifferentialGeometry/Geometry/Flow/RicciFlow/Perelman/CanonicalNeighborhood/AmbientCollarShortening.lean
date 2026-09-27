import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderBallCapture

set_option autoImplicit false
noncomputable section
open Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem exists_fixed_ambient_collar_shortening_constants :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (C : CylinderReference) (h : ℝ → SmoothRiemannianMetric IC Cylinder)
      (g : ℝ → SmoothRiemannianMetric I3 M)
      (F : PartialDiffeomorph IC I3 Cylinder M ∞)
      (U : Set Cylinder) (times : Set ℝ) (order : ℕ) (eps : ℝ),
      MetricComparisonOn h g F U times order eps → h 0 = C.metric 0 →
      0 ≤ eps → eps ≤ 1 / 2 → 0 ∈ times → U ⊆ F.source →
      univ ×ˢ Icc (-H₀) H₀ ⊆ U → ∀ (p q : Sphere 2) (gamma : ℝ → M),
      ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (Icc (0 : ℝ) 1) →
      gamma 0 = F (p, 0) → gamma 1 = F (q, 0) →
      (∃ s ∈ Icc (0 : ℝ) 1, gamma s ∉ F '' (univ ×ˢ Icc (-H₀) H₀)) →
      ∃ shortcut : ℝ → M,
        shortcut 0 = gamma 0 ∧ shortcut 1 = gamma 1 ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I3 1 shortcut (Icc (0 : ℝ) 1) ∧
        (∀ s ∈ Icc (0 : ℝ) 1, shortcut s ∈ F '' (univ ×ˢ ({0} : Set ℝ))) ∧
        metricPathELength (g 0) shortcut 0 1 + ENNReal.ofReal (1 / 2 : ℝ) <
          metricPathELength (g 0) gamma 0 1 := by
  obtain ⟨D, hD, hshortcuts⟩ := exists_uniform_transverse_shortcuts (M := M)
  refine ⟨4 * (D + 1), by positivity, ?_⟩
  intro C h g F U times order eps cmp hmetric heps hepsHalf hzero hsource hslab
    p q gamma hgamma hstart hend hleave
  have hlevel : ∀ y : Sphere 2, (y, (0 : ℝ)) ∈ U := by
    intro y
    apply hslab
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  obtain ⟨shortcut, hx, hy, hC, hS, hlength⟩ :=
    hshortcuts C h g F U times order eps 0 cmp hmetric heps (by linarith)
      hzero hsource hlevel p q
  refine ⟨shortcut, hx.trans hstart.symm, hy.trans hend.symm, hC, hS, ?_⟩
  have hlower := collar_length_lower_of_leaves C g F cmp hmetric hepsHalf hzero
    (by positivity : 0 < 4 * (D + 1)) hsource hslab p hgamma hstart hleave
  calc
    _ ≤ ENNReal.ofReal D + ENNReal.ofReal (1 / 2 : ℝ) := add_le_add hlength le_rfl
    _ = ENNReal.ofReal (D + 1 / 2) := (ENNReal.ofReal_add hD.le (by norm_num)).symm
    _ < ENNReal.ofReal (4 * (D + 1) / 2) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
    _ ≤ _ := hlower

theorem exists_fixed_ambient_collar_trapping_constants :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (C : CylinderReference) (h : ℝ → SmoothRiemannianMetric IC Cylinder)
      (g : ℝ → SmoothRiemannianMetric I3 M)
      (F : PartialDiffeomorph IC I3 Cylinder M ∞)
      (U : Set Cylinder) (times : Set ℝ) (order : ℕ) (eps : ℝ),
      MetricComparisonOn h g F U times order eps → h 0 = C.metric 0 →
      0 ≤ eps → eps ≤ 1 / 2 → 0 ∈ times → U ⊆ F.source →
      univ ×ˢ Icc (-H₀) H₀ ⊆ U → ∀ (p q : Sphere 2) (gamma : ℝ → M),
      ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (Icc (0 : ℝ) 1) →
      gamma 0 = F (p, 0) → gamma 1 = F (q, 0) →
      metricPathELength (g 0) gamma 0 1 ≤
        riemannianEDistOf (g 0) (gamma 0) (gamma 1) + ENNReal.ofReal (1 / 2 : ℝ) →
      ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ F '' (univ ×ˢ Icc (-H₀) H₀) := by
  obtain ⟨H₀, hH₀, hshorten⟩ := exists_fixed_ambient_collar_shortening_constants (M := M)
  refine ⟨H₀, hH₀, ?_⟩
  intro C h g F U times order eps cmp hmetric heps hepsHalf hzero hsource hslab
    p q gamma hgamma hstart hend hnear s hs
  by_contra hnot
  obtain ⟨shortcut, hx, hy, hC, _hS, hsave⟩ :=
    hshorten C h g F U times order eps cmp hmetric heps hepsHalf hzero hsource hslab
      p q gamma hgamma hstart hend ⟨s, hs, hnot⟩
  have hdist := edistOf_le_metricPathELength (g 0) (by norm_num : (0 : ℝ) ≤ 1) hC
  rw [hx, hy] at hdist
  exact (not_lt_of_ge (hnear.trans (add_le_add hdist le_rfl))) hsave

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
