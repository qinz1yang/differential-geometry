import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarMetricControl

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metricPathELength_add (g : SmoothRiemannianMetric I3 M)
    (gamma : ℝ → M) {a s b : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    metricPathELength g gamma a s + metricPathELength g gamma s b =
      metricPathELength g gamma a b := by
  let : RiemannianBundle (fun x : M => TangentSpace I3 x) := ⟨g.toRiemannianMetric⟩
  exact Manifold.pathELength_add has hsb


theorem collar_return_length_lower (C : CylinderReference)
    (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    {U : Set Cylinder} {times : Set ℝ} {order : ℕ} {eps : ℝ}
    {h : ℝ → SmoothRiemannianMetric IC Cylinder}
    (cmp : MetricComparisonOn h g F U times order eps) (hmetric : h 0 = C.metric 0)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hzero : 0 ∈ times)
    (hsource : U ⊆ F.source) {gamma : ℝ → Cylinder}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) IC 1 gamma (Icc (0 : ℝ) 1))
    (hU : ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ U)
    (hstart : (gamma 0).2 = 0) (hend : (gamma 1).2 = 0)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (2 * Real.sqrt (1 - eps) * |(gamma s).2|) ≤
      metricPathELength (g 0) ((F : Cylinder → M) ∘ gamma) 0 1 := by
  have hleft := collar_crossing_length_lower C g F cmp hmetric heps heps1 hzero hsource hs.1
    (hgamma.mono (Icc_subset_Icc le_rfl hs.2))
    (fun t ht => hU t ⟨ht.1, ht.2.trans hs.2⟩)
  have hright := collar_crossing_length_lower C g F cmp hmetric heps heps1 hzero hsource hs.2
    (hgamma.mono (Icc_subset_Icc hs.1 le_rfl))
    (fun t ht => hU t ⟨hs.1.trans ht.1, ht.2⟩)
  simp only [hstart, zero_sub, abs_neg] at hleft
  simp only [hend, sub_zero] at hright
  calc
    _ = ENNReal.ofReal (Real.sqrt (1 - eps) * |(gamma s).2|) +
        ENNReal.ofReal (Real.sqrt (1 - eps) * |(gamma s).2|) := by
      rw [← ENNReal.ofReal_add (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
        (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))]
      congr 1
      ring
    _ ≤ _ := add_le_add hleft hright
    _ = _ := metricPathELength_add (g 0) _ hs.1 hs.2

theorem exists_fixed_collar_shortening_constants :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (C : CylinderReference) (h : ℝ → SmoothRiemannianMetric IC Cylinder)
      (g : ℝ → SmoothRiemannianMetric I3 M)
      (F : PartialDiffeomorph IC I3 Cylinder M ∞)
      (U : Set Cylinder) (times : Set ℝ) (order : ℕ) (eps : ℝ),
      MetricComparisonOn h g F U times order eps → h 0 = C.metric 0 →
      0 ≤ eps → eps ≤ 1 / 2 → 0 ∈ times → U ⊆ F.source →
      (∀ y : Sphere 2, (y, 0) ∈ U) → ∀ (gamma : ℝ → Cylinder),
      ContMDiffOn 𝓘(ℝ, ℝ) IC 1 gamma (Icc (0 : ℝ) 1) →
      (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ U) →
      (gamma 0).2 = 0 → (gamma 1).2 = 0 →
      (∃ s ∈ Icc (0 : ℝ) 1, H₀ ≤ |(gamma s).2|) →
      ∃ shortcut : ℝ → M,
        shortcut 0 = F (gamma 0) ∧ shortcut 1 = F (gamma 1) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I3 1 shortcut (Icc (0 : ℝ) 1) ∧
        (∀ s ∈ Icc (0 : ℝ) 1, shortcut s ∈ F '' (univ ×ˢ ({0} : Set ℝ))) ∧
        metricPathELength (g 0) shortcut 0 1 + ENNReal.ofReal (1 / 2 : ℝ) <
          metricPathELength (g 0) ((F : Cylinder → M) ∘ gamma) 0 1 := by
  obtain ⟨D, hD, hshortcuts⟩ := exists_uniform_transverse_shortcuts (M := M)
  refine ⟨D + 1, by linarith, ?_⟩
  intro C h g F U times order eps cmp hmetric heps hepsHalf hzero hsource hlevel
    gamma hgamma hU hstart hend hvisit
  obtain ⟨s, hs, hdepth⟩ := hvisit
  have heps1 : eps ≤ 1 := by linarith
  obtain ⟨shortcut, hx, hy, hC, hS, hlength⟩ :=
    hshortcuts C h g F U times order eps 0 cmp hmetric heps heps1 hzero hsource hlevel
      (gamma 0).1 (gamma 1).1
  have h₀ : ((gamma 0).1, (0 : ℝ)) = gamma 0 := Prod.ext rfl hstart.symm
  have h₁ : ((gamma 1).1, (0 : ℝ)) = gamma 1 := Prod.ext rfl hend.symm
  refine ⟨shortcut, h₀ ▸ hx, h₁ ▸ hy, hC, hS, ?_⟩
  have hc : (1 / 2 : ℝ) ≤ Real.sqrt (1 - eps) := by
    have hsq := Real.sq_sqrt (by linarith : 0 ≤ 1 - eps)
    nlinarith [Real.sqrt_nonneg (1 - eps)]
  have hcost : D + 1 ≤ 2 * Real.sqrt (1 - eps) * |(gamma s).2| := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (abs_nonneg (gamma s).2)]
  calc
    _ ≤ ENNReal.ofReal D + ENNReal.ofReal (1 / 2 : ℝ) := add_le_add hlength le_rfl
    _ = ENNReal.ofReal (D + 1 / 2) := (ENNReal.ofReal_add hD.le (by norm_num)).symm
    _ < ENNReal.ofReal (D + 1) := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    _ ≤ ENNReal.ofReal (2 * Real.sqrt (1 - eps) * |(gamma s).2|) :=
      ENNReal.ofReal_le_ofReal hcost
    _ ≤ _ := collar_return_length_lower C g F cmp hmetric heps heps1 hzero hsource hgamma hU hstart hend hs

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
