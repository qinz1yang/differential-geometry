import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeComparisonDerivX140
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZClosed
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Staged

/-!
# An actual numeric selection for the X140 closed derivative consumer

The original closed BFZD producer supplies the family. Its positive thresholds are consumed
in their original order by the existing staged minimum/half constructions. The extra derivative
caps are selected after Delta and its region thresholds. No row inequality is an input below.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Curvature
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- Fixed positive tolerances for the auxiliary staged numeric construction. -/
def selectedTolerances_X140S : C14Tol where
  γT := 1
  θs := 1 / 2
  θe := 1 / 2
  θ2 := 1 / 2
  Cρ := 1
  e₁ := 1
  C₁ := 1
  γT_pos := by norm_num
  γT_le := le_rfl
  θs_pos := by norm_num
  θs_lt := by norm_num
  θe_pos := by norm_num
  θe_lt := by norm_num
  θ2_pos := by norm_num
  θ2_lt := by norm_num
  Cρ_pos := one_pos
  e₁_pos := one_pos
  C₁_pos := one_pos

/-- Choose every row number before the standing sequence, then apply the derivative theorem
to the actual BFZD family on its tail. The original sequence geometry assumptions are retained. -/
theorem exists_selected_edgeB_derivative_X140S (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
    ∃ (P : C14PreFinal) (Lc η₀ : ℝ), 0 < Lc ∧ 0 < η₀ ∧
      P.b ≤ η₀ ∧ P.β 1 ≤ η₀ ∧ P.σc ≤ θ ^ 2 / 10 ^ 8 ∧ P.μ * P.Δ < θ / 100 ∧
      ∀ (X : ℕ → Type) [_mX : ∀ i, MetricSpace (X i)] [_cX : ∀ i, ChartedSpace E3 (X i)]
        [_iX : ∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [_kX : ∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
      ∀ hor : ∀ i, ManifoldOrientation (𝓡 3) (X i) 3,
      ∃ V δ Lmax : ℝ, P.T ≤ V ∧ 0 < δ ∧ δ < P.δ' ∧ 0 < Lmax ∧ Lc ≤ Lmax ∧
        ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p P.w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (P.w / (2 * (1 + 2 * P.Λ⁻¹) ^ 3))) ∧
        ∃ F : LocalPacketsOnBFRZ (X i) (g i) (hmetric i) ρ hρpos P.Λ P.β P.Δ P.σs K
          P.σc P.μ P.b P.s P.b' P.s' P.ε P.γc P.βc Lmax P.τ P.γ δ P.εr P.e P.T V
          P.vs P.ζ P.Λz univ univ univ univ (hor i),
        let L := F.toLocalPacketsOnBFR.toLocalPacketsOnBF.toLocalPacketsOnB
        ∀ i₀, i₀ ∈ L.edgeB.centres → ∀ j, j ∈ egpEdgeList_BAUGP L i₀ →
          ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i₀ (20 * P.Δ * ρ i₀), ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              (ρ i₀)⁻¹ ^ 2 * (g i).inner x w w = 1 →
                |ρ j / ρ i₀ * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA j) x w -
                  a * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA i₀) x w| < θ := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localPacketsOnBFRZ_closed_BFZD K hK A hA
  obtain ⟨p1, -, rfl, -, h⟩ :=
    c14_stage_circ_FAM2b selectedTolerances_X140S ha₂ (r := 1) one_pos h
  obtain ⟨p2, rfl, -, -, h⟩ :=
    c14_stage_collar_FAM2b p1 (r₁ := 1) (r₂ := 1) one_pos one_pos h
  obtain ⟨p3, rfl, -, h⟩ := c14_stage_excl_FAM2b p2 (r := 1) one_pos h
  obtain ⟨p4, rfl, -, h⟩ := c14_stage_scale_FAM2b p3 0 h
  have hΔ0 : 0 < p4.Δ := by linarith [p4.Δ_gt6]
  have hΔ1 : 1 ≤ p4.Δ := by linarith [p4.Δ_gt6]
  have hβ₂1 : p4.β₂ < 1 / 1000000 := p4.β₂_le7.trans_lt (by norm_num)
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ :=
    egp04_edgeB_derivative_region_X140 hΔ1 p4.β₂_pos hβ₂1 hθ hθ1
  obtain ⟨p5, rfl, hσcθ, -, hμθ, -, -, -, -, h⟩ := c14_stage_edge_FAM2b p4
    (rσc := θ ^ 2 / 10 ^ 8) (rε := 1) (rμ := θ / (200 * p4.Δ)) (rτ := 1)
    (rs := 1) (rb' := 1) (rs' := 1)
    (by positivity) one_pos (by positivity) one_pos one_pos one_pos one_pos h
  obtain ⟨p6, rfl, -, h⟩ := c14_stage_lip_FAM2b p5 (r := 1) one_pos h
  obtain ⟨p7, rfl, -, h⟩ := c14_stage_vol_FAM2b p6 (r := 1) one_pos h
  obtain ⟨p8, rfl, hbη, h⟩ := c14_stage_split_FAM2b p7 hη₀ h
  obtain ⟨p9, rfl, -, -, h⟩ :=
    c14_stage_slim_FAM2b p8 (r₁ := 1) (r₂ := 1) one_pos one_pos h
  obtain ⟨p10, rfl, -, hβη, h⟩ := c14_stage_beta_FAM2b p9 (rζ := 1) one_pos hη₀ h
  obtain ⟨p11, rfl, -, h⟩ := c14_stage_zero_FAM2b p10 (r := 1) one_pos h
  obtain ⟨P, rfl, -, -, h⟩ := c14_stage_final_FAM2b p11 0 (re := 1) one_pos h
  have hμΔ : P.μ * P.Δ < θ / 100 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 200 * P.Δ)).mp hμθ
    nlinarith
  refine ⟨P, Lc, η₀, hLc, hη₀, hbη, hβη, hσcθ, hμΔ, ?_⟩
  intro X mX cX iX kX g hmetric α hα hstand hder hor
  obtain ⟨V, hTV, δ, hδ, hδδ', hV⟩ := h X g hmetric α hα hstand hder hor
  let Lmax := max 1 Lc
  have hLmax : 0 < Lmax := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hLcLmax : Lc ≤ Lmax := le_max_right _ _
  refine ⟨V, δ, Lmax, hTV, hδ, hδδ', hLmax, hLcLmax, ?_⟩
  filter_upwards [hV Lmax hLmax] with i hi
  obtain ⟨ρ, hρpos, hρb, ⟨F⟩⟩ := hi
  have hμ1 : P.μ ≤ 1 / 100 := P.μ_le.trans (by norm_num)
  have hτ1 : P.τ ≤ 1 / 100 := P.τ_le30.trans (by norm_num)
  have hs6 : P.s < 1 / 1000000 := by
    simpa only [show (10 : ℝ) ^ 6 = 1000000 by norm_num] using P.s_lt6
  exact ⟨ρ, hρpos, hρb, F,
    hrow F hbη hs6 hβη hLcLmax P.Λ_pos.le P.LΛ_lt hμ1 hτ1 hσcθ hμΔ⟩

end DifferentialGeometry.Geometry.Collapse
