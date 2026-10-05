import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Density

/-!
# LFR44 item 2 in the form used by FDC01 (replacement index, steps 6–7)

Lane C14-FAM3. Blueprint 207B, FDC01 (B:7217–7222): at an edge centre `p_i` of the one-stratum
which is nonslim, the weak border witness `q'` of (WB) (`d(q', p_i) < 4.1Δρ(p_i)`, lane C14-FDC1's
`fdc01_border_witness_FDC1` / `fdc01_original_steps_C14`) has, by LFR44 item 2, a strong edge `p`
with `d(p, q') < ρ(p)`, and `covers_strong` gives a selected edge centre `j` with
`d(p, j) < Δρ(j)`; hence `d(q', j) < (Δ + 2)ρ(j) ≤ 2Δρ(j)`.

* `LocalChartPacketsC14D.fdc01_replacement_centre_FAM3`: this statement on the final family
  `LocalChartPacketsC14D` (both the strong edge and the centre are returned).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **FDC01, steps 6–7** (B:7217–7222): a nonslim one-stratum point `i` (in FDC01 an edge
centre) and a weak edge `q'` with `d(q', i) < 4.1Δρ(i)` (the output of (WB)) give a strong edge
`a` with `d(q', a) < ρ(a)` and an edge centre `j` of the SAME family with `d(a, j) < Δρ(j)`,
`d(q', j) < (Δ + 2)ρ(j)` and `d(q', j) < 2Δρ(j)`. -/
theorem LocalChartPacketsC14D.fdc01_replacement_centre_FAM3
    (P : LocalChartPacketsC14D X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz) (hΛ : 0 ≤ Λ) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hΔ : 2 ≤ Δ)
    {i : X} (hi : i ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1)
    (hns : ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))))
    {q' : X} (hq' : @isEdgePoint.{0, 0} X (mX.rescale (ρ q')⁻¹ (inv_pos.mpr (hρ q'))) q' Δ b' s')
    (hq'i : dist q' i < 41 / 10 * Δ * ρ i) :
    ∃ a : X, @isEdgePoint.{0, 0} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))) a Δ b s ∧
      dist q' a < ρ a ∧ ∃ j ∈ P.edge.centres, dist a j < Δ * ρ j ∧
        dist q' j < (Δ + 2) * ρ j ∧ dist q' j < 2 * Δ * ρ j := by
  have hρi := hρ i
  have h10 : dist q' i < 10 * Δ * ρ i := by
    have := mul_pos (by linarith : (0 : ℝ) < Δ) hρi
    linarith
  obtain ⟨a, ha, hq'a, j, hj, haj, hq'j⟩ := P.weak_edge_centre_FAM3 hΛ hΔΛ hi hns hq' h10
  refine ⟨a, ha, hq'a, j, hj, haj, hq'j, hq'j.trans_le ?_⟩
  have hρj := hρ j
  nlinarith

end DifferentialGeometry.Geometry.Collapse
