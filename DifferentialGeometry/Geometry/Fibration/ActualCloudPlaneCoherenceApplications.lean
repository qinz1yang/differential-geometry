import DifferentialGeometry.Geometry.Fibration.ActualCloudPlaneCoherence

/-!
# Consumer of CFS08 on the actual clouds: CFS11's (LP) step on `LocalChartPackets`

CFS11's proof (B:2499–2501): "Conditions (DS) imply … the strict smallness requirements of CFS08
with `L = 128b`. That lemma proves (LP)."

* `cfs08_smallness_of_ds_KA3`: (DS) with `B = 5/3` (B:2444) implies CFS08's strict bound at
  `L = 128b`.
* `cfs08_first_cloud_ds_packets`: on `LocalChartPackets`, FC07's first cloud with FC04's radius,
  `Σ ≤ 1/(640b)` and (DS): every two points of `S₁` within `128b·max r₁` have normal offset
  `≤ δ r₁(x)` and normal projectors within `16δ`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- (DS) with `B = 5/3` gives CFS08's strict smallness at the scale `L = 128b`. -/
theorem cfs08_smallness_of_ds_KA3 {bb δc : ℝ} (hbb : 1 ≤ bb) (hδ : 0 < δc)
    (hds : δc ≤ min (1 / (8 * (5 / 3)))
      (min (1 / (4 * (128 * bb * (5 / 3) + 3))) (1 / (8 * (5 / 3 + 1))))) :
    δc < min (1 / (4 * (5 / 3)))
      (min (1 / (2 * (128 * bb * (5 / 3) + 3))) (1 / (4 * (5 / 3 + 1)))) := by
  have h1 := hds.trans (min_le_left _ _)
  have h2 := (hds.trans (min_le_right _ _)).trans (min_le_left _ _)
  have h3 := (hds.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hpos : 0 < 128 * bb * (5 / 3) + 3 := by positivity
  refine lt_min (h1.trans_lt (by norm_num)) (lt_min (h2.trans_lt ?_) (h3.trans_lt (by norm_num)))
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN'_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN'_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC'_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **CFS11's (LP) step on FC07's first cloud** (`LocalChartPackets`, `Σ ≤ 1/(640b)`, (DS)): under
the (CS) tests on `S₁`, any two points of `S₁` within `128b·max r₁` have normal offset
`≤ δ r₁(x)` and normal projectors within `16δ`. -/
theorem cfs08_first_cloud_ds_packets
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {bb sg δc : ℝ} (hbb : 1 ≤ bb) (hsg : 0 < sg) (hbsg : 128 * bb * sg ≤ 1 / 5)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hdim : ∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero ''
        fc04Set P.toLocalChartFamily P.zero 7,
      Module.finrank ℝ (plane x) = 2)
    (hδ : 0 < δc) (hds : δc ≤ min (1 / (8 * (5 / 3)))
      (min (1 / (4 * (128 * bb * (5 / 3) + 3))) (1 / (8 * (5 / 3 + 1)))))
    (hcloud : ∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero ''
        fc04Set P.toLocalChartFamily P.zero 7,
      hausdorffEDist (cgpGlobalMap P.toLocalChartFamily P.zero ''
          fc04Set P.toLocalChartFamily P.zero 8 ∩
          ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / δc))
        ((AffineSubspace.mk' x (plane x) :
            Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
          ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / δc)) ≤
        ENNReal.ofReal (δc * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x)) :
    ∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
      ∀ y ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
      dist y x ≤ 128 * bb * max (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x)
        (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg y) →
      ‖(plane x)ᗮ.starProjection (y - x)‖ ≤
          δc * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x ∧
        ‖(plane x)ᗮ.starProjection - (plane y)ᗮ.starProjection‖ ≤ 16 * δc := by
  intro x hx y hy hd
  have h := cfs08_first_cloud P.toLocalChartFamily P.zero (L' := 128 * bb) (by linarith) hsg
    hbsg plane hdim hδ (cfs08_smallness_of_ds_KA3 hbb hδ hds) hcloud x hx y hy hd
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  ring

end DifferentialGeometry.Geometry.Collapse
