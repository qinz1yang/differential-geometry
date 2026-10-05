import DifferentialGeometry.Geometry.Fibration.ActualCloudLargeCover

/-!
# Consumer of CFS11 on the actual edge cloud: the reference ball `V_x` at unit buffer

* `cfs11_edge_cloud_unit`: on `LocalChartPackets` (FC07's parameter range), FC27's actual edge cloud
  with FC26's selected radius at `Σ = 1/640` (`b = 1`), any selection of preimages, one-dimensional
  planes with the (CS) tests at quality `δ ≤ 3/2596` (= (DS) at `b = 1`): a finite greedy set of
  centres `T ⊆ S₂` with `|x − x_i| < 3r_i`, and for every `x ∈ S₂` at most `551` selected centres
  whose closed `80r_j`-balls meet the reference ball `V_x = B(x, 8r(x))` of CFS11.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN'''_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN'''_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC'''_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **CFS11 on the actual edge cloud at unit buffer** (`Σ = 1/640`): a finite greedy set of centres
covering `S₂` to `3r_i`, and at most `551` selected centres meeting each reference ball
`V_x = B(x, 8r(x))`. -/
theorem cfs11_edge_cloud_unit
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (he : e < 1 / 40)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (select : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hselect : ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero) '' fc27EdgeSet P.toLocalChartFamily 8,
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) (select x) = x)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hdim : ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero) '' fc27EdgeSet P.toLocalChartFamily 7,
      Module.finrank ℝ (plane x) = 1)
    {δc : ℝ} (hδ : 0 < δc) (hδ' : δc ≤ 3 / 2596)
    (hcloud : ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero) '' fc27EdgeSet P.toLocalChartFamily 7,
      hausdorffEDist (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ2Tags P.toLocalChartFamily P.zero) '' fc27EdgeSet P.toLocalChartFamily 8 ∩
          ball x (1 / 640 * ρ (select x) / δc))
        ((AffineSubspace.mk' x (plane x) :
            Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
          ball x (1 / 640 * ρ (select x) / δc)) ≤ ENNReal.ofReal (δc * (1 / 640 * ρ (select x)))) :
    ∃ T' : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      T' ⊆ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
        fc27EdgeSet P.toLocalChartFamily 7 ∧ T'.Finite ∧
      (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
          fc27EdgeSet P.toLocalChartFamily 7,
        ∃ i ∈ T', dist x i < 3 * (1 / 640 * ρ (select i))) ∧
      ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
          fc27EdgeSet P.toLocalChartFamily 7,
        ((T' ∩ {i | (closedBall i (80 * (1 / 640 * ρ (select i))) ∩
          ball x (8 * (1 / 640 * ρ (select x)))).Nonempty}).ncard : ℝ) ≤ 551 := by
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hds : δc ≤ min (1 / (8 * (5 / 3)))
      (min (1 / (4 * (128 * 1 * (5 / 3) + 3))) (1 / (8 * (5 / 3 + 1)))) := by
    refine le_min ?_ (le_min ?_ ?_) <;> norm_num <;> linarith
  obtain ⟨T', hTS, hfin, -, hcover, -, -, hJ⟩ := cfs11_edge_cloud P hΛ hΔ hμ hτ (by linarith)
    hsmall select hselect le_rfl (by norm_num : (0 : ℝ) < 1 / 640) (by norm_num) plane hdim hδ
    hds hcloud
  refine ⟨T', hTS, hfin, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, h1, -⟩ := hcover x hx
    exact ⟨i, hi, h1⟩
  · have hrx : 0 < 1 / 640 * ρ (select x) := by have := hρ (select x); positivity
    have hsub : T' ∩ {i | (closedBall i (80 * (1 / 640 * ρ (select i))) ∩
          ball x (8 * (1 / 640 * ρ (select x)))).Nonempty} ⊆
        T' ∩ {i | (closedBall i (80 * 1 * (1 / 640 * ρ (select i))) ∩
          ball x (30 * 1 * (1 / 640 * ρ (select x)))).Nonempty} := by
      rintro i ⟨hi, z, hz1, hz2⟩
      refine ⟨hi, z, by rw [mul_one]; exact hz1, ?_⟩
      exact ball_subset_ball (by nlinarith) hz2
    have hle := (Set.ncard_le_ncard hsub (hfin.subset inter_subset_left))
    calc ((T' ∩ {i | (closedBall i (80 * (1 / 640 * ρ (select i))) ∩
          ball x (8 * (1 / 640 * ρ (select x)))).Nonempty}).ncard : ℝ) ≤
        ((T' ∩ {i | (closedBall i (80 * 1 * (1 / 640 * ρ (select i))) ∩
          ball x (30 * 1 * (1 / 640 * ρ (select x)))).Nonempty}).ncard : ℝ) := by
          exact_mod_cast hle
      _ ≤ 551 := by
          have h' := (hJ x hx).1
          norm_num at h' ⊢
          exact h'

end DifferentialGeometry.Geometry.Collapse
