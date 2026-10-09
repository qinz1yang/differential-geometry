import DifferentialGeometry.Geometry.Fibration.ActualStageTargets
import DifferentialGeometry.Geometry.Fibration.ActualEdgeCloudCoverageApplications

/-!
# FC27's edge test: EGP07's planes inside `Q₂`, in the stage notation of GAF01/GAF02

Blueprint `master207B.tex`, FC27 (`found:fibration-projected-clouds`, B:1658, the edge case from
EGP07) in the frozen form of `sheet-C14-GAF2.md` (stage `st = 1`, `k = 1`) with the amendment
`plane x ≤ Q₂` (needed for GAF02's `P_j = π_{Q_j} ∘ p_j`).

* `fc27_edge_test_GAF3`: on `LocalChartPacketsC14` under EGP07's hypotheses (verbatim,
  `egp07_coverage`), planes over `S₂ = gafCloud 1` with dimension `gafStageDim 1 = 1`, inside
  `gafStageQ 1 = Q₂`, with the (CS) test of CFS15 / FC27 at quality `Γ` and radius `Σρ(sel x)`
  for EVERY selection over `S̃₂ = gafCloudEnlarged 1`, and EGP07's all-preimage rank clauses for
  the same planes (consumed by GAF02's normal error). The planes are `im DΦ_i(η_i p)` at a core
  witness `p`; `Φ_i` is `Q₂`-valued (`egp07_coverage`'s model clause), so
  `range_fderiv_le_range_blockRestrict_GAF3` puts them in `Q₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_GAF3e {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF3e {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF3e {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- A line through the derivative of a map `ℝ → H` with `‖v‖ ≤ ‖Dφ(a) v‖` has dimension one. -/
theorem finrank_range_fderiv_eq_one_GAF3 {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (φ : ℝ → H) (a : ℝ) (hlow : ∀ v : ℝ, ‖v‖ ≤ ‖fderiv ℝ φ a v‖) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ φ a : ℝ →ₗ[ℝ] H)) = 1 := by
  have hinj : Function.Injective (fderiv ℝ φ a : ℝ →ₗ[ℝ] H) := by
    intro z w hzw
    have h := hlow (z - w)
    have hzw' : fderiv ℝ φ a z = fderiv ℝ φ a w := hzw
    rw [map_sub, hzw', sub_self, norm_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  have h := LinearMap.finrank_range_of_inj hinj
  rw [Module.finrank_self] at h
  exact h

/-- **FC27, the edge test** (stage `1` of GAF01/GAF02; EGP07 with the planes inside `Q₂`). For
(EP) `Γ ∈ (0,1)`, `0 < Σ < min(Γ/200, Γ³/(100C†))`, `0 < e < min(1/100, ΓΣ/100, Σ/1000)` there are
EGP07's thresholds such that on every actual `LocalChartPacketsC14` with EGP07's hypotheses there
are planes `plane x` over `S₂ = gafCloud 1` (`im DΦ_i(η_i p)` at a core witness) with
(1) `dim plane x = gafStageDim 1` and `plane x ≤ gafStageQ 1 = Q₂`; (2) for ANY selection of
preimages over `S̃₂ = gafCloudEnlarged 1`, the (CS) test at quality `Γ`, radius `r = Σρ(sel x)`:
`hausdorffEDist (S̃₂ ∩ B(x, r/Γ)) ((x + plane x) ∩ B(x, r/Γ)) ≤ Γr`; (3) EGP07's all-preimage rank
clauses for `plane x` at every preimage `q` of `x` in the units of a reference edge centre `i`
(`D w = ρ(i)⁻¹dπ₂𝓔⁰_q(w)` on `ρ(i)⁻²g`-unit vectors: normal error `< e`, projection `≤ 3C†`, a unit
vector with projection `≥ 1/2`, and the projection onto `plane x` is onto). -/
theorem fc27_edge_test_GAF3 {Δ β₂ Γ Sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) (hΓ : Γ ∈ Ioo (0 : ℝ) 1) (hS : 0 < Sg)
    (hSmin : Sg < min (Γ / 200) (Γ ^ 3 / (100 * egpGraphConst)))
    (heg : 0 < eg) (hemin : eg < min (1 / 100) (min (Γ * Sg / 100) (Sg / 1000))) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
        σc ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        μ * Δ < eg / (20 * egpGraphConst) / 100 → 0 < σs →
        σs ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        vs < eg / (20 * egpGraphConst) / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T → 0 < ζ →
        ζ ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
        εr < eg / (20 * egpGraphConst) / (100 * (1000000 * Δ)) →
        ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
            Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
            Module.finrank ℝ (plane x) = gafStageDim 1 ∧
              plane x ≤ gafStageQ P.toLocalChartFamily P.zero 1) ∧
          (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
              cgpProjMap P.toLocalChartFamily P.zero
                (gafStageTags P.toLocalChartFamily P.zero 1) (sel x) = x) →
            ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
              hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 1 ∩
                  ball x (Sg * ρ (sel x) / Γ))
                ((AffineSubspace.mk' x (plane x) :
                    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                  ball x (Sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (Sg * ρ (sel x)))) ∧
          ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∃ i ∈ P.edge.centres,
            ∀ q : X,
            cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
              (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
                ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
                  (plane x).starProjection
                    ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg) ∧
              (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
                ‖(plane x).starProjection
                    ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ ≤ 3 * egpGraphConst) ∧
              (∃ w₀ : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w₀ w₀ = 1 ∧
                1 / 2 ≤ ‖(plane x).starProjection ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
                      (cgpProjMap P.toLocalChartFamily P.zero
                        (cgpQ2Tags P.toLocalChartFamily P.zero)) q w₀)‖) ∧
              (∀ k ∈ plane x, ∃ w : TangentSpace 𝓘(ℝ, E3) q,
                  (plane x).starProjection
                    ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w) = k) := by
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ := egp07_coverage hΔ hβ₂ hβ₂1 hΓ hS hSmin heg hemin
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hb
    hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr
  have hrowP := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr
  have hΔ0 : 0 ≤ Δ := by linarith
  have hpt : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      ∃ W : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (Module.finrank ℝ W = gafStageDim 1 ∧ W ≤ gafStageQ P.toLocalChartFamily P.zero 1) ∧
        (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
          (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
            cgpProjMap P.toLocalChartFamily P.zero
              (gafStageTags P.toLocalChartFamily P.zero 1) (sel x) = x) →
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 1 ∩
              ball x (Sg * ρ (sel x) / Γ))
            ((AffineSubspace.mk' x W :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (Sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (Sg * ρ (sel x)))) ∧
        ∃ i ∈ P.edge.centres, ∀ q : X,
          cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
            (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
              ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
                W.starProjection
                  ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg) ∧
            (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
              ‖W.starProjection
                  ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ ≤ 3 * egpGraphConst) ∧
            (∃ w₀ : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w₀ w₀ = 1 ∧
              1 / 2 ≤ ‖W.starProjection ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
                    (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w₀)‖) ∧
            (∀ k ∈ W, ∃ w : TangentSpace 𝓘(ℝ, E3) q,
                W.starProjection
                  ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero)) q w) = k) := by
    intro x hx
    have hx' : x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
        fc27EdgeSet P.toLocalChartFamily 7 := hx
    obtain ⟨p, hp7, rfl⟩ := hx'
    obtain ⟨j, hp, hηp, htp⟩ := hp7
    have hj : j.1 ∈ P.edge.centres := (Set.Finite.mem_toFinset _).mp j.2
    have hrowj := hrowP j.1 hj
    obtain ⟨sgn, c, -, -, -, hlow, hQ2, -, hrk, hcov⟩ := hrowj
    have hη8 : |P.edge.coord j.1 p| ≤ 8 * Δ := by linarith
    have ht8 : cgpHeight P.toLocalChartFamily p ≤ 8 * Δ := by
      have h := htp
      linarith
    refine ⟨LinearMap.range (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero j.1 sgn c)
        (P.edge.coord j.1 p) : ℝ →ₗ[ℝ]
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), ⟨?_, ?_⟩, ?_,
      j.1, hj, ?_⟩
    · exact finrank_range_fderiv_eq_one_GAF3 _ _ (hlow _)
    · classical
      exact range_fderiv_le_range_blockRestrict_GAF3 _ _ hQ2 _
    · intro sel hsel
      have hpx : cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) p ∈
          gafCloudEnlarged P.toLocalChartFamily P.zero 1 :=
        gafCloud_subset_enlarged P.toLocalChartFamily P.zero hΔ0 1 hx
      exact hcov p hp hηp htp _ (hsel _ hpx)
    · intro q hq
      have hrkq := hrk p hp hη8 ht8 q hq
      exact ⟨hrkq.2.1, hrkq.2.2.1, hrkq.2.2.2.1, hrkq.2.2.2.2⟩
  choose! plane hplane using hpt
  exact ⟨plane, fun x hx => (hplane x hx).1, fun sel hsel x hx =>
    (hplane x hx).2.1 sel hsel, fun x hx => (hplane x hx).2.2⟩

end DifferentialGeometry.Geometry.Collapse
