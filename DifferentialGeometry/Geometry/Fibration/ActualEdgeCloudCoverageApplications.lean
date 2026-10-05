import DifferentialGeometry.Geometry.Fibration.ActualEdgeCloudCoverage
import DifferentialGeometry.Geometry.Fibration.ActualEdgeCloudApplications
import DifferentialGeometry.Geometry.Fibration.ActualSlimGraphModel
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Applications
import DifferentialGeometry.Geometry.Fibration.ActualCloudPlaneCoherence

/-!
# EGP07 on the final family: rank and cloud coverage together (`egp07_coverage`)

Blueprint `master207B.tex`, EGP07 (`thm:fibration-actual-second-cloud`, B:5141–5225): for
`0 < Γ < 1` and (EP) `0 < Σ < min(Γ/200, Γ³/(100C†))`, `0 < e < min(1/100, ΓΣ/100, Σ/1000)`, the
projected images `(S₂, S̃₂, r)`, `r(x) = Σρ(p_x)` for ANY chosen preimage, satisfy FC27's (CS)
test with the planes `A_x = x + im DΦ_i(a)`; the rank estimates hold for exactly these planes at
all preimages.

* `egp07_coverage` (frozen): on every actual `LocalChartPacketsC14` with EGP06's hypotheses, at
  every edge centre `i`, ONE choice of signs and translations carries EGP06's model clauses, (EG),
  `egp07_rank`'s all-preimage rank clauses AND, at every core witness `p` of `i`
  (`p ∈ B(i, 100Δρ(i))`, `|η_i(p)| ≤ 7Δ`, `t(p) ≤ 7Δ`) and every preimage `p'` of `x = π₂F(p)`:
  `d_H(S̃₂ ∩ B(x, Σρ(p')/Γ), (x + range DΦ_i(η_i(p))) ∩ B(x, Σρ(p')/Γ)) ≤ Γ·Σρ(p')` — exactly the
  hypothesis `hcloud` of `cfs11_edge_cloud` with `sg = Σ`, `δc = Γ`, `select x = p'`.
  The section is EGP05's `LocalChartPacketsC14.edge_section_FAM`; the radii come from FC27's (AS)
  (`fc27_edge_cloud_scale`). (EP) is taken verbatim; `Γ < 1` and `e < Σ/1000` are not used here.
* `egp07_row_C14`: FC27's packaged form (the edge analogue of `sgp06_row_C14`): ONE choice of
  planes `plane x` (a line at every point of `S₂`) such that for EVERY selection of preimages over
  `S̃₂` the (CS) test `hcloud` of `cfs11_edge_cloud` / `cfs08_edge_cloud` holds (`sg = Σ`,
  `δc = Γ`), and at every point `x` of `S₂` some edge centre `i` and `T_x` with
  `plane x = range T_x` carry the all-preimage rank clauses at every `q` with `π₂F(q) = x`.
* `egp07_edge_coherence_C14` (consumer): the planes of `egp07_row_C14` feed `cfs08_edge_cloud`
  (CFS08 on FC27's edge cloud): (LC) for every pair of `S₂` at distance `≤ L' max(r)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_KC5c {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_KC5c {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_KC5c {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

open Classical in
/-- **EGP07 on the final family: rank and coverage from ONE choice.** For `Δ ≥ 1`,
`β₂ ∈ (0, 10⁻⁶)`, `0 < Γ < 1` and (EP) there are `Lc, η₀ > 0` such that on every actual
`LocalChartPacketsC14` with EGP06's hypotheses, at every edge centre `i` there is ONE choice of
signs and translations for which `Φ_i` carries EGP06's model clauses, (EG), `egp07_rank`'s rank
clauses, and FC27's (CS) test at every core witness `p` of `i` for every preimage `p'` of
`π₂F(p)`. -/
theorem egp07_coverage {Δ β₂ Γ Sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hΓ : Γ ∈ Ioo (0 : ℝ) 1) (hS : 0 < Sg)
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
        ∀ i ∈ P.edge.centres,
          ∃ sgn c : CGPTag P.toLocalChartFamily P.zero → ℝ, (∀ t, |sgn t| ≤ 1) ∧
            ContDiff ℝ ∞ (egpModelGraph P.toLocalChartFamily P.zero i sgn c) ∧
            (∀ a, ‖fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c) a‖ ≤
                egpGraphConst ∧
              ‖fderiv ℝ (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)) a‖ ≤
                egpGraphConst) ∧
            (∀ a v : ℝ, ‖v‖ ≤ ‖fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c) a v‖) ∧
            (∀ a, blockRestrict (cgpQ2Tags P.toLocalChartFamily P.zero)
              (egpModelGraph P.toLocalChartFamily P.zero i sgn c a) =
                egpModelGraph P.toLocalChartFamily P.zero i sgn c a) ∧
            (∀ x ∈ ball i (100 * Δ * ρ i), |P.edge.coord i x| ≤ 8 * Δ →
              cgpHeight P.toLocalChartFamily x ≤ 8 * Δ →
              ‖(ρ i)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero) x -
                egpModelGraph P.toLocalChartFamily P.zero i sgn c (P.edge.coord i x)‖ < eg ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
                ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero)) x w -
                  fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
                    (P.edge.coord i x) (mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w)‖ < eg) ∧
            (∀ p ∈ ball i (100 * Δ * ρ i), |P.edge.coord i p| ≤ 8 * Δ →
              cgpHeight P.toLocalChartFamily p ≤ 8 * Δ → ∀ q : X,
              cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q =
                cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) p →
              P.edge.coord i q = P.edge.coord i p ∧
              (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
                ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
                  (LinearMap.range (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
                    (P.edge.coord i p) : ℝ →ₗ[ℝ]
                      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))).starProjection
                    ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg) ∧
              (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
                ‖(LinearMap.range (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
                    (P.edge.coord i p) : ℝ →ₗ[ℝ]
                      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))).starProjection
                    ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ ≤ 3 * egpGraphConst) ∧
              (∃ w₀ : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w₀ w₀ = 1 ∧
                1 / 2 ≤ ‖(LinearMap.range (fderiv ℝ
                    (egpModelGraph P.toLocalChartFamily P.zero i sgn c) (P.edge.coord i p) :
                    ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
                    ).starProjection ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
                      (cgpProjMap P.toLocalChartFamily P.zero
                        (cgpQ2Tags P.toLocalChartFamily P.zero)) q w₀)‖) ∧
              (∀ k ∈ LinearMap.range (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
                  (P.edge.coord i p) : ℝ →ₗ[ℝ]
                    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
                ∃ w : TangentSpace 𝓘(ℝ, E3) q,
                  (LinearMap.range (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
                    (P.edge.coord i p) : ℝ →ₗ[ℝ]
                      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))).starProjection
                    ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w) = k)) ∧
            ∀ p ∈ ball i (100 * Δ * ρ i), |P.edge.coord i p| ≤ 7 * Δ →
              cgpHeight P.toLocalChartFamily p ≤ 7 * Δ → ∀ p' : X,
              cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) p' =
                cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) p →
              hausdorffEDist (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero) '' fc27EdgeSet P.toLocalChartFamily 8 ∩
                  ball (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero) p) (Sg * ρ p' / Γ))
                ((AffineSubspace.mk' (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero) p)
                    (LinearMap.range (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
                      (P.edge.coord i p) : ℝ →ₗ[ℝ]
                        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) :
                    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                  ball (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero) p) (Sg * ρ p' / Γ)) ≤
                ENNReal.ofReal (Γ * (Sg * ρ p')) := by
  have hΓ0 := hΓ.1
  have hSΓ : Sg < Γ / 200 := (lt_min_iff.mp hSmin).1
  have hC := egpGraphConst_pos_KC4
  have hSC : egpGraphConst * Sg < Γ ^ 3 / 100 := by
    have h := (lt_min_iff.mp hSmin).2
    rw [lt_div_iff₀ (by positivity)] at h
    rw [lt_div_iff₀ (by norm_num)]
    linarith
  have heg1 : eg < 1 / 100 := (lt_min_iff.mp hemin).1
  have hegΓ : eg < Γ * Sg / 100 := (lt_min_iff.mp (lt_min_iff.mp hemin).2).1
  have hsm : ∀ Λ : ℝ, 1000000 * Δ * Λ < 1 / 100000 → Λ * (1000000 * Δ) ≤ 1 / 4 :=
    fun Λ h => by linarith
  obtain ⟨Lc, η₀, hLc, hη₀, hrk⟩ := egp07_rank hΔ hβ₂ hβ₂1 heg heg1
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hb
    hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr i hi
  have hrkP := hrk X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr
  have hrki := hrkP i hi
  obtain ⟨sgn, c, hsgn, hcd, hbd, hlow, hQ, hEG, hrank⟩ := hrki
  refine ⟨sgn, c, hsgn, hcd, hbd, hlow, hQ, hEG, hrank, ?_⟩
  intro p hp hηp htp p' hp'
  have hsec := P.edge_section_FAM hi
  obtain ⟨sec, -, hsec'⟩ := hsec
  let j : P.edge.finite_centres.toFinset := ⟨i, (Set.Finite.mem_toFinset _).mpr hi⟩
  exact egp07_coverage_point_KC5 P.toLocalChartFamily P.zero hΔ hΛ (hsm Λ hLΛ) hΓ0 hS hSΓ hC hSC
    heg.le hegΓ j _ (hcd.of_le (by simp))
    (fun a => egpModelGraph_own P.toLocalChartFamily P.zero i sgn c j rfl a)
    (fun a => (norm_iteratedFDeriv_two_eq_SGP3 _ a).trans_le (hbd a).2)
    (fun x hx hη ht => (hEG x hx hη ht).1)
    (fun u hu => by
      obtain ⟨h1, -, h3, h4⟩ := hsec' ⟨u, abs_lt.mp hu⟩
      exact ⟨sec ⟨u, abs_lt.mp hu⟩, h1, h3, h4⟩)
    hp hηp htp hp'

open Classical in
/-- **EGP07 in FC27's packaged form** (the edge analogue of `sgp06_row_C14`): on every actual
`LocalChartPacketsC14` with EGP06's hypotheses and (EP), there are planes `plane x`, a line at
every point of `S₂`, such that for EVERY selection of preimages over `S̃₂` the (CS) test of
`cfs11_edge_cloud` / `cfs08_edge_cloud` holds with `sg = Σ`, `δc = Γ`, and at every preimage of
every point of `S₂` the all-preimage rank holds for exactly these planes (`P` the orthogonal
projection onto `plane x`, `D w = ρ(i)⁻¹dπ₂F_q(w)`). -/
theorem egp07_row_C14 {Δ β₂ Γ Sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hΓ : Γ ∈ Ioo (0 : ℝ) 1) (hS : 0 < Sg)
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
          (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
              fc27EdgeSet P.toLocalChartFamily 7, Module.finrank ℝ (plane x) = 1) ∧
          (∀ select : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
                fc27EdgeSet P.toLocalChartFamily 8,
              cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)
                (select x) = x) →
            ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
              fc27EdgeSet P.toLocalChartFamily 7,
              hausdorffEDist (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero) '' fc27EdgeSet P.toLocalChartFamily 8 ∩
                  ball x (Sg * ρ (select x) / Γ))
                ((AffineSubspace.mk' x (plane x) :
                    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                  ball x (Sg * ρ (select x) / Γ)) ≤ ENNReal.ofReal (Γ * (Sg * ρ (select x)))) ∧
          ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
              fc27EdgeSet P.toLocalChartFamily 7,
            ∃ (i : P.toLocalChartFamily.edge.finite_centres.toFinset)
              (Tx : ℝ →L[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
              plane x = LinearMap.range
                (Tx : ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∧
              ∀ q : X,
              cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
              (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i.1)⁻¹ ^ 2 * g.inner q w w = 1 →
                ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
                  (LinearMap.range (Tx : ℝ →ₗ[ℝ]
                    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))).starProjection
                    ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg) ∧
              (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i.1)⁻¹ ^ 2 * g.inner q w w = 1 →
                ‖(LinearMap.range (Tx : ℝ →ₗ[ℝ]
                    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))).starProjection
                    ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ ≤ 3 * egpGraphConst) ∧
              (∃ w₀ : TangentSpace 𝓘(ℝ, E3) q, (ρ i.1)⁻¹ ^ 2 * g.inner q w₀ w₀ = 1 ∧
                1 / 2 ≤ ‖(LinearMap.range (Tx : ℝ →ₗ[ℝ]
                    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))).starProjection
                    ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w₀)‖) ∧
              ∀ k ∈ LinearMap.range (Tx : ℝ →ₗ[ℝ]
                  BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
                ∃ w : TangentSpace 𝓘(ℝ, E3) q,
                  (LinearMap.range (Tx : ℝ →ₗ[ℝ]
                    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))).starProjection
                    ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w) = k := by
  obtain ⟨Lc, η₀, hLc, hη₀, hcov⟩ := egp07_coverage hΔ hβ₂ hβ₂1 hΓ hS hSmin heg hemin
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hb
    hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr
  have hcovP := hcov X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr
  choose sgn c hmod using hcovP
  have hW : ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
      fc27EdgeSet P.toLocalChartFamily 7, ∃ (j : P.toLocalChartFamily.edge.finite_centres.toFinset)
        (q : X), q ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |P.edge.coord j.1 q| ≤ 7 * Δ ∧
        cgpHeight P.toLocalChartFamily q ≤ 7 * Δ ∧
        cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x := by
    rintro x ⟨q, ⟨j, hq, hη, ht⟩, rfl⟩
    exact ⟨j, q, hq, hη, ht, rfl⟩
  choose jx qx hjq using hW
  have hmem : ∀ j : P.toLocalChartFamily.edge.finite_centres.toFinset, j.1 ∈ P.edge.centres :=
    fun j => (Set.Finite.mem_toFinset _).mp j.2
  obtain ⟨plane, hplane_def⟩ : ∃ plane :
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      plane = fun x => if h : x ∈ cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero) '' fc27EdgeSet P.toLocalChartFamily 7 then
        LinearMap.range (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero (jx x h).1
          (sgn (jx x h).1 (hmem (jx x h))) (c (jx x h).1 (hmem (jx x h))))
          (P.edge.coord (jx x h).1 (qx x h)) :
            ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        else ⊥ := ⟨_, rfl⟩
  have hplane : ∀ x (hx : x ∈ cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ2Tags P.toLocalChartFamily P.zero) '' fc27EdgeSet P.toLocalChartFamily 7),
      plane x = LinearMap.range (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero (jx x hx).1
          (sgn (jx x hx).1 (hmem (jx x hx))) (c (jx x hx).1 (hmem (jx x hx))))
          (P.edge.coord (jx x hx).1 (qx x hx)) :
            ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) := by
    intro x hx
    rw [hplane_def]
    exact dite_eq_left hx
  refine ⟨plane, ?_, ?_, ?_⟩
  · intro x hx
    rw [hplane x hx]
    have hm := hmod (jx x hx).1 (hmem (jx x hx))
    obtain ⟨-, -, -, hlow, -⟩ := hm
    refine finrank_range_KC5 _ fun z => ?_
    have h := hlow (P.edge.coord (jx x hx).1 (qx x hx)) z
    rwa [Real.norm_eq_abs] at h
  · intro select hselect x hx
    have hx8 : x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
        fc27EdgeSet P.toLocalChartFamily 8 :=
      image_mono (fc27EdgeSet_mono P.toLocalChartFamily (by linarith) (by norm_num)) hx
    have hp' := hselect x hx8
    obtain ⟨hq100, hη7, ht7, hqx⟩ := hjq x hx
    have hm := hmod (jx x hx).1 (hmem (jx x hx))
    obtain ⟨-, -, -, -, -, -, -, hcovc⟩ := hm
    have h := hcovc (qx x hx) hq100 hη7 ht7 (select x) (hp'.trans hqx.symm)
    rw [hqx] at h
    rw [hplane x hx]
    exact h
  · intro x hx
    have hq := hjq x hx
    have hq100 := hq.1
    have hη7 := hq.2.1
    have ht7 := hq.2.2.1
    have hqx := hq.2.2.2
    refine ⟨jx x hx, fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero (jx x hx).1
      (sgn (jx x hx).1 (hmem (jx x hx))) (c (jx x hx).1 (hmem (jx x hx))))
      (P.edge.coord (jx x hx).1 (qx x hx)), hplane x hx, fun q hq => ?_⟩
    have hm := hmod (jx x hx).1 (hmem (jx x hx))
    obtain ⟨-, -, -, -, -, -, hrank, -⟩ := hm
    have h := hrank (qx x hx) hq100 (by linarith) (by linarith) q (hq.trans hqx.symm)
    obtain ⟨-, h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, h3, h4⟩

/-- **Consumer: CFS08 on FC27's edge cloud with EGP07's planes** (the edge analogue of
`sgp06_slim_coherence_C14`). On the final family, for every selection of preimages over `S̃₂`, every
scale `L' ≥ 1` with `L'Σ ≤ 1/5` and `Γ` below CFS08's threshold, the planes of `egp07_row_C14`
satisfy (LC) for every pair of `S₂` at distance `≤ L' max(r(x), r(y))`, `r = Σρ ∘ select`. -/
theorem egp07_edge_coherence_C14 {Δ β₂ Γ Sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000)
    (hΓ : Γ ∈ Ioo (0 : ℝ) 1) (hS : 0 < Sg)
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
          ∀ select : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
                fc27EdgeSet P.toLocalChartFamily 8,
              cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)
                (select x) = x) →
            ∀ L' : ℝ, 1 ≤ L' → L' * Sg ≤ 1 / 5 →
            Γ < min (1 / (4 * (5 / 3)))
              (min (1 / (2 * (L' * (5 / 3) + 3))) (1 / (4 * (5 / 3 + 1)))) →
            ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
              fc27EdgeSet P.toLocalChartFamily 7,
            ∀ y ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
              fc27EdgeSet P.toLocalChartFamily 7,
              dist y x ≤ L' * max (Sg * ρ (select x)) (Sg * ρ (select y)) →
              ‖(plane x)ᗮ.starProjection (y - x)‖ ≤ Γ * (Sg * ρ (select x)) ∧
                ‖(plane x)ᗮ.starProjection - (plane y)ᗮ.starProjection‖ ≤ 6 * (5 / 3 + 1) * Γ := by
  have hsm : ∀ Λ : ℝ, 1000000 * Δ * Λ < 1 / 100000 → Λ * (1000000 * Δ) ≤ 1 / 4 :=
    fun Λ h => by linarith
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ := egp07_row_C14 hΔ hβ₂ hβ₂1 hΓ hS hSmin heg hemin
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hb
    hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr
  have hP := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr
  obtain ⟨plane, hdim, hcloud, -⟩ := hP
  refine ⟨plane, fun select hselect L' hL' hLsg hδsmall => ?_⟩
  exact cfs08_edge_cloud P.toLocalChartFamily P.zero hΔ hΛ (hsm Λ hLΛ) select hselect hL' hS hLsg
    plane hdim hΓ.1 hδsmall (hcloud select hselect)

end DifferentialGeometry.Geometry.Collapse
