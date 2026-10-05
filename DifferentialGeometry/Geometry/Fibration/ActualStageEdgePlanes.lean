import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneTypes

/-!
# The enhanced plane witness of stage `1` (edge / EGP06–EGP07): the producer

Blueprint `master207B.tex`, FC27 (B:1658) edge cloud, EGP06–EGP07; draft 59 §1 (D59-2) and the
consumption packages of review 60 (EGP06: the full model with global bounds and constants on the
same coefficients; FC27: plane provenance). The witness is built from EGP07's table at EVERY edge
centre `a` (`egp07_coverage`: ONE choice of signs and translations per centre for which the model
`Φ_a = egpModelGraph a sgn_a c_a` carries the global bounds, the lower bound, `Q₂`-values, (EG), the
rank clauses and the cloud test); no pruning (`K_a = id`); the plane at a cloud point is (PDEF)
`im DΦ_a(η_a(q))` at a chosen core witness `q` of the reference `a`.

* `edgeStagePlanes_of_row_PLN`: EGP07's table at every centre ⇒ `Nonempty (EdgeStagePlanes_PLN …)`.
* `exists_edgeStagePlanes_PLN`: the producer, with the thresholds and hypotheses of
  `fc27_edge_test_pp_GAF4` verbatim.
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
local instance instMetricNC14_PLNe {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_PLNe {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_PLNe {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

section C14

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

open Classical in
/-- **The stage-`1` witness from EGP07's table** (the per-family conclusion of `egp07_coverage`
at every edge centre): the enhanced stage-`1` plane witness exists. -/
theorem edgeStagePlanes_of_row_PLN
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) {Γ Sg eg : ℝ}
    (hrow :
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
            ENNReal.ofReal (Γ * (Sg * ρ p'))) :
    Nonempty (EdgeStagePlanes_PLN P Γ Sg eg) := by
  have hΔ0 : 0 ≤ Δ := by linarith
  have hm : ∀ a : P.toLocalChartFamily.edge.finite_centres.toFinset, a.1 ∈ P.edge.centres :=
    fun a => (Set.Finite.mem_toFinset _).mp a.2
  choose sgnf cf hspec using fun a : P.toLocalChartFamily.edge.finite_centres.toFinset => hrow a.1
      (hm a)
  have hpt : ∀ x : gafCloud P.toLocalChartFamily P.zero 1,
      ∃ (p : X) (j : P.toLocalChartFamily.edge.finite_centres.toFinset),
        p ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |P.edge.coord j.1 p| ≤ 7 * Δ ∧
        cgpHeight P.toLocalChartFamily p ≤ 7 * Δ ∧
        cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) p =
          x.1 := by
    intro x
    obtain ⟨p, hp, hpx⟩ := x.2
    have hp' : p ∈ fc27EdgeSet P.toLocalChartFamily 7 := hp
    obtain ⟨j, hpj, hηj, htj⟩ := hp'
    exact ⟨p, j, hpj, hηj, htj, hpx⟩
  choose pre ref hpre using hpt
  have hrp : ∀ x : gafCloudEnlarged P.toLocalChartFamily P.zero 1, ∃ q : X,
      q ∈ gafStageEnlargement P.toLocalChartFamily P.zero 1 ∧
        cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) q =
          x.1 := fun x => x.2
  choose rpre hrpre using hrp
  obtain ⟨D, hDr, hDp, hDref, hDm, hDk, hDc⟩ : ∃ D : StagePlaneData_PLN X (BlockSpace
      (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ℝ
      P.toLocalChartFamily.edge.finite_centres.toFinset (gafCloud P.toLocalChartFamily P.zero 1)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 1),
      D.rpre = rpre ∧ D.pre = pre ∧ D.ref = ref ∧
      D.model = (fun a => egpModelGraph P.toLocalChartFamily P.zero a.1 (sgnf a) (cf a)) ∧
      D.prune = (fun _ => ContinuousLinearMap.id ℝ _) ∧
      D.coord = (fun a => P.edge.coord a.1) :=
    ⟨⟨rpre, pre, ref, _, _, _⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hid : ∀ a, D.prune a ∘ D.model a =
      egpModelGraph P.toLocalChartFamily P.zero a.1 (sgnf a) (cf a) := fun a => by
    rw [hDk, hDm]; rfl
  have hDpl : ∀ x (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 1),
      D.plane x = LinearMap.range (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero
        (ref ⟨x, hx⟩).1 (sgnf (ref ⟨x, hx⟩)) (cf (ref ⟨x, hx⟩)))
        (P.edge.coord (ref ⟨x, hx⟩).1 (pre ⟨x, hx⟩)) : ℝ →ₗ[ℝ]
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) := fun x hx => by
    rw [D.plane_of_mem hx, hid, hDc, hDref, hDp]
  refine ⟨{ toStagePlaneData_PLN := D
            sgn := sgnf
            trans := cf
            model_eq := fun a => by rw [hDm]
            prune_eq := fun a => by rw [hDk]
            coord_eq := fun a => by rw [hDc]
            sgn_le := fun a => (hspec a).1
            model_bounds := fun a => by rw [hid a]; exact (hspec a).2.2.1
            model_lower := fun a => by rw [hid a]; exact (hspec a).2.2.2.1
            model_mem_Q := fun a => by rw [hid a]; exact (hspec a).2.2.2.2.1
            model_tg := fun a => by rw [hid a, hDc]; exact (hspec a).2.2.2.2.2.1
            rpre_spec := fun x => by rw [hDr]; exact hrpre x
            pre_spec := fun x => by rw [hDp, hDref, hDc]; exact hpre x
            dimension := fun x hx => ?_
            cloudy := fun sel hsel x hx => ?_
            normal := fun x hx q hq => ?_
            small_pp := fun x hx q hq a ha => ?_ }⟩
  · rw [hDpl x hx]
    exact ⟨finrank_range_fderiv_eq_one_GAF3 _ _ ((hspec (ref ⟨x, hx⟩)).2.2.2.1 _),
      range_fderiv_le_range_blockRestrict_GAF3 _ _ (hspec (ref ⟨x, hx⟩)).2.2.2.2.1 _⟩
  · have hxT := gafCloud_subset_enlarged P.toLocalChartFamily P.zero hΔ0 1 hx
    have hpx := (hpre ⟨x, hx⟩).2.2.2
    have h := (hspec (ref ⟨x, hx⟩)).2.2.2.2.2.2.2 (pre ⟨x, hx⟩) (hpre ⟨x, hx⟩).1
      (hpre ⟨x, hx⟩).2.1 (hpre ⟨x, hx⟩).2.2.1 (sel x) ((hsel x hxT).trans hpx.symm)
    have hpx' : cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)
        (pre ⟨x, hx⟩) = x := hpx
    rw [hpx'] at h
    rw [hDpl x hx]
    exact h
  · have hpx := (hpre ⟨x, hx⟩).2.2.2
    have h := (hspec (ref ⟨x, hx⟩)).2.2.2.2.2.2.1 (pre ⟨x, hx⟩) (hpre ⟨x, hx⟩).1
      (le_trans (hpre ⟨x, hx⟩).2.1 (by linarith)) (le_trans (hpre ⟨x, hx⟩).2.2.1 (by linarith)) q
      (hq.trans hpx.symm)
    change egpNormalSpec_PLN P eg (D.plane x) (D.ref ⟨x, hx⟩).1 q
    rw [hDpl x hx, hDref]
    exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · have hpx := (hpre ⟨x, hx⟩).2.2.2
    rw [hDpl x hx]
    exact edge_pp_point_GAF4 P.toLocalChartFamily P.zero hΔ hΛ hLΛ (ref ⟨x, hx⟩) (sgnf _) (cf _)
      (hpre ⟨x, hx⟩).1 (hpre ⟨x, hx⟩).2.1 (hpre ⟨x, hx⟩).2.2.1 q (hq.trans hpx.symm) a ha

/-- **The enhanced stage-`1` plane witness exists** (FC27 edge cloud with EGP07's table, review
60's EGP06 / FC27 packages): for `Δ ≥ 1`, `β₂ ∈ (0, 10⁻⁶)` and (EP) there are the thresholds of
`fc27_edge_test_pp_GAF4` (verbatim) such that every actual `LocalChartPacketsC14` satisfying them
carries an `EdgeStagePlanes_PLN P Γ Σ e`. -/
theorem exists_edgeStagePlanes_PLN {Δ β₂ Γ Sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
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
        Nonempty (EdgeStagePlanes_PLN P Γ Sg eg) := by
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ := egp07_coverage hΔ hβ₂ hβ₂1 hΓ hS hSmin heg hemin
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hb
    hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr
  exact edgeStagePlanes_of_row_PLN P hΔ hΛ hLΛ
    (hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hb hs
      hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr)

end C14

end DifferentialGeometry.Geometry.Collapse
