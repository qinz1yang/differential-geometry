import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneTypes

/-!
# The enhanced plane witness of stage `2` (slim / SGP04–SGP06): the producer

Blueprint `master207B.tex`, FC27 (B:1658) slim cloud, SGP04–SGP06; draft 59 §1 (D59-2) and the
consumption packages of review 60 (SGP04: the FULL model `sgpFullGraph` with global bounds and the
constants on the same coefficients; SGP06 / FC27: plane provenance). The witness is built from
SGP05's table at EVERY slim centre `a` (`sgp05_row`: signs, translations, zero sign and zero
translation with (SG) for the full model and the rank at every preimage), SGP01's comparison list
(at most one meeting zero support, zero scale ratio `≥ T/20 ≥ 1`) for the global bounds; no pruning
(`K_a = id`); the plane at a cloud point is (PDEF) `im DΦ_a(η_a(q))` at a chosen core witness `q`.

* `slimStagePlanes_of_row_PLN`: SGP05's table at every centre ⇒ `Nonempty (SlimStagePlanes_PLN …)`.
* `exists_slimStagePlanes_PLN`: the producer, with the thresholds and hypotheses of
  `fc27_slim_test_pp_C14_GAF4` verbatim.
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
local instance instMetricNC14_PLNs {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_PLNs {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_PLNs {X : Type} [MetricSpace X] [ChartedSpace E3 X]
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

/-- SGP05's rank clauses at a core witness, in the form `sgpNormalSpec_PLN` (the plane named). -/
theorem slim_normal_of_rank_PLN
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) {eg : ℝ} (i : P.toLocalChartFamily.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ)
    (hrk :
      ∀ p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1),
        |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
          7 * (10 ^ 5 * Δ) →
        ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
          cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p →
        let Tx := fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
          ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p)
        let Pq := Tx.range.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
        Function.Surjective Pq ∧
        (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
          eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
          1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
        ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) :
    ∀ p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1),
      |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 7 * (10 ^ 5 * Δ) →
      ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
        cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p →
      sgpNormalSpec_PLN P eg (LinearMap.range (fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i
        sgn c zsgn zc) ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p) :
          ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) i.1 q :=
  hrk

open Classical in
/-- **The stage-`2` witness from SGP05's table** (the per-family conclusion of `sgp05_row` at every
slim centre) with SGP01's numbers (`10⁶ΔΛ < 10⁻⁵`, `e < 1/40`, `T ≥ 1600·10⁶Δ`, `0 < σ_s < 1/100`)
and (SP): the enhanced stage-`2` plane witness exists. -/
theorem slimStagePlanes_of_row_PLN
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 < σs) (hσ1 : σs < 1 / 100) {Γ sg eg : ℝ}
    (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * sgpGraphBound)) (heg : 0 < eg) (hegΓ : eg < Γ * sg / 100)
    (hrow :
    ∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset, ∃ sgn c zsgn zc : X → ℝ,
      (∀ j, |sgn j| ≤ 1) ∧ (∀ k, |zsgn k| ≤ 1) ∧
      (∀ x ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1),
        |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x| ≤
          8 * 10 ^ 5 * Δ →
        ‖(ρ i.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero) x -
          sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc
            ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)‖ < eg ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
            fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
              ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
              (mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1
                ((Set.Finite.mem_toFinset _).mp i.2)).coord x w)‖ ≤
            eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner x w w)) ∧
      ∀ p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1),
        |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
          7 * (10 ^ 5 * Δ) →
        ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
          cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p →
        let Tx := fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
          ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p)
        let Pq := Tx.range.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
        Function.Surjective Pq ∧
        (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
          eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
          1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
        ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) :
    Nonempty (SlimStagePlanes_PLN P Γ sg eg) := by
  have hΔ0 : 0 ≤ Δ := by linarith
  have hm : ∀ a : P.toLocalChartFamily.slim.finite_centres.toFinset, a.1 ∈ P.slim.centres :=
    fun a => (Set.Finite.mem_toFinset _).mp a.2
  choose sgnf cf zsgnf zcf hspec using hrow
  -- SGP01's zero clauses at every reference
  have hs01 := fun a : P.toLocalChartFamily.slim.finite_centres.toFinset =>
    sgp01_row P.toLocalChartPacketsR hΛ hΔ hLΛ he hT hσs.le hσ1.le (hm a)
  have hs0 : ∀ (a : P.toLocalChartFamily.slim.finite_centres.toFinset) k (hk : k ∈ P.zero.centres),
      sgpZeroMeets P.zero (Δ := Δ) (ρ := ρ) a.1 k hk → 1 ≤ (P.zero.zero k hk).radius / ρ a.1 :=
    fun a k hk hmt => (one_le_div_twenty_SGP4 hΔ hT).trans ((hs01 a).2.2.2.2.1 k hk hmt).1
  have hpt : ∀ x : gafCloud P.toLocalChartFamily P.zero 2,
      ∃ (p : X) (j : P.toLocalChartFamily.slim.finite_centres.toFinset),
        p ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| ≤ 7 * (10 ^ 5 * Δ) ∧
        cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) p =
          x.1 := by
    intro x
    obtain ⟨p, hp, hpx⟩ := x.2
    have hp' : p ∈ fc27SlimSet P.toLocalChartFamily 7 := hp
    obtain ⟨j, hpj, hηj⟩ := hp'
    refine ⟨p, j, hpj, ?_, hpx⟩
    rw [← mul_assoc]
    exact hηj
  choose pre ref hpre using hpt
  have hrp : ∀ x : gafCloudEnlarged P.toLocalChartFamily P.zero 2, ∃ q : X,
      q ∈ gafStageEnlargement P.toLocalChartFamily P.zero 2 ∧
        cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) q =
          x.1 := fun x => x.2
  choose rpre hrpre using hrp
  obtain ⟨D, hDr, hDp, hDref, hDm, hDk, hDc⟩ : ∃ D : StagePlaneData_PLN X (BlockSpace
      (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ℝ
      P.toLocalChartFamily.slim.finite_centres.toFinset (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2),
      D.rpre = rpre ∧ D.pre = pre ∧ D.ref = ref ∧
      D.model = (fun a => sgpFullGraph P.toLocalChartFamily P.zero a (sgnf a) (cf a) (zsgnf a)
        (zcf a)) ∧
      D.prune = (fun _ => ContinuousLinearMap.id ℝ _) ∧
      D.coord = (fun a => (P.slim.centre a.1 ((Set.Finite.mem_toFinset _).mp a.2)).coord) :=
    ⟨⟨rpre, pre, ref, _, _, _⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hid : ∀ a, D.prune a ∘ D.model a =
      sgpFullGraph P.toLocalChartFamily P.zero a (sgnf a) (cf a) (zsgnf a) (zcf a) := fun a => by
    rw [hDk, hDm]; rfl
  have hDpl : ∀ x (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 2),
      D.plane x = LinearMap.range (fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero
        (ref ⟨x, hx⟩) (sgnf (ref ⟨x, hx⟩)) (cf (ref ⟨x, hx⟩)) (zsgnf (ref ⟨x, hx⟩))
        (zcf (ref ⟨x, hx⟩)))
        ((P.slim.centre (ref ⟨x, hx⟩).1 ((Set.Finite.mem_toFinset _).mp (ref ⟨x, hx⟩).2)).coord
          (pre ⟨x, hx⟩)) : ℝ →ₗ[ℝ]
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) := fun x hx => by
    rw [D.plane_of_mem hx, hid, hDc, hDref, hDp]
  have hpoint := fun x (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 2) =>
    sgp06_point_SGP5 P.toLocalChartFamily P.zero hΔ hΛ hLΛ (ref ⟨x, hx⟩) (sgnf _) (cf _) (zsgnf _)
      (zcf _) (hspec (ref ⟨x, hx⟩)).1 (hspec (ref ⟨x, hx⟩)).2.1 (hs0 (ref ⟨x, hx⟩))
      (hs01 (ref ⟨x, hx⟩)).2.2.2.1 hΓ hΓ1 hsg hsgΓ hsgC heg hegΓ
      (fun y hy hyη => ((hspec (ref ⟨x, hx⟩)).2.2.1 y hy hyη).1) (hpre ⟨x, hx⟩).1
      (hpre ⟨x, hx⟩).2.1
  refine ⟨{ toStagePlaneData_PLN := D
            sgn := sgnf
            trans := cf
            zsgn := zsgnf
            ztrans := zcf
            model_eq := fun a => by rw [hDm]
            prune_eq := fun a => by rw [hDk]
            coord_eq := fun a => by rw [hDc]
            sgn_le := fun a => (hspec a).1
            zsgn_le := fun a => (hspec a).2.1
            model_bounds := fun a u => ?_
            model_mem_Q := fun a u => ?_
            model_tg := fun a => by rw [hid a, hDc]; exact (hspec a).2.2.1
            rpre_spec := fun x => by rw [hDr]; exact hrpre x
            pre_spec := fun x => by rw [hDp, hDref, hDc]; exact hpre x
            dimension := fun x hx => ?_
            cloudy := fun sel hsel x hx => ?_
            normal := fun x hx q hq => ?_
            small_pp := fun x hx q hq a ha => ?_ }⟩
  · rw [hid a]
    have h := sgp04_full_model_bounds P.toLocalChartFamily P.zero hΔ hΛ hLΛ a (sgnf a) (cf a)
      (zsgnf a) (zcf a) (hspec a).1 (hspec a).2.1 (hs0 a) (hs01 a).2.2.2.1 u
    exact ⟨h.1, h.2.1⟩
  · rw [hid a]
    exact sgpFullGraph_blockRestrict_GAF3 P.toLocalChartFamily P.zero a _ _ _ _ u
  · rw [hDpl x hx]
    exact ⟨(hpoint x hx).1, range_fderiv_sgpFullGraph_le_GAF3 P.toLocalChartFamily P.zero _ _ _ _
      _ _⟩
  · have hpx : cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
        (pre ⟨x, hx⟩) = x := (hpre ⟨x, hx⟩).2.2
    have h := (hpoint x hx).2 sel hsel
    rw [hpx] at h
    rw [hDpl x hx]
    exact h
  · have hpx : cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
        (pre ⟨x, hx⟩) = x := (hpre ⟨x, hx⟩).2.2
    change sgpNormalSpec_PLN P eg (D.plane x) (D.ref ⟨x, hx⟩).1 q
    rw [hDpl x hx, hDref]
    exact slim_normal_of_rank_PLN P (ref ⟨x, hx⟩) (sgnf _) (cf _) (zsgnf _) (zcf _)
      (hspec (ref ⟨x, hx⟩)).2.2.2 (pre ⟨x, hx⟩) (hpre ⟨x, hx⟩).1 (hpre ⟨x, hx⟩).2.1 q
      (hq.trans hpx.symm)
  · have hpx := (hpre ⟨x, hx⟩).2.2
    rw [hDpl x hx]
    have hη : |(P.slim.centre (ref ⟨x, hx⟩).1
        ((Set.Finite.mem_toFinset _).mp (ref ⟨x, hx⟩).2)).coord (pre ⟨x, hx⟩)| ≤
        7 * 10 ^ 5 * Δ := by
      rw [mul_assoc]
      exact (hpre ⟨x, hx⟩).2.1
    exact slim_pp_point_GAF4 P.toLocalChartFamily P.zero hΔ hΛ hLΛ (ref ⟨x, hx⟩) (sgnf _) (cf _)
      (zsgnf _) (zcf _) (hpre ⟨x, hx⟩).1 hη q (hq.trans hpx.symm) a ha

/-- **The enhanced stage-`2` plane witness exists** (FC27 slim cloud with SGP05's table, review 60's
SGP04 / SGP06 / FC27 packages): for `Δ ≥ 1`, `β₂ ∈ (0, 1)` and (SP) there are the thresholds of
`fc27_slim_test_pp_C14_GAF4` (verbatim) such that every actual `LocalChartPacketsC14` satisfying
them carries a `SlimStagePlanes_PLN P Γ Σ e`. -/
theorem exists_slimStagePlanes_PLN {Δ β₂ Γ sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * sgpGraphBound)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        Nonempty (SlimStagePlanes_PLN P Γ sg eg) := by
  obtain ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, hrow⟩ := sgp05_row hΔ hβ₂ hβ₂1 heg heg1
  have hθ2 : θ ^ 2 / 10 ^ 6 < 1 / 100 := by
    have : θ ^ 2 < 1 := by nlinarith
    rw [div_lt_iff₀ (by norm_num)]
    linarith
  refine ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  exact slimStagePlanes_of_row_PLN P hΔ hΛ hLΛ he hT hσs (hσθ.trans hθ2) hΓ hΓ1 hsg hsgΓ hsgC heg
    hegΓ (hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      P.toLocalChartPacketsRVZ hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr)

end C14

end DifferentialGeometry.Geometry.Collapse
