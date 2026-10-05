import DifferentialGeometry.Geometry.Fibration.ActualCloudPlaneCoherenceApplications
import DifferentialGeometry.Geometry.Metric.LargeCloudCoverBindings

/-!
# CFS11 on the three actual clouds of FC07 / FC27

Blueprint `master207B.tex`, CFS11 (`lem:fibration-cloud-large-cover`, B:2451) with the standing
hypotheses of B:2425–2449 ("the actual (CS) tests hold with quality `δ` and chosen affine
`k`-planes", (MCb), (DS)), bound on the final family `LocalChartPackets` to the actual clouds of
`ActualCloudPackets`. The (CS) tests and (DS) are the row's own hypotheses; boundedness of `S`, the
radius bounds and (MCb) (`B = 5/3`, buffer `128b`, `Σ ≤ 1/(640b)`) are discharged from the compact
carrier, CGP01's continuity (`cgp01_rowE`) and CFS07 (G1). `S ≠ ∅` is not needed (strengthening).

* `cfs11_of_scale_ratio_KA3`: CFS11 for any totally bounded cloud with radius bounds and (MCb);
  kernel `exists_large_cloud_cover_of_blueprint_smallness` (`D = 80B + 31 ≤ 165`).
* `cfs11_first_cloud` (FC04's radius, `k = 2`), `cfs11_edge_cloud`, `cfs11_slim_cloud` (FC26's
  selected radius for ANY selection of preimages, `k = 1`).
Conclusion: finite `T ⊆ S` with disjoint `B(x_i, r_i)`, the greedy cover (`|x − x_i| < 3r_i`,
`r(x) ≤ 2r_i`), `N_{8br}(S) ⊆ U_b ⊆ Ω_b`, and for the reference ball `B(x, 30b r(x))` of EVERY
`x ∈ S` (it contains `V_x = B(x, 8b r(x))` and is `V_i` at selected centres) the list `J` of
selected centres whose closed `80b r_j`-ball meets it: `|J| ≤ (1 + 2BDb)^k`, (LM) and (LP).
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

section Generic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **CFS11** for a totally bounded cloud `S ⊆ S̃` whose radius is bounded above and away from zero
on `S` and satisfies (MCb) with `B = 5/3` at the buffer `128b`: under (DS) and the (CS) tests on
`S`, the greedy selection `T ⊆ S` with CFS11's cover, tube inclusions, and (LM) (`D = 165`) / (LP)
for the reference ball `B(x, 30b r(x))` of every `x ∈ S` (it contains `V_x = B(x, 8b r(x))` and
equals `V_i` at selected centres). -/
theorem cfs11_of_scale_ratio_KA3 (S St : Set H) (hSSt : S ⊆ St) (hS : TotallyBounded S)
    (r : H → ℝ) {rmin R : ℝ} (hrmin : 0 < rmin) (hlower : ∀ x ∈ S, rmin ≤ r x)
    (hupper : ∀ x ∈ S, r x ≤ R) (k : ℕ) (plane : H → Submodule ℝ H)
    [∀ x, FiniteDimensional ℝ (plane x)] (hdim : ∀ x ∈ S, Module.finrank ℝ (plane x) = k)
    {bb δc : ℝ} (hbb : 1 ≤ bb)
    (hscale : ∀ x ∈ S, ∀ y ∈ S, dist y x ≤ 128 * bb * max (r y) (r x) →
      r x / (5 / 3) ≤ r y ∧ r y ≤ (5 / 3) * r x)
    (hδ : 0 < δc) (hds : δc ≤ min (1 / (8 * (5 / 3)))
      (min (1 / (4 * (128 * bb * (5 / 3) + 3))) (1 / (8 * (5 / 3 + 1)))))
    (hcloud : ∀ x ∈ S, hausdorffEDist (St ∩ ball x (r x / δc))
      ((AffineSubspace.mk' x (plane x) : Set H) ∩ ball x (r x / δc)) ≤
        ENNReal.ofReal (δc * r x)) :
    ∃ T : Set H, T ⊆ S ∧ T.Finite ∧ T.PairwiseDisjoint (fun i => ball i (r i)) ∧
      (∀ x ∈ S, ∃ i ∈ T, dist x i < 3 * r i ∧ r x ≤ 2 * r i) ∧
      (⋃ x ∈ S, ball x (8 * bb * r x)) ⊆ ⋃ i ∈ T, ball i (20 * bb * r i) ∧
      (⋃ i ∈ T, ball i (20 * bb * r i)) ⊆ ⋃ i ∈ T, ball i (30 * bb * r i) ∧
      ∀ x ∈ S,
        ((T ∩ {i | (closedBall i (80 * bb * r i) ∩ ball x (30 * bb * r x)).Nonempty}).ncard : ℝ) ≤
          (1 + 2 * (5 / 3) * 165 * bb) ^ k ∧
        ∀ i ∈ T, (closedBall i (80 * bb * r i) ∩ ball x (30 * bb * r x)).Nonempty →
          r x / (5 / 3) ≤ r i ∧ r i ≤ (5 / 3) * r x ∧ dist i x < 165 * bb * r x ∧
          ‖(plane x)ᗮ.starProjection (i - x)‖ ≤ δc * r x ∧
          ‖(plane i)ᗮ.starProjection - (plane x)ᗮ.starProjection‖ ≤ 6 * (5 / 3 + 1) * δc := by
  have hbpos : 0 < bb := zero_lt_one.trans_le hbb
  obtain ⟨T, hTS, hfin, hdisj, hcover, htube, hJ⟩ :=
    exists_large_cloud_cover_of_blueprint_smallness S St hSSt hS r (fun x : S => plane x) k
      (fun x => hdim x x.2) rmin R bb (5 / 3) δc hrmin hlower hupper hbb (by norm_num) hδ hds
      hscale (fun x => hcloud x x.2)
  refine ⟨T, hTS, hfin, hdisj, fun x hx => ?_, htube, ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, h1, h2⟩ := hcover x hx
    exact ⟨i, hi, h2, h1⟩
  · refine iUnion₂_mono fun i hi => ball_subset_ball ?_
    have hri : 0 < r i := hrmin.trans_le (hlower i (hTS hi))
    nlinarith
  · obtain ⟨hcard, hloc⟩ := hJ ⟨x, hx⟩
    have hrx : 0 < r x := hrmin.trans_le (hlower x hx)
    refine ⟨hcard.trans (pow_le_pow_left₀ (by positivity) ?_ k), fun i hi hmeet => ?_⟩
    · have : (80 : ℝ) * (5 / 3) + 31 ≤ 165 := by norm_num
      nlinarith
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hloc i ⟨hi, hmeet⟩
      refine ⟨h1, h2, h3.trans_le ?_, h4, h5⟩
      have : (80 : ℝ) * (5 / 3) + 31 ≤ 165 := by norm_num
      have h0 : 0 ≤ bb * r x := by positivity
      nlinarith

end Generic

/-- A positive continuous function on a compact space is bounded above and away from zero. -/
theorem exists_pos_bounds_KA3 {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] (f : Y → ℝ)
    (hf : Continuous f) (hpos : ∀ p, 0 < f p) : ∃ m M : ℝ, 0 < m ∧ ∀ p, m ≤ f p ∧ f p ≤ M := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact ⟨1, 1, one_pos, fun p => (IsEmpty.false p).elim⟩
  · obtain ⟨p₀, -, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
    obtain ⟨p₁, -, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf.continuousOn
    exact ⟨f p₀, f p₁, hpos p₀, fun p => ⟨hmin (mem_univ p), hmax (mem_univ p)⟩⟩

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN''_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN''_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC''_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- CGP01's continuity on `LocalChartPackets` and of every projection `π_t 𝓔⁰`. -/
theorem continuous_cgpProjMap_packets
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (he : e ≤ 1 / 8)
    (t : Finset (CGPTag P.toLocalChartFamily P.zero)) :
    Continuous (cgpGlobalMap P.toLocalChartFamily P.zero) ∧
      Continuous (cgpProjMap P.toLocalChartFamily P.zero t) := by
  have hc : Continuous (cgpGlobalMap P.toLocalChartFamily P.zero) :=
    (cgp01_rowE P.toLocalChartFamilyE P.zero hΛ hΔ hμ hτ hΔΛ he).continuous
  refine ⟨hc, ?_⟩
  classical
  exact (ContinuousLinearMap.continuous _).comp hc

/-- **CFS11 on FC07's first cloud** (`LocalChartPackets`): `S₁ = 𝓔⁰(A₁) ⊆ S̃₁ = 𝓔⁰(Ã₁)`, FC04's
exact radius `r₁ = Σ x_ρ` with `0 < Σ`, `128bΣ ≤ 1/5`, two-dimensional planes, (DS) with `B = 5/3`
and the (CS) tests on `S₁`. Boundedness, the radius bounds and (MCb) are discharged. -/
theorem cfs11_first_cloud
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (he : e ≤ 1 / 8) {bb sg δc : ℝ} (hbb : 1 ≤ bb) (hsg : 0 < sg)
    (hbsg : 128 * bb * sg ≤ 1 / 5)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hdim : ∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero ''
        fc04Set P.toLocalChartFamily P.zero 7, Module.finrank ℝ (plane x) = 2)
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
    ∃ T' : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      T' ⊆ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7 ∧
      T'.Finite ∧
      T'.PairwiseDisjoint
        (fun i => ball i (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg i)) ∧
      (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        ∃ i ∈ T', dist x i < 3 * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg i ∧
          scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x ≤
            2 * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg i) ∧
      (⋃ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        ball x (8 * bb * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x)) ⊆
        ⋃ i ∈ T', ball i (20 * bb * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg i) ∧
      (⋃ i ∈ T', ball i (20 * bb * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg i)) ⊆
        ⋃ i ∈ T', ball i (30 * bb * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg i) ∧
      ∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        ((T' ∩ {i | (closedBall i (80 * bb *
            scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg i) ∩
          ball x (30 * bb * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x)).Nonempty}
          ).ncard : ℝ) ≤ (1 + 2 * (5 / 3) * 165 * bb) ^ 2 ∧
        ∀ i ∈ T', (closedBall i (80 * bb *
            scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg i) ∩
          ball x (30 * bb * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x)).Nonempty →
          scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / (5 / 3) ≤
            scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg i ∧
          scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg i ≤
            (5 / 3) * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x ∧
          dist i x < 165 * bb * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x ∧
          ‖(plane x)ᗮ.starProjection (i - x)‖ ≤
            δc * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x ∧
          ‖(plane i)ᗮ.starProjection - (plane x)ᗮ.starProjection‖ ≤ 6 * (5 / 3 + 1) * δc := by
  obtain ⟨hc, -⟩ := continuous_cgpProjMap_packets P hΛ hΔ hμ hτ hΔΛ he ∅
  obtain ⟨m, M, hm, hmM⟩ := exists_pos_bounds_KA3 ρ P.contMDiff_scale.continuous hρ
  obtain ⟨hr, -, hmc⟩ := fc04_first_cloud_scale P.toLocalChartFamily P.zero hsg.le hbsg
  have hsub : cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7 ⊆
      range (cgpGlobalMap P.toLocalChartFamily P.zero) := image_subset_range _ _
  refine cfs11_of_scale_ratio_KA3 _ _ (image_mono (fc04Set_mono _ _ (by norm_num)))
    ((isCompact_range hc).totallyBounded.subset hsub) _ (R := sg * M) (mul_pos hsg hm) ?_ ?_ 2 plane
    hdim hbb
    (fun x hx y hy hd => hmc x (hsub hx) y (hsub hy) hd) hδ hds hcloud
  · rintro _ ⟨p, -, rfl⟩
    rw [hr]
    exact mul_le_mul_of_nonneg_left (hmM p).1 hsg.le
  · rintro _ ⟨p, -, rfl⟩
    rw [hr]
    exact mul_le_mul_of_nonneg_left (hmM p).2 hsg.le

/-- **CFS11 on FC27's edge cloud** (`LocalChartPackets`): `S₂ = π₂𝓔⁰(A₂) ⊆ S̃₂ = π₂𝓔⁰(Ã₂)`, FC26's
selected radius `Σρ ∘ select` for ANY selection of preimages over `S̃₂` (`0 < Σ`, `128bΣ ≤ 1/5`),
one-dimensional planes, (DS) with `B = 5/3` and the (CS) tests on `S₂`. Boundedness, the radius
bounds and (MCb) are discharged. -/
theorem cfs11_edge_cloud
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (he : e ≤ 1 / 8)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (select : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hselect : ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero) '' fc27EdgeSet P.toLocalChartFamily 8,
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) (select x) = x)
    {bb sg δc : ℝ} (hbb : 1 ≤ bb) (hsg : 0 < sg) (hbsg : 128 * bb * sg ≤ 1 / 5)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hdim : ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
        fc27EdgeSet P.toLocalChartFamily 7, Module.finrank ℝ (plane x) = 1)
    (hδ : 0 < δc) (hds : δc ≤ min (1 / (8 * (5 / 3)))
      (min (1 / (4 * (128 * bb * (5 / 3) + 3))) (1 / (8 * (5 / 3 + 1)))))
    (hcloud : ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero) '' fc27EdgeSet P.toLocalChartFamily 7,
      hausdorffEDist (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ2Tags P.toLocalChartFamily P.zero) '' fc27EdgeSet P.toLocalChartFamily 8 ∩
          ball x (sg * ρ (select x) / δc))
        ((AffineSubspace.mk' x (plane x) :
            Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
          ball x (sg * ρ (select x) / δc)) ≤ ENNReal.ofReal (δc * (sg * ρ (select x)))) :
    ∃ T' : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      T' ⊆ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
        fc27EdgeSet P.toLocalChartFamily 7 ∧
      T'.Finite ∧ T'.PairwiseDisjoint (fun i => ball i (sg * ρ (select i))) ∧
      (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
          fc27EdgeSet P.toLocalChartFamily 7,
        ∃ i ∈ T', dist x i < 3 * (sg * ρ (select i)) ∧
          sg * ρ (select x) ≤ 2 * (sg * ρ (select i))) ∧
      (⋃ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
          fc27EdgeSet P.toLocalChartFamily 7, ball x (8 * bb * (sg * ρ (select x)))) ⊆
        ⋃ i ∈ T', ball i (20 * bb * (sg * ρ (select i))) ∧
      (⋃ i ∈ T', ball i (20 * bb * (sg * ρ (select i)))) ⊆
        ⋃ i ∈ T', ball i (30 * bb * (sg * ρ (select i))) ∧
      ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
          fc27EdgeSet P.toLocalChartFamily 7,
        ((T' ∩ {i | (closedBall i (80 * bb * (sg * ρ (select i))) ∩
          ball x (30 * bb * (sg * ρ (select x)))).Nonempty}).ncard : ℝ) ≤
          (1 + 2 * (5 / 3) * 165 * bb) ^ 1 ∧
        ∀ i ∈ T', (closedBall i (80 * bb * (sg * ρ (select i))) ∩
          ball x (30 * bb * (sg * ρ (select x)))).Nonempty →
          sg * ρ (select x) / (5 / 3) ≤ sg * ρ (select i) ∧
          sg * ρ (select i) ≤ (5 / 3) * (sg * ρ (select x)) ∧
          dist i x < 165 * bb * (sg * ρ (select x)) ∧
          ‖(plane x)ᗮ.starProjection (i - x)‖ ≤ δc * (sg * ρ (select x)) ∧
          ‖(plane i)ᗮ.starProjection - (plane x)ᗮ.starProjection‖ ≤ 6 * (5 / 3 + 1) * δc := by
  have hΔ0 : 0 < Δ := by linarith
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  obtain ⟨-, hc⟩ := continuous_cgpProjMap_packets P hΛ hΔ0 hμ hτ hΔΛ he
    (cgpQ2Tags P.toLocalChartFamily P.zero)
  obtain ⟨m, M, hm, hmM⟩ := exists_pos_bounds_KA3 ρ P.contMDiff_scale.continuous hρ
  have hsub := image_mono (f := cgpProjMap P.toLocalChartFamily P.zero
    (cgpQ2Tags P.toLocalChartFamily P.zero)) (fc27EdgeSet_mono P.toLocalChartFamily hΔ0.le
      (by norm_num : (7 : ℝ) ≤ 8))
  have hmc := fc27_edge_cloud_mcb P.toLocalChartFamily P.zero hΔ hΛ hsmall select hselect hsg.le
    (by linarith : (0 : ℝ) ≤ 128 * bb) hbsg
  refine cfs11_of_scale_ratio_KA3 _ _ hsub
    ((isCompact_range hc).totallyBounded.subset (image_subset_range _ _))
    (fun x => sg * ρ (select x)) (R := sg * M) (mul_pos hsg hm)
    (fun x _ => mul_le_mul_of_nonneg_left (hmM _).1 hsg.le)
    (fun x _ => mul_le_mul_of_nonneg_left (hmM _).2 hsg.le) 1 plane hdim hbb
    (fun x hx y hy hd => hmc x (hsub hx) y (hsub hy) hd) hδ hds hcloud

/-- **CFS11 on FC27's slim cloud** (`LocalChartPackets`): `S₃ = π₃𝓔⁰(A₃) ⊆ S̃₃ = π₃𝓔⁰(Ã₃)`, FC26's
selected radius `Σρ ∘ select` for ANY selection of preimages over `S̃₃` (`0 < Σ`, `128bΣ ≤ 1/5`),
one-dimensional planes, (DS) with `B = 5/3` and the (CS) tests on `S₃`. Boundedness, the radius
bounds and (MCb) are discharged. -/
theorem cfs11_slim_cloud
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (he : e ≤ 1 / 8)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (select : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hselect : ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ3Tags P.toLocalChartFamily P.zero) '' fc27SlimSet P.toLocalChartFamily 8,
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) (select x) = x)
    {bb sg δc : ℝ} (hbb : 1 ≤ bb) (hsg : 0 < sg) (hbsg : 128 * bb * sg ≤ 1 / 5)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hdim : ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
        fc27SlimSet P.toLocalChartFamily 7, Module.finrank ℝ (plane x) = 1)
    (hδ : 0 < δc) (hds : δc ≤ min (1 / (8 * (5 / 3)))
      (min (1 / (4 * (128 * bb * (5 / 3) + 3))) (1 / (8 * (5 / 3 + 1)))))
    (hcloud : ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ3Tags P.toLocalChartFamily P.zero) '' fc27SlimSet P.toLocalChartFamily 7,
      hausdorffEDist (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero) '' fc27SlimSet P.toLocalChartFamily 8 ∩
          ball x (sg * ρ (select x) / δc))
        ((AffineSubspace.mk' x (plane x) :
            Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
          ball x (sg * ρ (select x) / δc)) ≤ ENNReal.ofReal (δc * (sg * ρ (select x)))) :
    ∃ T' : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      T' ⊆ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
        fc27SlimSet P.toLocalChartFamily 7 ∧
      T'.Finite ∧ T'.PairwiseDisjoint (fun i => ball i (sg * ρ (select i))) ∧
      (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
          fc27SlimSet P.toLocalChartFamily 7,
        ∃ i ∈ T', dist x i < 3 * (sg * ρ (select i)) ∧
          sg * ρ (select x) ≤ 2 * (sg * ρ (select i))) ∧
      (⋃ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
          fc27SlimSet P.toLocalChartFamily 7, ball x (8 * bb * (sg * ρ (select x)))) ⊆
        ⋃ i ∈ T', ball i (20 * bb * (sg * ρ (select i))) ∧
      (⋃ i ∈ T', ball i (20 * bb * (sg * ρ (select i)))) ⊆
        ⋃ i ∈ T', ball i (30 * bb * (sg * ρ (select i))) ∧
      ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
          fc27SlimSet P.toLocalChartFamily 7,
        ((T' ∩ {i | (closedBall i (80 * bb * (sg * ρ (select i))) ∩
          ball x (30 * bb * (sg * ρ (select x)))).Nonempty}).ncard : ℝ) ≤
          (1 + 2 * (5 / 3) * 165 * bb) ^ 1 ∧
        ∀ i ∈ T', (closedBall i (80 * bb * (sg * ρ (select i))) ∩
          ball x (30 * bb * (sg * ρ (select x)))).Nonempty →
          sg * ρ (select x) / (5 / 3) ≤ sg * ρ (select i) ∧
          sg * ρ (select i) ≤ (5 / 3) * (sg * ρ (select x)) ∧
          dist i x < 165 * bb * (sg * ρ (select x)) ∧
          ‖(plane x)ᗮ.starProjection (i - x)‖ ≤ δc * (sg * ρ (select x)) ∧
          ‖(plane i)ᗮ.starProjection - (plane x)ᗮ.starProjection‖ ≤ 6 * (5 / 3 + 1) * δc := by
  have hΔ0 : 0 < Δ := by linarith
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  obtain ⟨-, hc⟩ := continuous_cgpProjMap_packets P hΛ hΔ0 hμ hτ hΔΛ he
    (cgpQ3Tags P.toLocalChartFamily P.zero)
  obtain ⟨m, M, hm, hmM⟩ := exists_pos_bounds_KA3 ρ P.contMDiff_scale.continuous hρ
  have hsub := image_mono (f := cgpProjMap P.toLocalChartFamily P.zero
    (cgpQ3Tags P.toLocalChartFamily P.zero)) (fc27SlimSet_mono P.toLocalChartFamily hΔ0.le
      (by norm_num : (7 : ℝ) ≤ 8))
  have hmc := fc27_slim_cloud_mcb P.toLocalChartFamily P.zero hΔ hΛ hsmall select hselect hsg.le
    (by linarith : (0 : ℝ) ≤ 128 * bb) hbsg
  refine cfs11_of_scale_ratio_KA3 _ _ hsub
    ((isCompact_range hc).totallyBounded.subset (image_subset_range _ _))
    (fun x => sg * ρ (select x)) (R := sg * M) (mul_pos hsg hm)
    (fun x _ => mul_le_mul_of_nonneg_left (hmM _).1 hsg.le)
    (fun x _ => mul_le_mul_of_nonneg_left (hmM _).2 hsg.le) 1 plane hdim hbb
    (fun x hx y hy hd => hmc x (hsub hx) y (hsub hy) hd) hδ hds hcloud

end DifferentialGeometry.Geometry.Collapse
