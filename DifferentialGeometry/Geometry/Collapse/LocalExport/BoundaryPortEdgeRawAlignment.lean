import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimRaw
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightEdge
import DifferentialGeometry.Geometry.Fibration.ActualEdgeRawAlignmentApplications

/-!
# EGP03 on the boundary family: fixed raw `edgeB` alignments (lane B-PORT-EDGE, G1)

GENERATED from `Geometry/Fibration/ActualEdgeRawAlignment.lean` (sections `Actual`, `Row`) and
`…/ActualEdgeRawAlignmentApplications.lean` by `build-logs/scratch/B-PORT-EDGE/gen_egp03.py`
(tables of `portedge.py`); do not edit by hand, re-run the script.

The closed EGP03 (ER) on the enriched boundary base family `L : LocalPacketsOnB X …` with the
ACTIVE edge family `L.edgeB` (raw coordinate `egpRaw_BAUGP` = real factor of the `edgeB` chart's
normalized splitting) and the regional slim family (`sgpRaw_BAUGP`, lane B-PORT-SLIM):

* substitution table as in `BoundaryPortEdgeComparisonList.lean`; parameter lists gain
  `γ δ εr e T V vs` and the regions `U₁ U₂ Ue₁ Ue₂` (`portedge.fix_param_lists`); every ported
  declaration `x` ↦ `x_BAUGP`;
* reused unchanged (generic): `exists_kleinerLott_of_base_eq_KC2`, `egp03_parameters_KC2`,
  `abs_increment_lt_of_affine_KC2`, `kl_reference_tests_SGP`;
* boundary twins in place of closed lemmas: `exists_sign_raw_alignment_real_complete_BCG1`
  (BCG-1: the complete σ-compact form of `exists_sign_raw_alignment_real_KC`, same statement),
  `LocalPacketsOnB.tsupport_edgeB_cutoff_subset_BAUGA` (FC18 (ii)),
  `SlimFamilyOn.tsupport_cutoff_subset_BCNT` (in place of `fc18_slim_row`);
* the ONE substantive difference: LPA01's curvature buffer of the boundary family is asserted at
  points of `U₁` only; the reference centre `i ∈ edgeB.centres` lies in `U₁` by `edgeB_domain`
  (`edgeB_centre_mem_U₁_BCNT`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Actual

universe u

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}
  {U₁ U₂ : Set X}

/-- The real factor of the edge chart's normalized `b`-splitting at a centre `j`. -/
def egpChartRaw_BAUGP (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) {j : X}
    (hj : j ∈ F.centres) (x : X) : ℝ :=
  let C := F.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  letI := C.instY
  (C.split.toFun x).fst

open Classical in
/-- The ORIGINAL raw real coordinate `u_j` of the actual edge chart at `j`: the real factor of the
chart's normalized `b`-splitting (zero off the centres). -/
def egpRaw_BAUGP (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (j x : X) : ℝ :=
  if hj : j ∈ F.centres then egpChartRaw_BAUGP F hj x else 0

theorem egpRaw_of_mem_BAUGP (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) {j : X}
    (hj : j ∈ F.centres) (x : X) : egpRaw_BAUGP F j x = egpChartRaw_BAUGP F hj x := by
  unfold egpRaw_BAUGP
  rw [dite_eq_left hj]

/-- The edge chart's splitting, based at `j` itself (the chart centre is `j`), as a normalized
rank-one `b`-splitting whose raw coordinate is `egpRaw_BAUGP`. -/
theorem exists_edge_split_KC2_BAUGP (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂)
    {j : X} (hj : j ∈ F.centres) :
    ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
      ∃ q : Y, ∃ f : @KleinerLottApprox X (WithLp 2 (ℝ × Y))
          (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j (WithLp.toLp 2 ((0 : ℝ), q)) b,
        ∀ x, (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
          f x).fst = egpRaw_BAUGP F j x := by
  have hcen := F.chart_center j hj
  have hraw : ∀ x, egpRaw_BAUGP F j x = egpChartRaw_BAUGP F hj x := egpRaw_of_mem_BAUGP F hj
  let C := F.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hcen' : C.center = j := hcen
  let _ := C.instY
  obtain ⟨f, hf⟩ := exists_kleinerLott_of_base_eq_KC2 hcen' C.split
  refine ⟨C.Y, C.instY, C.q, f, fun x => ?_⟩
  rw [hraw, hf]
  rfl

theorem egpRaw_center_BAUGP (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (j : X) :
    egpRaw_BAUGP F j j = 0 := by
  by_cases hj : j ∈ F.centres
  · obtain ⟨Y, mY, q, f, hf⟩ := exists_edge_split_KC2_BAUGP F hj
    rw [← hf j, @KleinerLottApprox.basepoint X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j
      _ b f]
    rfl
  · unfold egpRaw_BAUGP
    rw [dite_eq_right hj]

/-- EGP03: `a_i = 1`, `c_i = 0`. -/
theorem egp03_self_BAUGP (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (i x : X) :
    ρ i / ρ i * egpRaw_BAUGP F i x - 1 * egpRaw_BAUGP F i x - ρ i / ρ i * egpRaw_BAUGP F i i = 0 := by
  rw [div_self (hρ i).ne', egpRaw_center_BAUGP]
  ring

/-- **EGP03's side clauses for the edge reference splitting**: for `b ≤ min(1/(1000L), δ/100)`
(`L = 10⁶Δ`) the original edge splitting at `i` (raw coordinate `u_i = egpRaw_BAUGP`) has tested ball
containing `B(i, 100L)`, distortion at most `δ` there, and every target of radius `< 20L` lifts
into `B(i, 21L)` to error `< δ` (reference units). The slim ones are C14-SGP's
`sgp02_reference_tests`. -/
theorem egp03_reference_tests_BAUGP (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂)
    {δ : ℝ} (hΔ : 1 ≤ Δ) (hb : b ≤ min (1 / (1000 * (1000000 * Δ))) (δ / 100)) {i : X}
    (hi : i ∈ F.centres) :
    ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
      ∃ q : Y, ∃ f : @KleinerLottApprox X (WithLp 2 (ℝ × Y))
          (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i (WithLp.toLp 2 ((0 : ℝ), q)) b,
        let u := @KleinerLottApprox.toFun X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ _ _ _ f
        (∀ x, (u x).fst = egpRaw_BAUGP F i x) ∧ 100 * (1000000 * Δ) ≤ b⁻¹ ∧
          (∀ x ∈ ball i (100 * (1000000 * Δ) * ρ i), ∀ x' ∈ ball i (100 * (1000000 * Δ) * ρ i),
            |dist (u x) (u x') - (ρ i)⁻¹ * dist x x'| ≤ δ) ∧
          ∀ y, dist y (u i) < 20 * (1000000 * Δ) →
            ∃ x ∈ ball i (21 * (1000000 * Δ) * ρ i), dist y (u x) < δ := by
  obtain ⟨Y, mY, q, f, hf⟩ := exists_edge_split_KC2_BAUGP F hi
  have hri := hρ i
  obtain ⟨h1, h2, h3⟩ := @kl_reference_tests_SGP X Y
    (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i q b δ (1000000 * Δ) (by linarith) f hb
  have hball : ∀ r : ℝ, ∀ x, x ∈ ball i (r * ρ i) ↔
      x ∈ @ball X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).toPseudoMetricSpace i r := by
    intro r x
    change dist x i < r * ρ i ↔ (ρ i)⁻¹ * dist x i < r
    rw [inv_mul_lt_iff₀ hri, mul_comm]
  refine ⟨Y, mY, q, f, hf, h1, fun x hx x' hx' => h2 x ((hball _ x).mp hx) x'
    ((hball _ x').mp hx'), fun y hy => ?_⟩
  obtain ⟨x, hx, hxy⟩ := h3 y hy
  exact ⟨x, (hball _ x).mpr hx, hxy⟩

end Actual

section Row

/-- **EGP03 (ER) on the actual LC87 family with packet (iv).** Fix `Δ ≥ 1`, the exclusion
quality `β₂ < 10⁻⁶` and `E > 0`. There are a curvature radius `Lc` (asked of LPA01's buffer) and a
raw quality `η₀` such that for EVERY actual family `L` with `b, β₁ ≤ η₀`, `s < 10⁻⁶`, `Lc ≤ Lmax`,
`10⁶ΔΛ < 10⁻⁵` and packet (iv)'s `μ, τ ≤ 1/100`, every edge centre `i` and every listed
`j ∈ J_e ∪ J_s` have one sign `a_j` with `|s_j u_j − a_j u_i − s_j u_j(i)| < E` on
`B(i, 600Δρ(i))`, `s_j = ρ(j)/ρ(i)`. -/
theorem egp03_row_BAUGP {Δ β₂ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompleteSpace X] [SigmaCompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ) (U₁ U₂ Ue₁ Ue₂ : Set X)
        (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → ∀ i ∈ L.edgeB.centres,
          (∀ j ∈ egpEdgeList_BAUGP L i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (600 * Δ * ρ i),
              |ρ j / ρ i * egpRaw_BAUGP L.edgeB j x - a * egpRaw_BAUGP L.edgeB i x -
                ρ j / ρ i * egpRaw_BAUGP L.edgeB j i| < E) ∧
          (∀ j ∈ egpSlimList_BAUGP L i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (600 * Δ * ρ i),
              |ρ j / ρ i * sgpRaw_BAUGP L.slim j x - a * egpRaw_BAUGP L.edgeB i x -
                ρ j / ρ i * sgpRaw_BAUGP L.slim j i| < E) := by
  have hΔ0 : 0 < Δ := by linarith
  set H : ℝ := 600 * Δ with hH
  set t : ℝ := min (E / 100) (1 / (2 * (H + 1))) with ht
  obtain ⟨ht0, ht1, ha, ha2, htE⟩ := egp03_parameters_KC2 hΔ hE hH ht
  obtain ⟨σ, hσ, hσ1, hprop⟩ :=
    exists_sign_raw_alignment_real_complete_BCG1 ht0 ht1 hβ₂ (by linarith) ha ha2
  obtain ⟨η, hη, hal⟩ := hprop (1000000 * Δ) (by positivity)
  have hH1 : 0 < 1 / (2 * (H + 1)) := by positivity
  refine ⟨σ⁻¹, min η (min (σ / 3) (min (1 / (2 * (H + 1))) (1 / 10000000))), inv_pos.mpr hσ,
    lt_min hη (lt_min (by positivity) (lt_min hH1 (by norm_num))), ?_⟩
  intro X mX _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂ L hb hs hβ1 hLc hΛ hLΛ
    hμ hτ i hi
  have hri := hρ i
  have hbη : b ≤ η := hb.trans (min_le_left _ _)
  have hbσ : 3 * b ≤ σ := by
    have := hb.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hbH0 : b ≤ 1 / (2 * (H + 1)) :=
    hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbH : b * (2 * (H + 1)) ≤ 1 := by
    rw [le_div_iff₀ (by linarith)] at hbH0
    linarith
  have hb6 : b < 1 / 1000000 := by
    have := hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  have hβη : β 1 ≤ η := hβ1.trans (min_le_left _ _)
  -- the common inputs at the reference centre
  have hsec := L.sectional_buffer σ⁻¹ (inv_pos.mpr hσ) hLc i
    (L.edgeB_centre_mem_U₁_BCNT hΔ0 hi)
  have hno : ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) i 2 β₂ :=
    @not_hasEuclideanSplitting_two_of_isEdgePoint.{0, 0, 0} X
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) i Δ b s β₂ (L.edgeB.strong i hi) hb6 hs hβ₂1
  have hρL : LipschitzWith (Real.toNNReal Λ) ρ := L.lipschitz_scale
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  have hΔΛ0 : 0 ≤ Δ * Λ := mul_nonneg hΔ0.le hΛ
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  have hLΛ' : 1000000 * Δ * ((Real.toNNReal Λ : NNReal) : ℝ) < 1 / 100000 := by rwa [hc]
  obtain ⟨Bi, mBi, qi, ψ, hψx⟩ := exists_edge_split_KC2_BAUGP L.edgeB hi
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · -- `j ∈ J_e`
    obtain ⟨hjc, y, hy1, hy2⟩ := hj
    have h14 := (L.tsupport_edgeB_cutoff_subset_BAUGA hΛ hΔ0 hμ hτ hΔΛ hjc).1 hy1
    have hm : (closedBall j (15 * Δ * ρ j) ∩ ball i (20 * Δ * ρ i)).Nonempty := by
      refine ⟨y, closedBall_subset_closedBall ?_ h14, hy2⟩
      nlinarith [hρ j]
    obtain ⟨h1, h2, h3, -⟩ := edge_comparison_list_edge_bounds hρL hri (hρ j) hΔ hLΛ' hm
    have hd : dist i j ≤ 1000000 * Δ * ρ i := by nlinarith
    obtain ⟨Aj, mAj, qj, φ, hφx⟩ := exists_edge_split_KC2_BAUGP L.edgeB hjc
    obtain ⟨a, ha1, hlin⟩ := hal X g hmetric ρ hρ i j hsec hno (by linarith) (by linarith) hd
      Aj Bi qj qi hbη hbσ hbH φ ψ
    refine ⟨a, ha1, fun x hx => ?_⟩
    have hmain := hlin x hx
    rw [hψx, hφx, hφx] at hmain
    linarith
  · -- `j ∈ J_s`
    obtain ⟨hjc, y, hy1, hy2⟩ := hj
    have hsl1 : tsupport (L.slim.cutoff_BCNT j) ⊆ closedBall j ((910000 * Δ) * ρ j) := by
      rw [show (910000 * Δ) * ρ j = 91 / 100 * (10 ^ 6 * Δ) * ρ j by ring]
      exact L.slim.tsupport_cutoff_subset_BCNT j
    have hm : (closedBall j ((910000 * Δ) * ρ j) ∩ ball i ((20 * Δ) * ρ i)).Nonempty :=
      ⟨y, hsl1 hy1, hy2⟩
    obtain ⟨h1, h2, h3, -⟩ := support_meeting_sharp_bounds hρL hri (hρ j) (a := 20 * Δ)
      (c := 910000 * Δ) (by positivity) (by positivity) (by rw [hc]; nlinarith)
      (by rw [hc]; nlinarith) hm
    have hd : dist i j ≤ 1000000 * Δ * ρ i := by nlinarith
    let Sj := L.slim.centre j hjc
    let _ := Sj.instZ
    obtain ⟨a, ha1, hlin⟩ := hal X g hmetric ρ hρ i j hsec hno (by linarith) (by linarith) hd
      Sj.Z Bi Sj.z qi hβη hbσ hbH Sj.split ψ
    refine ⟨a, ha1, fun x hx => ?_⟩
    have hmain := hlin x hx
    rw [hψx] at hmain
    rw [sgpRaw_of_mem_BAUGP L.slim hjc, sgpRaw_of_mem_BAUGP L.slim hjc]
    exact lt_of_le_of_lt hmain (by linarith)

end Row


/-- **Consumer of `egp03_row_BAUGP`**: raw increments of every listed edge or slim chart agree with the
reference edge increments up to the sign `a_j`, with error `2E`, on the same thresholds. -/
theorem egp03_increment_BAUGP {Δ β₂ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompleteSpace X] [SigmaCompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ) (U₁ U₂ Ue₁ Ue₂ : Set X)
        (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → ∀ i ∈ L.edgeB.centres,
          (∀ j ∈ egpEdgeList_BAUGP L i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (600 * Δ * ρ i), ∀ y ∈ ball i (600 * Δ * ρ i),
              |ρ j / ρ i * (egpRaw_BAUGP L.edgeB j x - egpRaw_BAUGP L.edgeB j y) -
                a * (egpRaw_BAUGP L.edgeB i x - egpRaw_BAUGP L.edgeB i y)| < 2 * E) ∧
          (∀ j ∈ egpSlimList_BAUGP L i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (600 * Δ * ρ i), ∀ y ∈ ball i (600 * Δ * ρ i),
              |ρ j / ρ i * (sgpRaw_BAUGP L.slim j x - sgpRaw_BAUGP L.slim j y) -
                a * (egpRaw_BAUGP L.edgeB i x - egpRaw_BAUGP L.edgeB i y)| < 2 * E) := by
  obtain ⟨Lc, η₀, hLc, hη₀, h⟩ := egp03_row_BAUGP hΔ hβ₂ hβ₂1 hE
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂ L hb hs hβ1 hLmax hΛ hLΛ
    hμ hτ i hi
  obtain ⟨he, hsl⟩ := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂ L hb hs hβ1 hLmax
    hΛ hLΛ hμ hτ i hi
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨a, ha, hER⟩ := he j hj
    exact ⟨a, ha, fun x hx y hy => abs_increment_lt_of_affine_KC2 (hER x hx) (hER y hy)⟩
  · obtain ⟨a, ha, hER⟩ := hsl j hj
    exact ⟨a, ha, fun x hx y hy => abs_increment_lt_of_affine_KC2 (hER x hx) (hER y hy)⟩

/-- **Consumer of `egp03_self_BAUGP`**: for the reference chart itself, `a_i = 1` and the increments
agree exactly. -/
theorem egp03_self_increment_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}
    {U₁ U₂ : Set X} (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (i x y : X) :
    |ρ i / ρ i * (egpRaw_BAUGP F i x - egpRaw_BAUGP F i y) - 1 * (egpRaw_BAUGP F i x - egpRaw_BAUGP F i y)| = 0 := by
  have hx := egp03_self_BAUGP F i x
  have hy := egp03_self_BAUGP F i y
  have hsplit : ρ i / ρ i * (egpRaw_BAUGP F i x - egpRaw_BAUGP F i y) - 1 * (egpRaw_BAUGP F i x - egpRaw_BAUGP F i y) =
      (ρ i / ρ i * egpRaw_BAUGP F i x - 1 * egpRaw_BAUGP F i x - ρ i / ρ i * egpRaw_BAUGP F i i) -
        (ρ i / ρ i * egpRaw_BAUGP F i y - 1 * egpRaw_BAUGP F i y - ρ i / ρ i * egpRaw_BAUGP F i i) := by ring
  rw [hsplit, hx, hy, sub_zero, abs_zero]

end DifferentialGeometry.Geometry.Collapse
