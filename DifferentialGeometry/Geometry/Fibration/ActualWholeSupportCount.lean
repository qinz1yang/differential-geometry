import DifferentialGeometry.Geometry.Fibration.ActualAdjustmentChoice
import DifferentialGeometry.Geometry.Fibration.ActualSlimComparisonList
import DifferentialGeometry.Geometry.Fibration.ActualEdgeComparisonList
import DifferentialGeometry.Geometry.Comparison.Volume.CompleteSupportMeetingMultiplicitySol
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# Whole support-list counts with one early numerical constant `N_TCP` (lane C14-COUNT)

Review 57 §6.3 and review 53 §5: the early `N` of PBR01 (B:10078–10086, "Let `N` dominate LPA06,
SGP01, EGP02 and TCP01's WHOLE support-list counts") must bound the WHOLE lists of supports meeting
a reference ball, not a pointwise multiplicity. Blueprint TCP01
(`lem:fibration-first-comparison-list`, B:5250–5260): for a circle centre `p_i`,
`D_i = B(p_i, 10R_i)`, `R_i = ρ(p_i)`, the circle, edge and slim indices whose ACTUAL closed
supports meet `D_i` number at most an early numerical constant, independent of `Δ` and
noncollapse; at most one zero support meets `D_i` (kept separately).

* `tcp01SupportBound : ℕ` (`N_TCP`): `⌊V(4(10+2·200+⅓))/V(⅓) + V(4(10+4·10⁶+⅓))/V(⅓) +
  V(4(10+2·100+⅓))/V(⅓)⌋₊`, `V = modelVolume (-1) 3` (FC08's "bound chosen before Δ", B:492–532);
  `tcp01SupportBound_add_one_CNT : tcp01SupportBound + 1 = gafMultiplicity` (the `+1` is the zero
  slot).
* `tcp01CircleList`, `tcp01EdgeList`, `tcp01SlimList`: `J₂(i)`, `J_e(i)`, `J_s(i)` (closed supports
  meeting `B(i, 10ρ(i))`).
* `LocalChartFamilyQ.whole_count_of_buffer_CNT`: FC08 on the family at ANY reference ball
  `B(p, RΔc ρ(p))` from the curvature buffer `sectional_buffer` (kernel of every count below).
* `LocalChartFamilyQ.whole_support_count_CNT`: at EVERY point `p`,
  `|J₂(p)| + |J_e(p)| + |J_s(p)| ≤ N_TCP`.
* `tcp01_support_count_C14`: TCP01's whole-list count on `LocalChartPacketsC14` at every circle
  centre,
  with the zero clause (`≤ 1`) as a separate conjunct (vacuous for an empty circle family).
* `LocalChartFamilyQ.egp02_whole_count_CNT`, `LocalChartFamilyQ.sgp01_whole_count_CNT`: EGP02's and
  SGP01's whole lists (reference balls `B(i, 20Δρ(i))`, `B(i, .95·10⁶Δρ(i))`) are bounded by the
  SAME `N_TCP` (FC08 packing; the existing `egp02_list_count`/`sgpSlimList_ncard_le_ZERO` use the
  enlarged
  multiplicity fields, whose constants are not visibly below `N_TCP`).
* `LocalChartFamilyQ.lpa06_pointwise_le_CNT`: LPA06's pointwise active count at `p` is at most
  `N_TCP`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ### The early constant -/

/-- The model volume of curvature `-1` is monotone in the radius on `[0, ∞)`. -/
theorem modelVolume_neg_one_mono_CNT {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (n : ℕ) :
    modelVolume (-(1 ^ 2)) n r ≤ modelVolume (-(1 ^ 2)) n t := by
  unfold modelVolume
  apply intervalIntegral.integral_mono_interval le_rfl hr hrt
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    unfold modelArea
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (euclideanUnitBallVolume_pos n).le)
      (pow_nonneg (modelRadius_nonneg hx.1.le ⟨hx.1.le, by norm_num⟩) _)
  · exact (modelArea_continuous _ n).intervalIntegrable _ _

/-- The FC08 ratio `V(H)/V(1/3)` (curvature `-1`, dimension three) is monotone in `H ≥ 0`. -/
theorem fc08Ratio_mono_CNT {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) :
    modelVolume (-(1 ^ 2)) 3 r / modelVolume (-(1 ^ 2)) 3 (1 / 3) ≤
      modelVolume (-(1 ^ 2)) 3 t / modelVolume (-(1 ^ 2)) 3 (1 / 3) := by
  have hden : 0 < modelVolume (-(1 ^ 2)) 3 (1 / 3) :=
    modelVolume_pos (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
  exact div_le_div_of_nonneg_right (modelVolume_neg_one_mono_CNT hr hrt 3) hden.le

/-- The FC08 ratio `V(H)/V(1/3)` is nonnegative for `H ≥ 0`. -/
theorem fc08Ratio_nonneg_CNT {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ modelVolume (-(1 ^ 2)) 3 t / modelVolume (-(1 ^ 2)) 3 (1 / 3) := by
  have h := fc08Ratio_mono_CNT le_rfl ht
  simpa only [modelVolume_at_zero, zero_div] using h

/-- TCP01's early real bound: the circle, slim and edge FC08 ratios of LC87 (`fc07ActiveBound`
without the zero slot). -/
def tcp01SupportBoundReal : ℝ :=
  modelVolume (-(1 ^ 2)) 3 (4 * (10 + 2 * 200 + 1 / 3)) / modelVolume (-(1 ^ 2)) 3 (1 / 3) +
    modelVolume (-(1 ^ 2)) 3 (4 * (10 + 2 * 2000000 + 1 / 3)) /
      modelVolume (-(1 ^ 2)) 3 (1 / 3) +
    modelVolume (-(1 ^ 2)) 3 (4 * (10 + 2 * 100 + 1 / 3)) / modelVolume (-(1 ^ 2)) 3 (1 / 3)

/-- **`N_TCP`**: TCP01's early numerical whole-list bound (independent of `Δ`, noncollapse, the
member and the number of charts). -/
def tcp01SupportBound : ℕ := ⌊tcp01SupportBoundReal⌋₊

theorem tcp01SupportBoundReal_nonneg_CNT : 0 ≤ tcp01SupportBoundReal := by
  unfold tcp01SupportBoundReal
  have h1 := fc08Ratio_nonneg_CNT (t := 4 * (10 + 2 * 200 + 1 / 3)) (by norm_num)
  have h2 := fc08Ratio_nonneg_CNT (t := 4 * (10 + 2 * 2000000 + 1 / 3)) (by norm_num)
  have h3 := fc08Ratio_nonneg_CNT (t := 4 * (10 + 2 * 100 + 1 / 3)) (by norm_num)
  linarith

/-- FC07's active bound is `N_TCP`'s real bound plus TCP01's one zero slot. -/
theorem fc07ActiveBound_eq_CNT : fc07ActiveBound = tcp01SupportBoundReal + 1 := rfl

/-- **`N_TCP + 1 = gafMultiplicity`**: GAF01's multiplicity (the register's `N` source) is `N_TCP`
plus the zero slot. -/
theorem tcp01SupportBound_add_one_CNT : tcp01SupportBound + 1 = gafMultiplicity := by
  unfold gafMultiplicity tcp01SupportBound
  rw [fc07ActiveBound_eq_CNT, Nat.floor_add_one tcp01SupportBoundReal_nonneg_CNT]

/-- A natural number below a real bound is below its floor. -/
theorem nat_le_tcp01SupportBound_CNT {n : ℕ} (h : (n : ℝ) ≤ tcp01SupportBoundReal) :
    n ≤ tcp01SupportBound :=
  Nat.le_floor h

/-! ### The three lists -/

section Lists

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}

/-- TCP01's circle list `J₂(i)`: circle centres whose ACTUAL closed support meets `B(i, 10ρ(i))`. -/
def tcp01CircleList (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (i : X) : Set X :=
  {j | j ∈ L.circle.centres ∧ (tsupport (L.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}

/-- TCP01's edge list `J_e(i)`. -/
def tcp01EdgeList (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (i : X) : Set X :=
  {j | j ∈ L.edge.centres ∧ (tsupport (L.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}

/-- TCP01's slim list `J_s(i)`. -/
def tcp01SlimList (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (i : X) : Set X :=
  {j | j ∈ L.slim.centres ∧ (tsupport (L.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}

theorem tcp01CircleList_finite_CNT
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (i : X) :
    (tcp01CircleList L i).Finite :=
  L.circle.finite_centres.subset fun _ hj => hj.1

theorem tcp01EdgeList_finite_CNT
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (i : X) :
    (tcp01EdgeList L i).Finite :=
  L.edge.finite_centres.subset fun _ hj => hj.1

theorem tcp01SlimList_finite_CNT
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (i : X) :
    (tcp01SlimList L i).Finite :=
  L.slim.finite_centres.subset fun _ hj => hj.1

end Lists

/-! ### FC08 on the family at any reference ball -/

namespace LocalChartFamilyQ

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ}

/-- **FC08 on the family at any reference ball** `B(p, RΔc ρ(p))`: a finite family of centres with
`Δc ρ/3`-disjoint cores and supports in `B̄(j, CΔc ρ(j))`, the scale budget `Λ max(RΔc, CΔc) ≤ 1/4`
and the curvature buffer at `L = 4(R + 2C + 1/3)Δc ≤ Lmax`: at most `V(4(R+2C+1/3))/V(1/3)` supports
meet the reference ball (the WHOLE list; no pointwise multiplicity is used). -/
theorem whole_count_of_buffer_CNT
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (hΛ : 0 ≤ Λ) {J : Set X} (hJ : J.Finite) (S : X → Set X) {R C Δc : ℝ} (hΔc : 0 < Δc)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hbudget : Λ * max (R * Δc) (C * Δc) ≤ 1 / 4)
    (hL : 4 * (R + 2 * C + 1 / 3) * Δc ≤ Lmax)
    (hS : ∀ j ∈ J, S j ⊆ closedBall j (C * Δc * ρ j))
    (hdisj : J.PairwiseDisjoint fun j => ball j (Δc * ρ j / 3)) (p : X) :
    ({j | j ∈ J ∧ (S j ∩ ball p (R * Δc * ρ p)).Nonempty}.ncard : ℝ) ≤
      modelVolume (-(1 ^ 2)) 3 (4 * (R + 2 * C + 1 / 3)) /
        modelVolume (-(1 ^ 2)) 3 (1 / 3) := by
  let _ : RiemannianBundle (fun x : X => TangentSpace 𝓘(ℝ, E3) x) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric g
  have : IsRiemannianManifold 𝓘(ℝ, E3) X := by
    constructor
    intro a b
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]
  have hEnorm : IsMetricNorm (I := 𝓘(ℝ, E3)) g := isMetricNorm_of_riemannianBundle g
  have : CompleteSpace X := complete_of_compact
  have hdim : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  set Q : ℝ := 4 * (R + 2 * C + 1 / 3) * Δc with hQdef
  have hQΔ : Δc ≤ Q := by rw [hQdef]; nlinarith
  have hQpos : 0 < Q := hΔc.trans_le hQΔ
  have hcore : ∀ x : X, 1 / 3 * Δc * ρ x = Δc * ρ x / 3 := fun x => by ring
  have h := X81Sol.ncard_supports_meeting_ball_le_of_complete_scaled_ricci_bound g hEnorm
    hJ.toFinset id S L.lipschitz_scale hρ (R := R) (C := C) (a := 1 / 3) (q := 1) hΔc hR hC
    (by norm_num) zero_le_one (by rw [Real.coe_toNNReal _ hΛ]; exact hbudget)
    (fun j hj => hS j (hJ.mem_toFinset.mp hj))
    (by
      intro i hi j hj hij
      have h := hdisj (hJ.mem_toFinset.mp hi) (hJ.mem_toFinset.mp hj) hij
      simpa only [id, hcore] using h) p
    (by
      intro j _ _ x hx v
      have hrj := hρ j
      have hsub : ball j (4 * (R + 2 * C + 1 / 3) * Δc * ρ j) ⊆ ball j (Q * ρ j) := by
        rw [hQdef]
      have hsec := L.sectional_buffer Q hQpos hL j x (hsub hx)
      have hlow := ricci_lower_of_sectionalBoundedBelowAt g x hsec v
      have hgv : 0 ≤ (g.inner x v v : ℝ) := by
        by_cases hv : v = 0
        · subst hv
          simp
        · exact (g.pos x v hv).le
      have hcmp : -(1 / (Δc * ρ j)) ^ 2 ≤ -((Q * ρ j) ^ 2)⁻¹ := by
        rw [one_div, neg_le_neg_iff, ← inv_pow]
        have hpos : 0 < Δc * ρ j := mul_pos hΔc hrj
        have hle : Δc * ρ j ≤ Q * ρ j := mul_le_mul_of_nonneg_right hQΔ hrj.le
        exact pow_le_pow_left₀ (inv_nonneg.mpr (mul_pos hQpos hrj).le) (inv_anti₀ hpos hle) 2
      have hn : (0 : ℝ) ≤ ((Module.finrank ℝ E3 - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      calc ((Module.finrank ℝ E3 - 1 : ℕ) : ℝ) * -((1 / (Δc * ρ (id j))) ^ 2) * (g.inner x v v : ℝ)
          ≤ ((Module.finrank ℝ E3 - 1 : ℕ) : ℝ) * -((Q * ρ j) ^ 2)⁻¹ * (g.inner x v v : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hgv
            exact mul_le_mul_of_nonneg_left hcmp hn
        _ ≤ _ := hlow)
  rw [hdim] at h
  have hset : {j | j ∈ J ∧ (S j ∩ ball p (R * Δc * ρ p)).Nonempty} =
      {j | j ∈ hJ.toFinset ∧ (S j ∩ ball p (R * Δc * ρ p)).Nonempty} := by
    ext j
    simp only [mem_ofPred_eq, Set.Finite.mem_toFinset]
  rw [hset]
  exact h

/-- **The whole TCP01 list at every point** `p` (reference ball `B(p, 10ρ(p))`): the circle, edge
and slim centres whose ACTUAL closed supports meet it number at most `N_TCP` (LC87's three FC08
counts; parameters `1 ≤ Δ`, `10⁶ΔΛ < 10⁻⁵`, `4(10 + 4·10⁶Δ + Δ/3) ≤ Lmax`). -/
theorem whole_support_count_CNT
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (p : X) :
    (tcp01CircleList L.toLocalChartFamily p).ncard + (tcp01EdgeList L.toLocalChartFamily p).ncard +
      (tcp01SlimList L.toLocalChartFamily p).ncard ≤ tcp01SupportBound := by
  apply nat_le_tcp01SupportBound_CNT
  have hΔΛ : 0 ≤ Δ * Λ := mul_nonneg (by linarith) hΛ
  have hc := L.circle_active_count hΛ (by nlinarith) (by nlinarith) p
  have hs := L.slim_active_count hΔ hΛ (by nlinarith) hLmax p
  have he := L.edge_active_count hΔ hΛ (by nlinarith) (by nlinarith) p
  unfold tcp01SupportBoundReal
  push_cast
  unfold tcp01CircleList tcp01EdgeList tcp01SlimList
  linarith

/-- **EGP02's whole lists are bounded by `N_TCP`**: at every point `i`, the edge and slim centres
whose ACTUAL closed supports meet `D_i = B(i, 20Δρ(i))` (`egpEdgeList`, `egpSlimList`) number at
most `N_TCP` (FC08 at `R = 20`, `Δc = Δ`, `C = 100` resp. `910000`, then monotonicity of the FC08
ratio). -/
theorem egp02_whole_count_CNT
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (i : X) :
    (egpEdgeList L.toLocalChartFamily i).ncard + (egpSlimList L.toLocalChartFamily i).ncard ≤
      tcp01SupportBound := by
  apply nat_le_tcp01SupportBound_CNT
  have hΔ0 : 0 < Δ := by linarith
  have hΔΛ : 0 ≤ Δ * Λ := mul_nonneg hΔ0.le hΛ
  have hE := L.whole_count_of_buffer_CNT hΛ L.edge.finite_centres
    (fun j => tsupport (L.edge.cutoff j))
    (R := 20) (C := 100) hΔ0 (by norm_num) (by norm_num)
    (by rw [max_eq_right (by nlinarith)]; nlinarith) (by nlinarith)
    (fun j _ => L.edge.tsupport_cutoff_subset j) L.edge.disjoint_centres i
  have hS := L.whole_count_of_buffer_CNT hΛ L.slim.finite_centres
    (fun j => tsupport (L.slim.cutoff j))
    (R := 20) (C := 910000) hΔ0 (by norm_num) (by norm_num)
    (by rw [max_eq_right (by nlinarith)]; nlinarith) (by nlinarith)
    (fun j hj => (fc18_slim_row L.toLocalChartFamily hΔ0 hj).1) L.slim.disjoint_centres i
  have hE' := hE.trans (fc08Ratio_mono_CNT (r := 4 * (20 + 2 * 100 + 1 / 3))
    (t := 4 * (10 + 2 * 200 + 1 / 3)) (by norm_num) (by norm_num))
  have hS' := hS.trans (fc08Ratio_mono_CNT (r := 4 * (20 + 2 * 910000 + 1 / 3))
    (t := 4 * (10 + 2 * 2000000 + 1 / 3)) (by norm_num) (by norm_num))
  have h3 := fc08Ratio_nonneg_CNT (t := 4 * (10 + 2 * 100 + 1 / 3)) (by norm_num)
  unfold tcp01SupportBoundReal
  push_cast
  unfold egpEdgeList egpSlimList
  linarith

/-- **SGP01's whole list is bounded by `N_TCP`**: at every point `i`, the slim centres whose ACTUAL
closed supports meet `D_i = B(i, .95·10⁶Δρ(i))` (`sgpSlimList`) number at most `N_TCP` (FC08 at
`R = 950000`, `C = 910000`, `Δc = Δ`). -/
theorem sgp01_whole_count_CNT
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (i : X) :
    (sgpSlimList L.slim i).ncard ≤ tcp01SupportBound := by
  apply nat_le_tcp01SupportBound_CNT
  have hΔ0 : 0 < Δ := by linarith
  have hΔΛ : 0 ≤ Δ * Λ := mul_nonneg hΔ0.le hΛ
  have hS := L.whole_count_of_buffer_CNT hΛ L.slim.finite_centres
    (fun j => tsupport (L.slim.cutoff j))
    (R := 950000) (C := 910000) hΔ0 (by norm_num) (by norm_num)
    (by rw [max_eq_left (by nlinarith)]; nlinarith) (by nlinarith)
    (fun j hj => (fc18_slim_row L.toLocalChartFamily hΔ0 hj).1) L.slim.disjoint_centres i
  have hS' := hS.trans (fc08Ratio_mono_CNT (r := 4 * (950000 + 2 * 910000 + 1 / 3))
    (t := 4 * (10 + 2 * 2000000 + 1 / 3)) (by norm_num) (by norm_num))
  have hset : sgpSlimList L.slim i = {j | j ∈ L.slim.centres ∧
      (tsupport (L.slim.cutoff j) ∩ ball i (950000 * Δ * ρ i)).Nonempty} := by
    unfold sgpSlimList
    rw [show 95 / 100 * (1000000 * Δ) * ρ i = 950000 * Δ * ρ i by ring]
  have h1 := fc08Ratio_nonneg_CNT (t := 4 * (10 + 2 * 200 + 1 / 3)) (by norm_num)
  have h3 := fc08Ratio_nonneg_CNT (t := 4 * (10 + 2 * 100 + 1 / 3)) (by norm_num)
  rw [hset]
  unfold tcp01SupportBoundReal
  linarith

/-- **LPA06's pointwise multiplicity is below `N_TCP`**: the circle, slim and edge closed supports
containing a point `x` are among the whole lists at `x` (`x ∈ B(x, 10ρ(x))`). -/
theorem lpa06_pointwise_le_CNT
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (x : X) :
    (L.circle.centres ∩ {j | x ∈ tsupport (L.circle.cutoff j)}).ncard +
      (L.slim.centres ∩ {j | x ∈ tsupport (L.slim.cutoff j)}).ncard +
      (L.edge.centres ∩ {j | x ∈ tsupport (L.edge.cutoff j)}).ncard ≤ tcp01SupportBound := by
  have hx : x ∈ ball x (10 * ρ x) := mem_ball_self (by have := hρ x; positivity)
  have hc : (L.circle.centres ∩ {j | x ∈ tsupport (L.circle.cutoff j)}).ncard ≤
      (tcp01CircleList L.toLocalChartFamily x).ncard :=
    Set.ncard_le_ncard (fun j hj => ⟨hj.1, x, hj.2, hx⟩)
      (tcp01CircleList_finite_CNT L.toLocalChartFamily x)
  have hs : (L.slim.centres ∩ {j | x ∈ tsupport (L.slim.cutoff j)}).ncard ≤
      (tcp01SlimList L.toLocalChartFamily x).ncard :=
    Set.ncard_le_ncard (fun j hj => ⟨hj.1, x, hj.2, hx⟩)
      (tcp01SlimList_finite_CNT L.toLocalChartFamily x)
  have he : (L.edge.centres ∩ {j | x ∈ tsupport (L.edge.cutoff j)}).ncard ≤
      (tcp01EdgeList L.toLocalChartFamily x).ncard :=
    Set.ncard_le_ncard (fun j hj => ⟨hj.1, x, hj.2, hx⟩)
      (tcp01EdgeList_finite_CNT L.toLocalChartFamily x)
  have h := L.whole_support_count_CNT hΛ hΔ hLΛ hLmax x
  omega

end LocalChartFamilyQ

/-! ### TCP01 on the final family -/

section C14

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_CNT
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_CNT
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_CNT
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- At most one zero support of the final family meets `B(p, 10ρ(p))` (FC09/FC13 from slow
variation, `e < 1/40`, `T ≥ 1600·10⁶Δ`). -/
theorem zeroMeetingList_ncard_le_one_C14_CNT
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (p : X) :
    (zeroMeetingList P.zero p 10).ncard ≤ 1 := by
  have hTpos : 0 < T := by nlinarith
  refine ncard_zeroMeetingList_le_one P.zero P.lipschitz_scale he hTpos p (by norm_num) ?_
  rw [Real.coe_toNNReal _ hΛ]
  have h1 : 10 / T ≤ 1 / 100000000 := by
    rw [div_le_iff₀ hTpos]
    nlinarith
  have h2 : Λ ≤ 1 / 100000000000 := by nlinarith
  linarith

/-- **TCP01's whole support-list count** (`lem:fibration-first-comparison-list`, B:5250–5260; review
57 §6.3) on the final family `LocalChartPacketsC14`, at `D_i = B(i, 10R_i)`, `R_i = ρ(i)`: the
circle,
edge and slim centres whose ACTUAL closed supports meet `D_i` number at most the early numerical
`N_TCP = tcp01SupportBound` (independent of `Δ`, noncollapse, the member and the number of charts),
and, SEPARATELY, at most one zero support meets `D_i`. Strengthening: stated at EVERY point `i`; the
blueprint's circle-centre form (`i ∈ I₂`, vacuous for an empty circle family) is the `example`
below. -/
theorem tcp01_support_count_C14
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (i : X) :
    (tcp01CircleList P.toLocalChartFamily i).ncard + (tcp01EdgeList P.toLocalChartFamily i).ncard +
        (tcp01SlimList P.toLocalChartFamily i).ncard ≤ tcp01SupportBound ∧
      (zeroMeetingList P.zero i 10).ncard ≤ 1 :=
  ⟨P.toLocalChartFamilyQ.whole_support_count_CNT hΛ hΔ hLΛ hLmax i,
    zeroMeetingList_ncard_le_one_C14_CNT P hΛ hΔ hLΛ he hT i⟩

/-- TCP01's count in the blueprint's form: at every circle centre `i ∈ I₂`. -/
example
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) :
    ∀ i ∈ P.circle.centres,
      (tcp01CircleList P.toLocalChartFamily i).ncard +
          (tcp01EdgeList P.toLocalChartFamily i).ncard +
          (tcp01SlimList P.toLocalChartFamily i).ncard ≤ tcp01SupportBound ∧
        (zeroMeetingList P.zero i 10).ncard ≤ 1 :=
  fun i _ => tcp01_support_count_C14 P hΛ hΔ hLΛ hLmax he hT i

end C14

end DifferentialGeometry.Geometry.Collapse
