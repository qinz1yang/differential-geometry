import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimCutoffOn
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeBCutoff
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZ
import DifferentialGeometry.Geometry.Fibration.ActualWholeSupportCount

/-!
# Whole support-list counts on the final boundary family (lane B-COUNT, G1–G2)

BCG03's input list (`state-BCG-8.md` §(8b-1), M1; blueprint BCG.0 `B:8700–8726`: "Add one to the
early whole-list and multiplicity constants"): the WHOLE lists of interior supports meeting a
reference ball of the boundary family are bounded by the SAME early numerical constant
`N_TCP = tcp01SupportBound` as on the closed family (lane C14-COUNTb), independent of `Δ`,
noncollapse, the member and the number of charts.

The family lives on the completed interior `(W°, d_ĝ)` — a COMPLETE, σ-compact carrier, not a
compact one. FC08's packing kernels (`fc08_count_of_sectional`,
`X81Sol.ncard_supports_meeting_ball_le_of_complete_scaled_ricci_bound`) need only completeness, and
the curvature buffer `sectional_buffer` (asserted at `p ∈ U₁`) is used only at the CENTRES of the
counted families, which lie in `U₁` (circle, slim: `centres_subset`; revised edges `edgeB`: their
packet domains `B(j, 1000Δρ(j)) ⊆ U₁`, `edgeB_domain`).

* Kernels on `ChartFamilyQOn`: `ChartFamilyQOn.active_count_of_buffer_BCNT` (reference ball
  `B(p, 10ρ(p))`), `ChartFamilyQOn.whole_count_of_buffer_BCNT` (reference ball
  `B(p, RΔ_cρ(p))`), for any finite family of centres in `U₁` with `Δ_cρ/3`-disjoint cores.
* The ACTUAL lists of a boundary family (`LocalPacketsOnB`) at a ball `B(p, r)`, two-sided by
  definition: `bdCircleList_BCNT` (circle cutoffs), `bdEdgeBList_BCNT` (the actual `edgeB` cutoffs
  `EdgeFamilyOn.cutoff_BAUGA`, lane BAUG-A), `bdSlimList_BCNT` (the actual slim cutoffs
  `SlimFamilyOn.cutoff_BCNT`); the zero list `zeroMeetingListOn_BCNT` of a regional zero family and
  `ncard_zeroMeetingListOn_le_one_BCNT` (FC09 from slow variation, port of
  `ncard_zeroMeetingList_le_one`).
* **G1** `tcp01_support_count_BFRZ`: on `LocalPacketsOnBFRZ`, at EVERY point `p`, the circle,
  `edgeB` and slim supports meeting `B(p, 10ρ(p))` number at most `N_TCP`; separately at most one
  zero support meets it.
* **G2** `egp02_whole_count_BFRZ` (`edgeB` and slim lists at `B(i, 20Δρ(i))`),
  `sgp01_whole_count_BFRZ` (slim list at `B(i, 950000Δρ(i)) = B(i, .95Lρ(i))`), both `≤ N_TCP`;
  `zero_list_le_one_BFRZ` (at most one zero support meets `B(p, ℓρ(p))`, `0 < ℓ ≤ 950000Δ`);
  `lpa06_pointwise_le_BFRZ` (LPA06's pointwise active count `≤ N_TCP`).

Parameters are the closed ones of `tcp01_support_count_C14`: `0 ≤ Λ`, `1 ≤ Δ`, `10⁶ΔΛ < 10⁻⁵`,
`4(10 + 4·10⁶Δ + Δ/3) ≤ Lmax`, and for the zero clause `e < 1/40`, `1600·10⁶Δ ≤ T`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ### FC08 on a regional family at any reference ball -/

namespace ChartFamilyQOn

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ} {U₁ U₂ : Set X}

/-- **FC08 at `B(p, 10ρ(p))` on a regional family** (twin of `active_count_of_buffer_LC87` on a
complete carrier): a finite family of centres in `U₁` with `Δ_cρ/3`-disjoint cores and supports in
`B̄(j, C₀Δ_cρ(j))`, the budget `Λ max(10, C₀Δ_c) ≤ 1/4` and the buffer at
`L = 4(10 + 2C₀Δ_c + Δ_c/3) ≤ Lmax` (used at the centres only): at most `V(4(10+2C₀+1/3))/V(1/3)`
supports meet `B(p, 10ρ(p))`. -/
theorem active_count_of_buffer_BCNT
    (L : ChartFamilyQOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax U₁ U₂)
    (hΛ : 0 ≤ Λ) {J : Set X} (hJ : J.Finite) (hJU : J ⊆ U₁) (S : X → Set X) {C₀ Δc : ℝ}
    (hΔ : 1 ≤ Δc) (hC₀ : 0 ≤ C₀) (hbudget : Λ * max 10 (C₀ * Δc) ≤ 1 / 4)
    (hL : 4 * (10 + 2 * (C₀ * Δc) + Δc / 3) ≤ Lmax)
    (hS : ∀ j ∈ J, S j ⊆ closedBall j (C₀ * Δc * ρ j))
    (hdisj : J.PairwiseDisjoint fun j => ball j (Δc * ρ j / 3)) (p : X) :
    ({j | j ∈ J ∧ (S j ∩ ball p (10 * ρ p)).Nonempty}.ncard : ℝ) ≤
      modelVolume (-(1 ^ 2)) 3 (4 * (10 + 2 * C₀ + 1 / 3)) /
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
  have hdim : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  set Q : ℝ := 4 * (10 + 2 * (C₀ * Δc) + Δc / 3) with hQdef
  have hQΔ : Δc ≤ Q := by rw [hQdef]; nlinarith
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  have h := fc08_count_of_sectional g hEnorm hJ.toFinset id S L.lipschitz_scale hρ hΔ hC₀
    (by rw [Real.coe_toNNReal _ hΛ]; exact hbudget) le_rfl hQΔ
    (fun j hj => hS j (hJ.mem_toFinset.mp hj))
    (by
      intro i hi j hj hij
      exact hdisj (hJ.mem_toFinset.mp hi) (hJ.mem_toFinset.mp hj) hij) p
    (fun j hj _ y hy => by
      have h := L.sectional_buffer Q hQpos hL j (hJU (hJ.mem_toFinset.mp hj)) y hy
      rw [← inv_pow] at h
      exact h)
  rw [hdim] at h
  have hset : {j | j ∈ J ∧ (S j ∩ ball p (10 * ρ p)).Nonempty} =
      {j | j ∈ hJ.toFinset ∧ (S j ∩ ball p (10 * ρ p)).Nonempty} := by
    ext j
    simp only [mem_ofPred_eq, Set.Finite.mem_toFinset]
  rw [hset]
  exact h

/-- **FC08 at any reference ball `B(p, RΔ_cρ(p))` on a regional family** (twin of
`LocalChartFamilyQ.whole_count_of_buffer_CNT` on a complete carrier; centres in `U₁`): at most
`V(4(R+2C+1/3))/V(1/3)` supports meet the WHOLE reference ball. -/
theorem whole_count_of_buffer_BCNT
    (L : ChartFamilyQOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax U₁ U₂)
    (hΛ : 0 ≤ Λ) {J : Set X} (hJ : J.Finite) (hJU : J ⊆ U₁) (S : X → Set X) {R C Δc : ℝ}
    (hΔc : 0 < Δc) (hR : 0 ≤ R) (hC : 0 ≤ C) (hbudget : Λ * max (R * Δc) (C * Δc) ≤ 1 / 4)
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
      intro j hj _ x hx v
      have hrj := hρ j
      have hsub : ball j (4 * (R + 2 * C + 1 / 3) * Δc * ρ j) ⊆ ball j (Q * ρ j) := by
        rw [hQdef]
      have hsec := L.sectional_buffer Q hQpos hL j (hJU (hJ.mem_toFinset.mp hj)) x (hsub hx)
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

end ChartFamilyQOn

/-! ### The zero list of a regional zero family -/

section ZeroOn

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X} {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ} {U₁ U₂ : Set X}

/-- The zero centres of a regional zero family whose LC31 cutoff support meets `B(p, ℓρ(p))`
(twin of `zeroMeetingList`). -/
def zeroMeetingListOn_BCNT (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (p : X) (ℓ : ℝ) : Set X :=
  {k | ∃ hk : k ∈ Z.centres, (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
    ((Z.zero k hk).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty}

/-- The closed support of an LC31 zero cutoff of a regional zero family lies in the physical band
`7R/40 < d(k,·) < 37R/40` once `e < 1/40` (twin of `zero_cutoff_tsupport_band`). -/
theorem zero_cutoff_tsupport_band_BCNT
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (he : e < 1 / 40) {k : X} (hk : k ∈ Z.centres) {x : X}
    (hx : x ∈ tsupport (fun y =>
      Calculus.annularCutoff Calculus.cutoffProfile ((Z.zero k hk).radial y))) :
    7 / 40 * (Z.zero k hk).radius < dist k x ∧ dist k x < 37 / 40 * (Z.zero k hk).radius := by
  have hspec := (Z.zero k hk).radial_spec.2.2.2.2.2.2.2.2.2.2.2
  have hts := hspec.choose_spec.2.2.2.2.2.1
  have hc : (Z.zero k hk).center = k := Z.zero_center k hk
  have hR := (Z.zero k hk).radius_pos
  obtain ⟨h1, h2⟩ := hts hx
  change 1 / 5 - e < (Z.zero k hk).radius⁻¹ * dist x (Z.zero k hk).center at h1
  change (Z.zero k hk).radius⁻¹ * dist x (Z.zero k hk).center < 9 / 10 + e at h2
  rw [hc, dist_comm] at h1 h2
  rw [lt_inv_mul_iff₀ hR] at h1
  rw [inv_mul_lt_iff₀ hR] at h2
  constructor <;> nlinarith

/-- **At most one zero support of a regional zero family meets `B(p, ℓρ(p))`** (FC09 from slow
variation; twin of `ncard_zeroMeetingList_le_one`). -/
theorem ncard_zeroMeetingListOn_le_one_BCNT
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) {Λ : NNReal}
    (hρL : LipschitzWith Λ ρ) (he : e < 1 / 40) (hT : 0 < T) (p : X) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hsmall : 2 * (ℓ / T) + 2 * (ℓ * Λ) ≤ 1 / 40) :
    (zeroMeetingListOn_BCNT Z p ℓ).ncard ≤ 1 := by
  have hshell : ∀ k (hk : k ∈ Z.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((Z.zero k hk).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty →
      ∀ x ∈ ball p (ℓ * ρ p), 3 / 20 * (Z.zero k hk).radius < dist k x ∧
        dist k x < 19 / 20 * (Z.zero k hk).radius := fun k hk hmeet =>
    zero_support_shell_of_lipschitz hρL (hρ k) hℓ hT (Z.radius_mem k hk).1 hsmall
      (fun x hx => zero_cutoff_tsupport_band_BCNT Z he hk hx) hmeet
  have hp : p ∈ ball p (ℓ * ρ p) := mem_ball_self (mul_pos hℓ (hρ p))
  have hfin : (zeroMeetingListOn_BCNT Z p ℓ).Finite :=
    Z.finite_centres.subset fun k hk => hk.choose
  refine (Set.ncard_le_one hfin).mpr ?_
  rintro k₁ ⟨hk₁, h₁⟩ k₂ ⟨hk₂, h₂⟩
  by_contra hne
  have hdisj := Z.disjoint k₁ hk₁ k₂ hk₂ hne
  have hp₁ : p ∈ ball k₁ (Z.zero k₁ hk₁).radius := by
    rw [mem_ball, dist_comm]
    linarith [(hshell k₁ hk₁ h₁ p hp).2, (Z.zero k₁ hk₁).radius_pos]
  have hp₂ : p ∈ ball k₂ (Z.zero k₂ hk₂).radius := by
    rw [mem_ball, dist_comm]
    linarith [(hshell k₂ hk₂ h₂ p hp).2, (Z.zero k₂ hk₂).radius_pos]
  exact Set.disjoint_left.mp hdisj hp₁ hp₂

end ZeroOn

/-! ### The actual lists of a boundary family -/

section Lists

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The circle centres of a boundary family whose ACTUAL closed cutoff support meets `B(p, r)`. -/
def bdCircleList_BCNT
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) (p : X) (r : ℝ) : Set X :=
  {j | j ∈ F.circle.centres ∧ (tsupport (F.circle.cutoff j) ∩ ball p r).Nonempty}

/-- The revised (active) edge centres of a boundary family whose ACTUAL closed `edgeB` cutoff
support (`EdgeFamilyOn.cutoff_BAUGA`) meets `B(p, r)`. -/
def bdEdgeBList_BCNT
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) (p : X) (r : ℝ) : Set X :=
  {j | j ∈ F.edgeB.centres ∧ (tsupport (F.edgeB.cutoff_BAUGA j) ∩ ball p r).Nonempty}

/-- The slim centres of a boundary family whose ACTUAL closed slim cutoff support
(`SlimFamilyOn.cutoff_BCNT`) meets `B(p, r)`. -/
def bdSlimList_BCNT
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) (p : X) (r : ℝ) : Set X :=
  {j | j ∈ F.slim.centres ∧ (tsupport (F.slim.cutoff_BCNT j) ∩ ball p r).Nonempty}

namespace LocalPacketsOnB

variable (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
  V vs U₁ U₂ Ue₁ Ue₂)

theorem bdCircleList_finite_BCNT (p : X) (r : ℝ) : (bdCircleList_BCNT F p r).Finite :=
  F.circle.finite_centres.subset fun _ hj => hj.1

theorem bdEdgeBList_finite_BCNT (p : X) (r : ℝ) : (bdEdgeBList_BCNT F p r).Finite :=
  F.edgeB.finite_centres.subset fun _ hj => hj.1

theorem bdSlimList_finite_BCNT (p : X) (r : ℝ) : (bdSlimList_BCNT F p r).Finite :=
  F.slim.finite_centres.subset fun _ hj => hj.1

/-- The closed support of an actual `edgeB` cutoff lies in `B̄(j, 100Δρ(j))` (it vanishes off the
physical chart ball). -/
theorem tsupport_edgeB_cutoff_subset_closedBall_BCNT (hΔ : 0 < Δ) (j : X) :
    tsupport (F.edgeB.cutoff_BAUGA j) ⊆ closedBall j (100 * Δ * ρ j) := by
  refine closure_minimal (fun x hx => ball_subset_closedBall ?_) isClosed_closedBall
  by_contra hxb
  exact hx (F.edgeB.cutoff_eq_zero_of_notMem_ball_BAUGA hΔ hxb)

/-- Every revised edge centre lies in `U₁` (it lies in its own packet domain). -/
theorem edgeB_centre_mem_U₁_BCNT (hΔ : 0 < Δ) {j : X} (hj : j ∈ F.edgeB.centres) : j ∈ U₁ :=
  F.edgeB_domain j hj (mem_ball_self (by have := hρ j; positivity))

/-- **The circle count at `B(p, 10ρ(p))`** on a boundary family. -/
theorem circle_count_BCNT (hΛ : 0 ≤ Λ) (hΛb : Λ * 200 ≤ 1 / 4)
    (hL : 4 * (10 + 2 * 200 + 1 / 3) ≤ Lmax) (p : X) :
    ((bdCircleList_BCNT F p (10 * ρ p)).ncard : ℝ) ≤
      modelVolume (-(1 ^ 2)) 3 (4 * (10 + 2 * 200 + 1 / 3)) /
        modelVolume (-(1 ^ 2)) 3 (1 / 3) := by
  refine F.toChartFamilyQOn.active_count_of_buffer_BCNT (Δc := 1) hΛ F.circle.finite_centres
    (fun _ hj => (F.circle.centres_subset hj).1) (fun j => tsupport (F.circle.cutoff j)) le_rfl
    (by norm_num) ?_ (by simpa using hL) ?_ ?_ p
  · rw [mul_one, max_eq_right (by norm_num)]
    exact hΛb
  · intro j hj
    rw [mul_one]
    exact (F.circle.tsupport_subset_ball j hj).trans ball_subset_closedBall
  · intro i hi j hj hij
    have h := F.circle.disjoint_centres hi hj hij
    simpa only [one_mul] using h

/-- **The slim count at `B(p, 10ρ(p))`** on a boundary family (constant independent of `Δ`). -/
theorem slim_count_BCNT (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛb : Λ * (2000000 * Δ) ≤ 1 / 4)
    (hL : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (p : X) :
    ((bdSlimList_BCNT F p (10 * ρ p)).ncard : ℝ) ≤
      modelVolume (-(1 ^ 2)) 3 (4 * (10 + 2 * 2000000 + 1 / 3)) /
        modelVolume (-(1 ^ 2)) 3 (1 / 3) := by
  refine F.toChartFamilyQOn.active_count_of_buffer_BCNT hΛ F.slim.finite_centres
    (fun _ hj => (F.slim.centres_subset hj).1) (fun j => tsupport (F.slim.cutoff_BCNT j)) hΔ
    (by norm_num) ?_ hL ?_ F.slim.disjoint_centres p
  · rw [max_eq_right (by nlinarith)]
    exact hΛb
  · intro j _
    refine (F.slim.tsupport_cutoff_subset_BCNT j).trans (closedBall_subset_closedBall ?_)
    have hr := hρ j
    nlinarith

/-- **The `edgeB` count at `B(p, 10ρ(p))`** on a boundary family (constant independent of `Δ`). -/
theorem edgeB_count_BCNT (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛb : Λ * (100 * Δ) ≤ 1 / 4)
    (hL : 4 * (10 + 2 * (100 * Δ) + Δ / 3) ≤ Lmax) (p : X) :
    ((bdEdgeBList_BCNT F p (10 * ρ p)).ncard : ℝ) ≤
      modelVolume (-(1 ^ 2)) 3 (4 * (10 + 2 * 100 + 1 / 3)) /
        modelVolume (-(1 ^ 2)) 3 (1 / 3) := by
  have hΔ0 : 0 < Δ := by linarith
  refine F.toChartFamilyQOn.active_count_of_buffer_BCNT hΛ F.edgeB.finite_centres
    (fun _ hj => F.edgeB_centre_mem_U₁_BCNT hΔ0 hj) (fun j => tsupport (F.edgeB.cutoff_BAUGA j))
    hΔ (by norm_num) ?_ hL (fun j _ => F.tsupport_edgeB_cutoff_subset_closedBall_BCNT hΔ0 j)
    F.edgeB.disjoint_centres p
  rw [max_eq_right (by nlinarith)]
  exact hΛb

/-- **The whole TCP01 list at every point** of a boundary family: circle, `edgeB` and slim supports
meeting `B(p, 10ρ(p))` number at most `N_TCP`. -/
theorem whole_support_count_BCNT (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (p : X) :
    (bdCircleList_BCNT F p (10 * ρ p)).ncard + (bdEdgeBList_BCNT F p (10 * ρ p)).ncard +
      (bdSlimList_BCNT F p (10 * ρ p)).ncard ≤ tcp01SupportBound := by
  apply nat_le_tcp01SupportBound_CNT
  have hΔΛ : 0 ≤ Δ * Λ := mul_nonneg (by linarith) hΛ
  have hc := F.circle_count_BCNT hΛ (by nlinarith) (by nlinarith) p
  have hs := F.slim_count_BCNT hΔ hΛ (by nlinarith) hLmax p
  have he := F.edgeB_count_BCNT hΔ hΛ (by nlinarith) (by nlinarith) p
  unfold tcp01SupportBoundReal
  push_cast
  linarith

/-- **EGP02's whole lists on a boundary family**: at every point `i`, the `edgeB` and slim supports
meeting `D_i = B(i, 20Δρ(i))` number at most `N_TCP`. -/
theorem egp02_whole_count_BCNT (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (i : X) :
    (bdEdgeBList_BCNT F i (20 * Δ * ρ i)).ncard + (bdSlimList_BCNT F i (20 * Δ * ρ i)).ncard ≤
      tcp01SupportBound := by
  apply nat_le_tcp01SupportBound_CNT
  have hΔ0 : 0 < Δ := by linarith
  have hΔΛ : 0 ≤ Δ * Λ := mul_nonneg hΔ0.le hΛ
  have hE := F.toChartFamilyQOn.whole_count_of_buffer_BCNT hΛ F.edgeB.finite_centres
    (fun _ hj => F.edgeB_centre_mem_U₁_BCNT hΔ0 hj) (fun j => tsupport (F.edgeB.cutoff_BAUGA j))
    (R := 20) (C := 100) hΔ0 (by norm_num) (by norm_num)
    (by rw [max_eq_right (by nlinarith)]; nlinarith) (by nlinarith)
    (fun j _ => F.tsupport_edgeB_cutoff_subset_closedBall_BCNT hΔ0 j) F.edgeB.disjoint_centres i
  have hS := F.toChartFamilyQOn.whole_count_of_buffer_BCNT hΛ F.slim.finite_centres
    (fun _ hj => (F.slim.centres_subset hj).1) (fun j => tsupport (F.slim.cutoff_BCNT j))
    (R := 20) (C := 910000) hΔ0 (by norm_num) (by norm_num)
    (by rw [max_eq_right (by nlinarith)]; nlinarith) (by nlinarith)
    (fun j _ => (F.slim.tsupport_cutoff_subset_BCNT j).trans
      (closedBall_subset_closedBall (by have := hρ j; nlinarith)))
    F.slim.disjoint_centres i
  have hE' := hE.trans (fc08Ratio_mono_CNT (r := 4 * (20 + 2 * 100 + 1 / 3))
    (t := 4 * (10 + 2 * 200 + 1 / 3)) (by norm_num) (by norm_num))
  have hS' := hS.trans (fc08Ratio_mono_CNT (r := 4 * (20 + 2 * 910000 + 1 / 3))
    (t := 4 * (10 + 2 * 2000000 + 1 / 3)) (by norm_num) (by norm_num))
  have h3 := fc08Ratio_nonneg_CNT (t := 4 * (10 + 2 * 100 + 1 / 3)) (by norm_num)
  unfold tcp01SupportBoundReal
  push_cast
  unfold bdEdgeBList_BCNT bdSlimList_BCNT
  linarith

/-- **SGP01's whole list on a boundary family**: at every point `i`, the slim supports meeting
`D_i = B(i, 950000Δρ(i)) = B(i, .95Lρ(i))` number at most `N_TCP`. -/
theorem sgp01_whole_count_BCNT (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (i : X) :
    (bdSlimList_BCNT F i (950000 * Δ * ρ i)).ncard ≤ tcp01SupportBound := by
  apply nat_le_tcp01SupportBound_CNT
  have hΔ0 : 0 < Δ := by linarith
  have hΔΛ : 0 ≤ Δ * Λ := mul_nonneg hΔ0.le hΛ
  have hS := F.toChartFamilyQOn.whole_count_of_buffer_BCNT hΛ F.slim.finite_centres
    (fun _ hj => (F.slim.centres_subset hj).1) (fun j => tsupport (F.slim.cutoff_BCNT j))
    (R := 950000) (C := 910000) hΔ0 (by norm_num) (by norm_num)
    (by rw [max_eq_left (by nlinarith)]; nlinarith) (by nlinarith)
    (fun j _ => (F.slim.tsupport_cutoff_subset_BCNT j).trans
      (closedBall_subset_closedBall (by have := hρ j; nlinarith)))
    F.slim.disjoint_centres i
  have hS' := hS.trans (fc08Ratio_mono_CNT (r := 4 * (950000 + 2 * 910000 + 1 / 3))
    (t := 4 * (10 + 2 * 2000000 + 1 / 3)) (by norm_num) (by norm_num))
  have h1 := fc08Ratio_nonneg_CNT (t := 4 * (10 + 2 * 200 + 1 / 3)) (by norm_num)
  have h3 := fc08Ratio_nonneg_CNT (t := 4 * (10 + 2 * 100 + 1 / 3)) (by norm_num)
  unfold tcp01SupportBoundReal
  unfold bdSlimList_BCNT
  linarith

/-- **LPA06's pointwise multiplicity on a boundary family is below `N_TCP`**: the circle, slim and
`edgeB` closed supports containing a point `x` are among the whole lists at `x`. -/
theorem lpa06_pointwise_le_BCNT (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (x : X) :
    (F.circle.centres ∩ {j | x ∈ tsupport (F.circle.cutoff j)}).ncard +
      (F.slim.centres ∩ {j | x ∈ tsupport (F.slim.cutoff_BCNT j)}).ncard +
      (F.edgeB.centres ∩ {j | x ∈ tsupport (F.edgeB.cutoff_BAUGA j)}).ncard ≤
        tcp01SupportBound := by
  have hx : x ∈ ball x (10 * ρ x) := mem_ball_self (by have := hρ x; positivity)
  have hc : (F.circle.centres ∩ {j | x ∈ tsupport (F.circle.cutoff j)}).ncard ≤
      (bdCircleList_BCNT F x (10 * ρ x)).ncard :=
    Set.ncard_le_ncard (fun j hj => ⟨hj.1, x, hj.2, hx⟩) (F.bdCircleList_finite_BCNT x _)
  have hs : (F.slim.centres ∩ {j | x ∈ tsupport (F.slim.cutoff_BCNT j)}).ncard ≤
      (bdSlimList_BCNT F x (10 * ρ x)).ncard :=
    Set.ncard_le_ncard (fun j hj => ⟨hj.1, x, hj.2, hx⟩) (F.bdSlimList_finite_BCNT x _)
  have he : (F.edgeB.centres ∩ {j | x ∈ tsupport (F.edgeB.cutoff_BAUGA j)}).ncard ≤
      (bdEdgeBList_BCNT F x (10 * ρ x)).ncard :=
    Set.ncard_le_ncard (fun j hj => ⟨hj.1, x, hj.2, hx⟩) (F.bdEdgeBList_finite_BCNT x _)
  have h := F.whole_support_count_BCNT hΛ hΔ hLΛ hLmax x
  omega

end LocalPacketsOnB

end Lists

/-! ### G1–G2 on the complete final boundary family -/

section BFRZ

attribute [local instance] LocalPacketsOn.instMetricN LocalPacketsOn.instChartedN
  LocalPacketsOn.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **At most one zero support of the final boundary family meets `B(p, ℓρ(p))`**, for every
`0 < ℓ ≤ 950000Δ` (covers the reference radii `10`, `20Δ`, `.95L` of TCP01, EGP02, SGP01). -/
theorem zero_list_le_one_BFRZ
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (p : X) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓΔ : ℓ ≤ 950000 * Δ) :
    (zeroMeetingListOn_BCNT F.zero p ℓ).ncard ≤ 1 := by
  have hTpos : 0 < T := by nlinarith
  refine ncard_zeroMeetingListOn_le_one_BCNT F.zero F.lipschitz_scale he hTpos p hℓ ?_
  rw [Real.coe_toNNReal _ hΛ]
  have h1 : ℓ / T ≤ 1 / 1000 := by
    rw [div_le_iff₀ hTpos]
    nlinarith
  have h2 : ℓ * Λ ≤ 1 / 100000 := by nlinarith
  linarith

/-- **G1: TCP01's whole support-list count on the complete final boundary family**
(`lem:fibration-first-comparison-list`, B:5250–5260, boundary setting of BCG.0): at EVERY point `p`
of `W°`, the circle, ACTIVE edge (`edgeB`) and slim centres whose ACTUAL closed cutoff supports meet
`D_p = B(p, 10ρ(p))` number at most the early numerical `N_TCP = tcp01SupportBound` (the closed
constant: independent of `Δ`, noncollapse, the member and the number of charts), and, SEPARATELY,
at most one zero support of the family meets `D_p`. -/
theorem tcp01_support_count_BFRZ
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (p : X) :
    (bdCircleList_BCNT F.toLocalPacketsOnB p (10 * ρ p)).ncard +
        (bdEdgeBList_BCNT F.toLocalPacketsOnB p (10 * ρ p)).ncard +
        (bdSlimList_BCNT F.toLocalPacketsOnB p (10 * ρ p)).ncard ≤ tcp01SupportBound ∧
      (zeroMeetingListOn_BCNT F.zero p 10).ncard ≤ 1 :=
  ⟨F.toLocalPacketsOnB.whole_support_count_BCNT hΛ hΔ hLΛ hLmax p,
    zero_list_le_one_BFRZ F hΛ hΔ hLΛ he hT p (by norm_num) (by linarith)⟩

/-- TCP01's boundary count in the blueprint's form: at every circle centre `i ∈ I₂`. -/
example
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) :
    ∀ i ∈ F.circle.centres,
      (bdCircleList_BCNT F.toLocalPacketsOnB i (10 * ρ i)).ncard +
          (bdEdgeBList_BCNT F.toLocalPacketsOnB i (10 * ρ i)).ncard +
          (bdSlimList_BCNT F.toLocalPacketsOnB i (10 * ρ i)).ncard ≤ tcp01SupportBound ∧
        (zeroMeetingListOn_BCNT F.zero i 10).ncard ≤ 1 :=
  fun i _ => tcp01_support_count_BFRZ F hΛ hΔ hLΛ hLmax he hT i

/-- **G2 (EGP02): the boundary edge-reference lists** on the complete final boundary family: at
every point `i`, the `edgeB` and slim supports meeting `D_i = B(i, 20Δρ(i))` number at most
`N_TCP`, and at most one zero support meets `D_i`. -/
theorem egp02_whole_count_BFRZ
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (i : X) :
    (bdEdgeBList_BCNT F.toLocalPacketsOnB i (20 * Δ * ρ i)).ncard +
        (bdSlimList_BCNT F.toLocalPacketsOnB i (20 * Δ * ρ i)).ncard ≤ tcp01SupportBound ∧
      (zeroMeetingListOn_BCNT F.zero i (20 * Δ)).ncard ≤ 1 :=
  ⟨F.toLocalPacketsOnB.egp02_whole_count_BCNT hΛ hΔ hLΛ hLmax i,
    zero_list_le_one_BFRZ F hΛ hΔ hLΛ he hT i (by linarith) (by linarith)⟩

/-- **G2 (SGP01): the boundary slim-reference list** on the complete final boundary family: at
every point `i`, the slim supports meeting `D_i = B(i, 950000Δρ(i)) = B(i, .95Lρ(i))` number at
most `N_TCP`, and at most one zero support meets `D_i`. -/
theorem sgp01_whole_count_BFRZ
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (i : X) :
    (bdSlimList_BCNT F.toLocalPacketsOnB i (950000 * Δ * ρ i)).ncard ≤ tcp01SupportBound ∧
      (zeroMeetingListOn_BCNT F.zero i (950000 * Δ)).ncard ≤ 1 :=
  ⟨F.toLocalPacketsOnB.sgp01_whole_count_BCNT hΛ hΔ hLΛ hLmax i,
    zero_list_le_one_BFRZ F hΛ hΔ hLΛ he hT i (by linarith) le_rfl⟩

/-- **G2 (LPA06) on the complete final boundary family**: the circle, slim and `edgeB` closed
supports containing any point `x` number at most `N_TCP`. -/
theorem lpa06_pointwise_le_BFRZ
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (x : X) :
    (F.circle.centres ∩ {j | x ∈ tsupport (F.circle.cutoff j)}).ncard +
      (F.slim.centres ∩ {j | x ∈ tsupport (F.slim.cutoff_BCNT j)}).ncard +
      (F.edgeB.centres ∩ {j | x ∈ tsupport (F.edgeB.cutoff_BAUGA j)}).ncard ≤
        tcp01SupportBound :=
  F.toLocalPacketsOnB.lpa06_pointwise_le_BCNT hΛ hΔ hLΛ hLmax x

end BFRZ

end DifferentialGeometry.Geometry.Collapse
