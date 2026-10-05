import DifferentialGeometry.Geometry.Fibration.ActualEdgeSupportLink
import DifferentialGeometry.Geometry.Metric.SupportComparisonLists

/-!
# EGP02: whole edge comparison lists on the actual families

Blueprint `master207B.tex`, EGP02 (`lem:fibration-edge-comparison-list`, B:4845–4895), on the actual
LC87 family with packet (iv) (`L : LocalChartFamilyE`) and the SAME LC80 zero family
`Z : ZeroModelFamily` as CGP01's `cgpGlobalMap L.toLocalChartFamily Z`. For an edge centre `i`,
`D_i = B(i, 20Δρ(i))`; `J_e`, `J_s` are the edge and slim centres whose ACTUAL closed supports
(`tsupport` of `L.edge.cutoff j`, `L.slim.cutoff j`) meet `D_i` (`egpEdgeList`, `egpSlimList`).

* `egp02_list_count`: `|J_e| + |J_s| ≤ N†` with the numerical `N† = egp02ListBound` (the sum of the
  two family multiplicity constants of LC87, independent of `Δ`, noncollapse and the number of
  charts): every listed centre has `i` within `2·10⁶Δρ(j)`.
* `zero_support_shell_of_lipschitz` (kernel, NEW: the tree's FC09/FC13 kernels need LC62's local
  comparison, which `ZeroModelFamily` does not store; here `ℓΛ` and `ℓ/T` small replace it) and
  `zero_supports_meeting_ball_shell`: at most one zero support of `Z` meets `B(p, ℓρ(p))`, the
  whole ball lies in its buffered shell `{3/20 < d(k,·)/R < 19/20}`, and the ORIGINAL radial
  function is smooth on an open neighbourhood of it.
* `egp02_row`: the row. Hypotheses `1 ≤ Δ`, `LΛ < 10⁻⁵` (`L = 10⁶Δ`), `T₀ ≥ 1600L`, the zero
  tolerance `e < 1/40`, and packet (iv)'s `μ, τ ≤ 1/100`.

Deviation: LC87's slim closed support radius is `.91L` (`fc18_slim_row`), not FC18's `901002Δ`;
the slim inclusion is therefore `D_i ⊆ B(j, .92Lρ(j))` (still inside the original smooth domain
`B(j, Lρ(j))`), instead of `.91L`. The edge lines are verbatim (support `14Δ ≤ 15Δ`).
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

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Kernel

/-- **Zero shell from slow variation alone.** A support `S` in the band `7R/40 < d(z,·) < 37R/40`
of a zero ball with `R ≥ Tρ(z)` meeting `B(p, ℓρ(p))` forces the whole ball into
`3R/20 < d(z,·) < 19R/20`, when `2ℓ/T + 2ℓΛ ≤ 1/40`. -/
theorem zero_support_shell_of_lipschitz {Y : Type*} [PseudoMetricSpace Y] {ρ : Y → ℝ}
    {Λ : NNReal} (hρ : LipschitzWith Λ ρ) {p z : Y} (hz : 0 < ρ z) {ℓ T R : ℝ} (hℓ : 0 < ℓ)
    (hT : 0 < T) (hR : T * ρ z ≤ R) (hsmall : 2 * (ℓ / T) + 2 * (ℓ * Λ) ≤ 1 / 40) {S : Set Y}
    (hS : ∀ x ∈ S, 7 / 40 * R < dist z x ∧ dist z x < 37 / 40 * R)
    (hmeet : (S ∩ ball p (ℓ * ρ p)).Nonempty) :
    ∀ x ∈ ball p (ℓ * ρ p), 3 / 20 * R < dist z x ∧ dist z x < 19 / 20 * R := by
  have hR0 : 0 < R := (mul_pos hT hz).trans_le hR
  have hΛ0 : (0 : ℝ) ≤ Λ := NNReal.coe_nonneg Λ
  obtain ⟨q, hqS, hqp⟩ := hmeet
  obtain ⟨hq1, hq2⟩ := hS q hqS
  rw [mem_ball] at hqp
  have ha0 : 0 ≤ ℓ / T := div_nonneg hℓ.le hT.le
  have hk0 : 0 ≤ ℓ * (Λ : ℝ) := mul_nonneg hℓ.le hΛ0
  have hℓz : ℓ * ρ z ≤ ℓ / T * R := by
    have h1 : ρ z ≤ R / T := by
      rw [le_div_iff₀ hT]
      linarith
    calc ℓ * ρ z ≤ ℓ * (R / T) := mul_le_mul_of_nonneg_left h1 hℓ.le
      _ = ℓ / T * R := by ring
  have hlip : ρ p ≤ ρ z + Λ * dist p z := by
    have h := hρ.dist_le_mul p z
    rw [Real.dist_eq] at h
    linarith [(abs_le.mp h).2]
  have hℓp : ℓ * ρ p ≤ ℓ / T * R + ℓ * Λ * dist p z := by
    have h := mul_le_mul_of_nonneg_left hlip hℓ.le
    have he : ℓ * (ρ z + Λ * dist p z) = ℓ * ρ z + ℓ * Λ * dist p z := by ring
    linarith
  have hD0 : 0 ≤ dist p z := dist_nonneg
  have hD : dist p z < ℓ * ρ p + 37 / 40 * R := by
    have ht := dist_triangle p q z
    rw [dist_comm p q, dist_comm q z] at ht
    linarith
  have ha1 : ℓ / T ≤ 1 / 80 := by linarith
  have hk1 : ℓ * (Λ : ℝ) ≤ 1 / 80 := by linarith
  have hkD : ℓ * Λ * dist p z ≤ 1 / 80 * dist p z := mul_le_mul_of_nonneg_right hk1 hD0
  have haR : ℓ / T * R ≤ 1 / 80 * R := mul_le_mul_of_nonneg_right ha1 hR0.le
  have hDR : dist p z < R := by linarith
  have hkR : ℓ * Λ * dist p z ≤ ℓ * Λ * R := mul_le_mul_of_nonneg_left hDR.le hk0
  have hsum : (2 * (ℓ / T) + 2 * (ℓ * Λ)) * R ≤ 1 / 40 * R :=
    mul_le_mul_of_nonneg_right hsmall hR0.le
  have hsum' : 2 * (ℓ / T * R) + 2 * (ℓ * Λ * R) ≤ 1 / 40 * R := by
    have he : (2 * (ℓ / T) + 2 * (ℓ * Λ)) * R = 2 * (ℓ / T * R) + 2 * (ℓ * Λ * R) := by ring
    linarith
  intro x hx
  rw [mem_ball] at hx
  have hqx : dist q x < 1 / 40 * R := by
    have ht := dist_triangle q p x
    rw [dist_comm p x] at ht
    linarith
  constructor
  · have ht := dist_triangle z x q
    rw [dist_comm x q] at ht
    linarith
  · have ht := dist_triangle z q x
    linarith

end Kernel

section Lists

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}
  {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc Lmax τ : ℝ}

/-- EGP02's edge list `J_e` at `i`: the edge centres whose ACTUAL closed support meets
`D_i = B(i, 20Δρ(i))`. -/
def egpEdgeList (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (i : X) : Set X :=
  {j | j ∈ L.edge.centres ∧ (tsupport (L.edge.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty}

/-- EGP02's slim list `J_s` at `i`. -/
def egpSlimList (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (i : X) : Set X :=
  {j | j ∈ L.slim.centres ∧ (tsupport (L.slim.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty}

/-- The edge family's multiplicity constant (LC87, numerical). -/
def egp02EdgeCount : ℝ :=
  modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3
      (4 * (1 + 2 * 2000000 + 1 / 3)) /
    modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3 (1 / 3)

/-- The slim family's multiplicity constant (LC87, numerical). -/
def egp02SlimCount : ℝ :=
  modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
    modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)

/-- EGP02's early numerical list bound `N†` (independent of `Δ`, noncollapse and the number of
charts). -/
def egp02ListBound : ℝ := egp02EdgeCount + egp02SlimCount

/-- **EGP02, the count**: `|J_e| + |J_s| ≤ N†`. A listed centre has its support within
`100Δρ(j)` (edge) or `.91·10⁶Δρ(j)` (slim) of `j`, so slow variation puts `i` in
`B(j, 2·10⁶Δρ(j))`, and the family multiplicity fields at `i` apply. -/
theorem egp02_list_count
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΛ : 0 ≤ Λ)
    (hΔ : 0 < Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (i : X) :
    ((egpEdgeList L i).ncard : ℝ) + (egpSlimList L i).ncard ≤ egp02ListBound := by
  have hρL : LipschitzWith (Real.toNNReal Λ) ρ := L.lipschitz_scale
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  have hΔΛ : 0 ≤ Δ * Λ := mul_nonneg hΔ.le hΛ
  -- a listed centre `j` with support radius `c Δ ρ(j)` has `i ∈ B(j, 2·10⁶Δρ(j))`
  have hnear : ∀ (j : X) (c : ℝ), 0 ≤ c → c ≤ 910000 →
      (closedBall j (c * Δ * ρ j) ∩ ball i (20 * Δ * ρ i)).Nonempty →
      i ∈ ball j (2000000 * (Δ * ρ j)) := by
    intro j c hc0 hc1 hm
    have hm' : (closedBall j ((c * Δ) * ρ j) ∩ ball i ((20 * Δ) * ρ i)).Nonempty := hm
    obtain ⟨h1, -, h3, -⟩ := support_meeting_sharp_bounds hρL (hρ i) (hρ j) (a := 20 * Δ)
      (c := c * Δ) (by positivity) (by positivity) (by rw [hc]; nlinarith)
      (by rw [hc]; nlinarith) hm'
    have hij : 99 / 100 * ρ i < ρ j := by
      have h := (lt_div_iff₀ (hρ i)).mp h1
      linarith
    have hpos := mul_pos hΔ (hρ j)
    have hcoef : 0 ≤ 20 * Δ + 101 / 100 * (c * Δ) := by positivity
    have hstep : (20 * Δ + 101 / 100 * (c * Δ)) * ρ i ≤
        (20 * Δ + 101 / 100 * (c * Δ)) * (100 / 99 * ρ j) :=
      mul_le_mul_of_nonneg_left (by linarith) hcoef
    have hb : (20 * Δ + 101 / 100 * (c * Δ)) * (100 / 99 * ρ j) ≤
        (20 * 100 / 99 + 101 / 99 * 910000) * (Δ * ρ j) := by
      have hcΔ : c * (Δ * ρ j) ≤ 910000 * (Δ * ρ j) := mul_le_mul_of_nonneg_right hc1 hpos.le
      nlinarith
    rw [mem_ball]
    nlinarith
  have hsubE : egpEdgeList L i ⊆ L.edge.centres ∩ {j | i ∈ ball j (2000000 * (Δ * ρ j))} := by
    rintro j ⟨hj, y, hy1, hy2⟩
    refine ⟨hj, hnear j 100 (by norm_num) (by norm_num) ⟨y, ?_, hy2⟩⟩
    exact L.edge.tsupport_cutoff_subset j hy1
  have hsubS : egpSlimList L i ⊆ L.slim.centres ∩ {j | i ∈ ball j (2000000 * (Δ * ρ j))} := by
    rintro j ⟨hj, y, hy1, hy2⟩
    refine ⟨hj, hnear j 910000 (by norm_num) le_rfl ⟨y, ?_, hy2⟩⟩
    exact (fc18_slim_row L hΔ hj).1 hy1
  have hE := Set.ncard_le_ncard hsubE (L.edge.finite_centres.inter_of_left _)
  have hS := Set.ncard_le_ncard hsubS (L.slim.finite_centres.inter_of_left _)
  have hE' : ((egpEdgeList L i).ncard : ℝ) ≤ egp02EdgeCount :=
    (Nat.cast_le.mpr hE).trans (L.edge.multiplicity i)
  have hS' : ((egpSlimList L i).ncard : ℝ) ≤ egp02SlimCount :=
    (Nat.cast_le.mpr hS).trans (L.slim.multiplicity i)
  unfold egp02ListBound
  linarith

end Lists

section ZeroSupports

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- The closed support of an LC31 zero cutoff `Φ ∘ radial` lies in the physical band
`7R/40 < d(k,·) < 37R/40` once `e < 1/40`. -/
theorem zero_cutoff_tsupport_band (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
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

/-- **FC09 + FC13 on the actual zero family, from slow variation** (EGP02's zero assertions with
comparison radius `ℓ`): at most one zero support of `Z` meets `B(p, ℓρ(p))`; for a meeting one the
whole ball lies in the buffered shell `3R/20 < d(k,·) < 19R/20` and the ORIGINAL radial function
is smooth on an open neighbourhood of the ball. -/
theorem zero_supports_meeting_ball_shell
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) {Λ : NNReal}
    (hρL : LipschitzWith Λ ρ) (he : e < 1 / 40) (hT : 0 < T) (p : X) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hsmall : 2 * (ℓ / T) + 2 * (ℓ * Λ) ≤ 1 / 40) :
    (∀ k₁ (hk₁ : k₁ ∈ Z.centres) k₂ (hk₂ : k₂ ∈ Z.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((Z.zero k₁ hk₁).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty →
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((Z.zero k₂ hk₂).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty → k₁ = k₂) ∧
    ∀ k (hk : k ∈ Z.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((Z.zero k hk).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty →
      (∀ x ∈ ball p (ℓ * ρ p), 3 / 20 * (Z.zero k hk).radius < dist k x ∧
        dist k x < 19 / 20 * (Z.zero k hk).radius) ∧
      ∃ O : Set X, IsOpen O ∧ ball p (ℓ * ρ p) ⊆ O ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (Z.zero k hk).radial O := by
  have hshell : ∀ k (hk : k ∈ Z.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((Z.zero k hk).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty →
      ∀ x ∈ ball p (ℓ * ρ p), 3 / 20 * (Z.zero k hk).radius < dist k x ∧
        dist k x < 19 / 20 * (Z.zero k hk).radius := fun k hk hmeet =>
    zero_support_shell_of_lipschitz hρL (hρ k) hℓ hT (Z.radius_mem k hk).1 hsmall
      (fun x hx => zero_cutoff_tsupport_band Z he hk hx) hmeet
  have hp : p ∈ ball p (ℓ * ρ p) := mem_ball_self (mul_pos hℓ (hρ p))
  refine ⟨fun k₁ hk₁ k₂ hk₂ h₁ h₂ => ?_, fun k hk hmeet => ⟨hshell k hk hmeet, ?_⟩⟩
  · by_contra hne
    have hdisj := Z.disjoint k₁ hk₁ k₂ hk₂ hne
    have hR₁ := (Z.zero k₁ hk₁).radius_pos
    have hR₂ := (Z.zero k₂ hk₂).radius_pos
    have hp₁ : p ∈ ball k₁ (Z.zero k₁ hk₁).radius := by
      rw [mem_ball, dist_comm]
      linarith [(hshell k₁ hk₁ h₁ p hp).2]
    have hp₂ : p ∈ ball k₂ (Z.zero k₂ hk₂).radius := by
      rw [mem_ball, dist_comm]
      linarith [(hshell k₂ hk₂ h₂ p hp).2]
    exact Set.disjoint_left.mp hdisj hp₁ hp₂
  · obtain ⟨O, hO, hsub, hsm⟩ := (Z.zero k hk).radial_spec.2.1
    have hc : (Z.zero k hk).center = k := Z.zero_center k hk
    have hR := (Z.zero k hk).radius_pos
    refine ⟨O, hO, fun x hx => hsub ⟨?_, ?_⟩, hsm⟩
    · change 3 / 40 ≤ (Z.zero k hk).radius⁻¹ * dist x (Z.zero k hk).center
      rw [hc, dist_comm, le_inv_mul_iff₀ hR]
      linarith [(hshell k hk hmeet x hx).1]
    · change (Z.zero k hk).radius⁻¹ * dist x (Z.zero k hk).center ≤ 11
      rw [hc, dist_comm, inv_mul_le_iff₀ hR]
      linarith [(hshell k hk hmeet x hx).2]

end ZeroSupports

section Row

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- **EGP02** (`lem:fibration-edge-comparison-list`) on `LocalChartFamilyE` and the zero family of
CGP01. For an edge centre `i` and `D_i = B(i, 20Δρ(i))`:
1. `|J_e| + |J_s| ≤ N†` (`egp02ListBound`, numerical);
2. `i ∈ J_e`;
3. (EL), edge line: `.99 < ρ(j)/ρ(i) < 1.01`, `d(i,j) < 36Δρ(i)`, `D_i ⊆ B(j, 57Δρ(j))`, and the
   original coordinate `η_j` is smooth on that open neighbourhood of `D_i`;
4. (EL), slim line: the ratio bounds, `d(i,j) < .92Lρ(i)`, `D_i ⊆ B(j, .92Lρ(j))` with `η_j` smooth
   there (`L = 10⁶Δ`);
5. the original edge enlargement `{|η_i| ≤ 8Δ, F/ρ ≤ 8Δ}` (in the chart ball) lies in `D_i`;
6. at most one zero support meets `D_i`; a meeting one has `D_i` in its buffered shell and its
   radial function smooth on an open neighbourhood of `D_i`. -/
theorem egp02_row
    (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) {i : X} (hi : i ∈ L.edge.centres) :
    ((egpEdgeList L.toLocalChartFamily i).ncard : ℝ) +
        (egpSlimList L.toLocalChartFamily i).ncard ≤ egp02ListBound ∧
      i ∈ egpEdgeList L.toLocalChartFamily i ∧
      (∀ j ∈ egpEdgeList L.toLocalChartFamily i,
        99 / 100 < ρ j / ρ i ∧ ρ j / ρ i < 101 / 100 ∧ dist i j < 36 * Δ * ρ i ∧
          ball i (20 * Δ * ρ i) ⊆ ball j (57 * Δ * ρ j) ∧
          ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (L.edge.coord j) (ball j (57 * Δ * ρ j))) ∧
      (∀ j (hj : j ∈ L.slim.centres),
        (tsupport (L.slim.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty →
        99 / 100 < ρ j / ρ i ∧ ρ j / ρ i < 101 / 100 ∧
          dist i j < 92 / 100 * (1000000 * Δ) * ρ i ∧
          ball i (20 * Δ * ρ i) ⊆ ball j (92 / 100 * (1000000 * Δ) * ρ j) ∧
          ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (L.slim.centre j hj).coord
            (ball j (92 / 100 * (1000000 * Δ) * ρ j))) ∧
      (∀ x ∈ ball i (100 * Δ * ρ i), |L.edge.coord i x| ≤ 8 * Δ →
        L.edge.smoothing x / ρ x ≤ 8 * Δ → x ∈ ball i (20 * Δ * ρ i)) ∧
      (∀ k₁ (hk₁ : k₁ ∈ Z.centres) k₂ (hk₂ : k₂ ∈ Z.centres),
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((Z.zero k₁ hk₁).radial y)) ∩ ball i (20 * Δ * ρ i)).Nonempty →
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((Z.zero k₂ hk₂).radial y)) ∩ ball i (20 * Δ * ρ i)).Nonempty → k₁ = k₂) ∧
      ∀ k (hk : k ∈ Z.centres),
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((Z.zero k hk).radial y)) ∩ ball i (20 * Δ * ρ i)).Nonempty →
        (∀ x ∈ ball i (20 * Δ * ρ i), 3 / 20 * (Z.zero k hk).radius < dist k x ∧
          dist k x < 19 / 20 * (Z.zero k hk).radius) ∧
        ∃ O : Set X, IsOpen O ∧ ball i (20 * Δ * ρ i) ⊆ O ∧
          ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (Z.zero k hk).radial O := by
  have hΔ0 : 0 < Δ := by linarith
  have hρL : LipschitzWith (Real.toNNReal Λ) ρ := L.lipschitz_scale
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  have hΔΛ0 : 0 ≤ Δ * Λ := mul_nonneg hΔ0.le hΛ
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  have hLΛ' : 1000000 * Δ * ((Real.toNNReal Λ : NNReal) : ℝ) < 1 / 100000 := by rwa [hc]
  have hT0 : 0 < T := by nlinarith
  refine ⟨egp02_list_count L.toLocalChartFamily hΛ hΔ0 hLΛ i, ⟨hi, i, ?_, ?_⟩,
    fun j hj => ?_, fun j hj hmeet => ?_, fun x hx hcx hFx => ?_, ?_⟩
  · -- `i ∈ J_e`: the cutoff is one at its centre
    refine subset_tsupport _ ?_
    rw [mem_support, L.edge.cutoff_eq_one hi (by rw [dist_self]; have := hρ i; positivity)]
    exact one_ne_zero
  · have := hρ i
    exact mem_ball_self (by positivity)
  · -- edge line
    obtain ⟨hjc, y, hy1, hy2⟩ := hj
    have h14 := (fc18_edge_rowE L hΛ hΔ0 hμ hτ hΔΛ hjc).1 hy1
    have hm : (closedBall j (15 * Δ * ρ j) ∩ ball i (20 * Δ * ρ i)).Nonempty := by
      refine ⟨y, closedBall_subset_closedBall ?_ h14, hy2⟩
      nlinarith [hρ j]
    obtain ⟨h1, h2, h3, h4⟩ := edge_comparison_list_edge_bounds hρL (hρ i) (hρ j) hΔ hLΛ' hm
    refine ⟨h1, h2, h3, h4, (L.edge.contMDiffOn_coord hjc).mono (ball_subset_ball ?_)⟩
    nlinarith [hρ j]
  · -- slim line
    obtain ⟨y, hy1, hy2⟩ := hmeet
    have hsl := fc18_slim_row L.toLocalChartFamily hΔ0 hj
    have hm : (closedBall j ((910000 * Δ) * ρ j) ∩ ball i ((20 * Δ) * ρ i)).Nonempty :=
      ⟨y, hsl.1 hy1, hy2⟩
    obtain ⟨h1, h2, h3, h4⟩ := support_meeting_sharp_bounds hρL (hρ i) (hρ j) (a := 20 * Δ)
      (c := 910000 * Δ) (by positivity) (by positivity) (by rw [hc]; nlinarith)
      (by rw [hc]; nlinarith) hm
    have hpi := mul_pos hΔ0 (hρ i)
    have hpj := mul_pos hΔ0 (hρ j)
    have hsub : ball i (20 * Δ * ρ i) ⊆ ball j (92 / 100 * (1000000 * Δ) * ρ j) :=
      (h4 (20 * Δ) (by positivity)).trans (ball_subset_ball (by nlinarith))
    refine ⟨h1, h2, h3.trans_le (by nlinarith), hsub, hsl.2.2.2.mono (ball_subset_ball ?_)⟩
    nlinarith
  · -- the original enlargement
    have hcut := L.edge.cutoff_eq_coordinateProfile_of_le hΔ0 hi hx hFx
    have hle : |L.edge.coord i x / Δ| ≤ 8 := by
      rw [abs_div, abs_of_pos hΔ0, div_le_iff₀ hΔ0]
      linarith
    rw [edgeCoordinateProfile_eq_one_sub_cfsRamp_abs,
      cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num) hle,
      sub_zero] at hcut
    have hsupp : x ∈ tsupport (L.edge.cutoff i) := by
      refine subset_tsupport _ ?_
      rw [mem_support, hcut]
      exact one_ne_zero
    have h14 := (fc18_edge_rowE L hΛ hΔ0 hμ hτ hΔΛ hi).1 hsupp
    rw [mem_closedBall] at h14
    rw [mem_ball]
    nlinarith [mul_pos hΔ0 (hρ i)]
  · -- the zero assertions (FC09/FC13 on the SAME zero family)
    have hsmall : 2 * (20 * Δ / T) + 2 * (20 * Δ * ((Real.toNNReal Λ : NNReal) : ℝ)) ≤ 1 / 40 := by
      rw [hc]
      have hq : 20 * Δ / T ≤ 1 / 80000000 := by
        rw [div_le_iff₀ hT0]
        nlinarith
      nlinarith
    exact zero_supports_meeting_ball_shell Z hρL he hT0 i (by positivity) hsmall

end Row

end DifferentialGeometry.Geometry.Collapse
