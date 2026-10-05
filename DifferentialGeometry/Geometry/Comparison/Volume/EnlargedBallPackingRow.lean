import DifferentialGeometry.Geometry.Comparison.Volume.CompleteSupportMeetingMultiplicitySol
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

/-!
# FC08 on a complete Riemannian manifold: count and ratio clauses together

Blueprint `master207B.tex`, FC08 (`lem:fibration-ball-packing`, lines 448–490) and the paragraph
"A bound chosen before Δ" (lines 492–532).

* `fc08_ratio_mem_Icc` (metric step): a support `S ⊆ closedBall c (C ρ c)` meeting
  `ball p (R ρ p)`, with `ρ > 0` `Λ`-Lipschitz and `Λ max R C ≤ 1/4`, has `ρ c / ρ p ∈ [1/2, 2]`.
* `fc08_row`: the row on an actual complete Riemannian manifold (any dimension `n`, Ricci lower
  bound `(n - 1)·(-(κ/r_j)²)` on the WHOLE enlarged ball for the meeting indices): the number of
  supports meeting `D = B(p, R r)` is at most `V_κ(H)/V_κ(a)` (`H = 4(R + 2C + a)`, the tree's
  `modelVolume`) AND every meeting index has `r_j / r ∈ [1/2, 2]`. `fc08_row_three` is the literal
  three-dimensional form with `Ric ≥ -2 κ² r_j⁻² g`.
* `fc08_count_of_sectional`: the "bound chosen before Δ" paragraph bound to a sectional-curvature
  buffer (the form in which LC05 / LC09 deliver curvature): if every meeting centre has sectional
  curvature `≥ -(Q r_j)⁻²` on `B(p_j, Q r_j)` with `Q ≥ H = 4(10 + 2C₀Δ + Δ/3)` and `Q ≥ Δ`, then
  the number of supports meeting `B(p, 10 r)` is at most `V₁(4(10 + 2C₀ + 1/3)) / V₁(1/3)`, a
  constant independent of `Δ`. The suppliers are Codex X81 Sol's complete-manifold multiplicity
  theorems.

Strengthenings: `R, C ≥ 0` instead of `> 0`; any dimension; the Ricci bound only for the meeting
indices (exactly the row's `J`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open _root_.Metric

/-- FC08's ratio clause (metric step): a support meeting the reference ball has comparable scale. -/
theorem fc08_ratio_mem_Icc {X : Type*} [PseudoMetricSpace X] {ρ : X → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {R C : ℝ}
    (hbudget : (Λ : ℝ) * max R C ≤ 1 / 4) {c p : X} {S : Set X}
    (hS : S ⊆ closedBall c (C * ρ c)) (hmeet : (S ∩ ball p (R * ρ p)).Nonempty) :
    ρ c / ρ p ∈ Icc (1 / 2 : ℝ) 2 := by
  obtain ⟨y, hyS, hyD⟩ := hmeet
  have hyc : dist y c ≤ C * ρ c := mem_closedBall.mp (hS hyS)
  have hyp : dist y p < R * ρ p := mem_ball.mp hyD
  have hd : dist c p ≤ R * ρ p + C * ρ c := by
    have := dist_triangle c y p
    rw [dist_comm c y] at this
    linarith
  have hL : |ρ c - ρ p| ≤ (Λ : ℝ) * dist c p := by
    have := hρ.dist_le_mul c p
    rwa [Real.dist_eq] at this
  have hΛ0 : (0 : ℝ) ≤ Λ := NNReal.coe_nonneg Λ
  have hΛR : (Λ : ℝ) * R ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left (le_max_left R C) hΛ0).trans hbudget
  have hΛC : (Λ : ℝ) * C ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left (le_max_right R C) hΛ0).trans hbudget
  have hpc := hρpos c
  have hpp := hρpos p
  have hb : (Λ : ℝ) * dist c p ≤ (Λ * R) * ρ p + (Λ * C) * ρ c := by
    have := mul_le_mul_of_nonneg_left hd hΛ0
    linarith
  have h1 : (Λ * R) * ρ p ≤ 1 / 4 * ρ p := mul_le_mul_of_nonneg_right hΛR hpp.le
  have h2 : (Λ * C) * ρ c ≤ 1 / 4 * ρ c := mul_le_mul_of_nonneg_right hΛC hpc.le
  have habs := abs_le.mp (hL.trans hb)
  constructor
  · rw [le_div_iff₀ hpp]
    linarith [habs.1]
  · rw [div_le_iff₀ hpp]
    linarith [habs.2]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [SigmaCompactSpace M] [CompleteSpace M]

/-- FC08 (`lem:fibration-ball-packing`) on an actual complete Riemannian manifold: the count of
the supports meeting `D = B(p, R ρ(p))` is at most `V_κ(H) / V_κ(a)`, `H = 4(R + 2C + a)`, and every
meeting index has `ρ(p_j)/ρ(p) ∈ [1/2, 2]`. -/
theorem fc08_row (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {ι : Type*} (J : Finset ι) (c : ι → M) (S : ι → Set M) {ρ : M → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {R C a κ : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (ha : 0 < a) (hκ : 0 ≤ κ) (hbudget : (Λ : ℝ) * max R C ≤ 1 / 4)
    (hS : ∀ j ∈ J, S j ⊆ closedBall (c j) (C * ρ (c j)))
    (hdisj : (J : Set ι).PairwiseDisjoint fun j => ball (c j) (a * ρ (c j))) (p : M)
    (hRic : ∀ j ∈ J, (S j ∩ ball p (R * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (c j) (4 * (R + 2 * C + a) * ρ (c j)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((κ / ρ (c j)) ^ 2)))) :
    ({j | j ∈ J ∧ (S j ∩ ball p (R * ρ p)).Nonempty}.ncard : ℝ) ≤
        modelVolume (-(κ ^ 2)) (Module.finrank ℝ E) (4 * (R + 2 * C + a)) /
          modelVolume (-(κ ^ 2)) (Module.finrank ℝ E) a ∧
      ∀ j ∈ J, (S j ∩ ball p (R * ρ p)).Nonempty → ρ (c j) / ρ p ∈ Icc (1 / 2 : ℝ) 2 :=
  ⟨X81Sol.ncard_supports_meeting_ball_le_of_complete_ricci_bound g hEnorm J c S hρ hρpos hR hC
      ha hκ hbudget hS hdisj p hRic,
    fun j hj hmeet => fc08_ratio_mem_Icc hρ hρpos hbudget (hS j hj) hmeet⟩

/-- FC08 verbatim in dimension three: `Ric ≥ -2 κ² r_j⁻² g` on the whole enlarged ball. -/
theorem fc08_row_three (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hdim : Module.finrank ℝ E = 3)
    {ι : Type*} (J : Finset ι) (c : ι → M) (S : ι → Set M) {ρ : M → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {R C a κ : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (ha : 0 < a) (hκ : 0 ≤ κ) (hbudget : (Λ : ℝ) * max R C ≤ 1 / 4)
    (hS : ∀ j ∈ J, S j ⊆ closedBall (c j) (C * ρ (c j)))
    (hdisj : (J : Set ι).PairwiseDisjoint fun j => ball (c j) (a * ρ (c j))) (p : M)
    (hRic : ∀ j ∈ J, (S j ∩ ball p (R * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (c j) (4 * (R + 2 * C + a) * ρ (c j))) (-2 * κ ^ 2 * (ρ (c j))⁻¹ ^ 2)) :
    ({j | j ∈ J ∧ (S j ∩ ball p (R * ρ p)).Nonempty}.ncard : ℝ) ≤
        modelVolume (-(κ ^ 2)) 3 (4 * (R + 2 * C + a)) / modelVolume (-(κ ^ 2)) 3 a ∧
      ∀ j ∈ J, (S j ∩ ball p (R * ρ p)).Nonempty → ρ (c j) / ρ p ∈ Icc (1 / 2 : ℝ) 2 := by
  have h := fc08_row g hEnorm J c S hρ hρpos hR hC ha hκ hbudget hS hdisj p (by
    intro j hj hmeet
    have hK : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((κ / ρ (c j)) ^ 2)) =
        -2 * κ ^ 2 * (ρ (c j))⁻¹ ^ 2 := by
      rw [hdim, div_eq_mul_inv]
      push_cast
      ring
    rw [hK]
    exact hRic j hj hmeet)
  rwa [hdim] at h

/-- "A bound chosen before Δ" (FC08, lines 492–532) from a sectional-curvature buffer: a family with
cores `B(p_j, Δ r_j / 3)`, supports in `B̄(p_j, C₀ Δ r_j)`, and sectional curvature
`≥ -(Q r_j)⁻²` on `B(p_j, Q r_j)` for the meeting indices, where `Q ≥ 4(10 + 2C₀Δ + Δ/3)` and
`Q ≥ Δ`; then at most `V₁(4(10 + 2C₀ + 1/3)) / V₁(1/3)` supports meet `B(p, 10 r)`. -/
theorem fc08_count_of_sectional (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g)
    {ι : Type*} (J : Finset ι) (c : ι → M) (S : ι → Set M) {ρ : M → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {Δ C₀ Q : ℝ} (hΔ : 1 ≤ Δ) (hC₀ : 0 ≤ C₀)
    (hbudget : (Λ : ℝ) * max 10 (C₀ * Δ) ≤ 1 / 4)
    (hQH : 4 * (10 + 2 * (C₀ * Δ) + Δ / 3) ≤ Q) (hQΔ : Δ ≤ Q)
    (hS : ∀ j ∈ J, S j ⊆ closedBall (c j) (C₀ * Δ * ρ (c j)))
    (hdisj : (J : Set ι).PairwiseDisjoint fun j => ball (c j) (Δ * ρ (c j) / 3)) (p : M)
    (hsec : ∀ j ∈ J, (S j ∩ ball p (10 * ρ p)).Nonempty →
      ∀ y ∈ ball (c j) (Q * ρ (c j)), SectionalBoundedBelowAt (I := I) g y (-(Q * ρ (c j))⁻¹ ^ 2)) :
    ({j | j ∈ J ∧ (S j ∩ ball p (10 * ρ p)).Nonempty}.ncard : ℝ) ≤
      modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (4 * (10 + 2 * C₀ + 1 / 3)) /
        modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (1 / 3) := by
  refine X81Sol.complete_fixed_test_ball_scaled_card_le g hEnorm J c S hρ hρpos hΔ hC₀ hbudget hS
    hdisj p ?_
  intro j hj hmeet x hx v
  have hrj := hρpos (c j)
  have hΔpos : 0 < Δ := by linarith
  have hsub : ball (c j) (4 * (10 + 2 * (C₀ * Δ) + Δ / 3) * ρ (c j)) ⊆ ball (c j) (Q * ρ (c j)) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right hQH hrj.le)
  have hlow := ricci_lower_of_sectionalBoundedBelowAt g x (hsec j hj hmeet x (hsub hx)) v
  have hgv : 0 ≤ (g.inner x v v : ℝ) := by
    by_cases hv : v = 0
    · subst hv
      simp
    · exact (g.pos x v hv).le
  have hcmp : -(1 / (Δ * ρ (c j))) ^ 2 ≤ -(Q * ρ (c j))⁻¹ ^ 2 := by
    rw [one_div, neg_le_neg_iff]
    have hpos : 0 < Δ * ρ (c j) := mul_pos hΔpos hrj
    have hle : Δ * ρ (c j) ≤ Q * ρ (c j) := mul_le_mul_of_nonneg_right hQΔ hrj.le
    exact pow_le_pow_left₀ (inv_nonneg.mpr (mul_pos (hΔpos.trans_le hQΔ) hrj).le)
      (inv_anti₀ hpos hle) 2
  have hn : (0 : ℝ) ≤ ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * -((1 / (Δ * ρ (c j))) ^ 2) * (g.inner x v v : ℝ)
      ≤ ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * -(Q * ρ (c j))⁻¹ ^ 2 * (g.inner x v v : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hgv
        exact mul_le_mul_of_nonneg_left hcmp hn
    _ ≤ _ := hlow

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
