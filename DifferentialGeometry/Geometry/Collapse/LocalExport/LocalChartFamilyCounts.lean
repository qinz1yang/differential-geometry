import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyQuantitativeApplications
import DifferentialGeometry.Geometry.Comparison.Volume.EnlargedBallPackingRow

/-!
# LC87: the enlarged-ball active-list counts (review-42 packet (iii))

Review 42 §6.5: FC07 / FC23 / FC24 use the number of ACTIVE supports meeting a given comparison ball,
not only the pointwise multiplicity. With the curvature buffer of `LocalChartFamilyQ`
(`sec ≥ -(Lρ(p))⁻²` on `B(p, Lρ(p))` for `L ≤ Lmax`) and the scale-Lipschitz bound, FC08's
"bound chosen before Δ" (`fc08_count_of_sectional`) gives, for every point `p`,
* `LocalChartFamilyQ.circle_active_count`: at most `V₁(4(10 + 400 + 1/3)) / V₁(1/3)` circle
  supports meet `B(p, 10ρ(p))`;
* `LocalChartFamilyQ.slim_active_count`: at most `V₁(4(10 + 4·10⁶ + 1/3)) / V₁(1/3)` slim supports;
* `LocalChartFamilyQ.edge_active_count`: at most `V₁(4(10 + 200 + 1/3)) / V₁(1/3)` edge supports;
all numerical (independent of `Δ`, `w'` and the manifold), as long as
`Lmax ≥ 4(10 + 2C₀Δ + Δ/3)` (`C₀ = 200, 2·10⁶, 100`) and `Λ C₀Δ ≤ 1/4`.
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

namespace LocalChartFamilyQ

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ}

/-- FC08's count on a finite family of supports of the family's scale, at a Riemannian
three-manifold built from `g` (the generic step of the three counts). -/
theorem active_count_of_buffer_LC87
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (hΛ : 0 ≤ Λ) {J : Set X} (hJ : J.Finite) (S : X → Set X) {C₀ Δc : ℝ} (hΔ : 1 ≤ Δc)
    (hC₀ : 0 ≤ C₀) (hbudget : Λ * max 10 (C₀ * Δc) ≤ 1 / 4)
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
  have : CompleteSpace X := complete_of_compact
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
    (fun j _ _ y hy => by
      have h := L.sectional_buffer Q hQpos hL j y hy
      rw [← inv_pow] at h
      exact h)
  rw [hdim] at h
  have hset : {j | j ∈ J ∧ (S j ∩ ball p (10 * ρ p)).Nonempty} =
      {j | j ∈ hJ.toFinset ∧ (S j ∩ ball p (10 * ρ p)).Nonempty} := by
    ext j
    simp only [mem_ofPred_eq, Set.Finite.mem_toFinset]
  rw [hset]
  exact h

/-- **Active circle supports meeting a comparison ball `B(p, 10ρ(p))`.** -/
theorem circle_active_count
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (hΛ : 0 ≤ Λ) (hΛb : Λ * 200 ≤ 1 / 4) (hL : 4 * (10 + 2 * 200 + 1 / 3) ≤ Lmax) (p : X) :
    ({j | j ∈ L.circle.centres ∧
        (tsupport (L.circle.cutoff j) ∩ ball p (10 * ρ p)).Nonempty}.ncard : ℝ) ≤
      modelVolume (-(1 ^ 2)) 3 (4 * (10 + 2 * 200 + 1 / 3)) /
        modelVolume (-(1 ^ 2)) 3 (1 / 3) := by
  refine L.active_count_of_buffer_LC87 (Δc := 1) hΛ L.circle.finite_centres
    (fun j => tsupport (L.circle.cutoff j)) le_rfl (by norm_num) ?_ (by simpa using hL) ?_ ?_ p
  · rw [mul_one, max_eq_right (by norm_num)]
    exact hΛb
  · intro j hj
    rw [mul_one]
    exact (L.circle.tsupport_subset_ball j hj).trans ball_subset_closedBall
  · intro i hi j hj hij
    have h := L.circle.disjoint_centres hi hj hij
    simpa only [one_mul] using h

/-- **Active slim supports meeting `B(p, 10ρ(p))`** (constant independent of `Δ`). -/
theorem slim_active_count
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛb : Λ * (2000000 * Δ) ≤ 1 / 4)
    (hL : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (p : X) :
    ({j | j ∈ L.slim.centres ∧
        (tsupport (L.slim.cutoff j) ∩ ball p (10 * ρ p)).Nonempty}.ncard : ℝ) ≤
      modelVolume (-(1 ^ 2)) 3 (4 * (10 + 2 * 2000000 + 1 / 3)) /
        modelVolume (-(1 ^ 2)) 3 (1 / 3) := by
  refine L.active_count_of_buffer_LC87 hΛ L.slim.finite_centres
    (fun j => tsupport (L.slim.cutoff j)) hΔ (by norm_num) ?_ hL ?_ L.slim.disjoint_centres p
  · rw [max_eq_right (by nlinarith)]
    exact hΛb
  · intro j hj
    have hS : tsupport (L.slim.cutoff j) ⊆ closedBall j (91 / 100 * (10 ^ 6 * Δ) * ρ j) := by
      unfold SlimFamily.cutoff
      rw [dite_eq_left hj]
      exact (L.slim.centre j hj).tsupport_cutoff_subset
    refine hS.trans (closedBall_subset_closedBall ?_)
    have hr := hρ j
    nlinarith

/-- **Active edge supports meeting `B(p, 10ρ(p))`** (constant independent of `Δ`). -/
theorem edge_active_count
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛb : Λ * (100 * Δ) ≤ 1 / 4)
    (hL : 4 * (10 + 2 * (100 * Δ) + Δ / 3) ≤ Lmax) (p : X) :
    ({j | j ∈ L.edge.centres ∧
        (tsupport (L.edge.cutoff j) ∩ ball p (10 * ρ p)).Nonempty}.ncard : ℝ) ≤
      modelVolume (-(1 ^ 2)) 3 (4 * (10 + 2 * 100 + 1 / 3)) /
        modelVolume (-(1 ^ 2)) 3 (1 / 3) := by
  refine L.active_count_of_buffer_LC87 hΛ L.edge.finite_centres
    (fun j => tsupport (L.edge.cutoff j)) hΔ (by norm_num) ?_ hL
    (fun j _ => L.edge.tsupport_cutoff_subset j) L.edge.disjoint_centres p
  rw [max_eq_right (by nlinarith)]
  exact hΛb

end LocalChartFamilyQ

end DifferentialGeometry.Geometry.Collapse
