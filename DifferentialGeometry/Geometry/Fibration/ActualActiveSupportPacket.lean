import DifferentialGeometry.Geometry.Fibration.ActualEdgeComparisonListApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyCounts
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyBindings

/-!
# FC07's LC87 input packet on the final family `LocalChartPackets`

Blueprint `master207B.tex`, FC07 (`found:fibration-two-cloud`, B:352; proof decomposition B:388–405):
"First obtain the enlarged-ball count for all active supports …; they retain the edge annular and
zero-shell domains", with FC12's buffered domains (binding matrix B:1530–1540). FC07's OWN conclusion
(the `(2, Γ₁)` cloudy two-manifold of KL 12.7) stays source-qualified (TCP05/TCP06 assembly); this
module binds its LC87 inputs on `P : LocalChartPackets` (packets (iii) and (iv) and the zero family
`P.zero` of CGP01's map `cgpGlobalMap P.toLocalChartFamily P.zero`), at every point `p` and the
comparison ball `B(p, 10ρ(p))`:

* `zeroMeetingList`: the zero centres whose LC31 cutoff support meets `B(p, ℓρ(p))`.
* `fc07ActiveBound`: the numerical bound `N₇ = N_circle + N_slim + N_edge + 1` (LC87's FC08 counts
  `circle_active_count`, `slim_active_count`, `edge_active_count`; at most one zero support).
* `fc07_input_packet`: the count of ALL active supports, FC12's buffers for every meeting circle,
  slim and edge support (`circle_support_scale_buffer`, `slim_support_scale_buffer`,
  `fc12_edge_rowE`) and FC09/FC13 for the zero supports (`zero_supports_meeting_ball_shell`).
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

/-- FC07's numerical bound on ALL active supports meeting `B(p, 10ρ(p))`: LC87's circle, slim and
edge counts and one zero support. -/
def fc07ActiveBound : ℝ :=
  modelVolume (-(1 ^ 2)) 3 (4 * (10 + 2 * 200 + 1 / 3)) / modelVolume (-(1 ^ 2)) 3 (1 / 3) +
    modelVolume (-(1 ^ 2)) 3 (4 * (10 + 2 * 2000000 + 1 / 3)) /
      modelVolume (-(1 ^ 2)) 3 (1 / 3) +
    modelVolume (-(1 ^ 2)) 3 (4 * (10 + 2 * 100 + 1 / 3)) / modelVolume (-(1 ^ 2)) 3 (1 / 3) +
    1

section ZeroList

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X} {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- The zero centres whose LC31 cutoff support meets `B(p, ℓρ(p))`. -/
def zeroMeetingList (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (p : X)
    (ℓ : ℝ) : Set X :=
  {k | ∃ hk : k ∈ Z.centres, (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
    ((Z.zero k hk).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty}

/-- At most one zero support meets `B(p, ℓρ(p))` (FC09 from slow variation). -/
theorem ncard_zeroMeetingList_le_one
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) {Λ : NNReal}
    (hρL : LipschitzWith Λ ρ) (he : e < 1 / 40) (hT : 0 < T) (p : X) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hsmall : 2 * (ℓ / T) + 2 * (ℓ * Λ) ≤ 1 / 40) :
    (zeroMeetingList Z p ℓ).ncard ≤ 1 := by
  have huniq := (zero_supports_meeting_ball_shell Z hρL he hT p hℓ hsmall).1
  have hfin : (zeroMeetingList Z p ℓ).Finite :=
    Z.finite_centres.subset fun k hk => hk.choose
  refine (Set.ncard_le_one hfin).mpr ?_
  rintro k₁ ⟨hk₁, h₁⟩ k₂ ⟨hk₂, h₂⟩
  exact huniq k₁ hk₁ k₂ hk₂ h₁ h₂

end ZeroList

section Packet

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNA_C14KA
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNA_C14KA
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCA_C14KA
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FC07's LC87 input packet** on `LocalChartPackets`, at the comparison ball `B(p, 10ρ(p))`:
1. the number of ALL active supports (circle, slim, edge, zero) meeting it is at most the numerical
   `fc07ActiveBound` (independent of `Δ`, noncollapse and the number of charts);
2. FC12 for every meeting circle support (smooth domain `B(j, 200ρ(j))`);
3. FC12 for every meeting slim support, with its original coordinate smooth on its domain;
4. FC12 for every meeting edge support (packet (iv));
5. FC09/FC13 for the zero supports of `P.zero`: at most one meets, and then the ball lies in its
   buffered shell with the original radial function smooth on an open neighbourhood. -/
theorem fc07_input_packet
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (p : X) :
    ({j | j ∈ P.circle.centres ∧
        (tsupport (P.circle.cutoff j) ∩ ball p (10 * ρ p)).Nonempty}.ncard : ℝ) +
      {j | j ∈ P.slim.centres ∧
        (tsupport (P.slim.cutoff j) ∩ ball p (10 * ρ p)).Nonempty}.ncard +
      {j | j ∈ P.edge.centres ∧
        (tsupport (P.edge.cutoff j) ∩ ball p (10 * ρ p)).Nonempty}.ncard +
      (zeroMeetingList P.zero p 10).ncard ≤ fc07ActiveBound ∧
    (∀ j ∈ P.circle.centres, (tsupport (P.circle.cutoff j) ∩ ball p (10 * ρ p)).Nonempty →
      ρ j / ρ p ∈ Icc (1 / 2) 2 ∧ dist j p ≤ (10 + 2 * 102) * ρ p ∧
        ball p (10 * ρ p) ⊆ ball j ((102 + 4 * 10) * ρ j) ∧
        ball j ((102 + 4 * 10) * ρ j) ⊆ ball j (200 * ρ j) ∧
        ∀ x ∈ ball p (10 * ρ p), (ball j (200 * ρ j))ᶜ.Nonempty →
          (200 - 102 - 4 * 10) * ρ j ≤ infDist x (ball j (200 * ρ j))ᶜ) ∧
    (∀ j (hj : j ∈ P.slim.centres),
      (tsupport (P.slim.cutoff j) ∩ ball p (10 * ρ p)).Nonempty →
      ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.slim.centre j hj).coord (ball j (10 ^ 6 * Δ * ρ j)) ∧
        ρ j / ρ p ∈ Icc (1 / 2) 2 ∧ dist j p ≤ (10 + 2 * (91 / 100 * (10 ^ 6 * Δ))) * ρ p ∧
        ball p (10 * ρ p) ⊆ ball j ((91 / 100 * (10 ^ 6 * Δ) + 4 * 10) * ρ j) ∧
        ball j ((91 / 100 * (10 ^ 6 * Δ) + 4 * 10) * ρ j) ⊆ ball j (10 ^ 6 * Δ * ρ j) ∧
        ∀ x ∈ ball p (10 * ρ p), (ball j (10 ^ 6 * Δ * ρ j))ᶜ.Nonempty →
          (10 ^ 6 * Δ - 91 / 100 * (10 ^ 6 * Δ) - 4 * 10) * ρ j ≤
            infDist x (ball j (10 ^ 6 * Δ * ρ j))ᶜ) ∧
    (∀ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball p (10 * ρ p)).Nonempty →
      ρ j / ρ p ∈ Icc (1 / 2) 2 ∧ dist j p ≤ (10 + 2 * (14 * Δ)) * ρ p ∧
        ball p (10 * ρ p) ⊆ ball j ((14 * Δ + 4 * 10) * ρ j) ∧
        ball j ((14 * Δ + 4 * 10) * ρ j) ⊆ ball j (100 * Δ * ρ j) ∧
        ∀ x ∈ ball p (10 * ρ p), (ball j (100 * Δ * ρ j))ᶜ.Nonempty →
          (100 * Δ - 14 * Δ - 4 * 10) * ρ j ≤ infDist x (ball j (100 * Δ * ρ j))ᶜ) ∧
    (∀ k ∈ zeroMeetingList P.zero p 10, ∀ k' ∈ zeroMeetingList P.zero p 10, k = k') ∧
    ∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k hk).radial y)) ∩ ball p (10 * ρ p)).Nonempty →
      (∀ x ∈ ball p (10 * ρ p), 3 / 20 * (P.zero.zero k hk).radius < dist k x ∧
        dist k x < 19 / 20 * (P.zero.zero k hk).radius) ∧
      ∃ O : Set X, IsOpen O ∧ ball p (10 * ρ p) ⊆ O ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.zero.zero k hk).radial O := by
  have hΔ0 : 0 < Δ := by linarith
  have hΛΔ : Λ ≤ Δ * Λ := le_mul_of_one_le_left hΛ hΔ
  have hΔΛ0 : 0 ≤ Δ * Λ := mul_nonneg hΔ0.le hΛ
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  have hρL : LipschitzWith (Real.toNNReal Λ) ρ := P.lipschitz_scale
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  have hT0 : 0 < T := by nlinarith
  have hsmall : 2 * (10 / T) + 2 * (10 * ((Real.toNNReal Λ : NNReal) : ℝ)) ≤ 1 / 40 := by
    rw [hc]
    have hq : 10 / T ≤ 1 / 160000000 := by
      rw [div_le_iff₀ hT0]
      nlinarith
    nlinarith
  have hzero := zero_supports_meeting_ball_shell P.zero hρL he hT0 p (ℓ := 10) (by norm_num)
    hsmall
  have hcirc := P.toLocalChartFamilyQ.circle_active_count hΛ (by nlinarith) (by nlinarith) p
  have hslim := P.toLocalChartFamilyQ.slim_active_count hΔ hΛ (by nlinarith) hLmax p
  have hedge := P.toLocalChartFamilyQ.edge_active_count hΔ hΛ (by nlinarith) (by nlinarith) p
  have hz := ncard_zeroMeetingList_le_one P.zero hρL he hT0 p (ℓ := 10) (by norm_num) hsmall
  have hz' : ((zeroMeetingList P.zero p 10).ncard : ℝ) ≤ 1 := by exact_mod_cast hz
  refine ⟨?_, fun j hj hmeet => ?_, fun j hj hmeet => ?_, fun j hj hmeet => ?_, ?_, hzero.2⟩
  · unfold fc07ActiveBound
    linarith
  · exact P.toLocalChartFamily.circle_support_scale_buffer hΛ hj (R := 10) (by norm_num)
      (by rw [max_eq_right (by norm_num)]; nlinarith) (by norm_num) hmeet
  · exact P.toLocalChartFamily.slim_support_scale_buffer hΛ hΔ0 hj (R := 10) (by norm_num)
      (by rw [max_eq_right (by nlinarith)]; nlinarith) (by nlinarith) hmeet
  · exact fc12_edge_rowE P.toLocalChartFamilyE hΛ hΔ0 hμ hτ hΔΛ hj (R := 10) (by norm_num)
      (by rw [max_eq_right (by nlinarith)]; nlinarith) (by nlinarith) hmeet
  · rintro k₁ ⟨hk₁, h₁⟩ k₂ ⟨hk₂, h₂⟩
    exact hzero.1 k₁ hk₁ k₂ hk₂ h₁ h₂

end Packet

end DifferentialGeometry.Geometry.Collapse
