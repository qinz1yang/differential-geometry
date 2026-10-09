import DifferentialGeometry.Geometry.Fibration.ActualActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment

/-!
# Boundary port (lane B-PORT-A): ActualActiveSupportPacket (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualActiveSupportPacket.lean` by
`build-logs/scratch/B-PORT-A/gen_circle.py` (engine `portlib2.py`); do
not edit by hand, re-run the script. Closed family → boundary family (`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
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

section ZeroList

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X} {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ} {U₁ U₂ : Set X}

/-- The zero centres whose LC31 cutoff support meets `B(p, ℓρ(p))`. -/
def zeroMeetingList_BAUGP (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (p : X)
    (ℓ : ℝ) : Set X :=
  {k | ∃ hk : k ∈ Z.centres, (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
    ((Z.zero k hk).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty}

/-- At most one zero support meets `B(p, ℓρ(p))` (FC09 from slow variation). -/
theorem ncard_zeroMeetingList_le_one_BAUGP
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) {Λ : NNReal}
    (hρL : LipschitzWith Λ ρ) (he : e < 1 / 40) (hT : 0 < T) (p : X) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hsmall : 2 * (ℓ / T) + 2 * (ℓ * Λ) ≤ 1 / 40) :
    (zeroMeetingList_BAUGP Z p ℓ).ncard ≤ 1 := by
  have huniq := (zero_supports_meeting_ball_shell_BAUGP Z hρL he hT p hℓ hsmall).1
  have hfin : (zeroMeetingList_BAUGP Z p ℓ).Finite :=
    Z.finite_centres.subset fun k hk => hk.choose
  refine (Set.ncard_le_one hfin).mpr ?_
  rintro k₁ ⟨hk₁, h₁⟩ k₂ ⟨hk₂, h₂⟩
  exact huniq k₁ hk₁ k₂ hk₂ h₁ h₂

end ZeroList

section Packet

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNA_C14KA_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNA_C14KA_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCA_C14KA_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
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
theorem fc07_input_packet_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (p : X) :
    ({j | j ∈ P.circle.centres ∧
        (tsupport (P.circle.cutoff j) ∩ ball p (10 * ρ p)).Nonempty}.ncard : ℝ) +
      {j | j ∈ P.slim.centres ∧
        (tsupport (P.slim.cutoff_BCNT j) ∩ ball p (10 * ρ p)).Nonempty}.ncard +
      {j | j ∈ P.edgeB.centres ∧
        (tsupport (P.edgeB.cutoff_BAUGA j) ∩ ball p (10 * ρ p)).Nonempty}.ncard +
      (zeroMeetingList_BAUGP P.zero p 10).ncard ≤ fc07ActiveBound ∧
    (∀ j ∈ P.circle.centres, (tsupport (P.circle.cutoff j) ∩ ball p (10 * ρ p)).Nonempty →
      ρ j / ρ p ∈ Icc (1 / 2) 2 ∧ dist j p ≤ (10 + 2 * 102) * ρ p ∧
        ball p (10 * ρ p) ⊆ ball j ((102 + 4 * 10) * ρ j) ∧
        ball j ((102 + 4 * 10) * ρ j) ⊆ ball j (200 * ρ j) ∧
        ∀ x ∈ ball p (10 * ρ p), (ball j (200 * ρ j))ᶜ.Nonempty →
          (200 - 102 - 4 * 10) * ρ j ≤ infDist x (ball j (200 * ρ j))ᶜ) ∧
    (∀ j (hj : j ∈ P.slim.centres),
      (tsupport (P.slim.cutoff_BCNT j) ∩ ball p (10 * ρ p)).Nonempty →
      ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.slim.centre j hj).coord_BCG2 (ball j (10 ^ 6 * Δ * ρ j)) ∧
        ρ j / ρ p ∈ Icc (1 / 2) 2 ∧ dist j p ≤ (10 + 2 * (91 / 100 * (10 ^ 6 * Δ))) * ρ p ∧
        ball p (10 * ρ p) ⊆ ball j ((91 / 100 * (10 ^ 6 * Δ) + 4 * 10) * ρ j) ∧
        ball j ((91 / 100 * (10 ^ 6 * Δ) + 4 * 10) * ρ j) ⊆ ball j (10 ^ 6 * Δ * ρ j) ∧
        ∀ x ∈ ball p (10 * ρ p), (ball j (10 ^ 6 * Δ * ρ j))ᶜ.Nonempty →
          (10 ^ 6 * Δ - 91 / 100 * (10 ^ 6 * Δ) - 4 * 10) * ρ j ≤
            infDist x (ball j (10 ^ 6 * Δ * ρ j))ᶜ) ∧
    (∀ j ∈ P.edgeB.centres, (tsupport (P.edgeB.cutoff_BAUGA j) ∩ ball p (10 * ρ p)).Nonempty →
      ρ j / ρ p ∈ Icc (1 / 2) 2 ∧ dist j p ≤ (10 + 2 * (14 * Δ)) * ρ p ∧
        ball p (10 * ρ p) ⊆ ball j ((14 * Δ + 4 * 10) * ρ j) ∧
        ball j ((14 * Δ + 4 * 10) * ρ j) ⊆ ball j (100 * Δ * ρ j) ∧
        ∀ x ∈ ball p (10 * ρ p), (ball j (100 * Δ * ρ j))ᶜ.Nonempty →
          (100 * Δ - 14 * Δ - 4 * 10) * ρ j ≤ infDist x (ball j (100 * Δ * ρ j))ᶜ) ∧
    (∀ k ∈ zeroMeetingList_BAUGP P.zero p 10, ∀ k' ∈ zeroMeetingList_BAUGP P.zero p 10, k = k') ∧
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
  have hzero := zero_supports_meeting_ball_shell_BAUGP P.zero hρL he hT0 p (ℓ := 10) (by norm_num)
    hsmall
  have hcirc := P.circle_count_BCNT hΛ (by nlinarith) (by nlinarith) p
  have hslim := P.slim_count_BCNT hΔ hΛ (by nlinarith) hLmax p
  have hedge := P.edgeB_count_BCNT hΔ hΛ (by nlinarith) (by nlinarith) p
  have hz := ncard_zeroMeetingList_le_one_BAUGP P.zero hρL he hT0 p (ℓ := 10) (by norm_num) hsmall
  have hz' : ((zeroMeetingList_BAUGP P.zero p 10).ncard : ℝ) ≤ 1 := by exact_mod_cast hz
  unfold bdCircleList_BCNT at hcirc
  unfold bdSlimList_BCNT at hslim
  unfold bdEdgeBList_BCNT at hedge
  refine ⟨?_, fun j hj hmeet => ?_, fun j hj hmeet => ?_, fun j hj hmeet => ?_, ?_, hzero.2⟩
  · unfold fc07ActiveBound
    linarith
  · exact P.circle_support_scale_buffer_BAUGP hΛ hj (R := 10) (by norm_num)
      (by rw [max_eq_right (by norm_num)]; nlinarith) (by norm_num) hmeet
  · exact P.slim_support_scale_buffer_BAUGP hΛ hΔ0 hj (R := 10) (by norm_num)
      (by rw [max_eq_right (by nlinarith)]; nlinarith) (by nlinarith) hmeet
  · exact fc12_edge_rowE_BAUGP P hΛ hΔ0 hμ hτ hΔΛ hj (R := 10) (by norm_num)
      (by rw [max_eq_right (by nlinarith)]; nlinarith) (by nlinarith) hmeet
  · rintro k₁ ⟨hk₁, h₁⟩ k₂ ⟨hk₂, h₂⟩
    exact hzero.1 k₁ hk₁ k₂ hk₂ h₁ h₂

end Packet


end DifferentialGeometry.Geometry.Collapse
