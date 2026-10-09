import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleAdapted
import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusFlat
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyEdge
import DifferentialGeometry.Geometry.Collapse.LocalExport.ZeroModelBall

/-!
# The empty slim, edge and zero families and the family `LocalChartFamilyE` of the flat torus
(S-FIXTURE-C1b, F1, G5 file 1)

At the constant scale `R` every point of the thin flat torus has splitting rank exactly two
(`torRank_eq_two_FXC1`): the one-stratum and the zero stratum are empty and there is no strong edge
point (`torNotEdge_FXC1`). Hence the slim, edge and zero families are empty (their multiplicity
bounds are non-negative constants), and

* `torFamilyE_FXC1 : LocalChartFamilyE (Tor Λ) …` combines the non-empty circle family of G3 with
  these empty families; the exhaustion is the covering of the centre net; the curvature buffer is
  `sec = 0`; the circle cutoff is the formula cutoff (`rfl`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The multiplicity bounds of the families are nonnegative (negative model curvature). -/
theorem multiplicity_ratio_nonneg_FXC1 (K r₁ r₂ : ℝ) (hK : K < 0) (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) : 0 ≤ modelVolume K 3 r₁ / modelVolume K 3 r₂ :=
  div_nonneg (modelVolume_pos (by norm_num) h₁ ⟨h₁.le, fun h => absurd h (not_lt.mpr hK.le)⟩).le
    (modelVolume_pos (by norm_num) h₂ ⟨h₂.le, fun h => absurd h (not_lt.mpr hK.le)⟩).le

section Families

variable (Λ : TorusPeriods_FXC1) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ} (hβ2 : 0 < β 2)
  (hβ2s : β 2 ≤ 1 / 10 ^ 7) (hL2 : Λ.L 2 ≤ R * β 2) (hLp : 8 * R / β 2 ≤ planePeriod_FXC1 Λ)
  (hβ3 : β 3 ≤ 3 / 20)

include hR hβ2 hβ2s hL2 hLp hβ3 in
/-- No point of the torus lies in a stratum other than the two-stratum. -/
theorem torNotMemStratum_FXC1 {k : Fin 4} (hk : k ≠ 2) (p : Tor_FXC1 Λ) :
    p ∉ scaledSplittingStratum.{0, 0} (fun _ : Tor_FXC1 Λ => R) (fun _ => hR) β k := by
  rw [torStratum_ne_two_empty_FXC1 Λ hR hβ2 (hβ2s.trans (by norm_num)) hβ3 hL2 hLp hk]
  exact notMem_empty p

variable {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc : ℝ}

include hR hβ2 hβ2s hL2 hLp hβ3 in
/-- **The empty slim family** (no point of the one-stratum). -/
def torSlim_FXC1 :
    SlimFamily (Tor_FXC1 Λ) (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ) (fun _ => R)
      (fun _ => hR) β Δ σs K where
  centres := ∅
  finite_centres := finite_empty
  centres_subset := empty_subset _
  disjoint_centres := pairwiseDisjoint_empty
  covers := fun p hp => absurd hp (torNotMemStratum_FXC1 Λ hR hβ2 hβ2s hL2 hLp hβ3
    (by decide) p)
  centre := fun j hj => absurd hj (notMem_empty j)
  multiplicity := fun x => by
    rw [empty_inter, ncard_empty, Nat.cast_zero]
    exact multiplicity_ratio_nonneg_FXC1 _ _ _ (by norm_num) (by norm_num) (by norm_num)

include hR hβ2 hβ2s hL2 hLp hβ3 in
/-- **The empty edge family** (no strong edge point, no point of the one-stratum). -/
def torEdge_FXC1 (hb : b ≤ 1 / 6) (hs : s ≤ 1 / 7) (hbs : b + s ≤ 1 / 100) :
    EdgeFamily (Tor_FXC1 Λ) (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ) (fun _ => R)
      (fun _ => hR) β Δ σc μ b s b' s' ε γc βc where
  centres := ∅
  finite_centres := finite_empty
  strong := fun j hj => absurd hj (notMem_empty j)
  disjoint_centres := pairwiseDisjoint_empty
  covers_strong := fun a ha => absurd ha (torNotEdge_FXC1 Λ hR hβ2
    (hβ2s.trans (by norm_num)) hβ3 hL2 hLp hb hs hbs a)
  covers_nonslim := fun p hp => absurd hp (torNotMemStratum_FXC1 Λ hR hβ2 hβ2s hL2 hLp hβ3
    (by decide) p)
  multiplicity := fun x => by
    rw [empty_inter, ncard_empty, Nat.cast_zero]
    exact multiplicity_ratio_nonneg_FXC1 _ _ _ (by norm_num) (by norm_num) (by norm_num)
  smoothing := fun _ => 0
  smoothing_nonneg := fun _ => le_rfl
  lipschitz_smoothing := (LipschitzWith.const (0 : ℝ)).weaken zero_le
  smoothing_value := fun p hp => absurd hp (notMem_empty p)
  chart := fun j hj => absurd hj (notMem_empty j)
  chart_center := fun j hj => absurd hj (notMem_empty j)

variable {δ εr e T V : ℝ}

include hR hβ2 hβ2s hL2 hLp hβ3 in
/-- **The empty zero family** (no point of the zero stratum; the models are the torus itself). -/
def torZeroFamily_FXC1 :
    ZeroModelFamily 𝓘(ℝ, E3) (Tor_FXC1 Λ) (torMetric_FXC1 Λ) (fun _ => R) (fun _ => hR) β
      (fun _ : Tor_FXC1 Λ => Tor_FXC1 Λ) (fun _ : Tor_FXC1 Λ => PUnit.{1})
      (fun _ => PUnit.unit) δ εr e T V where
  centres := ∅
  finite_centres := finite_empty
  zero := fun i hi => absurd hi (notMem_empty i)
  zero_center := fun i hi => absurd hi (notMem_empty i)
  radius_mem := fun i hi => absurd hi (notMem_empty i)
  disjoint := fun i hi => absurd hi (notMem_empty i)
  meets_stratum := fun i hi => absurd hi (notMem_empty i)
  covers_stratum := fun p hp => absurd hp (torNotMemStratum_FXC1 Λ hR hβ2 hβ2s hL2 hLp hβ3
    (by decide) p)
  one_end := fun i hi => absurd hi (notMem_empty i)

variable (N : ℕ) (hL0 : Λ.L 0 = N * R) (hL1 : Λ.L 1 = N * R)
  {Lam : ℝ} {Lmax τ : ℝ}

include hR hβ2 hβ2s hL2 hLp hβ3 hL0 hL1 in
/-- **The family `LocalChartFamilyE` of the flat torus**: the non-empty circle family and the empty
slim and edge families. -/
def torFamilyE_FXC1 (hb : b ≤ 1 / 6) (hs : s ≤ 1 / 7) (hbs : b + s ≤ 1 / 100) :
    LocalChartFamilyE (Tor_FXC1 Λ) (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ) (fun _ => R)
      (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ where
  contMDiff_scale := contMDiff_const
  lipschitz_scale := (LipschitzWith.const R).weaken zero_le
  circle := torCircleFamily_FXC1 Λ hR hβ2 hβ2s hL2 hLp N hL0 hL1 hβ3
  slim := torSlim_FXC1 Λ hR hβ2 hβ2s hL2 hLp hβ3
  edge := torEdge_FXC1 Λ hR hβ2 hβ2s hL2 hLp hβ3 hb hs hbs
  exhaustion := fun x => by
    obtain ⟨j, hj, hd⟩ := torCentres_cover_FXC1 Λ N hL0 hL1 hR
      (torCentres_pos_FXC1 Λ N hL0) (torL2_le_half_FXC1 Λ hR hβ2s hL2) x
    exact Or.inr (Or.inl ⟨j, hj, mem_ball.mpr (by linarith)⟩)
  circle_cutoff_eq := fun j _ => rfl
  slim_cutoff_eq := fun j hj => absurd hj (notMem_empty j)
  sectional_buffer := fun _ _ _ _ y _ =>
    torMetric_sectional_FXC1 Λ y (neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg _)))
  edge_coarse := fun j hj => absurd hj (notMem_empty j)

end Families

end DifferentialGeometry.Geometry.Collapse
