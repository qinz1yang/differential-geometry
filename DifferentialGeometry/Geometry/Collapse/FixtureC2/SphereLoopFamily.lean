import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopSlimCentre
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyEdge
import DifferentialGeometry.Geometry.Collapse.LocalExport.ZeroModelBall

/-!
# The families of the sphere loop: non-empty slim family, empty circle / edge / zero families
(S-FIXTURE-C2b, F2, G3 file 3)

At the constant scale `ρ ≡ R` every point of the sphere loop of length `ℓ = N Δ R` has splitting
rank exactly one (`loopRank_eq_one_FXC2`): the circle stratum (rank two), the zero stratum and the
rank-three stratum are empty and no point is a strong edge point. The families are

* `loopSlim_FXC2`: the NON-EMPTY slim family, centres `π_0 (z₀, k Δ R)`, `k < N` (spacing `Δ R`:
  disjoint `Δ R / 3`-balls, covering radius `Δ R / 2 + D₀ ≤ Δ R`, at most `4·10⁶` centres within
  `2·10⁶ Δ R`), with the LC87 slim centre (`SlimCentre`) at every centre;
* `loopCircle_FXC2`, `loopEdge_FXC2`, `loopZero_FXC2`: the empty circle, edge and zero families;
* `loopFamilyE_FXC2 : LocalChartFamilyE …` combining them (exhaustion by the slim balls).
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bundle GC.MetricGeometry
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ContDiff Topology ENNReal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete
attribute [local instance] loopMS3_FXC2
attribute [local instance] nezero_finrank_euclideanThree_LC87

namespace DifferentialGeometry.Geometry.Collapse

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The multiplicity bounds of the empty families are nonnegative. -/
theorem multiplicity_ratio_nonneg_FXC2 (K r₁ r₂ : ℝ) (hK : K < 0) (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) : 0 ≤ modelVolume K 3 r₁ / modelVolume K 3 r₂ :=
  div_nonneg (modelVolume_pos (by norm_num) h₁ ⟨h₁.le, fun h => absurd h (not_lt.mpr hK.le)⟩).le
    (modelVolume_pos (by norm_num) h₂ ⟨h₂.le, fun h => absurd h (not_lt.mpr hK.le)⟩).le

section Families

variable (ℓ : LoopLen_FXC2) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ} {D0 : ℝ}
  (hD0 : ∀ s s' : S2, sphereDist_FXC2 s s' ≤ D0) (hβ1 : 0 < β 1) (hβ1' : β 1 < 1)
  (hβ2 : β 2 ≤ 3 / 20) (hβ3 : β 3 ≤ 3 / 20) (hthin : β 1 / 2 + D0 / R ≤ 1 / 100)
  (hℓ : 8 * R / β 1 ≤ ℓ.1)

include hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ in
/-- No point of the loop lies in a stratum other than the one-stratum. -/
theorem loopNotMemStratum_FXC2 {k : Fin 4} (hk : k ≠ 1) (p : LoopC_FXC2 ℓ) :
    p ∉ scaledSplittingStratum.{0, 0} (fun _ : LoopC_FXC2 ℓ => R) (fun _ => hR) β k := by
  rw [loopStratum_ne_one_empty_FXC2 ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ hk]
  exact notMem_empty p

include hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ in
/-- **The empty circle family** (no point of the two-stratum). -/
def loopCircle_FXC2 :
    CircleFamily 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) (fun _ => R) (fun _ => hR) β where
  centres := ∅
  finite_centres := finite_empty
  centres_subset := empty_subset _
  disjoint_centres := pairwiseDisjoint_empty
  covers := fun p hp => absurd hp
    (loopNotMemStratum_FXC2 ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ (by decide) p)
  chart := fun j hj => absurd hj (notMem_empty j)
  chart_center := fun j hj => absurd hj (notMem_empty j)
  cutoff := fun _ _ => 0
  contMDiff_cutoff := fun j hj => absurd hj (notMem_empty j)
  cutoff_mem_Icc := fun j hj => absurd hj (notMem_empty j)
  cutoff_eq_one := fun j hj => absurd hj (notMem_empty j)
  coord_lt_of_cutoff_ne_zero := fun j hj => absurd hj (notMem_empty j)
  tsupport_subset_domain := fun j hj => absurd hj (notMem_empty j)
  plateau := fun j hj => absurd hj (notMem_empty j)
  tsupport_subset_ball := fun j hj => absurd hj (notMem_empty j)
  multiplicity := fun x => by
    rw [empty_inter, ncard_empty, Nat.cast_zero]
    exact multiplicity_ratio_nonneg_FXC2 _ _ _ (by norm_num) (by norm_num) (by norm_num)

variable {Δ σc μ b s b' s' ε γc βc : ℝ}

include hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ in
/-- **The empty edge family** (no strong edge point; the antecedent of `covers_nonslim` is
refuted by the thin approximation at the tolerance `β 1`). -/
def loopEdge_FXC2 (hΔ : 1 ≤ Δ) (hbs : b + s ≤ 1 / 100) :
    EdgeFamily (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ) (fun _ => R)
      (fun _ => hR) β Δ σc μ b s b' s' ε γc βc where
  centres := ∅
  finite_centres := finite_empty
  strong := fun j hj => absurd hj (notMem_empty j)
  disjoint_centres := pairwiseDisjoint_empty
  covers_strong := fun a ha => absurd ha
    (loopNotEdge_FXC2 ℓ hR hD0 hβ1 hβ1' hthin hℓ hΔ hbs a)
  covers_nonslim := fun p _ hns => absurd (loopSlimFactor_FXC2 ℓ hR hD0 hβ1 hβ1' hthin hℓ hΔ p) hns
  multiplicity := fun x => by
    rw [empty_inter, ncard_empty, Nat.cast_zero]
    exact multiplicity_ratio_nonneg_FXC2 _ _ _ (by norm_num) (by norm_num) (by norm_num)
  smoothing := fun _ => 0
  smoothing_nonneg := fun _ => le_rfl
  lipschitz_smoothing := (LipschitzWith.const (0 : ℝ)).weaken zero_le
  smoothing_value := fun p hp => absurd hp (notMem_empty p)
  chart := fun j hj => absurd hj (notMem_empty j)
  chart_center := fun j hj => absurd hj (notMem_empty j)

variable {δ εr e T V : ℝ}

include hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ in
/-- **The empty zero family** (no point of the zero stratum; the models are the loop itself). -/
def loopZero_FXC2 :
    ZeroModelFamily 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (fun _ => R) (fun _ => hR) β
      (fun _ : LoopC_FXC2 ℓ => LoopC_FXC2 ℓ) (fun _ : LoopC_FXC2 ℓ => PUnit.{1})
      (fun _ => PUnit.unit) δ εr e T V where
  centres := ∅
  finite_centres := finite_empty
  zero := fun i hi => absurd hi (notMem_empty i)
  zero_center := fun i hi => absurd hi (notMem_empty i)
  radius_mem := fun i hi => absurd hi (notMem_empty i)
  disjoint := fun i hi => absurd hi (notMem_empty i)
  meets_stratum := fun i hi => absurd hi (notMem_empty i)
  covers_stratum := fun p hp => absurd hp
    (loopNotMemStratum_FXC2 ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ (by decide) p)
  one_end := fun i hi => absurd hi (notMem_empty i)

section SlimFam

variable {Δ σs vs : ℝ} {K : ℕ} (hΔ : 1 ≤ Δ) (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (hvs : 0 < vs)
  (hK : 5 ≤ K) (hR1 : 1 ≤ R) (hD00 : 0 ≤ D0) (z₀ : S2) {N : ℕ} (hN : ℓ.1 = N * (Δ * R))
  (hΔR : 2 * D0 ≤ Δ * R) (hβ0 : β 1 < slimBeta0_FXC2 hR z₀ hΔ hσs hσs1 hvs hK)

include hβ1 hβ1' hℓ hR in
theorem loop_two_R_le_FXC2 : 2 * R ≤ ℓ.1 := by
  have h1 : 8 * R ≤ 8 * R / β 1 := by
    rw [le_div_iff₀ hβ1]
    nlinarith
  linarith

include hΔ hR in
theorem loop_sp_pos_FXC2 : 0 < Δ * R := mul_pos (by linarith) hR

/-- The index of a centre. -/
def loopSlimA_FXC2 (j : LoopC_FXC2 ℓ) (hj : j ∈ loopCentres_FXC2 ℓ z₀ (Δ * R) N) : ℝ :=
  ((Classical.choose (Set.mem_range.mp hj) : Fin N) : ℕ) * (Δ * R)

theorem loopSlimHja_FXC2 (j : LoopC_FXC2 ℓ) (hj : j ∈ loopCentres_FXC2 ℓ z₀ (Δ * R) N) :
    j = loopDiffeo_FXC2 ℓ (loopCoverS_FXC2 ℓ.1 (loopSlimA_FXC2 ℓ z₀ j hj) (z₀, 0)) := by
  refine (Classical.choose_spec (Set.mem_range.mp hj)).symm.trans ?_
  unfold loopCentre_FXC2 loopSlimA_FXC2
  rw [loopCoverS_base_FXC2]
  rfl

include hR1 hD00 hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ hN hΔR hβ0 hσs hσs1 hvs hK in
/-- **The NON-EMPTY slim family of the sphere loop**: the net of the `N` centres
`π_0 (z₀, k Δ R)` with the LC87 slim centre at every centre. -/
def loopSlim_FXC2 :
    SlimFamily (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ) (fun _ => R)
      (fun _ => hR) β Δ σs K where
  centres := loopCentres_FXC2 ℓ z₀ (Δ * R) N
  finite_centres := loopCentres_finite_FXC2 ℓ z₀ (Δ * R) N
  centres_subset := by
    rintro j ⟨k, rfl⟩
    refine ⟨?_, loopSlimFactor_FXC2 ℓ hR hD0 hβ1 hβ1' hthin hℓ hΔ _⟩
    rw [loopStratum_one_eq_univ_FXC2 ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ]
    exact mem_univ _
  disjoint_centres := by
    intro j hj j' hj' hne
    obtain ⟨k, rfl⟩ := hj
    obtain ⟨k', rfl⟩ := hj'
    have hkk : k ≠ k' := fun h => hne (by rw [h])
    have hfar := loopCentres_far_FXC2 ℓ z₀ (loop_sp_pos_FXC2 hR hΔ) hN k k' hkk
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    have hx1 : dist x (loopCentre_FXC2 ℓ z₀ (Δ * R) k) < Δ * R / 3 := mem_ball.mp hx
    have hx2 : dist x (loopCentre_FXC2 ℓ z₀ (Δ * R) k') < Δ * R / 3 := mem_ball.mp hx'
    have h1 := dist_triangle (loopCentre_FXC2 ℓ z₀ (Δ * R) k) x
      (loopCentre_FXC2 ℓ z₀ (Δ * R) k')
    rw [dist_comm (loopCentre_FXC2 ℓ z₀ (Δ * R) k) x] at h1
    have := loop_sp_pos_FXC2 hR hΔ
    linarith
  covers := fun p _ _ => by
    obtain ⟨k, hk⟩ := loopCentres_cover_FXC2 ℓ z₀ (loop_sp_pos_FXC2 hR hΔ) hN hD00 hD0 p
    refine ⟨loopCentre_FXC2 ℓ z₀ (Δ * R) k, ⟨k, rfl⟩, fun x hx => ?_⟩
    have hx1 : dist x p < Δ * R := mem_ball.mp hx
    rw [mem_ball]
    have h1 := dist_triangle x p (loopCentre_FXC2 ℓ z₀ (Δ * R) k)
    change dist x (loopCentre_FXC2 ℓ z₀ (Δ * R) k) < 2 * (Δ * R)
    have := loop_sp_pos_FXC2 hR hΔ
    linarith
  centre := fun j hj => Classical.choose (exists_slimCentre_loop_FXC2 hΔ hσs hσs1 hvs hK hR hR1
    z₀ ℓ (loop_two_R_le_FXC2 ℓ hR hβ1 hβ1' hℓ) j (loopSlimA_FXC2 ℓ z₀ j hj)
    (loopSlimHja_FXC2 ℓ z₀ j hj) hβ1 hβ0
    (loopSlimFactor_FXC2 ℓ hR hD0 hβ1 hβ1' hthin hℓ hΔ j))
  multiplicity := fun x =>
    (loopCentres_ncard_le_FXC2 ℓ z₀ (loop_sp_pos_FXC2 hR hΔ) hN x).trans
      slim_multiplicity_const_ge_FXC2

end SlimFam

end Families

end DifferentialGeometry.Geometry.Collapse
