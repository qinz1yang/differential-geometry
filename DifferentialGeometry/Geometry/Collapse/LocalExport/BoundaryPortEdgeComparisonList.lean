import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedInteriorKernels
import DifferentialGeometry.Geometry.Fibration.ActualEdgeComparisonList

/-!
# EGP02 on the boundary family: the `edgeB` comparison lists (lane B-PORT-EDGE, G1)

GENERATED from `Geometry/Fibration/ActualEdgeComparisonList.lean` (sections `Lists`,
`ZeroSupports`, `Row`), `…/ActualEdgeComparisonListApplications.lean` (section `General`) and
`Collapse/LocalExport/LocalChartFamilyApplications.lean` (`EdgeFamily.cutoff_eq_one`) by
`build-logs/scratch/B-PORT-EDGE/gen_egp02.py` (tables of `portedge.py`); do not edit by hand,
re-run the script.

The closed EGP02 row on the enriched boundary base family `L : LocalPacketsOnB X …` (complete
σ-compact carrier, regional families) with the ACTIVE edge family `L.edgeB` and a regional zero
family `Z : ZeroModelFamilyOn …`:

* substitution table: `[CompactSpace X]` ↦ `[CompleteSpace X] [SigmaCompactSpace X]`;
  `LocalChartFamily(E) …` ↦ `LocalPacketsOnB … U₁ U₂ Ue₁ Ue₂`; `ZeroModelFamily …` ↦
  `ZeroModelFamilyOn … U₁ U₂`; `EdgeFamily …` ↦ `EdgeFamilyOn … U₁ U₂`; `L.edge` ↦ `L.edgeB`;
  `cutoff / coord / contMDiffOn_coord` ↦ the `…_BAUGA` copies (BAUG-A); `SlimFamily.cutoff` ↦
  `cutoff_BCNT`; `SlimCentre.coord` ↦ `coord_BCG2`; every ported declaration `x` ↦ `x_BAUGP`;
* reused unchanged (generic): `zero_support_shell_of_lipschitz`, `egp02EdgeCount`,
  `egp02SlimCount`, `egp02ListBound` (the numerical `N†` is the SAME constant);
* boundary twins in place of closed lemmas: `zero_cutoff_tsupport_band_BCNT` (B-COUNT),
  `LocalPacketsOnB.tsupport_edgeB_cutoff_subset_BAUGA` (FC18 (ii), BAUG-A),
  `tsupport_edgeB_cutoff_subset_closedBall_BCNT`, `SlimFamilyOn.tsupport_cutoff_subset_BCNT`
  (B-COUNT), `SlimCentreOn.contMDiffOn_coord_BAUGA` (BAUG-A) in place of `fc18_slim_row`, and
  FC27's plateau `EdgeFamilyOn.cutoff_eq_one_of_le_BCF2K` in place of
  `cutoff_eq_coordinateProfile_of_le`.
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

universe u

section API

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}
  {U₁ U₂ : Set X}

/-- The edge cutoff is one on the physical ball `B(j, 3Δρ(j))`. -/
theorem EdgeFamilyOn.cutoff_eq_one_BAUGP (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) {j : X}
    (hj : j ∈ F.centres) {x : X} (hx : dist x j < 3 * Δ * ρ j) : F.cutoff_BAUGA j x = 1 := by
  have hd : (ρ j)⁻¹ * dist x j < 3 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
  have hc := F.chart_center j hj
  unfold EdgeFamilyOn.cutoff_BAUGA
  rw [dite_eq_left hj]
  let C := F.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  have hmem : x ∈ ball C.center (3 * Δ) := by
    rw [hc']
    exact hd
  exact C.cutoff_eq_one hmem

end API

section Lists

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}
  {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ}
  {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- EGP02's edge list `J_e` at `i`: the edge centres whose ACTUAL closed support meets
`D_i = B(i, 20Δρ(i))`. -/
def egpEdgeList_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (i : X) : Set X :=
  {j | j ∈ L.edgeB.centres ∧ (tsupport (L.edgeB.cutoff_BAUGA j) ∩ ball i (20 * Δ * ρ i)).Nonempty}

/-- EGP02's slim list `J_s` at `i`. -/
def egpSlimList_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (i : X) : Set X :=
  {j | j ∈ L.slim.centres ∧ (tsupport (L.slim.cutoff_BCNT j) ∩ ball i (20 * Δ * ρ i)).Nonempty}

/-- **EGP02, the count**: `|J_e| + |J_s| ≤ N†`. A listed centre has its support within
`100Δρ(j)` (edge) or `.91·10⁶Δρ(j)` (slim) of `j`, so slow variation puts `i` in
`B(j, 2·10⁶Δρ(j))`, and the family multiplicity fields at `i` apply. -/
theorem egp02_list_count_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) (hΛ : 0 ≤ Λ)
    (hΔ : 0 < Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (i : X) :
    ((egpEdgeList_BAUGP L i).ncard : ℝ) + (egpSlimList_BAUGP L i).ncard ≤ egp02ListBound := by
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
  have hsubE : egpEdgeList_BAUGP L i ⊆ L.edgeB.centres ∩ {j | i ∈ ball j (2000000 * (Δ * ρ j))} := by
    rintro j ⟨hj, y, hy1, hy2⟩
    refine ⟨hj, hnear j 100 (by norm_num) (by norm_num) ⟨y, ?_, hy2⟩⟩
    exact L.tsupport_edgeB_cutoff_subset_closedBall_BCNT hΔ j hy1
  have hsubS : egpSlimList_BAUGP L i ⊆ L.slim.centres ∩ {j | i ∈ ball j (2000000 * (Δ * ρ j))} := by
    rintro j ⟨hj, y, hy1, hy2⟩
    refine ⟨hj, hnear j 910000 (by norm_num) le_rfl ⟨y, ?_, hy2⟩⟩
    have h91 := L.slim.tsupport_cutoff_subset_BCNT j hy1
    rwa [show 91 / 100 * (10 ^ 6 * Δ) * ρ j = 910000 * Δ * ρ j by ring] at h91
  have hE := Set.ncard_le_ncard hsubE (L.edgeB.finite_centres.inter_of_left _)
  have hS := Set.ncard_le_ncard hsubS (L.slim.finite_centres.inter_of_left _)
  have hE' : ((egpEdgeList_BAUGP L i).ncard : ℝ) ≤ egp02EdgeCount :=
    (Nat.cast_le.mpr hE).trans (L.edgeB.multiplicity i)
  have hS' : ((egpSlimList_BAUGP L i).ncard : ℝ) ≤ egp02SlimCount :=
    (Nat.cast_le.mpr hS).trans (L.slim.multiplicity i)
  unfold egp02ListBound
  linarith

end Lists

section ZeroSupports

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ} {U₁ U₂ : Set X}

/-- **FC09 + FC13 on the actual zero family, from slow variation** (EGP02's zero assertions with
comparison radius `ℓ`): at most one zero support of `Z` meets `B(p, ℓρ(p))`; for a meeting one the
whole ball lies in the buffered shell `3R/20 < d(k,·) < 19R/20` and the ORIGINAL radial function
is smooth on an open neighbourhood of the ball. -/
theorem zero_supports_meeting_ball_shell_BAUGP
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) {Λ : NNReal}
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
      (fun x hx => zero_cutoff_tsupport_band_BCNT Z he hk hx) hmeet
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
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
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
theorem egp02_row_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) {i : X} (hi : i ∈ L.edgeB.centres) :
    ((egpEdgeList_BAUGP L i).ncard : ℝ) +
        (egpSlimList_BAUGP L i).ncard ≤ egp02ListBound ∧
      i ∈ egpEdgeList_BAUGP L i ∧
      (∀ j ∈ egpEdgeList_BAUGP L i,
        99 / 100 < ρ j / ρ i ∧ ρ j / ρ i < 101 / 100 ∧ dist i j < 36 * Δ * ρ i ∧
          ball i (20 * Δ * ρ i) ⊆ ball j (57 * Δ * ρ j) ∧
          ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (L.edgeB.coord_BAUGA j) (ball j (57 * Δ * ρ j))) ∧
      (∀ j (hj : j ∈ L.slim.centres),
        (tsupport (L.slim.cutoff_BCNT j) ∩ ball i (20 * Δ * ρ i)).Nonempty →
        99 / 100 < ρ j / ρ i ∧ ρ j / ρ i < 101 / 100 ∧
          dist i j < 92 / 100 * (1000000 * Δ) * ρ i ∧
          ball i (20 * Δ * ρ i) ⊆ ball j (92 / 100 * (1000000 * Δ) * ρ j) ∧
          ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (L.slim.centre j hj).coord_BCG2
            (ball j (92 / 100 * (1000000 * Δ) * ρ j))) ∧
      (∀ x ∈ ball i (100 * Δ * ρ i), |L.edgeB.coord_BAUGA i x| ≤ 8 * Δ →
        L.edgeB.smoothing x / ρ x ≤ 8 * Δ → x ∈ ball i (20 * Δ * ρ i)) ∧
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
  refine ⟨egp02_list_count_BAUGP L hΛ hΔ0 hLΛ i, ⟨hi, i, ?_, ?_⟩,
    fun j hj => ?_, fun j hj hmeet => ?_, fun x hx hcx hFx => ?_, ?_⟩
  · -- `i ∈ J_e`: the cutoff is one at its centre
    refine subset_tsupport _ ?_
    rw [mem_support, L.edgeB.cutoff_eq_one_BAUGP hi (by rw [dist_self]; have := hρ i; positivity)]
    exact one_ne_zero
  · have := hρ i
    exact mem_ball_self (by positivity)
  · -- edge line
    obtain ⟨hjc, y, hy1, hy2⟩ := hj
    have h14 := (L.tsupport_edgeB_cutoff_subset_BAUGA hΛ hΔ0 hμ hτ hΔΛ hjc).1 hy1
    have hm : (closedBall j (15 * Δ * ρ j) ∩ ball i (20 * Δ * ρ i)).Nonempty := by
      refine ⟨y, closedBall_subset_closedBall ?_ h14, hy2⟩
      nlinarith [hρ j]
    obtain ⟨h1, h2, h3, h4⟩ := edge_comparison_list_edge_bounds hρL (hρ i) (hρ j) hΔ hLΛ' hm
    refine ⟨h1, h2, h3, h4, (L.edgeB.contMDiffOn_coord_BAUGA hjc).mono (ball_subset_ball ?_)⟩
    nlinarith [hρ j]
  · -- slim line
    obtain ⟨y, hy1, hy2⟩ := hmeet
    have hsl1 : tsupport (L.slim.cutoff_BCNT j) ⊆ closedBall j ((910000 * Δ) * ρ j) := by
      rw [show (910000 * Δ) * ρ j = 91 / 100 * (10 ^ 6 * Δ) * ρ j by ring]
      exact L.slim.tsupport_cutoff_subset_BCNT j
    have hm : (closedBall j ((910000 * Δ) * ρ j) ∩ ball i ((20 * Δ) * ρ i)).Nonempty :=
      ⟨y, hsl1 hy1, hy2⟩
    obtain ⟨h1, h2, h3, h4⟩ := support_meeting_sharp_bounds hρL (hρ i) (hρ j) (a := 20 * Δ)
      (c := 910000 * Δ) (by positivity) (by positivity) (by rw [hc]; nlinarith)
      (by rw [hc]; nlinarith) hm
    have hpi := mul_pos hΔ0 (hρ i)
    have hpj := mul_pos hΔ0 (hρ j)
    have hsub : ball i (20 * Δ * ρ i) ⊆ ball j (92 / 100 * (1000000 * Δ) * ρ j) :=
      (h4 (20 * Δ) (by positivity)).trans (ball_subset_ball (by nlinarith))
    refine ⟨h1, h2, h3.trans_le (by nlinarith), hsub,
      (L.slim.centre j hj).contMDiffOn_coord_BAUGA.mono (ball_subset_ball ?_)⟩
    nlinarith
  · -- the original enlargement
    have hcut := L.edgeB.cutoff_eq_one_of_le_BCF2K hΔ0 hi hx hcx hFx
    have hsupp : x ∈ tsupport (L.edgeB.cutoff_BAUGA i) := by
      refine subset_tsupport _ ?_
      rw [mem_support, hcut]
      exact one_ne_zero
    have h14 := (L.tsupport_edgeB_cutoff_subset_BAUGA hΛ hΔ0 hμ hτ hΔΛ hi).1 hsupp
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
    exact zero_supports_meeting_ball_shell_BAUGP Z hρL he hT0 i (by positivity) hsmall

end Row

section General

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}
  {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ}
  {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- On `D_i` every actual edge cutoff outside EGP02's list `J_e` vanishes. -/
theorem egp02_edge_cutoff_eq_zero_of_unlisted_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) {i j x : X}
    (hj : j ∈ L.edgeB.centres) (hjl : j ∉ egpEdgeList_BAUGP L i) (hx : x ∈ ball i (20 * Δ * ρ i)) :
    L.edgeB.cutoff_BAUGA j x = 0 := by
  by_contra hne
  exact hjl ⟨hj, x, subset_tsupport _ hne, hx⟩

end General

end DifferentialGeometry.Geometry.Collapse
