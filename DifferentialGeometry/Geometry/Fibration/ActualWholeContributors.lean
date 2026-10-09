import DifferentialGeometry.Geometry.Fibration.ActualWholeSupportCount
import DifferentialGeometry.Geometry.Fibration.ActualFirstComparisonList
import DifferentialGeometry.Geometry.Fibration.ActualOriginalSlabs

/-!
# Whole contributor lists of the original charts at a reference ball (E-free part of GAF04–06)

Lane C14-FIBRE-PRE, class-(b) derived lemma of dispositions-task53 ("whole-reference-ball
support-list bound (pointwise multiplicity is not it)"); review 53 §2.1 / §10.2: GAF04–07 need the
whole-contributor lemmas, which do not depend on the adjusted map `E`. On the final closed family
`LocalChartPacketsC14Z`, for ANY reference set `D ⊆ B(x, 10ρ(x))` (e.g. GAF04's contributor windows
or the base point neighbourhoods of GAF05–07):

* `LocalChartPacketsC14Z.whole_contributors_FPRE`: the circle, edge and slim charts whose ACTUAL
  closed supports meet `D` are among TCP01's lists at `x`; they form finite lists of total size at
  most the early constant `N_TCP` (`tcp01_support_count_C14`, reused, not re-proved), and at most
  one zero support meets `D`.
* `LocalChartPacketsC14Z.whole_contributors_radius_FPRE`: at a reference ball `B(x, RΔρ(x))` of ANY
  radius (FC08 kernel `whole_count_of_buffer_CNT`, reused) the slim and edge lists are bounded by
  FC08's volume ratio.
* `buffer_ratio_of_support_meet_FPRE` (kernel, slow variation of a `Λ`-Lipschitz scale) and
  `LocalChartPacketsC14Z.whole_contributor_buffer_FPRE`: every listed chart centre `i` lies in a
  fixed buffer of `x` measured in `ρ(x)` (`d(i, x) < (10 + 1.01·C)ρ(x)` with the support radius
  `C = 102`, `100Δ`, `.91·10⁶Δ`), and `ρ(i)/ρ(x) ∈ (.99, 1.01)`.
* `LocalChartPacketsC14Z.circle_slab_subset_tsupport_FPRE`,
  `LocalChartPacketsC14Z.slim_slab_subset_tsupport_FPRE`: the whole original slab `{‖η_i‖ ≤ 8}`
  (circle) / `{|η_i| ≤ 8·10⁵Δ}` (slim) lies in the closed support of the original cutoff (it is in
  the plateau), so every chart whose whole slab meets `D` is a listed contributor.
* consumer `whole_contributors_pempty_FPRE` on the inhabitant over `PEmpty`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- **Slow variation at a support meeting** (kernel): if `d(i, x) < 10ρ(x) + Cρ(i)` for a
`Λ`-Lipschitz positive scale with `Λ(10 + 2C) < 1/100`, then
`ρ(i)/ρ(x) ∈ (.99, 1.01)` and `d(i, x) < (10 + 1.01·C)ρ(x)`. -/
theorem buffer_ratio_of_support_meet_FPRE {Y : Type*} [PseudoMetricSpace Y] {ρ : Y → ℝ} {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hρL : LipschitzWith (Real.toNNReal Λ) ρ) {i x : Y} (hx : 0 < ρ x)
    {C : ℝ} (hC : 0 ≤ C) (hd : dist i x < 10 * ρ x + C * ρ i)
    (hsmall : Λ * (10 + 2 * C) < 1 / 100) :
    ρ i / ρ x ∈ Ioo (99 / 100 : ℝ) (101 / 100) ∧ dist i x < (10 + 101 / 100 * C) * ρ x := by
  have hl := hρL.dist_le_mul i x
  rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at hl
  have hle : ρ i - ρ x ≤ Λ * dist i x := (le_abs_self _).trans hl
  have hΛd : Λ * dist i x ≤ Λ * (10 * ρ x + C * ρ i) := mul_le_mul_of_nonneg_left hd.le hΛ
  have h10 : Λ * 10 < 1 / 100 := by nlinarith
  have hρi : ρ i ≤ 2 * ρ x := by nlinarith
  have hd2 : dist i x ≤ (10 + 2 * C) * ρ x := by nlinarith
  have hratio := ratio_mem_Ioo_of_lipschitz_KA2 hΛ hρL hx hd2 hsmall
  refine ⟨hratio, ?_⟩
  have hρi' : ρ i < 101 / 100 * ρ x := by
    have := hratio.2
    rwa [div_lt_iff₀ hx] at this
  nlinarith

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **The whole contributor lists at a reference set `D ⊆ B(x, 10ρ(x))`**: the circle, edge and
slim charts whose ACTUAL closed supports meet `D` are among TCP01's lists at `x`, the three lists
are finite with total size at most `N_TCP = tcp01SupportBound`, and at most one zero support meets
`D` (TCP01's count `tcp01_support_count_C14`, reused). -/
theorem LocalChartPacketsC14Z.whole_contributors_FPRE
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) {x : X} {D : Set X} (hD : D ⊆ ball x (10 * ρ x)) :
    {i | i ∈ P.circle.centres ∧ (tsupport (P.circle.cutoff i) ∩ D).Nonempty} ⊆
        tcp01CircleList P.toLocalChartFamily x ∧
      {i | i ∈ P.edge.centres ∧ (tsupport (P.edge.cutoff i) ∩ D).Nonempty} ⊆
        tcp01EdgeList P.toLocalChartFamily x ∧
      {i | i ∈ P.slim.centres ∧ (tsupport (P.slim.cutoff i) ∩ D).Nonempty} ⊆
        tcp01SlimList P.toLocalChartFamily x ∧
      {i | i ∈ P.circle.centres ∧ (tsupport (P.circle.cutoff i) ∩ D).Nonempty}.Finite ∧
      {i | i ∈ P.edge.centres ∧ (tsupport (P.edge.cutoff i) ∩ D).Nonempty}.Finite ∧
      {i | i ∈ P.slim.centres ∧ (tsupport (P.slim.cutoff i) ∩ D).Nonempty}.Finite ∧
      {i | i ∈ P.circle.centres ∧ (tsupport (P.circle.cutoff i) ∩ D).Nonempty}.ncard +
          {i | i ∈ P.edge.centres ∧ (tsupport (P.edge.cutoff i) ∩ D).Nonempty}.ncard +
          {i | i ∈ P.slim.centres ∧ (tsupport (P.slim.cutoff i) ∩ D).Nonempty}.ncard ≤
        tcp01SupportBound ∧
      {k | ∃ hk : k ∈ P.zero.centres, (tsupport (fun y => Calculus.annularCutoff
          Calculus.cutoffProfile ((P.zero.zero k hk).radial y)) ∩ D).Nonempty}.ncard ≤ 1 := by
  obtain ⟨hcount, hzero⟩ :=
    tcp01_support_count_C14 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 hΛ hΔ hLΛ hLmax he
      hT x
  have hc : {i | i ∈ P.circle.centres ∧ (tsupport (P.circle.cutoff i) ∩ D).Nonempty} ⊆
      tcp01CircleList P.toLocalChartFamily x := fun i hi =>
    ⟨hi.1, hi.2.mono (inter_subset_inter_right _ hD)⟩
  have hed : {i | i ∈ P.edge.centres ∧ (tsupport (P.edge.cutoff i) ∩ D).Nonempty} ⊆
      tcp01EdgeList P.toLocalChartFamily x := fun i hi =>
    ⟨hi.1, hi.2.mono (inter_subset_inter_right _ hD)⟩
  have hs : {i | i ∈ P.slim.centres ∧ (tsupport (P.slim.cutoff i) ∩ D).Nonempty} ⊆
      tcp01SlimList P.toLocalChartFamily x := fun i hi =>
    ⟨hi.1, hi.2.mono (inter_subset_inter_right _ hD)⟩
  have hfc := tcp01CircleList_finite_CNT P.toLocalChartFamily x
  have hfe := tcp01EdgeList_finite_CNT P.toLocalChartFamily x
  have hfs := tcp01SlimList_finite_CNT P.toLocalChartFamily x
  have hz : {k | ∃ hk : k ∈ P.zero.centres, (tsupport (fun y => Calculus.annularCutoff
      Calculus.cutoffProfile ((P.zero.zero k hk).radial y)) ∩ D).Nonempty} ⊆
      zeroMeetingList P.zero x 10 := fun k ⟨hk, hne⟩ =>
    ⟨hk, hne.mono (inter_subset_inter_right _ hD)⟩
  have hfz : (zeroMeetingList P.zero x 10).Finite :=
    P.zero.finite_centres.subset fun k ⟨hk, _⟩ => hk
  have h1 := Set.ncard_le_ncard hc hfc
  have h2 := Set.ncard_le_ncard hed hfe
  have h3 := Set.ncard_le_ncard hs hfs
  refine ⟨hc, hed, hs, hfc.subset hc, hfe.subset hed, hfs.subset hs, by omega,
    (Set.ncard_le_ncard hz hfz).trans hzero⟩

/-- **Whole contributor lists at a reference ball of ANY radius** (FC08 kernel
`whole_count_of_buffer_CNT`, reused): for `D ⊆ B(x, RΔρ(x))`, `R ≥ 0`, with the scale budget
`Λ·max(RΔ, 910000Δ) ≤ 1/4` and the curvature buffer `4(R + 2·910000 + 1/3)Δ ≤ Lmax`, the slim and
edge charts whose actual closed supports meet `D` number at most `V(4(R+2C+1/3))/V(1/3)`
(`C = 910000`, `100`; `V = modelVolume (-1) 3`), a bound independent of the member. -/
theorem LocalChartPacketsC14Z.whole_contributors_radius_FPRE
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM)
    (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) {R : ℝ} (hR : 0 ≤ R)
    (hbudget : Λ * max (R * Δ) (910000 * Δ) ≤ 1 / 4)
    (hL : 4 * (R + 2 * 910000 + 1 / 3) * Δ ≤ Lmax) {x : X} {D : Set X}
    (hD : D ⊆ ball x (R * Δ * ρ x)) :
    ({i | i ∈ P.slim.centres ∧ (tsupport (P.slim.cutoff i) ∩ D).Nonempty}.ncard : ℝ) ≤
        modelVolume (-(1 ^ 2)) 3 (4 * (R + 2 * 910000 + 1 / 3)) /
          modelVolume (-(1 ^ 2)) 3 (1 / 3) ∧
      ({i | i ∈ P.edge.centres ∧ (tsupport (P.edge.cutoff i) ∩ D).Nonempty}.ncard : ℝ) ≤
        modelVolume (-(1 ^ 2)) 3 (4 * (R + 2 * 100 + 1 / 3)) /
          modelVolume (-(1 ^ 2)) 3 (1 / 3) := by
  have hS := P.toLocalChartFamilyQ.whole_count_of_buffer_CNT hΛ P.slim.finite_centres
    (fun j => tsupport (P.slim.cutoff j)) (R := R) (C := 910000) hΔ hR (by norm_num) hbudget hL
    (fun j hj => (fc18_slim_row P.toLocalChartFamily hΔ hj).1) P.slim.disjoint_centres x
  have hmax : max (R * Δ) (100 * Δ) ≤ max (R * Δ) (910000 * Δ) :=
    max_le_max le_rfl (by nlinarith)
  have hE := P.toLocalChartFamilyQ.whole_count_of_buffer_CNT hΛ P.edge.finite_centres
    (fun j => tsupport (P.edge.cutoff j)) (R := R) (C := 100) hΔ hR (by norm_num)
    ((mul_le_mul_of_nonneg_left hmax hΛ).trans hbudget) (by nlinarith)
    (fun j _ => P.edge.tsupport_cutoff_subset j) P.edge.disjoint_centres x
  have hsl : {i | i ∈ P.slim.centres ∧ (tsupport (P.slim.cutoff i) ∩ D).Nonempty} ⊆
      {j | j ∈ P.slim.centres ∧ (tsupport (P.slim.cutoff j) ∩ ball x (R * Δ * ρ x)).Nonempty} :=
    fun i hi => ⟨hi.1, hi.2.mono (inter_subset_inter_right _ hD)⟩
  have hed : {i | i ∈ P.edge.centres ∧ (tsupport (P.edge.cutoff i) ∩ D).Nonempty} ⊆
      {j | j ∈ P.edge.centres ∧ (tsupport (P.edge.cutoff j) ∩ ball x (R * Δ * ρ x)).Nonempty} :=
    fun i hi => ⟨hi.1, hi.2.mono (inter_subset_inter_right _ hD)⟩
  have h1 := Set.ncard_le_ncard hsl (P.slim.finite_centres.subset fun _ hj => hj.1)
  have h2 := Set.ncard_le_ncard hed (P.edge.finite_centres.subset fun _ hj => hj.1)
  exact ⟨(Nat.cast_le.mpr h1).trans hS, (Nat.cast_le.mpr h2).trans hE⟩

/-- **Every listed contributor is in a fixed buffer of `x` with comparable scale**: for
`D ⊆ B(x, 10ρ(x))` (`0 ≤ Λ`, `1 ≤ Δ`, `10⁶ΔΛ < 10⁻⁵`), a circle / edge / slim centre `i` whose
closed support meets `D` satisfies `ρ(i)/ρ(x) ∈ (.99, 1.01)` and `d(i, x) < (10 + 1.01·C)ρ(x)`
with `C = 102`, `100Δ`, `.91·10⁶Δ` respectively. -/
theorem LocalChartPacketsC14Z.whole_contributor_buffer_FPRE
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) {x : X} {D : Set X}
    (hD : D ⊆ ball x (10 * ρ x)) :
    (∀ i ∈ P.circle.centres, (tsupport (P.circle.cutoff i) ∩ D).Nonempty →
      ρ i / ρ x ∈ Ioo (99 / 100 : ℝ) (101 / 100) ∧ dist i x < (10 + 101 / 100 * 102) * ρ x) ∧
    (∀ i ∈ P.edge.centres, (tsupport (P.edge.cutoff i) ∩ D).Nonempty →
      ρ i / ρ x ∈ Ioo (99 / 100 : ℝ) (101 / 100) ∧
        dist i x < (10 + 101 / 100 * (100 * Δ)) * ρ x) ∧
    (∀ i ∈ P.slim.centres, (tsupport (P.slim.cutoff i) ∩ D).Nonempty →
      ρ i / ρ x ∈ Ioo (99 / 100 : ℝ) (101 / 100) ∧
        dist i x < (10 + 101 / 100 * (910000 * Δ)) * ρ x) := by
  have hx := hρ x
  have hΔ0 : 0 < Δ := by linarith
  have key : ∀ (i : X) (C : ℝ) (S : Set X), S ⊆ closedBall i (C * ρ i) → (S ∩ D).Nonempty →
      dist i x < 10 * ρ x + C * ρ i := by
    intro i C S hS ⟨y, hyS, hyD⟩
    have h1 := mem_closedBall.mp (hS hyS)
    have h2 := mem_ball.mp (hD hyD)
    calc dist i x ≤ dist y i + dist y x := by
          have := dist_triangle i y x
          rw [dist_comm i y] at this
          exact this
      _ < C * ρ i + 10 * ρ x := by linarith
      _ = 10 * ρ x + C * ρ i := by ring
  refine ⟨fun i hi hne => ?_, fun i hi hne => ?_, fun i hi hne => ?_⟩
  · exact buffer_ratio_of_support_meet_FPRE hΛ P.lipschitz_scale hx (by norm_num)
      (key i 102 _ (P.circle.tsupport_cutoff_subset_closedBall hi) hne) (by nlinarith)
  · exact buffer_ratio_of_support_meet_FPRE hΛ P.lipschitz_scale hx (by positivity)
      (key i (100 * Δ) _ (fun y hy => by
        have := P.edge.tsupport_cutoff_subset i hy
        rw [mem_closedBall] at this ⊢
        linarith) hne) (by nlinarith)
  · exact buffer_ratio_of_support_meet_FPRE hΛ P.lipschitz_scale hx (by positivity)
      (key i (910000 * Δ) _ (fc18_slim_row P.toLocalChartFamily hΔ0 hi).1 hne) (by nlinarith)

/-- **The whole original circle slab `{‖η_i‖ ≤ 8}` lies in the closed support of the original
cutoff** (it is in the plateau `Φ = 1`); so a circle chart whose whole slab meets `D` is a listed
contributor at `D`. -/
theorem LocalChartPacketsC14Z.circle_slab_subset_tsupport_FPRE
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {i : X} (hi : i ∈ P.circle.centres) :
    {y | y ∈ ball i (200 * ρ i) ∧ ‖cgpCircleCoord P.toLocalChartFamily i hi y‖ ≤ 8} ⊆
      tsupport (P.circle.cutoff i) := by
  have hr := hρ i
  have hone : ∀ y ∈ @ball X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hr)).toPseudoMetricSpace i 200,
      ‖cgpCircleCoord P.toLocalChartFamily i hi y‖ ≤ 8 → P.circle.cutoff i y = 1 :=
    P.circle.cutoff_eq_one i hi
  intro y hy
  refine subset_tsupport _ ?_
  rw [mem_support, hone y ((mem_ball_rescale_iff_FPRE (m := mX) hr (k := 200)).mpr hy.1) hy.2]
  exact one_ne_zero

/-- **The whole original slim slab `{|η_i| ≤ 8·10⁵Δ}` lies in the closed support of the original
cutoff** (LC85's plateau); so a slim chart whose whole slab meets `D` is a listed contributor. -/
theorem LocalChartPacketsC14Z.slim_slab_subset_tsupport_FPRE
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {i : X} (hi : i ∈ P.slim.centres) :
    {y | y ∈ ball i (10 ^ 6 * Δ * ρ i) ∧ |(P.slim.centre i hi).coord y| ≤ 8 * 10 ^ 5 * Δ} ⊆
      tsupport (P.slim.cutoff i) := by
  intro y hy
  refine subset_tsupport _ ?_
  rw [mem_support, slimFamily_cutoff_eq_KA2 P.toLocalChartFamily hi,
    SlimCentre.cutoff_eq_one_of_abs_coord_le _ hy.1 hy.2]
  exact one_ne_zero

section Consumer

/-- The metric on `PEmpty` (the same term as the instance of `metricPEmpty_FAM`). -/
local instance metricSpacePEmpty_FPRE3 : MetricSpace PEmpty.{1} :=
  (MetricSpace.induced (PEmpty.elim : PEmpty.{1} → ℝ) (fun x => x.elim)
    inferInstance).replaceTopology (by ext s; simp only [Set.eq_empty_of_isEmpty s, isOpen_empty])

/-- The empty three-manifold (the same term as the instance of `metricPEmpty_FAM`). -/
local instance chartedSpacePEmpty_FPRE3 : ChartedSpace E3 PEmpty.{1} :=
  ChartedSpace.empty E3 PEmpty.{1}

/-- **Consumer on the structural inhabitant over `PEmpty`**: the final family over the empty
three-manifold has, at every reference set `D ⊆ B(x, 10ρ(x))`, whole contributor lists of total
size at most `N_TCP`, buffered slim contributors, and slim slabs inside the supports. -/
theorem whole_contributors_pempty_FPRE (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ) (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) :
    ∃ P : LocalChartPacketsC14Z PEmpty.{1} metricPEmpty_FAM (fun a => a.elim) (fun a => a.elim)
        (fun a => a.elim) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
        manifoldOrientationPEmpty_FAMZ,
      ∀ (x : PEmpty.{1}) (D : Set PEmpty.{1}),
        D ⊆ ball x (10 * (fun a : PEmpty.{1} => a.elim) x) →
        {i | i ∈ P.circle.centres ∧ (tsupport (P.circle.cutoff i) ∩ D).Nonempty}.ncard +
            {i | i ∈ P.edge.centres ∧ (tsupport (P.edge.cutoff i) ∩ D).Nonempty}.ncard +
            {i | i ∈ P.slim.centres ∧ (tsupport (P.slim.cutoff i) ∩ D).Nonempty}.ncard ≤
          tcp01SupportBound ∧
        ∀ i ∈ P.slim.centres, (tsupport (P.slim.cutoff i) ∩ D).Nonempty →
          (fun a : PEmpty.{1} => a.elim) i / (fun a : PEmpty.{1} => a.elim) x ∈
            Ioo (99 / 100 : ℝ) (101 / 100) := by
  obtain ⟨P⟩ := nonempty_localChartPacketsC14Z_pempty_FAMZ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax
    τ γ δ εr e T V vs ζ Λz manifoldOrientationPEmpty_FAMZ
  exact ⟨P, fun x D hD => ⟨(P.whole_contributors_FPRE hΛ hΔ hLΛ hLmax he hT hD).2.2.2.2.2.2.1,
    fun i hi hne => ((P.whole_contributor_buffer_FPRE hΛ hΔ hLΛ hD).2.2 i hi hne).1⟩⟩

end Consumer

end DifferentialGeometry.Geometry.Collapse
