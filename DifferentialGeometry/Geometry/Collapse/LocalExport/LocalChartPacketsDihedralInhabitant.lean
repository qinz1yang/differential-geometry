import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralZeroFamily
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralCurvature
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Gradient
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound

/-!
# A nonempty inhabitant of the closed chapter-14 families (lane C14-CHAIN-INST)

The only compiled inhabitants of `LocalChartPackets…` so far live over `X = PEmpty`
(`LocalChartPacketsInhabitants.lean`, `LocalChartPacketsC14ZeroTypesInhabitant.lean`). Structures
with a field of type `… → X` (for instance the selections of `Gaf02Chain`) have no inhabitant there,
so a nonempty fixture is needed. This file gives one on an actual closed three-manifold.

The source is `RP³ # RP³` (`dihedralZeroSource`) with the unit dihedral metric
(`dihedralMetric 1 1`, sectional curvature `≥ 0`) and its induced length metric (`hmetric` by
`inducedMetricSpace_hmetric`). The scale is constant, `ρ ≡ R = diam X + 1`, so the rescaled source
has diameter `< 1`. Then:

* `not_kleinerLottApprox_prod_CHI`: no `β`-Kleiner–Lott map (`β ≤ 1/4`) from a space of radius
  `< 1` to a product with a factor that has a vector of norm `2`. Hence every point has splitting
  rank zero (`dihedralTiny_rank_zero_CHI`, for `β_j ≤ 1/4`, `j = 1, 2, 3`) and no point is a strong
  edge point (`dihedralTiny_not_isEdgePoint_CHI`, for `b ≤ 1/4`).
* The circle, slim and edge families are empty (`dihedralTinyCircle_CHI`, `dihedralTinySlim_CHI`,
  `dihedralTinyEdge_CHI`, `dihedralTinyFamilyE_CHI`; the curvature buffer from `sec ≥ 0`).
* One zero ball of radius `T·R` covers the source (`dihedralTinyZeroBall_CHI`,
  `dihedralTinyZeroFamily_CHI`). Its model is the source itself with identity charts, its cone is a
  point, and its radial function is the rescaled distance to the centre, for which every LC30 clause
  holds (`tiny_radial_spec_CHI`: the shells are empty and the cutoff vanishes).
* `dihedralTinyPackets_CHI : LocalChartPacketsC14 …`, `dihedralTinyPacketsC14D_CHI`,
  `dihedralTinyPacketsC14Z_CHI` (at the canonical orientation: the zero sublevels are the whole
  source, a compact model of type `RP³ # RP³`), and the base projection
  `dihedralTinyBasePackets_CHI : LocalChartPackets …`.

The parameter hypotheses are `β_j ≤ 1/4` (`j = 1, 2, 3`), `b ≤ 1/4`, `0 < δ < 1`, `0 ≤ εr`, `0 < e`,
`1000 ≤ T`, `1 ≤ δT` and `T ≤ V`. All other parameters are free.

The geometry is degenerate on purpose: no circle, slim or edge chart. The fixture tests the field
texts on a nonempty manifold. It is not geometric existence evidence; the producers are.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis.Calculus DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

universe uX uV uY

/-! ### The dihedral source with the unit dihedral metric -/

/-- The unit dihedral metric on `RP³ # RP³` (sectional curvature `≥ 0`). -/
abbrev dihedralTinyMetric_CHI : SmoothRiemannianMetric 𝓘(ℝ, E3) dihedralZeroSource :=
  dihedralMetric.{0} 1 1 one_pos one_pos

/-- The metric space of the unit dihedral metric (the induced length metric). Not an instance. -/
@[reducible] def dihedralTinyMetricSpace_CHI : MetricSpace dihedralZeroSource :=
  inducedMetricSpace dihedralTinyMetric_CHI

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- The induced metric is the Riemannian distance. -/
theorem dihedralTiny_hmetric_CHI : ∀ a b : dihedralZeroSource,
    riemannianEDistOf dihedralTinyMetric_CHI a b = ENNReal.ofReal (dist a b) :=
  inducedMetricSpace_hmetric dihedralTinyMetric_CHI

/-- The diameter of the source. -/
def dihedralTinyDiam_CHI : ℝ := Metric.diam (univ : Set dihedralZeroSource)

/-- Distances are bounded by the diameter. -/
theorem dist_le_dihedralTinyDiam_CHI (x y : dihedralZeroSource) :
    dist x y ≤ dihedralTinyDiam_CHI :=
  Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)

/-- The constant scale `R = diam + 1`. -/
def dihedralTinyScale_CHI : ℝ := dihedralTinyDiam_CHI + 1

/-- Distances are below the scale. -/
theorem dist_lt_dihedralTinyScale_CHI (x y : dihedralZeroSource) :
    dist x y < dihedralTinyScale_CHI := by
  have h := dist_le_dihedralTinyDiam_CHI x y
  rw [dihedralTinyScale_CHI]
  linarith

/-- The scale is positive. -/
theorem dihedralTinyScale_pos_CHI : 0 < dihedralTinyScale_CHI :=
  lt_of_le_of_lt dist_nonneg (dist_lt_dihedralTinyScale_CHI (Classical.arbitrary _)
    (Classical.arbitrary _))

/-- The constant scale function `ρ ≡ R`. -/
def dihedralTinyRho_CHI : dihedralZeroSource → ℝ := fun _ => dihedralTinyScale_CHI

/-- The scale function is positive. -/
theorem dihedralTinyRho_pos_CHI : ∀ p, 0 < dihedralTinyRho_CHI p :=
  fun _ => dihedralTinyScale_pos_CHI

/-- The base point of the source (the centre of its one zero ball). -/
def dihedralTinyBase_CHI : dihedralZeroSource := Classical.arbitrary _

/-! ### No splitting at the scale `ρ` -/

/-- A space within distance `1` of `p` has no `β`-Kleiner–Lott map at `p` to a product with a
factor containing a vector of norm `2`, for `β ≤ 1/4`. -/
theorem not_kleinerLottApprox_prod_CHI {X : Type uX} [MetricSpace X] {V : Type uV} {Y : Type uY}
    [NormedAddCommGroup V] [MetricSpace Y] (v : V) (hv : ‖v‖ = 2) {p : X} {q : Y} {β : ℝ}
    (hβ : β ≤ 1 / 4) (hX : ∀ x, dist x p < 1)
    (f : KleinerLottApprox p (WithLp.toLp 2 ((0 : V), q)) β) : False := by
  have hβ0 := f.error_pos
  have hy : dist (WithLp.toLp 2 (v, q) : WithLp 2 (V × Y)) (WithLp.toLp 2 ((0 : V), q)) = 2 := by
    rw [WithLp.prod_dist_eq_add (by norm_num)]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_self, dist_zero_right, hv,
      ENNReal.toReal_ofNat]
    rw [Real.zero_rpow two_ne_zero, add_zero, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hinv : 4 ≤ β⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hβ0]; linarith
  obtain ⟨x, hx, hxy⟩ := f.coverage_witness (WithLp.toLp 2 (v, q)) (by rw [hy]; linarith)
  have hr := f.radial_error x hx
  have h1 := dist_triangle (WithLp.toLp 2 (v, q) : WithLp 2 (V × Y)) (f.toFun x)
    (WithLp.toLp 2 ((0 : V), q))
  have h2 := hX x
  rw [hy] at h1
  have h3 := (abs_le.mp hr).2
  linarith

/-- At the scale `ρ ≡ R` every point is within rescaled distance `1`. -/
theorem dihedralTiny_rescaled_dist_lt_CHI (p x : dihedralZeroSource) :
    @dist dihedralZeroSource (dihedralTinyMetricSpace_CHI.rescale (dihedralTinyRho_CHI p)⁻¹
      (inv_pos.mpr (dihedralTinyRho_pos_CHI p))).toDist x p < 1 := by
  change (dihedralTinyScale_CHI)⁻¹ * dist x p < 1
  rw [inv_mul_lt_iff₀ dihedralTinyScale_pos_CHI, mul_one]
  exact dist_lt_dihedralTinyScale_CHI x p

/-- **Every point has splitting rank zero** at `ρ ≡ R` when `β_j ≤ 1/4` (`j = 1, 2, 3`). -/
theorem dihedralTiny_rank_zero_CHI {β : ℕ → ℝ} (hβ : ∀ j, 1 ≤ j → j ≤ 3 → β j ≤ 1 / 4)
    (p : dihedralZeroSource) :
    scaledSplittingRank.{0, 0} dihedralTinyRho_CHI dihedralTinyRho_pos_CHI β p = 0 := by
  rw [scaledSplittingRank_eq_iff]
  refine ⟨by norm_num, fun h => absurd rfl h, fun j hj hj3 => ?_⟩
  rintro ⟨Y, mY, q, ⟨f⟩⟩
  have hv : ‖(EuclideanSpace.single (⟨0, hj⟩ : Fin j) (2 : ℝ) : EuclideanSpace ℝ (Fin j))‖ = 2 := by
    simp
  exact @not_kleinerLottApprox_prod_CHI dihedralZeroSource
    (dihedralTinyMetricSpace_CHI.rescale (dihedralTinyRho_CHI p)⁻¹
      (inv_pos.mpr (dihedralTinyRho_pos_CHI p))) _ _ _ mY _ hv p q (β j) (hβ j hj hj3)
    (fun x => dihedralTiny_rescaled_dist_lt_CHI p x) f

/-- Every point lies in the zero stratum. -/
theorem dihedralTiny_mem_stratum_zero_CHI {β : ℕ → ℝ} (hβ : ∀ j, 1 ≤ j → j ≤ 3 → β j ≤ 1 / 4)
    (p : dihedralZeroSource) :
    p ∈ scaledSplittingStratum.{0, 0} dihedralTinyRho_CHI dihedralTinyRho_pos_CHI β 0 :=
  dihedralTiny_rank_zero_CHI hβ p

/-- No point lies in a positive stratum. -/
theorem dihedralTiny_not_mem_stratum_CHI {β : ℕ → ℝ} (hβ : ∀ j, 1 ≤ j → j ≤ 3 → β j ≤ 1 / 4)
    {k : Fin 4} (hk : k ≠ 0) (p : dihedralZeroSource) :
    p ∉ scaledSplittingStratum.{0, 0} dihedralTinyRho_CHI dihedralTinyRho_pos_CHI β k := by
  intro hp
  have h0 := dihedralTiny_rank_zero_CHI hβ p
  change scaledSplittingRank.{0, 0} dihedralTinyRho_CHI dihedralTinyRho_pos_CHI β p = k.val at hp
  rw [h0] at hp
  exact hk (Fin.ext hp.symm)

/-- No point is a strong edge point at `ρ ≡ R` when `b ≤ 1/4`. -/
theorem dihedralTiny_not_isEdgePoint_CHI {Δ b s : ℝ} (hb : b ≤ 1 / 4) (a : dihedralZeroSource) :
    ¬ @isEdgePoint.{0, 0} dihedralZeroSource
      (dihedralTinyMetricSpace_CHI.rescale (dihedralTinyRho_CHI a)⁻¹
        (inv_pos.mpr (dihedralTinyRho_pos_CHI a))) a Δ b s := by
  rintro ⟨Y, mY, q, C, hC, -, ⟨F⟩, -⟩
  exact @not_kleinerLottApprox_prod_CHI dihedralZeroSource
    (dihedralTinyMetricSpace_CHI.rescale (dihedralTinyRho_CHI a)⁻¹
      (inv_pos.mpr (dihedralTinyRho_pos_CHI a))) _ _ _ mY (2 : ℝ) (by norm_num) a q b hb
    (fun x => dihedralTiny_rescaled_dist_lt_CHI a x) F

/-- The multiplicity bounds of the families are nonnegative (negative model curvature). -/
theorem dihedralTiny_multiplicity_ratio_nonneg_CHI (K r₁ r₂ : ℝ) (hK : K < 0) (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) : 0 ≤ modelVolume K 3 r₁ / modelVolume K 3 r₂ :=
  div_nonneg (modelVolume_pos (by norm_num) h₁ ⟨h₁.le, fun h => absurd h (not_lt.mpr hK.le)⟩).le
    (modelVolume_pos (by norm_num) h₂ ⟨h₂.le, fun h => absurd h (not_lt.mpr hK.le)⟩).le

/-- **LC30's radial clauses for a tiny ball**: if every point is within `r/1000` of `c`, the
rescaled distance to `c` satisfies every clause of `ZeroModelBall.radial_spec` at the scale `r`
(the shell and the annuli are empty and the cutoff vanishes identically). -/
theorem tiny_radial_spec_CHI {M : Type} [mM : MetricSpace M] [ChartedSpace E3 M]
    [IsManifold 𝓘(ℝ, E3) ∞ M] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (c : M) {r ε e : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (he : 0 < e) (hsmall : ∀ x, dist x c < r / 1000) :
    letI := mM.rescale r⁻¹ (inv_pos.mpr hr)
    let gR := scaleMetric (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g
    LipschitzWith (Real.toNNReal (1 + ε)) (fun x => dist x c) ∧
      (∃ O : Set M, IsOpen O ∧ {x : M | 3 / 40 ≤ dist x c ∧ dist x c ≤ 11} ⊆ O ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun x => dist x c) O) ∧
      (∀ x, |(fun x => dist x c) x - Metric.infDist x {c}| < e) ∧
      (∀ x, x ∉ {x : M | 1 / 20 < dist x c ∧ dist x c < 20} →
        (fun x => dist x c) x = Metric.infDist x {c}) ∧
      (∀ x y, |((fun x => dist x c) x - Metric.infDist x {c}) -
          ((fun x => dist x c) y - Metric.infDist y {c})| ≤ ε * dist x y) ∧
      (∀ x, 0 ≤ (fun x => dist x c) x) ∧ (fun x => dist x c) c = 0 ∧
      (∀ q ∈ {x : M | 1 / 10 ≤ dist x c ∧ dist x c ≤ 10},
        1 - ε ≤ Real.sqrt (gR.inner q (gradFun gR (fun x => dist x c) q)
            (gradFun gR (fun x => dist x c) q)) ∧
          Real.sqrt (gR.inner q (gradFun gR (fun x => dist x c) q)
            (gradFun gR (fun x => dist x c) q)) ≤ 1 + ε) ∧
      (∀ x, (fun x => dist x c) x ∈ Icc (1 / 5 : ℝ) 2 →
        1 / 5 - e < dist x c ∧ dist x c < 2 + e) ∧
      (fun x => dist x c) ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆
        {x : M | 1 / 10 ≤ dist x c ∧ dist x c ≤ 10} ∧
      (∃ O' : Set M, IsOpen O' ∧ (fun x => dist x c) ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun x => dist x c) O' ∧
          ∀ q ∈ O', gradFun gR (fun x => dist x c) q ≠ 0) ∧
      ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
        ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
          (fun x => annularCutoff cutoffProfile ((fun x => dist x c) x)) ∧
        (∀ x, annularCutoff cutoffProfile ((fun x => dist x c) x) ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, (fun x => dist x c) x ∈ Icc (3 / 10 : ℝ) (4 / 5) →
          annularCutoff cutoffProfile ((fun x => dist x c) x) = 1) ∧
        tsupport (fun x => annularCutoff cutoffProfile ((fun x => dist x c) x)) ⊆
          {x : M | 1 / 5 - e < dist x c ∧ dist x c < 9 / 10 + e} ∧
        ∀ q, Real.sqrt (gR.inner q
          (gradFun gR (fun x => annularCutoff cutoffProfile ((fun x => dist x c) x)) q)
          (gradFun gR (fun x => annularCutoff cutoffProfile ((fun x => dist x c) x)) q)) ≤
            L * (1 + ε) := by
  intro gR
  have hd : ∀ x, @dist M (mM.rescale r⁻¹ (inv_pos.mpr hr)).toDist x c < 1 / 1000 := by
    intro x
    change r⁻¹ * @dist M mM.toDist x c < 1 / 1000
    have h := hsmall x
    rw [inv_mul_lt_iff₀ hr]
    linarith
  have hd0 : ∀ x, 0 ≤ @dist M (mM.rescale r⁻¹ (inv_pos.mpr hr)).toDist x c := fun x =>
    @dist_nonneg M (mM.rescale r⁻¹ (inv_pos.mpr hr)).toPseudoMetricSpace x c
  have hinf : ∀ x, @Metric.infDist M (mM.rescale r⁻¹ (inv_pos.mpr hr)).toPseudoMetricSpace x {c} =
      @dist M (mM.rescale r⁻¹ (inv_pos.mpr hr)).toDist x c := fun x =>
    @Metric.infDist_singleton M (mM.rescale r⁻¹ (inv_pos.mpr hr)).toPseudoMetricSpace x c
  have hzero : (fun x => annularCutoff cutoffProfile
      (@dist M (mM.rescale r⁻¹ (inv_pos.mpr hr)).toDist x c)) = fun _ => 0 := by
    funext x
    exact annularCutoff_eq_zero_of_le (fun t ht => cutoffProfile_eq_zero ht)
      (by linarith [hd x])
  obtain ⟨L, hL, hLd⟩ := exists_abs_deriv_annularCutoff_le cutoffProfile_contDiff
    (fun t ht => cutoffProfile_eq_zero ht)
  have h1 : Real.toNNReal (1 + ε) = 1 + Real.toNNReal ε := by
    rw [Real.toNNReal_add zero_le_one hε, Real.toNNReal_one]
  refine ⟨?_, ⟨∅, isOpen_empty, fun x hx => ?_, contMDiffOn_empty⟩, fun x => ?_, fun x _ => ?_,
    fun x y => ?_, hd0, @dist_self M (mM.rescale r⁻¹ (inv_pos.mpr hr)).toPseudoMetricSpace c,
    fun q hq => ?_, fun x hx => ?_, fun x hx => ?_,
    ⟨∅, isOpen_empty, fun x hx => ?_, contMDiffOn_empty, fun q hq => hq.elim⟩,
    L, hL, hLd, ?_, ?_, fun x hx => ?_, ?_, fun q => ?_⟩
  · rw [h1]
    let _ : MetricSpace M := mM.rescale r⁻¹ (inv_pos.mpr hr)
    exact (LipschitzWith.dist_left c).weaken (le_add_of_nonneg_right zero_le)
  · linarith [hx.1, hd x]
  · rw [hinf, sub_self, abs_zero]; exact he
  · exact (hinf x).symm
  · rw [hinf, hinf, sub_self, sub_self, sub_self, abs_zero]
    exact mul_nonneg hε (@dist_nonneg M (mM.rescale r⁻¹ (inv_pos.mpr hr)).toPseudoMetricSpace x y)
  · linarith [hq.1, hd q]
  · linarith [hx.1, hd x]
  · linarith [hx.1, hd x]
  · linarith [show (1 / 5 : ℝ) ≤ @dist M (mM.rescale r⁻¹ (inv_pos.mpr hr)).toDist x c from hx.1,
      hd x]
  · rw [hzero]; exact contMDiff_const
  · intro x
    have hx := congrFun hzero x
    simp only at hx ⊢
    rw [hx]
    exact ⟨le_rfl, zero_le_one⟩
  · linarith [hx.1, hd x]
  · rw [hzero]
    intro x hx
    rw [show (fun _ : M => (0 : ℝ)) = 0 from rfl, tsupport_zero] at hx
    exact hx.elim
  · rw [hzero, DifferentialGeometry.Geometry.Connection.gradFun_zero]
    simp only [map_zero, Real.sqrt_zero]
    exact mul_nonneg hL (by linarith)


/-! ### The empty circle, slim and edge families -/

variable {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The empty circle family (no point of the two-stratum). -/
def dihedralTinyCircle_CHI (hβ : ∀ j, 1 ≤ j → j ≤ 3 → β j ≤ 1 / 4) :
    CircleFamily 𝓘(ℝ, E3) dihedralZeroSource dihedralTinyRho_CHI dihedralTinyRho_pos_CHI β where
  centres := ∅
  finite_centres := finite_empty
  centres_subset := empty_subset _
  disjoint_centres := pairwiseDisjoint_empty
  covers := fun p hp => absurd hp (dihedralTiny_not_mem_stratum_CHI hβ (by decide) p)
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
    exact dihedralTiny_multiplicity_ratio_nonneg_CHI _ _ _ (by norm_num) (by norm_num)
      (by norm_num)

/-- The empty slim family (no point of the one-stratum). -/
def dihedralTinySlim_CHI (hβ : ∀ j, 1 ≤ j → j ≤ 3 → β j ≤ 1 / 4) :
    SlimFamily dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
      dihedralTinyRho_CHI dihedralTinyRho_pos_CHI β Δ σs K where
  centres := ∅
  finite_centres := finite_empty
  centres_subset := empty_subset _
  disjoint_centres := pairwiseDisjoint_empty
  covers := fun p hp => absurd hp (dihedralTiny_not_mem_stratum_CHI hβ (by decide) p)
  centre := fun j hj => absurd hj (notMem_empty j)
  multiplicity := fun x => by
    rw [empty_inter, ncard_empty, Nat.cast_zero]
    exact dihedralTiny_multiplicity_ratio_nonneg_CHI _ _ _ (by norm_num) (by norm_num)
      (by norm_num)

/-- The empty edge family (no strong edge point, no point of the one-stratum). -/
def dihedralTinyEdge_CHI (hβ : ∀ j, 1 ≤ j → j ≤ 3 → β j ≤ 1 / 4) (hb : b ≤ 1 / 4) :
    EdgeFamily dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
      dihedralTinyRho_CHI dihedralTinyRho_pos_CHI β Δ σc μ b s b' s' ε γc βc where
  centres := ∅
  finite_centres := finite_empty
  strong := fun j hj => absurd hj (notMem_empty j)
  disjoint_centres := pairwiseDisjoint_empty
  covers_strong := fun a ha => absurd ha (dihedralTiny_not_isEdgePoint_CHI hb a)
  covers_nonslim := fun p hp => absurd hp (dihedralTiny_not_mem_stratum_CHI hβ (by decide) p)
  multiplicity := fun x => by
    rw [empty_inter, ncard_empty, Nat.cast_zero]
    exact dihedralTiny_multiplicity_ratio_nonneg_CHI _ _ _ (by norm_num) (by norm_num)
      (by norm_num)
  smoothing := fun _ => 0
  smoothing_nonneg := fun _ => le_rfl
  lipschitz_smoothing := (LipschitzWith.const (0 : ℝ)).weaken zero_le
  smoothing_value := fun p hp => absurd hp (notMem_empty p)
  chart := fun j hj => absurd hj (notMem_empty j)
  chart_center := fun j hj => absurd hj (notMem_empty j)

/-- **The LC87 family on the dihedral source** (empty circle, slim and edge families; every point
in the zero stratum). -/
def dihedralTinyFamilyE_CHI (hβ : ∀ j, 1 ≤ j → j ≤ 3 → β j ≤ 1 / 4) (hb : b ≤ 1 / 4) :
    LocalChartFamilyE dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
      dihedralTinyRho_CHI dihedralTinyRho_pos_CHI Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ where
  contMDiff_scale := contMDiff_const
  lipschitz_scale := (LipschitzWith.const dihedralTinyScale_CHI).weaken zero_le
  circle := dihedralTinyCircle_CHI hβ
  slim := dihedralTinySlim_CHI hβ
  edge := dihedralTinyEdge_CHI hβ hb
  exhaustion := fun x => Or.inl (dihedralTiny_mem_stratum_zero_CHI hβ x)
  circle_cutoff_eq := fun j hj => absurd hj (notMem_empty j)
  slim_cutoff_eq := fun j hj => absurd hj (notMem_empty j)
  sectional_buffer := fun _ _ _ _ y _ =>
    (dihedralMetric_sectional_nonneg 1 1 one_pos one_pos y).mono
      (neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg _)))
  edge_coarse := fun j hj => absurd hj (notMem_empty j)

/-! ### One zero ball covering the source -/

/-- The zero-ball radius `T·R` is positive. -/
theorem dihedralTiny_radius_pos_CHI (hT : 1000 ≤ T) : 0 < T * dihedralTinyScale_CHI :=
  mul_pos (by linarith) dihedralTinyScale_pos_CHI

/-- Distances are below a thousandth of the zero-ball radius. -/
theorem dihedralTiny_dist_lt_radius_CHI (hT : 1000 ≤ T) (x y : dihedralZeroSource) :
    dist x y < T * dihedralTinyScale_CHI / 1000 := by
  have h := dist_lt_dihedralTinyScale_CHI x y
  have hR := dihedralTinyScale_pos_CHI
  have h2 : dihedralTinyScale_CHI ≤ T * dihedralTinyScale_CHI / 1000 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- At the zero-ball scale, rescaled distances are at most `δ`. -/
theorem dihedralTiny_rescaled_dist_le_CHI (hT : 1000 ≤ T) (hδT : 1 ≤ δ * T)
    (x x' : dihedralZeroSource) :
    |@dist dihedralZeroSource (dihedralTinyMetricSpace_CHI.rescale (T * dihedralTinyScale_CHI)⁻¹
      (inv_pos.mpr (dihedralTiny_radius_pos_CHI hT))).toDist x x'| ≤ δ := by
  change |(T * dihedralTinyScale_CHI)⁻¹ * dist x x'| ≤ δ
  have hr := dihedralTiny_radius_pos_CHI hT
  have hx := dist_lt_dihedralTinyScale_CHI x x'
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) dist_nonneg), inv_mul_le_iff₀ hr]
  have h1 : dihedralTinyScale_CHI ≤ δ * (T * dihedralTinyScale_CHI) := by
    rw [← mul_assoc]
    nlinarith [dihedralTinyScale_pos_CHI]
  linarith

/-- The cone map of the zero ball: the constant map to the one-point cone (the rescaled source has
diameter `< δ`). -/
def dihedralTinyConeMap_CHI (hδ : 0 < δ) (hδ1 : δ < 1) (hT : 1000 ≤ T) (hδT : 1 ≤ δ * T)
    (c : dihedralZeroSource) :
    @KleinerLottApprox dihedralZeroSource PUnit.{1} (dihedralTinyMetricSpace_CHI.rescale
      (T * dihedralTinyScale_CHI)⁻¹ (inv_pos.mpr (dihedralTiny_radius_pos_CHI hT))) _ c
      PUnit.unit δ := by
  letI : MetricSpace dihedralZeroSource := dihedralTinyMetricSpace_CHI.rescale
    (T * dihedralTinyScale_CHI)⁻¹ (inv_pos.mpr (dihedralTiny_radius_pos_CHI hT))
  exact
    { error_pos := hδ
      error_lt_one := hδ1
      toFun := fun _ => PUnit.unit
      basepoint := rfl
      distortion := fun x _ x' _ => by
        rw [dist_self, zero_sub, abs_neg]
        exact dihedralTiny_rescaled_dist_le_CHI hT hδT x x'
      coverage := fun y _ => by
        refine (Metric.infDist_zero_of_mem ((mem_image _ _ _).mpr
          ⟨c, Metric.mem_ball_self (inv_pos.mpr hδ), Subsingleton.elim _ _⟩)).le.trans hδ.le }

/-- **The zero ball of radius `T·R` at `c`**: model `N = X` (identity charts), cone a point,
radial function the rescaled distance to `c`. -/
def dihedralTinyZeroBall_CHI (hδ : 0 < δ) (hδ1 : δ < 1) (hεr : 0 ≤ εr) (he : 0 < e)
    (hT : 1000 ≤ T) (hδT : 1 ≤ δ * T) (c : dihedralZeroSource) :
    ZeroModelBall 𝓘(ℝ, E3) dihedralZeroSource dihedralTinyMetric_CHI
      (fun _ : dihedralZeroSource => dihedralZeroSource) (fun _ : dihedralZeroSource => PUnit.{1})
      (fun _ => PUnit.unit) δ εr e where
  center := c
  radius := T * dihedralTinyScale_CHI
  radius_pos := dihedralTiny_radius_pos_CHI hT
  model := c
  coneMap := dihedralTinyConeMap_CHI hδ hδ1 hT hδT c
  radial := fun x => @dist dihedralZeroSource (dihedralTinyMetricSpace_CHI.rescale
    (T * dihedralTinyScale_CHI)⁻¹ (inv_pos.mpr (dihedralTiny_radius_pos_CHI hT))).toDist x c
  radial_spec := tiny_radial_spec_CHI dihedralTinyMetric_CHI c (dihedralTiny_radius_pos_CHI hT)
    hεr he (fun x => dihedralTiny_dist_lt_radius_CHI hT x c)
  modelChart := fun _ _ => (Diffeomorph.refl 𝓘(ℝ, E3) dihedralZeroSource ∞).toPartialDiffeomorph
  modelChart_source := fun ρ' hρ' => by
    refine (eq_univ_of_forall fun x => ?_).symm
    rw [mem_ball]
    have hx := dihedralTiny_dist_lt_radius_CHI hT x c
    have hr := dihedralTiny_radius_pos_CHI hT
    nlinarith [hρ'.1]
  modelChart_target := fun _ _ => rfl

/-- **The zero family**: one zero ball of radius `T·R` at the base point. -/
def dihedralTinyZeroFamily_CHI (hβ : ∀ j, 1 ≤ j → j ≤ 3 → β j ≤ 1 / 4) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hεr : 0 ≤ εr) (he : 0 < e) (hT : 1000 ≤ T) (hδT : 1 ≤ δ * T)
    (hTV : T ≤ V) :
    ZeroModelFamily 𝓘(ℝ, E3) dihedralZeroSource dihedralTinyMetric_CHI dihedralTinyRho_CHI
      dihedralTinyRho_pos_CHI β (fun _ : dihedralZeroSource => dihedralZeroSource)
      (fun _ : dihedralZeroSource => PUnit.{1}) (fun _ => PUnit.unit) δ εr e T V where
  centres := {dihedralTinyBase_CHI}
  finite_centres := finite_singleton _
  zero := fun i _ => dihedralTinyZeroBall_CHI hδ hδ1 hεr he hT hδT i
  zero_center := fun _ _ => rfl
  radius_mem := fun _ _ => ⟨le_rfl, mul_le_mul_of_nonneg_right hTV dihedralTinyScale_pos_CHI.le⟩
  disjoint := fun i hi j hj hij => absurd ((mem_singleton_iff.mp hi).trans
    (mem_singleton_iff.mp hj).symm) hij
  meets_stratum := fun i _ => ⟨i, mem_ball_self (dihedralTiny_radius_pos_CHI hT),
    dihedralTiny_mem_stratum_zero_CHI hβ i⟩
  covers_stratum := fun x _ => by
    refine mem_iUnion₂.mpr ⟨dihedralTinyBase_CHI, mem_singleton _, ?_⟩
    rw [mem_ball]
    have hx := dihedralTiny_dist_lt_radius_CHI hT x dihedralTinyBase_CHI
    change dist x dihedralTinyBase_CHI < T * dihedralTinyScale_CHI / 10
    have hr := dihedralTiny_radius_pos_CHI hT
    linarith
  one_end := fun _ _ K _ a₁ _ h₁ _ => absurd (isCompact_univ.isBounded.subset (subset_univ _)) h₁

/-! ### The final closed family on the dihedral source -/

/-- **A nonempty inhabitant of `LocalChartPacketsC14`** on the compact three-manifold
`RP³ # RP³` with the unit dihedral metric (sectional curvature `≥ 0`), at the constant scale
`ρ ≡ R = diam + 1`: every point has splitting rank zero (`β_j ≤ 1/4`), the circle, slim and edge
families are empty (`b ≤ 1/4`: no strong edge point), and one zero ball of radius `T·R` covers the
source (model the source itself with identity charts, cone a point). -/
def dihedralTinyPackets_CHI (hβ : ∀ j, 1 ≤ j → j ≤ 3 → β j ≤ 1 / 4) (hb : b ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hεr : 0 ≤ εr) (he : 0 < e) (hT : 1000 ≤ T) (hδT : 1 ≤ δ * T)
    (hTV : T ≤ V) :
    LocalChartPacketsC14 dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
      dihedralTinyRho_CHI dihedralTinyRho_pos_CHI Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
      e T V vs ζ Λz where
  toLocalChartFamilyE := dihedralTinyFamilyE_CHI hβ hb
  circleAdapted := fun j hj => absurd hj (notMem_empty j)
  N := fun _ => dihedralZeroSource
  C := fun _ => PUnit.{1}
  instMetricN := fun _ => dihedralTinyMetricSpace_CHI
  instChartedN := fun _ => inferInstance
  instMetricC := fun _ => inferInstance
  o := fun _ => PUnit.unit
  zero := dihedralTinyZeroFamily_CHI hβ hδ hδ1 hεr he hT hδT hTV
  edgeDisk := fun j hj => absurd hj (notMem_empty j)
  circle_residual := fun j hj => absurd hj (notMem_empty j)
  zero_local_comparison := fun _ _ q _ => by
    change T / 20 ≤ T * dihedralTinyScale_CHI / dihedralTinyScale_CHI
    rw [mul_div_cancel_right₀ _ dihedralTinyScale_pos_CHI.ne']
    linarith
  slim_value := fun j hj => absurd hj (notMem_empty j)
  zero_shell_split := fun c _ q hq _ => absurd hq (not_le.mpr (by
    change dist c q < T * dihedralTinyScale_CHI / 10
    have h := dihedralTiny_dist_lt_radius_CHI hT c q
    linarith [dihedralTiny_radius_pos_CHI hT]))
  zero_adapted := fun c _ q hq _ => absurd hq (not_le.mpr (by
    change dist c q < T * dihedralTinyScale_CHI / 10
    have h := dihedralTiny_dist_lt_radius_CHI hT c q
    linarith [dihedralTiny_radius_pos_CHI hT]))
  zero_curvature := fun _ _ y _ =>
    (dihedralMetric_sectional_nonneg 1 1 one_pos one_pos y).mono
      (neg_nonpos.mpr (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  edge_section := fun j hj => absurd hj (notMem_empty j)

/-- The base projection `LocalChartPackets` of the dihedral inhabitant. -/
def dihedralTinyBasePackets_CHI (hβ : ∀ j, 1 ≤ j → j ≤ 3 → β j ≤ 1 / 4) (hb : b ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hεr : 0 ≤ εr) (he : 0 < e) (hT : 1000 ≤ T) (hδT : 1 ≤ δ * T)
    (hTV : T ≤ V) :
    LocalChartPackets dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
      dihedralTinyRho_CHI dihedralTinyRho_pos_CHI Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
      e T V :=
  (dihedralTinyPackets_CHI (Λ := Λ) (Δ := Δ) (σs := σs) (K := K) (σc := σc) (μ := μ) (s := s)
    (b' := b') (s' := s') (ε := ε) (γc := γc) (βc := βc) (Lmax := Lmax) (τ := τ) (γ := γ)
    (vs := 0) (ζ := 0) (Λz := 0) hβ hb hδ hδ1 hεr he hT hδT hTV).toLocalChartPackets

/-- `LocalChartPacketsC14D` on the dihedral source (`weak_edge_density` is vacuous: the
one-stratum is empty). -/
def dihedralTinyPacketsC14D_CHI (hβ : ∀ j, 1 ≤ j → j ≤ 3 → β j ≤ 1 / 4) (hb : b ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hεr : 0 ≤ εr) (he : 0 < e) (hT : 1000 ≤ T) (hδT : 1 ≤ δ * T)
    (hTV : T ≤ V) :
    LocalChartPacketsC14D dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
      dihedralTinyRho_CHI dihedralTinyRho_pos_CHI Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
      e T V vs ζ Λz where
  toLocalChartPacketsC14 := dihedralTinyPackets_CHI hβ hb hδ hδ1 hεr he hT hδT hTV
  weak_edge_density := fun p hp => absurd hp (dihedralTiny_not_mem_stratum_CHI hβ (by decide) p)

/-- `RP³ # RP³` as a connected closed oriented three-manifold (carrier `dihedralZeroSource`). -/
abbrev dihedralTinyManifold_CHI : Topology.ConnectedClosedOrientedManifold.{0} 3 :=
  Topology.connectedSum Topology.projectiveThreeSpaceLift.{0}
    Topology.projectiveThreeSpaceLift.{0}

/-- The canonical orientation of `RP³ # RP³`. -/
def dihedralTinyOrientation_CHI : ManifoldOrientation 𝓘(ℝ, E3) dihedralZeroSource 3 :=
  dihedralTinyManifold_CHI.orientation

/-- The rescaled distance to a centre is `< 1/1000` at the zero-ball scale. -/
theorem dihedralTiny_radial_lt_CHI (hT : 1000 ≤ T) (c x : dihedralZeroSource) :
    @dist dihedralZeroSource (dihedralTinyMetricSpace_CHI.rescale (T * dihedralTinyScale_CHI)⁻¹
      (inv_pos.mpr (dihedralTiny_radius_pos_CHI hT))).toDist x c < 1 / 1000 := by
  change (T * dihedralTinyScale_CHI)⁻¹ * dist x c < 1 / 1000
  have hr := dihedralTiny_radius_pos_CHI hT
  rw [inv_mul_lt_iff₀ hr]
  have h := dihedralTiny_dist_lt_radius_CHI hT x c
  linarith

/-- **The complete closed family `LocalChartPacketsC14Z` on the dihedral source**, at its canonical
orientation: every zero sublevel `{η ≤ a}`, `a ∈ [1/5, 2]`, is the whole source, a compact model of
type `RP³ # RP³` (`IsCompactNonnegativeType`, identity diffeomorphism). -/
def dihedralTinyPacketsC14Z_CHI (hβ : ∀ j, 1 ≤ j → j ≤ 3 → β j ≤ 1 / 4) (hb : b ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hεr : 0 ≤ εr) (he : 0 < e) (hT : 1000 ≤ T) (hδT : 1 ≤ δ * T)
    (hTV : T ≤ V) :
    LocalChartPacketsC14Z dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
      dihedralTinyRho_CHI dihedralTinyRho_pos_CHI Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
      e T V vs ζ Λz dihedralTinyOrientation_CHI where
  toLocalChartPacketsC14D := dihedralTinyPacketsC14D_CHI hβ hb hδ hδ1 hεr he hT hδT hTV
  zero_sublevel_types := fun c _ a ha => Or.inl
    ⟨eq_univ_of_forall fun x => by
        change @dist dihedralZeroSource (dihedralTinyMetricSpace_CHI.rescale
          (T * dihedralTinyScale_CHI)⁻¹ (inv_pos.mpr (dihedralTiny_radius_pos_CHI hT))).toDist
          x c ≤ a
        linarith [dihedralTiny_radial_lt_CHI hT c x, ha.1],
      inferInstanceAs (CompactSpace dihedralZeroSource),
      ⟨Diffeomorph.refl 𝓘(ℝ, E3) dihedralZeroSource ∞⟩,
      dihedralTinyManifold_CHI,
      Or.inr (Or.inr (Or.inl ⟨Diffeomorph.refl 𝓘(ℝ, E3) dihedralZeroSource ∞⟩)),
      Diffeomorph.refl 𝓘(ℝ, E3) dihedralZeroSource ∞,
      Diffeomorph.preservesOrientation_refl _⟩

end DifferentialGeometry.Geometry.Collapse
