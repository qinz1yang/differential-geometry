import DifferentialGeometry.Geometry.Fibration.ActualSlimRawAlignment
import DifferentialGeometry.Geometry.Fibration.ActualEdgeComparisonList
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeCenterSplittingExclusion
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleGeometry

/-!
# EGP03: fixed raw edge alignments on a short common ball (actual LC87 family)

Blueprint `master207B.tex`, EGP03 (`lem:fibration-edge-raw-alignment`, B:4897–4941): fix `Δ, β₂`
and `0 < δ, E < 1`; choose `β_E`, then `β₁` and the tail. In reference `R_i` units, on
`B(p_i, 600Δ)` each `j ∈ J_e ∪ J_s` has one sign `a_j` and translation `c_j = s_j u_j(p_i)` with
`|s_j u_j − a_j u_i − c_j| < E` (ER), `u_j` the ORIGINAL raw real coordinate, `a_i = 1, c_i = 0`;
every original raw tested ball contains its radius-`100L` ball with distortion at most `δ`, and
lifts of targets of radius at most `20L` have error `< δ` and pointed radius `< 21L`.

* `exists_sign_raw_alignment_real_KC` (kernel, physical form of Codex X125's MC10/MC11 producer
  `exists_scaled_raw_coisometry_parameter_riemannian` for real factors, `j = k = 1`): an original
  rank-one splitting at `j` in its own normalized metric `ρ(j)⁻¹d` and the reference one at `i` in
  `ρ(i)⁻¹d`, with `ρ(j)/ρ(i) ∈ [1/2, 2]`, `d(i, j) ≤ Cρ(i)`, no `(2, ν)`-splitting at `i` and the
  curvature buffer of radius `σ⁻¹ρ(i)`, satisfy `|s u_j − a u_i − s u_j(i)| ≤ 50τ` on `B(i, Hρ(i))`.
* `egpChartRaw`, `egpRaw`: the raw coordinate `u_j` of the actual edge chart (real factor of its
  normalized `b`-splitting); `exists_edge_split_KC2`: that splitting based at `j` itself.
* `egp03_row`: (ER) on the actual family `LocalChartFamilyE` for `J_e` (edge raw coordinates) and
  `J_s` (C14-SGP's `sgpRaw`); `egp03_self`: `a_i = 1`, `c_i = 0`; `egp03_reference_tests`: the
  reference edge splitting's tested ball, distortion and lifts (slim: C14-SGP's
  `sgp02_reference_tests`).

The exclusion at the reference centre is EGP01 (`not_hasEuclideanSplitting_two_of_isEdgePoint`),
the curvature is LPA01's buffer at radius `Lc = σ⁻¹`, the list bounds are EGP02's (FC18 supports).
NOT here: the zero clause (ER0) (needs LC73/LCP04's actual shell splitting).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E1" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Kernel

/-- **MC10/MC11 for real factors, physical form.** See the module docstring. -/
theorem exists_sign_raw_alignment_real_KC {τ ν H : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (hν : 0 < ν)
    (hν1 : ν < 1) (ha : 20 * τ ≤ H + 1) (ha2 : 2 * (H + 1) ≤ τ⁻¹) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∀ C : ℝ, 0 ≤ C → ∃ η : ℝ, 0 < η ∧
      ∀ (M : Type) [m : MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
        [CompactSpace M] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M),
        (∀ x y, riemannianEDistOf g x y = ENNReal.ofReal (dist x y)) →
        ∀ (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p) (i j : M),
        (∀ y ∈ ball i (σ⁻¹ * ρ i), SectionalBoundedBelowAt g y (-((σ⁻¹ * ρ i) ^ 2)⁻¹)) →
        ¬ @HasEuclideanSplitting.{0, 0} M (m.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) i 2 ν →
        1 / 2 ≤ ρ j / ρ i → ρ j / ρ i ≤ 2 → dist i j ≤ C * ρ i →
        ∀ (A B : Type) [MetricSpace A] [MetricSpace B] (a : A) (b : B) {ε₁ ε₂ : ℝ},
        ε₁ ≤ η → 3 * ε₂ ≤ σ → ε₂ * (2 * (H + 1)) ≤ 1 →
        ∀ (φ : @KleinerLottApprox M (WithLp 2 (ℝ × A)) (m.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)))
            _ j (WithLp.toLp 2 ((0 : ℝ), a)) ε₁)
          (ψ : @KleinerLottApprox M (WithLp 2 (ℝ × B)) (m.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i)))
            _ i (WithLp.toLp 2 ((0 : ℝ), b)) ε₂),
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ x ∈ ball i (H * ρ i),
          |ρ j / ρ i * (@KleinerLottApprox.toFun M _ (m.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j _
              ε₁ φ x).fst -
            s * (@KleinerLottApprox.toFun M _ (m.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i _
              ε₂ ψ x).fst -
            ρ j / ρ i * (@KleinerLottApprox.toFun M _ (m.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j _
              ε₁ φ i).fst| ≤ 50 * τ := by
  have hkn : (1 : ℕ) ≤ Module.finrank ℝ E3 := by rw [finrank_euclideanSpace_fin]; norm_num
  obtain ⟨σ, hσ, hσ1, hprop⟩ := exists_scaled_raw_coisometry_parameter_riemannian.{0}
    (E := E3) (H := E3) (I := 𝓘(ℝ, E3)) (j := 1) (k := 1) le_rfl le_rfl hkn hτ hτ1 hν hν1
    (by linarith : (0 : ℝ) < H + 1) (by push_cast; linarith) ha2
  refine ⟨σ, hσ, hσ1, fun C hC => ?_⟩
  obtain ⟨η, hη, hprop⟩ := hprop C hC
  refine ⟨η, hη, ?_⟩
  intro M m _ _ _ g hmetric ρ hρ i j hsec hno hc1 hc2 hd A B _ _ a b ε₁ ε₂ hε₁ hε₂ hε₂H φ ψ
  have hri := hρ i
  have hrj := hρ j
  set c : ℝ := ρ j / ρ i with hcdef
  have hc : 0 < c := div_pos hrj hri
  -- physical facts, before the reference metric is introduced
  have hdR : (ρ i)⁻¹ * dist i j ≤ C := by
    rw [inv_mul_le_iff₀ hri]
    linarith
  have hmR := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale g hmetric hri
  set gR : SmoothRiemannianMetric 𝓘(ℝ, E3) M :=
    scaleMetric ((ρ i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hri) 2) g with hgR
  have hsecR : ∀ y, (ρ i)⁻¹ * dist y i < σ⁻¹ → SectionalBoundedBelowAt gR y (-σ) := by
    intro y hy
    have hy' : y ∈ ball i (σ⁻¹ * ρ i) := by
      rw [mem_ball]
      rw [inv_mul_lt_iff₀ hri] at hy
      linarith
    have hb := hsec y hy'
    rw [hgR, sectionalBoundedBelowAt_scaleMetric_iff]
    refine hb.mono ?_
    have hσ2 : σ ^ 2 ≤ σ := by nlinarith
    have he : -((σ⁻¹ * ρ i) ^ 2)⁻¹ = -(σ ^ 2 * (ρ i)⁻¹ ^ 2) := by
      rw [mul_pow, mul_inv, inv_pow, inv_inv, ← inv_pow]
    rw [he]
    have hr2 : 0 ≤ (ρ i)⁻¹ ^ 2 := by positivity
    nlinarith
  -- the reference splitting with target `ℝ¹ × B`
  let ψ' := @KleinerLottApprox.mapTargetIsometryAt M (WithLp 2 (ℝ × B)) (WithLp 2 (E1 × B))
    (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ i (WithLp.toLp 2 ((0 : ℝ), b)) ε₂ ψ
    (realProdIso_SGP B) (WithLp.toLp 2 ((0 : E1), b)) (realProdIso_SGP_zero b)
  -- the other splitting with target `ℝ¹ × A`, read in the reference metric
  let φ₀ := @KleinerLottApprox.mapTargetIsometryAt M (WithLp 2 (ℝ × A)) (WithLp 2 (E1 × A))
    (m.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ j (WithLp.toLp 2 ((0 : ℝ), a)) ε₁ φ
    (realProdIso_SGP A) (WithLp.toLp 2 ((0 : E1), a)) (realProdIso_SGP_zero a)
  have hmetq : m.rescale (ρ j)⁻¹ (inv_pos.mpr hrj) =
      (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).rescale c⁻¹ (inv_pos.mpr hc) :=
    (MetricSpace.rescale_inv_ratio m hri hrj).symm
  obtain ⟨φ', hφ'⟩ := exists_kleinerLott_of_metric_eq_SGP hmetq φ₀
  have hcpt :
      @CompactSpace M (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).toUniformSpace.toTopologicalSpace :=
    MetricSpace.rescale_compactSpace m _ _
  have hcomp : @CompleteSpace M (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).toUniformSpace :=
    (m.rescale_completeSpace_iff (ρ i)⁻¹ (inv_pos.mpr hri)).mpr complete_of_compact
  have hsig : @SigmaCompactSpace M
      (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).toUniformSpace.toTopologicalSpace :=
    @CompactSpace.sigmaCompact M _ hcpt
  obtain ⟨Λ₁, hΛ₁, hal⟩ := @hprop M (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ hsig hcomp gR hmR i
    (fun y hy => hsecR y hy) hno A B _ _ a b j ε₁ ε₂ c hc hc1 hc2 hdR hε₁ hε₂ φ' ψ'
  obtain ⟨s, hs, hlin⟩ := coisometry_fin_one_SGP Λ₁ hΛ₁
  refine ⟨s, hs, fun x hx => ?_⟩
  have hxR : (ρ i)⁻¹ * dist x i < H := by
    rw [inv_mul_lt_iff₀ hri]
    have : dist x i < H * ρ i := hx
    linarith
  have hb0 : 0 < ε₂ := @KleinerLottApprox.error_pos M (WithLp 2 (ℝ × B))
    (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂ ψ
  have hb1 : ε₂ < 1 := @KleinerLottApprox.error_lt_one M (WithLp 2 (ℝ × B))
    (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂ ψ
  have hεinv : 2 * (H + 1) ≤ ε₂⁻¹ := by
    rw [le_inv_comm₀ (by linarith) hb0, inv_eq_one_div, le_div_iff₀ (by linarith)]
    linarith
  -- `|u_i(x)| ≤ H + 1`
  have hui : |(@KleinerLottApprox.toFun M _ (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂
      ψ x).fst| ≤ H + 1 := by
    have hdist := @KleinerLottApprox.radial_error M (WithLp 2 (ℝ × B))
      (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂ ψ x
      (show (ρ i)⁻¹ * dist x i < ε₂⁻¹ by linarith)
    change |dist (@KleinerLottApprox.toFun M _ (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂
      ψ x) (WithLp.toLp 2 ((0 : ℝ), b)) - (ρ i)⁻¹ * dist x i| ≤ ε₂ at hdist
    have hfst := WithLp.dist_fst_le (@KleinerLottApprox.toFun M _
      (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂ ψ x) (WithLp.toLp 2 ((0 : ℝ), b))
    rw [Real.dist_eq] at hfst
    change |(@KleinerLottApprox.toFun M _ (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂
      ψ x).fst - 0| ≤ _ at hfst
    rw [sub_zero] at hfst
    linarith [(abs_le.mp hdist).2]
  have hxτ : (ρ i)⁻¹ * dist x i < τ⁻¹ := by linarith
  have hψx : (@KleinerLottApprox.toFun M _ (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂
      ψ' x).fst = realFinOneIso_SGP (@KleinerLottApprox.toFun M _
        (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂ ψ x).fst := rfl
  have hφx : ∀ y, (@KleinerLottApprox.toFun M _
      ((m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).rescale c⁻¹ (inv_pos.mpr hc)) _ j _ ε₁ φ' y).fst =
        realFinOneIso_SGP (@KleinerLottApprox.toFun M _ (m.rescale (ρ j)⁻¹ (inv_pos.mpr hrj))
          _ j _ ε₁ φ y).fst := by
    intro y
    rw [hφ']
    rfl
  have hnorm : ‖(@KleinerLottApprox.toFun M _ (m.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ ε₂
      ψ' x).fst‖ ≤ H + 1 := by
    rw [hψx, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
    exact hui
  have hmain := hal x hxτ hnorm
  rw [hψx, hφx, hφx, hlin] at hmain
  rw [← map_smul, ← map_smul, ← map_sub, ← map_sub, LinearIsometryEquiv.norm_map,
    Real.norm_eq_abs, smul_eq_mul, smul_eq_mul] at hmain
  have h50 : 2 * (1 + 24 * ((1 : ℕ) : ℝ)) * τ = 50 * τ := by push_cast; ring
  rw [h50] at hmain
  exact hmain

/-- A Kleiner–Lott map transported along an equality of base points keeps its map. -/
theorem exists_kleinerLott_of_base_eq_KC2 {X Y : Type*} {m : MetricSpace X} [MetricSpace Y]
    {p p' : X} (h : p = p') {q : Y} {δ : ℝ} (f : @KleinerLottApprox X Y m _ p q δ) :
    ∃ f' : @KleinerLottApprox X Y m _ p' q δ,
      @KleinerLottApprox.toFun X Y m _ p' q δ f' = @KleinerLottApprox.toFun X Y m _ p q δ f := by
  subst h
  exact ⟨f, rfl⟩

/-- The parameters of EGP03's application of X125 (`H = 600Δ`, `a = H + 1`). -/
theorem egp03_parameters_KC2 {Δ E H t : ℝ} (hΔ : 1 ≤ Δ) (hE : 0 < E) (hH : H = 600 * Δ)
    (ht : t = min (E / 100) (1 / (2 * (H + 1)))) :
    0 < t ∧ t < 1 ∧ 20 * t ≤ H + 1 ∧ 2 * (H + 1) ≤ t⁻¹ ∧ 50 * t < E := by
  have hH' : 600 ≤ H := by rw [hH]; linarith
  have hH1 : 0 < 2 * (H + 1) := by linarith
  have ht0 : 0 < t := by rw [ht]; exact lt_min (by positivity) (by positivity)
  have ht1 : t ≤ 1 / (2 * (H + 1)) := by rw [ht]; exact min_le_right _ _
  have htE : t ≤ E / 100 := by rw [ht]; exact min_le_left _ _
  have htsmall : t ≤ 1 / 1202 := ht1.trans
    (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hinv : 2 * (H + 1) ≤ t⁻¹ := by
    rw [le_inv_comm₀ hH1 ht0]
    simpa only [one_div] using ht1
  exact ⟨ht0, by linarith, by linarith, hinv, by linarith⟩

end Kernel

section Actual

universe u

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}

/-- The real factor of the edge chart's normalized `b`-splitting at a centre `j`. -/
def egpChartRaw (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) {j : X}
    (hj : j ∈ F.centres) (x : X) : ℝ :=
  let C := F.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  letI := C.instY
  (C.split.toFun x).fst

open Classical in
/-- The ORIGINAL raw real coordinate `u_j` of the actual edge chart at `j`: the real factor of the
chart's normalized `b`-splitting (zero off the centres). -/
def egpRaw (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (j x : X) : ℝ :=
  if hj : j ∈ F.centres then egpChartRaw F hj x else 0

theorem egpRaw_of_mem (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) {j : X}
    (hj : j ∈ F.centres) (x : X) : egpRaw F j x = egpChartRaw F hj x := by
  unfold egpRaw
  rw [dite_eq_left hj]

/-- The edge chart's splitting, based at `j` itself (the chart centre is `j`), as a normalized
rank-one `b`-splitting whose raw coordinate is `egpRaw`. -/
theorem exists_edge_split_KC2 (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc)
    {j : X} (hj : j ∈ F.centres) :
    ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
      ∃ q : Y, ∃ f : @KleinerLottApprox X (WithLp 2 (ℝ × Y))
          (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j (WithLp.toLp 2 ((0 : ℝ), q)) b,
        ∀ x, (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
          f x).fst = egpRaw F j x := by
  have hcen := F.chart_center j hj
  have hraw : ∀ x, egpRaw F j x = egpChartRaw F hj x := egpRaw_of_mem F hj
  let C := F.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hcen' : C.center = j := hcen
  let _ := C.instY
  obtain ⟨f, hf⟩ := exists_kleinerLott_of_base_eq_KC2 hcen' C.split
  refine ⟨C.Y, C.instY, C.q, f, fun x => ?_⟩
  rw [hraw, hf]
  rfl

theorem egpRaw_center (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (j : X) :
    egpRaw F j j = 0 := by
  by_cases hj : j ∈ F.centres
  · obtain ⟨Y, mY, q, f, hf⟩ := exists_edge_split_KC2 F hj
    rw [← hf j, @KleinerLottApprox.basepoint X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j
      _ b f]
    rfl
  · unfold egpRaw
    rw [dite_eq_right hj]

/-- EGP03: `a_i = 1`, `c_i = 0`. -/
theorem egp03_self (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (i x : X) :
    ρ i / ρ i * egpRaw F i x - 1 * egpRaw F i x - ρ i / ρ i * egpRaw F i i = 0 := by
  rw [div_self (hρ i).ne', egpRaw_center]
  ring

/-- **EGP03's side clauses for the edge reference splitting**: for `b ≤ min(1/(1000L), δ/100)`
(`L = 10⁶Δ`) the original edge splitting at `i` (raw coordinate `u_i = egpRaw`) has tested ball
containing `B(i, 100L)`, distortion at most `δ` there, and every target of radius `< 20L` lifts
into `B(i, 21L)` to error `< δ` (reference units). The slim ones are C14-SGP's
`sgp02_reference_tests`. -/
theorem egp03_reference_tests (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc)
    {δ : ℝ} (hΔ : 1 ≤ Δ) (hb : b ≤ min (1 / (1000 * (1000000 * Δ))) (δ / 100)) {i : X}
    (hi : i ∈ F.centres) :
    ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
      ∃ q : Y, ∃ f : @KleinerLottApprox X (WithLp 2 (ℝ × Y))
          (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i (WithLp.toLp 2 ((0 : ℝ), q)) b,
        let u := @KleinerLottApprox.toFun X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ _ _ _ f
        (∀ x, (u x).fst = egpRaw F i x) ∧ 100 * (1000000 * Δ) ≤ b⁻¹ ∧
          (∀ x ∈ ball i (100 * (1000000 * Δ) * ρ i), ∀ x' ∈ ball i (100 * (1000000 * Δ) * ρ i),
            |dist (u x) (u x') - (ρ i)⁻¹ * dist x x'| ≤ δ) ∧
          ∀ y, dist y (u i) < 20 * (1000000 * Δ) →
            ∃ x ∈ ball i (21 * (1000000 * Δ) * ρ i), dist y (u x) < δ := by
  obtain ⟨Y, mY, q, f, hf⟩ := exists_edge_split_KC2 F hi
  have hri := hρ i
  obtain ⟨h1, h2, h3⟩ := @kl_reference_tests_SGP X Y
    (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i q b δ (1000000 * Δ) (by linarith) f hb
  have hball : ∀ r : ℝ, ∀ x, x ∈ ball i (r * ρ i) ↔
      x ∈ @ball X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).toPseudoMetricSpace i r := by
    intro r x
    change dist x i < r * ρ i ↔ (ρ i)⁻¹ * dist x i < r
    rw [inv_mul_lt_iff₀ hri, mul_comm]
  refine ⟨Y, mY, q, f, hf, h1, fun x hx x' hx' => h2 x ((hball _ x).mp hx) x'
    ((hball _ x').mp hx'), fun y hy => ?_⟩
  obtain ⟨x, hx, hxy⟩ := h3 y hy
  exact ⟨x, (hball _ x).mpr hx, hxy⟩

end Actual

section Row

/-- **EGP03 (ER) on the actual LC87 family with packet (iv).** Fix `Δ ≥ 1`, the exclusion
quality `β₂ < 10⁻⁶` and `E > 0`. There are a curvature radius `Lc` (asked of LPA01's buffer) and a
raw quality `η₀` such that for EVERY actual family `L` with `b, β₁ ≤ η₀`, `s < 10⁻⁶`, `Lc ≤ Lmax`,
`10⁶ΔΛ < 10⁻⁵` and packet (iv)'s `μ, τ ≤ 1/100`, every edge centre `i` and every listed
`j ∈ J_e ∪ J_s` have one sign `a_j` with `|s_j u_j − a_j u_i − s_j u_j(i)| < E` on
`B(i, 600Δρ(i))`, `s_j = ρ(j)/ρ(i)`. -/
theorem egp03_row {Δ β₂ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ : ℝ)
        (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → ∀ i ∈ L.edge.centres,
          (∀ j ∈ egpEdgeList L.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (600 * Δ * ρ i),
              |ρ j / ρ i * egpRaw L.edge j x - a * egpRaw L.edge i x -
                ρ j / ρ i * egpRaw L.edge j i| < E) ∧
          (∀ j ∈ egpSlimList L.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (600 * Δ * ρ i),
              |ρ j / ρ i * sgpRaw L.slim j x - a * egpRaw L.edge i x -
                ρ j / ρ i * sgpRaw L.slim j i| < E) := by
  have hΔ0 : 0 < Δ := by linarith
  set H : ℝ := 600 * Δ with hH
  set t : ℝ := min (E / 100) (1 / (2 * (H + 1))) with ht
  obtain ⟨ht0, ht1, ha, ha2, htE⟩ := egp03_parameters_KC2 hΔ hE hH ht
  obtain ⟨σ, hσ, hσ1, hprop⟩ :=
    exists_sign_raw_alignment_real_KC ht0 ht1 hβ₂ (by linarith) ha ha2
  obtain ⟨η, hη, hal⟩ := hprop (1000000 * Δ) (by positivity)
  have hH1 : 0 < 1 / (2 * (H + 1)) := by positivity
  refine ⟨σ⁻¹, min η (min (σ / 3) (min (1 / (2 * (H + 1))) (1 / 10000000))), inv_pos.mpr hσ,
    lt_min hη (lt_min (by positivity) (lt_min hH1 (by norm_num))), ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ L hb hs hβ1 hLc hΛ hLΛ
    hμ hτ i hi
  have hri := hρ i
  have hbη : b ≤ η := hb.trans (min_le_left _ _)
  have hbσ : 3 * b ≤ σ := by
    have := hb.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hbH0 : b ≤ 1 / (2 * (H + 1)) :=
    hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbH : b * (2 * (H + 1)) ≤ 1 := by
    rw [le_div_iff₀ (by linarith)] at hbH0
    linarith
  have hb6 : b < 1 / 1000000 := by
    have := hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  have hβη : β 1 ≤ η := hβ1.trans (min_le_left _ _)
  -- the common inputs at the reference centre
  have hsec := L.sectional_buffer σ⁻¹ (inv_pos.mpr hσ) hLc i
  have hno : ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) i 2 β₂ :=
    @not_hasEuclideanSplitting_two_of_isEdgePoint.{0, 0, 0} X
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) i Δ b s β₂ (L.edge.strong i hi) hb6 hs hβ₂1
  have hρL : LipschitzWith (Real.toNNReal Λ) ρ := L.lipschitz_scale
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  have hΔΛ0 : 0 ≤ Δ * Λ := mul_nonneg hΔ0.le hΛ
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  have hLΛ' : 1000000 * Δ * ((Real.toNNReal Λ : NNReal) : ℝ) < 1 / 100000 := by rwa [hc]
  obtain ⟨Bi, mBi, qi, ψ, hψx⟩ := exists_edge_split_KC2 L.edge hi
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · -- `j ∈ J_e`
    obtain ⟨hjc, y, hy1, hy2⟩ := hj
    have h14 := (fc18_edge_rowE L hΛ hΔ0 hμ hτ hΔΛ hjc).1 hy1
    have hm : (closedBall j (15 * Δ * ρ j) ∩ ball i (20 * Δ * ρ i)).Nonempty := by
      refine ⟨y, closedBall_subset_closedBall ?_ h14, hy2⟩
      nlinarith [hρ j]
    obtain ⟨h1, h2, h3, -⟩ := edge_comparison_list_edge_bounds hρL hri (hρ j) hΔ hLΛ' hm
    have hd : dist i j ≤ 1000000 * Δ * ρ i := by nlinarith
    obtain ⟨Aj, mAj, qj, φ, hφx⟩ := exists_edge_split_KC2 L.edge hjc
    obtain ⟨a, ha1, hlin⟩ := hal X g hmetric ρ hρ i j hsec hno (by linarith) (by linarith) hd
      Aj Bi qj qi hbη hbσ hbH φ ψ
    refine ⟨a, ha1, fun x hx => ?_⟩
    have hmain := hlin x hx
    rw [hψx, hφx, hφx] at hmain
    linarith
  · -- `j ∈ J_s`
    obtain ⟨hjc, y, hy1, hy2⟩ := hj
    have hsl := fc18_slim_row L.toLocalChartFamily hΔ0 hjc
    have hm : (closedBall j ((910000 * Δ) * ρ j) ∩ ball i ((20 * Δ) * ρ i)).Nonempty :=
      ⟨y, hsl.1 hy1, hy2⟩
    obtain ⟨h1, h2, h3, -⟩ := support_meeting_sharp_bounds hρL hri (hρ j) (a := 20 * Δ)
      (c := 910000 * Δ) (by positivity) (by positivity) (by rw [hc]; nlinarith)
      (by rw [hc]; nlinarith) hm
    have hd : dist i j ≤ 1000000 * Δ * ρ i := by nlinarith
    let Sj := L.slim.centre j hjc
    let _ := Sj.instZ
    obtain ⟨a, ha1, hlin⟩ := hal X g hmetric ρ hρ i j hsec hno (by linarith) (by linarith) hd
      Sj.Z Bi Sj.z qi hβη hbσ hbH Sj.split ψ
    refine ⟨a, ha1, fun x hx => ?_⟩
    have hmain := hlin x hx
    rw [hψx] at hmain
    rw [sgpRaw_of_mem L.slim hjc, sgpRaw_of_mem L.slim hjc]
    exact lt_of_le_of_lt hmain (by linarith)

end Row

end DifferentialGeometry.Geometry.Collapse
