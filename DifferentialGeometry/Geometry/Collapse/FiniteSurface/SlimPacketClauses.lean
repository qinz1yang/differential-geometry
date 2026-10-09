import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimCoordinateClauses
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimSlabBundle

/-!
# LFR20 items 2 and 4 for EVERY coordinate of LFR19 (no limit argument)

Blueprint LFR20 (master207A:26358) with `L = 10⁶Δ`, `D = 10³Δ`, `e = Δ/100`, `a = 9L/10`. Let
`α = (u, v)` be a normalized `(1, β)`-splitting with `diam Y ≤ D`, `β ≤ 10⁻⁸Δ⁻¹`, and let `η` be
ANY coordinate with LFR19's displayed estimates on `B(p, L)` (smooth near `B̄(p, L)`,
`(1 + σ)`-Lipschitz, `|η - u| < e`, (LFR19.1) with `T = L/σ`, `σ ≤ 1/100`). Then
(`slimPacket_clauses_of_coordinate`), with `a' = 905·10³Δ` and `r = 0.91L`:

1. (LFR20.2) `|η x| ≤ a'` on `B(p, L)` forces `d(x, p) < r`;
2. every `x ∈ B(p, r)` has a unit `w` with `dη_x(w) > 3/4`;
3. `η(B(p, L)) ⊇ [-a', a']`;
4. `η : {x ∈ B(p, L) | |η x| < a'} → (-a', a')` is a smooth proper submersion, trivial over every
   `(-R, R)`, `R < a'` — in particular over `(-a, a)` (item 2 except the fibre type);
5. item 4: every smooth profile `ψ` vanishing for `|s| > c`, `c ≤ a'`, gives a smooth compactly
   supported `1_{B(p,L)} · ψ ∘ η` with support in `{d(x,p) ≤ r, |η| ≤ c}`; such a profile with
   plateau `|s| ≤ 8·10⁵Δ` and support in `|s| < 89·10⁴Δ` exists (`exists_slim_profile`).

`exists_slimPacket_coordinate` composes this with LFR19 (`exists_rankOne_coordinate_value_tolerance`):
LFR20 item 1 together with the clauses above, under LFR20's hypotheses, after one reduction of β₀.
The fibre TYPE (S² or T²), connectedness and the model embedding (item 3) need the limit
(LFR14/LFR16/LFR17) and are not claimed here.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open GC.MetricGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

/-- **LFR20, the profile of item 4.** A smooth `ψ : ℝ → [0, 1]`, equal to one on
`|s| ≤ 8·10⁵Δ`, nonzero only where `|s| < 89·10⁴Δ` (closed support strictly inside
`|s| < 9·10⁵Δ`). -/
theorem exists_slim_profile {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ s, ψ s ∈ Icc (0 : ℝ) 1) ∧
      (∀ s, |s| ≤ 8 * 10 ^ 5 * Δ → ψ s = 1) ∧ (∀ s, ψ s ≠ 0 → |s| < 89 * 10 ^ 4 * Δ) := by
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := 8 * 10 ^ 5 * Δ, rOut := 89 * 10 ^ 4 * Δ,
      rIn_pos := by positivity, rIn_lt_rOut := by nlinarith }
  refine ⟨b, b.contDiff, fun s => ⟨b.nonneg, b.le_one⟩, fun s hs => ?_, fun s hs => ?_⟩
  · apply b.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact hs
  · have h : s ∈ Function.support b := hs
    rw [b.support_eq, mem_ball, dist_zero_right, Real.norm_eq_abs] at h
    exact h

/-- The numerical facts used below, for `Δ ≥ 1`, `σ ≤ 1/100`, `0 < β ≤ 10⁻⁸Δ⁻¹`. -/
theorem slimPacket_coordinate_constants {Δ σ β : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 100) (hβ : 0 < β) (hβΔ : β * (10 ^ 8 * Δ) ≤ 1) :
    Real.sqrt ((905 * 10 ^ 3 * Δ + Δ / 100) ^ 2 + (10 ^ 3 * Δ) ^ 2) + β <
        91 / 100 * (10 ^ 6 * Δ) ∧
      91 / 100 * (10 ^ 6 * Δ) + 2 * (10 ^ 6 * Δ) + 2 * β < β⁻¹ ∧
      91 / 100 * (10 ^ 6 * Δ) + 2 * (10 ^ 6 * Δ) + 3 * β < 10 ^ 6 * Δ / σ ∧
      3 * β < 10 ^ 6 * Δ ∧
      3 / 4 ≤ (2 * (10 ^ 6 * Δ) - 2 * β) / (2 * (10 ^ 6 * Δ) + 3 * β) - σ ∧
      95 / 100 * (10 ^ 6 * Δ) + 3 * β < 10 ^ 6 * Δ ∧
      95 / 100 * (10 ^ 6 * Δ) + β < β⁻¹ ∧
      905 * 10 ^ 3 * Δ ≤ 95 / 100 * (10 ^ 6 * Δ) - 2 * β - Δ / 100 ∧
      (10 ^ 6 * Δ) ≤ β⁻¹ := by
  have hΔ0 : 0 < Δ := by linarith
  have hβ1 : β ≤ 1 / 10 ^ 8 := by
    have : β * 10 ^ 8 ≤ β * (10 ^ 8 * Δ) := by nlinarith
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hinv : 10 ^ 8 * Δ ≤ β⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hβ]
    rw [le_inv_comm₀ hβ (by positivity)] at *
    rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
    linarith
  refine ⟨?_, by nlinarith, ?_, by nlinarith, ?_, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith⟩
  · have hpos : 0 < 91 / 100 * (10 ^ 6 * Δ) - β := by nlinarith
    have hlow : 909999 * Δ ≤ 91 / 100 * (10 ^ 6 * Δ) - β := by nlinarith
    have hsq : (909999 * Δ) ^ 2 ≤ (91 / 100 * (10 ^ 6 * Δ) - β) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    have : Real.sqrt ((905 * 10 ^ 3 * Δ + Δ / 100) ^ 2 + (10 ^ 3 * Δ) ^ 2) <
        91 / 100 * (10 ^ 6 * Δ) - β := by
      rw [Real.sqrt_lt' hpos]
      nlinarith
    linarith
  · rw [lt_div_iff₀ hσ]
    nlinarith
  · rw [le_sub_iff_add_le, le_div_iff₀ (by nlinarith)]
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LFR20, items 2 (minus the fibre type) and 4, for EVERY coordinate of LFR19.** -/
theorem slimPacket_clauses_of_coordinate (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Δ σ β : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 100)
    (hβΔ : β * (10 ^ 8 * Δ) ≤ 1) {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y}
    (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β)
    (hD : ∀ y z : Y, dist y z ≤ 10 ^ 3 * Δ)
    {η : M → ℝ} {O : Set M} (hO : IsOpen O) (hLO : closedBall p (10 ^ 6 * Δ) ⊆ O)
    (hη : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η O) (hηl : LipschitzWith (Real.toNNReal (1 + σ)) η)
    (hval : ∀ x ∈ ball p (10 ^ 6 * Δ), |η x - (α.toFun x).fst| < Δ / 100)
    (h19 : ∀ x ∈ ball p (10 ^ 6 * Δ), ∀ x' ∈ ball p (10 ^ 6 * Δ / σ), 10 ^ 6 * Δ < dist x x' →
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x x') = x' →
      |mvfderiv (I := I) η x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ) :
    (∀ x ∈ ball p (10 ^ 6 * Δ), |η x| ≤ 905 * 10 ^ 3 * Δ →
      dist x p < 91 / 100 * (10 ^ 6 * Δ)) ∧
    (∀ x ∈ ball p (91 / 100 * (10 ^ 6 * Δ)), ∃ w : TangentSpace I x, g.inner x w w = 1 ∧
      3 / 4 < mvfderiv (I := I) η x w) ∧
    Icc (-(905 * 10 ^ 3 * Δ)) (905 * 10 ^ 3 * Δ) ⊆ η '' ball p (10 ^ 6 * Δ) ∧
    (∃ hreg : ∀ x ∈ ball p (10 ^ 6 * Δ), |η x| < 905 * 10 ^ 3 * Δ →
        ∃ w : E, mfderiv I 𝓘(ℝ, ℝ) η x w ≠ 0,
      let f := realSlabMap (ball p (10 ^ 6 * Δ)) isOpen_ball η hηl.continuous.continuousOn
        (905 * 10 ^ 3 * Δ)
      IsProperMap f ∧
      ∀ R (hR : 0 < R) (hRr : R < 905 * 10 ^ 3 * Δ),
        let y₀ : lineBallOpens (905 * 10 ^ 3 * Δ) :=
          ⟨0, zero_mem_lineBallOpens (hR.trans hRr)⟩
        let _ := regularFiberChartedSpace f y₀
          (contMDiff_realSlabMap isOpen_ball (hη.mono (ball_subset_closedBall.trans hLO)) _)
          (fun x _ ↦ surjective_mfderiv_realSlabMap isOpen_ball
            (hη.mono (ball_subset_closedBall.trans hLO)) hreg x)
        let U : TopologicalSpace.Opens (realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball η
            hηl.continuous.continuousOn (905 * 10 ^ 3 * Δ)) :=
          ⟨f ⁻¹' lineBallInner (905 * 10 ^ 3 * Δ) R,
            (lineBallInner (905 * 10 ^ 3 * Δ) R).isOpen.preimage
              (continuous_realSlabMap isOpen_ball _ _)⟩
        ∃ (hy : y₀ ∈ lineBallInner (905 * 10 ^ 3 * Δ) R) (Θ : Diffeomorph
            (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ).prod 𝓘(ℝ, ℝ)) I
            ({x // f x = y₀} × lineBallInner (905 * 10 ^ 3 * Δ) R) U ∞),
          (∀ q, f (Θ q).1 = q.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1)) ∧
    (∀ (ψ : ℝ → ℝ) (c : ℝ), ContDiff ℝ ∞ ψ → c ≤ 905 * 10 ^ 3 * Δ →
      (∀ s, c < |s| → ψ s = 0) →
      ContMDiff I 𝓘(ℝ, ℝ) ∞ ((ball p (10 ^ 6 * Δ)).indicator (ψ ∘ η)) ∧
        HasCompactSupport ((ball p (10 ^ 6 * Δ)).indicator (ψ ∘ η)) ∧
        tsupport ((ball p (10 ^ 6 * Δ)).indicator (ψ ∘ η)) ⊆
          {x | dist x p ≤ 91 / 100 * (10 ^ 6 * Δ) ∧ |η x| ≤ c}) := by
  have hβ := α.error_pos
  obtain ⟨hsq, hβR, hTR, hL3, hratio, hcL, hcβ, hca, hLβ⟩ :=
    slimPacket_coordinate_constants hΔ hσ hσ1 hβ hβΔ
  set L : ℝ := 10 ^ 6 * Δ with hLdef
  set r : ℝ := 91 / 100 * L with hrdef
  set a' : ℝ := 905 * 10 ^ 3 * Δ with ha'def
  have hΔ0 : 0 < Δ := by linarith
  have hrL : r < L := by rw [hrdef, hLdef]; nlinarith
  have hηc : Continuous η := hηl.continuous
  have hD' : ∀ y : Y, dist y y₀ ≤ 10 ^ 3 * Δ := fun y => hD y y₀
  -- (LFR20.2)
  have hencl : ∀ x ∈ ball p L, |η x| ≤ a' → dist x p < r := by
    intro x hx hxa
    exact (dist_le_of_abs_coord_le α hD' hval hLβ hx hxa).trans_lt hsq
  -- derivative
  have hder : ∀ x ∈ ball p r, ∃ w : TangentSpace I x, g.inner x w w = 1 ∧
      3 / 4 < mvfderiv (I := I) η x w := by
    intro x hx
    obtain ⟨w, hw, hlt⟩ := exists_unit_lt_mvfderiv_of_rankOne g hEnorm α h19 hrL.le hL3 hTR hβR hx
    exact ⟨w, hw, hratio.trans_lt hlt⟩
  -- the compact enclosing ball
  have hcpt : IsCompact (closedBall p r) := soul_isCompact_closedBall (I := I) g hEnorm p r
  have hηball : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η (ball p L) := hη.mono (ball_subset_closedBall.trans hLO)
  have hreg : ∀ x ∈ ball p L, |η x| < a' → ∃ w : E, mfderiv I 𝓘(ℝ, ℝ) η x w ≠ 0 := by
    intro x hx hxa
    obtain ⟨w, -, hlt⟩ := hder x (mem_ball.mpr (hencl x hx hxa.le))
    refine ⟨w, fun h0 => ?_⟩
    have : mvfderiv (I := I) η x w = 0 := by
      change (NormedSpace.fromTangentSpace (η x)).toContinuousLinearMap
        (mfderiv I 𝓘(ℝ, ℝ) η x w) = 0
      rw [h0, map_zero]
    linarith
  have hencl' : ∀ x ∈ ball p L, |η x| < a' → x ∈ closedBall p r :=
    fun x hx hxa => mem_closedBall.mpr (hencl x hx hxa.le).le
  have hKW : closedBall p r ⊆ ball p L := closedBall_subset_ball hrL
  obtain ⟨-, -, hprop, htriv⟩ :=
    exists_trivial_proper_slab_of_enclosure isOpen_ball hηball hreg hcpt hKW hencl'
  refine ⟨hencl, hder, ?_, ⟨hreg, hprop, htriv⟩, ?_⟩
  · have h := Icc_subset_image_ball_of_rankOne g hEnorm α hηc hval
      (c := 95 / 100 * L) (by positivity) hcL hcβ
    refine (Icc_subset_Icc ?_ ?_).trans h <;> linarith
  · intro ψ c hψ hca' hψc
    exact contMDiff_indicator_comp_of_enclosure hO (ball_subset_closedBall.trans hLO) hη hηc hψ
      hψc hrL hcpt fun x hx hxc => (hencl x hx (hxc.trans hca')).le

end DifferentialGeometry.Geometry.Collapse
