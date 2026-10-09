import DifferentialGeometry.Geometry.Metric.Approximation.CoarseBorderEnclosure
import DifferentialGeometry.Analysis.Calculus.Cutoff.IntervalProfiles
import DifferentialGeometry.Geometry.Collapse.EdgeScaledSmoothing

/-!
# LFR28, step 5: the smooth compactly supported source cutoff

Blueprint 207A, LFR28 (`thm:collapse-finite-source-edge-packet`, A:27223–27467), last sentence of
the statement and proof step 5 (A:27446–27455): "Choose smooth profiles with plateau
`[-8Δ, 8Δ]` in the first variable and `(-∞, 8Δ]` in the second, supported respectively in
`[-8.9Δ, 8.9Δ]` and `(-∞, 8.9Δ]`. Their product evaluated at `(f_i, η_i)` is smooth: the second
profile is constant near the nonsmooth core, and its transition lies in LFR27's smooth collar.
Repeating (LFR28.6) with `9` in place of `4` puts its closed support inside `B(p_i, 13Δ)`, strictly
inside the chart. Extension by zero is therefore smooth and compactly supported."

This step uses only the chart, LFR27's output clauses for `F` (value, continuity, smoothness on its
collar) and the LFR19 coordinate's value and smoothness; no finite model (LFR14) is involved.

* `coarseBorder_source_slab_nine_subset_ball`: (LFR28.6) with `9` in place of `4`: the slab
  `{|f| ≤ 9Δ, F/ρ ≤ 9Δ} ∩ B(p, 100Δ)` lies in `B(p, 12.9Δ)` (a copy of W4-F7d1's
  `coarseBorder_source_slab_subset_ball` with the constants changed).
* `exists_edge_source_cutoff`: the cutoff `ζ = φ₁(f/Δ) φ₂((F/ρ)/Δ)` on `B(p, 100Δ)`, extended by
  zero, is smooth on `M`, compactly supported, `[0,1]`-valued, equal to one on
  `{|f| ≤ 8Δ, F/ρ ≤ 8Δ}`, with `tsupport ζ ⊆ B(p, 13Δ) ∩ {|f| < 9Δ, F/ρ < 9Δ}`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Analysis

namespace GC.MetricGeometry

variable {X : Type*} [MetricSpace X]

/-- **(LFR28.6) with `9` in place of `4`.** -/
theorem coarseBorder_source_slab_nine_subset_ball {Q : X → WithLp 2 (ℝ × ℝ)} {p : X} {A : Set X}
    {f F ρ : X → ℝ} {Δ τ μ lam : ℝ} (hΔ : 0 < Δ) (hτ : τ ≤ 1 / 10000) (hμ : μ ≤ 1 / 100)
    (hlam : lam ≤ 1 / 100) (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hpA : p ∈ A) (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hf : ∀ x ∈ ball p (100 * Δ), |f x - (Q x).fst| ≤ μ * Δ)
    (hF : ∀ x ∈ ball p (100 * Δ), |F x - infDist x A| ≤ μ * Δ)
    (hρ : ∀ x ∈ ball p (100 * Δ), 0 < ρ x ∧ ρ x ≤ 1 + lam)
    {x : X} (hx : x ∈ ball p (100 * Δ)) (hfx : |f x| ≤ 9 * Δ) (hηx : F x / ρ x ≤ 9 * Δ) :
    dist x p < 129 / 10 * Δ := by
  have hp : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  have hτ0 : 0 ≤ τ * Δ := by simpa using hdist p hp p hp
  have hxp : dist x p < 100 * Δ := hx
  have hx200 : x ∈ ball p (200 * Δ) := (show dist x p < 200 * Δ by linarith)
  obtain ⟨hρ0, hρ1⟩ := hρ x hx
  have hu : |(Q x).fst| ≤ (9 + μ) * Δ := by
    have h := abs_le.mp (hf x hx)
    have h' := abs_le.mp hfx
    rw [abs_le]
    constructor <;> nlinarith
  have hFx : F x ≤ 9 * Δ * (1 + lam) := by
    rw [div_le_iff₀ hρ0] at hηx
    nlinarith
  have hax : infDist x A ≤ (9 * (1 + lam) + μ) * Δ := by
    have h := (abs_le.mp (hF x hx)).1
    nlinarith
  have hμ0 : 0 ≤ μ * Δ := (abs_nonneg _).trans (hF x hx)
  have hlam0 : -1 ≤ lam := by
    by_contra h
    push Not at h
    linarith
  have hbx : (Q x).snd ≤ infDist x A + 2 * (τ * Δ) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨z, hzA, hz⟩ := (infDist_lt_iff ⟨p, hpA⟩).mp
      (show infDist x A < min ((Q x).snd - 2 * (τ * Δ)) (infDist x A + Δ) from
        lt_min (by linarith) (by linarith))
    have hz1 := hz.trans_le (min_le_left _ _)
    have hz2 := hz.trans_le (min_le_right _ _)
    have hzp : dist z p < 190 * Δ := by
      have := dist_triangle z x p
      rw [dist_comm z x] at this
      nlinarith
    have hz200 : z ∈ ball p (200 * Δ) := (show dist z p < 200 * Δ by linarith)
    have hd := (abs_le.mp (hdist x hx200 z hz200)).2
    have hsnd : (Q x).snd - (Q z).snd ≤ dist (Q x) (Q z) := by
      have h := WithLp.dist_snd_le (Q x) (Q z)
      rw [Real.dist_eq] at h
      linarith [le_abs_self ((Q x).snd - (Q z).snd)]
    linarith [hborder z ⟨hzA, hzp⟩]
  have hb0 := hheight x hx200
  have hnorm : ‖Q x‖ < 1285 / 100 * Δ := by
    have hsq := WithLp.prod_norm_sq_eq_of_L2 (Q x)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at hsq
    have h1 : (Q x).fst ^ 2 ≤ ((9 + μ) * Δ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hu 2
    have hb : (Q x).snd ≤ (9 * (1 + lam) + μ + 2 * τ) * Δ := by nlinarith
    have h2 : (Q x).snd ^ 2 ≤ ((9 * (1 + lam) + μ + 2 * τ) * Δ) ^ 2 :=
      pow_le_pow_left₀ hb0 hb 2
    have hlt : ‖Q x‖ ^ 2 < (1285 / 100 * Δ) ^ 2 := by
      rw [hsq]
      have hc1 : (9 + μ) * Δ ≤ 901 / 100 * Δ := by nlinarith
      have hc2 : (9 * (1 + lam) + μ + 2 * τ) * Δ ≤ 91002 / 10000 * Δ := by nlinarith
      have hc1' : 0 ≤ (9 + μ) * Δ := by nlinarith [abs_nonneg (Q x).fst]
      have hc2' : 0 ≤ (9 * (1 + lam) + μ + 2 * τ) * Δ := hb0.trans hb
      nlinarith [pow_le_pow_left₀ hc1' hc1 2, pow_le_pow_left₀ hc2' hc2 2]
    exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp hlt
  have h := (abs_le.mp (hdist x hx200 p hp)).1
  rw [hQp, dist_zero_right] at h
  nlinarith


end GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

open GC.MetricGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LFR28, step 5.** See the module docstring. -/
theorem exists_edge_source_cutoff (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {Q : M → WithLp 2 (ℝ × ℝ)} {p : M} {A O : Set M} {f F ρ : M → ℝ} {Δ τ μ : ℝ} {Λ : ℝ≥0}
    (hΔ : 0 < Δ) (hτ : τ ≤ 1 / 10000) (hμ : μ ≤ 1 / 100) (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hpA : p ∈ A) (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hf : ∀ x ∈ ball p (100 * Δ), |f x - (Q x).fst| ≤ μ * Δ)
    (hfs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball p (100 * Δ)))
    (hF : ∀ x, |F x - infDist x A| ≤ μ * Δ) (hFc : Continuous F) (hO : IsOpen O)
    (hCO : closedBall p (20 * Δ) ∩ {x | 3 / 4 * Δ ≤ infDist x A ∧ infDist x A ≤ 21 / 2 * Δ} ⊆ O)
    (hFO : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1)
    (hρs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ρ (ball p (100 * Δ))) (hlam : 100 * Δ * Λ ≤ 1 / 100) :
    ∃ ζ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧ (∀ x, ζ x ∈ Icc 0 1) ∧
      (∀ x ∈ ball p (100 * Δ), ζ x = intervalPlateauProfile (-(89 / 10)) (-8) 8 (89 / 10)
        (f x / Δ) * descendingIntervalProfile 8 (89 / 10) (F x / ρ x / Δ)) ∧
      (∀ x ∈ ball p (100 * Δ), |f x| ≤ 8 * Δ → F x / ρ x ≤ 8 * Δ → ζ x = 1) ∧
      tsupport ζ ⊆ ball p (13 * Δ) ∩ {x | |f x| < 9 * Δ ∧ F x / ρ x < 9 * Δ} := by
  set φ₁ : ℝ → ℝ := intervalPlateauProfile (-(89 / 10)) (-8) 8 (89 / 10) with hφ₁
  set φ₂ : ℝ → ℝ := descendingIntervalProfile 8 (89 / 10) with hφ₂
  set P : M → ℝ := fun x => φ₁ (f x / Δ) * φ₂ (F x / ρ x / Δ) with hP
  set ζ : M → ℝ := (ball p (100 * Δ)).indicator P with hζ
  have hball : IsOpen (ball p (100 * Δ)) := isOpen_ball
  -- the scale on the chart ball
  have hρb (x : M) (hx : x ∈ ball p (100 * Δ)) : 99 / 100 ≤ ρ x ∧ ρ x ≤ 101 / 100 := by
    have h := hρ.dist_le_mul x p
    rw [Real.dist_eq, hρp] at h
    have hxp : dist x p < 100 * Δ := hx
    have h2 : (Λ : ℝ) * dist x p ≤ Λ * (100 * Δ) :=
      mul_le_mul_of_nonneg_left hxp.le Λ.coe_nonneg
    have h3 : (Λ : ℝ) * (100 * Δ) = 100 * Δ * Λ := by ring
    constructor <;> linarith [(abs_le.mp (h.trans h2)).1, (abs_le.mp (h.trans h2)).2]
  have hρne (x : M) (hx : x ∈ ball p (100 * Δ)) : ρ x ≠ 0 := by
    linarith [(hρb x hx).1]
  have hηc : ContinuousOn (fun x => F x / ρ x) (ball p (100 * Δ)) :=
    hFc.continuousOn.div hρs.continuousOn hρne
  have hfc : ContinuousOn f (ball p (100 * Δ)) := hfs.continuousOn
  -- nonvanishing forces the strict profile windows
  have hwin (x : M) (hPx : P x ≠ 0) :
      |f x| < 89 / 10 * Δ ∧ F x / ρ x < 89 / 10 * Δ := by
    have h1 : φ₁ (f x / Δ) ≠ 0 := left_ne_zero_of_mul hPx
    have h2 : φ₂ (F x / ρ x / Δ) ≠ 0 := right_ne_zero_of_mul hPx
    have hlo : -(89 / 10) < f x / Δ := by
      by_contra h
      exact h1 (intervalPlateauProfile_zero_left (by norm_num) (le_of_not_gt h))
    have hhi : f x / Δ < 89 / 10 := by
      by_contra h
      exact h1 (intervalPlateauProfile_zero_right (by norm_num) (le_of_not_gt h))
    have hη : F x / ρ x / Δ < 89 / 10 := by
      by_contra h
      exact h2 (descendingIntervalProfile_zero (by norm_num) (le_of_not_gt h))
    rw [lt_div_iff₀ hΔ] at hlo
    rw [div_lt_iff₀ hΔ] at hhi hη
    exact ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, by linarith⟩
  -- enclosure (LFR28.6 with 9)
  have henc (x : M) (hx : x ∈ ball p (100 * Δ)) (hPx : P x ≠ 0) : dist x p < 129 / 10 * Δ := by
    obtain ⟨hfx, hηx⟩ := hwin x hPx
    exact coarseBorder_source_slab_nine_subset_ball (f := f) (F := F) (ρ := ρ) hΔ hτ hμ
      (lam := 1 / 100) (by norm_num) hQp
      hdist hheight hpA hborder hf (fun y _ => hF y)
      (fun y hy => ⟨by linarith [(hρb y hy).1], by linarith [(hρb y hy).2]⟩) hx
      (by linarith) (by linarith)
  have hζzero (x : M) (hx : 129 / 10 * Δ < dist x p) : ζ x = 0 := by
    by_cases hxb : x ∈ ball p (100 * Δ)
    · rw [hζ, indicator_of_mem hxb]
      by_contra hPx
      linarith [henc x hxb hPx]
    · rw [hζ, indicator_of_notMem hxb]
  have hfar : IsOpen {y : M | 129 / 10 * Δ < dist y p} :=
    isOpen_lt continuous_const (continuous_id.dist continuous_const)
  refine ⟨ζ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hxfar : 129 / 10 * Δ < dist x p
    · have he : ζ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (hfar.mem_nhds hxfar) fun y hy => hζzero y hy
      exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq he
    have hxb : x ∈ ball p (100 * Δ) := by
      change dist x p < 100 * Δ
      linarith [le_of_not_gt hxfar]
    have hζP : ζ =ᶠ[𝓝 x] P :=
      Filter.eventually_of_mem (hball.mem_nhds hxb) fun y hy => by rw [hζ, indicator_of_mem hy]
    have hc1 : ContDiff ℝ ∞ (fun t : ℝ => φ₁ (t / Δ)) :=
      (contDiff_intervalPlateauProfile _ _ _ _).comp (contDiff_id.div_const Δ)
    have hc2 : ContDiff ℝ ∞ (fun t : ℝ => φ₂ (t / Δ)) :=
      (contDiff_descendingIntervalProfile _ _).comp (contDiff_id.div_const Δ)
    have hfx : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x := hfs.contMDiffAt (hball.mem_nhds hxb)
    have hηx := hηc.continuousAt (hball.mem_nhds hxb)
    rcases lt_or_ge (F x / ρ x) (8 * Δ) with hlow | hge
    · -- the second profile is constant one near `x`
      have hev : ∀ᶠ y in 𝓝 x, y ∈ ball p (100 * Δ) ∧ F y / ρ y < 8 * Δ :=
        (hball.eventually_mem hxb).and (hηx.eventually (gt_mem_nhds hlow))
      have he : ζ =ᶠ[𝓝 x] fun y => φ₁ (f y / Δ) := by
        filter_upwards [hev] with y hy
        rw [hζ, indicator_of_mem hy.1]
        change φ₁ (f y / Δ) * φ₂ (F y / ρ y / Δ) = φ₁ (f y / Δ)
        rw [hφ₂, descendingIntervalProfile_one (by norm_num)
          (by rw [div_le_iff₀ hΔ]; linarith [hy.2]), mul_one]
      exact (hc1.comp_contMDiffAt hfx).congr_of_eventuallyEq he
    rcases lt_or_ge (89 / 10 * Δ) (F x / ρ x) with hhigh | hmid
    · -- the second profile vanishes near `x`
      have he : ζ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [hball.mem_nhds hxb, hηx.eventually (lt_mem_nhds hhigh)] with y hy hyη
        rw [hζ, indicator_of_mem hy]
        change φ₁ (f y / Δ) * φ₂ (F y / ρ y / Δ) = 0
        rw [hφ₂, descendingIntervalProfile_zero (by norm_num)
          (by rw [le_div_iff₀ hΔ]; linarith), mul_zero]
      exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq he
    · -- the transition happens inside LFR27's smooth collar
      obtain ⟨hρ1, hρ2⟩ := hρb x hxb
      have hρpos : 0 < ρ x := by linarith
      have hFx : F x = F x / ρ x * ρ x := by field_simp
      have hFlo : 792 / 100 * Δ ≤ F x := by rw [hFx]; nlinarith
      have hFhi : F x ≤ 8989 / 1000 * Δ := by rw [hFx]; nlinarith
      have hd := abs_le.mp (hF x)
      have hμΔ : μ * Δ ≤ Δ / 100 := by nlinarith
      have hxC : x ∈ closedBall p (20 * Δ) ∩
          {x | 3 / 4 * Δ ≤ infDist x A ∧ infDist x A ≤ 21 / 2 * Δ} := by
        refine ⟨?_, ?_, ?_⟩
        · change dist x p ≤ 20 * Δ
          linarith [le_of_not_gt hxfar]
        · linarith [hd.2]
        · linarith [hd.1]
      have hFAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ F x := hFO.contMDiffAt (hO.mem_nhds (hCO hxC))
      have hρAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ ρ x := hρs.contMDiffAt (hball.mem_nhds hxb)
      have hηAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => F y / ρ y) x :=
        hFAt.div₀ hρAt hρpos.ne'
      exact ((hc1.comp_contMDiffAt hfx).mul (hc2.comp_contMDiffAt hηAt)).congr_of_eventuallyEq
        hζP
  · -- compact support
    have hsub : tsupport ζ ⊆ closedBall p (129 / 10 * Δ) := by
      apply closure_minimal _ isClosed_closedBall
      intro x hx
      by_contra hout
      exact hx (hζzero x (lt_of_not_ge hout))
    exact (soul_isCompact_closedBall (I := I) g hEnorm p _).of_isClosed_subset
      (isClosed_tsupport ζ) hsub
  · intro x
    by_cases hxb : x ∈ ball p (100 * Δ)
    · rw [hζ, indicator_of_mem hxb]
      have h1 := intervalPlateauProfile_mem_Icc (-(89 / 10)) (-8) 8 (89 / 10) (f x / Δ)
      have h2 := descendingIntervalProfile_mem_Icc 8 (89 / 10) (F x / ρ x / Δ)
      exact ⟨mul_nonneg h1.1 h2.1,
        (mul_le_mul_of_nonneg_left h2.2 h1.1).trans (by simpa using h1.2)⟩
    · rw [hζ, indicator_of_notMem hxb]
      exact ⟨le_rfl, zero_le_one⟩
  · intro x hxb
    rw [hζ, indicator_of_mem hxb]
  · intro x hxb hfx hηx
    rw [hζ, indicator_of_mem hxb]
    change φ₁ (f x / Δ) * φ₂ (F x / ρ x / Δ) = 1
    have hf1 : f x / Δ ∈ Icc (-8 : ℝ) 8 := by
      have h := abs_le.mp hfx
      constructor
      · rw [le_div_iff₀ hΔ]; linarith [h.1]
      · rw [div_le_iff₀ hΔ]; linarith [h.2]
    rw [hφ₁, hφ₂, intervalPlateauProfile_one (by norm_num) (by norm_num) hf1,
      descendingIntervalProfile_one (by norm_num) (by rw [div_le_iff₀ hΔ]; linarith), one_mul]
  · -- the closed support stays strictly inside the windows
    let G : M → ℝ := fun x => max |f x| (F x / ρ x)
    have hcb : closedBall p (129 / 10 * Δ) ⊆ ball p (100 * Δ) :=
      closedBall_subset_ball (by linarith)
    have habs : ContinuousOn (fun x => |f x|) (closedBall p (129 / 10 * Δ)) :=
      continuous_abs.comp_continuousOn (hfc.mono hcb)
    have hGc : ContinuousOn G (closedBall p (129 / 10 * Δ)) :=
      ContinuousOn.sup habs (hηc.mono hcb)
    have hK : IsClosed (closedBall p (129 / 10 * Δ) ∩ G ⁻¹' Iic (89 / 10 * Δ)) :=
      hGc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Iic
    have hsupp : tsupport ζ ⊆ closedBall p (129 / 10 * Δ) ∩ G ⁻¹' Iic (89 / 10 * Δ) := by
      apply closure_minimal _ hK
      intro x hx
      have hxb : x ∈ ball p (100 * Δ) := by
        by_contra hxb
        exact hx (by rw [hζ, indicator_of_notMem hxb])
      have hPx : P x ≠ 0 := by
        intro h0
        exact hx (by rw [hζ, indicator_of_mem hxb, h0])
      obtain ⟨hw1, hw2⟩ := hwin x hPx
      exact ⟨mem_closedBall.mpr (henc x hxb hPx).le,
        show G x ≤ 89 / 10 * Δ from max_le hw1.le hw2.le⟩
    intro x hx
    obtain ⟨hx1, hx2⟩ := hsupp hx
    have hxG : G x ≤ 89 / 10 * Δ := hx2
    refine ⟨?_, ?_, ?_⟩
    · change dist x p < 13 * Δ
      linarith [mem_closedBall.mp hx1]
    · linarith [le_max_left |f x| (F x / ρ x)]
    · linarith [le_max_right |f x| (F x / ρ x)]

end DifferentialGeometry.Geometry.Collapse
