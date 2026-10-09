import DifferentialGeometry.Geometry.Fibration.ActualEdgeSection

/-!
# CGP03: actual sections through the inner coordinate balls (kernels on the LC87 family)

Blueprint `master207B.tex`, CGP03 (`lem:fibration-actual-inner-sections`, B:4004–4016): "Put
`ℓ_i = 1, Δ, 10⁵Δ` for `i ∈ I_2, I_e, I_s`. For each such `i` there is a continuous section
`s_i : B(0, 23ℓ_i/4) → U_i`, `η_i s_i(a) = a`, whose image lies in the original threshold-6
plateau of its adjustment. For edge charts it also has `t < Δ/100`. All points of this image have a
full `i` marker and scale in `[3R_i/4, 5R_i/4]`."

Reading (sheet C14-KC, decision D3): the plateau clause is `|η_i| < 6ℓ_i` (automatic, `23/4 < 6`)
together with the original cutoff `ζ_i = 1`, i.e. a FULL `i` marker `R_iζ_i = R_i` of
`𝓔⁰ = cgpGlobalMap`; `U_i` are CGP01's domains `B(j, 200ρ(j))`, `B(j, 10⁶Δρ(j))`, `B(j, 100Δρ(j))`.

* `CircleChart.exists_section_KC`, `SlimChart.exists_section_KC`: a continuous section of the chart
  coordinate over `B(0, R)` (LC83's trivial circle bundle over `B(0, R)`, `R < 100`; LFR20's trivial
  slab bundle over `(-R, R)`, `R < 905·10³Δ`).
* `scale_mem_of_dist_lt_KC`: a `Λ`-Lipschitz scale on `B(j, kρ(j))` with `Λk ≤ 1/4` lies in
  `[3ρ(j)/4, 5ρ(j)/4]`.
* `cgp03_circle_section`, `cgp03_slim_section` on any `L : LocalChartFamily`; `cgp03_edge_point`:
  a point of an EGP05 section with `|η_j| ≤ 8Δ` has a full edge marker and comparable scale.
The row `cgp03_row` (on the G10 family, with EGP05's sections) is in
`ActualInnerSectionsApplications.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A continuous section of an LC83 circle chart's coordinate over `B(0, R)`, `0 < R < 100`. -/
theorem CircleChart.exists_section_KC (c : CircleChart I M) {R : ℝ} (hR : 0 < R)
    (hRr : R < 100) :
    ∃ sec : ball (0 : ℝ²) R → M, Continuous sec ∧
      ∀ a, c.coord (sec a) = a ∧ sec a ∈ ball c.center 200 := by
  let _ := regularFiberChartedSpace
    (diskPreimageMap (ball c.center 200) isOpen_ball c.coord c.contMDiffOn_coord.continuousOn 100)
    (⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩ : planeBallOpens 100)
    (contMDiff_diskPreimageMap isOpen_ball c.contMDiffOn_coord 100)
    (fun x _ ↦ surjective_mfderiv_diskPreimageMap isOpen_ball c.contMDiffOn_coord c.rank 100 x)
  obtain ⟨hy, Θ, hΘ, -⟩ := c.trivial R hR hRr
  obtain ⟨x₀, hx₀⟩ := c.surjective ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
  have hmem : ∀ a : ball (0 : ℝ²) R, (a : ℝ²) ∈ planeBallOpens 100 := fun a =>
    mem_planeBallOpens_iff.mpr (by have := mem_ball_zero_iff.mp a.2; linarith)
  let ι : ball (0 : ℝ²) R → planeBallInner 100 R := fun a =>
    ⟨⟨a, hmem a⟩, mem_planeBallInner_iff.mpr (mem_ball_zero_iff.mp a.2)⟩
  have hι : Continuous ι :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  refine ⟨fun a => ((Θ (⟨x₀, hx₀⟩, ι a)).1 : M), ?_, fun a => ⟨?_, ?_⟩⟩
  · exact continuous_subtype_val.comp (continuous_subtype_val.comp
      (Θ.continuous.comp (continuous_const.prodMk hι)))
  · exact congrArg (fun z : planeBallOpens 100 => (z : ℝ²)) (hΘ (⟨x₀, hx₀⟩, ι a))
  · exact ((Θ (⟨x₀, hx₀⟩, ι a)).1).2.1

variable [SigmaCompactSpace M]

variable [NeZero (Module.finrank ℝ E)] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {Δ σ : ℝ}
  {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
  {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}

/-- A continuous section of an LC85 slim chart's coordinate over `(-R, R)`, `0 < R < 905·10³Δ`. -/
theorem SlimChart.exists_section_KC (c : SlimChart g hEnorm Δ σ α) {R : ℝ} (hR : 0 < R)
    (hRr : R < 905 * 10 ^ 3 * Δ) :
    ∃ sec : ball (0 : ℝ) R → M, Continuous sec ∧
      ∀ a, c.coord (sec a) = a ∧ sec a ∈ ball p (10 ^ 6 * Δ) := by
  let _ := regularFiberChartedSpace
    (realSlabMap (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord c.lipschitz.continuous.continuousOn
      (905 * 10 ^ 3 * Δ))
    (⟨0, zero_mem_lineBallOpens (hR.trans hRr)⟩ : lineBallOpens (905 * 10 ^ 3 * Δ))
    (contMDiff_realSlabMap isOpen_ball
      (c.contMDiffOn_coord.mono (ball_subset_closedBall.trans c.closedBall_subset_domain)) _)
    (fun x _ ↦ surjective_mfderiv_realSlabMap isOpen_ball
      (c.contMDiffOn_coord.mono (ball_subset_closedBall.trans c.closedBall_subset_domain))
      c.regular x)
  obtain ⟨hy, Θ, hΘ, -⟩ := c.trivial R hR hRr
  have h0 : (0 : ℝ) ∈ Icc (-(905 * 10 ^ 3 * Δ)) (905 * 10 ^ 3 * Δ) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨x, hxb, hx0⟩ := c.surjective h0
  have hxs : x ∈ realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
      c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ) :=
    mem_realSlabOpens_iff.mpr ⟨hxb, by rw [hx0, abs_zero]; linarith⟩
  have hx₀ : realSlabMap (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
      c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ) ⟨x, hxs⟩ =
      ⟨0, zero_mem_lineBallOpens (hR.trans hRr)⟩ := Subtype.ext hx0
  have hmem : ∀ a : ball (0 : ℝ) R, (a : ℝ) ∈ lineBallOpens (905 * 10 ^ 3 * Δ) := fun a =>
    mem_lineBallOpens_iff.mpr (by
      have := mem_ball_zero_iff.mp a.2
      rw [Real.norm_eq_abs] at this
      linarith)
  let ι : ball (0 : ℝ) R → lineBallInner (905 * 10 ^ 3 * Δ) R := fun a =>
    ⟨⟨a, hmem a⟩, mem_lineBallInner_iff.mpr (by
      have := mem_ball_zero_iff.mp a.2
      rwa [Real.norm_eq_abs] at this)⟩
  have hι : Continuous ι :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  refine ⟨fun a => ((Θ (⟨⟨x, hxs⟩, hx₀⟩, ι a)).1 : M), ?_, fun a => ⟨?_, ?_⟩⟩
  · exact continuous_subtype_val.comp (continuous_subtype_val.comp
      (Θ.continuous.comp (continuous_const.prodMk hι)))
  · exact congrArg (fun z : lineBallOpens (905 * 10 ^ 3 * Δ) => (z : ℝ))
      (hΘ (⟨⟨x, hxs⟩, hx₀⟩, ι a))
  · exact ((Θ (⟨⟨x, hxs⟩, hx₀⟩, ι a)).1).2.1

end Abstract

/-- A `Λ`-Lipschitz positive scale on `B(j, kρ(j))` with `Λk ≤ 1/4` lies in `[3ρ(j)/4, 5ρ(j)/4]`. -/
theorem scale_mem_of_dist_lt_KC {X : Type*} [MetricSpace X] {ρ : X → ℝ} {Λ k : ℝ}
    (hρL : LipschitzWith (Real.toNNReal Λ) ρ) (hΛ : 0 ≤ Λ) {j x : X} (hj : 0 < ρ j)
    (hd : dist x j < k * ρ j) (hk : Λ * k ≤ 1 / 4) :
    3 / 4 * ρ j ≤ ρ x ∧ ρ x ≤ 5 / 4 * ρ j := by
  have h1 := hρL.dist_le_mul x j
  rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1
  have h2 : Λ * dist x j ≤ Λ * (k * ρ j) := mul_le_mul_of_nonneg_left hd.le hΛ
  have h3 : Λ * (k * ρ j) ≤ 1 / 4 * ρ j := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hk hj.le
  have h4 := abs_le.mp (h1.trans (h2.trans h3))
  constructor <;> linarith [h4.1, h4.2]

section Family

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}
  {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc : ℝ}

/-- **CGP03, circle kind**, on the actual LC87 family. -/
theorem cgp03_circle_section
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΛ : 0 ≤ Λ)
    (hbud : Λ * 102 ≤ 1 / 4) {j : X} (hj : j ∈ L.circle.centres) :
    ∃ sec : ball (0 : ℝ²) (23 / 4) → X, Continuous sec ∧ ∀ a,
      (let c := L.circle.chart j hj;
        letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord (sec a)) = a ∧
      sec a ∈ ball j (200 * ρ j) ∧ L.circle.cutoff j (sec a) = 1 ∧
      3 / 4 * ρ j ≤ ρ (sec a) ∧ ρ (sec a) ≤ 5 / 4 * ρ j := by
  have hrj := hρ j
  have hscale := fun x (hx : dist x j < 102 * ρ j) =>
    scale_mem_of_dist_lt_KC L.lipschitz_scale hΛ hrj hx hbud
  have hcen := L.circle.chart_center j hj
  have hone := L.circle.cutoff_eq_one j hj
  let c := L.circle.chart j hj
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hc : c.center = j := hcen
  obtain ⟨sec, hsc, hs⟩ := c.exists_section_KC (R := 23 / 4) (by norm_num) (by norm_num)
  refine ⟨sec, hsc, fun a => ?_⟩
  obtain ⟨hco, hb⟩ := hs a
  have hnorm : ‖c.coord (sec a)‖ < 23 / 4 := by rw [hco]; exact mem_ball_zero_iff.mp a.2
  have h102 := c.enclosure (sec a) hb (by linarith)
  rw [hc] at h102 hb
  have hd : (ρ j)⁻¹ * @dist X mX.toDist (sec a) j < 102 := h102
  rw [inv_mul_lt_iff₀ hrj] at hd
  have hd' : @dist X mX.toDist (sec a) j < 102 * ρ j := by linarith
  refine ⟨hco, ?_, hone (sec a) hb (by linarith), hscale (sec a) hd'⟩
  change @dist X mX.toDist (sec a) j < 200 * ρ j
  linarith

/-- **CGP03, slim kind**, on the actual LC87 family. -/
theorem cgp03_slim_section
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ)
    (hΛ : 0 ≤ Λ) (hbud : Λ * (10 ^ 6 * Δ) ≤ 1 / 4) {j : X} (hj : j ∈ L.slim.centres) :
    ∃ sec : ball (0 : ℝ) (23 / 4 * (10 ^ 5 * Δ)) → X, Continuous sec ∧ ∀ a,
      (L.slim.centre j hj).coord (sec a) = a ∧ sec a ∈ ball j (10 ^ 6 * Δ * ρ j) ∧
      L.slim.cutoff j (sec a) = 1 ∧ 3 / 4 * ρ j ≤ ρ (sec a) ∧ ρ (sec a) ≤ 5 / 4 * ρ j := by
  have hrj := hρ j
  have hscale := fun x (hx : dist x j < 10 ^ 6 * Δ * ρ j) =>
    scale_mem_of_dist_lt_KC L.lipschitz_scale hΛ hrj hx hbud
  let S := L.slim.centre j hj
  let P := S.packet
  let iZ := S.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  obtain ⟨sec, hsc, hs⟩ := P.toSlimChart.exists_section_KC (R := 23 / 4 * (10 ^ 5 * Δ))
    (by positivity) (by nlinarith)
  refine ⟨sec, hsc, fun a => ?_⟩
  obtain ⟨hco, hb⟩ := hs a
  have ha : |(a : ℝ)| < 23 / 4 * (10 ^ 5 * Δ) := by
    have := mem_ball_zero_iff.mp a.2
    rwa [Real.norm_eq_abs] at this
  have hd : (ρ j)⁻¹ * @dist X mX.toDist (sec a) j < 10 ^ 6 * Δ := hb
  rw [inv_mul_lt_iff₀ hrj] at hd
  have hd' : @dist X mX.toDist (sec a) j < 10 ^ 6 * Δ * ρ j := by linarith
  have hcut : P.cutoff (sec a) = 1 := P.cutoff_eq_one (sec a) hb (by
    have h1 : P.coord (sec a) = a := hco
    rw [h1]
    nlinarith)
  refine ⟨hco, hd', ?_, hscale (sec a) hd'⟩
  unfold SlimFamily.cutoff
  rw [dite_eq_left hj]
  exact hcut

/-- **CGP03, edge kind, pointwise**: a point of `B(j, 10Δρ(j))` with `|η_j| ≤ 8Δ` and
`t = F/ρ ≤ 8Δ` (e.g. a point of an EGP05 section over `B(0, 23Δ/4)`) lies in `U_j`, has a full
edge marker and comparable scale. -/
theorem cgp03_edge_point
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ)
    (hΛ : 0 ≤ Λ) (hbud : Λ * (10 * Δ) ≤ 1 / 4) {j : X} (hj : j ∈ L.edge.centres) {x : X}
    (hη : |L.edge.coord j x| ≤ 8 * Δ) (ht : L.edge.smoothing x / ρ x ≤ 8 * Δ)
    (hd : dist x j < 10 * Δ * ρ j) :
    x ∈ ball j (100 * Δ * ρ j) ∧ L.edge.cutoff j x = 1 ∧
      3 / 4 * ρ j ≤ ρ x ∧ ρ x ≤ 5 / 4 * ρ j := by
  have hrj := hρ j
  have hx : x ∈ ball j (100 * Δ * ρ j) := by
    rw [mem_ball]
    nlinarith
  exact ⟨hx, L.edge.cutoff_eq_one_of_le hΔ hj hx hη ht,
    scale_mem_of_dist_lt_KC L.lipschitz_scale hΛ hrj hd hbud⟩

end Family

end DifferentialGeometry.Geometry.Collapse
