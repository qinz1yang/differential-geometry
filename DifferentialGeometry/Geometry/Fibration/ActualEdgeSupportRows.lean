import DifferentialGeometry.Geometry.Fibration.ActualSupportRows

/-!
# FC18 (ii) and the FC12 edge half on the actual strong-edge centres

Blueprint `master207B.tex`, FC18 (`prop:fibration-support-enclosures`, B:1199, case (ii)) and FC12
(`lem:fibration-buffered-domain`, B:738, edge row of its budget table).

* `fc18_edge_support_kernel`: the metric core of FC18 (ii) in the normalized metric: if the
  pointed composite `Q = (u, h)` has distortion `δ ≤ Δ/100` on `B(p, 200Δ)`, `h ≥ 0`, every point
  of `A` in `B(p, 120Δ)` has `h < Δ/10` (FC17), and `|η − u| ≤ Δ/100` on `B(p, 100Δ)`, then a
  point `x ∈ B(p, 100Δ)` with `|η(x)| < 9Δ` within `46Δ/5` of `A` has `d(p, x) < 14Δ`.
* `EdgeFamily.mem_of_cutoff_ne_zero`: where an actual edge cutoff is nonzero, `x` lies in the
  chart ball `B(j, 100Δ)` (normalized), `|η_j(x)| < 9Δ` and `F(x)/ρ(x) < 9Δ` (the two factors of
  KL (9.19)).
* `fc18_edge_row`: at every actual strong-edge centre `j` there is the original composite `Q`
  (FC17's clauses) such that, as soon as the chart coordinate is `Δ/100`-close to `Q`'s first
  coordinate on `B(j, 100Δ)`, the closed support of the actual edge cutoff lies in
  `B̄(j, 14Δρ(j)) ⊆ B(j, 20Δρ(j))`.
* `fc12_edge_row`: under the same link, FC12's buffered-domain conclusion for every test ball
  `B(p, Rρ(p))` meeting that support (support radius `14Δ`, smooth coordinate domain `100Δ`).

The link `|η_j − u| ≤ Δ/100` relates the chart's own adapted coordinate to the composite of the
centre's strong-edge maps; `EdgeChart` records the coordinate's value bound against its own
splitting `split`, not against that composite. Supplying it is LC87 packet (iv) (edge auxiliary
packet); it is an explicit hypothesis here (no new Prop).
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

/-- The metric core of FC18 (ii) in the normalized metric. -/
theorem fc18_edge_support_kernel {Y : Type*} [PseudoMetricSpace Y]
    {Q : Y → WithLp 2 (ℝ × ℝ)} {η : Y → ℝ} {A : Set Y} {p : Y} {Δ δ : ℝ} (hΔ : 0 < Δ)
    (hδ : δ ≤ Δ / 100) (hQp : Q p = 0) (hQnn : ∀ x, 0 ≤ (Q x).snd)
    (hQdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ δ)
    (hlow : ∀ z ∈ A ∩ ball p (120 * Δ), (Q z).snd < Δ / 10)
    (hη : ∀ x ∈ ball p (100 * Δ), |η x - (Q x).fst| ≤ Δ / 100) {x : Y}
    (hx : x ∈ ball p (100 * Δ)) (hηx : |η x| < 9 * Δ) (hA : ∃ z ∈ A, dist x z < 46 * Δ / 5) :
    dist x p < 14 * Δ := by
  obtain ⟨z, hzA, hxz⟩ := hA
  have hxp : dist x p < 100 * Δ := hx
  have hzp : dist z p < 120 * Δ := by
    have := dist_triangle z x p
    rw [dist_comm z x] at this
    linarith
  have hQz := hlow z ⟨hzA, hzp⟩
  have hQzn := hQnn z
  have hdxz := (abs_le.mp (hQdist x (mem_ball.mpr (by linarith)) z
    (mem_ball.mpr (by linarith)))).2
  have hsnd : |(Q x).snd - (Q z).snd| ≤ dist (Q x) (Q z) := by
    have h := WithLp.dist_snd_le (Q x) (Q z)
    rwa [Real.dist_eq] at h
  have hsx : (Q x).snd ≤ 931 * Δ / 100 := by
    linarith [(abs_le.mp hsnd).2]
  have hsx0 := hQnn x
  have hfx : |(Q x).fst| ≤ 901 * Δ / 100 := by
    have := hη x hx
    have h1 := abs_sub_abs_le_abs_sub (Q x).fst (η x)
    rw [abs_sub_comm] at h1
    linarith
  have hnorm : ‖Q x‖ < 13 * Δ := by
    rw [WithLp.prod_norm_eq_of_L2, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    rw [Real.sqrt_lt' (by positivity)]
    have h1 : (Q x).fst ^ 2 ≤ (901 * Δ / 100) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hfx 2
    have h2 : (Q x).snd ^ 2 ≤ (931 * Δ / 100) ^ 2 := pow_le_pow_left₀ hsx0 hsx 2
    nlinarith
  have hdxp := (abs_le.mp (hQdist x (mem_ball.mpr (by linarith)) p
    (mem_ball_self (by positivity)))).1
  rw [hQp, dist_zero_right] at hdxp
  linarith

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}
  {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc : ℝ}

/-- Where an actual edge cutoff is nonzero, both factors of KL (9.19) are positive: `x` lies in the
chart ball `B(j, 100Δ)` (normalized), `|η_j(x)| < 9Δ` and `F(x)/ρ(x) < 9Δ`. -/
theorem EdgeFamily.mem_of_cutoff_ne_zero
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ) {j x : X}
    (h : F.cutoff j x ≠ 0) :
    j ∈ F.centres ∧ (ρ j)⁻¹ * dist x j < 100 * Δ ∧ |F.coord j x| < 9 * Δ ∧
      F.smoothing x / ρ x < 9 * Δ := by
  by_cases hj : j ∈ F.centres
  swap
  · exfalso
    apply h
    unfold EdgeFamily.cutoff
    rw [dite_eq_right hj]
    rfl
  refine ⟨hj, ?_⟩
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hrx := hρ x
  let Fs := F.smoothing
  have hq : Fs x / ρ j / (Δ * (ρ x / ρ j)) = Fs x / ρ x / Δ := by
    field_simp
  unfold EdgeFamily.coord
  rw [dite_eq_left hj]
  unfold EdgeFamily.cutoff at h
  rw [dite_eq_left hj] at h
  let C := F.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  change (Subtype.val : ball C.center (100 * Δ) → X).extend
      (fun y => edgeCoordinateProfile (C.coord y.val / Δ) *
        edgeHeightProfile (Fs y.val / ρ j / (Δ * (ρ y.val / ρ j)))) 0 x ≠ 0 at h
  by_cases hmem : x ∈ ball C.center (100 * Δ)
  swap
  · exfalso
    apply h
    rw [Function.extend_apply' _ _ _ (fun ⟨a, ha⟩ => hmem (ha ▸ a.property))]
    rfl
  have hval := h
  rw [show x = ((⟨x, hmem⟩ : ball C.center (100 * Δ)) : X) from rfl,
    Subtype.val_injective.extend_apply] at hval
  have hball : (ρ j)⁻¹ * @dist X mX.toDist x j < 100 * Δ := by
    have hm : x ∈ ball C.center (100 * Δ) := hmem
    rw [hc'] at hm
    exact hm
  have hcoord : edgeCoordinateProfile (C.coord x / Δ) ≠ 0 := left_ne_zero_of_mul hval
  have hheight : edgeHeightProfile (Fs x / ρ j / (Δ * (ρ x / ρ j))) ≠ 0 :=
    right_ne_zero_of_mul hval
  refine ⟨hball, ?_, ?_⟩
  · change |C.coord x| < 9 * Δ
    rw [abs_lt]
    constructor
    · by_contra hle
      apply hcoord
      refine intervalPlateauProfile_zero_left (by norm_num) ?_
      rw [div_le_iff₀ hΔ]
      linarith
    · by_contra hle
      apply hcoord
      refine intervalPlateauProfile_zero_right (by norm_num) ?_
      rw [le_div_iff₀ hΔ]
      linarith
  · by_contra hle
    apply hheight
    rw [hq]
    refine descendingIntervalProfile_zero (by norm_num) ?_
    rw [le_div_iff₀ hΔ]
    linarith

/-- **FC18 (ii)** at an actual strong-edge centre `j`: the original composite `Q` of the centre's
two KL maps (normalized metric `d/ρ(j)`; FC17's clauses) is such that, whenever the chart
coordinate `η_j` is `Δ/100`-close to `Q`'s first coordinate on `B(j, 100Δ)` (LC87 packet (iv)),
the closed support of the actual edge cutoff lies in `B̄(j, 14Δρ(j)) ⊆ B(j, 20Δρ(j))`. -/
theorem fc18_edge_row (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΛ : 0 ≤ Λ) {j : X} (hj : j ∈ L.edge.centres) {τ : ℝ} (hΔ : 1 ≤ Δ) (hτ : 0 < τ)
    (hτsmall : τ < 1 / 10000) (hscale : Λ < 1 / (1000000 * Δ))
    (hend : Λ < s' / (100000000 * Δ ^ 2))
    (hb'domain : b' < 1 / (1000000 * Δ)) (hs'domain : s' < 1 / (1000000 * Δ))
    (hb'error : b' < τ * Δ / 1000000000) (hs'error : s' < τ * Δ / 1000000000)
    (hsb' : s < b' / 100000) (hss' : s < s' / 100000) (hbs : b < s / 100000)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hμ : μ ≤ 1 / 10) :
    ∃ Q : X → WithLp 2 (ℝ × ℝ), Q j = 0 ∧ (∀ x, 0 ≤ (Q x).snd) ∧
      (∀ x y, (ρ j)⁻¹ * dist x j < 200 * Δ → (ρ j)⁻¹ * dist y j < 200 * Δ →
        |dist (Q x) (Q y) - (ρ j)⁻¹ * dist x y| ≤ τ * Δ) ∧
      (∀ z ∈ closure {y : X | @isEdgePoint.{u, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y)))
          y Δ b' s'}, (ρ j)⁻¹ * dist z j < 120 * Δ → (Q z).snd < Δ / 10) ∧
      ((∀ x, (ρ j)⁻¹ * dist x j < 100 * Δ → |L.edge.coord j x - (Q x).fst| ≤ Δ / 100) →
        tsupport (L.edge.cutoff j) ⊆ closedBall j (14 * Δ * ρ j) ∧
          closedBall j (14 * Δ * ρ j) ⊆ ball j (20 * Δ * ρ j)) := by
  have hΔ0 : 0 < Δ := by linarith
  have hrj := hρ j
  obtain ⟨Y, mY, q, C, hC, hlen, ⟨F⟩, ⟨G⟩⟩ := L.edge.strong j hj
  have hscale' : ((Real.toNNReal Λ : NNReal) : ℝ) < 1 / (1000000 * Δ) := by
    rwa [Real.coe_toNNReal _ hΛ]
  have hend' : ((Real.toNNReal Λ : NNReal) : ℝ) < s' / (100000000 * Δ ^ 2) := by
    rwa [Real.coe_toNNReal _ hΛ]
  have hcb := @GC.MetricGeometry.coarse_border_of_physical_lipschitz_scale X Y mX mY j q C b s hC
    Δ τ b' s' (Real.toNNReal Λ) ρ L.lipschitz_scale hρ F G hΔ hτ hτsmall hscale' hend'
    hb'domain hs'domain hb'error hs'error hsb' hss' hbs hlen.le
  dsimp only at hcb
  obtain ⟨-, hpE, h0, hnn, hdist, -, hlow, -⟩ := hcb
  let Q : X → WithLp 2 (ℝ × ℝ) :=
    (letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); F.stripMap G)
  have hτΔ : τ * Δ < Δ / 10 := by nlinarith
  have hlow' : ∀ z ∈ closure {y : X | @isEdgePoint.{u, 0} X
      (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'},
      (ρ j)⁻¹ * dist z j < 120 * Δ → (Q z).snd < Δ / 10 := fun z hz hzj =>
    lt_of_le_of_lt (hlow z ⟨hz, (show (ρ j)⁻¹ * dist z j < 190 * Δ by linarith)⟩) hτΔ
  refine ⟨Q, h0, hnn, fun x y hx hy => hdist x hx y hy, hlow', fun hlink => ?_⟩
  have hpt : ∀ x, L.edge.cutoff j x ≠ 0 → dist x j ≤ 14 * Δ * ρ j := by
    intro x hx
    obtain ⟨-, hball, hcoord, hheight⟩ := L.edge.mem_of_cutoff_ne_zero hΔ0 hx
    have hrx := hρ x
    have hdxj : dist x j < 100 * Δ * ρ j := by
      rw [inv_mul_lt_iff₀ hrj] at hball
      linarith
    have hρx : ρ x ≤ 101 / 100 * ρ j := by
      have hlip := L.lipschitz_scale.dist_le_mul x j
      rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at hlip
      have h1 : Λ * dist x j ≤ Λ * (100 * Δ * ρ j) := mul_le_mul_of_nonneg_left hdxj.le hΛ
      have h2 : Λ * (100 * Δ * ρ j) ≤ 1 / 100 * ρ j := by nlinarith
      linarith [(abs_le.mp hlip).2]
    have hval := L.edge.smoothing_value j hj x
    have hFx : L.edge.smoothing x < 9 * Δ * ρ x := by
      rwa [div_lt_iff₀ hrx] at hheight
    have hinf : infDist x (closure {y : X | @isEdgePoint.{u, 0} X
        (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}) < 46 * Δ / 5 * ρ j := by
      have h9 : 9 * Δ * ρ x ≤ 9 * Δ * (101 / 100 * ρ j) :=
        mul_le_mul_of_nonneg_left hρx (by positivity)
      have hμ' : μ * (Δ * ρ j) ≤ 1 / 10 * (Δ * ρ j) :=
        mul_le_mul_of_nonneg_right hμ (by positivity)
      have := mul_pos hΔ0 hrj
      linarith [(abs_lt.mp hval).1]
    have hne : (closure {y : X | @isEdgePoint.{u, 0} X
        (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}).Nonempty := ⟨j, hpE⟩
    obtain ⟨z, hz, hxz⟩ := (infDist_lt_iff hne).mp hinf
    have hk := @fc18_edge_support_kernel X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))).toPseudoMetricSpace
      Q (L.edge.coord j) (closure {y : X | @isEdgePoint.{u, 0} X
        (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}) j Δ (τ * Δ) hΔ0
      (by nlinarith) h0 hnn hdist (fun z hz => hlow' z hz.1 hz.2) (fun x hx => hlink x hx) x
      hball hcoord ⟨z, hz, (show (ρ j)⁻¹ * dist x z < 46 * Δ / 5 by
        rw [inv_mul_lt_iff₀ hrj]; linarith)⟩
    have hk' : (ρ j)⁻¹ * dist x j < 14 * Δ := hk
    rw [inv_mul_lt_iff₀ hrj] at hk'
    linarith
  refine ⟨closure_minimal (fun x hx => mem_closedBall.mpr (hpt x hx)) isClosed_closedBall,
    closedBall_subset_ball ?_⟩
  have := mul_pos hΔ0 hrj
  nlinarith

/-- **FC12, edge half**, at an actual strong-edge centre under the same coordinate link: every
test ball `B(p, Rρ(p))` meeting the closed support of the actual edge cutoff has comparable scale,
lies in `B(j, (14Δ + 4R)ρ(j)) ⊆ B(j, 100Δρ(j))` (the chart ball), with complement-distance margin
`(86Δ − 4R)ρ(j)`. -/
theorem fc12_edge_row (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΛ : 0 ≤ Λ) {j : X} (hj : j ∈ L.edge.centres) {τ : ℝ} (hΔ : 1 ≤ Δ) (hτ : 0 < τ)
    (hτsmall : τ < 1 / 10000) (hscale : Λ < 1 / (1000000 * Δ))
    (hend : Λ < s' / (100000000 * Δ ^ 2))
    (hb'domain : b' < 1 / (1000000 * Δ)) (hs'domain : s' < 1 / (1000000 * Δ))
    (hb'error : b' < τ * Δ / 1000000000) (hs'error : s' < τ * Δ / 1000000000)
    (hsb' : s < b' / 100000) (hss' : s < s' / 100000) (hbs : b < s / 100000)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hμ : μ ≤ 1 / 10) :
    ∃ Q : X → WithLp 2 (ℝ × ℝ), Q j = 0 ∧
      ((∀ x, (ρ j)⁻¹ * dist x j < 100 * Δ → |L.edge.coord j x - (Q x).fst| ≤ Δ / 100) →
        ∀ {p : X} {R : ℝ}, 0 < R → Λ * max R (14 * Δ) ≤ 1 / 4 → 4 * R < 100 * Δ - 14 * Δ →
          (tsupport (L.edge.cutoff j) ∩ ball p (R * ρ p)).Nonempty →
          ρ j / ρ p ∈ Icc (1 / 2) 2 ∧ dist j p ≤ (R + 2 * (14 * Δ)) * ρ p ∧
            ball p (R * ρ p) ⊆ ball j ((14 * Δ + 4 * R) * ρ j) ∧
            ball j ((14 * Δ + 4 * R) * ρ j) ⊆ ball j (100 * Δ * ρ j) ∧
            ∀ x ∈ ball p (R * ρ p), (ball j (100 * Δ * ρ j))ᶜ.Nonempty →
              (100 * Δ - 14 * Δ - 4 * R) * ρ j ≤ infDist x (ball j (100 * Δ * ρ j))ᶜ) := by
  obtain ⟨Q, h0, -, -, -, hsupp⟩ := fc18_edge_row L hΛ hj hΔ hτ hτsmall hscale hend hb'domain
    hs'domain hb'error hs'error hsb' hss' hbs hΔΛ hμ
  refine ⟨Q, h0, fun hlink p R hR hbudget hgap hmeet => ?_⟩
  have hS := (hsupp hlink).1
  have hS' : tsupport (L.edge.cutoff j) ⊆ closedBall j ((14 * Δ) * ρ j) := by
    rw [show (14 * Δ) * ρ j = 14 * Δ * ρ j by ring]
    exact hS
  exact DifferentialGeometry.Geometry.Fibration.finite_packet_support_scale_buffer
    L.lipschitz_scale (hρ p) (hρ j) hR (by linarith) (by rwa [Real.coe_toNNReal _ hΛ]) hgap hS'
    (by rw [show 100 * Δ * ρ j = (100 * Δ) * ρ j by ring]) hmeet

end DifferentialGeometry.Geometry.Collapse
