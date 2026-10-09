import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementCentreBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZEligibility
import DifferentialGeometry.Geometry.Fibration.ActualEdgeBuffer
import DifferentialGeometry.Geometry.Fibration.ActualBorderWitness

/-!
# BCF02, strict replacement, steps two and three: border witness, strong witness, eligibility

External draft 61 §6.2, steps two and three of (Repl_∂), dispositions D61-10 and D64-4; blueprint
`master207B.tex`, BCF02 (B:9781–9799) and FDC01 (B:7201–7230). Step two takes the weak-border
witness `q' ∈ E'` of LFR32's ACTUAL border coverage on the revised edge chart at `i`, with the SAME
`edgeB.smoothing` for the height (two smoothings of the same distance function need not agree), and
then the strong witness `p` of `weak_edge_density` (BD). Step three proves the replacement
eligibility `d(p, ∂W) > 70/3 > 20` from the boundary margin of the CURRENT consumer point:
`d(q, p) < 5ΔR_i`, `R_i < 2ρ(q)`, the tail request `10Δρ(q) < d(q, ∂W)/3` and `d(q, ∂W) ≥ 35`;
only AFTER that is `edgeB.covers_strong` applied. `weak_edge_eligible_BFZD` (D64-4) is the
family-level half; here the witness is BCF02's actual replacement witness (displacement from `q`,
not from `q'`).

Generic carrier (`LocalPacketsOnB` / `LocalPacketsOnBFRZ` over any complete `X`):
* `LocalPacketsOnB.exists_edgeB_border_chart_BCF2K`: LFR32's clauses of a revised edge chart in
  physical form, INCLUDING the border coverage by the closed weak edge set (the composite
  `edgeB_coarse`; `exists_edgeB_link_BAUGA` drops the coverage);
* `LocalPacketsOnB.edgeB_enclosure_BCF2K`: EDP03's enclosure on `edgeB` (`|η_i| ≤ aΔ`, `t ≤ aΔ` on
  `U_i` give `d(q, i) < 8Δρ_i`, and `< 6Δρ_i` for `a ≤ 4.2`);
* `LocalPacketsOnB.bcf02_border_witness_BCF2K` (WB): an actual weak edge `q'` with
  `d(q', i) < 4.1Δρ_i`, `d(q, q') < 4.2Δρ_i`, `|η_i(q') − η_i(q)| < Δ/100`, `t(q') < Δ/100`;
* `LocalPacketsOnBFRZ.bcf02_strong_candidate_BCF2K`: at a nonslim one-stratum revised centre `i`,
  (BD) gives a strong edge `a` with `d(q', a) < ρ(a)`, and slow variation gives `ρ(a) ≤ 1.01ρ_i`,
  `d(q, a) < 5Δρ_i`, `ρ_i < 2ρ(q)` (no membership of `q` in the open edge base is assumed).
Boundary carrier `(W°, d_ĝ)`, `D = d(·, ∂W)`:
* `bcf02_tail_request_BCF2K`: BCP04.a at `q` with `1140Δ ≤ 35n` gives `10Δρ(q) < D(q)/3` on
  `{D ≥ 35}`;
* `bcf02_eligibility_BCF2K`: `d(q, a) < 5Δρ_i`, `ρ_i < 2ρ(q)`, `10Δρ(q) < D(q)/3`, `D(q) ≥ 35` give
  `D(a) > (2/3)D(q)` and `D(a) > 70/3`;
* `LocalPacketsOnBFRZ.bcf02_strong_witness_BCF2K` (steps two–three on the final family over
  `{D > 10}, {D ≥ 20}, {D > 20}, {D ≥ 35}`): the weak witness `q'`, the strong witness `a` with
  `D(a) > 70/3`, and THEN a centre `j` of the SAME `edgeB` with `d(a, j) < Δρ_j`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry GC.Endpoint GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **LFR32's clauses of a revised edge chart in physical form** (the composite `edgeB_coarse`): a
plane map `Q` with `Q(j) = 0`, `Q₂ ≥ 0`, distortion `≤ τΔ` against `ρ(j)⁻¹d` on `B(j, 200Δρ(j))`,
the closed weak edge set at height `≤ τΔ` on `B(j, 190Δρ(j))`, every `(t, 0)` with `|t| ≤ 100Δ`
within `τΔ` of the image of a point of that set in `B(j, 190Δρ(j))`, and `|η_j − Q₁| < μΔ` on
`B(j, 100Δρ(j))`. -/
theorem LocalPacketsOnB.exists_edgeB_border_chart_BCF2K
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂)
    (hΔ : 0 < Δ) {j : X} (hj : j ∈ F.edgeB.centres) :
    ∃ Q : X → WithLp 2 (ℝ × ℝ), Q j = 0 ∧ (∀ x, 0 ≤ (Q x).snd) ∧
      (∀ x y, (ρ j)⁻¹ * dist x j < 200 * Δ → (ρ j)⁻¹ * dist y j < 200 * Δ →
        |dist (Q x) (Q y) - (ρ j)⁻¹ * dist x y| ≤ τ * Δ) ∧
      (∀ z ∈ closure {y : X | @isEdgePoint.{0, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y)))
          y Δ b' s'}, (ρ j)⁻¹ * dist z j < 190 * Δ → (Q z).snd ≤ τ * Δ) ∧
      (∀ t : ℝ, |t| ≤ 100 * Δ → ∃ a ∈ closure {y : X | @isEdgePoint.{0, 0} X
          (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'},
        (ρ j)⁻¹ * dist a j < 190 * Δ ∧ dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) ∧
      (∀ x, (ρ j)⁻¹ * dist x j < 100 * Δ → |F.edgeB.coord_BAUGA j x - (Q x).fst| < μ * Δ) := by
  have hco := F.edgeB_coarse j hj
  have hcen := F.edgeB.chart_center j hj
  have hcoordeq := F.edgeB.coord_BAUGA_of_mem hj
  let C := F.edgeB.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hcen' : C.center = j := hcen
  obtain ⟨h0, hdist, hnn, -, hlow, hcov⟩ := hco
  let Qn : X → WithLp 2 (ℝ × ℝ) := C.Qn
  let Q : X → WithLp 2 (ℝ × ℝ) := fun x => WithLp.toLp 2 ((Qn x).fst, max 0 (Qn x).snd)
  have hQ : ∀ x, (ρ j)⁻¹ * @dist X mX.toDist x j < 200 * Δ → Q x = Qn x := by
    intro x hx
    have h := hnn x hx
    change WithLp.toLp 2 ((Qn x).fst, max 0 (Qn x).snd) = Qn x
    rw [max_eq_right h]
    rfl
  refine ⟨Q, ?_, fun x => le_max_left _ _, ?_, ?_, ?_, ?_⟩
  · rw [hQ j (by rw [@dist_self X mX.toPseudoMetricSpace j, mul_zero]; positivity)]
    exact h0
  · intro x y hx hy
    rw [hQ x hx, hQ y hy]
    exact hdist x hx y hy
  · intro z hz hzj
    rw [hQ z (by linarith)]
    exact hlow z ⟨hz, hzj⟩
  · intro t ht
    obtain ⟨a, ⟨haA, haB⟩, hd⟩ := hcov t ht
    have haB' : (ρ j)⁻¹ * @dist X mX.toDist a j < 190 * Δ := haB
    refine ⟨a, haA, haB', ?_⟩
    rw [hQ a (by linarith)]
    exact hd
  · intro x hx
    rw [hQ x (by linarith)]
    have hx' : x ∈ ball C.center (100 * Δ) := by rw [hcen']; exact hx
    have hv := C.value x hx'
    rw [← C.Qn_fst x] at hv
    rw [hcoordeq]
    unfold EdgeFamilyOn.coord_BCG1
    exact hv

/-- **EDP03's enclosure on a revised edge chart**: on `U_j = B(j, 100Δρ(j))`, `|η_j| ≤ aΔ` and
`t ≤ aΔ` (`a ≤ 5`) give `d(x, j) < 8Δρ(j)`, and `< 6Δρ(j)` when `a ≤ 4.2`. -/
theorem LocalPacketsOnB.edgeB_enclosure_BCF2K
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂)
    (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8)
    {j : X} (hj : j ∈ F.edgeB.centres) {x : X} {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 5)
    (hx : x ∈ ball j (100 * Δ * ρ j)) (hfx : |F.edgeB.coord_BAUGA j x| ≤ a * Δ)
    (htx : F.edgeB.smoothing x / ρ x ≤ a * Δ) :
    dist x j < 8 * Δ * ρ j ∧ (a ≤ 21 / 5 → dist x j < 6 * Δ * ρ j) := by
  have hco := F.edgeB_coarse j hj
  have hcen := F.edgeB.chart_center j hj
  have hval := F.edgeB.smoothing_value j hj
  have hlip := F.lipschitz_scale
  have hrj := hρ j
  have hrx := hρ x
  have hd : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hrj hx
  set A : Set X := closure
    {y | @isEdgePoint.{0, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'} with hA
  set lam : ℝ := 100 * Δ * (Real.toNNReal Λ : ℝ) with hlamdef
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : lam ≤ 1 / 10 ^ 8 := by
    rcases le_total 0 Λ with h | h
    · rw [hlamdef, Real.coe_toNNReal _ h]
      exact hlam
    · rw [hlamdef, Real.toNNReal_of_nonpos h]
      norm_num
  -- the scale on `U_j`, normalized at `j`
  have hρx : ρ x / ρ j ≤ 1 + lam := by
    have h1 := hlip.dist_le_mul x j
    rw [Real.dist_eq] at h1
    have h2 : ((Real.toNNReal Λ : ℝ)) * dist x j ≤ (Real.toNNReal Λ : ℝ) * (100 * Δ * ρ j) := by
      have hxj : dist x j < 100 * Δ * ρ j := hx
      exact mul_le_mul_of_nonneg_left hxj.le (NNReal.coe_nonneg _)
    rw [div_le_iff₀ hrj]
    have he : (1 + lam) * ρ j = ρ j + (Real.toNNReal Λ : ℝ) * (100 * Δ * ρ j) := by
      rw [hlamdef]
      ring
    rw [he]
    linarith [(abs_le.mp (h1.trans h2)).2]
  have hcoord : |F.edgeB.coord_BAUGA j x| ≤ a * Δ := hfx
  rw [F.edgeB.coord_BAUGA_of_mem hj] at hcoord
  unfold EdgeFamilyOn.coord_BCG1 at hcoord
  have hFn : |F.edgeB.smoothing x / ρ j -
      @infDist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)).toPseudoMetricSpace x A| ≤ μ * Δ := by
    rw [infDist_rescale, div_eq_inv_mul, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hrj)]
    have h := hval x
    rw [← div_eq_inv_mul, div_le_iff₀ hrj]
    linarith
  have htn : F.edgeB.smoothing x / ρ j / (ρ x / ρ j) ≤ a * Δ := by
    have hq : F.edgeB.smoothing x / ρ j / (ρ x / ρ j) = F.edgeB.smoothing x / ρ x := by
      field_simp
    rw [hq]
    exact htx
  let C := F.edgeB.chart j hj
  let Fs := F.edgeB.smoothing
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hcen' : C.center = j := hcen
  obtain ⟨hQp, hdist, hheight, -, hborder, -⟩ := hco
  have hxR : x ∈ ball j (100 * Δ) := hd
  have hxC : x ∈ ball C.center (100 * Δ) := by rw [hcen']; exact hxR
  have hf : |C.coord x - (C.Qn x).fst| ≤ μ * Δ := by
    have hv := C.value x hxC
    rw [← C.Qn_fst x] at hv
    exact hv.le
  have hpA : j ∈ A := by
    have h := C.center_mem
    rw [hcen'] at h
    exact h
  have henc := coarseBorder_slab_dist_le_KC (Y := X) (Q := C.Qn) (p := j) (A := A)
    (f := C.coord) (F := fun y => Fs y / ρ j) (ρ := fun y => ρ y / ρ j) hΔ ha0 ha
    hμ hlam1 hQp hdist hheight hpA hborder hxR hf hFn (div_pos hrx hrj) hρx hcoord htn
  have hdn : (ρ j)⁻¹ * @dist X mX.toDist x j ≤
      Δ * (Real.sqrt ((a + μ) ^ 2 + (a * (1 + lam) + μ + 2 * τ) ^ 2) + τ) := henc
  have hμ0 : 0 ≤ μ := by
    by_contra h
    push Not at h
    nlinarith [abs_nonneg (C.coord x - (C.Qn x).fst)]
  have hτ0 : 0 ≤ τ := by
    have hjj : j ∈ ball j (200 * Δ) := mem_ball_self (by positivity)
    have h := hdist j hjj j hjj
    rw [dist_self, dist_self, sub_self, abs_zero] at h
    by_contra h'
    push Not at h'
    nlinarith
  obtain ⟨h8, h6⟩ := EdgeDisk.edgeDist_enclosure_lt ha0 hlam0 (by norm_num at hlam1 ⊢; exact hlam1)
    hμ0 (by norm_num at hμ ⊢; exact hμ) hτ0 (by norm_num at hτ ⊢; exact hτ)
  rw [inv_mul_le_iff₀ hrj] at hdn
  refine ⟨?_, fun ha' => ?_⟩
  · have := mul_lt_mul_of_pos_left (h8 ha) hΔ
    change @dist X mX.toDist x j < 8 * Δ * ρ j
    nlinarith
  · have := mul_lt_mul_of_pos_left (h6 ha') hΔ
    change @dist X mX.toDist x j < 6 * Δ * ρ j
    nlinarith

/-- **(Repl_∂), step two: the weak-border witness (WB) on the revised edge chart** (the SAME
`edgeB.smoothing`): for `q ∈ U_i = B(i, 100Δρ(i))` with `|η_i(q)| ≤ 4.01Δ` and `t(q) ≤ 4.01Δ`,
there is an ACTUAL weak edge point `q'` (own scale, qualities `b', s'`) with `d(q', i) < 4.1Δρ(i)`,
`d(q, q') < 4.2Δρ(i)`, `|η_i(q') − η_i(q)| < Δ/100` and `t(q') < Δ/100` (`μ, τ ≤ 10⁻⁸`,
`100ΔΛ ≤ 10⁻⁸`). -/
theorem LocalPacketsOnB.bcf02_border_witness_BCF2K
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂)
    (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) {i : X} (hi : i ∈ F.edgeB.centres) {q : X}
    (hq : q ∈ ball i (100 * Δ * ρ i)) (hηq : |F.edgeB.coord_BAUGA i q| ≤ 401 / 100 * Δ)
    (htq : F.edgeB.smoothing q / ρ q ≤ 401 / 100 * Δ) :
    ∃ q' : X, @isEdgePoint.{0, 0} X (mX.rescale (ρ q')⁻¹ (inv_pos.mpr (hρ q'))) q' Δ b' s' ∧
      dist q' i < 41 / 10 * Δ * ρ i ∧ dist q q' < 42 / 10 * Δ * ρ i ∧
      |F.edgeB.coord_BAUGA i q' - F.edgeB.coord_BAUGA i q| < Δ / 100 ∧
      F.edgeB.smoothing q' / ρ q' < Δ / 100 := by
  obtain ⟨Q, hQ0, hQnn, hQd, hQlow, hQcov, hQval⟩ := F.exists_edgeB_border_chart_BCF2K hΔ hi
  set A : Set X := closure
    {y : X | @isEdgePoint.{0, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'} with hA
  have hr := hρ i
  have hiA : i ∈ A := F.edgeB.mem_closure_weakEdge_BDRY5 hi
  have hval := F.edgeB.smoothing_value i hi
  have hlip := F.lipschitz_scale
  have hΔΛ : Δ * Λ ≤ 1 / 10 ^ 10 := by nlinarith
  have hD : 0 < Δ * ρ i := mul_pos hΔ hr
  have hμΔ : μ * Δ ≤ Δ / 10 ^ 8 := by nlinarith
  have hτΔ : τ * Δ ≤ Δ / 10 ^ 8 := by nlinarith
  -- normalized distances
  have hqd : (ρ i)⁻¹ * dist q i < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hr hq
  have hii : (ρ i)⁻¹ * dist i i < 200 * Δ := by rw [dist_self, mul_zero]; positivity
  have hτ0 : 0 ≤ τ * Δ := by
    have h := hQd i i hii hii
    rw [dist_self, dist_self, mul_zero, sub_zero, abs_zero] at h
    exact h
  -- the first coordinate `t = Q₁(q) = u_i⁰(q)`
  set t := (Q q).fst with htdef
  have hqv := hQval q hqd
  have htb : |t| < 401 / 100 * Δ + μ * Δ := by
    have h1 := abs_sub_abs_le_abs_sub t (F.edgeB.coord_BAUGA i q)
    rw [abs_sub_comm] at h1
    linarith
  obtain ⟨a, haA, haB, hat⟩ := hQcov t (by linarith)
  -- the witness `a` is close to the centre
  have hai : (ρ i)⁻¹ * dist a i ≤ |t| + 2 * (τ * Δ) := by
    have h1 := (abs_le.mp (hQd a i (by linarith) hii)).1
    rw [hQ0] at h1
    have h2 := dist_triangle (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) 0
    rw [dist_toLp_zero_FDC1] at h2
    linarith
  -- an actual weak edge point `q'` near `a`
  obtain ⟨q', hq'E, hq'a⟩ := Metric.mem_closure_iff.mp haA (Δ * ρ i / 1000) (by positivity)
  have hq'a' : (ρ i)⁻¹ * dist q' a < Δ / 1000 := by
    rw [dist_comm, inv_mul_lt_iff₀ hr]
    linarith
  have hq'i : (ρ i)⁻¹ * dist q' i < 41 / 10 * Δ := by
    have h1 := dist_triangle q' a i
    have h2 : (ρ i)⁻¹ * dist q' i ≤ (ρ i)⁻¹ * dist q' a + (ρ i)⁻¹ * dist a i := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hr).le
    linarith
  have hq'i' : dist q' i < 41 / 10 * Δ * ρ i := by
    rw [inv_mul_lt_iff₀ hr] at hq'i
    linarith
  -- the tangential coordinate at `q'`
  have hcoord : |F.edgeB.coord_BAUGA i q' - F.edgeB.coord_BAUGA i q| < Δ / 100 := by
    have h1 := hQval q' (by linarith)
    have h2 : |(Q q').fst - (Q a).fst| ≤ (ρ i)⁻¹ * dist q' a + τ * Δ := by
      have h := WithLp.dist_fst_le (Q q') (Q a)
      rw [Real.dist_eq] at h
      linarith [(abs_le.mp (hQd q' a (by linarith) (by linarith))).2]
    have h3 : |(Q a).fst - t| ≤ τ * Δ := by
      have h := WithLp.dist_fst_le (Q a) (WithLp.toLp 2 (t, (0 : ℝ)))
      rw [Real.dist_eq] at h
      exact h.trans hat
    have h4 := abs_sub_le (F.edgeB.coord_BAUGA i q') ((Q q').fst) ((Q a).fst)
    have h5 := abs_sub_le (F.edgeB.coord_BAUGA i q') ((Q a).fst) t
    have h6 := abs_sub_le (F.edgeB.coord_BAUGA i q') t (F.edgeB.coord_BAUGA i q)
    rw [abs_sub_comm t] at h6
    linarith
  -- the height of `q` bounds `Q₂(q)`
  have hρq : ρ q ≤ ρ i * (1 + 1 / 10 ^ 8) := by
    have h1 := hlip.dist_le_mul q i
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1
    have h2 : Λ * dist q i ≤ Λ * (100 * Δ * ρ i) := mul_le_mul_of_nonneg_left (le_of_lt hq) hΛ
    have h3 : Λ * (100 * Δ * ρ i) ≤ ρ i / 10 ^ 8 := by nlinarith
    linarith [(abs_le.mp h1).2]
  have hinf : (ρ i)⁻¹ * infDist q A < 4011 / 1000 * Δ := by
    have h1 := (abs_lt.mp (hval q)).1
    have h2 : F.edgeB.smoothing q ≤ 401 / 100 * Δ * ρ q := by
      rwa [div_le_iff₀ (hρ q)] at htq
    have h3 : 401 / 100 * Δ * ρ q ≤ 401 / 100 * Δ * (ρ i * (1 + 1 / 10 ^ 8)) :=
      mul_le_mul_of_nonneg_left hρq (by positivity)
    rw [inv_mul_lt_iff₀ hr]
    nlinarith
  have hsnd : (Q q).snd ≤ 4011 / 1000 * Δ + 2 * (τ * Δ) := by
    by_contra hlt
    push Not at hlt
    have hlt' : infDist q A < ρ i * (4011 / 1000 * Δ) := by
      rw [inv_mul_lt_iff₀ hr] at hinf
      linarith
    obtain ⟨z, hzA, hz⟩ := (infDist_lt_iff ⟨i, hiA⟩).mp hlt'
    have hzq : (ρ i)⁻¹ * dist q z < 4011 / 1000 * Δ := by
      rw [inv_mul_lt_iff₀ hr]
      linarith
    have hzi : (ρ i)⁻¹ * dist z i < 190 * Δ := by
      have h1 := dist_triangle z q i
      rw [dist_comm z q] at h1
      have h2 : (ρ i)⁻¹ * dist z i ≤ (ρ i)⁻¹ * dist q z + (ρ i)⁻¹ * dist q i := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hr).le
      linarith
    have h1 := (abs_le.mp (hQd q z (by linarith) (by linarith))).2
    have h2 : (Q q).snd - (Q z).snd ≤ dist (Q q) (Q z) := by
      have h := WithLp.dist_snd_le (Q q) (Q z)
      rw [Real.dist_eq] at h
      linarith [le_abs_self ((Q q).snd - (Q z).snd)]
    linarith [hQlow z hzA hzi]
  -- the distance from `q` to `q'`
  have hqq' : dist q q' < 42 / 10 * Δ * ρ i := by
    have h1 := (abs_le.mp (hQd q q' (by linarith) (by linarith))).1
    have h2 := dist_triangle (Q q) (WithLp.toLp 2 (t, (0 : ℝ))) (Q q')
    have h3 := dist_triangle (WithLp.toLp 2 (t, (0 : ℝ))) (Q a) (Q q')
    have h4 : dist (Q q) (WithLp.toLp 2 (t, (0 : ℝ))) = (Q q).snd := by
      rw [htdef, dist_toLp_fst_FDC1, abs_of_nonneg (hQnn q)]
    have h5 := (abs_le.mp (hQd a q' (by linarith) (by linarith))).2
    rw [dist_comm a q'] at h5
    rw [dist_comm] at hat
    have h6 : (ρ i)⁻¹ * dist q q' < 42 / 10 * Δ := by linarith
    rw [inv_mul_lt_iff₀ hr] at h6
    linarith
  -- the height of `q'`
  have htq' : F.edgeB.smoothing q' / ρ q' < Δ / 100 := by
    have hq'A : q' ∈ A := subset_closure hq'E
    have h1 := (abs_lt.mp (hval q')).2
    rw [infDist_zero_of_mem hq'A] at h1
    have hρq' : ρ i * (1 - 1 / 10 ^ 8) ≤ ρ q' := by
      have h2 := hlip.dist_le_mul q' i
      rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h2
      have h3 : Λ * dist q' i ≤ Λ * (41 / 10 * Δ * ρ i) :=
        mul_le_mul_of_nonneg_left hq'i'.le hΛ
      have h4 : Λ * (41 / 10 * Δ * ρ i) ≤ ρ i / 10 ^ 8 := by nlinarith
      linarith [(abs_le.mp h2).1]
    rw [div_lt_iff₀ (hρ q')]
    have h5 : μ * (Δ * ρ i) ≤ 1 / 10 ^ 8 * (Δ * ρ i) := mul_le_mul_of_nonneg_right hμ hD.le
    have h6 : Δ / 100 * (ρ i * (1 - 1 / 10 ^ 8)) ≤ Δ / 100 * ρ q' :=
      mul_le_mul_of_nonneg_left hρq' (by positivity)
    linarith
  exact ⟨q', hq'E, hq'i', hqq', hcoord, htq'⟩

/-- **(Repl_∂), step two, the strong witness before eligibility.** At a revised edge centre `i` that
is a nonslim one-stratum point, for `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`: the weak
witness `q'` of (WB) and the strong edge `a` of (BD) at `(i, q')` (own scale, qualities `b, s`),
with `d(q', a) < ρ(a)`, `ρ(a) ≤ 1.01ρ_i`, `d(q, a) < 5Δρ_i` and `ρ_i < 2ρ(q)` (slow variation;
`Δ ≥ 2`, `μ, τ ≤ 10⁻⁸`, `100ΔΛ ≤ 10⁻⁸`). Nothing about `a`'s region is claimed. -/
theorem LocalPacketsOnBFRZ.bcf02_strong_candidate_BCF2K
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8)
    (hτ : τ ≤ 1 / 10 ^ 8) (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) {i : X} (hi : i ∈ F.edgeB.centres)
    (h1 : i ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1)
    (hns : ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))))
    {q : X} (hq : q ∈ ball i (100 * Δ * ρ i))
    (hηq : |F.edgeB.coord_BAUGA i q| ≤ 401 / 100 * Δ)
    (htq : F.edgeB.smoothing q / ρ q ≤ 401 / 100 * Δ) :
    ∃ q' a : X, @isEdgePoint.{0, 0} X (mX.rescale (ρ q')⁻¹ (inv_pos.mpr (hρ q'))) q' Δ b' s' ∧
      dist q' i < 41 / 10 * Δ * ρ i ∧ dist q q' < 42 / 10 * Δ * ρ i ∧
      |F.edgeB.coord_BAUGA i q' - F.edgeB.coord_BAUGA i q| < Δ / 100 ∧
      F.edgeB.smoothing q' / ρ q' < Δ / 100 ∧
      @isEdgePoint.{0, 0} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))) a Δ b s ∧
      dist q' a < ρ a ∧ ρ a ≤ 101 / 100 * ρ i ∧ dist q a < 5 * Δ * ρ i ∧ ρ i < 2 * ρ q := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  obtain ⟨q', hq'E, hq'i, hqq', hcoord, htq'⟩ :=
    F.toLocalPacketsOnB.bcf02_border_witness_BCF2K hΔ0 hΛ hμ hτ hlam hi hq hηq htq
  have hiU : i ∈ U₁ := F.edgeB_domain i hi (mem_ball_self (by positivity))
  have hq'i10 : dist q' i < 10 * Δ * ρ i := by nlinarith
  obtain ⟨a, haE, hq'a⟩ := F.weak_edge_density i hiU h1 hns q' hq'E hq'i10
  have hra := hρ a
  have hΛ1 : Λ ≤ 1 / 10 ^ 10 := by nlinarith
  have hΔΛ : Δ * Λ ≤ 1 / 10 ^ 10 := by nlinarith
  have hlip := F.lipschitz_scale
  -- `ρ(a) ≤ 1.01ρ_i`
  have hai : dist a i < ρ a + 41 / 10 * Δ * ρ i := by
    have h := dist_triangle a q' i
    rw [dist_comm a q'] at h
    linarith
  have hρa : ρ a ≤ 101 / 100 * ρ i := by
    have h1 := hlip.dist_le_mul a i
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1
    have h2 : Λ * dist a i ≤ Λ * (ρ a + 41 / 10 * Δ * ρ i) := mul_le_mul_of_nonneg_left hai.le hΛ
    have h3 : Λ * ρ a ≤ 1 / 10 ^ 10 * ρ a := mul_le_mul_of_nonneg_right hΛ1 hra.le
    have h4 : Δ * Λ * ρ i ≤ 1 / 10 ^ 10 * ρ i := mul_le_mul_of_nonneg_right hΔΛ hri.le
    have h5 : Λ * (ρ a + 41 / 10 * Δ * ρ i) = Λ * ρ a + 41 / 10 * (Δ * Λ * ρ i) := by ring
    linarith [(abs_le.mp h1).2]
  -- `d(q, a) < (4.2Δ + 1.01)ρ_i < 5Δρ_i`
  have hqa : dist q a < 5 * Δ * ρ i := by
    have h := dist_triangle q q' a
    have h2 : 101 / 100 * ρ i < 8 / 10 * Δ * ρ i := by nlinarith
    linarith
  -- `ρ_i < 2ρ(q)`
  have hρq : ρ i < 2 * ρ q := by
    have h1 := hlip.dist_le_mul q i
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1
    have hqi : dist q i < 100 * Δ * ρ i := hq
    have h2 : Λ * dist q i ≤ Λ * (100 * Δ * ρ i) := mul_le_mul_of_nonneg_left hqi.le hΛ
    have h4 : Δ * Λ * ρ i ≤ 1 / 10 ^ 10 * ρ i := mul_le_mul_of_nonneg_right hΔΛ hri.le
    have h5 : Λ * (100 * Δ * ρ i) = 100 * (Δ * Λ * ρ i) := by ring
    have := hρ q
    linarith [(abs_le.mp h1).1]
  exact ⟨q', a, hq'E, hq'i, hqq', hcoord, htq', haE, hq'a, hρa, hqa, hρq⟩

end Generic

/-! ## The boundary carrier `(W°, d_ĝ)`: tail request, eligibility, the strong witness -/

section Carrier

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **The tail request of BCF02** (BCP04.a supplies the fixed-buffer bound): at a point with
`D ≥ 35`, BCP04.a `nD/(D + 3) < D/ρ` with `1140Δ ≤ 35n` gives `10Δρ < D/3`. -/
theorem bcf02_tail_request_BCF2K {D ρq n Δ : ℝ} (hn : 1140 * Δ ≤ 35 * n) (hρq : 0 < ρq)
    (hD : 35 ≤ D) (hbcp : n * D / (D + 3) < D / ρq) : 10 * Δ * ρq < D / 3 := by
  have hD0 : 0 < D := by linarith
  have hnρ : n * ρq < D + 3 := by
    rw [div_lt_div_iff₀ (by linarith) hρq] at hbcp
    nlinarith
  have h1 : 1140 * Δ * ρq ≤ 35 * n * ρq := mul_le_mul_of_nonneg_right hn hρq.le
  linarith

/-- **BCF02's replacement eligibility** (step three): for points `q, a` of `W°` with
`d_ĝ(q, a) < 5Δρ_i`, `ρ_i < 2ρ(q)`, the tail request `10Δρ(q) < D(q)/3` and `D(q) ≥ 35`, the
distance of `a` to `∂W` exceeds `(2/3)D(q)`, hence `70/3 > 20` (`g° ≤ ĝ`, so `d_g ≤ d_ĝ`). -/
theorem bcf02_eligibility_BCF2K (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (q a : W.pieceInterior ⊤) {ρq ρi Δ : ℝ} (hΔ : 0 < Δ) :
    letI := inducedMetricSpace ĝ
    dist q a < 5 * Δ * ρi → ρi < 2 * ρq →
      10 * Δ * ρq < (distanceToBoundary W g q).toReal / 3 →
      ENNReal.ofReal 35 ≤ distanceToBoundary W g q →
      ENNReal.ofReal (2 / 3 * (distanceToBoundary W g q).toReal) < distanceToBoundary W g a ∧
        ENNReal.ofReal (70 / 3) < distanceToBoundary W g a := by
  let _ : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  intro hqa hρ hreq h35
  have : Nonempty (W.pieceInterior ⊤) := ⟨q⟩
  have hdist : riemannianEDistOf g a.val q.val ≤ ENNReal.ofReal (dist a q) := by
    rw [← inducedMetricSpace_hmetric ĝ a q]
    exact riemannianEDistOf_val_le_completion_BDRY1 W g ĝ hle a q
  have htri := distanceToBoundary_le_add W g q.val a.val
  rw [riemannianEDistOf_comm] at htri
  have h2 : distanceToBoundary W g q ≤ distanceToBoundary W g a + ENNReal.ofReal (dist a q) :=
    htri.trans (add_le_add_right hdist _)
  by_cases hat : distanceToBoundary W g a = ⊤
  · rw [hat]
    exact ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  have hsum : distanceToBoundary W g a + ENNReal.ofReal (dist a q) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hat, ENNReal.ofReal_ne_top⟩
  have hqt : distanceToBoundary W g q ≠ ⊤ := ne_top_of_le_ne_top hsum h2
  have h2r : (distanceToBoundary W g q).toReal ≤ (distanceToBoundary W g a).toReal + dist a q := by
    have h := ENNReal.toReal_mono hsum h2
    rwa [ENNReal.toReal_add hat ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal dist_nonneg] at h
  have h35r : 35 ≤ (distanceToBoundary W g q).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hqt).mp h35
  have hda : dist a q < 10 * Δ * ρq := by
    rw [dist_comm]
    nlinarith
  have hlt : 2 / 3 * (distanceToBoundary W g q).toReal < (distanceToBoundary W g a).toReal := by
    linarith
  rw [← ENNReal.ofReal_toReal hat]
  refine ⟨(ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hlt,
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr (by linarith)⟩

/-- **(Repl_∂), steps two and three, on the final boundary family** over the completion
`(W°, d_ĝ)` (regions `{D > 10}`, `{D ≥ 20}`, `{D > 20}`, `{D ≥ 35}`), with BCP04.a at the index `n`
(`1140Δ ≤ 35n`): at a revised edge centre `i` that is a nonslim one-stratum point, for `q ∈ U_i`
with `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ` and `D(q) ≥ 35`, there are the weak witness `q'` of (WB),
the strong witness `a` of (BD) with `d(q', a) < ρ(a)` and the eligibility `D(a) > 70/3`, and THEN,
by `edgeB.covers_strong` of the SAME revised edge family, a centre `j` with `d(a, j) < Δρ(j)`. -/
theorem LocalPacketsOnBFRZ.bcf02_strong_witness_BCF2K (W : CompactCarrier.{0})
    [ConnectedSpace W.Carrier] (g : SmoothRiemannianMetric W.model W.Carrier)
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ}
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (hn : 1140 * Δ ≤ 35 * n)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3) :
    letI := inducedMetricSpace ĝ
    ∀ [CompleteSpace (W.pieceInterior ⊤)]
      (F : LocalPacketsOnBFRZ (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
        (fun x => ρ x) (fun x => hρ x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} oM)
      (i : W.pieceInterior ⊤), i ∈ F.edgeB.centres →
      i ∈ scaledSplittingStratum.{0, 0} (fun x : W.pieceInterior ⊤ => ρ x) (fun x => hρ x) β 1 →
      ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
        Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
        Nonempty (@KleinerLottApprox (W.pieceInterior ⊤) (WithLp 2 (ℝ × Z))
          ((inducedMetricSpace ĝ).rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i
          (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) →
      ∀ q : W.pieceInterior ⊤, dist q i < 100 * Δ * ρ i →
        |F.edgeB.coord_BAUGA i q| ≤ 401 / 100 * Δ →
        F.edgeB.smoothing q / ρ q ≤ 401 / 100 * Δ →
        ENNReal.ofReal 35 ≤ distanceToBoundary W g q →
        ∃ q' a : W.pieceInterior ⊤, @isEdgePoint.{0, 0} (W.pieceInterior ⊤)
            ((inducedMetricSpace ĝ).rescale (ρ q')⁻¹ (inv_pos.mpr (hρ q'))) q' Δ b' s' ∧
          dist q' i < 41 / 10 * Δ * ρ i ∧ dist q q' < 42 / 10 * Δ * ρ i ∧
          |F.edgeB.coord_BAUGA i q' - F.edgeB.coord_BAUGA i q| < Δ / 100 ∧
          F.edgeB.smoothing q' / ρ q' < Δ / 100 ∧
          @isEdgePoint.{0, 0} (W.pieceInterior ⊤)
            ((inducedMetricSpace ĝ).rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))) a Δ b s ∧
          dist q' a < ρ a ∧ ENNReal.ofReal (70 / 3) < distanceToBoundary W g a ∧
          ∃ j ∈ F.edgeB.centres, dist a j < Δ * ρ j := by
  let _ : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  intro _ F i hi h1 hns q hq hηq htq hq35
  obtain ⟨q', a, hq'E, hq'i, hqq', hcoord, htq', haE, hq'a, -, hqa, hρq⟩ :=
    F.bcf02_strong_candidate_BCF2K hΔ hΛ hμ hτ hlam hi h1 hns (mem_ball.mpr hq) hηq htq
  have hΔ0 : 0 < Δ := by linarith
  have hD0 : 0 < distanceToBoundary W g q :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num)) hq35
  have hb := hbcp q.val hD0
  have hqt : distanceToBoundary W g q ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hb
    simp at hb
  have h35r : 35 ≤ (distanceToBoundary W g q).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hqt).mp hq35
  have hreq := bcf02_tail_request_BCF2K hn (hρ q) h35r hb
  obtain ⟨-, h703⟩ := bcf02_eligibility_BCF2K W g ĝ hle q a hΔ0 hqa hρq hreq hq35
  have haU : a ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 20 < distanceToBoundary W g x} := by
    refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by norm_num)) h703
  obtain ⟨j, hj, haj⟩ := F.edgeB.covers_strong a haU haE
  exact ⟨q', a, hq'E, hq'i, hqq', hcoord, htq', haE, hq'a, h703, j, hj, haj⟩

end Carrier

end DifferentialGeometry.Geometry.Collapse
