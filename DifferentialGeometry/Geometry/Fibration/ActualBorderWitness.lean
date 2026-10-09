import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Fibration.ActualEdgeSupportLink

/-!
# FDC01's weak-border witness (WB) on the original edge chart

Blueprint `master207B.tex`, FDC01 (`lem:fibration-actual-replacement-edge-chart`, B:7201–7215):
"Let `u_i⁰` be the original raw tangential function in `R_i` units. LFR32's ACTUAL border coverage
supplies `q' ∈ E'` with `|Q_i(q') − (u_i⁰(q), 0)| < τΔ`, `d(q', p_i) < 4.1ΔR_i`,
`|η_i(q') − η_i(q)| < .01Δ` (WB). … The corresponding height bound and distortion also give
`d(q, q') < 4.2ΔR_i`." Together with "`q' ∈ E'`, so the SAME distance smoothing gives tiny `t(q')`"
(B:7226–7227). This part involves only the original chart, not the final map `E`.

On the actual edge chart at `i` of `L : LocalChartFamilyE` (recorded coarse-border composite
`Q_i = Qn`, LFR32's clauses `edge_coarse`, the ONE shared smoothing `F`, `t = F/ρ`), with the
original LFR28 bounds `μ, τ ≤ 10⁻⁸`, `100ΔΛ ≤ 10⁻⁸`:

* `dist_toLp_fst_FDC1`, `dist_toLp_zero_FDC1`: two plane distances.
* `LocalChartFamilyE.exists_edge_border_chart_FDC1`: LFR32's clauses of the chart in physical form,
  INCLUDING the border coverage by the closed weak edge set and the exact value link
  `|η_i − Q₁| < μΔ` (the existing `exists_edge_link` drops both).
* `fdc01_border_witness_FDC1`: for `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`, an ACTUAL weak
  edge point `q'` (own scale) with `d(q', i) < 4.1Δρ(i)`, `d(q, q') < 4.2Δρ(i)`,
  `|η_i(q') − η_i(q)| < Δ/100` and `t(q') < Δ/100`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- A plane point and its foot on the first axis are at distance `|x₂|`. -/
theorem dist_toLp_fst_FDC1 (x : WithLp 2 (ℝ × ℝ)) :
    dist x (WithLp.toLp 2 (x.fst, (0 : ℝ))) = |x.snd| := by
  rw [WithLp.prod_dist_eq_of_L2]
  simp [Real.sqrt_sq_eq_abs]

/-- A point of the first axis is at distance `|t|` from the origin. -/
theorem dist_toLp_zero_FDC1 (t : ℝ) :
    dist (WithLp.toLp 2 (t, (0 : ℝ))) (0 : WithLp 2 (ℝ × ℝ)) = |t| := by
  rw [WithLp.prod_dist_eq_of_L2]
  simp [Real.sqrt_sq_eq_abs]

section Family

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ : ℝ}

/-- **LFR32's clauses of an actual edge chart in physical form**: a plane map `Q` (the chart's
composite with its second coordinate truncated at `0`; equal to it on `B(j, 200Δρ(j))`) with
`Q(j) = 0`, `Q₂ ≥ 0`, distortion `≤ τΔ` against `ρ(j)⁻¹d` on `B(j, 200Δρ(j))`, the closed weak
edge set at height `≤ τΔ` on `B(j, 190Δρ(j))`, every `(t, 0)` with `|t| ≤ 100Δ` within `τΔ` of
the image of a point of that set in `B(j, 190Δρ(j))`, and `|η_j − Q₁| < μΔ` on `B(j, 100Δρ(j))`. -/
theorem LocalChartFamilyE.exists_edge_border_chart_FDC1
    (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ)
    (hΔ : 0 < Δ) {j : X} (hj : j ∈ L.edge.centres) :
    ∃ Q : X → WithLp 2 (ℝ × ℝ), Q j = 0 ∧ (∀ x, 0 ≤ (Q x).snd) ∧
      (∀ x y, (ρ j)⁻¹ * dist x j < 200 * Δ → (ρ j)⁻¹ * dist y j < 200 * Δ →
        |dist (Q x) (Q y) - (ρ j)⁻¹ * dist x y| ≤ τ * Δ) ∧
      (∀ z ∈ closure {y : X | @isEdgePoint.{u, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y)))
          y Δ b' s'}, (ρ j)⁻¹ * dist z j < 190 * Δ → (Q z).snd ≤ τ * Δ) ∧
      (∀ t : ℝ, |t| ≤ 100 * Δ → ∃ a ∈ closure {y : X | @isEdgePoint.{u, 0} X
          (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'},
        (ρ j)⁻¹ * dist a j < 190 * Δ ∧ dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) ∧
      (∀ x, (ρ j)⁻¹ * dist x j < 100 * Δ → |L.edge.coord j x - (Q x).fst| < μ * Δ) := by
  have hco := L.edge_coarse j hj
  have hcen := L.edge.chart_center j hj
  let C := L.edge.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
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
    unfold EdgeFamily.coord
    simp only [hj, ↓reduceDIte]
    exact hv

/-- **FDC01's weak-border witness (WB)**: for `q ∈ U_i = B(i, 100Δρ(i))` with `|η_i(q)| ≤ 4.01Δ`
and `t(q) ≤ 4.01Δ`, there is an ACTUAL weak edge point `q'` (own scale, qualities `b', s'`) with
`d(q', i) < 4.1Δρ(i)`, `d(q, q') < 4.2Δρ(i)`, `|η_i(q') − η_i(q)| < Δ/100` and `t(q') < Δ/100`
(`μ, τ ≤ 10⁻⁸`, `100ΔΛ ≤ 10⁻⁸`). -/
theorem fdc01_border_witness_FDC1
    (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ)
    (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) {i : X} (hi : i ∈ L.edge.centres) {q : X}
    (hq : q ∈ ball i (100 * Δ * ρ i)) (hηq : |L.edge.coord i q| ≤ 401 / 100 * Δ)
    (htq : L.edge.smoothing q / ρ q ≤ 401 / 100 * Δ) :
    ∃ q' : X, @isEdgePoint.{u, 0} X (mX.rescale (ρ q')⁻¹ (inv_pos.mpr (hρ q'))) q' Δ b' s' ∧
      dist q' i < 41 / 10 * Δ * ρ i ∧ dist q q' < 42 / 10 * Δ * ρ i ∧
      |L.edge.coord i q' - L.edge.coord i q| < Δ / 100 ∧
      L.edge.smoothing q' / ρ q' < Δ / 100 := by
  obtain ⟨Q, hQ0, hQnn, hQd, hQlow, hQcov, hQval⟩ := L.exists_edge_border_chart_FDC1 hΔ hi
  set A : Set X := closure
    {y : X | @isEdgePoint.{u, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'} with hA
  have hr := hρ i
  have hiA : i ∈ A := L.edge.centre_mem_closure_weak hi
  have hval := L.edge.smoothing_value i hi
  have hlip := L.lipschitz_scale
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
    have h1 := abs_sub_abs_le_abs_sub t (L.edge.coord i q)
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
  have hcoord : |L.edge.coord i q' - L.edge.coord i q| < Δ / 100 := by
    have h1 := hQval q' (by linarith)
    have h2 : |(Q q').fst - (Q a).fst| ≤ (ρ i)⁻¹ * dist q' a + τ * Δ := by
      have h := WithLp.dist_fst_le (Q q') (Q a)
      rw [Real.dist_eq] at h
      linarith [(abs_le.mp (hQd q' a (by linarith) (by linarith))).2]
    have h3 : |(Q a).fst - t| ≤ τ * Δ := by
      have h := WithLp.dist_fst_le (Q a) (WithLp.toLp 2 (t, (0 : ℝ)))
      rw [Real.dist_eq] at h
      exact h.trans hat
    have h4 := abs_sub_le (L.edge.coord i q') ((Q q').fst) ((Q a).fst)
    have h5 := abs_sub_le (L.edge.coord i q') ((Q a).fst) t
    have h6 := abs_sub_le (L.edge.coord i q') t (L.edge.coord i q)
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
    have h2 : L.edge.smoothing q ≤ 401 / 100 * Δ * ρ q := by
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
  have htq' : L.edge.smoothing q' / ρ q' < Δ / 100 := by
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

end Family

end DifferentialGeometry.Geometry.Collapse
