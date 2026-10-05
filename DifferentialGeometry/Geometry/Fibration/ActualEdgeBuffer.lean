import DifferentialGeometry.Geometry.Fibration.ActualGlobalBlockMap
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.StrongEdgeDiskCover
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.HeightQuotient
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimCoordinateClauses
import DifferentialGeometry.Geometry.Collapse.EdgeRowSequence

/-!
# EDP03: the smooth original buffer of an actual edge chart (the clauses free of the final map)

Blueprint `master207B.tex`, EDP03 (`lem:fibration-edge-original-buffer-and-height`, B:6837–6866),
for `i ∈ I_e` with `U_i = B(p_i, 100ΔR_i)` and
`Y_i = {p ∈ U_i : |η_i(p)| < 5Δ, t(p) < 5Δ}`, `H₀ = Δψ(t/Δ)` (LFR27's profile `ψ`):
"`η_i, H₀, g_i, T` are smooth on `Y_i`. There is a compact subset `Q_i ⋐ Y_i` containing
`{p ∈ U_i : |η_i| ≤ 4.1Δ, t ≤ 4.1Δ}` (EBuf) in its interior. All of `Y_i` lies in
`B(p_i, 8ΔR_i)`. ... `‖Dη_i‖ > .99` ..."

Bound here on the actual edge charts of `L : LocalChartFamilyE` (the chart's recorded coarse-border
composite `Q_j = Qn`, the ONE shared smoothing `F`, `t = F/ρ`), with the original LFR28 bounds
`λ = 100ΔΛ, μ, τ ≤ 10⁻⁸` and, for the derivative, `σ ≤ 1/1000`, `b · 1000Δ ≤ 1`:

* `coarseBorder_slab_dist_le_KC`: (EDist) for the coarse-border chart, any `a ≤ 5`.
* `LocalChartFamilyE.edge_enclosure_KC`: `|η_j| ≤ aΔ`, `t ≤ aΔ` on `U_j` give `d(p, j) < 8Δρ(j)`,
  and `< 6Δρ(j)` for `a ≤ 4.2`.
* `edp03_buffer`: `Y_j ⊆ B(j, 8Δρ(j))`; `η_j` and `H₀` smooth on `Y_j`; at every point of `Y_j` a
  vector of `g`-length `ρ(j)` (unit for `ρ(j)⁻²g`) on which `dη_j > .99`; the compact
  `Q_j = {d(·, j) ≤ 7Δρ(j), |η_j| ≤ 4.2Δ, t ≤ 4.2Δ} ⊆ Y_j` with (EBuf) in its interior.

NOT here (they concern GAF's final map `E`, EDP01's `s`, or the LFR35/LFR36 binding): smoothness of
`g_i = u_i(E)/R_i` and `T = A/s`, (ETan) `|g_i − η_i| < 5c₃/4`, `‖Dg_i − Dη_i‖ < c₃`, (EH),
`T < .31Δ` on `t < .3Δ`, the collar least singular value `> .9`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **(EDist)** for a coarse-border chart: a point of `B(p, 100Δ)` with `|f| ≤ aΔ`, `F/ρ ≤ aΔ`
(`a ≤ 5`) lies within `Δ(√((a+μ)² + (a(1+λ)+μ+2τ)²) + τ)` of `p`. -/
theorem coarseBorder_slab_dist_le_KC {Y : Type*} [MetricSpace Y] {Q : Y → WithLp 2 (ℝ × ℝ)}
    {p : Y} {A : Set Y} {f F ρ : Y → ℝ} {Δ τ μ lam a : ℝ} (hΔ : 0 < Δ) (ha0 : 0 ≤ a)
    (ha : a ≤ 5) (hμ : μ ≤ 1 / 10 ^ 8) (hlam : lam ≤ 1 / 10 ^ 8) (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hpA : p ∈ A) (hborder : ∀ z ∈ A ∩ ball p (190 * Δ), (Q z).snd ≤ τ * Δ)
    {x : Y} (hx : x ∈ ball p (100 * Δ)) (hf : |f x - (Q x).fst| ≤ μ * Δ)
    (hF : |F x - infDist x A| ≤ μ * Δ) (hρ0 : 0 < ρ x) (hρ1 : ρ x ≤ 1 + lam)
    (hfx : |f x| ≤ a * Δ) (hηx : F x / ρ x ≤ a * Δ) :
    dist x p ≤ Δ * (Real.sqrt ((a + μ) ^ 2 + (a * (1 + lam) + μ + 2 * τ) ^ 2) + τ) := by
  have hp : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  have hτ0 : 0 ≤ τ * Δ := by simpa using hdist p hp p hp
  have hτ0' : 0 ≤ τ := by
    by_contra h
    push Not at h
    nlinarith
  have hμ0 : 0 ≤ μ * Δ := (abs_nonneg _).trans hf
  have hμ0' : 0 ≤ μ := by
    by_contra h
    push Not at h
    nlinarith
  have hxp : dist x p < 100 * Δ := hx
  have hx200 : x ∈ ball p (200 * Δ) := mem_ball.mpr (by linarith)
  have hu : |(Q x).fst| ≤ (a + μ) * Δ := by
    have h1 := abs_le.mp hf
    have h2 := abs_le.mp hfx
    have he : (a + μ) * Δ = a * Δ + μ * Δ := by ring
    rw [abs_le, he]
    constructor <;> linarith
  have hFx : F x ≤ a * Δ * (1 + lam) := by
    rw [div_le_iff₀ hρ0] at hηx
    have : a * Δ * ρ x ≤ a * Δ * (1 + lam) := mul_le_mul_of_nonneg_left hρ1 (by positivity)
    linarith
  have hc6 : a * (1 + lam) + μ ≤ 6 := by nlinarith
  have hax : infDist x A ≤ (a * (1 + lam) + μ) * Δ := by
    have h := (abs_le.mp hF).1
    have he : (a * (1 + lam) + μ) * Δ = a * Δ * (1 + lam) + μ * Δ := by ring
    rw [he]
    linarith
  have hax6 : infDist x A ≤ 6 * Δ :=
    hax.trans (mul_le_mul_of_nonneg_right hc6 hΔ.le)
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
      linarith
    have hz200 : z ∈ ball p (200 * Δ) := mem_ball.mpr (by linarith)
    have hd := (abs_le.mp (hdist x hx200 z hz200)).2
    have hsnd : (Q x).snd - (Q z).snd ≤ dist (Q x) (Q z) := by
      have h := WithLp.dist_snd_le (Q x) (Q z)
      rw [Real.dist_eq] at h
      linarith [le_abs_self ((Q x).snd - (Q z).snd)]
    linarith [hborder z ⟨hzA, mem_ball.mpr hzp⟩]
  have hb0 := hheight x hx200
  have hsndle : (Q x).snd ≤ (a * (1 + lam) + μ + 2 * τ) * Δ := by
    have he : (a * (1 + lam) + μ + 2 * τ) * Δ = (a * (1 + lam) + μ) * Δ + 2 * (τ * Δ) := by ring
    rw [he]
    linarith
  set S : ℝ := (a + μ) ^ 2 + (a * (1 + lam) + μ + 2 * τ) ^ 2 with hS
  have hsq : ‖Q x‖ ^ 2 ≤ Δ ^ 2 * S := by
    have hsq := WithLp.prod_norm_sq_eq_of_L2 (Q x)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at hsq
    have h1 : (Q x).fst ^ 2 ≤ ((a + μ) * Δ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hu 2
    have h2 : (Q x).snd ^ 2 ≤ ((a * (1 + lam) + μ + 2 * τ) * Δ) ^ 2 :=
      pow_le_pow_left₀ hb0 hsndle 2
    have he : Δ ^ 2 * S = ((a + μ) * Δ) ^ 2 + ((a * (1 + lam) + μ + 2 * τ) * Δ) ^ 2 := by
      rw [hS]
      ring
    rw [hsq, he]
    linarith
  have hnorm : ‖Q x‖ ≤ Δ * Real.sqrt S := by
    have h := Real.abs_le_sqrt hsq
    rw [abs_of_nonneg (norm_nonneg _), Real.sqrt_mul (by positivity), Real.sqrt_sq hΔ.le] at h
    exact h
  have h := (abs_le.mp (hdist x hx200 p hp)).1
  rw [hQp, dist_zero_right] at h
  have he : Δ * (Real.sqrt S + τ) = Δ * Real.sqrt S + τ * Δ := by ring
  rw [he]
  linarith

section Family

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ : ℝ}

/-- **(EDist) on an actual edge chart**: on `U_j = B(j, 100Δρ(j))`, `|η_j| ≤ aΔ` and `t ≤ aΔ`
(`a ≤ 5`) give `d(p, j) < 8Δρ(j)`, and `< 6Δρ(j)` when `a ≤ 4.2`. -/
theorem LocalChartFamilyE.edge_enclosure_KC
    (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ)
    (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8)
    {j : X} (hj : j ∈ L.edge.centres) {x : X} {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 5)
    (hx : x ∈ ball j (100 * Δ * ρ j)) (hfx : |L.edge.coord j x| ≤ a * Δ)
    (htx : L.edge.smoothing x / ρ x ≤ a * Δ) :
    dist x j < 8 * Δ * ρ j ∧ (a ≤ 21 / 5 → dist x j < 6 * Δ * ρ j) := by
  have hco := L.edge_coarse j hj
  have hcen := L.edge.chart_center j hj
  have hval := L.edge.smoothing_value j hj
  have hlip := L.lipschitz_scale
  have hrj := hρ j
  have hrx := hρ x
  have hd : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hrj hx
  set A : Set X := closure
    {y | @isEdgePoint.{u, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'} with hA
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
  have hcoord : |L.edge.coord j x| ≤ a * Δ := hfx
  unfold EdgeFamily.coord at hcoord
  rw [dite_eq_left hj] at hcoord
  have hFn : |L.edge.smoothing x / ρ j -
      @infDist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)).toPseudoMetricSpace x A| ≤ μ * Δ := by
    rw [infDist_rescale, div_eq_inv_mul, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hrj)]
    have h := hval x
    rw [← div_eq_inv_mul, div_le_iff₀ hrj]
    linarith
  have htn : L.edge.smoothing x / ρ j / (ρ x / ρ j) ≤ a * Δ := by
    have hq : L.edge.smoothing x / ρ j / (ρ x / ρ j) = L.edge.smoothing x / ρ x := by
      field_simp
    rw [hq]
    exact htx
  let C := L.edge.chart j hj
  let Fs := L.edge.smoothing
  let hMc : CompleteSpace X := complete_of_compact
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

/-- **EDP03, the clauses free of the final map**, on the actual edge chart at `j`: see the module
docstring. -/
theorem edp03_buffer
    (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ)
    (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) {j : X} (hj : j ∈ L.edge.centres) :
    let Y : Set X := {p | p ∈ ball j (100 * Δ * ρ j) ∧ |L.edge.coord j p| < 5 * Δ ∧
      L.edge.smoothing p / ρ p < 5 * Δ}
    Y ⊆ ball j (8 * Δ * ρ j) ∧
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (L.edge.coord j) Y ∧
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (edgeRowHeight Δ L.edge.smoothing ρ) Y ∧
    (∀ p ∈ Y, ∃ w : TangentSpace 𝓘(ℝ, E3) p, g.inner p w w = ρ j ^ 2 ∧
      99 / 100 < mvfderiv 𝓘(ℝ, E3) (L.edge.coord j) p w) ∧
    ∃ Q : Set X, IsCompact Q ∧ Q ⊆ Y ∧
      {p | p ∈ ball j (100 * Δ * ρ j) ∧ |L.edge.coord j p| ≤ 41 / 10 * Δ ∧
        L.edge.smoothing p / ρ p ≤ 41 / 10 * Δ} ⊆ interior Q := by
  intro Y
  have hΔ0 : 0 < Δ := by linarith
  have hrj := hρ j
  have hcoordc : Continuous (L.edge.coord j) := by
    unfold EdgeFamily.coord
    rw [dite_eq_left hj]
    let C := L.edge.chart j hj
    let hMc : CompleteSpace X := complete_of_compact
    let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let kR : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    exact C.lipschitz.continuous
  have htc : Continuous (fun y => L.edge.smoothing y / ρ y) :=
    L.edge.lipschitz_smoothing.continuous.div L.contMDiff_scale.continuous
      (fun y => (hρ y).ne')
  have hencl := fun {x : X} {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 5)
      (hx : x ∈ ball j (100 * Δ * ρ j)) (hfx : |L.edge.coord j x| ≤ a * Δ)
      (htx : L.edge.smoothing x / ρ x ≤ a * Δ) =>
    L.edge_enclosure_KC hΔ0 hμ hτ hlam hj ha0 ha hx hfx htx
  -- (1) the enclosure of `Y`
  have hY8 : Y ⊆ ball j (8 * Δ * ρ j) := fun p hp =>
    (hencl (by norm_num) le_rfl hp.1 hp.2.1.le hp.2.2.le).1
  refine ⟨hY8, (L.edge.contMDiffOn_coord hj).mono fun p hp => hp.1, ?_, ?_, ?_⟩
  · -- (2) `H₀ = Δψ(t/Δ)` is smooth on `Y`
    intro p hp
    refine ContMDiffAt.contMDiffWithinAt ?_
    rcases lt_or_ge (L.edge.smoothing p / ρ p) Δ with hlow | hhigh
    · have hev : ∀ᶠ y in 𝓝 p, L.edge.smoothing y / ρ y < Δ :=
        htc.continuousAt.eventually (gt_mem_nhds hlow)
      have he : edgeRowHeight Δ L.edge.smoothing ρ =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
        filter_upwards [hev] with y hy
        unfold edgeRowHeight
        rw [edgeSublevelProfile_eq_zero (by rw [div_le_iff₀ hΔ0]; linarith), mul_zero]
      exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq he
    · have ht := L.edge.contMDiffAt_height_of_collar hj hp.1 (by linarith [hp.2.1])
        (by linarith) (by linarith [hp.2.2])
      have hH : edgeRowHeight Δ L.edge.smoothing ρ =
          fun y => Δ * edgeSublevelProfile (L.edge.smoothing y / ρ y / Δ) := rfl
      rw [hH]
      exact contMDiffAt_const.mul
        (contDiff_edgeSublevelProfile.comp_contMDiffAt (ht.div_const Δ))
  · -- (3) `dη_j > .99` on a unit vector of `ρ(j)⁻²g`
    intro p hp
    have hd : (ρ j)⁻¹ * dist p j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hrj hp.1
    have hcen := L.edge.chart_center j hj
    unfold EdgeFamily.coord
    rw [dite_eq_left hj]
    let C := L.edge.chart j hj
    let hMc : CompleteSpace X := complete_of_compact
    let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let kR : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g
    have hcen' : C.center = j := hcen
    let _ := C.instY
    have hb0 : 0 < b := C.split.error_pos
    have hbΔ : b ≤ 1 / 1000 := by
      have : b * 1000 ≤ b * (1000 * Δ) := by nlinarith
      linarith
    have hinv : 300 * Δ + 2 * b < b⁻¹ := by
      have h1 : 1000 * Δ ≤ b⁻¹ := by
        rw [le_inv_comm₀ (by positivity) hb0]
        rw [div_eq_inv_mul] at hbΔ
        have : b ≤ 1 / (1000 * Δ) := by
          rw [le_div_iff₀ (by positivity)]
          linarith
        rwa [one_div] at this
      linarith
    have hpC : p ∈ ball C.center (100 * Δ) := by rw [hcen']; exact hd
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
    have htest := C.test
    obtain ⟨w, hw, hlt⟩ := exists_unit_lt_mvfderiv_of_rankOne gR hnR C.split htest
      (r := 100 * Δ) le_rfl (by linarith) (by linarith) (by linarith) hpC
    refine ⟨w, ?_, ?_⟩
    · have hw' : (ρ j)⁻¹ ^ 2 * g.inner p w w = 1 := hw
      have hr2 : 0 < ρ j ^ 2 := by positivity
      field_simp at hw'
      linarith
    · refine lt_of_le_of_lt ?_ hlt
      rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
      nlinarith
  · -- (4) the compact buffer `Q_j`
    let Qb : Set X := {p | dist p j ≤ 7 * Δ * ρ j ∧ |L.edge.coord j p| ≤ 21 / 5 * Δ ∧
      L.edge.smoothing p / ρ p ≤ 21 / 5 * Δ}
    have hQc : IsClosed Qb :=
      (isClosed_le (continuous_id.dist continuous_const) continuous_const).inter
        ((isClosed_le (continuous_abs.comp hcoordc) continuous_const).inter
          (isClosed_le htc continuous_const))
    refine ⟨Qb, hQc.isCompact, fun p hp => ⟨mem_ball.mpr (by nlinarith [hp.1]), by
      linarith [hp.2.1], by linarith [hp.2.2]⟩, fun p hp => ?_⟩
    let O : Set X := {p | dist p j < 7 * Δ * ρ j ∧ |L.edge.coord j p| < 21 / 5 * Δ ∧
      L.edge.smoothing p / ρ p < 21 / 5 * Δ}
    have hO : IsOpen O :=
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const).inter
        ((isOpen_lt (continuous_abs.comp hcoordc) continuous_const).inter
          (isOpen_lt htc continuous_const))
    have h6 := (hencl (by norm_num) (by norm_num) hp.1 hp.2.1 hp.2.2).2 (by norm_num)
    have hΔρ : 0 < Δ * ρ j := mul_pos hΔ0 hrj
    have hpO : p ∈ O := ⟨by nlinarith, by linarith [hp.2.1], by linarith [hp.2.2]⟩
    exact interior_maximal (fun y (hy : y ∈ O) => (⟨hy.1.le, hy.2.1.le, hy.2.2.le⟩ : y ∈ Qb)) hO
      hpO

end Family

end DifferentialGeometry.Geometry.Collapse
