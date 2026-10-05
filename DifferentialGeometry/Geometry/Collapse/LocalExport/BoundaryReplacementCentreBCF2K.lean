import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZ
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeBCutoff
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeCenterSplittingExclusion

/-!
# BCF02, strict replacement, step one: the selected centre is a nonslim one-stratum point

External draft 61 §6.2, step one of (Repl_∂), disposition D61-10; blueprint `master207B.tex`, BCF02
(B:9771–9779) and FDC01 (B:7174–7199): "Its witnessing selected edge center `p_i` has distance
greater than 20. Therefore the zero tenth-cover and slim-cover exclusions in FDC01 are both eligible
at `p_i` and prove that it is an actual nonslim one-stratum point, not merely a strong-edge center."

On the boundary family the selected edge index set is `I_e^B = edgeB.centres`; the eligibility of
`p_i` for the zero and slim covers (both stated on `U₁`) is `edgeB_domain` (`B(i, 1000Δρ_i) ⊆ U₁`),
and the no-three input is the field `rank_le_two` on `U₁` (no tail needed). `q ∈ M₂` is used only
through two ORIGINAL-coordinate facts, exactly as on the closed side (lane C14-FDC,
`fdc01_centre_exclusions_FDC`): `q` lies outside every selected zero ball `B(z, .38R_z)` (boundary
ZSP02 puts that ball in `int Z`, and `M₂ ⊆ W ∖ int Z`) and outside every selected slim region
`{d(q, k) < 9Δρ_k, |η_k(q)| < 10Δ}` (BCF01's (K) puts the original slabs over `int K₃`, so such a
point lies in `int_{M₁} S`, removed from `M₂`). Those two inclusions concern the final map and are
bound later.

* `EdgeFamilyOn.coord_self_BCF2K`, `EdgeFamilyOn.coord_lipschitz_BCF2K`: `η_j(j) = 0` and the
  `max(1 + σ, 0)/ρ(j)`-Lipschitz bound of the actual edge coordinate `coord_BAUGA`;
* `SlimCentreOn.coord_self_BCF2K`, `SlimCentreOn.abs_coord_sub_le_BCF2K`: the same for a slim
  coordinate on a complete carrier;
* `LocalPacketsOn.bcf02_zero_exclusion_BCF2K`: a zero-stratum point `p ∈ U₁` and `d(q, p) < 6Δρ(p)`
  give a selected zero centre `z` with `p ∈ B(z, R_z/10)` and `d(q, z) < .38R_z`;
* `ChartFamilyOn.bcf02_slim_exclusion_BCF2K`: a slim one-stratum point `p ∈ U₁` and
  `d(q, p) < 6Δρ(p)` give a selected slim centre `k` with `d(q, k) < 9Δρ(k)` and `|η_k(q)| < 10Δ`;
* `LocalPacketsOnBFR.edgeB_centre_stratum_one_BCF2K`: a revised edge centre outside the zero stratum
  is one-stratum (`rank_le_two` at the centre, EGP01 at its strong-edge quality);
* `LocalPacketsOnBFR.bcf02_centre_decision_BCF2K` (step one): for `i ∈ I_e^B` and `d(q, i) < 6Δρ_i`
  with the two `M₂` facts, `p_i` is a one-stratum point and nonslim (the actual later `β₁`
  predicate).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalPacketsOn`, as a named local instance. -/
local instance instMetricNOn_BCF2K
    (P : LocalPacketsOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V U₁
      U₂) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalPacketsOn`, as a named local instance. -/
local instance instChartedNOn_BCF2K
    (P : LocalPacketsOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V U₁
      U₂) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalPacketsOn`, as a named local instance. -/
local instance instMetricCOn_BCF2K
    (P : LocalPacketsOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V U₁
      U₂) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The actual edge coordinate of a regional edge family vanishes at its centre. -/
theorem EdgeFamilyOn.coord_self_BCF2K
    (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) {j : X}
    (hj : j ∈ F.centres) : F.coord_BAUGA j j = 0 := by
  obtain ⟨Y, mY, q, f, h0, -⟩ := F.exists_split_BCG1 hj
  rw [F.coord_BAUGA_of_mem hj]
  exact h0

/-- The actual edge coordinate `η_j` is `max(1 + σ, 0)/ρ(j)`-Lipschitz for the physical distance. -/
theorem EdgeFamilyOn.coord_lipschitz_BCF2K
    (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) {j : X}
    (hj : j ∈ F.centres) (y z : X) :
    |F.coord_BAUGA j y - F.coord_BAUGA j z| ≤ max (1 + σc) 0 / ρ j * dist y z := by
  have hrj := hρ j
  have he : ((Real.toNNReal (1 + σc) : NNReal) : ℝ) * ((ρ j)⁻¹ * dist y z) =
      max (1 + σc) 0 / ρ j * dist y z := by
    rw [Real.coe_toNNReal']
    field_simp
  rw [F.coord_BAUGA_of_mem hj]
  unfold EdgeFamilyOn.coord_BCG1
  let C := F.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have h := C.lipschitz.dist_le_mul y z
  change |C.coord y - C.coord z| ≤
    ((Real.toNNReal (1 + σc) : NNReal) : ℝ) * ((ρ j)⁻¹ * @dist X mX.toDist y z) at h
  change |C.coord y - C.coord z| ≤ max (1 + σc) 0 / ρ j * @dist X mX.toDist y z
  linarith

/-- The slim coordinate of a slim centre on a complete carrier vanishes at its centre. -/
theorem SlimCentreOn.coord_self_BCF2K {β₁ : ℝ} {j : X}
    (S : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) : S.coord_BCG2 j = 0 := by
  have hr := hρ j
  unfold SlimCentreOn.coord_BCG2
  let P := S.packet
  let iZ := S.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hr)
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hr)
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr hr)
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr hr)
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr hr)).mpr hMc
  exact P.coord_center

/-- The slim coordinate on a complete carrier is `(1 + σs)ρ(j)⁻¹`-Lipschitz for the physical
distance. -/
theorem SlimCentreOn.abs_coord_sub_le_BCF2K {β₁ : ℝ} {j : X}
    (S : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) (hσs : 0 ≤ σs) (y z : X) :
    |S.coord_BCG2 y - S.coord_BCG2 z| ≤ (1 + σs) * (ρ j)⁻¹ * dist y z := by
  have hr := hρ j
  have hK : ((Real.toNNReal (1 + σs) : NNReal) : ℝ) = 1 + σs := Real.coe_toNNReal _ (by linarith)
  suffices h' : |S.coord_BCG2 y - S.coord_BCG2 z| ≤ (1 + σs) * ((ρ j)⁻¹ * dist y z) by
    calc |S.coord_BCG2 y - S.coord_BCG2 z| ≤ (1 + σs) * ((ρ j)⁻¹ * dist y z) := h'
      _ = (1 + σs) * (ρ j)⁻¹ * dist y z := by ring
  unfold SlimCentreOn.coord_BCG2
  let P := S.packet
  let iZ := S.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hr)
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hr)
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr hr)
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr hr)
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr hr)).mpr hMc
  have h := P.lipschitz.dist_le_mul y z
  rw [hK, Real.dist_eq] at h
  exact h

/-- **BCF02 / FDC01's zero exclusion on the regional packets**: a zero-stratum point `p` of the
eligible region `U₁` and a point `q` with `d(q, p) < 6Δρ(p)` give a selected zero centre `z` with
`p ∈ B(z, R_z/10)` (the tenth-radius cover of `U₁ ∩ Z₀`) and `d(q, z) < .38R_z` (`T ≥ 1000Δ`,
`100ΔΛ ≤ 1/100`). -/
theorem LocalPacketsOn.bcf02_zero_exclusion_BCF2K
    (P : LocalPacketsOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V U₁
      U₂) (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hT : 1000 * Δ ≤ T)
    {p q : X} (hpU : p ∈ U₁) (hp : p ∈ scaledSplittingStratum.{0, 0} ρ hρ β 0)
    (hqp : dist q p < 6 * Δ * ρ p) :
    ∃ z, ∃ hz : z ∈ P.zero.centres, dist p z < (P.zero.zero z hz).radius / 10 ∧
      dist q z < 38 / 100 * (P.zero.zero z hz).radius := by
  have hcov := P.zero.covers_stratum ⟨hpU, hp⟩
  simp only [mem_iUnion] at hcov
  obtain ⟨z, hz, hpz⟩ := hcov
  refine ⟨z, hz, hpz, ?_⟩
  have hrz := hρ z
  have hT0 : 0 < T := by nlinarith
  have hTR : T * ρ z ≤ (P.zero.zero z hz).radius := (P.zero.radius_mem z hz).1
  have hR : 0 < (P.zero.zero z hz).radius := lt_of_lt_of_le (mul_pos hT0 hrz) hTR
  have hpz' : dist p z < (P.zero.zero z hz).radius / 10 := hpz
  have hρp : ρ p ≤ ρ z + Λ * ((P.zero.zero z hz).radius / 10) := by
    have h1 := P.lipschitz_scale.dist_le_mul p z
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1
    have h2 : Λ * dist p z ≤ Λ * ((P.zero.zero z hz).radius / 10) :=
      mul_le_mul_of_nonneg_left hpz'.le hΛ
    linarith [(abs_le.mp h1).2]
  have h6 : 6 * Δ * ρ p ≤ 6 * Δ * ρ z + 6 * Δ * Λ * ((P.zero.zero z hz).radius / 10) := by
    have := mul_le_mul_of_nonneg_left hρp (by positivity : (0 : ℝ) ≤ 6 * Δ)
    linarith
  have hz1 : 6 * Δ * ρ z ≤ 6 / 1000 * (P.zero.zero z hz).radius := by
    have h1 : 1000 * Δ * ρ z ≤ T * ρ z := mul_le_mul_of_nonneg_right hT hrz.le
    linarith
  have hz2 : 6 * Δ * Λ * ((P.zero.zero z hz).radius / 10) ≤
      6 / 100000 * (P.zero.zero z hz).radius := by
    have h1 : Δ * Λ ≤ 1 / 10000 := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hR.le
    nlinarith
  have h3 := dist_triangle q p z
  linarith

/-- **BCF02 / FDC01's slim exclusion on the regional family**: a slim point `p` of `U₁` in the
one-stratum (the ORIGINAL slim predicate at scale `ρ(p)`) and a point `q` with `d(q, p) < 6Δρ(p)`
give a selected slim centre `k` with `d(q, k) < 9Δρ(k)` and `|η_k(q)| < 10Δ`
(`0 ≤ σs ≤ 1/100`, `100ΔΛ ≤ 1/100`). -/
theorem ChartFamilyOn.bcf02_slim_exclusion_BCF2K
    (L : ChartFamilyOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc U₁ U₂)
    (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) {p q : X} (hpU : p ∈ U₁)
    (hp : p ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1)
    (hsl : ∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)))
    (hqp : dist q p < 6 * Δ * ρ p) :
    ∃ k, ∃ hk : k ∈ L.slim.centres, dist q k < 9 * Δ * ρ k ∧
      |(L.slim.centre k hk).coord_BCG2 q| < 10 * Δ := by
  obtain ⟨k, hk, hsub⟩ := L.slim.covers p ⟨hpU, hp⟩ hsl
  refine ⟨k, hk, ?_⟩
  have hrp := hρ p
  have hrk := hρ k
  have hpk : dist p k < 2 * (Δ * ρ k) := hsub (mem_ball_self (by positivity))
  have hρp : ρ p ≤ 10002 / 10000 * ρ k := by
    have h1 := L.lipschitz_scale.dist_le_mul p k
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1
    have h2 : Λ * dist p k ≤ Λ * (2 * (Δ * ρ k)) := mul_le_mul_of_nonneg_left hpk.le hΛ
    have h3 : Δ * Λ * ρ k ≤ 1 / 10000 * ρ k := by
      have h4 : Δ * Λ ≤ 1 / 10000 := by linarith
      exact mul_le_mul_of_nonneg_right h4 hrk.le
    linarith [(abs_le.mp h1).2]
  have hqk : dist q k < 9 * Δ * ρ k := by
    have h1 := dist_triangle q p k
    have h2 : 6 * Δ * ρ p ≤ 6 * Δ * (10002 / 10000 * ρ k) :=
      mul_le_mul_of_nonneg_left hρp (by positivity)
    have := mul_pos hΔ hrk
    linarith
  refine ⟨hqk, ?_⟩
  have hlip := (L.slim.centre k hk).abs_coord_sub_le_BCF2K hσs q k
  rw [(L.slim.centre k hk).coord_self_BCF2K, sub_zero] at hlip
  have h1 : (1 + σs) * (ρ k)⁻¹ * dist q k ≤ 101 / 100 * (ρ k)⁻¹ * dist q k := by
    have := inv_pos.mpr hrk
    gcongr
    linarith
  have h2 : 101 / 100 * (ρ k)⁻¹ * dist q k < 101 / 100 * (ρ k)⁻¹ * (9 * Δ * ρ k) :=
    mul_lt_mul_of_pos_left hqk (by positivity)
  have h3 : 101 / 100 * (ρ k)⁻¹ * (9 * Δ * ρ k) = 909 / 100 * Δ := by
    have hc : (ρ k)⁻¹ * ρ k = 1 := inv_mul_cancel₀ hrk.ne'
    linear_combination (909 / 100 * Δ) * hc
  linarith

/-- **A revised edge centre outside the zero stratum is a one-stratum point**: the centre lies in
`U₁` (`edgeB_domain`), so `rank_le_two` bounds its rank by two; EGP01 at its strong-edge quality
(`b, s < 10⁻⁶`, `β 2 < 10⁻⁶`) excludes rank two. -/
theorem LocalPacketsOnBFR.edgeB_centre_stratum_one_BCF2K
    (F : LocalPacketsOnBFR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz U₁ U₂ Ue₁ Ue₂) (hΔ : 0 < Δ) (hb : b < 1 / 1000000) (hs : s < 1 / 1000000)
    (hβ2 : β 2 < 1 / 1000000) {j : X} (hj : j ∈ F.edgeB.centres)
    (h0 : j ∉ scaledSplittingStratum.{0, 0} ρ hρ β 0) :
    j ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1 := by
  have hjU : j ∈ U₁ := F.edgeB_domain j hj (mem_ball_self (by have := hρ j; positivity))
  have h2 : scaledSplittingRank.{0, 0} ρ hρ β j ≠ 2 :=
    scaledSplittingRank_ne_two_of_scaled_edge.{0, 0, 0} ρ hρ β (F.edgeB.strong j hj) hb hs hβ2
  have hle : scaledSplittingRank.{0, 0} ρ hρ β j ≤ 2 := F.rank_le_two j hjU
  have hne : scaledSplittingRank.{0, 0} ρ hρ β j ≠ 0 := fun h => h0 h
  change scaledSplittingRank.{0, 0} ρ hρ β j = 1
  omega

/-- **(Repl_∂), step one: the selected centre is a nonslim one-stratum point.** For a revised edge
centre `i` and a point `q` with `d(q, i) < 6Δρ_i` (EDP03's enclosure), lying outside every selected
zero ball `B(z, .38R_z)` and outside every selected slim region `{d(q, k) < 9Δρ_k,
|η_k(q)| < 10Δ}` (the two original-coordinate consequences of `q ∈ M₂`), the centre `i` is a
one-stratum point and nonslim (the ACTUAL `β₁` slim predicate at scale `ρ(i)`). -/
theorem LocalPacketsOnBFR.bcf02_centre_decision_BCF2K
    (F : LocalPacketsOnBFR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz U₁ U₂ Ue₁ Ue₂) (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100)
    (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) (hb : b < 1 / 1000000)
    (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000) {i : X} (hi : i ∈ F.edgeB.centres) {q : X}
    (hqi : dist q i < 6 * Δ * ρ i)
    (hZ : ∀ z (hz : z ∈ F.zero.centres), 38 / 100 * (F.zero.zero z hz).radius ≤ dist q z)
    (hS : ∀ k (hk : k ∈ F.slim.centres), dist q k < 9 * Δ * ρ k →
      10 * Δ ≤ |(F.slim.centre k hk).coord_BCG2 q|) :
    i ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1 ∧
      ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
          Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
            (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i (WithLp.toLp 2 ((0 : ℝ), z))
              (β 1))) := by
  have hiU : i ∈ U₁ := F.edgeB_domain i hi (mem_ball_self (by have := hρ i; positivity))
  have h0 : i ∉ scaledSplittingStratum.{0, 0} ρ hρ β 0 := by
    intro h0
    obtain ⟨z, hz, -, hqz⟩ :=
      F.toLocalPacketsOn.bcf02_zero_exclusion_BCF2K hΔ hΛ hΔΛ hT hiU h0 hqi
    exact absurd (hZ z hz) (not_le.mpr hqz)
  have h1 := F.edgeB_centre_stratum_one_BCF2K hΔ hb hs hβ2 hi h0
  refine ⟨h1, fun hsl => ?_⟩
  obtain ⟨k, hk, hqk, hηk⟩ :=
    F.toChartFamilyOn.bcf02_slim_exclusion_BCF2K hΔ hΛ hΔΛ hσs hσs1 hiU h1 hsl hqi
  exact absurd (hS k hk hqk) (not_le.mpr hηk)

end DifferentialGeometry.Geometry.Collapse
