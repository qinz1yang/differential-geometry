import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07Level
import DifferentialGeometry.Geometry.Fibration.ActualSlimSlabs
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimFibreSmoothTypeApplications

/-!
# GAF07 on the chain: the whole adjusted level is the original level (FC34), slim charts

Blueprint `master207B.tex`, GAF07 (B:6104–6137), slim stage (`j = 3`, `ℓ_i = 10⁵Δ`), on ONE chain,
WITHOUT BASES. The retained slim coordinate is one-dimensional (D66-7): `g_i = R_i⁻¹ proj₀ u_i(π₃E)`
(the axis coordinate). The whole adjusted level `{p ∈ Y_i | g_i(p) = a}`, `|a| < 4·10⁵Δ`, is
homeomorphic (FC34a: diffeomorphic) to the original level `{p ∈ Y_i | η_i(p) = a}`, which is the
image of a smooth embedding of the original zero fibre `F₀` (C14-FIBRE-PRE), hence connected.

Inputs: GAF07's axis value / derivative comparison (`Gaf02Chain.gaf07_slim_axis_value_GAFC`,
`Gaf02Chain.gaf07_slim_derivative_GAFC`), LFR20.1's derivative clause of the slim chart
(`SlimCentre.derivative_GAFC`: a unit vector of `R⁻²g` on which `dη > 3/4`, so a right inverse of
`dη` of gauge `≤ 4/3`), LFR20.2 (`SlimCentre.dist_lt_of_abs_coord_le_ZERO`), the compact slim slab
(`isCompact_slimSlab_GAFS`), the gauge kernel `nonempty_homeomorph_level_on_open_GAFC`, and
`SlimCentre.fibre_smooth_type_FPRE` for the original level.

* `SlimCentre.derivative_GAFC` (LFR20.1 in physical form).
* `gaf07SlimY_GAFC P i` (`Y_i`), `Gaf02Chain.gaf07SlimCoord_GAFC C i` (`g_i`),
  `isOpen_gaf07SlimY_GAFC`.
* `Gaf02Chain.gaf07_slim_level_GAFC`: the identification and connectedness.
* Consumer `Gaf02ChainEJA.gaf07_slim_level_GAFC`: the same on a chain with (JA), no numeric
  hypothesis.

The smooth TYPE of the fibre (`F₀ ≃ₘ S²` or `T²`) is NOT claimed here: `F₀` is homeomorphic to `S²`
or `T²` (C14-FIBRE-PRE; the smooth identification is lane C14-SLIM-STD's).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- **LFR20.1 in physical form**: at a slim centre `j` and `x ∈ B(j, .91Lρ(j))` there is a unit
vector `w` of the normalized metric `ρ(j)⁻²g` with `dη_j(w) > 3/4`. -/
theorem SlimCentre.derivative_GAFC {β₁ : ℝ} {j : X}
    (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) {x : X}
    (hx : dist x j < 91 / 100 * (10 ^ 6 * Δ) * ρ j) :
    ∃ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j)⁻¹ ^ 2 * g.inner x w w = 1 ∧
      3 / 4 < mvfderiv 𝓘(ℝ, E3) c.coord x w := by
  have hr := hρ j
  have hd : (ρ j)⁻¹ * dist x j < 91 / 100 * (10 ^ 6 * Δ) := by
    rw [inv_mul_lt_iff₀ hr]
    linarith
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  obtain ⟨w, hw, hdw⟩ := P.derivative x hd
  refine ⟨w, ?_, hdw⟩
  rw [scaleMetric_inner] at hw
  exact hw

/-- GAF07's original slim domain `Y_i = {p ∈ B(c_i, 10⁶Δρ(c_i)) | |η_i(p)| < 5·10⁵Δ}`. -/
def gaf07SlimY_GAFC (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V) (i : P.toLocalChartFamily.slim.finite_centres.toFinset) : Set X :=
  {p | p ∈ ball i.1 (1000000 * Δ * ρ i.1) ∧
    |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 5 * (10 ^ 5 * Δ)}

/-- GAF07's adjusted slim AXIS coordinate `g_i = R_i⁻¹ proj₀ u_i(π₃E)`. -/
def Gaf02Chain.gaf07SlimCoord_GAFC {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s
    b' s' ε γc βc Lmax τ γ δ εr e T V} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (i : P.toLocalChartFamily.slim.finite_centres.toFinset) :
    X → ℝ :=
  fun p => EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
    blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
      ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p)))

/-- The original slim domain `Y_i` is open. -/
theorem isOpen_gaf07SlimY_GAFC (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s'
    ε γc βc Lmax τ γ δ εr e T V) (i : P.toLocalChartFamily.slim.finite_centres.toFinset) :
    IsOpen (gaf07SlimY_GAFC P i) := by
  have hball : ball i.1 (1000000 * Δ * ρ i.1) = ball i.1 (10 ^ 6 * Δ * ρ i.1) := by norm_num
  have hc := (P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).contMDiffOn_coord.continuousOn
  have h := hc.abs.isOpen_inter_preimage isOpen_ball (isOpen_Iio (a := 5 * (10 ^ 5 * Δ)))
  rw [← hball] at h
  exact h

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **GAF07's whole adjusted slim level** (B:6104–6137), without BASES: with GAF01's
`c₃ < 1/1000`, for `|a| < 4·10⁵Δ` the WHOLE level `{p ∈ Y_i | g_i(p) = a}` of the adjusted axis
coordinate is homeomorphic (FC34a) to the original level `{p ∈ Y_i | η_i(p) = a}`, and both are
connected. -/
theorem gaf07_slim_level_GAFC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {a : ℝ}
    (ha : |a| < 4 * (10 ^ 5 * Δ)) :
    Nonempty ({p | p ∈ gaf07SlimY_GAFC P i ∧
          (P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p = a} ≃ₜ
        {p | p ∈ gaf07SlimY_GAFC P i ∧ C.gaf07SlimCoord_GAFC i p = a}) ∧
      IsConnected {p | p ∈ gaf07SlimY_GAFC P i ∧ C.gaf07SlimCoord_GAFC i p = a} ∧
      IsConnected {p | p ∈ gaf07SlimY_GAFC P i ∧
        (P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p = a} := by
  have hj := (Set.Finite.mem_toFinset _).mp i.2
  set cc := P.slim.centre i.1 hj with hcc
  have hri := hρ i.1
  obtain ⟨-, hΔ1, -⟩ := C.std
  have hΔ0 : (0 : ℝ) < Δ := by linarith
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  have hball : ball i.1 (1000000 * Δ * ρ i.1) = ball i.1 (10 ^ 6 * Δ * ρ i.1) := by norm_num
  obtain ⟨H, hH, hder⟩ := C.gaf07_slim_derivative_GAFC
  have hU := isOpen_gaf07SlimY_GAFC P i
  have hη : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ cc.coord (gaf07SlimY_GAFC P i) :=
    cc.contMDiffOn_coord.mono fun x hx => hball ▸ hx.1
  have hg : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (C.gaf07SlimCoord_GAFC i) (gaf07SlimY_GAFC P i) :=
    (C.gaf07_slim_smooth_GAFC i).2.contMDiffOn
  have hgη : ∀ y ∈ gaf07SlimY_GAFC P i, ‖C.gaf07SlimCoord_GAFC i y - cc.coord y‖ < 1 / 800 := by
    intro y hy
    rw [Real.norm_eq_abs]
    exact C.gaf07_slim_axis_value_GAFC hc i hy.1 hy.2
  have hcK : max H 0 * (4 / 3) < 1 := by
    have : max H 0 < 1 / 1000 := max_lt (hH.trans hc) (by norm_num)
    linarith
  have hright : ∀ y ∈ gaf07SlimY_GAFC P i, ∃ R : ℝ →L[ℝ] E3,
      (show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) cc.coord y).comp R =
          ContinuousLinearMap.id ℝ ℝ ∧
        ∀ w, Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y (R w) (R w)) ≤ 4 / 3 * ‖w‖ := by
    intro y hy
    have hyd : dist y i.1 < 91 / 100 * (10 ^ 6 * Δ) * ρ i.1 :=
      cc.dist_lt_of_abs_coord_le_ZERO (hball ▸ hy.1) (by nlinarith [hy.2, abs_nonneg (cc.coord y)])
    obtain ⟨w, hw1, hw⟩ := cc.derivative_GAFC hyd
    set d : ℝ := mvfderiv 𝓘(ℝ, E3) cc.coord y w with hd
    have hd0 : 0 < d := by linarith
    refine ⟨ContinuousLinearMap.toSpanSingleton ℝ (d⁻¹ • w), ?_, fun t => ?_⟩
    · refine ContinuousLinearMap.ext fun t => ?_
      change (mvfderiv 𝓘(ℝ, E3) cc.coord y) (t • d⁻¹ • w) = t
      rw [map_smul, map_smul, ← hd, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ hd0.ne', mul_one]
    · change Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y (t • d⁻¹ • w) (t • d⁻¹ • w)) ≤ 4 / 3 * ‖t‖
      have hsc : g.inner y (t • d⁻¹ • w) (t • d⁻¹ • w) = (t * d⁻¹) ^ 2 * g.inner y w w := by
        rw [smul_smul, map_smul, map_smul]
        simp only [smul_apply, smul_eq_mul]
        ring
      rw [hsc, show (ρ i.1)⁻¹ ^ 2 * ((t * d⁻¹) ^ 2 * g.inner y w w) =
        (t * d⁻¹) ^ 2 * ((ρ i.1)⁻¹ ^ 2 * g.inner y w w) by ring, hw1, mul_one,
        Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hd0), Real.norm_eq_abs]
      have h43 : d⁻¹ ≤ 4 / 3 := by
        rw [inv_le_comm₀ hd0 (by norm_num)]
        linarith
      calc |t| * d⁻¹ ≤ |t| * (4 / 3) := mul_le_mul_of_nonneg_left h43 (abs_nonneg t)
        _ = 4 / 3 * |t| := by ring
  have hDg : ∀ y ∈ gaf07SlimY_GAFC P i, ∀ v : E3,
      ‖(show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (C.gaf07SlimCoord_GAFC i) y) v -
        (show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) cc.coord y) v‖ ≤
        max H 0 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y v v) := by
    intro y hy v
    rw [Real.norm_eq_abs]
    refine (hder i y hy.1 (by nlinarith [hy.2]) v).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  have hQ : IsCompact {y | y ∈ gaf07SlimY_GAFC P i ∧ ‖cc.coord y‖ ≤ 401 / 100 * (10 ^ 5 * Δ)} := by
    convert isCompact_slimSlab_GAFS P.toLocalChartFamily hΔ0 i
      (a := 401 / 100 * (10 ^ 5 * Δ)) (by nlinarith) using 1
    ext x
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs]
    constructor
    · rintro ⟨⟨hx, -⟩, hxa⟩
      exact ⟨hball ▸ hx, hxa⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨⟨hball ▸ hx, by nlinarith⟩, hxa⟩
  obtain ⟨φ⟩ := nonempty_homeomorph_level_on_open_GAFC hU hη hg hℓ
    (by rw [Real.norm_eq_abs]; exact ha) hgη
    (fun y v => Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y v v)) (le_max_right _ _) hcK hright hDg hQ
  have hconn0 : IsConnected {p | p ∈ gaf07SlimY_GAFC P i ∧ cc.coord p = a} := by
    obtain ⟨F, _, _, -, -, hFc, -, hemb⟩ := cc.fibre_smooth_type_FPRE hΔ0
    obtain ⟨ι, hι, -, -, hrange⟩ := hemb a (by nlinarith)
    have hc' := isConnected_range hι.continuous
    rw [hrange] at hc'
    convert hc' using 1
    ext x
    constructor
    · rintro ⟨⟨hx, -⟩, hxa⟩
      exact ⟨hball ▸ hx, hxa⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨⟨hball ▸ hx, by rw [hxa]; linarith⟩, hxa⟩
  refine ⟨⟨φ⟩, ?_, hconn0⟩
  rw [isConnected_iff_connectedSpace] at hconn0 ⊢
  exact φ.connectedSpace_iff.mp hconn0

end Gaf02Chain

namespace Gaf02ChainEJA

variable {vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **Consumer: GAF07's whole adjusted slim level on a chain with (JA)**: for `|a| < 4·10⁵Δ`, the
whole level `{p ∈ Y_i | g_i(p) = a}` is homeomorphic to the original slim level and connected. -/
theorem gaf07_slim_level_GAFC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {a : ℝ}
    (ha : |a| < 4 * (10 ^ 5 * Δ)) :
    Nonempty ({p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
          (P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p = a} ≃ₜ
        {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
          C.toChain.gaf07SlimCoord_GAFC i p = a}) ∧
      IsConnected {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
        C.toChain.gaf07SlimCoord_GAFC i p = a} :=
  ⟨(C.toChain.gaf07_slim_level_GAFC C.c_two_lt i ha).1,
    (C.toChain.gaf07_slim_level_GAFC C.c_two_lt i ha).2.1⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
