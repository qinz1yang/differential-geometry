import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07Deriv
import DifferentialGeometry.Geometry.Fibration.ActualCircleGramExternal
import DifferentialGeometry.Geometry.Fibration.ActualConstantComparison
import DifferentialGeometry.Geometry.Fibration.ActualOriginalSlabs
import DifferentialGeometry.Geometry.Metric.WholeFiberLevelTypeNu

/-!
# GAF07 on the chain: the whole adjusted level is the original level (FC34), circle charts

Blueprint `master207B.tex`, GAF07 (B:6104–6137): on `Y_i = {|η_i| < 5ℓ_i}` put
`g_i = u_i(π_jE)/R_i`, `h_τ = (1 − τ)η_i + τg_i`; `|g_i − η_i| < 1/800`, `‖Dg_i − Dη_i‖ < c₃`
(source norm `R_i⁻²g`), the original coordinate has least singular value `> 9/10` (TCP01), so
every `h_τ` is a submersion; every level point of `h_τ` at `|a| < 4ℓ_i` lies in the compact slab
`Q_i = {|η_i| ≤ 4.01ℓ_i}`; FC34 identifies `h_1⁻¹(a)` with the original fibre `η_i⁻¹(a)`.

This module proves that identification for the CIRCLE charts (`j = 1`, `ℓ_i = 1`) on ONE chain,
WITHOUT BASES: the whole adjusted level `{p ∈ Y_i | g_i(p) = a}` is homeomorphic (FC34a:
diffeomorphic) to the original level `{p ∈ Y_i | η_i(p) = a}`, which is connected (LFR07's circle
fibre), so the adjusted level is connected. Inputs: GAF07's value comparison
(`Gaf02Chain.gaf07_circle_coordinate_G47`), the derivative comparison
(`Gaf02Chain.gaf07_circle_derivative_GAFC`), TCP01's right inverse in `R_i⁻²g`
(`tcp01_gram_right_inverse_FAM2`, which reads the packet's `β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10`), the
compact circle slab (CircleChart, as in FIBRE-PRE), the gauge kernel
`nonempty_homeomorph_level_on_open_GAFC`.

* `gaf07CircleY_GAFC P i` (`Y_i`), `Gaf02Chain.gaf07CircleCoord_GAFC C i` (`g_i = R_i⁻¹u_i(π₁E)`).
* `isCompact_circleSlab_GAFC`, `isConnected_circleLevel_GAFC` (original side, any family).
* `Gaf02Chain.gaf07_circle_level_GAFC`: the identification and connectedness.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Ehresmann

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

/-- GAF07's original circle domain `Y_i = {p ∈ B(c_i, 200ρ(c_i)) | ‖η_i(p)‖ < 5}`. -/
def gaf07CircleY_GAFC (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V) (i : P.toLocalChartFamily.circle.finite_centres.toFinset) : Set X :=
  {p | p ∈ ball i.1 (200 * ρ i.1) ∧ ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 5}

/-- GAF07's adjusted circle coordinate `g_i = R_i⁻¹u_i(π₁E)`. -/
def Gaf02Chain.gaf07CircleCoord_GAFC {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s
    b' s' ε γc βc Lmax τ γ δ εr e T V} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    X → ℝ² :=
  fun p => (ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
    (.inl i) ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p))

/-- The original circle domain `Y_i` is open. -/
theorem isOpen_gaf07CircleY_GAFC (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s'
    ε γc βc Lmax τ γ δ εr e T V) (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    IsOpen (gaf07CircleY_GAFC P i) :=
  ((cgpCircleCoord_contMDiffOn P.toLocalChartFamily
    ((Set.Finite.mem_toFinset _).mp i.2)).continuousOn).isOpen_inter_preimage isOpen_ball
      (isOpen_lt continuous_norm continuous_const)

/-- **The whole closed circle slab** `{p ∈ B(c_i, 200ρ(c_i)) | ‖η_i(p)‖ ≤ a}` is compact (`a < 100`;
the circle chart's proper disk bundle, LFR07). -/
theorem isCompact_circleSlab_GAFC (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b'
    s' ε γc βc Lmax τ γ δ εr e T V) (i : P.toLocalChartFamily.circle.finite_centres.toFinset)
    {a : ℝ} (ha : a < 100) :
    IsCompact {p | p ∈ ball i.1 (200 * ρ i.1) ∧
      ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ ≤ a} := by
  have hj := (Set.Finite.mem_toFinset _).mp i.2
  have hr := hρ i.1
  have hc0 := P.circle.chart_center i.1 hj
  let c := P.circle.chart i.1 hj
  let mR : MetricSpace X := mX.rescale (ρ i.1)⁻¹ (inv_pos.mpr hr)
  have hc : c.center = i.1 := hc0
  have h1 := c.isCompact_closedSlab_FPRE ha
  rw [hc] at h1
  convert h1 using 1
  ext x
  exact and_congr_left' (mem_ball_rescale_iff_FPRE (m := mX) hr (k := 200)).symm

/-- **The original circle level is connected** (LFR07's fibres): for `‖a‖ < 100`,
`{p ∈ B(c_i, 200ρ(c_i)) | η_i(p) = a}` is connected. -/
theorem isConnected_circleLevel_GAFC (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s
    b' s' ε γc βc Lmax τ γ δ εr e T V) (i : P.toLocalChartFamily.circle.finite_centres.toFinset)
    {a : ℝ²} (ha : ‖a‖ < 100) :
    IsConnected {p | p ∈ ball i.1 (200 * ρ i.1) ∧
      cgpCoord P.toLocalChartFamily P.zero (.inl i) p = a} := by
  have hj := (Set.Finite.mem_toFinset _).mp i.2
  have hr := hρ i.1
  have hc0 := P.circle.chart_center i.1 hj
  let c := P.circle.chart i.1 hj
  let mR : MetricSpace X := mX.rescale (ρ i.1)⁻¹ (inv_pos.mpr hr)
  have hc : c.center = i.1 := hc0
  have hz : a ∈ planeBallOpens 100 := mem_planeBallOpens_iff.mpr ha
  have hf := (c.fibres ⟨a, hz⟩).2
  have him := hf.image Subtype.val continuous_subtype_val.continuousOn
  convert him using 1
  ext x
  constructor
  · rintro ⟨hx, hxa⟩
    have hxR : x ∈ @ball X mR.toPseudoMetricSpace c.center 200 := by
      rw [hc]
      exact (mem_ball_rescale_iff_FPRE (m := mX) hr (k := 200)).mpr hx
    have hxa' : c.coord x = a := hxa
    refine ⟨⟨x, hxR, ?_⟩, ?_, rfl⟩
    · change c.coord x ∈ ball (0 : ℝ²) 100
      rw [hxa', mem_ball_zero_iff]
      exact ha
    · exact Subtype.ext hxa'
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hy' : c.coord x = a := by
      rw [← hyx]
      exact congrArg Subtype.val hy
    have hxR' : x ∈ @ball X mR.toPseudoMetricSpace c.center 200 := hyx ▸ y.2.1
    rw [hc] at hxR'
    exact ⟨(mem_ball_rescale_iff_FPRE (m := mX) hr (k := 200)).mp hxR', hy'⟩

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **GAF07's whole adjusted circle level** (B:6104–6137), without BASES: with GAF01's
`c₃ < 1/1000` and the packet's TCP01 range `β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10`, for `‖a‖ < 4` the WHOLE
level `{p ∈ Y_i | g_i(p) = a}` of the adjusted coordinate is homeomorphic (FC34a) to the original
level `{p ∈ Y_i | η_i(p) = a}`, and both are connected. -/
theorem gaf07_circle_level_GAFC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {a : ℝ²} (ha : ‖a‖ < 4) :
    Nonempty ({p | p ∈ gaf07CircleY_GAFC P i ∧ cgpCoord P.toLocalChartFamily P.zero (.inl i) p = a}
        ≃ₜ {p | p ∈ gaf07CircleY_GAFC P i ∧ C.gaf07CircleCoord_GAFC i p = a}) ∧
      IsConnected {p | p ∈ gaf07CircleY_GAFC P i ∧ C.gaf07CircleCoord_GAFC i p = a} ∧
      IsConnected {p | p ∈ gaf07CircleY_GAFC P i ∧
        cgpCoord P.toLocalChartFamily P.zero (.inl i) p = a} := by
  have hj := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  obtain ⟨H, hH, hder⟩ := C.gaf07_circle_derivative_GAFC
  have hU := isOpen_gaf07CircleY_GAFC P i
  have hη : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (cgpCoord P.toLocalChartFamily P.zero (.inl i))
      (gaf07CircleY_GAFC P i) :=
    (cgpCircleCoord_contMDiffOn P.toLocalChartFamily hj).mono fun x hx => hx.1
  have hg : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (C.gaf07CircleCoord_GAFC i)
      (gaf07CircleY_GAFC P i) :=
    (C.gaf07_circle_smooth_GAFC i).2.contMDiffOn
  have hgη : ∀ y ∈ gaf07CircleY_GAFC P i,
      ‖C.gaf07CircleCoord_GAFC i y - cgpCoord P.toLocalChartFamily P.zero (.inl i) y‖ < 1 / 800 :=
    fun y hy => (C.gaf07_circle_coordinate_G47 hc i hy.1 hy.2).1
  have hcK : max H 0 * 2 < 1 := by
    have : max H 0 < 1 / 1000 := max_lt (hH.trans hc) (by norm_num)
    linarith
  have hright : ∀ y ∈ gaf07CircleY_GAFC P i, ∃ R : ℝ² →L[ℝ] E3,
      (show E3 →L[ℝ] ℝ² from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²)
        (cgpCoord P.toLocalChartFamily P.zero (.inl i)) y).comp R =
          ContinuousLinearMap.id ℝ ℝ² ∧
        ∀ w, Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y (R w) (R w)) ≤ 2 * ‖w‖ := by
    intro y hy
    have key := tcp01_gram_right_inverse_FAM2 P hβ hd hj hy.1
    let _ := radialScaledBundle g (ρ i.1)⁻¹ (inv_pos.mpr hri)
    obtain ⟨-, R, hR, -, hR2⟩ := key
    refine ⟨R, hR, fun w => ?_⟩
    have hn := norm_tangent_radialScaled_KA4 g hri y (R w)
    calc Real.sqrt _ = ‖R w‖ := hn.symm
      _ ≤ ‖R‖ * ‖w‖ := R.le_opNorm w
      _ ≤ 2 * ‖w‖ := mul_le_mul_of_nonneg_right hR2.le (norm_nonneg w)
  have hDg : ∀ y ∈ gaf07CircleY_GAFC P i, ∀ v : E3,
      ‖(show E3 →L[ℝ] ℝ² from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (C.gaf07CircleCoord_GAFC i) y) v -
        (show E3 →L[ℝ] ℝ² from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²)
          (cgpCoord P.toLocalChartFamily P.zero (.inl i)) y) v‖ ≤
        max H 0 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y v v) := by
    intro y hy v
    refine (hder i y hy.1 (by linarith [hy.2]) v).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  have hQ : IsCompact {y | y ∈ gaf07CircleY_GAFC P i ∧
      ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) y‖ ≤ 401 / 100 * 1} := by
    convert isCompact_circleSlab_GAFC P i (a := 401 / 100) (by norm_num) using 1
    ext x
    constructor
    · rintro ⟨⟨hx, -⟩, hxa⟩
      exact ⟨hx, by linarith⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨⟨hx, by linarith⟩, by linarith⟩
  obtain ⟨φ⟩ := nonempty_homeomorph_level_on_open_GAFC hU hη hg le_rfl (by linarith) hgη
    (fun y v => Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y v v)) (le_max_right _ _) hcK hright hDg hQ
  have hconn0 : IsConnected {p | p ∈ gaf07CircleY_GAFC P i ∧
      cgpCoord P.toLocalChartFamily P.zero (.inl i) p = a} := by
    convert isConnected_circleLevel_GAFC P i (a := a) (by linarith) using 1
    ext x
    constructor
    · rintro ⟨⟨hx, -⟩, hxa⟩
      exact ⟨hx, hxa⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨⟨hx, by rw [hxa]; linarith⟩, hxa⟩
  refine ⟨⟨φ⟩, ?_, hconn0⟩
  rw [isConnected_iff_connectedSpace] at hconn0 ⊢
  exact φ.connectedSpace_iff.mp hconn0

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
