import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeTraceOWF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeHomotopyKernelOWF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesStageSubmersionEdge

/-!
# O-WF G6b (part 3): the transversality of EDP04's homotopy on the boundary chain

For `h_θ = (1 − θ)η_j + θ(g − a)` and `T_θ = (1 − θ)H₀ + θ(T − δ)` (`0 ≤ δ ≤ Δ/10`) on the
original source `Y_j ⊆ W°`
(`g = λ_j ∘ E ∘ val`, `T = A/s ∘ val`):

* `BoundaryGaf02ChainE.homotopy_reg_OWF`: `dh_θ ≠ 0` at every point of `Y_j` (`dη_j > .99` on a
  unit vector, `|dg − dη_j| ≤ H_d < c₃`, closed twin: the `hreg` step of `edp04_whole_disk_EFE`);
* `BoundaryGaf02ChainE.homotopy_face_OWF`: on the rim of the trace (`h_θ = 0`, `T_θ = 4Δ`,
  `|a| < 4.05Δ`) the pair `(h_θ, T_θ)` is a submersion onto `ℝ²` (closed twin:
  `edge_homotopy_conorm_EDPE` + `surjective_of_conorm_pos_EDP6`), from the rim co-norm of
  `(η_j, t)` and the rim kernel along the homotopy `homotopy_pair_surjective_of_conorm_OWF`.

Supporting: `edgePlateau_OWF` (the cutoff plateau `{|η_j| < 8Δ, t < 8Δ}` of the chart ball),
`abs_dedge_sub_deta_plateau_OWF`, `homotopy_rim_region_OWF`, `mvfderiv_congr_OWF`.
Register premises: `μ, τ ≤ 10⁻⁸`, `σc ≤ 10⁻³`, `b ≤ 1/(1000Δ)`, `c₃ < 10⁻⁵`, N76-9,
`0 ≤ ε < 1`, `0 < γc ≤ 1/100`, `βc ≤ 10⁻⁵`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- Eventually equal real functions have the same differential. -/
theorem mvfderiv_congr_OWF {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {f₁ f : M → ℝ} {x : M} (h : f₁ =ᶠ[𝓝 x] f) : mvfderiv I f₁ x = mvfderiv I f x := by
  unfold mvfderiv
  rw [h.mfderiv_eq, h.eq_of_nhds]
  rfl

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- The cutoff plateau `{|η_j| < 8Δ, t < 8Δ}` of the chart ball of the `edgeB` centre `j`. -/
def edgePlateau_OWF (j : S.EdgeIdx_BAUGD) : Set (W.pieceInterior ⊤) :=
  letI := inducedMetricSpace S.completion.metric
  {z | z ∈ ball j.1 (100 * Δ * S.rho j.1) ∧ |S.edgeEta_BIF j.1 z| < 8 * Δ ∧
    S.edgeHeightRaw z < 8 * Δ}

theorem isOpen_edgePlateau_OWF (j : S.EdgeIdx_BAUGD) : IsOpen (S.edgePlateau_OWF j) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hη : IsOpen (ball j.1 (100 * Δ * S.rho j.1) ∩
      S.family.edgeB.coord_BAUGA j.1 ⁻¹' Ioo (-(8 * Δ)) (8 * Δ)) :=
    (S.family.edgeB.contMDiffOn_coord_BAUGA hj).continuousOn.isOpen_inter_preimage isOpen_ball
      isOpen_Ioo
  have ht : IsOpen (S.edgeHeightRaw ⁻¹' Iio (8 * Δ)) :=
    isOpen_Iio.preimage S.family.continuous_edgeBHeight_BAUGA
  convert hη.inter ht using 1
  ext z
  simp only [edgePlateau_OWF, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo, mem_Iio,
    abs_lt, S.edgeEta_eq_coord_BAUGP2 j z]
  tauto

/-- On the cutoff plateau the normalized `edgeB` coordinate of `F_∂` is `η_j`. -/
theorem edgeRatio_boundaryOriginalMap_plateau_OWF (hΔ : 0 < Δ) (j : S.EdgeIdx_BAUGD)
    {z : W.pieceInterior ⊤} (hz : z ∈ S.edgePlateau_OWF j) :
    S.edgeRatio_BAUGD j (S.boundaryOriginalMap z.val) = S.edgeEta_BIF j.1 z := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨hd, hη, h8⟩ := hz
  have hζ := S.edgeCutoff_eq_one_BAUGD hΔ j z (mem_ball.mp hd) hη h8.le
  rw [S.edgeRatio_boundaryOriginalMap_BAUGD, hζ, one_mul, S.edgeEta_eq_coord_BAUGP2 j z]

end BoundarySupplyCore

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- The adjusted edge coordinate `g = λ_j ∘ E ∘ val` is smooth on `W°`. -/
theorem edgeAdjusted_contMDiff_OWF (j : S.EdgeIdx_BAUGD) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun q : W.pieceInterior ⊤ => S.edgeRatio_BAUGD j (C.toChain.E q.val)) :=
  (S.edgeRatio_BAUGD j).contDiff.comp_contMDiff
    ((C.stage_smooth_BAUGD 3).comp (isLocalDiffeomorph_pieceInterior_val W ⊤).contMDiff)

/-- `T ∘ val` is smooth on `W°`. -/
theorem heightRatio_interior_contMDiff_OWF :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun q : W.pieceInterior ⊤ => C.toChain.heightRatio q.val) :=
  C.heightRatio_contMDiff_BAUGD.comp (isLocalDiffeomorph_pieceInterior_val W ⊤).contMDiff

include C in
/-- **`dg` is close to `dη_j` on the cutoff plateau** (A3c; twin of
`abs_dedge_sub_deta_BAUGD` without the lower height bound). -/
theorem abs_dedge_sub_deta_plateau_OWF (hΔ : 0 < Δ) {Hd : ℝ}
    (hder : ∀ (p : W.Carrier) (v : TangentSpace W.model p),
      ‖mvfderiv W.model C.toChain.E p v - mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
        Hd * Real.sqrt (g.inner p v v))
    (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤} (hq : q ∈ S.edgePlateau_OWF j)
    (hD : ENNReal.ofReal 4 ≤ distanceToBoundary W g q.val) (u : TangentSpace (𝓡 3) q) :
    |mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => S.edgeRatio_BAUGD j (C.toChain.E z.val)) q u -
        mvfderiv (𝓡 3) (S.edgeEta_BIF j.1) q u| ≤
      (S.rho j.1)⁻¹ * (Hd * Real.sqrt (S.completion.metric.inner q u u)) := by
  have hE : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) C.toChain.E q.val :=
    ((C.stage_smooth_BAUGD 3) _).mdifferentiableAt (by simp)
  have hF := C.mdifferentiableAt_boundaryOriginalMap_BAUGD q.val
  have hev : (fun z : W.pieceInterior ⊤ =>
      S.edgeRatio_BAUGD j (S.boundaryOriginalMap z.val)) =ᶠ[𝓝 q] S.edgeEta_BIF j.1 := by
    filter_upwards [(S.isOpen_edgePlateau_OWF j).mem_nhds hq] with z hz
    exact S.edgeRatio_boundaryOriginalMap_plateau_OWF hΔ j hz
  exact abs_dclm_sub_germ_BAUGD (S.edgeRatio_BAUGD j) (inv_nonneg.mpr (S.rho_pos j.1).le)
    (fun w => by rw [← div_eq_inv_mul]; exact S.abs_edgeRatio_le_BAUGD j w) C.toChain.E
    S.boundaryOriginalMap q hE hF _ hev (fun v => hder _ v) S.completion.metric
    (S.inner_dval_BAUGD q hD) u

include C in
/-- **`dh_θ ≠ 0` on the original source** (see the module docstring). -/
theorem homotopy_reg_OWF (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000) (j : S.EdgeIdx_BAUGD) (a : ℝ) {θ : ℝ}
    (hθ : θ ∈ Icc (0 : ℝ) 1) {q : W.pieceInterior ⊤} (hq : q ∈ S.edgeSource_OWF j) :
    Surjective (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fun z : W.pieceInterior ⊤ =>
      (1 - θ) * S.edgeEta_BIF j.1 z + θ * (S.edgeRatio_BAUGD j (C.toChain.E z.val) - a)) q) := by
  obtain ⟨hΛ, hΔ0, hμ', hτ', hΔΛ, hV, hβ1, hb0, he, hΔ1, hLΛ, -⟩ := C.std
  have hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8 := by nlinarith
  have hb8 : b * (1000 * Δ) ≤ 1 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 1000 * Δ)).mp hb
    linarith
  obtain ⟨-, hηs, -, hdη, -⟩ := S.edge_buffer_OWF hΔ1 hμ hτ hlam hσc hb8 j
  obtain ⟨w, hw, hlt⟩ := hdη q hq
  have hηc : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (S.edgeEta_BIF j.1) q :=
    hηs.contMDiffAt ((S.isOpen_edgeSource_OWF j).mem_nhds hq)
  have hg0 := (C.edgeAdjusted_contMDiff_OWF j) q
  have hgc : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun z : W.pieceInterior ⊤ =>
      S.edgeRatio_BAUGD j (C.toChain.E z.val) - a) q := hg0.sub contMDiffAt_const
  obtain ⟨hd, hη5, ht5⟩ := hq
  have hD4 := S.four_le_distanceToBoundary_of_edge_plateau_BBP hΛ hΔ0 hμ' hτ' hΔΛ hV hβ1 hb0 he
    j hd (by linarith) (by linarith)
  obtain ⟨Hd, hHd, hder0⟩ := C.stage_derivative_lt_BAUGD 2
  have hder : ∀ (p : W.Carrier) (v : TangentSpace W.model p),
      ‖mvfderiv W.model C.toChain.E p v - mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
        Hd * Real.sqrt (g.inner p v v) := hder0
  have hpl : q ∈ S.edgePlateau_OWF j := ⟨hd, by linarith, by linarith⟩
  have hcl := C.abs_dedge_sub_deta_plateau_OWF hΔ0 hder j hpl hD4 w
  have hrj := S.rho_pos j.1
  rw [hw, Real.sqrt_sq hrj.le] at hcl
  have hRR : (S.rho j.1)⁻¹ * (Hd * S.rho j.1) = Hd := by field_simp
  rw [hRR] at hcl
  have hHd0 : 0 ≤ Hd := (abs_nonneg _).trans hcl
  refine surjective_mfderiv_of_mvfderiv_ne_zero_EFE w ?_
  have e1 := mvfderiv_homotopy_scalar_EFE θ hηc hgc w
  beta_reduce at e1
  have e2 := mvfderiv_sub_const_EFE (I := 𝓡 3)
    (f := fun z : W.pieceInterior ⊤ => S.edgeRatio_BAUGD j (C.toChain.E z.val))
    (hg0.mdifferentiableAt (by simp)) a w
  rw [e1, e2]
  have h1 := (abs_le.mp hcl).1
  have h2 : θ * (-Hd) ≤ θ * (mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ =>
      S.edgeRatio_BAUGD j (C.toChain.E z.val)) q w - mvfderiv (𝓡 3) (S.edgeEta_BIF j.1) q w) :=
    mul_le_mul_of_nonneg_left h1 hθ.1
  have h3 : θ * Hd ≤ 1 * Hd := mul_le_mul_of_nonneg_right hθ.2 hHd0
  intro h0
  nlinarith

include C in
/-- **The rim region along the homotopy**: an interior point of the chart ball with
`|η_j| < 4.1Δ` and `3.8Δ < t < 4.2Δ` has `D ≥ 4`, lies in the plateau region, `|A − F| < c₃ρ`
and `ρ(q)/ρ_j > 99/100` (twin of `rim_region_BAUGD` without `T = 4Δ`). -/
theorem homotopy_rim_region_OWF (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 41 / 10 * Δ) (h39 : 19 / 5 * Δ < S.edgeHeightRaw q)
    (h41 : S.edgeHeightRaw q < 21 / 5 * Δ) :
    ENNReal.ofReal 4 ≤ distanceToBoundary W g q.val ∧ q ∈ S.edgeRegion_BAUGD j ∧
      |C.toChain.height q.val - S.edgeSmoothing_BAUGD q| < c 2 * S.rho q.val ∧
      99 / 100 < S.rho q.val / S.rho j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨hΛ, hΔ0, -, -, hΔΛ, hV, hβ1, hb, -, hΔ1, hLΛ, -⟩ := C.std
  have hj : j.1 ∈ S.family.edgeB.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hj10 : ENNReal.ofReal 10 < distanceToBoundary W g j.1 :=
    lt_trans (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by norm_num, by norm_num⟩)
      (S.family.edgeB.centres_subset hj)
  have hD4 := S.four_lt_distanceToBoundary_of_dist_lt_BAUGC hV hβ1 hb hΔ0.le hj10
    (C := 100 * Δ) (by positivity) (by linarith) hd
  have hrj := S.rho_pos j.1
  have hρ99 : 99 / 100 < S.rho q.val / S.rho j.1 := by
    have h := S.abs_rho_sub_le_of_dist_lt_BAUGD hΛ hΔ1 hV hβ1 hb hj10 (r := 100 * Δ)
      (by positivity) (by linarith) hd
    have h1 := (abs_le.mp h).1
    rw [lt_div_iff₀ hrj]
    nlinarith [mul_pos hΔ0 hrj, mul_nonneg hΛ (mul_pos hΔ0 hrj).le]
  have hAF := C.stage_error_lt_BAUGD 2 q.val
  have hAerr : |C.toChain.height q.val - S.heightCoord_BIF (S.boundaryOriginalMap q.val)| <
      c 2 * S.rho q.val := by
    have h1 := S.abs_heightFun_le_BAUGD (C.toChain.E q.val - S.boundaryOriginalMap q.val)
    rw [map_sub] at h1
    exact h1.trans_lt hAF
  have hη8 : |S.edgeEta_BIF j.1 q| < 8 * Δ := by linarith
  have hm := S.edgeBMarker_eq_one_BAUGD hΔ0 j q hd hη8 (by linarith) (by linarith)
  have hAFe : S.heightCoord_BIF (S.boundaryOriginalMap q.val) = S.edgeSmoothing_BAUGD q := by
    rw [S.heightCoord_boundaryOriginalMap_BAUGD, hm, one_mul]
    rfl
  rw [hAFe] at hAerr
  have hreg : q ∈ S.edgeRegion_BAUGD j :=
    ⟨mem_ball.mpr hd, hη8, by linarith, by linarith⟩
  exact ⟨hD4.le, hreg, hAerr, hρ99⟩

include C in
/-- **The rim pair along the homotopy in pair form**: at a rim point of the trace, every
`y ∈ ℝ²` is `((1 − θ)dη_j + θ dg, (1 − θ)dt + θ dT)(v)` for some `v`. -/
theorem homotopy_face_pair_OWF (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (j : S.EdgeIdx_BAUGD) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη41 : |S.edgeEta_BIF j.1 q| < 41 / 10 * Δ) (h39 : 19 / 5 * Δ < S.edgeHeightRaw q)
    (h41 : S.edgeHeightRaw q < 21 / 5 * Δ) (y : ℝ × ℝ) :
    ∃ v : TangentSpace (𝓡 3) q,
      (1 - θ) * mvfderiv (𝓡 3) (S.edgeEta_BIF j.1) q v + θ * mvfderiv (𝓡 3)
          (fun z : W.pieceInterior ⊤ => S.edgeRatio_BAUGD j (C.toChain.E z.val)) q v = y.1 ∧
        (1 - θ) * mvfderiv (𝓡 3)
          (fun z : W.pieceInterior ⊤ => S.edgeSmoothing_BAUGD z / S.rho z.val) q v +
          θ * mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => C.toChain.heightRatio z.val) q v =
          y.2 := by
  obtain ⟨hΛ, hΔ0, -, -, -, -, -, -, -, hΔ1, -, -⟩ := C.std
  obtain ⟨hD4, hreg, hAP, hρ99⟩ := C.homotopy_rim_region_OWF j hd hη41 h39 h41
  obtain ⟨Hd, hHd, hder0⟩ := C.stage_derivative_lt_BAUGD 2
  have hder : ∀ (p : W.Carrier) (v : TangentSpace W.model p),
      ‖mvfderiv W.model C.toChain.E p v - mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
        Hd * Real.sqrt (g.inner p v v) := hder0
  have hrj := S.rho_pos j.1
  have hρq := S.rho_pos q.val
  have hκ : 0 ≤ 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ :=
    mul_nonneg (by linarith [C.scale_edp01_BAUGD.1]) hΛ
  have hΛκ : Λ ≤ 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ := by
    have := mul_le_mul_of_nonneg_right (C.scale_edp01_BAUGD.1) hΛ
    linarith
  have hηle : |S.edgeEta_BIF j.1 q| ≤ 10 * Δ := by linarith
  have h1' : Δ / 10 ≤ S.edgeHeightRaw q := by linarith
  have h2' : S.edgeHeightRaw q ≤ 10 * Δ := by linarith
  have hsph : ∀ u : TangentSpace (𝓡 3) q, S.completion.metric.inner q u u = S.rho j.1 ^ 2 →
      Real.sqrt (S.completion.metric.inner q u u) = S.rho j.1 := fun u hu => by
    rw [hu, Real.sqrt_sq hrj.le]
  have hsg : ∀ u : TangentSpace (𝓡 3) q, S.completion.metric.inner q u u = S.rho j.1 ^ 2 →
      Real.sqrt (g.inner q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
        (mfderiv (𝓡 3) W.model Subtype.val q u)) = S.rho j.1 := fun u hu => by
    rw [S.inner_dval_BAUGD q hD4 u, hsph u hu]
  have hs := (C.scale_edp01_BAUGD.2 q.val).2.1
  have hS : |C.toChain.scale q.val / S.rho j.1 - S.rho q.val / S.rho j.1| ≤
      100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * (S.rho q.val / S.rho j.1) := by
    rw [← sub_div, abs_div, abs_of_pos hrj, div_le_iff₀ hrj]
    calc |C.toChain.scale q.val - S.rho q.val| ≤
          100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * S.rho q.val := hs
      _ = 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * (S.rho q.val / S.rho j.1) *
          S.rho j.1 := by field_simp
  have hB : |C.toChain.height q.val / S.rho j.1 - S.edgeSmoothing_BAUGD q / S.rho j.1| <
      c 2 * (S.rho q.val / S.rho j.1) := by
    rw [← sub_div, abs_div, abs_of_pos hrj, div_lt_iff₀ hrj]
    calc |C.toChain.height q.val - S.edgeSmoothing_BAUGD q| < c 2 * S.rho q.val := hAP
      _ = c 2 * (S.rho q.val / S.rho j.1) * S.rho j.1 := by field_simp
  have hnorm : S.edgeSmoothing_BAUGD q / S.rho j.1 / (S.rho q.val / S.rho j.1) =
      S.edgeHeightRaw q := by
    rw [S.edgeHeightRaw_eq_BAUGD]
    field_simp
  have ht0 : 0 ≤ S.edgeSmoothing_BAUGD q / S.rho j.1 / (S.rho q.val / S.rho j.1) := by
    rw [hnorm, S.edgeHeightRaw_eq_BAUGD]
    exact div_nonneg (S.edgeSmoothing_nonneg_BAUGD q) hρq.le
  have hco := S.edge_conorm_BAUGD hγc hγc1 hβc1 j hd hηle h1' h2'
  let dη : TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ := mvfderiv (𝓡 3) (S.edgeEta_BIF j.1) q
  let dg : TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ :=
    mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => S.edgeRatio_BAUGD j (C.toChain.E z.val)) q
  let dt : TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ :=
    mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => S.edgeSmoothing_BAUGD z / S.rho z.val) q
  let dT : TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ :=
    mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => C.toChain.heightRatio z.val) q
  have hpert := rim_pert_lt_half_OWF
    {u : TangentSpace (𝓡 3) q | S.completion.metric.inner q u u = S.rho j.1 ^ 2} dη
    (mvfderiv (𝓡 3) S.edgeSmoothing_BAUGD q : TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ)
    (mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => S.rho z.val) q : TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ)
    (mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => C.toChain.height z.val) q :
      TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ)
    (mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => C.toChain.scale z.val) q :
      TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ) dg dt dT
    hrj hρ99 hS hB ht0 (by rw [hnorm]; linarith) hΔ1 hκ hC hc
    (fun u => S.dt_quotient_BAUGD j hd hηle h1' h2' u)
    (fun u => C.dT_quotient_BAUGD q u)
    (fun u hu => by
      have h := C.abs_dscale_le_BAUGD q u
      rw [hsg u hu] at h
      exact h.trans_eq (by ring))
    (fun u hu => by
      have h := abs_drho_le_BAUGD (S := S) hΛ q u
      rw [hsg u hu] at h
      exact h.trans (by nlinarith [hrj]))
    (fun u hu => by
      have h := C.abs_dheight_sub_dsmoothing_BAUGD hΔ0 hder j hreg hD4 u
      rw [hsph u hu] at h
      exact h.trans_lt (mul_lt_mul_of_pos_right hHd hrj))
    (fun u hu => by
      have h := S.abs_dedgeSmoothing_le_BAUGD hε0 j hd hηle h1' h2' u
      rw [hsph u hu] at h
      exact h.trans_lt (mul_lt_mul_of_pos_right (by linarith) hrj))
    (fun u hu => by
      have h := C.abs_dedge_sub_deta_BAUGD hΔ0 hder j hreg hD4 u
      rw [hsph u hu] at h
      refine h.trans_lt ?_
      calc (S.rho j.1)⁻¹ * (Hd * S.rho j.1) = Hd := by field_simp
        _ < c 2 := hHd)
  have hsurj := homotopy_pair_surjective_of_conorm_OWF
    {u : TangentSpace (𝓡 3) q | S.completion.metric.inner q u u = S.rho j.1 ^ 2} dη dt dg dT
    ((1 - θ) • dη + θ • dg) ((1 - θ) • dt + θ • dT) hθ (fun v => rfl) (fun v => rfl) hco hpert
  obtain ⟨v, hv⟩ := hsurj y
  exact ⟨v, congrArg Prod.fst hv, congrArg Prod.snd hv⟩

/-- The normalized edge height `t` is continuous on `W°`. -/
theorem continuous_edgeHeightRaw_OWF (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε
    γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM) : Continuous S.edgeHeightRaw := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  exact S.family.continuous_edgeBHeight_BAUGA

/-- `H₀ = t` near a point with `t > 2Δ`. -/
theorem edgeH0_eventuallyEq_OWF (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε
    γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM) (hΔ0 : 0 < Δ) {q : W.pieceInterior ⊤}
    (hq : 2 * Δ < S.edgeHeightRaw q) :
    S.edgeH0_OWF =ᶠ[𝓝 q]
      (fun z : W.pieceInterior ⊤ => S.edgeSmoothing_BAUGD z / S.rho z.val) := by
  have ho : IsOpen (S.edgeHeightRaw ⁻¹' Ioi (2 * Δ)) :=
    isOpen_Ioi.preimage (continuous_edgeHeightRaw_OWF S)
  filter_upwards [ho.mem_nhds hq] with z hz
  exact edgeRowHeight_eq_self_EDP3 (F := S.edgeSmoothing_BAUGD) (ρ := fun x => S.rho x.val)
    hΔ0 (le_of_lt hz)

include C in
/-- **The pair `(h_θ, T_θ)` is a submersion on the rim of the trace** (see the module
docstring). -/
theorem homotopy_face_OWF (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (j : S.EdgeIdx_BAUGD) {a θ δ : ℝ} (ha : |a| < 81 / 20 * Δ) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ Δ / 10) {q : W.pieceInterior ⊤} (hq : q ∈ S.edgeSource_OWF j)
    (hfib : (1 - θ) * S.edgeEta_BIF j.1 q +
      θ * (S.edgeRatio_BAUGD j (C.toChain.E q.val) - a) = 0)
    (hrim : (1 - θ) * S.edgeH0_OWF q + θ * (C.toChain.heightRatio q.val - δ) = 4 * Δ) :
    Surjective (mfderiv (𝓡 3) 𝓘(ℝ, ℝ × ℝ) (fun z : W.pieceInterior ⊤ =>
      ((1 - θ) * S.edgeEta_BIF j.1 z + θ * (S.edgeRatio_BAUGD j (C.toChain.E z.val) - a),
        (1 - θ) * S.edgeH0_OWF z + θ * (C.toChain.heightRatio z.val - δ))) q) := by
  obtain ⟨hΛ, hΔ0, -, -, -, -, -, -, -, hΔ1, hLΛ, -⟩ := C.std
  have hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8 := by nlinarith
  have hb8 : b * (1000 * Δ) ≤ 1 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 1000 * Δ)).mp hb
    linarith
  obtain ⟨-, hηs, hHs, -, -⟩ := S.edge_buffer_OWF hΔ1 hμ hτ hlam hσc hb8 j
  have hYn := (S.isOpen_edgeSource_OWF j).mem_nhds hq
  have hηc : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (S.edgeEta_BIF j.1) q := hηs.contMDiffAt hYn
  have hHc : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ S.edgeH0_OWF q := hHs.contMDiffAt hYn
  have hg0 := (C.edgeAdjusted_contMDiff_OWF j) q
  have hgc : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun z : W.pieceInterior ⊤ =>
      S.edgeRatio_BAUGD j (C.toChain.E z.val) - a) q := hg0.sub contMDiffAt_const
  have hT0 := (C.heightRatio_interior_contMDiff_OWF) q
  have hTc : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun z : W.pieceInterior ⊤ =>
      C.toChain.heightRatio z.val - δ) q := hT0.sub contMDiffAt_const
  obtain ⟨hη41, -, hrimt⟩ := C.edge_trace_OWF hc hC j ha hθ hδ0 hδ hq hfib hrim.le
  obtain ⟨h39, h41⟩ := hrimt hrim
  have hdH := mvfderiv_congr_OWF (I := 𝓡 3) (edgeH0_eventuallyEq_OWF S hΔ0 (by linarith))
  refine surjective_mfderiv_pair_EFE ((contMDiffAt_const.mul hηc).add (contMDiffAt_const.mul hgc))
    ((contMDiffAt_const.mul hHc).add (contMDiffAt_const.mul hTc)) fun y => ?_
  obtain ⟨v, hv1, hv2⟩ := C.homotopy_face_pair_OWF hc hC hε0 hε hγc hγc1 hβc1 j hθ hq.1 hη41 h39
    h41 y
  refine ⟨v, ?_, ?_⟩
  · have e1 := mvfderiv_homotopy_scalar_EFE θ hηc hgc v
    beta_reduce at e1
    have e2 := mvfderiv_sub_const_EFE (I := 𝓡 3)
      (f := fun z : W.pieceInterior ⊤ => S.edgeRatio_BAUGD j (C.toChain.E z.val))
      (hg0.mdifferentiableAt (by simp)) a v
    rw [e1, e2]
    exact hv1
  · have e1 := mvfderiv_homotopy_scalar_EFE θ hHc hTc v
    beta_reduce at e1
    have e2 := mvfderiv_sub_const_EFE (I := 𝓡 3)
      (f := fun z : W.pieceInterior ⊤ => C.toChain.heightRatio z.val)
      (hT0.mdifferentiableAt (by simp)) δ v
    rw [e1, e2, hdH]
    exact hv2

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
