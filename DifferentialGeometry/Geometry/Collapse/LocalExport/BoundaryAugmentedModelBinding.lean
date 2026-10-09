import DifferentialGeometry.Analysis.Calculus.Cutoff.BoundaryBlockModel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightTransport
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.SupportListsCollar
import DifferentialGeometry.Geometry.Fibration.RiemannianDerivativeTools
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedSupportSlot
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightSlimDifferential
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightEdgeDifferential

/-!
# BCG03 (BM) bound to the actual boundary block and to BCG02's clauses (lane BCG-8b, G13)

Blueprint 207B, BCG03 (`B:8960–9010`); external draft 61 §2.5, disposition D61-5. G12
(`Analysis/Calculus/Cutoff/BoundaryBlockModel.lean`) gives the augmented model
`Φ = boundaryModel_BCG8b (η_b(p_a)) R_a A (η_a(p_a))` with `‖DΦ‖ ≤ P_*`, `‖D²Φ‖ ≤ R_aP_*`. Here the
model is compared with the ACTUAL normalized block `R_a⁻¹F_b`, `F_b = P.block b` (the LC88 collar
block, `𝓑(η_b)` on the open collar band `e_b{2 < z < 98}`, zero outside), on `W°`:

* `mvfderiv_smul_block_BCG8b`: at a band point, `D(R⁻¹F_b)(u) = 𝓑'(η_b(x))(DU(u))`,
  `U = (η_b − c)/R` (the prefactor cancels; through `val : W° → W`, BCG-7's
  `mvfderiv_comp_val_BCG7`);
* `norm_sign_row_le_one_BCG8b`: a sign `a = ±1` is a row of norm `≤ 1`;
* `bcg03_model_errors_sign_BCG8b` (one point, one-dimensional reference, sign row): BCG02's value
  and differential clauses for the ONE sign `a` and `|Dη(u)| ≤ 2|u|` give
  `‖R⁻¹F_b(x) − Φ(η(x))‖ ≤ P_*θ` and
  `‖D(R⁻¹F_b)(u) − DΦ(η(x))(Dη(u))‖ ≤ 3P_*θ|u|_{R⁻²ĝ}`;
* `abs_mvfderiv_slim_coord_le_BCG8b`, `abs_mvfderiv_edge_coord_le_BCG8b`: the slim / edge reference
  coordinates have `|Dη(u)| ≤ (1 + σ)|u|_{ρ(j)⁻²g}` (their `(1 + σ)`-Lipschitz charts);
* `bcg03_model_errors_reference_BCG8b`: the same on the WHOLE reference domain `D = B(j, Cρ(j))`,
  `C ≤ .95L`, for a member `b ∈ J_∂` (G11's `boundarySupportList_BCG8b`; the band and
  `ρ(j) < 2r_∂ ≤ 1` come from G11's `bcg03_mem_boundarySupportList_BCG8b` through T3B's
  consumer-domain clause `d_g = d_ĝ` on `B(j, K₀ρ(j))`, `C ≤ K₀`);
* consumer `bcg03_model_errors_slim_edge_BCG8b`: the instance at the slim and ACTIVE edge
  (`F.edgeB`) references of `F : LocalPacketsOnB` with BCG-8 G10's slim / edge clause shapes.

The circle reference (two-dimensional coordinate, unit row `A_b : ℝ² → ℝ¹`) uses the same G12
kernels with `A = (proj 0) ∘ A_b`; its binding is the next group.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Riemannian
  GC.MetricGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **The actual normalized block differential at a band point.** At a point `x` of `W°` whose
image lies in the collar band `e_b{2 < z < 98}` (an open set on which `F_b = 𝓑(η_b)`):
`D(R⁻¹ F_b)(u) = 𝓑'(η_b(x))(DU(u))`, `U = (η_b − c)/R`. -/
theorem mvfderiv_smul_block_BCG8b (W : CompactCarrier.{0})
    (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}
    (P : BoundaryCollarPacket W g K A w₀ ε) (b : Fin P.cusp.count) (c R : ℝ)
    (x : W.pieceInterior ⊤)
    (hx : ∃ q ∈ cuspDomain, (P.cusp.collar b).toFun q = x.val ∧ 2 < q.2.val 0 ∧ q.2.val 0 < 98)
    (u : TangentSpace 𝓘(ℝ, E3) x) :
    mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => R⁻¹ • P.block b y) x u =
      fderiv ℝ boundaryBlock (P.height b x)
        (mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => (P.height b y - c) / R) x u) := by
  obtain ⟨q, -, hqx, hq2, hq98⟩ := hx
  have hO : IsOpen ((P.cusp.collar b).toFun ''
      {q : CuspHalfSpace | 2 < q.2.val 0 ∧ q.2.val 0 < 98}) :=
    (P.cusp.collar b).isOpen_image ((isOpen_lt continuous_const continuous_cusp_height).inter
      (isOpen_lt continuous_cusp_height continuous_const))
      fun q hq => cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hq.2.le
  have hmem : x.val ∈ (P.cusp.collar b).toFun ''
      {q : CuspHalfSpace | 2 < q.2.val 0 ∧ q.2.val 0 < 98} := ⟨q, ⟨hq2, hq98⟩, hqx⟩
  have hev : P.block b =ᶠ[𝓝 x.val] fun y => boundaryBlock (P.height b y) := by
    filter_upwards [hO.mem_nhds hmem] with y hy
    exact indicator_of_mem hy _
  have hηd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (P.height b) x.val :=
    (P.contMDiff_height b _).mdifferentiableAt (by simp)
  have hBd : MDifferentiableAt W.model 𝓘(ℝ, ℝ × ℝ) (P.block b) x.val :=
    (P.contMDiff_block b _).mdifferentiableAt (by simp)
  set w := mfderiv (𝓡 3) W.model Subtype.val x u with hw
  have hblock : mvfderiv W.model (P.block b) x.val w =
      fderiv ℝ boundaryBlock (P.height b x) (mvfderiv W.model (P.height b) x.val w) := by
    rw [BoundaryCollarPacket.mvfderiv_congr_of_eventuallyEq hev w]
    exact mvfderiv_comp_hasFDerivAt hηd (differentiable_boundaryBlock_BCG8b _).hasFDerivAt w
  have hBdv : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ × ℝ)
      (fun y : W.pieceInterior ⊤ => P.block b y) x :=
    hBd.comp x (mdifferentiableAt_val_BCG7 W x)
  have hηdv : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ)
      (fun y : W.pieceInterior ⊤ => P.height b y) x :=
    hηd.comp x (mdifferentiableAt_val_BCG7 W x)
  have hL : mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => R⁻¹ • P.block b y) x u =
      R⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => P.block b y) x u := by
    have h := mvfderiv_clm_comp hBdv (R⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)) u
    simpa using h
  have hRr : mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => (P.height b y - c) / R) x u =
      R⁻¹ * mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => P.height b y) x u := by
    have hφ : HasDerivAt (fun t : ℝ => (t - c) / R) R⁻¹ (P.height b x) := by
      have := ((hasDerivAt_id (P.height b x)).sub_const c).div_const R
      simpa [div_eq_mul_inv] using this
    exact mvfderiv_comp_hasDerivAt hηdv hφ u
  rw [hL, hRr, mvfderiv_comp_val_BCG7 W (P.block b) x hBd u,
    mvfderiv_comp_val_BCG7 W (P.height b) x hηd u, ← hw, hblock, ← smul_eq_mul, map_smul]

/-- A sign is a row of norm `≤ 1`. -/
theorem norm_sign_row_le_one_BCG8b {a : ℝ} (ha : a = 1 ∨ a = -1) :
    ‖a • ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 := by
  have ha1 : ‖a‖ = 1 := by rcases ha with rfl | rfl <;> norm_num
  rw [norm_smul, ha1, one_mul]
  exact ContinuousLinearMap.norm_id_le

/-- **(BM) at one point of a one-dimensional reference (edge or slim, sign row `a`).** At a point
`x` of `W°` in the collar band `e_b{2 < z < 98}`, with `0 < ρ(j) ≤ 1`, BCG02's value and
differential
clauses for the ONE sign `a` at `x`, and the reference bound `|Dη(u)| ≤ 2|u|_{ρ(j)⁻²ĝ}`: the
ACTUAL normalized block `ρ(j)⁻¹F_b` and the model `Φ = boundaryModel (η_b(j)) ρ(j) a (η(j))` satisfy
`‖ρ(j)⁻¹F_b(x) − Φ(η(x))‖ ≤ P_*θ` and `‖D(ρ(j)⁻¹F_b)(u) − DΦ(η(x))(Dη(u))‖ ≤ 3P_*θ|u|`. -/
theorem bcg03_model_errors_sign_BCG8b (W : CompactCarrier.{0})
    (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}
    (P : BoundaryCollarPacket W g K A w₀ ε) (b : Fin P.cusp.count)
    (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)) (ρ : W.Carrier → ℝ)
    (hρ : ∀ p, 0 < ρ p) {Pst : ℝ} (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ Pst)
    (hP2 : ∀ t, ‖fderiv ℝ (fderiv ℝ boundaryBlock) t‖ ≤ Pst) (j x : W.pieceInterior ⊤)
    (hρ1 : ρ j ≤ 1)
    (hx : ∃ q ∈ cuspDomain, (P.cusp.collar b).toFun q = x.val ∧ 2 < q.2.val 0 ∧ q.2.val 0 < 98)
    (η : W.pieceInterior ⊤ → ℝ) {a θ : ℝ} (ha : a = 1 ∨ a = -1)
    (hval : |(P.height b x - P.height b j) / ρ j - a * (η x - η j)| < θ)
    (hdiff : ∃ θ' < θ, ∀ u : TangentSpace 𝓘(ℝ, E3) x,
      |mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => (P.height b y - P.height b j) / ρ j) x u -
        a * mvfderiv 𝓘(ℝ, E3) η x u| ≤
        θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner
          x u u))
    (hη : ∀ u : TangentSpace 𝓘(ℝ, E3) x, |mvfderiv 𝓘(ℝ, E3) η x u| ≤
      2 * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner x u u)) :
    ‖(ρ j)⁻¹ • P.block b x - boundaryModel_BCG8b (P.height b j) (ρ j)
        (a • ContinuousLinearMap.id ℝ ℝ) (η j) (η x)‖ ≤ Pst * θ ∧
    ∀ u : TangentSpace 𝓘(ℝ, E3) x,
      ‖mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => (ρ j)⁻¹ • P.block b y) x u -
        fderiv ℝ (boundaryModel_BCG8b (P.height b j) (ρ j) (a • ContinuousLinearMap.id ℝ ℝ)
          (η j)) (η x) (mvfderiv 𝓘(ℝ, E3) η x u)‖ ≤
        3 * Pst * θ * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
          (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner x u u) := by
  have hρj := hρ j
  have hA := norm_sign_row_le_one_BCG8b ha
  have hrow : ∀ r : ℝ, (a • ContinuousLinearMap.id ℝ ℝ) r = a * r := fun r => by simp
  have hval' : |(P.height b x - P.height b j) / ρ j -
      (a • ContinuousLinearMap.id ℝ ℝ) (η x - η j)| < θ := by rw [hrow]; exact hval
  have hblock : P.block b x = boundaryBlock (P.height b x) := by
    obtain ⟨q, -, hqx, hq2, hq98⟩ := hx
    have hmem : x.val ∈ (P.cusp.collar b).toFun ''
        {q : CuspHalfSpace | 2 < q.2.val 0 ∧ q.2.val 0 < 98} := ⟨q, ⟨hq2, hq98⟩, hqx⟩
    exact indicator_of_mem hmem _
  refine ⟨?_, fun u => ?_⟩
  · rw [hblock]
    exact boundaryModel_value_error_BCG8b hP _ hρj _ _ _ hval'
  · obtain ⟨θ', hθ', hθ'u⟩ := hdiff
    rw [mvfderiv_smul_block_BCG8b W g P b (P.height b j) (ρ j) x hx u]
    refine boundaryModel_differential_error_BCG8b hP hP2 _ hρj hρ1 hA _ hval' ?_ hθ'.le ?_
    · rw [hrow]; exact hθ'u u
    · rw [Real.norm_eq_abs]; exact hη u

section ChartBounds

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

/-- The slim reference coordinate has `|Dη(u)| ≤ (1 + σ_s)|u|_{ρ(j)⁻²g}` on `B(j, 10⁶Δρ(j))`. -/
theorem abs_mvfderiv_slim_coord_le_BCG8b {β₁ Δ σs : ℝ} {K : ℕ} {j : X}
    (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) (hσs : 0 ≤ σs) {x : X}
    (hx : dist x j < 10 ^ 6 * Δ * ρ j) (u : TangentSpace 𝓘(ℝ, E3) x) :
    |mvfderiv 𝓘(ℝ, E3) c.coord_BCG2 x u| ≤ (1 + σs) *
      Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g).inner x u u) := by
  obtain ⟨-, hlipc, hdiffc, -⟩ := c.split_test_BCG8 hσs
  have hxb : x ∈ ball j (10 ^ 6 * Δ * ρ j) := mem_ball.mpr hx
  have h := norm_mvfderiv_le_of_lipschitz_rescale_BCG7 g hmetric isOpen_ball hxb
    (hdiffc x hx) (L := 1 + σs) (by linarith only [hσs]) (hρ j)
    (fun y' _ z' _ => by rw [Real.norm_eq_abs]; exact hlipc y' z') u
  rwa [Real.norm_eq_abs] at h

/-- The edge reference coordinate has `|Dη(u)| ≤ (1 + σ_c)|u|_{ρ(j)⁻²g}` on `B(j, 100Δρ(j))`. -/
theorem abs_mvfderiv_edge_coord_le_BCG8b {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}
    {U₁ U₂ : Set X} (E : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) {j : X}
    (hj : j ∈ E.centres) (hσc : 0 ≤ σc) {x : X} (hx : dist x j < 100 * Δ * ρ j)
    (u : TangentSpace 𝓘(ℝ, E3) x) :
    |mvfderiv 𝓘(ℝ, E3) (E.coord_BCG1 j hj) x u| ≤ (1 + σc) *
      Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g).inner x u u) := by
  obtain ⟨Y, mY, q, f, -, -, hlipc, hdiffc, -⟩ := E.exists_split_test_BCG7 hj hσc
  have hxb : x ∈ ball j (100 * Δ * ρ j) := mem_ball.mpr hx
  have h := norm_mvfderiv_le_of_lipschitz_rescale_BCG7 g hmetric isOpen_ball hxb
    (hdiffc x hx) (L := 1 + σc) (by linarith only [hσc]) (hρ j)
    (fun y' _ z' _ => by rw [Real.norm_eq_abs]; exact hlipc y' z') u
  rwa [Real.norm_eq_abs] at h

end ChartBounds

/-- **(BM) on the whole reference domain of a one-dimensional reference.** On the LC88 data
(nonproduct case, the hypotheses of `boundarySupportList_subsingleton_BCG8b`, `1 ≤ Δ`), for a
reference centre `j` of `W°` with `D = B(j, Cρ(j))`, `C ≤ .95L`, on which `d_ĝ = d_g` (T3B's
consumer-domain clause with `C ≤ K₀`), a member `b ∈ J_∂` and BCG02's clauses on `D` for ONE sign
`a` with a reference coordinate `η` of derivative `≤ 2|u|` on `D`: at EVERY `x ∈ D` the actual
normalized block and the model satisfy the value bound `P_*θ` and the differential bound
`3P_*θ|u|`. -/
theorem bcg03_model_errors_reference_BCG8b (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ εB : ℝ}
    (P : BoundaryCollarPacket W g K A w₀ εB) (hεB : εB ≤ 1 / 4) (ρ : W.Carrier → ℝ)
    (hρ : ∀ p, 0 < ρ p) {Λ Δ β₁ C K₀ : ℝ} (hΛ : 0 < Λ) (hΔ : 1 ≤ Δ) (hβ₁ : 0 < β₁)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hcol : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β₁ ^ 3 / 2000)
    (hΛΔ : 100 * Δ * Λ ≤ 1 / 1000000) (hreq : β₁ ^ 3 * (1000000 * Δ) < 1)
    (hC : C ≤ 95 / 100 * (1000000 * Δ)) (hCK : C ≤ K₀) {Pst : ℝ}
    (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ Pst)
    (hP2 : ∀ t, ‖fderiv ℝ (fderiv ℝ boundaryBlock) t‖ ≤ Pst)
    (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)) :
    letI := inducedMetricSpace ĝ
    ∀ (j : W.pieceInterior ⊤),
    (∀ y ∈ Metric.ball j (K₀ * ρ j), ∀ z ∈ Metric.ball j (K₀ * ρ j),
      riemannianEDistOf g y.val z.val = edist y z) →
    ∀ (b : Fin P.cusp.count), b ∈ P.boundarySupportList_BCG8b j.val (C * ρ j) →
    ∀ (η : W.pieceInterior ⊤ → ℝ) (a θ : ℝ), (a = 1 ∨ a = -1) →
    (∀ y : W.pieceInterior ⊤, dist y j < C * ρ j →
      |(P.height b y - P.height b j) / ρ j - a * (η y - η j)| < θ) →
    (∀ x : W.pieceInterior ⊤, dist x j < C * ρ j → ∃ θ' < θ, ∀ u : TangentSpace 𝓘(ℝ, E3) x,
      |mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => (P.height b y - P.height b j) / ρ j) x u -
        a * mvfderiv 𝓘(ℝ, E3) η x u| ≤
        θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner
          x u u)) →
    (∀ x : W.pieceInterior ⊤, dist x j < C * ρ j → ∀ u : TangentSpace 𝓘(ℝ, E3) x,
      |mvfderiv 𝓘(ℝ, E3) η x u| ≤
        2 * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner
          x u u)) →
    ∀ x : W.pieceInterior ⊤, dist x j < C * ρ j →
      ‖(ρ j)⁻¹ • P.block b x - boundaryModel_BCG8b (P.height b j) (ρ j)
          (a • ContinuousLinearMap.id ℝ ℝ) (η j) (η x)‖ ≤ Pst * θ ∧
      ∀ u : TangentSpace 𝓘(ℝ, E3) x,
        ‖mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => (ρ j)⁻¹ • P.block b y) x u -
          fderiv ℝ (boundaryModel_BCG8b (P.height b j) (ρ j) (a • ContinuousLinearMap.id ℝ ℝ)
            (η j)) (η x) (mvfderiv 𝓘(ℝ, E3) η x u)‖ ≤
          3 * Pst * θ * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner x u u) := by
  intro j hcons b hb η a θ ha hval hdiff hη x hx
  let instM_BCG8b : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  have hΔ0 : 0 < Δ := lt_of_lt_of_le one_pos hΔ
  have hρj := hρ j
  obtain ⟨hρp, hband, -⟩ := P.bcg03_mem_boundarySupportList_BCG8b hεB hρ hΛ hΔ0 hβ₁ hlip hcol hΛΔ
    hreq hC (Empty.elim : Empty → W.Carrier) (Empty.elim : Empty → ℝ) (fun k => k.elim) hb
  -- `ρ(j) ≤ 1`
  have hρ1 : ρ j ≤ 1 := by
    have h1 : β₁ ^ 3 < 1 := by nlinarith only [hreq, hΔ, pow_pos hβ₁ 3]
    have h2 : ρ j < β₁ ^ 3 / 500 := hρp
    linarith only [h1, h2]
  -- the band at `x`
  have hxg : x.val ∈ riemannianBallOf g j.val (C * ρ j) := by
    have hCρ : 0 < C * ρ j := lt_of_le_of_lt dist_nonneg hx
    have hK₀ρ : C * ρ j ≤ K₀ * ρ j := mul_le_mul_of_nonneg_right hCK hρj.le
    have hjb : j ∈ Metric.ball j (K₀ * ρ j) := Metric.mem_ball_self (lt_of_lt_of_le hCρ hK₀ρ)
    have hxb : x ∈ Metric.ball j (K₀ * ρ j) := Metric.mem_ball.mpr (lt_of_lt_of_le hx hK₀ρ)
    change riemannianEDistOf g j.val x.val < ENNReal.ofReal (C * ρ j)
    rw [hcons j hjb x hxb, edist_dist, dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff hCρ).mpr hx
  obtain ⟨q, hq, hqx, hq19, hq91, -, -⟩ := hband x.val hxg
  exact bcg03_model_errors_sign_BCG8b W g P b ĝ ρ hρ hP hP2 j x hρ1
    ⟨q, hq, hqx, by linarith only [hq19], by linarith only [hq91]⟩ η ha (hval x hx) (hdiff x hx)
    (hη x hx)

/-- **Consumer: (BM) at the slim and ACTIVE edge references of a boundary family.** For
`F : LocalPacketsOnB` on `(W°, d_ĝ, ρ)` with `σ_s, σ_c ≤ 1` and the LC88 data of T3B's tail: at a
slim
centre (`D = B(j, 950000Δρ(j))`, reference coordinate of `F.slim.centre j`) or an `F.edgeB` centre
(`D = B(j, 20Δρ(j))`, reference coordinate `F.edgeB.coord_BCG1 j`), for every `b ∈ J_∂` and BCG02's
clauses on `D` with ONE sign (BCG-8 G10's slim / edge clause shapes), the actual normalized block
and the augmented model have value error `≤ P_*θ` and differential error `≤ 3P_*θ|u|` on `D`. -/
theorem bcg03_model_errors_slim_edge_BCG8b (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ εB : ℝ}
    (P : BoundaryCollarPacket W g K A w₀ εB) (hεB : εB ≤ 1 / 4) (ρ : W.Carrier → ℝ)
    (hρ : ∀ p, 0 < ρ p) {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {Kf : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs K₀ : ℝ} (hΛ : 0 < Λ) (hΔ : 1 ≤ Δ)
    (hβ₁ : 0 < β 1)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hcol : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000)
    (hΛΔ : 100 * Δ * Λ ≤ 1 / 1000000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1)
    (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1) (hσc : 0 ≤ σc) (hσc1 : σc ≤ 1) (hK₀ : 950000 * Δ ≤ K₀)
    {Pst : ℝ} (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ Pst)
    (hP2 : ∀ t, ‖fderiv ℝ (fderiv ℝ boundaryBlock) t‖ ≤ Pst)
    (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)) :
    letI := inducedMetricSpace ĝ
    ∀ (_ : CompleteSpace (W.pieceInterior ⊤)) (U₁ U₂ Ue₁ Ue₂ : Set (W.pieceInterior ⊤))
      (F : LocalPacketsOnB (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
          (fun x => hρ x) Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂),
    (∀ (j : W.pieceInterior ⊤) (hj : j ∈ F.slim.centres),
      (∀ y ∈ Metric.ball j (K₀ * ρ j), ∀ z ∈ Metric.ball j (K₀ * ρ j),
        riemannianEDistOf g y.val z.val = edist y z) →
      ∀ bb ∈ P.boundarySupportList_BCG8b j.val (950000 * Δ * ρ j),
      ∀ a θ : ℝ, (a = 1 ∨ a = -1) →
      (∀ y : W.pieceInterior ⊤, dist y j < 950000 * Δ * ρ j →
        |(P.height bb y - P.height bb j) / ρ j -
          a * ((F.slim.centre j hj).coord_BCG2 y - (F.slim.centre j hj).coord_BCG2 j)| < θ) →
      (∀ x : W.pieceInterior ⊤, dist x j < 950000 * Δ * ρ j → ∃ θ' < θ,
        ∀ u : TangentSpace 𝓘(ℝ, E3) x,
        |mvfderiv 𝓘(ℝ, E3)
            (fun y : W.pieceInterior ⊤ => (P.height bb y - P.height bb j) / ρ j) x u -
          a * mvfderiv 𝓘(ℝ, E3) (F.slim.centre j hj).coord_BCG2 x u| ≤
          θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner
            x u u)) →
      ∀ x : W.pieceInterior ⊤, dist x j < 950000 * Δ * ρ j →
        ‖(ρ j)⁻¹ • P.block bb x - boundaryModel_BCG8b (P.height bb j) (ρ j)
            (a • ContinuousLinearMap.id ℝ ℝ) ((F.slim.centre j hj).coord_BCG2 j)
            ((F.slim.centre j hj).coord_BCG2 x)‖ ≤ Pst * θ ∧
        ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          ‖mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => (ρ j)⁻¹ • P.block bb y) x u -
            fderiv ℝ (boundaryModel_BCG8b (P.height bb j) (ρ j) (a • ContinuousLinearMap.id ℝ ℝ)
              ((F.slim.centre j hj).coord_BCG2 j)) ((F.slim.centre j hj).coord_BCG2 x)
              (mvfderiv 𝓘(ℝ, E3) (F.slim.centre j hj).coord_BCG2 x u)‖ ≤
            3 * Pst * θ * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner x u u)) ∧
    ∀ (j : W.pieceInterior ⊤) (hj : j ∈ F.edgeB.centres),
      (∀ y ∈ Metric.ball j (K₀ * ρ j), ∀ z ∈ Metric.ball j (K₀ * ρ j),
        riemannianEDistOf g y.val z.val = edist y z) →
      ∀ bb ∈ P.boundarySupportList_BCG8b j.val (20 * Δ * ρ j),
      ∀ a θ : ℝ, (a = 1 ∨ a = -1) →
      (∀ y : W.pieceInterior ⊤, dist y j < 20 * Δ * ρ j →
        |(P.height bb y - P.height bb j) / ρ j -
          a * (F.edgeB.coord_BCG1 j hj y - F.edgeB.coord_BCG1 j hj j)| < θ) →
      (∀ x : W.pieceInterior ⊤, dist x j < 20 * Δ * ρ j → ∃ θ' < θ,
        ∀ u : TangentSpace 𝓘(ℝ, E3) x,
        |mvfderiv 𝓘(ℝ, E3)
            (fun y : W.pieceInterior ⊤ => (P.height bb y - P.height bb j) / ρ j) x u -
          a * mvfderiv 𝓘(ℝ, E3) (F.edgeB.coord_BCG1 j hj) x u| ≤
          θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner
            x u u)) →
      ∀ x : W.pieceInterior ⊤, dist x j < 20 * Δ * ρ j →
        ‖(ρ j)⁻¹ • P.block bb x - boundaryModel_BCG8b (P.height bb j) (ρ j)
            (a • ContinuousLinearMap.id ℝ ℝ) (F.edgeB.coord_BCG1 j hj j)
            (F.edgeB.coord_BCG1 j hj x)‖ ≤ Pst * θ ∧
        ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          ‖mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => (ρ j)⁻¹ • P.block bb y) x u -
            fderiv ℝ (boundaryModel_BCG8b (P.height bb j) (ρ j) (a • ContinuousLinearMap.id ℝ ℝ)
              (F.edgeB.coord_BCG1 j hj j)) (F.edgeB.coord_BCG1 j hj x)
              (mvfderiv 𝓘(ℝ, E3) (F.edgeB.coord_BCG1 j hj) x u)‖ ≤
            3 * Pst * θ * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner x u u) := by
  intro _ U₁ U₂ Ue₁ Ue₂ F
  let instM_BCG8b : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  have hΔ0 : 0 < Δ := lt_of_lt_of_le one_pos hΔ
  refine ⟨fun j hj hcons bb hbb a θ ha hval hdiff => ?_,
    fun j hj hcons bb hbb a θ ha hval hdiff => ?_⟩
  · refine bcg03_model_errors_reference_BCG8b W g P hεB ρ hρ hΛ hΔ hβ₁ hlip hcol hΛΔ hreq
      (C := 950000 * Δ) (by linarith only [hΔ]) hK₀ hP hP2 ĝ j hcons bb hbb _ a θ ha hval hdiff
      (fun x hx u => ?_)
    have hx' : dist x j < 10 ^ 6 * Δ * ρ j := by
      have h1 : 950000 * Δ * ρ j ≤ 10 ^ 6 * Δ * ρ j := by nlinarith only [hΔ0, hρ j]
      linarith only [hx, h1]
    have h := abs_mvfderiv_slim_coord_le_BCG8b (F.slim.centre j hj) hσs hx' u
    have hN := Real.sqrt_nonneg
      ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner x u u)
    nlinarith only [h, hN, hσs1]
  · refine bcg03_model_errors_reference_BCG8b W g P hεB ρ hρ hΛ hΔ hβ₁ hlip hcol hΛΔ hreq
      (C := 20 * Δ) (by linarith only [hΔ]) (by linarith only [hK₀, hΔ]) hP hP2 ĝ j hcons bb hbb
      _ a θ ha hval hdiff (fun x hx u => ?_)
    have hx' : dist x j < 100 * Δ * ρ j := by
      have h1 : 20 * Δ * ρ j ≤ 100 * Δ * ρ j := by nlinarith only [hΔ0, hρ j]
      linarith only [hx, h1]
    have h := abs_mvfderiv_edge_coord_le_BCG8b F.edgeB hj hσc hx' u
    have hN := Real.sqrt_nonneg
      ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner x u u)
    nlinarith only [h, hN, hσc1]

end DifferentialGeometry.Geometry.Collapse
