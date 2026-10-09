import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedModelBinding

/-!
# BCG03 (BM) at the circle references (lane BCG-8b, G14)

Blueprint 207B, BCG03 (`B:8960–9010`); external draft 61 §2.5, disposition D61-5. G13 bound the
augmented model of G12 to the actual normalized block `R_a⁻¹F_b` at the slim and edge references
(one-dimensional coordinates, sign rows). At a circle reference the coordinate `η_a` is `ℝ²`-valued
and BCG02 (BCG-7 G6, BCG-8 G10) supplies ONE coisometry `A_b : ℝ² → ℝ¹`; the row of (BA) is
`A = proj₀ ∘ A_b`.

* `norm_mvfderiv_circle_coord_le_BCG8b`: the circle coordinate has `‖Dη(u)‖ ≤ (1 + γ)|u|_{ρ(j)⁻²g}`
  on `B(j, 200ρ(j))` (the adapted packet's `(1 + γ)`-Lipschitz bound on the normalized ball
  `B(j, 200)`; differentiable there as a chart coordinate);
* `norm_circleRow_le_one_BCG8b`: `‖proj₀ ∘ A_b‖ ≤ 1` for a coisometry;
* `bcg03_model_errors_row_BCG8b`: G13's one-point step for a coordinate in any normed space and any
  row `‖A‖ ≤ 1` (value `≤ P_*θ`, differential `≤ 3P_*θ|u|`);
* consumer `bcg03_model_errors_circle_BCG8b`: the circle references of `F : LocalPacketsOn`
  (`D = B(j, 10ρ(j))`, `0 ≤ γ ≤ 1`, `b ∈ J_∂`, T3B's consumer-domain clause), with BCG-8 G10's
  circle
  clause shape as input: value `≤ P_*θ` and differential `≤ 3P_*θ|u|` on all of `D`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Riemannian
  GC.MetricGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section ChartBound

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

/-- The circle reference coordinate has `‖Dη(u)‖ ≤ (1 + γ)|u|_{ρ(j)⁻²g}` on `B(j, 200ρ(j))` (the
circle adapted packet's `(1 + γ)`-Lipschitz bound on the normalized ball `B(j, 200)`). -/
theorem norm_mvfderiv_circle_coord_le_BCG8b {β : ℕ → ℝ} {γ : ℝ} {U₁ U₂ : Set X}
    (C : CircleFamilyOn 𝓘(ℝ, E3) X ρ hρ β U₁ U₂) {j : X} (hj : j ∈ C.centres)
    (ad : CircleAdaptedCentreOn X g hmetric ρ hρ β γ U₁ U₂ C j hj) (hγ : 0 ≤ γ) {x : X}
    (hx : dist x j < 200 * ρ j) (u : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (let c := C.chart j hj;
        letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord) x u‖ ≤
      (1 + γ) *
        Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g).inner x u u) := by
  have hρj := hρ j
  have hcc0 := C.chart_center j hj
  have hlip0 := ad.lipschitz
  have hlip : ∀ y ∈ ball j (200 * ρ j), ∀ z ∈ ball j (200 * ρ j),
      ‖(let c := C.chart j hj; letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord) y -
        (let c := C.chart j hj; letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord) z‖ ≤
        (1 + γ) * ((ρ j)⁻¹ * dist y z) := by
    intro y hy z hz
    have hya : (ρ j)⁻¹ * dist y j < 200 := by
      rw [inv_mul_lt_iff₀ hρj]; linarith only [mem_ball.mp hy]
    have hza : (ρ j)⁻¹ * dist z j < 200 := by
      rw [inv_mul_lt_iff₀ hρj]; linarith only [mem_ball.mp hz]
    let c := C.chart j hj
    let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    have hcc : c.center = j := hcc0
    have hl : LipschitzOnWith (Real.toNNReal (1 + γ)) c.coord (ball j 200) := hlip0
    have hyB : y ∈ ball j 200 := hya
    have hzB : z ∈ ball j 200 := hza
    have hd := hl.dist_le_mul y hyB z hzB
    rw [Real.coe_toNNReal _ (by linarith only [hγ]), dist_eq_norm] at hd
    exact hd
  have hdiff : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²)
      (let c := C.chart j hj; letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord) x := by
    have hxa : (ρ j)⁻¹ * dist x j < 200 := by
      rw [inv_mul_lt_iff₀ hρj]; linarith only [hx]
    let c := C.chart j hj
    let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    have hcc : c.center = j := hcc0
    have hsm : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ c.coord (ball c.center 200) :=
      c.contMDiffOn_coord
    have hxB : x ∈ ball c.center 200 := by rw [hcc]; exact hxa
    exact (hsm.contMDiffAt (isOpen_ball.mem_nhds hxB)).mdifferentiableAt (by simp)
  exact norm_mvfderiv_le_of_lipschitz_rescale_BCG7 g hmetric isOpen_ball (mem_ball.mpr hx) hdiff
    (L := 1 + γ) (by linarith only [hγ]) hρj hlip u

end ChartBound

/-- The circle row `A = proj₀ ∘ A_b : ℝ² → ℝ` of a coisometry `A_b : ℝ² → ℝ¹` has norm `≤ 1`. -/
theorem norm_circleRow_le_one_BCG8b (Ab : ℝ² →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (hAb : Ab.comp (ContinuousLinearMap.adjoint Ab) = ContinuousLinearMap.id ℝ _) :
    ‖(EuclideanSpace.proj (0 : Fin 1)).comp Ab‖ ≤ 1 := by
  have hp : ‖(EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul]
    exact PiLp.norm_apply_le v 0
  calc ‖(EuclideanSpace.proj (0 : Fin 1)).comp Ab‖
      ≤ ‖(EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)‖ * ‖Ab‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul hp (ContinuousLinearMap.norm_le_one_of_comp_adjoint_BCG1 Ab hAb)
        (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **(BM) at one point for a reference coordinate in any normed space** (row `A`, `‖A‖ ≤ 1`). At a
point `x` of `W°` in the collar band, with `0 < ρ(j) ≤ 1`, the value clause
`|U(x) − A(η(x) − η(j))| < θ`, the differential clause `|DU(u) − A(Dη(u))| ≤ θ'|u|`, `θ' < θ`, and
`‖Dη(u)‖ ≤ 2|u|`: the actual normalized block and `Φ = boundaryModel (η_b(j)) ρ(j) A (η(j))` have
value error `≤ P_*θ` and differential error `≤ 3P_*θ|u|`. -/
theorem bcg03_model_errors_row_BCG8b {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : CompactCarrier.{0}) (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ}
    {A : ℝ → ℝ} {w₀ ε : ℝ} (P : BoundaryCollarPacket W g K A w₀ ε) (b : Fin P.cusp.count)
    (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)) (ρ : W.Carrier → ℝ)
    (hρ : ∀ p, 0 < ρ p) {Pst : ℝ} (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ Pst)
    (hP2 : ∀ t, ‖fderiv ℝ (fderiv ℝ boundaryBlock) t‖ ≤ Pst) (j x : W.pieceInterior ⊤)
    (hρ1 : ρ j ≤ 1)
    (hx : ∃ q ∈ cuspDomain, (P.cusp.collar b).toFun q = x.val ∧ 2 < q.2.val 0 ∧ q.2.val 0 < 98)
    (η : W.pieceInterior ⊤ → E) {Ar : E →L[ℝ] ℝ} (hA : ‖Ar‖ ≤ 1) {θ : ℝ}
    (hval : |(P.height b x - P.height b j) / ρ j - Ar (η x - η j)| < θ)
    (hdiff : ∃ θ' < θ, ∀ u : TangentSpace 𝓘(ℝ, E3) x,
      |mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => (P.height b y - P.height b j) / ρ j) x u -
        Ar (mvfderiv 𝓘(ℝ, E3) η x u)| ≤
        θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner
          x u u))
    (hη : ∀ u : TangentSpace 𝓘(ℝ, E3) x, ‖mvfderiv 𝓘(ℝ, E3) η x u‖ ≤
      2 * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner
        x u u)) :
    ‖(ρ j)⁻¹ • P.block b x - boundaryModel_BCG8b (P.height b j) (ρ j) Ar (η j) (η x)‖ ≤
      Pst * θ ∧
    ∀ u : TangentSpace 𝓘(ℝ, E3) x,
      ‖mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => (ρ j)⁻¹ • P.block b y) x u -
        fderiv ℝ (boundaryModel_BCG8b (P.height b j) (ρ j) Ar (η j)) (η x)
          (mvfderiv 𝓘(ℝ, E3) η x u)‖ ≤
        3 * Pst * θ * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
          (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner x u u) := by
  have hρj := hρ j
  have hblock : P.block b x = boundaryBlock (P.height b x) := by
    obtain ⟨q, -, hqx, hq2, hq98⟩ := hx
    have hmem : x.val ∈ (P.cusp.collar b).toFun ''
        {q : CuspHalfSpace | 2 < q.2.val 0 ∧ q.2.val 0 < 98} := ⟨q, ⟨hq2, hq98⟩, hqx⟩
    exact indicator_of_mem hmem _
  refine ⟨?_, fun u => ?_⟩
  · rw [hblock]
    exact boundaryModel_value_error_BCG8b hP _ hρj _ _ _ hval
  · obtain ⟨θ', hθ', hθ'u⟩ := hdiff
    rw [mvfderiv_smul_block_BCG8b W g P b (P.height b j) (ρ j) x hx u]
    exact boundaryModel_differential_error_BCG8b hP hP2 _ hρj hρ1 hA _ hval (hθ'u u) hθ'.le
      (hη u)

/-- **Consumer: (BM) at the circle references of a boundary family.** For `F : LocalPacketsOn`
on `(W°, d_ĝ, ρ)` with `0 ≤ γ ≤ 1` (the circle adapted packets' Lipschitz quality) and the LC88
data of T3B's tail (nonproduct, the hypotheses of `boundarySupportList_subsingleton_BCG8b`, `1 ≤
Δ`):
at a circle centre `j` (`D = B(j, 10ρ(j))`, `d_g = d_ĝ` on `B(j, K₀ρ(j))`, `10 ≤ K₀`), for every
`b ∈ J_∂` and BCG02's circle clauses on `D` with ONE coisometry `A_b : ℝ² → ℝ¹` (BCG-7 G6 / BCG-8
G10
shape), the actual normalized block and the model with the row `proj₀ ∘ A_b` have value error
`≤ P_*θ` and differential error `≤ 3P_*θ|u|` on `D`. -/
theorem bcg03_model_errors_circle_BCG8b (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ εB : ℝ}
    (P : BoundaryCollarPacket W g K A w₀ εB) (hεB : εB ≤ 1 / 4) (ρ : W.Carrier → ℝ)
    (hρ : ∀ p, 0 < ρ p) {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {Kf : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V K₀ : ℝ} (hΛ : 0 < Λ) (hΔ : 1 ≤ Δ)
    (hβ₁ : 0 < β 1)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hcol : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000)
    (hΛΔ : 100 * Δ * Λ ≤ 1 / 1000000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hK₀ : 10 ≤ K₀)
    {Pst : ℝ} (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ Pst)
    (hP2 : ∀ t, ‖fderiv ℝ (fderiv ℝ boundaryBlock) t‖ ≤ Pst)
    (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)) :
    letI := inducedMetricSpace ĝ
    ∀ (_ : CompleteSpace (W.pieceInterior ⊤)) (U₁ U₂ : Set (W.pieceInterior ⊤))
      (F : LocalPacketsOn (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
          (fun x => hρ x) Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V U₁ U₂)
      (j : W.pieceInterior ⊤) (hj : j ∈ F.circle.centres),
      (∀ y ∈ Metric.ball j (K₀ * ρ j), ∀ z ∈ Metric.ball j (K₀ * ρ j),
        riemannianEDistOf g y.val z.val = edist y z) →
      ∀ bb ∈ P.boundarySupportList_BCG8b j.val (10 * ρ j),
      ∀ (Ab : ℝ² →L[ℝ] EuclideanSpace ℝ (Fin 1)) (θ : ℝ),
        Ab.comp (ContinuousLinearMap.adjoint Ab) = ContinuousLinearMap.id ℝ _ →
      (∀ y : W.pieceInterior ⊤, dist y j < 10 * ρ j →
        ‖EuclideanSpace.single 0 ((P.height bb y - P.height bb j) / ρ j) -
          Ab ((let c := F.circle.chart j hj;
              letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord y) -
            (let c := F.circle.chart j hj;
              letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord j))‖
          < θ) →
      (∀ x : W.pieceInterior ⊤, dist x j < 10 * ρ j → ∃ θ' < θ,
        ∀ u : TangentSpace 𝓘(ℝ, E3) x,
        |mvfderiv 𝓘(ℝ, E3)
            (fun y : W.pieceInterior ⊤ => (P.height bb y - P.height bb j) / ρ j) x u -
          Ab (mvfderiv 𝓘(ℝ, E3) (let c := F.circle.chart j hj;
              letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord)
            x u) 0| ≤
          θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner
            x u u)) →
      ∀ x : W.pieceInterior ⊤, dist x j < 10 * ρ j →
        ‖(ρ j)⁻¹ • P.block bb x - boundaryModel_BCG8b (P.height bb j) (ρ j)
            ((EuclideanSpace.proj (0 : Fin 1)).comp Ab)
            (let c := F.circle.chart j hj;
              letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord j)
            (let c := F.circle.chart j hj;
              letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord x)‖ ≤
          Pst * θ ∧
        ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          ‖mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => (ρ j)⁻¹ • P.block bb y) x u -
            fderiv ℝ (boundaryModel_BCG8b (P.height bb j) (ρ j)
              ((EuclideanSpace.proj (0 : Fin 1)).comp Ab)
              (let c := F.circle.chart j hj;
                letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord j))
              (let c := F.circle.chart j hj;
                letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord x)
              (mvfderiv 𝓘(ℝ, E3) (let c := F.circle.chart j hj;
                letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord)
                x u)‖ ≤
            3 * Pst * θ * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner x u u) := by
  intro _ U₁ U₂ F j hj hcons bb hbb Ab θ hAb hval hdiff x hx
  let instM_BCG8b : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  have hΔ0 : 0 < Δ := lt_of_lt_of_le one_pos hΔ
  have hρj := hρ j
  obtain ⟨hρp, hband, -⟩ := P.bcg03_mem_boundarySupportList_BCG8b hεB hρ hΛ hΔ0 hβ₁ hlip hcol hΛΔ
    hreq (C := 10) (by linarith only [hΔ]) (Empty.elim : Empty → W.Carrier)
    (Empty.elim : Empty → ℝ) (fun k => k.elim) hbb
  have hρ1 : ρ j ≤ 1 := by
    have h1 : β 1 ^ 3 < 1 := by nlinarith only [hreq, hΔ, pow_pos hβ₁ 3]
    linarith only [h1, hρp]
  have hxg : x.val ∈ riemannianBallOf g j.val (10 * ρ j) := by
    have hCρ : 0 < 10 * ρ j := by positivity
    have hK₀ρ : 10 * ρ j ≤ K₀ * ρ j := mul_le_mul_of_nonneg_right hK₀ hρj.le
    have hjb : j ∈ Metric.ball j (K₀ * ρ j) := Metric.mem_ball_self (lt_of_lt_of_le hCρ hK₀ρ)
    have hxb : x ∈ Metric.ball j (K₀ * ρ j) := Metric.mem_ball.mpr (lt_of_lt_of_le hx hK₀ρ)
    change riemannianEDistOf g j.val x.val < ENNReal.ofReal (10 * ρ j)
    rw [hcons j hjb x hxb, edist_dist, dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff hCρ).mpr hx
  obtain ⟨q, hq, hqx, hq19, hq91, -, -⟩ := hband x.val hxg
  have hrow : ∀ v : ℝ², ((EuclideanSpace.proj (0 : Fin 1)).comp Ab) v = Ab v 0 := fun v => rfl
  refine bcg03_model_errors_row_BCG8b W g P bb ĝ ρ hρ hP hP2 j x hρ1
    ⟨q, hq, hqx, by linarith only [hq19], by linarith only [hq91]⟩ _
    (norm_circleRow_le_one_BCG8b Ab hAb) ?_ ?_ ?_
  · rw [hrow]
    have h := hval x hx
    refine lt_of_le_of_lt ?_ h
    have h0 := PiLp.norm_apply_le (EuclideanSpace.single 0 ((P.height bb x - P.height bb j) / ρ j) -
      Ab ((let c := F.circle.chart j hj;
          letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord x) -
        (let c := F.circle.chart j hj;
          letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord j))) 0
    simpa [Real.norm_eq_abs] using h0
  · obtain ⟨θ', hθ', h⟩ := hdiff x hx
    exact ⟨θ', hθ', fun u => by rw [hrow]; exact h u⟩
  · intro u
    have h := norm_mvfderiv_circle_coord_le_BCG8b F.circle hj (F.circleAdapted j hj) hγ
      (x := x) (by nlinarith only [hx, hρj]) u
    have hN := Real.sqrt_nonneg
      ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner x u u)
    nlinarith only [h, hN, hγ1]

end DifferentialGeometry.Geometry.Collapse
