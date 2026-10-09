import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightEdgeOn
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightNormalized

/-!
# BCG02 at an edge reference (explicit edge family): value AND differential clause, ONE sign (BCG-7, G7)

Blueprint 207B, BCG02 (`B:8822–8958`) at an edge reference, for an EXPLICIT `EdgeFamilyOn` (review
51 P0-A, ACTIVE EDGE rule: the binding instantiates `F.edgeB`, never the inherited `F.edge`), on the
regionalised packets `LocalPacketsOn` (the curvature buffer is the base family's, `E.centres ⊆ U₁`):
"For edge references EGP01 supplies absence of a `(2, β₂)`-splitting … obtaining a sign and the same
raw comparison on the required … ball"; the differential check uses the axis length `400Δ`, the edge
test on `B(100Δ) × B(1000Δ)` with separation `> 100Δ` (LFR19.1) and the chart's `(1 + σ)`-Lipschitz
coordinate.

* `sign_row_comp_adjoint_BCG7`, `norm_single_BCG7`, `single_sub_smul_BCG7`: a sign `a = ±1` as a unit
  row of `ℝ¹`, and `ℝ¹` bookkeeping;
* `bcg02_differential_normalized_sign_BCG7`: the normalized-scale check (BCG-7 G4) for a rank-one
  reference splitting into `ℝ ×₂ Y`, a sign and a real reference coordinate (via
  `exists_finOne_split_KA3` and `a • id`);
* `EdgeFamilyOn.exists_split_test_BCG7`: the edge chart's normalized splitting at its centre with the
  coordinate's value error, global Lipschitz bound, differentiability on `B(j, 100Δρ(j))` and the edge
  test, all on the SAME splitting;
* `bcg02_edge_differential_of_split_on_BCG7`: for `θ < 1`, `ν < 10⁻⁶`, `Δ ≥ 1`: an early `σ` and a
  rank-one quality bound `η`; at every centre `j` of `E`, every rank-one approximation `φ` with real
  coordinate `U` (`‖DU‖ ≤ 1 + δ_N` in `R⁻²g`, BCG02.b along the normalized test geodesics up to length
  `400Δ + 1` on `B(j, 20Δρ(j))`) gives ONE sign `a` with the value clause `|U − a(η_j − η_j(j))| < θ`
  and the differential clause `‖DU − aDη_j‖ < θ` on `B(j, 20Δρ(j))`. Requests: `3b ≤ σ`,
  `b(2(421Δ + 1)) ≤ 1`, `b, s < 10⁻⁶`, `μΔ ≤ θ/4`, `0 ≤ σ_c ≤ θ²/10⁷`, `b, δ_N ≤ θ²/10⁷`,
  `ρ(j)(400Δ + 1) ≤ θ²/10⁷` (edge qualities may depend on `Δ`);
* consumer `bcg02_edge_differential_inherited_BCG7` (the statement at `E = F.edge`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The sign row `a • id : ℝ¹ → ℝ¹` (`a = ±1`) is a unit row. -/
theorem sign_row_comp_adjoint_BCG7 {a : ℝ} (ha : a = 1 ∨ a = -1) :
    (a • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))).comp
        (ContinuousLinearMap.adjoint (a • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))) =
      ContinuousLinearMap.id ℝ _ := by
  rw [map_smul, ContinuousLinearMap.adjoint_id]
  ext v i
  rcases ha with rfl | rfl <;> simp

/-- In `ℝ¹`: `‖e₀ c‖ = |c|`. -/
theorem norm_single_BCG7 (c : ℝ) : ‖EuclideanSpace.single (0 : Fin 1) c‖ = |c| := by
  simp

/-- In `ℝ¹`: `e₀t − ℓ⁻¹(e₀u − e₀v) = e₀(t − (u − v)/ℓ)`. -/
theorem single_sub_smul_BCG7 (t u v ℓ : ℝ) :
    EuclideanSpace.single (0 : Fin 1) t -
        ℓ⁻¹ • (EuclideanSpace.single (0 : Fin 1) u - EuclideanSpace.single (0 : Fin 1) v) =
      EuclideanSpace.single (0 : Fin 1) (t - (u - v) / ℓ) := by
  ext i
  fin_cases i
  simp [div_eq_inv_mul]

section Normalized

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **The normalized-scale check with a sign** (rank-one reference splitting into `ℝ ×₂ Y`, real
reference coordinate `φ_c`, sign `a`); hypotheses as in `bcg02_differential_normalized_BCG7`, with
`φ_c` differentiable on `B(p, r_x)`. -/
theorem bcg02_differential_normalized_sign_BCG7 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Y : Type*} [MetricSpace Y] {p : M} {a₀ : Y} {β : ℝ}
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), a₀)) β) {a : ℝ} (ha : a = 1 ∨ a = -1)
    (φc : M → ℝ) (U : M → ℝ)
    {θ L r rx rfar sep γ E δN R : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hβ : β ≤ 1 / 10000)
    (hL : 2 ≤ L) (hLr : L + r + 1 ≤ β⁻¹ / 2) (hrx : r ≤ rx) (hfar : L + r + 1 ≤ rfar)
    (hsep : sep + 1 ≤ L) (hγ : 0 ≤ γ) (hE : 0 ≤ E) (hδN : 0 ≤ δN) (hR : 0 ≤ R)
    (hbud : δN + γ + R * (L + 1) + γ + 2 * E + 5 * β ≤ θ ^ 2 / 100000)
    (hraw : ∀ y, dist y p < L + r + 1 → |U y - a * (ψ.toFun y).fst| < E)
    (hdiff : ∀ x ∈ ball p rx, MDifferentiableAt I 𝓘(ℝ, ℝ) φc x)
    (htest : ∀ x ∈ ball p rx, ∀ z ∈ ball p rfar, sep < dist x z →
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x z) = z →
      |mvfderiv I φc x w - ((ψ.toFun z).fst - (ψ.toFun x).fst) / dist x z| < γ)
    (hnc : ∀ x ∈ ball p r, ∀ u : TangentSpace I x,
      |mvfderiv I φc x u| ≤ (1 + γ) * Real.sqrt (g.inner x u u))
    (hnU : ∀ x ∈ ball p r, ∀ u : TangentSpace I x,
      |mvfderiv I U x u| ≤ (1 + δN) * Real.sqrt (g.inner x u u))
    (htay : ∀ x ∈ ball p r, ∀ w : TangentSpace I x, g.inner x w w = 1 →
      ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ L + 1 →
      |mvfderiv I U x w - (U (intrinsicGeodesic g hEnorm x w ℓ) - U x) / ℓ| ≤ R * ℓ)
    (x : M) (hx : x ∈ ball p r) :
    ∃ θ' < θ, ∀ u : TangentSpace I x,
      |mvfderiv I U x u - a * mvfderiv I φc x u| ≤ θ' * Real.sqrt (g.inner x u u) := by
  obtain ⟨ψ', hψ'⟩ := exists_finOne_split_KA3 ψ
  set A : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    a • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) with hAdef
  have hA := sign_row_comp_adjoint_BCG7 ha
  let S : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single 0 1)
  have hS : ∀ t : ℝ, S t = EuclideanSpace.single 0 t := fun t => by
    ext i
    simp [S]
  have hAS : ∀ t : ℝ, A (EuclideanSpace.single 0 t) 0 = a * t := fun t => by
    simp [hAdef]
  have hDφ : ∀ y ∈ ball p rx, ∀ u : TangentSpace I y,
      mvfderiv I (fun z => S (φc z)) y u = S (mvfderiv I φc y u) := fun y hy u =>
    mvfderiv_clm_comp (hdiff y hy) S u
  have hrr : ∀ y ∈ ball p r, y ∈ ball p rx := fun y hy =>
    mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hy) hrx)
  obtain ⟨θ', hθ', hle⟩ := bcg02_differential_normalized_BCG7 g hEnorm ψ' A hA
    (fun z => S (φc z)) U hθ hθ1 hβ hL hLr hrx hfar hsep hγ hE hδN hR hbud
    (fun y hy => by rw [hψ' y, hAS]; exact hraw y hy)
    (fun x' hx' z hz hsep' w hw hgeo => by
      rw [hDφ x' hx' w, hS, hψ' z, hψ' x', single_sub_smul_BCG7, norm_single_BCG7]
      exact htest x' hx' z hz hsep' w hw hgeo)
    (fun y hy u => by
      rw [hDφ y (hrr y hy) u, hS, norm_single_BCG7]
      exact hnc y hy u)
    hnU htay x hx
  refine ⟨θ', hθ', fun u => ?_⟩
  have h := hle u
  rw [hDφ x (hrr x hx) u, hS, hAS] at h
  exact h

end Normalized

section EdgeTest

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ} {U₁ U₂ : Set X}

/-- **The edge chart at its centre, with its test on the same splitting** (normalized scale). -/
theorem EdgeFamilyOn.exists_split_test_BCG7
    (E : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) {j : X}
    (hj : j ∈ E.centres) (hσc : 0 ≤ σc) :
    ∃ (Y : Type) (mY : MetricSpace Y), letI _y := mY
      ∃ q : Y, ∃ f : @KleinerLottApprox X (WithLp 2 (ℝ × Y))
          (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j (WithLp.toLp 2 (0, q)) b,
        E.coord_BCG1 j hj j = 0 ∧
        (∀ x, dist x j < 100 * Δ * ρ j →
          |E.coord_BCG1 j hj x - (@KleinerLottApprox.toFun X _
            (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _ f x).fst| < μ * Δ) ∧
        (∀ x y, |E.coord_BCG1 j hj x - E.coord_BCG1 j hj y| ≤
          (1 + σc) * ((ρ j)⁻¹ * dist x y)) ∧
        (∀ x, dist x j < 100 * Δ * ρ j →
          MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (E.coord_BCG1 j hj) x) ∧
        (let cE : X → ℝ := E.coord_BCG1 j hj;
          let hMc : CompleteSpace X := ‹CompleteSpace X›;
          letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j));
          letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j));
          letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
            radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j));
          letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
            radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j));
          letI : CompleteSpace X :=
            (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc;
          let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
            scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g;
          have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR :=
            isMetricNorm_of_riemannianBundle gR;
          ∀ x ∈ ball j (100 * Δ), ∀ x' ∈ ball j (1000 * Δ), 100 * Δ < dist x x' →
            ∀ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 →
            intrinsicGeodesic gR hnR x w (dist x x') = x' →
            |mvfderiv 𝓘(ℝ, E3) cE x w -
              ((@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
                  f x').fst -
                (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
                  f x).fst) / dist x x'| < σc) := by
  have hcen := E.chart_center j hj
  have hρj := hρ j
  let C := E.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hcen' : C.center = j := hcen
  let _ := C.instY
  obtain ⟨f, hf⟩ := exists_kla_basepoint_KA3 hcen' C.split
  refine ⟨C.Y, C.instY, C.q, f, ?_, fun x hx => ?_, fun x y => ?_, fun x hx => ?_, ?_⟩
  · change C.coord j = 0
    have h0 := C.coord_center
    rw [hcen'] at h0
    exact h0
  · rw [hf x]
    change |C.coord x - (C.split.toFun x).fst| < μ * Δ
    refine C.value x ?_
    rw [hcen']
    change @dist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toDist x j < 100 * Δ
    rw [MetricSpace.rescale_dist, inv_mul_lt_iff₀ hρj]
    linarith
  · have h := C.lipschitz.dist_le_mul x y
    rw [Real.coe_toNNReal _ (by linarith)] at h
    exact h
  · have hxd : x ∈ C.domain := by
      apply C.closedBall_subset_domain
      rw [hcen']
      change @dist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toDist x j ≤ 100 * Δ
      rw [MetricSpace.rescale_dist, inv_mul_le_iff₀ hρj]
      linarith
    exact (C.contMDiffOn_coord.contMDiffAt (C.isOpen_domain.mem_nhds hxd)).mdifferentiableAt
      (by simp)
  · dsimp only
    intro x hx x' hx' hsep w hw hgeo
    have h := C.test x (by rw [hcen']; exact hx) x' (by rw [hcen']; exact hx') hsep w hw hgeo
    rw [hf x, hf x']
    exact h

end EdgeTest

/-- **BCG02 at an edge reference, explicit edge family, value and differential clause with one sign**
(abstract step; see the module docstring). -/
theorem bcg02_edge_differential_of_split_on_BCG7 {θ ν Δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hν : 0 < ν) (hν1 : ν < 1 / 1000000) (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X},
      LocalPacketsOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V U₁ U₂ →
      ∀ (E : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc Ue₁ Ue₂),
      E.centres ⊆ U₁ → σ⁻¹ ≤ Lmax → 3 * b ≤ σ → b * (2 * (421 * Δ + 1)) ≤ 1 →
      b < 1 / 1000000 → s < 1 / 1000000 → μ * Δ ≤ θ / 4 → 0 ≤ σc → σc ≤ θ ^ 2 / 10000000 →
      b ≤ θ ^ 2 / 10000000 →
      ∀ (j : X) (hj : j ∈ E.centres) (Tm : Type) [MetricSpace Tm] (t₀ : Tm) {ε₁ : ℝ},
      ε₁ ≤ η →
      ∀ φ : @KleinerLottApprox X (WithLp 2 (ℝ × Tm)) (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j
          (WithLp.toLp 2 (0, t₀)) ε₁,
      ∀ U : X → ℝ, (∀ y, (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)))
          _ _ _ _ φ y).fst = U y) →
      ∀ {δN : ℝ}, 0 ≤ δN → δN ≤ θ ^ 2 / 10000000 → ρ j * (400 * Δ + 1) ≤ θ ^ 2 / 10000000 →
      (∀ x, dist x j < 20 * Δ * ρ j → ∀ u : TangentSpace 𝓘(ℝ, E3) x,
        |mvfderiv 𝓘(ℝ, E3) U x u| ≤ (1 + δN) * Real.sqrt
          ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g).inner x u u)) →
      (let hMc : CompleteSpace X := ‹CompleteSpace X›;
        letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI : CompleteSpace X :=
          (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc;
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g;
        have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR;
        ∀ x ∈ ball j (20 * Δ), ∀ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 →
          ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 400 * Δ + 1 → |mvfderiv 𝓘(ℝ, E3) U x w -
            (U (intrinsicGeodesic gR hnR x w ℓ) - U x) / ℓ| ≤ ρ j * ℓ) →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
        (∀ y, dist y j < 20 * Δ * ρ j →
          |U y - a * (E.coord_BCG1 j hj y - E.coord_BCG1 j hj j)| < θ) ∧
        ∀ x, dist x j < 20 * Δ * ρ j → ∃ θ' < θ, ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3) U x u - a * mvfderiv 𝓘(ℝ, E3) (E.coord_BCG1 j hj) x u| ≤
            θ' * Real.sqrt
              ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g).inner x u u) := by
  set H : ℝ := 421 * Δ with hH
  have hH0 : 0 < H := by rw [hH]; linarith
  set τ' : ℝ := min (θ ^ 2 / 10000000000) (1 / (2 * (H + 1))) with hτdef
  have hτ : 0 < τ' := lt_min (by positivity) (by positivity)
  have hτθ : τ' ≤ θ ^ 2 / 10000000000 := min_le_left _ _
  have hτH : τ' ≤ 1 / (2 * (H + 1)) := min_le_right _ _
  have hτ1 : τ' < 1 := by
    have : 1 / (2 * (H + 1)) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have ha : 20 * τ' ≤ H + 1 := by linarith
  have ha2 : 2 * (H + 1) ≤ τ'⁻¹ := by
    rw [le_inv_comm₀ (by linarith) hτ]
    rwa [one_div] at hτH
  obtain ⟨σ, hσ, hσ1, hk⟩ := exists_sign_raw_alignment_real_complete_BCG1 hτ hτ1 hν
    (by linarith) ha ha2
  obtain ⟨η, hη, hk⟩ := hk 0 le_rfl
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro X mX instC instM hXc instS g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V U₁ U₂ Ue₁ Ue₂ F E hEU hσL h3b hbH hb6 hs6 hμ hσc0 hσcθ hbθ j hj Tm _ t₀ ε₁ hε₁ φ U hU δN
    hδN0 hδN hρθ hnorm htay
  have hρj := hρ j
  have hjU : j ∈ U₁ := hEU hj
  obtain ⟨Y, mY, q, f, hc0, hval, hlipc, hdiffc, htestc⟩ := E.exists_split_test_BCG7 hj hσc0
  have hsec := F.sectional_buffer σ⁻¹ (inv_pos.mpr hσ) hσL j hjU
  have hno : ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) j 2 ν :=
    @not_hasEuclideanSplitting_two_of_isEdgePoint.{0, 0, 0} X
      (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) j Δ b s ν (E.strong j hj) hb6 hs6 hν1
  have hr1 : ρ j / ρ j = 1 := div_self hρj.ne'
  obtain ⟨a, ha, hlin⟩ := hk X g hmetric ρ hρ j j hsec hno (by rw [hr1]; norm_num)
    (by rw [hr1]; norm_num) (by rw [dist_self, zero_mul]) Tm Y t₀ q hε₁ h3b hbH φ f
  have hφj : (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
      φ j).fst = 0 := by
    rw [@KleinerLottApprox.basepoint X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ φ]
    rfl
  have hraw : ∀ y, dist y j < H * ρ j →
      |U y - a * (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
        f y).fst| ≤ 50 * τ' := by
    intro y hy
    have hmain := hlin y (by rw [mem_ball]; exact hy)
    rw [hr1, hφj, one_mul, mul_zero, sub_zero, hU y] at hmain
    exact hmain
  have ha1 : |a| = 1 := by rcases ha with rfl | rfl <;> norm_num
  have hθ2 : θ ^ 2 < θ := by nlinarith only [hθ, hθ1]
  refine ⟨a, ha, fun y hy => ?_, fun x hx => ?_⟩
  · -- the value clause with the same sign
    have hv := hval y (by
      have : 20 * Δ * ρ j ≤ 100 * Δ * ρ j := by nlinarith only [hΔ, hρj]
      linarith only [hy, this])
    rw [hc0, sub_zero]
    set fy := (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
      f y).fst
    set cy := E.coord_BCG1 j hj y
    have hr := hraw y (by
      have : 20 * Δ * ρ j ≤ H * ρ j := by rw [hH]; nlinarith only [hΔ, hρj]
      linarith only [hy, this])
    have h2 : |a * (fy - cy)| < μ * Δ := by
      rw [abs_mul, ha1, one_mul, abs_sub_comm]
      exact hv
    have hsplit : U y - a * cy = (U y - a * fy) + a * (fy - cy) := by ring
    calc |U y - a * cy| = |(U y - a * fy) + a * (fy - cy)| := by rw [hsplit]
      _ ≤ |U y - a * fy| + |a * (fy - cy)| := abs_add_le _ _
      _ < 50 * τ' + μ * Δ := by linarith only [hr, h2]
      _ ≤ θ := by linarith only [hτθ, hμ, hθ2, hθ]
  · -- the differential clause, at the normalized metric
    have hbpos : 0 < b :=
      @KleinerLottApprox.error_pos X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ f
    have hxR : x ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j
        (20 * Δ) := by
      change (ρ j)⁻¹ * dist x j < 20 * Δ
      rw [inv_mul_lt_iff₀ hρj]
      linarith only [hx]
    have hraw' : ∀ y, @dist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toDist y j <
        400 * Δ + 20 * Δ + 1 →
        |U y - a * (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
          f y).fst| < 100 * τ' := by
      intro y hy
      change (ρ j)⁻¹ * dist y j < 400 * Δ + 20 * Δ + 1 at hy
      rw [inv_mul_lt_iff₀ hρj] at hy
      have h1 := hraw y (by
        have : ρ j * (400 * Δ + 20 * Δ + 1) ≤ H * ρ j := by rw [hH]; nlinarith only [hΔ, hρj]
        linarith only [hy, this])
      linarith only [h1, hτ]
    have hdiff' : ∀ y ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j
        (100 * Δ), MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (E.coord_BCG1 j hj) y := by
      intro y hy
      change (ρ j)⁻¹ * dist y j < 100 * Δ at hy
      rw [inv_mul_lt_iff₀ hρj] at hy
      exact hdiffc y (by linarith only [hy])
    have hnc' : ∀ y ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j
        (20 * Δ), ∀ u : TangentSpace 𝓘(ℝ, E3) y, |mvfderiv 𝓘(ℝ, E3) (E.coord_BCG1 j hj) y u| ≤
          (1 + σc) * Real.sqrt
            ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρj) 2) g).inner y u u) := by
      intro y hy u
      change (ρ j)⁻¹ * dist y j < 20 * Δ at hy
      rw [inv_mul_lt_iff₀ hρj] at hy
      have hyb : y ∈ ball j (100 * Δ * ρ j) := mem_ball.mpr (by nlinarith only [hy, hΔ, hρj])
      have h := norm_mvfderiv_le_of_lipschitz_rescale_BCG7 g hmetric isOpen_ball hyb
        (hdiffc y (mem_ball.mp hyb)) (L := 1 + σc) (by linarith only [hσc0]) hρj
        (fun y' _ z' _ => by rw [Real.norm_eq_abs]; exact hlipc y' z') u
      rwa [Real.norm_eq_abs] at h
    have hnU' : ∀ y ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j
        (20 * Δ), ∀ u : TangentSpace 𝓘(ℝ, E3) y, |mvfderiv 𝓘(ℝ, E3) U y u| ≤ (1 + δN) * Real.sqrt
          ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρj) 2) g).inner y u u) := by
      intro y hy u
      change (ρ j)⁻¹ * dist y j < 20 * Δ at hy
      rw [inv_mul_lt_iff₀ hρj] at hy
      exact hnorm y (by linarith only [hy]) u
    have hbinv : 2 * (421 * Δ + 1) ≤ b⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hbpos, ← one_div, le_div_iff₀ (by positivity)]
      linarith only [hbH]
    let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hρj)
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρj) 2) g
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
    exact @bcg02_differential_normalized_sign_BCG7 E3 _ _ _ _ E3 _ 𝓘(ℝ, E3) _ X
      (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) instC instM instS
      (radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hρj))
      (radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr hρj))
      ((mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr hρj)).mpr hXc)
      (radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr hρj))
      gR hnR Y mY j q b f a ha (E.coord_BCG1 j hj) U θ (400 * Δ) (20 * Δ) (100 * Δ) (1000 * Δ)
      (100 * Δ) σc (100 * τ') δN (ρ j) hθ hθ1 (by linarith only [hb6])
      (by linarith only [hΔ]) (by linarith only [hbinv, hΔ]) (by linarith only [hΔ])
      (by linarith only [hΔ]) (by linarith only [hΔ]) hσc0 (by linarith only [hτ]) hδN0 hρj.le
      (by linarith only [hδN, hσcθ, hρθ, hτθ, hbθ, sq_nonneg θ]) hraw' hdiff' htestc hnc' hnU'
      htay x hxR

/-- **Consumer: the inherited edge family.** The abstract step at `E = F.edge` (the inherited family
of `LocalPacketsOn`, centres in `U₁`). The active boundary edge family is `F.edgeB` (review 51
P0-A); this instance only checks the explicit-family statement against the old one. -/
theorem bcg02_edge_differential_inherited_BCG7 {θ ν Δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hν : 0 < ν) (hν1 : ν < 1 / 1000000) (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ} {U₁ U₂ : Set X}
      (F : LocalPacketsOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
        U₁ U₂),
      σ⁻¹ ≤ Lmax → 3 * b ≤ σ → b * (2 * (421 * Δ + 1)) ≤ 1 →
      b < 1 / 1000000 → s < 1 / 1000000 → μ * Δ ≤ θ / 4 → 0 ≤ σc → σc ≤ θ ^ 2 / 10000000 →
      b ≤ θ ^ 2 / 10000000 →
      ∀ (j : X) (hj : j ∈ F.edge.centres) (Tm : Type) [MetricSpace Tm] (t₀ : Tm) {ε₁ : ℝ},
      ε₁ ≤ η →
      ∀ φ : @KleinerLottApprox X (WithLp 2 (ℝ × Tm)) (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j
          (WithLp.toLp 2 (0, t₀)) ε₁,
      ∀ U : X → ℝ, (∀ y, (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)))
          _ _ _ _ φ y).fst = U y) →
      ∀ {δN : ℝ}, 0 ≤ δN → δN ≤ θ ^ 2 / 10000000 → ρ j * (400 * Δ + 1) ≤ θ ^ 2 / 10000000 →
      (∀ x, dist x j < 20 * Δ * ρ j → ∀ u : TangentSpace 𝓘(ℝ, E3) x,
        |mvfderiv 𝓘(ℝ, E3) U x u| ≤ (1 + δN) * Real.sqrt
          ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g).inner x u u)) →
      (let hMc : CompleteSpace X := ‹CompleteSpace X›;
        letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI : CompleteSpace X :=
          (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc;
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g;
        have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR;
        ∀ x ∈ ball j (20 * Δ), ∀ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 →
          ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 400 * Δ + 1 → |mvfderiv 𝓘(ℝ, E3) U x w -
            (U (intrinsicGeodesic gR hnR x w ℓ) - U x) / ℓ| ≤ ρ j * ℓ) →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
        (∀ y, dist y j < 20 * Δ * ρ j →
          |U y - a * (F.edge.coord_BCG1 j hj y - F.edge.coord_BCG1 j hj j)| < θ) ∧
        ∀ x, dist x j < 20 * Δ * ρ j → ∃ θ' < θ, ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3) U x u - a * mvfderiv 𝓘(ℝ, E3) (F.edge.coord_BCG1 j hj) x u| ≤
            θ' * Real.sqrt
              ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g).inner x u u) := by
  obtain ⟨σ, hσ, hσ1, η, hη, h⟩ := bcg02_edge_differential_of_split_on_BCG7 hθ hθ1 hν hν1 hΔ
  exact ⟨σ, hσ, hσ1, η, hη, fun F => h F F.edge F.edge.centres_subset⟩

end DifferentialGeometry.Geometry.Collapse
