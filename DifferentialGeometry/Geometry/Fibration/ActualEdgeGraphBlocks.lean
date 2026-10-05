import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraphKernel

/-!
# EGP06 (EG): the blocks of `R_i⁻¹π₂F` at a point of `{|η_i| ≤ 8Δ, t ≤ 8Δ}`, tag by tag

Blueprint `master207B.tex`, EGP06 (B:5088–5139), proof. At a point `x` of the edge core of the
reference `i` each block of the actual map `𝓔⁰ = cgpGlobalMap L Z` is, to first order at `x`, the
model block of EGP06 evaluated at the actual coordinate `U_t = s_t c_t`:

* `egp06_own_tag_KC4`: the own block `(ρ_i ζ_i η_i, ρ_i ζ_i)` equals `ρ_i (η_i, 1)` in value and
  derivative (`ζ_i(x) = 1`, `dζ_i = 0`: `ζ_i ≤ 1` has a maximum at `x`).
* `egp06_edge_tag_KC4` (listed edge `j ≠ i`): `ζ_j ≤ f(η_j/Δ)` near `x` with equality at `x`
  (`t(x) ≤ 8Δ`), so `d(ζ_j − f(η_j/Δ))_x = 0` and the block is
  `graphPacketModelBlock Δ s_j (s_jη_j)`
  to first order; with EGP04's (EC) at `x` the block error is at most `4Bθ`, `B = 50(P† + 1)`.
* `egp06_slim_tag_KC4` (listed slim `j`): `ζ_j = f_s(η_j/10⁵Δ)` on `B(j, 10⁶Δρ_j)`;
  `egp06_zero_tag_KC4` (zero `k` meeting `D_i`): `ζ_k = Φ(η_k)` everywhere.
* `egp06_unlisted_tag_KC4`: a tag whose cutoff support misses `x` and whose model block is zero
  contributes nothing.
* `EdgeFamily.coord_lipschitz_max_KC4`, `EdgeFamily.abs_deriv_le_max_KC4`: the coordinate bound
  with `max(1 + σ, 0)` (no sign hypothesis on `σ`), giving `|dη_i(w)| ≤ 2` for `σ ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

section Coordinate

/-- The edge coordinate `η_j` is `max(1 + σ, 0)/ρ(j)`-Lipschitz (no sign hypothesis on `σ`). -/
theorem EdgeFamily.coord_lipschitz_max_KC4
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) {j : X} (hj : j ∈ F.centres)
    (y z : X) : |F.coord j y - F.coord j z| ≤ max (1 + σc) 0 / ρ j * dist y z := by
  have hrj := hρ j
  have he : ((Real.toNNReal (1 + σc) : NNReal) : ℝ) * ((ρ j)⁻¹ * dist y z) =
      max (1 + σc) 0 / ρ j * dist y z := by
    rw [Real.coe_toNNReal']
    field_simp
  unfold EdgeFamily.coord
  rw [dite_eq_left hj]
  let C := F.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
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

/-- The derivative of the reference coordinate on a `ρ_i⁻²g`-unit vector:
`|dη_i(w)| ≤ max(1 + σ, 0)` on the chart ball (no sign hypothesis on `σ`). -/
theorem EdgeFamily.abs_deriv_le_max_KC4
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) {i : X} (hi : i ∈ F.centres)
    {x : X} (hx : x ∈ ball i (100 * Δ * ρ i)) (w : TangentSpace 𝓘(ℝ, E3) x)
    (hw : (ρ i)⁻¹ ^ 2 * g.inner x w w = 1) :
    |mvfderiv 𝓘(ℝ, E3) (F.coord i) x w| ≤ max (1 + σc) 0 := by
  have hri := hρ i
  have hud : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (F.coord i) x :=
    ((F.contMDiffOn_coord hi).contMDiffAt (isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp)
  have h := abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_univ (mem_univ x) hud
    (fun y _ z _ => F.coord_lipschitz_max_KC4 hi y z) w
  have hg : g.inner x w w = ρ i ^ 2 := by
    have h2 : (ρ i)⁻¹ ^ 2 * ρ i ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hri.ne', one_pow]
    have h3 : (ρ i)⁻¹ ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero hri.ne')
    exact mul_left_cancel₀ h3 (hw.trans h2.symm)
  rw [hg, Real.sqrt_sq hri.le] at h
  have he : max (1 + σc) 0 / ρ i * ρ i = max (1 + σc) 0 := by field_simp
  linarith

end Coordinate

section Tags

/-- The common block bound `B = 50(P† + 1)` of EGP06's model blocks. -/
theorem egp06_block_bounds_KC4 :
    0 ≤ 50 * (egpProfileConst + 1) ∧ 50 * (edgeProfileDerivativeBound + 1) ≤
      50 * (egpProfileConst + 1) ∧ 50 * (sgpProfileBound + 1) ≤ 50 * (egpProfileConst + 1) ∧
      50 * (zeroProfileBound + 1) ≤ 50 * (egpProfileConst + 1) := by
  have hP := one_le_egpProfileConst
  have hPe : edgeProfileDerivativeBound ≤ egpProfileConst := le_max_left _ _
  have hPs : sgpProfileBound ≤ egpProfileConst := (le_max_left _ _).trans (le_max_right _ _)
  have hPz : zeroProfileBound ≤ egpProfileConst := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **The own block at a core point.** At `x ∈ B(i, 100Δρ_i)` with `|η_i(x)| ≤ 8Δ` and
`t(x) ≤ 8Δ`, the own block of `R_i⁻¹𝓔⁰` and its derivative equal EGP06's own model block
`(η_i, 1)` and its derivative. -/
theorem egp06_own_tag_KC4
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 0 < Δ)
    (hmargin : ∀ j ∈ L.edge.centres, tsupport (L.edge.cutoff j) ⊆ ball j (100 * Δ * ρ j))
    {i : X} (hi : i ∈ L.edge.centres) (sgn c : CGPTag L Z → ℝ)
    (j : L.edge.finite_centres.toFinset) (hj : j.1 = i) {x : X}
    (hx : x ∈ ball i (100 * Δ * ρ i)) (hη : |L.edge.coord i x| ≤ 8 * Δ)
    (ht : cgpHeight L x ≤ 8 * Δ) (w : TangentSpace 𝓘(ℝ, E3) x) :
    (ρ i)⁻¹ • cgpGlobalMap L Z x (.inr (.inr (.inl j))) =
        egpModelComponent L Z i sgn c (.inr (.inr (.inl j))) (L.edge.coord i x) ∧
      (ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap L Z y (.inr (.inr (.inl j)))) x w =
        fderiv ℝ (egpModelComponent L Z i sgn c (.inr (.inr (.inl j)))) (L.edge.coord i x)
          (mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x w) := by
  rcases j with ⟨j, hjm⟩
  dsimp only at hj
  subst hj
  have hri := hρ j
  have hζ1 : L.edge.cutoff j x = 1 := L.edge.cutoff_eq_one_of_le hΔ hi hx hη ht
  have hζle : ∀ y, L.edge.cutoff j y ≤ 1 := fun y => (cgpEdgeCutoff_mem_Icc L hΔ j y).2
  have hζd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (L.edge.cutoff j) x :=
    (L.edge.contMDiff_cutoff_of_margin hΔ L.contMDiff_scale.continuous (hmargin j hi)
      x).mdifferentiableAt (by simp)
  have hψd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => L.edge.cutoff j y - 1) x :=
    hζd.sub mdifferentiableAt_const
  have hmax : IsLocalMax (fun y => L.edge.cutoff j y - 1) x :=
    Eventually.of_forall fun y => by
      change L.edge.cutoff j y - 1 ≤ L.edge.cutoff j x - 1
      rw [hζ1]
      linarith [hζle y]
  have hdψ := hmax.mvfderiv_eq_zero (I := 𝓘(ℝ, E3)) BoundarylessManifold.isInteriorPoint
  have hcd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (L.edge.coord j) x :=
    ((L.edge.contMDiffOn_coord hi).contMDiffAt (isOpen_ball.mem_nhds hx)).mdifferentiableAt
      (by simp)
  have hW₀ : Differentiable ℝ (fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) :=
    own_block_bounds_KC3.1.differentiable (by simp)
  have hB : ∀ᶠ y in 𝓝 x, cgpGlobalMap L Z y (.inr (.inr (.inl ⟨j, hjm⟩))) =
      ρ j • blockLift_KC3 ((fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ)))
        (1 * L.edge.coord j y)) + (L.edge.cutoff j y - 1) • (ρ j • blockLift_KC3
          ((fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) (L.edge.coord j y))) :=
    Eventually.of_forall fun y => own_block_split_KC4 (ρ j) (L.edge.cutoff j y) (L.edge.coord j y)
  obtain ⟨hv, hd⟩ := mvfderiv_split_KC4 (I := 𝓘(ℝ, E3)) blockLift_KC3
    (B := fun y => cgpGlobalMap L Z y (.inr (.inr (.inl ⟨j, hjm⟩))))
    (W := fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ)))
    (W₀ := fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ)))
    (c := L.edge.coord j) (ψ := fun y => L.edge.cutoff j y - 1)
    (r := ρ j) (s := 1) (R := ρ j) hB hcd (hW₀ _) (hW₀ _) hψd (by rw [hζ1, sub_self]) hdψ w
  have hown : egpModelComponent L Z j sgn c (.inr (.inr (.inl ⟨j, hjm⟩))) =
      blockLift_KC3 ∘ fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ)) := by
    simp only [egpModelComponent, ite_true]
    rfl
  rw [hown, fderiv_clm_comp_apply_KC3 blockLift_KC3 (hW₀ _), hv, hd, inv_smul_smul₀ hri.ne',
    inv_smul_smul₀ hri.ne', one_mul, one_mul]
  exact ⟨rfl, rfl⟩

/-- **A listed edge block at a core point.** For `j ∈ J_e`, `j ≠ i`, at `x ∈ B(j, 100Δρ_j)` with
`t(x) ≤ 8Δ`, EGP04's (EC) at `x` with sign `σ = sgn_j` and translation `c_j` (`|σ| ≤ 1`), and
`|dη_i(w)| ≤ 2`: the block of `R_i⁻¹𝓔⁰` and its derivative differ from EGP06's model block
`graphPacketModelBlock Δ s_j (σa + c_j)` at `a = η_i(x)` by at most `4Bθ`, `B = 50(P† + 1)`. -/
theorem egp06_edge_tag_KC4
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ)
    (hmargin : ∀ j ∈ L.edge.centres, tsupport (L.edge.cutoff j) ⊆ ball j (100 * Δ * ρ j))
    {i : X} (sgn c : CGPTag L Z → ℝ) (j : L.edge.finite_centres.toFinset) (hji : j.1 ≠ i)
    (hjl : j.1 ∈ egpEdgeList L i) (hs : 99 / 100 ≤ ρ j.1 / ρ i) {θ : ℝ} (hθ1 : θ ≤ 1)
    (hσ : |sgn (.inr (.inr (.inl j)))| ≤ 1) {x : X} (hxj : x ∈ ball j.1 (100 * Δ * ρ j.1))
    (ht : cgpHeight L x ≤ 8 * Δ) (w : TangentSpace 𝓘(ℝ, E3) x)
    (hu : |ρ j.1 / ρ i * L.edge.coord j.1 x - (sgn (.inr (.inr (.inl j))) * L.edge.coord i x +
      c (.inr (.inr (.inl j))))| < θ)
    (hdu : |ρ j.1 / ρ i * mvfderiv 𝓘(ℝ, E3) (L.edge.coord j.1) x w -
      sgn (.inr (.inr (.inl j))) * mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x w| < θ)
    (hda : |mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x w| ≤ 2) :
    ‖(ρ i)⁻¹ • cgpGlobalMap L Z x (.inr (.inr (.inl j))) -
        egpModelComponent L Z i sgn c (.inr (.inr (.inl j))) (L.edge.coord i x)‖ ≤
        4 * (50 * (egpProfileConst + 1)) * θ ∧
      ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap L Z y (.inr (.inr (.inl j)))) x w -
        fderiv ℝ (egpModelComponent L Z i sgn c (.inr (.inr (.inl j)))) (L.edge.coord i x)
          (mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x w)‖ ≤ 4 * (50 * (egpProfileConst + 1)) * θ := by
  rcases j with ⟨j, hjm⟩
  dsimp only at hji hjl hs hxj hσ hu hdu ⊢
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  have hrj := hρ j
  have hjc : j ∈ L.edge.centres := (Set.Finite.mem_toFinset _).mp hjm
  obtain ⟨sj, hsjdef⟩ : ∃ sj : ℝ, sj = ρ j / ρ i := ⟨_, rfl⟩
  rw [← hsjdef] at hs hu hdu
  have hsj0 : sj ≠ 0 := by rw [hsjdef]; exact (div_pos hrj hri).ne'
  have hrs : ρ i * sj = ρ j := by rw [hsjdef]; field_simp
  have hζd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (L.edge.cutoff j) x :=
    (L.edge.contMDiff_cutoff_of_margin hΔ0 L.contMDiff_scale.continuous (hmargin j hjc)
      x).mdifferentiableAt (by simp)
  have hcc : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (L.edge.coord j) x :=
    (L.edge.contMDiffOn_coord hjc).contMDiffAt (isOpen_ball.mem_nhds hxj)
  have hcd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (L.edge.coord j) x :=
    hcc.mdifferentiableAt (by simp)
  have hφd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (fun y => scaledEdgeCoordinateProfile Δ (L.edge.coord j y)) x :=
    ((contDiff_scaledEdgeCoordinateProfile Δ).contMDiff.contMDiffAt.comp x
      hcc).mdifferentiableAt (by simp)
  have hψd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (fun y => L.edge.cutoff j y - scaledEdgeCoordinateProfile Δ (L.edge.coord j y)) x :=
    hζd.sub hφd
  have hψ0 : L.edge.cutoff j x - scaledEdgeCoordinateProfile Δ (L.edge.coord j x) = 0 := by
    rw [L.edge.cutoff_eq_coordinateProfile_of_le hΔ0 hjc hxj ht, sub_eq_zero]
    rfl
  have hmax : IsLocalMax
      (fun y => L.edge.cutoff j y - scaledEdgeCoordinateProfile Δ (L.edge.coord j y)) x := by
    filter_upwards [isOpen_ball.mem_nhds hxj] with y hy
    change L.edge.cutoff j y - scaledEdgeCoordinateProfile Δ (L.edge.coord j y) ≤
      L.edge.cutoff j x - scaledEdgeCoordinateProfile Δ (L.edge.coord j x)
    rw [hψ0, L.edge.cutoff_eq_formula hjc hy]
    have h1 := intervalPlateauProfile_mem_Icc (-9) (-8) 8 9 (L.edge.coord j y / Δ)
    have h2 := descendingIntervalProfile_mem_Icc 8 9 (L.edge.smoothing y / ρ y / Δ)
    change intervalPlateauProfile (-9) (-8) 8 9 (L.edge.coord j y / Δ) *
        descendingIntervalProfile 8 9 (L.edge.smoothing y / ρ y / Δ) -
      intervalPlateauProfile (-9) (-8) 8 9 (L.edge.coord j y / Δ) ≤ 0
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hdψ := hmax.mvfderiv_eq_zero (I := 𝓘(ℝ, E3)) BoundarylessManifold.isInteriorPoint
  have hW₀ : Differentiable ℝ (fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) :=
    own_block_bounds_KC3.1.differentiable (by simp)
  have hWd : Differentiable ℝ (graphPacketModelBlock Δ sj) :=
    (contDiff_graphPacketModelBlock Δ sj).differentiable (by simp)
  have hB : ∀ᶠ y in 𝓝 x, cgpGlobalMap L Z y (.inr (.inr (.inl ⟨j, hjm⟩))) =
      ρ i • blockLift_KC3 (graphPacketModelBlock Δ sj (sj * L.edge.coord j y)) +
        (L.edge.cutoff j y - scaledEdgeCoordinateProfile Δ (L.edge.coord j y)) •
          (ρ j • blockLift_KC3 ((fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) :
            WithLp 2 (ℝ × ℝ))) (L.edge.coord j y))) :=
    Eventually.of_forall fun y =>
      block_split_KC4 (scaledEdgeCoordinateProfile Δ) hsj0 hrs (L.edge.cutoff j y)
        (L.edge.coord j y)
  obtain ⟨hv, hd⟩ := mvfderiv_split_KC4 (I := 𝓘(ℝ, E3)) blockLift_KC3
    (B := fun y => cgpGlobalMap L Z y (.inr (.inr (.inl ⟨j, hjm⟩))))
    (W := graphPacketModelBlock Δ sj)
    (W₀ := fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ)))
    (c := L.edge.coord j)
    (ψ := fun y => L.edge.cutoff j y - scaledEdgeCoordinateProfile Δ (L.edge.coord j y))
    (r := ρ i) (s := sj) (R := ρ j) hB hcd (hWd _) (hW₀ _) hψd hψ0 hdψ w
  have hcomp : egpModelComponent L Z i sgn c (.inr (.inr (.inl ⟨j, hjm⟩))) =
      fun a => blockLift_KC3 (graphPacketModelBlock Δ sj
        (sgn (.inr (.inr (.inl ⟨j, hjm⟩))) * a + c (.inr (.inr (.inl ⟨j, hjm⟩))))) := by
    simp only [egpModelComponent, hji, hjl, ite_true, ite_false, hsjdef]
  obtain ⟨hB0, hBe, -, -⟩ := egp06_block_bounds_KC4
  have hb := graphPacketModelBlock_derivative_bounds hΔ hs
  exact tag_compare_KC4 blockLift_KC3 norm_blockLift_apply_KC3
    ((contDiff_graphPacketModelBlock Δ sj).of_le (by simp)) hB0
    (fun y => (hb y).1.trans hBe) (fun y => (hb y).2.trans hBe) hθ1 hri.ne' hu hdu hσ hda hcomp
    hv hd

/-- **A listed slim block at a point of its chart ball.** For `j ∈ J_s` at
`x ∈ B(j, 10⁶Δρ_j)` (where `ζ_j = f_s(η_j/10⁵Δ)`), EGP04's (EC) at `x` with sign `σ = sgn_j`,
translation `c_j` (`|σ| ≤ 1`) and `|dη_i(w)| ≤ 2`: the block of `R_i⁻¹𝓔⁰` and its derivative differ
from EGP06's model block `sgpModelBlock (10⁵Δ) s_j (σa + c_j)` at `a = η_i(x)` by at most `4Bθ`. -/
theorem egp06_slim_tag_KC4 {Lmax : ℝ}
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) {i : X}
    (sgn c : CGPTag L.toLocalChartFamily Z → ℝ) (j : L.slim.finite_centres.toFinset)
    (hjl : j.1 ∈ egpSlimList L.toLocalChartFamily i) (hs : 99 / 100 ≤ ρ j.1 / ρ i) {θ : ℝ}
    (hθ1 : θ ≤ 1) (hσ : |sgn (.inr (.inl j))| ≤ 1) {x : X}
    (hxj : x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1)) (w : TangentSpace 𝓘(ℝ, E3) x)
    (hu : |ρ j.1 / ρ i * (L.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x -
      (sgn (.inr (.inl j)) * L.edge.coord i x + c (.inr (.inl j)))| < θ)
    (hdu : |ρ j.1 / ρ i * mvfderiv 𝓘(ℝ, E3)
        (L.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x w -
      sgn (.inr (.inl j)) * mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x w| < θ)
    (hda : |mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x w| ≤ 2) :
    ‖(ρ i)⁻¹ • cgpGlobalMap L.toLocalChartFamily Z x (.inr (.inl j)) -
        egpModelComponent L.toLocalChartFamily Z i sgn c (.inr (.inl j)) (L.edge.coord i x)‖ ≤
        4 * (50 * (egpProfileConst + 1)) * θ ∧
      ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (fun y => cgpGlobalMap L.toLocalChartFamily Z y (.inr (.inl j))) x w -
        fderiv ℝ (egpModelComponent L.toLocalChartFamily Z i sgn c (.inr (.inl j)))
          (L.edge.coord i x) (mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x w)‖ ≤
        4 * (50 * (egpProfileConst + 1)) * θ := by
  rcases j with ⟨j, hjm⟩
  dsimp only at hjl hs hxj hσ hu hdu ⊢
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  have hrj := hρ j
  have hjc : j ∈ L.slim.centres := (Set.Finite.mem_toFinset _).mp hjm
  obtain ⟨sj, hsjdef⟩ : ∃ sj : ℝ, sj = ρ j / ρ i := ⟨_, rfl⟩
  rw [← hsjdef] at hs hu hdu
  have hsj0 : sj ≠ 0 := by rw [hsjdef]; exact (div_pos hrj hri).ne'
  have hrs : ρ i * sj = ρ j := by rw [hsjdef]; field_simp
  obtain ⟨cj, hcjdef⟩ : ∃ cj : X → ℝ, cj = (L.slim.centre j hjc).coord := ⟨_, rfl⟩
  have hcc : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ cj x := by
    rw [hcjdef]
    exact (fc18_slim_row L.toLocalChartFamily hΔ0 hjc).2.2.2.contMDiffAt
      (isOpen_ball.mem_nhds hxj)
  have hcd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) cj x := hcc.mdifferentiableAt (by simp)
  -- the slim cutoff is its profile on the chart ball
  have hcut : ∀ y ∈ ball j (10 ^ 6 * Δ * ρ j),
      L.slim.cutoff j y = sgpProfile (10 ^ 5 * Δ) (cj y) := by
    intro y hy
    have h := L.slim_cutoff_apply hjc y
    have hy' : dist y j < 10 ^ 6 * Δ * ρ j := hy
    simp only [hy', ↓reduceIte] at h
    unfold SlimFamily.cutoff
    rw [dite_eq_left hjc, h, hcjdef]
    rfl
  have hψev : (fun y => L.slim.cutoff j y - sgpProfile (10 ^ 5 * Δ) (cj y)) =ᶠ[𝓝 x]
      fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_ball.mem_nhds hxj] with y hy
    rw [hcut y hy, sub_self]
  have hψ0 : L.slim.cutoff j x - sgpProfile (10 ^ 5 * Δ) (cj x) = 0 := hψev.self_of_nhds
  have hψd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (fun y => L.slim.cutoff j y - sgpProfile (10 ^ 5 * Δ) (cj y)) x :=
    mdifferentiableAt_const.congr_of_eventuallyEq hψev
  have hmax : IsLocalMax (fun y => L.slim.cutoff j y - sgpProfile (10 ^ 5 * Δ) (cj y)) x := by
    filter_upwards [hψev] with y hy
    change L.slim.cutoff j y - sgpProfile (10 ^ 5 * Δ) (cj y) ≤
      L.slim.cutoff j x - sgpProfile (10 ^ 5 * Δ) (cj x)
    rw [hy, hψ0]
  have hdψ := hmax.mvfderiv_eq_zero (I := 𝓘(ℝ, E3)) BoundarylessManifold.isInteriorPoint
  have hW₀ : Differentiable ℝ (fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) :=
    own_block_bounds_KC3.1.differentiable (by simp)
  have hWd : Differentiable ℝ (sgpModelBlock (10 ^ 5 * Δ) sj) :=
    (contDiff_sgpModelBlock (10 ^ 5 * Δ) sj).differentiable (by simp)
  have hB : ∀ᶠ y in 𝓝 x, cgpGlobalMap L.toLocalChartFamily Z y (.inr (.inl ⟨j, hjm⟩)) =
      ρ i • blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) sj (sj * cj y)) +
        (L.slim.cutoff j y - sgpProfile (10 ^ 5 * Δ) (cj y)) •
          (ρ j • blockLift_KC3 ((fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) :
            WithLp 2 (ℝ × ℝ))) (cj y))) := by
    refine Eventually.of_forall fun y => ?_
    rw [hcjdef]
    exact block_split_KC4 (sgpProfile (10 ^ 5 * Δ)) hsj0 hrs (L.slim.cutoff j y)
      ((L.slim.centre j hjc).coord y)
  obtain ⟨hv, hd⟩ := mvfderiv_split_KC4 (I := 𝓘(ℝ, E3)) blockLift_KC3
    (B := fun y => cgpGlobalMap L.toLocalChartFamily Z y (.inr (.inl ⟨j, hjm⟩)))
    (W := sgpModelBlock (10 ^ 5 * Δ) sj)
    (W₀ := fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ)))
    (c := cj) (ψ := fun y => L.slim.cutoff j y - sgpProfile (10 ^ 5 * Δ) (cj y))
    (r := ρ i) (s := sj) (R := ρ j) hB hcd (hWd _) (hW₀ _) hψd hψ0 hdψ w
  have hcomp : egpModelComponent L.toLocalChartFamily Z i sgn c (.inr (.inl ⟨j, hjm⟩)) =
      fun a => blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) sj
        (sgn (.inr (.inl ⟨j, hjm⟩)) * a + c (.inr (.inl ⟨j, hjm⟩)))) := by
    simp only [egpModelComponent, hjl, ite_true, hsjdef]
  obtain ⟨hB0, -, hBs, -⟩ := egp06_block_bounds_KC4
  have hℓ : 1 ≤ 10 ^ 5 * Δ := by linarith
  have hb := sgpModelBlock_derivative_bounds hℓ hs
  rw [← hcjdef] at hu hdu
  exact tag_compare_KC4 blockLift_KC3 norm_blockLift_apply_KC3
    ((contDiff_sgpModelBlock (10 ^ 5 * Δ) sj).of_le (by simp)) hB0
    (fun y => (hb y).1.trans hBs) (fun y => (hb y).2.trans hBs) hθ1 hri.ne' hu hdu hσ hda hcomp
    hv hd

/-- **A zero block meeting `D_i`.** For a zero support `k` meeting `D_i` (zero ratio
`s₀ = R_k/ρ_i ≥ 1`, LC80's radial coordinate differentiable at `x`), EGP04's (EC) at `x` with
sign `σ`, translation `c_k` (`|σ| ≤ 1`) and `|dη_i(w)| ≤ 2`: the block of `R_i⁻¹𝓔⁰` and its
derivative differ from EGP06's model block `zeroModelBlock s₀ (σa + c_k)` by at most `4Bθ`. -/
theorem egp06_zero_tag_KC4
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) {i : X}
    (sgn c : CGPTag L Z → ℝ) (k : Z.finite_centres.toFinset)
    (hkl : k.1 ∈ zeroMeetingList Z i (20 * Δ))
    (hs : 1 ≤ (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i) {θ : ℝ}
    (hθ1 : θ ≤ 1) (hσ : |sgn (.inr (.inr (.inr (.inl k))))| ≤ 1) {x : X}
    (hrad : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x)
    (w : TangentSpace 𝓘(ℝ, E3) x)
    (hu : |(Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
        (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x -
      (sgn (.inr (.inr (.inr (.inl k)))) * L.edge.coord i x + c (.inr (.inr (.inr (.inl k)))))| <
        θ)
    (hdu : |(Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i * mvfderiv 𝓘(ℝ, E3)
        (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x w -
      sgn (.inr (.inr (.inr (.inl k)))) * mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x w| < θ)
    (hda : |mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x w| ≤ 2) :
    ‖(ρ i)⁻¹ • cgpGlobalMap L Z x (.inr (.inr (.inr (.inl k)))) -
        egpModelComponent L Z i sgn c (.inr (.inr (.inr (.inl k)))) (L.edge.coord i x)‖ ≤
        4 * (50 * (egpProfileConst + 1)) * θ ∧
      ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (fun y => cgpGlobalMap L Z y (.inr (.inr (.inr (.inl k))))) x w -
        fderiv ℝ (egpModelComponent L Z i sgn c (.inr (.inr (.inr (.inl k)))))
          (L.edge.coord i x) (mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x w)‖ ≤
        4 * (50 * (egpProfileConst + 1)) * θ := by
  rcases k with ⟨k, hkm⟩
  dsimp only at hkl hs hσ hrad hu hdu ⊢
  have hri := hρ i
  have hkc : k ∈ Z.centres := (Set.Finite.mem_toFinset _).mp hkm
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, R₀ = (Z.zero k hkc).radius := ⟨_, rfl⟩
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : X → ℝ, u₀ = (Z.zero k hkc).radial := ⟨_, rfl⟩
  obtain ⟨s₀, hs₀def⟩ : ∃ s₀ : ℝ, s₀ = R₀ / ρ i := ⟨_, rfl⟩
  rw [← hR₀, ← hs₀def, ← hu₀] at hu hdu
  rw [← hR₀, ← hs₀def] at hs
  rw [← hu₀] at hrad
  have hs₀0 : s₀ ≠ 0 := by linarith
  have hrs : ρ i * s₀ = R₀ := by rw [hs₀def]; field_simp
  have hψ : (fun y => annularCutoff cutoffProfile (u₀ y) - annularCutoff cutoffProfile (u₀ y)) =
      fun _ => (0 : ℝ) := funext fun y => sub_self _
  have hψd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (fun y => annularCutoff cutoffProfile (u₀ y) - annularCutoff cutoffProfile (u₀ y)) x := by
    rw [hψ]
    exact mdifferentiableAt_const
  have hdψ : mvfderiv 𝓘(ℝ, E3)
      (fun y => annularCutoff cutoffProfile (u₀ y) - annularCutoff cutoffProfile (u₀ y)) x = 0 := by
    rw [hψ]
    exact mvfderiv_const 0
  have hW₀ : Differentiable ℝ (fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) :=
    own_block_bounds_KC3.1.differentiable (by simp)
  have hWd : Differentiable ℝ (zeroModelBlock s₀) :=
    (contDiff_zeroModelBlock s₀).differentiable (by simp)
  have hB : ∀ᶠ y in 𝓝 x, cgpGlobalMap L Z y (.inr (.inr (.inr (.inl ⟨k, hkm⟩)))) =
      ρ i • blockLift_KC3 (zeroModelBlock s₀ (s₀ * u₀ y)) +
        (annularCutoff cutoffProfile (u₀ y) - annularCutoff cutoffProfile (u₀ y)) •
          (R₀ • blockLift_KC3 ((fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) :
            WithLp 2 (ℝ × ℝ))) (u₀ y))) := by
    refine Eventually.of_forall fun y => ?_
    have hrs' : ρ i * s₀ = (Z.zero k hkc).radius := by rw [hrs, hR₀]
    rw [hR₀, hu₀]
    exact block_split_KC4 (R := (Z.zero k hkc).radius) (annularCutoff cutoffProfile) hs₀0 hrs'
      (annularCutoff cutoffProfile ((Z.zero k hkc).radial y)) ((Z.zero k hkc).radial y)
  obtain ⟨hv, hd⟩ := mvfderiv_split_KC4 (I := 𝓘(ℝ, E3)) blockLift_KC3
    (B := fun y => cgpGlobalMap L Z y (.inr (.inr (.inr (.inl ⟨k, hkm⟩)))))
    (W := zeroModelBlock s₀)
    (W₀ := fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ)))
    (c := u₀)
    (ψ := fun y => annularCutoff cutoffProfile (u₀ y) - annularCutoff cutoffProfile (u₀ y))
    (r := ρ i) (s := s₀) (R := R₀) hB hrad (hWd _) (hW₀ _) hψd (sub_self _) hdψ w
  have hcomp : egpModelComponent L Z i sgn c (.inr (.inr (.inr (.inl ⟨k, hkm⟩)))) =
      fun a => blockLift_KC3 (zeroModelBlock s₀
        (sgn (.inr (.inr (.inr (.inl ⟨k, hkm⟩)))) * a +
          c (.inr (.inr (.inr (.inl ⟨k, hkm⟩)))))) := by
    simp only [egpModelComponent, hkl, ite_true, hs₀def, hR₀]
  obtain ⟨hB0, -, -, hBz⟩ := egp06_block_bounds_KC4
  have hb := zeroModelBlock_derivative_bounds hs
  exact tag_compare_KC4 blockLift_KC3 norm_blockLift_apply_KC3
    ((contDiff_zeroModelBlock s₀).of_le (by simp)) hB0
    (fun y => (hb y).1.trans hBz) (fun y => (hb y).2.trans hBz) hθ1 hri.ne' hu hdu hσ hda hcomp
    hv hd

/-- **An inactive tag.** A tag whose cutoff support misses `x` and whose model block is the zero
function contributes nothing: value and derivative errors vanish. -/
theorem egp06_unlisted_tag_KC4
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (sgn c : CGPTag L Z → ℝ) (t : CGPTag L Z) (hl : ¬ egpModelListed L Z i t) {x : X}
    (hx : x ∉ tsupport (cgpCutoff L Z t)) (w : TangentSpace 𝓘(ℝ, E3) x) :
    (ρ i)⁻¹ • cgpGlobalMap L Z x t - egpModelComponent L Z i sgn c t (L.edge.coord i x) = 0 ∧
      (ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap L Z y t) x w -
        fderiv ℝ (egpModelComponent L Z i sgn c t) (L.edge.coord i x)
          (mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x w) = 0 := by
  have h0 := egpModelComponent_eq_zero L Z i sgn c t hl
  have hval : cgpGlobalMap L Z x t = 0 := by
    change blockMap (cgpRadius L Z) (cgpCutoff L Z) (cgpCoord L Z) x t = 0
    rw [blockMap_apply, image_eq_zero_of_notMem_tsupport hx, mul_zero, zero_smul]
    rfl
  have hder : mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap L Z y t) x w = 0 :=
    mvfderiv_block_eq_zero_of_notMem_tsupport (R := cgpRadius L Z) (η := cgpCoord L Z) hx w
  rw [h0, hval, hder, smul_zero]
  refine ⟨by simp, ?_⟩
  rw [fderiv_zero]
  simp

end Tags

end DifferentialGeometry.Geometry.Collapse
