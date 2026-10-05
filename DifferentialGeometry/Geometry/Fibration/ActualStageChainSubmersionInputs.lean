import DifferentialGeometry.Geometry.Fibration.ActualStageChainLater
import DifferentialGeometry.Analysis.InnerProductSpace.RetainedCoordinateOrthogonalGraph

/-!
# GAF02 BASES, stage submersion: the linear-algebra and local inputs (frozen batch 2, (c1)–(c4))

Blueprint `master207B.tex`, GAF02 (B:5797–5870), CGP06 (B:4130); external draft 59 §4 step 1,
review 66 (D66-7). Frozen statements of lane C14-BASESb (build-logs/scratch/C14-BASES/
ParallelTargets2.lean), proved verbatim:

* (c1) `surjective_of_rank_le_BAS`: `range Q ⊆ Tm`, `dim Tm = dim E`, `κ` injective on `Tm`,
  `rank (Q ∘ B) ≥ dim E` ⇒ `κ ∘ Q ∘ B` is onto.
* (c2) `Cfs15StageOutput.ambient_tangent_coframe_BAS`: for `z ∈ B(x, r_x)` the range of `Da(z)`
  lies in the tangent plane `Tm` of the local graph `g x` at the coordinate of `a(z)`;
  `dim Tm = dim P x` and CGP06's coframe bound `(m − ε/3)|w| ≤ (1 + ε/3)|u w|` holds on `Tm`.
  Route: `a(z) ∈ Z ∩ B(x, 3ε⁻¹r_x)`; near `z`, `a = G ∘ τ ∘ a` with `G(t) = x + (t, g t)` and
  `τ(w) = π_{P x}(w − x)` (`graph_eq`); chain rule; `coframe_range_fderiv_orthogonalGraph_BPRE`.
* (c4a) `isOpen_gafStagePlateau_BAS`: the original threshold-6 plateaux are open (circle
  coordinates Lipschitz on `B(c, 200ρ)`, edge / slim coordinates smooth on their chart balls, the
  height continuous).
* (c4b) `Gaf02Chain.stageMap_eventuallyEq_BAS`: for an active slot `O`,
  `f_st = π_Q ∘ a ∘ π_Q ∘ g_st` near every plateau point (CFS31's plateau + (ADJ)).
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

/-- **(c1) Surjectivity from rank**: `range Q ⊆ Tm`, `dim Tm = dim E`, `κ` injective on `Tm`, and
`rank (Q ∘ B) ≥ dim E` ⇒ `κ ∘ Q ∘ B` is onto. -/
theorem surjective_of_rank_le_BAS {V H E : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup H]
    [Module ℝ H] [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] (Bm : V →ₗ[ℝ] H)
    (Q : H →ₗ[ℝ] H) (Tm : Submodule ℝ H) [FiniteDimensional ℝ Tm] (hQ : LinearMap.range Q ≤ Tm)
    (κ : H →ₗ[ℝ] E) (hκ : Set.InjOn κ Tm) (hdim : Module.finrank ℝ Tm = Module.finrank ℝ E)
    (hrank : Module.finrank ℝ E ≤ Module.finrank ℝ (LinearMap.range (Q ∘ₗ Bm))) :
    Surjective (κ ∘ₗ Q ∘ₗ Bm) := by
  have hle : LinearMap.range (Q ∘ₗ Bm) ≤ Tm := (LinearMap.range_comp_le_range _ _).trans hQ
  have heq : LinearMap.range (Q ∘ₗ Bm) = Tm :=
    Submodule.eq_of_le_of_finrank_le hle (hdim.le.trans hrank)
  have hinj : Injective (κ.domRestrict Tm) := fun a b hab =>
    Subtype.ext (hκ a.2 b.2 hab)
  have hsurj : Surjective (κ.domRestrict Tm) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  intro y
  obtain ⟨t, ht⟩ := hsurj y
  have htm : (t : H) ∈ LinearMap.range (Q ∘ₗ Bm) := by
    rw [heq]
    exact t.2
  obtain ⟨v, hv⟩ := htm
  refine ⟨v, ?_⟩
  rw [LinearMap.comp_apply, hv]
  exact ht

/-- `π_L(t + n) = t` for `t ∈ L`, `n ∈ Lᗮ`. -/
theorem orthogonalProjectionOnto_add_orthogonal_BASP {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (L : Submodule ℝ H) [L.HasOrthogonalProjection] (t : L) (n : Lᗮ) :
    L.orthogonalProjectionOnto ((t : H) + (n : H)) = t := by
  rw [map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal n.2, add_zero]

/-- The coordinate of a graph point: `π_L(x + (t, n) − x) = t`. -/
theorem orthogonalProjectionOnto_graph_BASP {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (L : Submodule ℝ H) [L.HasOrthogonalProjection] (x : H) (t : L)
    (n : Lᗮ) :
    L.orthogonalProjectionOnto (x + orthogonalCoordinateSum L (t, n) - x) = t := by
  rw [add_sub_cancel_left]
  exact orthogonalProjectionOnto_add_orthogonal_BASP L t n

/-- **(c2) The tangent of a CFS15 output's zero set along the ambient map, with CGP06's
coframe**: for `z ∈ B(x, r_x)`, `range Da(z)` lies in a subspace `Tm` (the tangent plane of the
local graph `g x` at the coordinate of `a(z)`) with `dim Tm = dim P x`, on which a retained
coordinate `u` with `m‖v‖ ≤ ‖u v‖` on `P x` (`ε/3 < m`) satisfies the coframe bound
`(m − ε/3)‖w‖ ≤ (1 + ε/3)‖u w‖` (so `u` is injective on `Tm`). Route: `O.value_deriv` puts `a(z)` in
`B(x, 3ε⁻¹r_x)`, `O.graph_eq` writes it on the graph, `a = G ∘ π_{P x}(a − x)` near `z`
(chain rule), `coframe_range_fderiv_orthogonalGraph_BPRE` with `O.graph_jets` (slope `ε/3`). -/
theorem Cfs15StageOutput.ambient_tangent_coframe_BAS {H E : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k K : ℕ} {ε cw : ℝ} {Sc T : Set H} {r : H → ℝ} {P : H → Submodule ℝ H}
    (O : Cfs15StageOutput k K ε cw Sc T r P) (x : Sc) {z : H} (hz : z ∈ ball (x : H) (r x))
    (u : H →L[ℝ] E) (hu : ‖u‖ ≤ 1) {m : ℝ} (hm : ∀ v ∈ P x, m * ‖v‖ ≤ ‖u v‖) (hεm : ε / 3 < m) :
    ∃ Tm : Submodule ℝ H, LinearMap.range (fderiv ℝ O.ambient z : H →ₗ[ℝ] H) ≤ Tm ∧
      Module.finrank ℝ Tm = Module.finrank ℝ (P x) ∧
      ∀ w ∈ Tm, (m - ε / 3) * ‖w‖ ≤ (1 + ε / 3) * ‖u w‖ := by
  have hε := O.eps_pos
  have hε1 := O.eps_le
  have hr := O.radius_pos x x.2
  have hinv : 10 ≤ ε⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hε]
    linarith
  -- the graph map and the coordinate map
  set L : Submodule ℝ H := P x with hL
  let G : L → H := fun s => (x : H) + orthogonalCoordinateSum L (s, O.g x s)
  let τ : H → L := fun w => L.orthogonalProjectionOnto (w - x)
  have hav := O.ambient_value_deriv x.2 hz
  -- every zero near `x` is `G (τ w)`
  have hgraph : ∀ w ∈ O.Z ∩ ball (x : H) (3 * ε⁻¹ * r x),
      w = G (τ w) ∧ τ w ∈ ball (0 : L) (4 * ε⁻¹ * r x) := by
    intro w hw
    have hw' := hw
    rw [O.graph_eq x] at hw'
    obtain ⟨⟨t, ht, hwt⟩, -⟩ := hw'
    have hτ : τ w = t := by
      change L.orthogonalProjectionOnto (w - x) = t
      rw [hwt]
      exact orthogonalProjectionOnto_graph_BASP L x t (O.g x t)
    rw [hτ]
    exact ⟨hwt, ht⟩
  -- `a(z)` is such a zero, and so is `a(y)` for `y` near `z`
  have hzΩ := mem_cfs15Omega_of_mem_C15 x.2 hz
  have hball : O.ambient z ∈ ball (x : H) (3 * ε⁻¹ * r x) := by
    rw [mem_ball, dist_eq_norm]
    have h1 : ‖(P x).starProjection (z - x)‖ ≤ ‖z - x‖ :=
      Submodule.norm_starProjection_apply_le _ _
    have h2 : ‖z - x‖ < r x := by
      rw [← dist_eq_norm]
      exact hz
    have h3 : ‖O.ambient z - x‖ ≤ ‖O.ambient z - (x + (P x).starProjection (z - x))‖ +
        ‖(P x).starProjection (z - x)‖ := by
      have := norm_add_le (O.ambient z - (x + (P x).starProjection (z - x)))
        ((P x).starProjection (z - x))
      rwa [show O.ambient z - (x + (P x).starProjection (z - x)) + (P x).starProjection (z - x) =
        O.ambient z - x by abel] at this
    have h4 : 3 * r x ≤ 3 * ε⁻¹ * r x / 10 := by
      have := mul_le_mul_of_nonneg_right hinv hr.le
      nlinarith
    nlinarith [hav.1]
  have hcont : ContinuousAt O.ambient z := (O.ambient_contDiffAt hzΩ).continuousAt
  have hev : O.ambient =ᶠ[𝓝 z] fun y => G (τ (O.ambient y)) := by
    have h1 : ∀ᶠ y in 𝓝 z, y ∈ ball (x : H) (r x) := isOpen_ball.mem_nhds hz
    have h2 : ∀ᶠ y in 𝓝 z, O.ambient y ∈ ball (x : H) (3 * ε⁻¹ * r x) :=
      hcont.eventually (isOpen_ball.mem_nhds hball)
    filter_upwards [h1, h2] with y hy1 hy2
    exact (hgraph _ ⟨O.ambient_mem (mem_cfs15Omega_of_mem_C15 x.2 hy1), hy2⟩).1
  -- the parameter of `a(z)` and the derivatives
  have hz0 := (hgraph _ ⟨O.ambient_mem hzΩ, hball⟩).2
  have hgd : DifferentiableAt ℝ (O.g x) (τ (O.ambient z)) :=
    ((O.graph_smooth x).contDiffAt (isOpen_ball.mem_nhds hz0)).differentiableAt (by simp)
  have hG := hasFDerivAt_orthogonalGraph_BPRE L (O.g x) (x : H) hgd
  have hτd : HasFDerivAt τ (L.orthogonalProjectionOnto : H →L[ℝ] L) (O.ambient z) := by
    have h := (L.orthogonalProjectionOnto : H →L[ℝ] L).hasFDerivAt (x := O.ambient z - x)
    exact h.comp (O.ambient z) ((hasFDerivAt_id _).sub_const (x : H))
  have had : HasFDerivAt O.ambient (fderiv ℝ O.ambient z) z := hav.2.1.hasFDerivAt
  have hcomp := hG.comp z (hτd.comp z had)
  have hfd : fderiv ℝ O.ambient z =
      (L.subtypeL + Lᗮ.subtypeL.comp (fderiv ℝ (O.g x) (τ (O.ambient z)))).comp
        ((L.orthogonalProjectionOnto : H →L[ℝ] L).comp (fderiv ℝ O.ambient z)) :=
    hev.fderiv_eq.trans hcomp.fderiv
  have hDg := norm_fderiv_le_of_iteratedFDeriv_one_BPRE (O.g x) hr
    (O.graph_jets x _ hz0 1 (by omega))
  -- the tangent plane of the graph
  refine ⟨LinearMap.range ((L.subtypeL + Lᗮ.subtypeL.comp (fderiv ℝ (O.g x) (τ (O.ambient z))) :
      L →L[ℝ] H) : L →ₗ[ℝ] H), ?_, ?_, ?_⟩
  · rintro w ⟨v, rfl⟩
    refine ⟨(L.orthogonalProjectionOnto : H →L[ℝ] L) (fderiv ℝ O.ambient z v), ?_⟩
    conv_rhs => rw [hfd]
    rfl
  · have hinj : Injective ((L.subtypeL + Lᗮ.subtypeL.comp (fderiv ℝ (O.g x) (τ (O.ambient z))) :
        L →L[ℝ] H) : L →ₗ[ℝ] H) := by
      intro a b hab
      have h := congrArg (fun w => L.orthogonalProjectionOnto w) hab
      change L.orthogonalProjectionOnto ((a : H) + ((fderiv ℝ (O.g x) (τ (O.ambient z)) a : Lᗮ) : H)) =
        L.orthogonalProjectionOnto ((b : H) + ((fderiv ℝ (O.g x) (τ (O.ambient z)) b : Lᗮ) : H)) at h
      rwa [orthogonalProjectionOnto_add_orthogonal_BASP,
        orthogonalProjectionOnto_add_orthogonal_BASP] at h
    exact LinearMap.finrank_range_of_inj hinj
  · have hcf := coframe_range_fderiv_orthogonalGraph_BPRE L u hu hm hεm.le (O.g x) (x : H) hgd hDg
    rw [hG.fderiv] at hcf
    exact hcf

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- The circle plateau `B⁶₁` is open (the circle coordinate is Lipschitz on `B(c, 200ρ(c))`). -/
theorem isOpen_gafStagePlateau_zero_BASP (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ
    b s b' s' ε γc βc Lmax τ γ δ εr e T V) : IsOpen (gafStagePlateau_BAS P 0) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨j, hpj, hη⟩ := hp
  have hj : j.1 ∈ P.toLocalChartFamily.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hρj := hρ j.1
  have hlip : LipschitzOnWith (Real.toNNReal (2 / ρ j.1))
      (cgpCoord P.toLocalChartFamily P.zero (.inl j)) (ball j.1 (200 * ρ j.1)) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy w hw => ?_
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
    exact cgpCircleCoord_lipschitz P.toLocalChartFamily hj y hy w hw
  have hU : IsOpen (ball j.1 (200 * ρ j.1) ∩
      cgpCoord P.toLocalChartFamily P.zero (.inl j) ⁻¹' ball (0 : ℝ²) 6) :=
    hlip.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_ball
  refine Filter.mem_of_superset (hU.mem_nhds ⟨hpj, by rwa [mem_preimage, mem_ball_zero_iff]⟩)
    fun q hq => ?_
  exact ⟨j, hq.1, by simpa [mem_ball_zero_iff] using hq.2⟩

/-- The edge plateau `B⁶₂` is open (the edge coordinate is smooth on `B(c, 100Δρ(c))`, the height
is continuous). -/
theorem isOpen_gafStagePlateau_one_BASP (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ
    b s b' s' ε γc βc Lmax τ γ δ εr e T V) : IsOpen (gafStagePlateau_BAS P 1) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨j, hpj, hη, ht⟩ := hp
  have hj : j.1 ∈ P.edge.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hU : IsOpen ((ball j.1 (100 * Δ * ρ j.1) ∩
      P.edge.coord j.1 ⁻¹' Ioo (-(6 * Δ)) (6 * Δ)) ∩
        cgpHeight P.toLocalChartFamily ⁻¹' Iio (6 * Δ)) :=
    ((P.toLocalChartFamily.edge.contMDiffOn_coord hj).continuousOn.isOpen_inter_preimage
      isOpen_ball isOpen_Ioo).inter (isOpen_Iio.preimage (continuous_cgpHeight _))
  refine Filter.mem_of_superset (hU.mem_nhds ⟨⟨hpj, abs_lt.mp hη⟩, ht⟩) fun q hq => ?_
  exact ⟨j, hq.1.1, abs_lt.mpr hq.1.2, hq.2⟩

/-- The slim plateau `B⁶₃` is open (the slim coordinate is smooth on `B(c, 10⁶Δρ(c))`). -/
theorem isOpen_gafStagePlateau_two_BASP (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ
    b s b' s' ε γc βc Lmax τ γ δ εr e T V) : IsOpen (gafStagePlateau_BAS P 2) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨j, hpj, hη⟩ := hp
  have hball : ball j.1 (1000000 * Δ * ρ j.1) = ball j.1 (10 ^ 6 * Δ * ρ j.1) := by norm_num
  have hU : IsOpen (ball j.1 (1000000 * Δ * ρ j.1) ∩
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord ⁻¹'
        Ioo (-(6 * (10 ^ 5 * Δ))) (6 * (10 ^ 5 * Δ))) := by
    rw [hball]
    exact (SlimCentre.contMDiffOn_coord _).continuousOn.isOpen_inter_preimage isOpen_ball
      isOpen_Ioo
  refine Filter.mem_of_superset (hU.mem_nhds ⟨hpj, abs_lt.mp hη⟩) fun q hq => ?_
  exact ⟨j, hq.1, abs_lt.mpr hq.2⟩

/-- **(c4a) The original threshold-6 plateaux are open** (chart coordinates and the height are
continuous on the chart domains). -/
theorem isOpen_gafStagePlateau_BAS (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s'
    ε γc βc Lmax τ γ δ εr e T V) (st : Fin 3) : IsOpen (gafStagePlateau_BAS P st) := by
  fin_cases st
  · exact isOpen_gafStagePlateau_zero_BASP P
  · exact isOpen_gafStagePlateau_one_BASP P
  · exact isOpen_gafStagePlateau_two_BASP P

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **(c4b) The stage map near a plateau point** (CFS31's plateau on an open set + (ADJ)): for an
active slot `O`, `f_st = π_Q ∘ a ∘ π_Q ∘ g_st` on a neighbourhood of every `p ∈ B⁶_st`. -/
theorem stageMap_eventuallyEq_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    {st : Fin 3}
    {O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st) (gafCloud P.toLocalChartFamily P.zero st)
      (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => S st * ρ (C.sel st x))
      (C.plane st)}
    (hO : C.slot st = .active O) {p : X} (hp : p ∈ gafStagePlateau_BAS P.toLocalChartPackets st) :
    C.stageMap_BAS st =ᶠ[𝓝 p] fun q => (gafStageQ P.toLocalChartFamily P.zero st).starProjection
      (O.ambient ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (C.stageIn_BAS st q))) := by
  filter_upwards [(isOpen_gafStagePlateau_BAS P.toLocalChartPackets st).mem_nhds hp] with q hq
  have h1 := C.cutoff_eq_one_of_plateau_BAS hq
  rw [stageMap_BAS, C.stageOut_eq_adjust_BAS st q,
    starProjection_adjust_of_one_BAS _ (C.slot st).map _ h1, hO]
  rfl

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
