import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc33Row

/-!
# GAF02 BASES: the threshold-5 submersions `π_jE : U_j → W_j` into the manifold `W_j`

Lane S-BASES-KER, group G10 (residual of D74-2 row 5, gap (c) of C14-REG-CHAIN G11). The threshold-5
submersions of the bases object (`Gaf02Bases.*.spec.submersion`, `final_submersion_*_BAS`) are in
chart form: `D(κ_j ∘ π_stE)` is onto for the linear chart `κ_j`. Here the corestriction
`U_st → W_st` is a smooth map INTO the manifold `W_st` (chart-form structure of
`Gaf02Bases.toSmoothStageBases74`, models `ℝ²`, `ℝ`, `ℝ`) with SURJECTIVE manifold derivative at
every point of FC33's exact `U_st`.

Route: (1) the charts of `W_st` are `κ_i ∘ val` (chosen piece `i`), so a map into `W_st` is smooth
iff its inclusion into the block space is (`contMDiffAt_of_val_BAS`); (2) `val` is an immersion
(`SmoothStageBasesOn74.*_isManifold`); the rank of `D(val ∘ F) = D(π_stE)` is at least `d` (the
chart `κ_j ∘ π_stE` of the domain's index `j` is onto `ℝ^d`) and `range D(val ∘ F) ⊆ range D val`
has dimension `d`, so `D F` is onto (`surjective_mfderiv_of_immersion_BAS`; no comparison of
different charts is needed).

* `surjective_mfderiv_congr_eventually_BAS`, `surjective_mfderiv_of_immersion_BAS`,
  `linearChartedSpace_chartAt_apply_BAS`, `contMDiffAt_of_val_BAS` (generic);
* `Gaf02Bases.finalCorestrict_BAS` (the corestriction, with a junk value outside `U_st`);
* **`Gaf02Bases.final_submersion_manifold_circle_BAS`**, `…edge_BAS`, `…slim_BAS`;
* `SmoothStageBasesOn74.edge_later_embedding`, `slim_later_embedding` (row 2: mirrors of the
  accepted `circle_later_embedding`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- Transport of a surjective manifold derivative along an EVENTUAL equality of functions. -/
theorem surjective_mfderiv_congr_eventually_BAS {E H' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H' M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f f' : M → F} {x : M} (h : f =ᶠ[𝓝 x] f')
    (hs : Surjective (mfderiv I 𝓘(ℝ, F) f' x)) : Surjective (mfderiv I 𝓘(ℝ, F) f x) := by
  rw [h.mfderiv_eq]
  exact hs

/-- **A map into an immersed target is a submersion once its immersed image is**: if `ψ` is an
immersion at `F x` (injective differential) of a manifold whose model has the dimension of `E'`,
and `κ ∘ ψ ∘ F` has surjective differential at `x` for a continuous linear `κ : H → E'`, then `F`
has surjective differential at `x` (rank count: `range D(ψ ∘ F) ⊆ range Dψ` has dimension `d`). -/
theorem surjective_mfderiv_of_immersion_BAS {E H' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H' M] {EN HN : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [FiniteDimensional ℝ EN] [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {H E' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (F : M → N) (ψ : N → H) (κ : H →L[ℝ] E') {x : M}
    (hF : MDifferentiableAt I J F x) (hψ : MDifferentiableAt J 𝓘(ℝ, H) ψ (F x))
    (hψi : Injective (mfderiv J 𝓘(ℝ, H) ψ (F x)))
    (hdim : Module.finrank ℝ E' = Module.finrank ℝ EN)
    (hs : Surjective (mfderiv I 𝓘(ℝ, E') (fun q => κ (ψ (F q))) x)) :
    Surjective (mfderiv I J F x) := by
  have hκ : MDifferentiableAt 𝓘(ℝ, H) 𝓘(ℝ, E') κ (ψ (F x)) := κ.differentiableAt.mdifferentiableAt
  have hψF : MDifferentiableAt I 𝓘(ℝ, H) (fun q => ψ (F q)) x := hψ.comp x hF
  have h1 : mfderiv I 𝓘(ℝ, H) (fun q => ψ (F q)) x =
      (mfderiv J 𝓘(ℝ, H) ψ (F x)).comp (mfderiv I J F x) := mfderiv_comp x hψ hF
  have h2 : mfderiv I 𝓘(ℝ, E') (fun q => κ (ψ (F q))) x =
      (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E') κ (ψ (F x))).comp (mfderiv I 𝓘(ℝ, H) (fun q => ψ (F q)) x) :=
    mfderiv_comp x hκ hψF
  rw [h2, h1] at hs
  have : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, H) (ψ (F x))) :=
    inferInstanceAs (FiniteDimensional ℝ H)
  have : FiniteDimensional ℝ (TangentSpace J (F x)) := inferInstanceAs (FiniteDimensional ℝ EN)
  let Al := (mfderiv I J F x).toLinearMap
  let Dl := (mfderiv J 𝓘(ℝ, H) ψ (F x)).toLinearMap
  let Ll := (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E') κ (ψ (F x))).toLinearMap
  have hs2 : Surjective (Ll ∘ₗ (Dl ∘ₗ Al)) := hs
  have hRD : Module.finrank ℝ (LinearMap.range Dl) = Module.finrank ℝ EN :=
    LinearMap.finrank_range_of_inj hψi
  have hRT : LinearMap.range (Dl ∘ₗ Al) ≤ LinearMap.range Dl := LinearMap.range_comp_le_range Al Dl
  have hge : Module.finrank ℝ E' ≤ Module.finrank ℝ (LinearMap.range (Dl ∘ₗ Al)) := by
    have h3 : Module.finrank ℝ (LinearMap.range (Ll ∘ₗ (Dl ∘ₗ Al))) = Module.finrank ℝ E' := by
      rw [LinearMap.range_eq_top.mpr hs2, finrank_top]
      rfl
    rw [← h3, LinearMap.range_comp]
    exact Submodule.finrank_map_le _ _
  have heq : LinearMap.range (Dl ∘ₗ Al) = LinearMap.range Dl :=
    Submodule.eq_of_le_of_finrank_le hRT (by rw [hRD, ← hdim]; exact hge)
  intro t
  have ht : Dl t ∈ LinearMap.range Dl := ⟨t, rfl⟩
  rw [← heq] at ht
  obtain ⟨v, hv⟩ := ht
  exact ⟨v, hψi hv⟩

/-- charts of a chart-form subset are linear on the ambient space. -/
theorem linearChartedSpace_chartAt_apply_BAS {H E : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} (W : Set H)
    (κ : ι → H →L[ℝ] E) (φ : ι → E → H) (O : ι → Set H) (r : ℝ) (hO : ∀ i, IsOpen (O i))
    (hφs : ∀ i, ContDiffOn ℝ ∞ (φ i) (ball 0 r))
    (hφ : ∀ i, ∀ b ∈ ball (0 : E) r, φ i b ∈ W ∩ O i ∧ κ i (φ i b) = b)
    (hκ : ∀ i, ∀ y ∈ W ∩ O i, κ i y ∈ ball (0 : E) r ∧ φ i (κ i y) = y)
    (hcov : W ⊆ ⋃ i, O i) :
    let _ := linearChartedSpace_R74 W κ φ O r hO hφs hφ hκ hcov
    ∀ y : W, ∃ k : H →L[ℝ] E, ∀ z : W, chartAt E y z = k z.1 :=
  fun y => ⟨κ (linearChartIdx_R74 W O hcov y), fun _ => rfl⟩

/-- A map into a subset with linear charts is smooth iff its inclusion into the ambient space is. -/
theorem contMDiffAt_of_val_BAS {E H' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H' M] {H E₁ : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] {W : Set H}
    [ChartedSpace E₁ W] (hchart : ∀ y : W, ∃ k : H →L[ℝ] E₁, ∀ z : W, chartAt E₁ y z = k z.1)
    {F : M → W} {x : M} (hc : ContinuousAt F x)
    (hv : ContMDiffAt I 𝓘(ℝ, H) ∞ (fun q => (F q : H)) x) :
    ContMDiffAt I 𝓘(ℝ, E₁) ∞ F x := by
  rw [contMDiffAt_iff_target]
  refine ⟨hc, ?_⟩
  obtain ⟨k, hk⟩ := hchart (F x)
  have h : (extChartAt 𝓘(ℝ, E₁) (F x)) ∘ F = fun q => k (F q).1 := by
    funext q
    simp [extChartAt, hk]
  rw [h]
  exact k.contMDiff.contMDiffAt.comp x hv

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02Bases

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw} {R : Gaf02RoughData C}

open scoped Classical in
/-- **The corestriction `π_stE : U_st → W_st`**, extended by the junk value `y₀` outside the open
`U_st` (only its germ at points of `U_st` is used). -/
def finalCorestrict_BAS (B : Gaf02Bases C R) (st : Fin 3) (y₀ : ↥(C.finalBase_BAS st)) :
    X → ↥(C.finalBase_BAS st) := fun p =>
  if h : p ∈ gafStageDomain5_BAS P.toLocalChartPackets st then
    ⟨(gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p), B.later.mapsTo_final st h⟩
  else y₀

/-- On `U_st` the corestriction has the value `π_stE`. -/
theorem finalCorestrict_val_BAS (B : Gaf02Bases C R) (st : Fin 3) (y₀ : ↥(C.finalBase_BAS st))
    {p : X} (hp : p ∈ gafStageDomain5_BAS P.toLocalChartPackets st) :
    (B.finalCorestrict_BAS st y₀ p :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) =
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) := by
  simp [finalCorestrict_BAS, hp]

/-- The values of the corestriction agree with `π_stE` near a point of `U_st` (`U_st` is open). -/
theorem finalCorestrict_eventuallyEq_BAS (B : Gaf02Bases C R) (st : Fin 3)
    (y₀ : ↥(C.finalBase_BAS st)) {p : X}
    (hp : p ∈ gafStageDomain5_BAS P.toLocalChartPackets st) :
    (fun q => (B.finalCorestrict_BAS st y₀ q : BlockSpace
      (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) =ᶠ[𝓝 p]
      fun q => (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E q) :=
  Filter.eventually_of_mem ((isOpen_gafStageDomain5_R74 P.toLocalChartPackets st).mem_nhds hp)
    fun _ hq => B.finalCorestrict_val_BAS st y₀ hq

/-- The corestriction is continuous at every point of `U_st` and its inclusion is smooth there. -/
theorem finalCorestrict_cont_BAS (B : Gaf02Bases C R) (st : Fin 3) (y₀ : ↥(C.finalBase_BAS st))
    {p : X} (hp : p ∈ gafStageDomain5_BAS P.toLocalChartPackets st) :
    ContinuousAt (B.finalCorestrict_BAS st y₀) p ∧
      ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
        (fun q => (B.finalCorestrict_BAS st y₀ q : BlockSpace
          (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) p := by
  have hv := ((B.later.final_smooth st).contMDiffAt (x := p)).congr_of_eventuallyEq
    (B.finalCorestrict_eventuallyEq_BAS st y₀ hp)
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hv.continuousAt, hv⟩

/-- **`π_1E : U_1 → W_1` is a smooth submersion into the manifold `W_1`** (model `ℝ²`): at every
point `p` of FC33's exact threshold-5 domain `U_1` the corestriction is smooth and its manifold
derivative is onto. -/
theorem final_submersion_manifold_circle_BAS (B : Gaf02Bases C R) (y₀ : ↥(C.finalBase_BAS 0))
    {p : X} (hp : p ∈ gafStageDomain5_BAS P.toLocalChartPackets 0) :
    let _ := B.toSmoothStageBases74.circleChartedSpace
    ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (B.finalCorestrict_BAS 0 y₀) p ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (B.finalCorestrict_BAS 0 y₀) p) := by
  intro _
  have hF : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (B.finalCorestrict_BAS 0 y₀) p :=
    contMDiffAt_of_val_BAS (linearChartedSpace_chartAt_apply_BAS _ _ _ _ _ _ _ _ _ _)
      (B.finalCorestrict_cont_BAS 0 y₀ hp).1 (B.finalCorestrict_cont_BAS 0 y₀ hp).2
  refine ⟨hF, ?_⟩
  have hp' : ∃ j : P.toLocalChartFamily.circle.finite_centres.toFinset,
      p ∈ ball j.1 (200 * ρ j.1) ∧ ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 5 := hp
  refine hp'.elim fun j hj => ?_
  have hsub := (B.circle.spec.submersion j hj.1 hj.2).2
  obtain ⟨-, hval, hinj⟩ := B.toSmoothStageBases74.circle_isManifold
  refine surjective_mfderiv_of_immersion_BAS (B.finalCorestrict_BAS 0 y₀)
    (Subtype.val : ↥(C.finalBase_BAS 0) → _) ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
    (hF.mdifferentiableAt (by simp)) ((hval _).mdifferentiableAt (by simp)) (hinj _) rfl ?_
  refine surjective_mfderiv_congr_eventually_BAS ?_ hsub
  filter_upwards [B.finalCorestrict_eventuallyEq_BAS 0 y₀ hp] with q hq
  change ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
    (B.finalCorestrict_BAS 0 y₀ q).1 = _
  rw [hq]

/-- **`π_2E : U_2 → W_2` is a smooth submersion into the manifold `W_2`** (model `ℝ`; `U_2`
includes `η_{E'} < 5Δ`). -/
theorem final_submersion_manifold_edge_BAS (B : Gaf02Bases C R) (y₀ : ↥(C.finalBase_BAS 1))
    {p : X} (hp : p ∈ gafStageDomain5_BAS P.toLocalChartPackets 1) :
    let _ := B.toSmoothStageBases74.edgeChartedSpace
    ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (B.finalCorestrict_BAS 1 y₀) p ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (B.finalCorestrict_BAS 1 y₀) p) := by
  intro _
  have hF : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (B.finalCorestrict_BAS 1 y₀) p :=
    contMDiffAt_of_val_BAS (linearChartedSpace_chartAt_apply_BAS _ _ _ _ _ _ _ _ _ _)
      (B.finalCorestrict_cont_BAS 1 y₀ hp).1 (B.finalCorestrict_cont_BAS 1 y₀ hp).2
  refine ⟨hF, ?_⟩
  have hp' : ∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
      |P.edge.coord j.1 p| < 5 * Δ ∧ cgpHeight P.toLocalChartFamily p < 5 * Δ := hp
  refine hp'.elim fun j hj => ?_
  have hsub := (B.edge.spec.submersion j hj.1 hj.2.1 hj.2.2).2
  obtain ⟨-, hval, hinj⟩ := B.toSmoothStageBases74.edge_isManifold
  refine surjective_mfderiv_of_immersion_BAS (B.finalCorestrict_BAS 1 y₀)
    (Subtype.val : ↥(C.finalBase_BAS 1) → _)
    ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
    (hF.mdifferentiableAt (by simp)) ((hval _).mdifferentiableAt (by simp)) (hinj _) rfl ?_
  refine surjective_mfderiv_congr_eventually_BAS ?_ hsub
  filter_upwards [B.finalCorestrict_eventuallyEq_BAS 1 y₀ hp] with q hq
  change ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
    (B.finalCorestrict_BAS 1 y₀ q).1 = _
  rw [hq]

/-- **`π_3E : U_3 → W_3` is a smooth submersion into the manifold `W_3`** (model `ℝ`;
`π₃E = f₃`). -/
theorem final_submersion_manifold_slim_BAS (B : Gaf02Bases C R) (y₀ : ↥(C.finalBase_BAS 2))
    {p : X} (hp : p ∈ gafStageDomain5_BAS P.toLocalChartPackets 2) :
    let _ := B.toSmoothStageBases74.slimChartedSpace
    ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (B.finalCorestrict_BAS 2 y₀) p ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (B.finalCorestrict_BAS 2 y₀) p) := by
  intro _
  have hF : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (B.finalCorestrict_BAS 2 y₀) p :=
    contMDiffAt_of_val_BAS (linearChartedSpace_chartAt_apply_BAS _ _ _ _ _ _ _ _ _ _)
      (B.finalCorestrict_cont_BAS 2 y₀ hp).1 (B.finalCorestrict_cont_BAS 2 y₀ hp).2
  refine ⟨hF, ?_⟩
  have hp' : ∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| <
        5 * (10 ^ 5 * Δ) := hp
  refine hp'.elim fun j hj => ?_
  have hsub := (B.slim.spec.submersion j hj.1 hj.2).2
  obtain ⟨-, hval, hinj⟩ := B.toSmoothStageBases74.slim_isManifold
  refine surjective_mfderiv_of_immersion_BAS (B.finalCorestrict_BAS 2 y₀)
    (Subtype.val : ↥(C.finalBase_BAS 2) → _)
    ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
    (hF.mdifferentiableAt (by simp)) ((hval _).mdifferentiableAt (by simp)) (hinj _) rfl ?_
  refine surjective_mfderiv_congr_eventually_BAS ?_ hsub
  filter_upwards [B.finalCorestrict_eventuallyEq_BAS 2 y₀ hp] with q hq
  change ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
    (B.finalCorestrict_BAS 2 y₀ q).1 = _
  rw [hq]

end Gaf02Bases

namespace SmoothStageBasesOn74

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw}

/-- Row 2, edge (mirror of `circle_later_embedding`): on a native edge patch, `Θ₂` is the smooth
parametrization `Θ₂ ∘ chart_j` after the linear axis coordinate `κ_j`, with values in
`W₂ ∩ {marked j}` and inverse `chart_j ∘ κ_j` — a smooth embedding of the patch. -/
theorem edge_later_embedding (A : SmoothStageBasesOn74 C) (j : P.edge.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ C.edgePatch_BAS j) :
    C.Θ_BAS 1 w = (C.Θ_BAS 1 ∘ A.edgeChart j) (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
        (gafEdgeVector P.toLocalChartFamily P.zero j)) w) ∧
      C.Θ_BAS 1 w ∈ C.finalBase_BAS 1 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ ∧
      A.edgeChart j (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
        (gafEdgeVector P.toLocalChartFamily P.zero j)) (C.Θ_BAS 1 w)) = w := by
  obtain ⟨hb, hcw⟩ := A.charts.edge_patch j w hw
  have hpar := A.charts.edge_param j _ hb
  rw [hcw] at hpar
  refine ⟨by rw [Function.comp_apply, hcw], hpar.1, ?_⟩
  rw [hpar.2, hcw]

/-- Row 2, slim (mirror of `circle_later_embedding`; `Θ₃ = id`). -/
theorem slim_later_embedding (A : SmoothStageBasesOn74 C) (j : P.slim.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ C.slimPatch_BAS j) :
    C.Θ_BAS 2 w = (C.Θ_BAS 2 ∘ A.slimChart j) (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
        (gafSlimVector P.toLocalChartFamily P.zero j)) w) ∧
      C.Θ_BAS 2 w ∈ C.finalBase_BAS 2 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) ∧
      A.slimChart j (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
        (gafSlimVector P.toLocalChartFamily P.zero j)) (C.Θ_BAS 2 w)) = w := by
  obtain ⟨hb, hcw⟩ := A.charts.slim_patch j w hw
  have hpar := A.charts.slim_param j _ hb
  rw [hcw] at hpar
  refine ⟨by rw [Function.comp_apply, hcw], hpar.1, ?_⟩
  rw [hpar.2, hcw]

end SmoothStageBasesOn74

end DifferentialGeometry.Geometry.Collapse
