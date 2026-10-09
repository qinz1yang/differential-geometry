import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCompactDomainEFE
import DifferentialGeometry.Topology.Manifold.LinearChartMaps74

/-!
# EDP04's rank two on the abstract edge base (`EdgeBundle.rank_two`), group G9

Lane S-EDP-FDC4, group G9 (first part). Blueprint `master207B.tex`, EDP04 (B:6949–7013), EDP05
(B:7080–7084: "EDP04 gives independence of `dg_i` and `dT` at the vertical boundary") and EDP06
(B:7125–7129). On a chain `Ĉ : Gaf02ChainE L …` with the smooth stage bases `A` (D74-2) and the
abstract edge base `B₂ ⊆ W₂` (`edgeBaseOpens_EFE`, model `𝓡 1`):

* `surjective_pair_of_comp_EFE` (kernel): if `u : B → ℝ` is a linear functional on a line `B`, and
  every pair `(r, s)` of reals is `(u (L₁ v), L₂ v)` for some `v`, then `v ↦ (L₁ v, L₂ v)` is onto
  `B × ℝ` (the descended differential of a coordinate is invertible, hence the pair on the
  abstract base is onto);
* `mvfderiv_comp_subtype_val_EFE`: the vector-valued differential on an open subtype is the
  ambient one;
* `edge_rank_two_EFE` (**`EdgeBundle.rank_two` of the actual chain**): at every point `x` of the
  edge source with `T x = 4Δ` the pair `(d f₂, dT)` is onto `T_{f₂ x} B₂ × ℝ`. Proof: the marker
  is exact (`edgeBase_marker_exact_EDP23`), so `|g_k x| < 4Δ` for the witnessing index, the
  localization gives the ball and `|η_k|`, `t` bounds, and `edge_vertical_rank_EDPE` makes
  `(g_k, T)` onto `ℝ²`; `g_k = ℓ_k ∘ ι ∘ f₂` with `ι : B₂ → block space` smooth and `ℓ_k` linear,
  so the descended functional `u = ℓ_k ∘ dι` is onto `ℝ` and the kernel applies;
* `edge_corner_independence_EFE` (EDP05 / EDP06's independence): for a function `φ` on `B₂` with
  `dφ ≠ 0` at `f₂ x`, the pair `(d(φ ∘ f₂), dT)` is onto `ℝ²` at `x` (`T x = 4Δ`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **Kernel (descended invertibility, pair form).** `B` a line, `u : B → ℝ` linear, and every pair
`(r, s)` realized as `(u (L₁ v), L₂ v)`: then `v ↦ (L₁ v, L₂ v)` is onto `B × ℝ`. -/
theorem surjective_pair_of_comp_EFE {V B : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup B]
    [Module ℝ B] (hB : Module.finrank ℝ B = 1) (L₁ : V →ₗ[ℝ] B) (L₂ : V →ₗ[ℝ] ℝ)
    (u : B →ₗ[ℝ] ℝ) (h : ∀ r s : ℝ, ∃ v, u (L₁ v) = r ∧ L₂ v = s) :
    Function.Surjective (fun v => (L₁ v, L₂ v)) := by
  obtain ⟨v₀, hv₀, -⟩ := h 1 0
  have hb₀ : L₁ v₀ ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv₀
    exact zero_ne_one hv₀
  rintro ⟨b, s⟩
  obtain ⟨v, hv1, hv2⟩ := h (u b) s
  refine ⟨v, Prod.ext ?_ hv2⟩
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (L₁ v₀) hb₀).mp hB (L₁ v)
  obtain ⟨a', ha'⟩ := (finrank_eq_one_iff_of_nonzero' (L₁ v₀) hb₀).mp hB b
  have h1 : u (L₁ v) = a := by rw [← ha, map_smul, hv₀, smul_eq_mul, mul_one]
  have h2 : u b = a' := by rw [← ha', map_smul, hv₀, smul_eq_mul, mul_one]
  have : a = a' := h1.symm.trans (hv1.trans h2)
  change L₁ v = b
  rw [← ha, ← ha', this]

/-- **Kernel (a functional that is onto `ℝ` along a map into a line).** If `B` is a line and
`u (L v)` takes every real value, then `L` is onto `B`. -/
theorem surjective_of_comp_functional_EFE {V B : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup B] [Module ℝ B] (hB : Module.finrank ℝ B = 1) (L : V →ₗ[ℝ] B)
    (u : B →ₗ[ℝ] ℝ) (h : ∀ r : ℝ, ∃ v, u (L v) = r) : Function.Surjective L := by
  obtain ⟨v₀, hv₀⟩ := h 1
  have hb₀ : L v₀ ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv₀
    exact zero_ne_one hv₀
  intro b
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (L v₀) hb₀).mp hB b
  refine ⟨a • v₀, ?_⟩
  rw [map_smul]
  exact ha

/-- **Kernel (face independence on a line).** If `(L₁, L₂)` is onto `B × ℝ` and `u : B → ℝ` is a
nonzero functional, then `(u ∘ L₁, L₂)` is onto `ℝ × ℝ` (EDP05's independence of `d(b ∘ f₂)` and
`dT` from the rank two and `db ≠ 0`). -/
theorem surjective_pair_comp_functional_EFE {V B : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup B] [Module ℝ B] (L₁ : V →ₗ[ℝ] B) (L₂ : V →ₗ[ℝ] ℝ)
    (hL : Function.Surjective (fun v => (L₁ v, L₂ v))) (u : B →ₗ[ℝ] ℝ) (hu : u ≠ 0) :
    Function.Surjective (fun v => (u (L₁ v), L₂ v)) := by
  obtain ⟨b₀, hb₀⟩ : ∃ b, u b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu (LinearMap.ext hcon)
  rintro ⟨r, s⟩
  obtain ⟨v, hv⟩ := hL ((r / u b₀) • b₀, s)
  have h2 : L₂ v = s := congrArg Prod.snd hv
  refine ⟨v, Prod.ext ?_ h2⟩
  have h1 : L₁ v = (r / u b₀) • b₀ := congrArg Prod.fst hv
  change u (L₁ v) = r
  rw [h1, map_smul, smul_eq_mul, div_mul_cancel₀ _ hb₀]

section Subtype

variable {EX HX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {I : ModelWithCorners ℝ EX HX} {Mf : Type*} [TopologicalSpace Mf] [ChartedSpace HX Mf]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The vector-valued differential on an open subtype is the ambient one. -/
theorem mvfderiv_comp_subtype_val_EFE (U : TopologicalSpace.Opens Mf) {f : Mf → V}
    {g : U → V} (hg : ∀ z : U, g z = f z) (x : U)
    (hf : MDifferentiableAt I 𝓘(ℝ, V) f (x : Mf)) :
    mvfderiv I g x = mvfderiv I f (x : Mf) := by
  unfold mvfderiv
  rw [hg x, mfderiv_comp_subtype_val_R74 U hg x hf]
  rfl

end Subtype

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainE

variable {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- The edge coordinate `g_k = u_k(E)/ρ_k` of the chain (EDP03's `g_i`). -/
def edgeCoordG_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (k : L.edge.finite_centres.toFinset) : X → ℝ := fun z =>
  EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero k (Ĉ.toChain.E z)) /
    ρ k.1

/-- `g_k` is smooth on `X`. -/
theorem contMDiff_edgeCoordG_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (k : L.edge.finite_centres.toFinset) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (Ĉ.edgeCoordG_EFE k) :=
  (Ĉ.toChain.final_smooth_EDPE).2.2.2.2 k

/-- The global height `T` is smooth on `X`. -/
theorem contMDiff_edgeHeightGlobal_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ Ĉ.edgeHeightGlobal_EFE :=
  (Ĉ.toChain.final_smooth_EDPE).2.2.2.1

/-- **(g_k, T) is onto `ℝ²` at a point of the vertical face** (E3 level): at `x` in the edge source
with `T x = 4Δ` there is a witnessing edge index `k` such that every pair of reals is
`(d g_k(v), dT(v))` for some tangent vector `v` (EDP04's final-time rank
`edge_vertical_rank_EDPE`, with `|g_k x| < 4Δ` from the exact marker). -/
theorem edge_coord_height_surj_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) (x : Ĉ.edgeSource_EFE) (hx : Ĉ.edgeHeight_EFE x = 4 * Δ) :
    ∃ k : L.edge.finite_centres.toFinset, ∀ r s : ℝ, ∃ v : TangentSpace 𝓘(ℝ, E3) (x : X),
      mvfderiv 𝓘(ℝ, E3) (Ĉ.edgeCoordG_EFE k) x.1 v = r ∧
        mvfderiv 𝓘(ℝ, E3) Ĉ.edgeHeightGlobal_EFE x.1 v = s := by
  have hxs := Ĉ.edgeSource_mem_EFE x.2
  obtain ⟨k, hv, hu₀⟩ := hxs.2
  have hΔ0 : 0 < Δ := by linarith
  have hk : k.1 ∈ L.edge.centres := (Set.Finite.mem_toFinset _).mp k.2
  have hrk := hρ k.1
  have hmark := Ĉ.edgeBase_marker_exact_EDP23 hΔ2 k hxs.1 hv.le hu₀
  have hu : ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
        (Ĉ.toChain.E x.1))‖ < 4 * Δ * ρ k.1 := by
    rw [hmark] at hu₀
    exact hu₀
  obtain ⟨hball, hη, ht, -⟩ := Ĉ.toChain.stageTwo_ratio_localization_FDC hΔ2 k hv hu₀
    (Or.inr ⟨(Ĉ.toChain.scale_pos x.1).2, hx.le⟩)
  have hga : |Ĉ.edgeCoordG_EFE k x.1| < 4 * Δ := by
    change |EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero k
      (Ĉ.toChain.E x.1)) / ρ k.1| < 4 * Δ
    rw [abs_div, abs_of_pos hrk, div_lt_iff₀ hrk]
    rw [gafStageQ_edgeVector_FDC L.toLocalChartPackets k (Ĉ.toChain.E x.1)] at hu
    exact lt_of_le_of_lt (abs_proj_zero_le_norm_EFC _) hu
  obtain ⟨-, -, -, hsurj, -⟩ := Ĉ.toChain.edge_vertical_rank_EDPE (Ĉ.rough.cw_nonneg 0)
    (Ĉ.rough.sigma_le 0).le hc hϑ hε0 hε hγc hγc1 hβc1 hk x.1 hball
    (by linarith [hη]) (by linarith [ht]) hga hx
  have hfc : ∀ j, ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (![Ĉ.edgeCoordG_EFE k, Ĉ.edgeHeightGlobal_EFE] j) x.1 := fun j => by
    fin_cases j
    · exact (Ĉ.contMDiff_edgeCoordG_EFE k).contMDiffAt
    · exact Ĉ.contMDiff_edgeHeightGlobal_EFE.contMDiffAt
  refine ⟨k, fun r s => ?_⟩
  obtain ⟨v, hv0⟩ := hsurj (WithLp.toLp 2 ![r, s])
  have hv' : mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates
      ![Ĉ.edgeCoordG_EFE k, Ĉ.edgeHeightGlobal_EFE]) x.1 v = WithLp.toLp 2 ![r, s] := hv0
  refine ⟨v, ?_, ?_⟩
  · have h0 := edgeReferenceCoordinates_derivative (I := 𝓘(ℝ, E3))
      (f := ![Ĉ.edgeCoordG_EFE k, Ĉ.edgeHeightGlobal_EFE]) hfc v 0
    rw [hv'] at h0
    simpa using h0.symm
  · have h0 := edgeReferenceCoordinates_derivative (I := 𝓘(ℝ, E3))
      (f := ![Ĉ.edgeCoordG_EFE k, Ĉ.edgeHeightGlobal_EFE]) hfc v 1
    rw [hv'] at h0
    simpa using h0.symm

/-- **The coordinate `g_k` descends to a linear functional on the tangent line of `B₂`**: `g_k =
ℓ_k ∘ ι ∘ f₂` with `ι : B₂ → block space` smooth and `ℓ_k` linear, so `d g_k = u ∘ d f₂` with
`u = ℓ_k ∘ dι`. -/
theorem exists_descended_functional_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) (k : L.edge.finite_centres.toFinset)
    (x : Ĉ.edgeSource_EFE) :
    let _ := A.edgeChartedSpace1
    ∃ u : TangentSpace (𝓡 1) (Ĉ.edgeProj_EFE x) →ₗ[ℝ] ℝ,
      ∀ v : TangentSpace 𝓘(ℝ, E3) (x : X),
        u (mfderiv 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE x v) =
          mvfderiv 𝓘(ℝ, E3) (Ĉ.edgeCoordG_EFE k) x.1 v := by
  intro _
  let valB : Ĉ.edgeBaseOpens_EFE → BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) :=
    fun cc => ((cc : Ĉ.toChain.finalBase_BAS 1) :
      BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))
  have hval : ContMDiff (𝓡 1)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)) ∞ valB :=
    (A.edge_isManifold1.2.1).comp (contMDiff_subtype_val (I := 𝓡 1))
  have hproj := Ĉ.edgeProj_contMDiff_EFE A
  let ℓ : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) →L[ℝ] ℝ :=
    (ρ k.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k)
  have hℓ : ∀ z : Ĉ.edgeSource_EFE, ℓ (valB (Ĉ.edgeProj_EFE z)) = Ĉ.edgeCoordG_EFE k z.1 :=
    fun z => by
    change (ρ k.1)⁻¹ * EuclideanSpace.proj (0 : Fin 2) (blockVectorCLM (V := fun _ :
      CGPTag L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl k)))
        ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E z.1))) =
      EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero k
        (Ĉ.toChain.E z.1)) / ρ k.1
    rw [gafStageQ_edgeVector_FDC L.toLocalChartPackets k (Ĉ.toChain.E z.1), div_eq_inv_mul]
    rfl
  have hmd : MDifferentiableAt (𝓡 1) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero
      => ℝ²)) valB (Ĉ.edgeProj_EFE x) := (hval (Ĉ.edgeProj_EFE x)).mdifferentiableAt (by simp)
  have hpd : MDifferentiableAt 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE x :=
    (hproj x).mdifferentiableAt (by simp)
  have hPv : MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))
      (valB ∘ Ĉ.edgeProj_EFE) x := hmd.comp x hpd
  have hchain : mvfderiv 𝓘(ℝ, E3) (valB ∘ Ĉ.edgeProj_EFE) x =
      (mvfderiv (𝓡 1) valB (Ĉ.edgeProj_EFE x)).comp
        (mfderiv 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE x) := mvfderiv_comp x hmd hpd
  let u : TangentSpace (𝓡 1) (Ĉ.edgeProj_EFE x) →L[ℝ] ℝ :=
    ℓ.comp (mvfderiv (𝓡 1) valB (Ĉ.edgeProj_EFE x))
  refine ⟨u.toLinearMap, fun v => ?_⟩
  have h1 : mvfderiv 𝓘(ℝ, E3) (fun z : Ĉ.edgeSource_EFE => Ĉ.edgeCoordG_EFE k z.1) x =
      mvfderiv 𝓘(ℝ, E3) (Ĉ.edgeCoordG_EFE k) x.1 :=
    mvfderiv_comp_subtype_val_EFE Ĉ.edgeSource_EFE (fun _ => rfl) x
      ((Ĉ.contMDiff_edgeCoordG_EFE k).contMDiffAt.mdifferentiableAt (by simp))
  have h2 : (fun z : Ĉ.edgeSource_EFE => ℓ ((valB ∘ Ĉ.edgeProj_EFE) z)) =
      fun z : Ĉ.edgeSource_EFE => Ĉ.edgeCoordG_EFE k z.1 := funext fun z => hℓ z
  have h3 := mvfderiv_clm_comp_apply_EDPE (I := 𝓘(ℝ, E3)) ℓ hPv v
  calc u (mfderiv 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE x v)
      = ℓ (mvfderiv 𝓘(ℝ, E3) (valB ∘ Ĉ.edgeProj_EFE) x v) := by
        rw [hchain]
        rfl
    _ = mvfderiv 𝓘(ℝ, E3) (fun z : Ĉ.edgeSource_EFE => ℓ ((valB ∘ Ĉ.edgeProj_EFE) z)) x v :=
        h3.symm
    _ = mvfderiv 𝓘(ℝ, E3) (fun z : Ĉ.edgeSource_EFE => Ĉ.edgeCoordG_EFE k z.1) x v := by
        rw [h2]
    _ = mvfderiv 𝓘(ℝ, E3) (Ĉ.edgeCoordG_EFE k) x.1 v := by
        rw [h1]
        rfl

/-- **The descended functional is invertible on the line `T_{f₂ x} B₂`**: if the coordinate `g_k`
and the height `T` realize every pair of reals, then `(d f₂, dT)` is onto `T_{f₂ x} B₂ × ℝ`. -/
theorem edge_pair_surjective_of_coord_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) (k : L.edge.finite_centres.toFinset)
    (x : Ĉ.edgeSource_EFE)
    (hsurj2 : ∀ r s : ℝ, ∃ v : TangentSpace 𝓘(ℝ, E3) (x : X),
      mvfderiv 𝓘(ℝ, E3) (Ĉ.edgeCoordG_EFE k) x.1 v = r ∧
        mvfderiv 𝓘(ℝ, E3) Ĉ.edgeHeightGlobal_EFE x.1 v = s) :
    let _ := A.edgeChartedSpace1
    Function.Surjective (fun v : TangentSpace 𝓘(ℝ, E3) (x : X) =>
      (mfderiv 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE x v,
        mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) Ĉ.edgeHeight_EFE x v)) := by
  intro _
  obtain ⟨u, hu_eq⟩ := Ĉ.exists_descended_functional_EFE A k x
  have hT_eq : ∀ v, mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) Ĉ.edgeHeight_EFE x v =
      mvfderiv 𝓘(ℝ, E3) Ĉ.edgeHeightGlobal_EFE x.1 v := fun v => by
    have h1 : mvfderiv 𝓘(ℝ, E3) Ĉ.edgeHeight_EFE x =
        mvfderiv 𝓘(ℝ, E3) Ĉ.edgeHeightGlobal_EFE x.1 :=
      mvfderiv_comp_subtype_val_EFE Ĉ.edgeSource_EFE (fun _ => rfl) x
        (Ĉ.contMDiff_edgeHeightGlobal_EFE.contMDiffAt.mdifferentiableAt (by simp))
    rw [← h1]
    rfl
  have hB : Module.finrank ℝ (TangentSpace (𝓡 1) (Ĉ.edgeProj_EFE x)) = 1 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1
    simp
  refine surjective_pair_of_comp_EFE hB
    (mfderiv 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE x).toLinearMap
    (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) Ĉ.edgeHeight_EFE x).toLinearMap u ?_
  intro r s
  obtain ⟨v, hv1, hv2⟩ := hsurj2 r s
  exact ⟨v, (hu_eq v).trans hv1, (hT_eq v).trans hv2⟩

/-- **`EdgeBundle.proj_submersion` of the actual chain**: `f₂ = π₂E : X₂ → B₂` is a submersion at
every point of the edge source (the threshold-5 chart-form submersion of D74-2 gives a surjective
differential of `g_k = ℓ_k ∘ f₂`; the descended functional on the line `T_{f₂ x} B₂` is nonzero,
hence injective, hence `d f₂` is onto). -/
theorem edge_proj_submersion_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) (x : Ĉ.edgeSource_EFE) :
    let _ := A.edgeChartedSpace1
    Function.Surjective (mfderiv 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE x) := by
  intro _
  obtain ⟨⟨k, hk, hη, ht⟩, -⟩ := x.2
  obtain ⟨u, hu_eq⟩ := Ĉ.exists_descended_functional_EFE A k x
  have hsub := (A.proj.edge_submersion k hk hη ht).2
  have hfun : (fun q => ((ρ k.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily
      L.zero k)) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E q))) =
      Ĉ.edgeCoordG_EFE k := funext fun q => by
    change (ρ k.1)⁻¹ * EuclideanSpace.proj (0 : Fin 2) (blockVectorCLM (V := fun _ :
      CGPTag L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl k)))
        ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E q))) =
      EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero k
        (Ĉ.toChain.E q)) / ρ k.1
    rw [gafStageQ_edgeVector_FDC L.toLocalChartPackets k (Ĉ.toChain.E q), div_eq_inv_mul]
    rfl
  have hsub' : Function.Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (Ĉ.edgeCoordG_EFE k) x.1) :=
    (congrArg (fun f => Function.Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) f x.1)) hfun).mp hsub
  have hB : Module.finrank ℝ (TangentSpace (𝓡 1) (Ĉ.edgeProj_EFE x)) = 1 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1
    simp
  refine surjective_of_comp_functional_EFE hB
    (mfderiv 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE x).toLinearMap u ?_
  intro r
  obtain ⟨v, hv⟩ := hsub' r
  exact ⟨v, (hu_eq v).trans hv⟩

/-- **`EdgeBundle.rank_two` of the actual chain** (EDP04's final-time rank, B:6995–7013 and
B:7080–7084): at a point `x` of the edge source with `T x = 4Δ`, the pair
`(d f₂, dT) : T_x X → T_{f₂ x} B₂ × ℝ` is onto. -/
theorem edge_rank_two_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) (hΔ2 : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) (x : Ĉ.edgeSource_EFE) (hx : Ĉ.edgeHeight_EFE x = 4 * Δ) :
    let _ := A.edgeChartedSpace1
    Function.Surjective (fun v : TangentSpace 𝓘(ℝ, E3) (x : X) =>
      (mfderiv 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE x v,
        mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) Ĉ.edgeHeight_EFE x v)) := by
  obtain ⟨k, hk⟩ := Ĉ.edge_coord_height_surj_EFE hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 x hx
  exact Ĉ.edge_pair_surjective_of_coord_EFE A k x hk

/-- **EDP05's face independence at the vertical boundary** (B:7080–7084; also EDP06, B:7125–7129):
for a function `φ` on `B₂` with `dφ ≠ 0` at `f₂ x`, the differentials of `φ ∘ f₂` and of `T` are
independent at every `x` of the edge source with `T x = 4Δ`. -/
theorem edge_corner_independence_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) (hΔ2 : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) (x : Ĉ.edgeSource_EFE) (hx : Ĉ.edgeHeight_EFE x = 4 * Δ) :
    let _ := A.edgeChartedSpace1
    ∀ φ : Ĉ.edgeBaseOpens_EFE → ℝ, MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) φ (Ĉ.edgeProj_EFE x) →
      mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ (Ĉ.edgeProj_EFE x) ≠ 0 →
      Function.Surjective (fun v : TangentSpace 𝓘(ℝ, E3) (x : X) =>
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (φ ∘ Ĉ.edgeProj_EFE) x v,
          mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) Ĉ.edgeHeight_EFE x v)) := by
  intro _ φ hφ hφ0
  have hr := Ĉ.edge_rank_two_EFE A hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 x hx
  have hpd : MDifferentiableAt 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE x :=
    ((Ĉ.edgeProj_contMDiff_EFE A) x).mdifferentiableAt (by simp)
  have hcomp : ∀ v, mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (φ ∘ Ĉ.edgeProj_EFE) x v =
      mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ (Ĉ.edgeProj_EFE x)
        (mfderiv 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE x v) := fun v => by
    rw [mfderiv_comp x hφ hpd]
    rfl
  have h := surjective_pair_comp_functional_EFE
    (mfderiv 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE x).toLinearMap
    (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) Ĉ.edgeHeight_EFE x).toLinearMap hr
    (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ (Ĉ.edgeProj_EFE x)).toLinearMap
    (fun h0 => hφ0 (ContinuousLinearMap.ext fun v => LinearMap.congr_fun h0 v))
  intro p
  obtain ⟨v, hv⟩ := h p
  have h1 := congrArg Prod.fst hv
  have h2 := congrArg Prod.snd hv
  exact ⟨v, Prod.ext ((hcomp v).trans h1) h2⟩

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
