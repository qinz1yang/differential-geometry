import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageGeometrySmoothOBD
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRankTwoEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpBlocks

/-!
# `EdgeCutFacts74.rank_two` for the produced stages (lane S-BD2c)

Lane O-BD1 (by S-BD2c, suffix `_OBD`), group G8a (hlift, the cut facts `H`, `EdgeCutFacts74`,
first field). For ANY `P : BoundaryStageGeometry74b zc` whose edge inclusion is smooth:

* `pair_surjective_of_rank_two_OBD`: linear algebra: if `(M ∘ L₁, L₂)` has range of dimension `2`
  and `L₁` takes values in a line, then `(L₁, L₂)` is onto;
* `BoundaryStageGeometry74b.edge_rank_two_OBD`: the `rank_two` field of `EdgeCutFacts74`: the
  chain rule `d(f₂, T) = (dι × id) ∘ d(proj, T)` on the restricted bundle and
  `rank d(f₂, T) = 2` on `T = 4Δ` (`BoundaryEdgeParent_BIFc.edgeParent_rank_two`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **Rank two from a line**: if `L₁` takes values in a line `X` and `(M ∘ L₁, L₂)` has a
two-dimensional range, then `(L₁, L₂)` is onto `X × ℝ`. -/
theorem pair_surjective_of_rank_two_OBD {U X Y : Type*} [AddCommGroup U] [Module ℝ U]
    [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (L₁ : U →ₗ[ℝ] X) (L₂ : U →ₗ[ℝ] ℝ) (M : X →ₗ[ℝ] Y) (hX : Module.finrank ℝ X = 1)
    (h : Module.finrank ℝ (LinearMap.range (LinearMap.prod (M.comp L₁) L₂)) = 2) :
    Surjective fun v => (L₁ v, L₂ v) := by
  have hcomp : LinearMap.prod (M.comp L₁) L₂ = (LinearMap.prodMap M LinearMap.id).comp
      (LinearMap.prod L₁ L₂) := by
    ext v <;> simp
  rw [hcomp, LinearMap.range_comp] at h
  have h1 := Submodule.finrank_map_le (LinearMap.prodMap M (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
    (LinearMap.range (LinearMap.prod L₁ L₂))
  have h2 := Submodule.finrank_le (LinearMap.range (LinearMap.prod L₁ L₂))
  rw [Module.finrank_prod, hX, Module.finrank_self] at h2
  have h3 : LinearMap.range (LinearMap.prod L₁ L₂) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by
      rw [Module.finrank_prod, hX, Module.finrank_self]
      omega)
  intro p
  have : p ∈ LinearMap.range (LinearMap.prod L₁ L₂) := by rw [h3]; trivial
  obtain ⟨v, hv⟩ := this
  exact ⟨v, hv⟩

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

section RankTwo

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
  {dec : BoundaryActualDecompositionV2b C} {zc : BoundaryZeroCuspExit74b C dec}
  (P : BoundaryStageGeometry74b zc)

/-- **`EdgeCutFacts74.rank_two` for the produced stages**: on the vertical level `T = 4Δ` of the
restricted edge bundle, `d(proj, T)` is onto `ℝ × ℝ`. -/
theorem BoundaryStageGeometry74b.edge_rank_two_OBD
    (hι : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      P.ιedge) :
    ∀ x : P.cut.edgeSource, P.cut.edgeHeight x = P.stageGeometry.edge.level →
      Surjective fun v : TangentSpace W.model (x : W.Carrier) =>
        (mfderiv W.model (𝓡 1) (P.stageGeometry.edge.restrictProj P.cut.edgeBaseOpen) x v,
          mfderiv W.model 𝓘(ℝ, ℝ) P.cut.edgeHeight x v) := by
  intro x hx
  have hxpar : (x : W.Carrier) ∈ P.edge.parent := P.edge.restrictParent_le _ x.2
  have hxp : (x : W.Carrier) ∈ dec.bases.edgeParent := by
    rw [← P.edge_ident.parent_eq]
    exact hxpar
  have hT : C.heightRatio (x : W.Carrier) = 4 * Δ := by
    have h1 : P.cut.edgeHeight x = C.heightRatio (x : W.Carrier) := P.edge_height _
    have h2 : P.stageGeometry.edge.level = 4 * Δ := P.edge_level
    rw [← h1, hx, h2]
  have hrk : C.edgePairRank_BIFc (x : W.Carrier) = 2 :=
    dec.bases.parent.edgeParent_rank_two _ hxp hT
  let Pj := P.stageGeometry.edge.restrictProj P.cut.edgeBaseOpen
  have hPj : ContMDiff W.model (𝓡 1) ∞ Pj := P.stageGeometry.edge.restrictProj_smooth _
  let ιV : P.cut.edgeBaseOpen → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
    fun c => P.ιedge c.1
  have hιV : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ ιV :=
    hι.comp (contMDiff_subtype_val (I := 𝓡 1) (U := P.cut.edgeBaseOpen))
  let Ψ : P.cut.edgeSource → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ :=
    fun z => (ιV (Pj z), P.cut.edgeHeight z)
  have hΨ : ContMDiff W.model 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count) × ℝ) ∞ Ψ :=
    (hιV.comp hPj).prodMk_space P.cut.edgeHeight_smooth
  have hsm := dec.bases.parent.edgeParent_smooth _ hxp
  have hpair : mvfderiv W.model Ψ x = mvfderiv W.model
      (fun q => (C.stageMap 1 q, C.heightRatio q)) (x : W.Carrier) :=
    mvfderiv_comp_subtype_val_EFE P.cut.edgeSource
      (f := fun q => (C.stageMap 1 q, C.heightRatio q)) (g := Ψ)
      (fun z => Prod.ext (P.edge_ident.proj_eq (P.stageGeometry.edge.restrictIncl _ z))
        (P.edge_height _)) x
      ((hsm.1.prodMk_space hsm.2).mdifferentiableAt (by simp))
  have hcomp : ∀ v, mvfderiv W.model Ψ x v = (mvfderiv W.model (fun z => ιV (Pj z)) x v,
      mvfderiv W.model P.cut.edgeHeight x v) := by
    intro v
    refine Prod.ext ?_ ?_
    · exact (mvfderiv_clm_comp_apply_EDPE (ContinuousLinearMap.fst ℝ _ ℝ)
        (hΨ.mdifferentiableAt (by simp)) v).symm
    · exact (mvfderiv_clm_comp_apply_EDPE (ContinuousLinearMap.snd ℝ _ ℝ)
        (hΨ.mdifferentiableAt (by simp)) v).symm
  have hfirst : ∀ v, mvfderiv W.model (fun z => ιV (Pj z)) x v =
      mvfderiv (𝓡 1) ιV (Pj x) (mfderiv W.model (𝓡 1) Pj x v) := fun v =>
    mvfderiv_comp_apply x (hιV.mdifferentiableAt (by simp)) (hPj.mdifferentiableAt (by simp)) v
  let M : TangentSpace (𝓡 1) (Pj x) →ₗ[ℝ] BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count) := (mvfderiv (𝓡 1) ιV (Pj x)).toLinearMap
  let L₁ : TangentSpace W.model x →ₗ[ℝ] TangentSpace (𝓡 1) (Pj x) :=
    (mfderiv W.model (𝓡 1) Pj x).toLinearMap
  let L₂ : TangentSpace W.model x →ₗ[ℝ] ℝ :=
    (mfderiv W.model 𝓘(ℝ, ℝ) P.cut.edgeHeight x).toLinearMap
  have hlin : (mvfderiv W.model (fun q => (C.stageMap 1 q, C.heightRatio q))
      (x : W.Carrier)).toLinearMap = LinearMap.prod (M.comp L₁) L₂ := by
    rw [← hpair]
    refine LinearMap.ext fun v => ?_
    change mvfderiv W.model Ψ x v = _
    rw [hcomp v, hfirst v]
    rfl
  have hX : Module.finrank ℝ (TangentSpace (𝓡 1) (Pj x)) = 1 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1
    simp
  have hrank : Module.finrank ℝ (LinearMap.range (LinearMap.prod (M.comp L₁) L₂)) = 2 := by
    rw [← hlin]
    exact hrk
  exact pair_surjective_of_rank_two_OBD L₁ L₂ M hX hrank

end RankTwo

end DifferentialGeometry.Geometry.Collapse
