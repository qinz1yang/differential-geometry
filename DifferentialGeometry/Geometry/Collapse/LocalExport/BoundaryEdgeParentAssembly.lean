import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEExits
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceBasesV2

/-!
# G12 / G16: the assembly of the open edge parent (S-BAUG-D, part a)

Target `BoundaryEdgeParent_BIFc` (`LE/BoundaryInterfaceBasesV2.lean`, review 69 D69-7) on the
enhanced chain `C : BoundaryGaf02ChainE DP …`; closed twin `Gaf02Chain.vertical_eq_FDC`,
`Gaf02Chain.edge_vertical_rank_EDPE`.

* `BoundaryGaf02ChainE.stageMap_contMDiff_BAUGD`, `heightRatio_contMDiff_BAUGD`: `f_j = π_j ∘ E`
  and `T = A/s` are smooth on ALL of `W` (A3a, `scale_pos`), so the smoothness field of the
  parent holds for every parent set;
* `mvfderiv_pair_BAUGD`: the differential of a pair is the pair of differentials;
* `finrank_range_prod_eq_two_BAUGD` (linear algebra): `rank L = 1` and `(μ ∘ L, ℓ)` onto `ℝ × ℝ`
  give `rank (L, ℓ) = 2`;
* `BoundaryGaf02ChainE.edgePairRank_eq_two_of_surjective_BAUGD`: rank one of `df₂` and a linear
  functional `ℓ` of `f₂` with `(d(ℓ ∘ f₂), dT)` onto at `p` give `rank d(f₂, T) = 2`;
* `BoundaryEdgeParent_BIFc.ofRim_BAUGD`: the parent structure from an open parent domain, the cut
  equality, the inclusion into `f₂⁻¹ B₂`, rank one on it and the rim surjectivity (the geometric
  input, produced in `LE/BoundaryEdgeRimSurjective…`).
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
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- `rank L = 1` and `(μ ∘ L, ℓ)` onto `ℝ × ℝ` give `rank (L, ℓ) = 2`. -/
theorem finrank_range_prod_eq_two_BAUGD {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup H] [Module ℝ H] (L : V →ₗ[ℝ] H) (ℓ : V →ₗ[ℝ] ℝ) (μ' : H →ₗ[ℝ] ℝ)
    (h1 : Module.finrank ℝ (LinearMap.range L) = 1)
    (hs : Function.Surjective (fun v => (μ' (L v), ℓ v))) :
    Module.finrank ℝ (LinearMap.range (L.prod ℓ)) = 2 := by
  have hfin1 : Module.Finite ℝ (LinearMap.range L) := Module.finite_of_finrank_pos (by omega)
  have hmem : ∀ x : LinearMap.range (L.prod ℓ), x.1.1 ∈ LinearMap.range L := by
    rintro ⟨_, v, rfl⟩
    exact ⟨v, rfl⟩
  let f : LinearMap.range (L.prod ℓ) →ₗ[ℝ] (LinearMap.range L) × ℝ :=
    (LinearMap.codRestrict (LinearMap.range L)
      (LinearMap.fst ℝ H ℝ ∘ₗ (LinearMap.range (L.prod ℓ)).subtype) hmem).prod
      (LinearMap.snd ℝ H ℝ ∘ₗ (LinearMap.range (L.prod ℓ)).subtype)
  have hf : Function.Injective f := by
    intro x y hxy
    have h1' := congrArg (fun z : (LinearMap.range L) × ℝ => z.1.1) hxy
    have h2' := congrArg (fun z : (LinearMap.range L) × ℝ => z.2) hxy
    exact Subtype.ext (Prod.ext h1' h2')
  have hle : Module.finrank ℝ (LinearMap.range (L.prod ℓ)) ≤ 2 := by
    have := LinearMap.finrank_le_finrank_of_injective hf
    rw [Module.finrank_prod, h1, Module.finrank_self] at this
    exact this
  have hfin : Module.Finite ℝ (LinearMap.range (L.prod ℓ)) := Module.Finite.of_injective f hf
  let Φ : H × ℝ →ₗ[ℝ] ℝ × ℝ := μ'.prodMap LinearMap.id
  let f2 : LinearMap.range (L.prod ℓ) →ₗ[ℝ] ℝ × ℝ := Φ ∘ₗ (LinearMap.range (L.prod ℓ)).subtype
  have hf2 : LinearMap.range f2 = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨v, rfl⟩ := hs y
    exact ⟨⟨(L.prod ℓ) v, v, rfl⟩, rfl⟩
  have hge : 2 ≤ Module.finrank ℝ (LinearMap.range (L.prod ℓ)) := by
    have h := LinearMap.finrank_range_le f2
    rw [hf2, finrank_top, Module.finrank_prod, Module.finrank_self] at h
    omega
  omega

/-- The differential of a pair is the pair of differentials. -/
theorem mvfderiv_pair_BAUGD {E H' M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'} [TopologicalSpace M] [ChartedSpace H' M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : M → F} {T : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (hT : MDifferentiableAt I 𝓘(ℝ, ℝ) T x)
    (v : TangentSpace I x) :
    mvfderiv I (fun z => (f z, T z)) x v = (mvfderiv I f x v, mvfderiv I T x v) := by
  have hP : MDifferentiableAt I 𝓘(ℝ, F × ℝ) (fun z => (f z, T z)) x := hf.prodMk_space hT
  have h1 := mvfderiv_clm_comp_BDFB (I := I) (ContinuousLinearMap.fst ℝ F ℝ) hP v
  have h2 := mvfderiv_clm_comp_BDFB (I := I) (ContinuousLinearMap.snd ℝ F ℝ) hP v
  exact Prod.ext h1.symm h2.symm

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- The final stage maps `f_j = π_j ∘ E` are smooth on all of `W` (A3a). -/
theorem stageMap_contMDiff_BAUGD (st : Fin 3) :
    ContMDiff W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      (C.toChain.stageMap st) :=
  ((actualSlotsV2_BAUGD S).stageProj st).contDiff.comp_contMDiff (C.stage_smooth_BAUGD 3)

/-- The height ratio `T = A/s` is smooth on all of `W` (A3a and `s > 0`). -/
theorem heightRatio_contMDiff_BAUGD :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ C.toChain.heightRatio := by
  have hE := C.stage_smooth_BAUGD 3
  have hh : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ C.toChain.height :=
    ((EuclideanSpace.proj (0 : Fin 2)).contDiff.comp
      (blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
        (Sum.inl S.edgeTag_BAUGA)).contDiff).comp_contMDiff hE
  have hs : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ C.toChain.scale :=
    S.scaleMarker_BIF.contDiff.comp_contMDiff hE
  exact hh.div₀ hs fun p => (C.scale_pos_BAUGD p).2.2.ne'

/-- **Rank two from rank one and the rim surjectivity**: if `rank df₂ = 1` at `p` and some linear
functional `ℓ` of `f₂` has `(d(ℓ ∘ f₂), dT)` onto `ℝ × ℝ` at `p`, then `rank d(f₂, T) = 2`. -/
theorem edgePairRank_eq_two_of_surjective_BAUGD (p : W.Carrier)
    (hrk : C.toChain.stageRank_BIFc 1 p = 1)
    (ℓ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)
    (hsurj : Function.Surjective (fun v : TangentSpace W.model p =>
      (mvfderiv W.model (fun z => ℓ (C.toChain.stageMap 1 z)) p v,
        mvfderiv W.model C.toChain.heightRatio p v))) :
    C.toChain.edgePairRank_BIFc p = 2 := by
  have hf : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (C.toChain.stageMap 1) p :=
    (C.stageMap_contMDiff_BAUGD 1 p).mdifferentiableAt (by simp)
  have hT : MDifferentiableAt W.model 𝓘(ℝ, ℝ) C.toChain.heightRatio p :=
    (C.heightRatio_contMDiff_BAUGD p).mdifferentiableAt (by simp)
  have hpair : (mvfderiv W.model
      (fun q => (C.toChain.stageMap 1 q, C.toChain.heightRatio q)) p :
        TangentSpace W.model p →L[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ) =
      (mvfderiv W.model (C.toChain.stageMap 1) p).prod
        (mvfderiv W.model C.toChain.heightRatio p) :=
    ContinuousLinearMap.ext fun v => mvfderiv_pair_BAUGD hf hT v
  have hsurj' : Function.Surjective (fun v : TangentSpace W.model p =>
      ((ℓ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ)
        ((mvfderiv W.model (C.toChain.stageMap 1) p : TangentSpace W.model p →ₗ[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) v),
        (mvfderiv W.model C.toChain.heightRatio p : TangentSpace W.model p →ₗ[ℝ] ℝ) v)) := by
    intro y
    obtain ⟨v, hv⟩ := hsurj y
    refine ⟨v, ?_⟩
    have hc := mvfderiv_clm_comp_BDFB ℓ hf v
    beta_reduce at hv ⊢
    rw [hc] at hv
    exact hv
  have hrk' : Module.finrank ℝ (LinearMap.range
      ((mvfderiv W.model (C.toChain.stageMap 1) p :
          TangentSpace W.model p →L[ℝ]
            BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
        TangentSpace W.model p →ₗ[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) = 1 := hrk
  have key := finrank_range_prod_eq_two_BAUGD _ _ _ hrk' hsurj'
  have hc := congrArg (fun L : TangentSpace W.model p →L[ℝ]
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ =>
    Module.finrank ℝ (LinearMap.range (L : TangentSpace W.model p →ₗ[ℝ]
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ))) hpair
  rw [ContinuousLinearMap.coe_prod] at hc
  exact hc.trans key

/-- **The open edge parent from the open domain and the rim surjectivity** (D69-7): the open
parent domain `U` with `X₂ = U ∩ {T ≤ 4Δ}`, `U ⊆ f₂⁻¹ B₂`, `rank df₂ = 1` on `U`, and at every
point of `U` on the rim `T = 4Δ` a linear functional `ℓ` of `f₂` with `(d(ℓ ∘ f₂), dT)` onto;
smoothness of `f₂` and `T` holds on all of `W`. -/
def edgeParentOfRim_BAUGD
    (source : Fin 3 → Set W.Carrier)
    (base : Fin 3 → Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
    (U : Set W.Carrier) (hU : IsOpen U)
    (hcut : source 1 = U ∩ {p | C.toChain.heightRatio p ≤ 4 * Δ})
    (hsub : U ⊆ C.toChain.stageMap 1 ⁻¹' base 1)
    (hrk : ∀ p ∈ U, C.toChain.stageRank_BIFc 1 p = 1)
    (hrim : ∀ p ∈ U, C.toChain.heightRatio p = 4 * Δ →
      ∃ ℓ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ,
        Function.Surjective (fun v : TangentSpace W.model p =>
          (mvfderiv W.model (fun z => ℓ (C.toChain.stageMap 1 z)) p v,
            mvfderiv W.model C.toChain.heightRatio p v))) :
    BoundaryEdgeParent_BIFc C.toChain source base where
  edgeParent := U
  isOpen_edgeParent := hU
  edgeParent_cut := hcut
  edgeParent_subset := hsub
  edgeParent_smooth := fun p _ =>
    ⟨C.stageMap_contMDiff_BAUGD 1 p, C.heightRatio_contMDiff_BAUGD p⟩
  edgeParent_rank := hrk
  edgeParent_rank_two := fun p hp hT => by
    obtain ⟨ℓ, hℓ⟩ := hrim p hp hT
    exact C.edgePairRank_eq_two_of_surjective_BAUGD p (hrk p hp) ℓ hℓ

/-- **Inhabitant** of the parent structure: the empty sources and bases have the empty parent
(on every chain, in particular on the empty-family chain). -/
theorem nonempty_edgeParent_empty_BAUGD :
    Nonempty (BoundaryEdgeParent_BIFc C.toChain (fun _ => ∅) (fun _ => ∅)) :=
  ⟨C.edgeParentOfRim_BAUGD _ _ ∅ isOpen_empty (by simp) (by simp) (by simp) (by simp)⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
