import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedSmoothCoreViaOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDecompositionV2bOBD

/-!
# The boundary zero rows `ZeroDomains W` from the actual zero domains (lane O-BD2b)

Lane O-BD1 (by O-BD2b, suffix `_OBD`), group G3 (Z2 on the boundary, draft 74 §3.1 / D74-7 /
D74-8, review 76 D76-5 bridge Z1). The closed route (`zeroDomainsOfExits74`,
`Gaf02ChainE.zeroDomains_of_actual_zero_exit74`) needs `φ : X ≃ W` and `∂W = ∅`. On the boundary
the rows live directly on `W.Carrier` (D76-5) and no carrier identification is used:

* the PIECE of the zero index `k` is the selected solid core `Q k` of the original model sublevel
  `{radial_k ≤ 2/5} ⊆ W°` (Z1 data, exactly as on the closed route) carried by the inclusion
  `W° → W` and ZSP02's ONE ambient diffeomorphism `Ψ_k` of `W` (`transport`, (ZH)):
  map `Ψ_k ∘ val ∘ param`, range `Ψ_k(val {radial_k ≤ 2/5}) = Z_k`;
* the RATIO is the decomposition's global defining function `defFn k` EXACTLY (smooth, regular on
  its zeros, `{defFn ≤ 0} = Z_k`, `{defFn = 0} = face = ∂Z_k`);
* the BUFFER is ZSP02's open face neighbourhood (`ratio_near`) cut down to `W°`; the face lies in
  `W°` because `Ψ_k` preserves interior points;
* the MODEL is the selected core's branch (closed branch: `ClosedZeroPiece` with its metric).

Main statement: **`BoundaryActualZeroDomains_BIFc.exists_zeroDomains_OBD Z Q`** — `ZeroDomains W`
with `σ : Fin count ≃ ZeroIdx`, `range (piece j) = Z_{σ j}`, `ratio j = defFn (σ j)` (the
`zero_link` of the boundary landing), `pieceBoundary (piece j) = face_{σ j}`, closed branch iff
the selected core is closed.
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

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

section Inclusion

variable (W : CompactCarrier.{0})

/-- The inclusion `W° → W` (interior atlas) is smooth. -/
theorem contMDiff_pieceInteriorVal_OBD :
    ContMDiff (𝓡 3) W.model ∞ (Subtype.val : W.pieceInterior ⊤ → W.Carrier) :=
  (isLocalDiffeomorph_pieceInterior_val W ⊤).contMDiff

/-- The inclusion `W° → W` has bijective differential. -/
theorem bijective_mfderiv_pieceInteriorVal_OBD (x : W.pieceInterior ⊤) :
    Bijective (mfderiv (𝓡 3) W.model (Subtype.val : W.pieceInterior ⊤ → W.Carrier) x) := by
  have h := ((isLocalDiffeomorph_pieceInterior_val W ⊤).mfderivToContinuousLinearEquiv
    (by simp) x).bijective
  rwa [← ContinuousLinearEquiv.coe_coe,
    IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe] at h

/-- The inclusion `W° → W` is an open embedding. -/
theorem isOpenEmbedding_pieceInteriorVal_OBD :
    Topology.IsOpenEmbedding (Subtype.val : W.pieceInterior ⊤ → W.Carrier) :=
  (W.pieceInterior ⊤).isOpen.isOpenEmbedding_subtypeVal

variable {W}

/-- An ambient diffeomorphism of `W` keeps the points of `W°` in the interior of `W`. -/
theorem diffeo_val_mem_interior_OBD (Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier)
    (q : W.pieceInterior ⊤) : Ψ q.val ∈ W.interior := by
  have hq : q.val ∈ W.model.interior W.Carrier := by
    rw [← coe_pieceInterior_top_BDRY1 W]
    exact q.property
  have hΨ : Ψ q.val ∈ W.model.interior W.Carrier :=
    ((Ψ.isLocalDiffeomorph q.val).isInteriorPoint_iff (by simp)).mp hq
  rw [← coe_pieceInterior_top_BDRY1 W] at hΨ
  exact hΨ.2

end Inclusion

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

namespace BoundaryActualZeroDomains_BIFc

/-- **Z2 on the boundary** (draft 74 §3.1, D74-7 / D74-8; D76-5: rows directly on `W.Carrier`):
the actual zero domains of the decomposition and the selected solid cores `Q k` of the original
model sublevels `{radial_k ≤ 2/5} ⊆ W°` (Z1 data, as on the closed route) give `ZeroDomains W`
whose pieces are `Ψ_k ∘ val ∘ param` (range `Z_k`, model boundary the face), whose ratios are the
global defining functions EXACTLY, and whose models are the selected cores' branches. -/
theorem exists_zeroDomains_OBD {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    {Bs : BoundaryGaf02BasesV2 C} (Z : BoundaryActualZeroDomains_BIFc C Bs)
    (Q : ∀ k : S.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5}) :
    ∃ (zero : ZeroDomains W) (σ : Fin zero.count ≃ S.ZeroIdx_BAUGC), ∀ j,
      range (zero.piece j).map = C.actualZeroDomain_BIFc (σ j) ∧
        zero.ratio j = Z.defFn (σ j) ∧
        pieceBoundary (zero.piece j) = C.actualZeroFace_BIFc (σ j) ∧
        ((zero.model j).isRight = true ↔ (Q (σ j)).IsClosed) := by
  classical
  choose Ψ hΨ using Z.transport
  choose O hO hfO _ using Z.ratio_near
  have hι := contMDiff_pieceInteriorVal_OBD W
  have hιb := bijective_mfderiv_pieceInteriorVal_OBD W
  have hιo := isOpenEmbedding_pieceInteriorVal_OBD W
  have hιi : Injective (Subtype.val : W.pieceInterior ⊤ → W.Carrier) := Subtype.val_injective
  let σ : Fin (Fintype.card S.ZeroIdx_BAUGC) ≃ S.ZeroIdx_BAUGC := (Fintype.equivFin _).symm
  have hrange : ∀ k, range ((Q k).pieceVia_OBD Subtype.val hι hιb hιi (Ψ k)).map =
      C.actualZeroDomain_BIFc k := fun k =>
    ((Q k).range_pieceVia_OBD Subtype.val hι hιb hιi (Ψ k)).trans (hΨ k).1
  have hbdry : ∀ k, pieceBoundary ((Q k).pieceVia_OBD Subtype.val hι hιb hιi (Ψ k)) =
      C.actualZeroFace_BIFc k := fun k => by
    rw [(Q k).pieceBoundary_pieceVia_OBD Subtype.val hι hιb hιi (Ψ k) hιo, (hΨ k).1,
      Z.frontier_eq k]
  have hint : ∀ k, C.actualZeroFace_BIFc k ⊆ W.interior := fun k y hy => by
    have hyZ : y ∈ C.actualZeroDomain_BIFc k := by
      rw [Z.domain_eq k]
      rw [Z.face_eq k] at hy
      exact le_of_eq hy
    rw [← (hΨ k).1] at hyZ
    obtain ⟨x, ⟨q, -, rfl⟩, rfl⟩ := hyZ
    exact diffeo_val_mem_interior_OBD (Ψ k) q
  refine ⟨{
    count := Fintype.card S.ZeroIdx_BAUGC
    piece := fun j => (Q (σ j)).pieceVia_OBD Subtype.val hι hιb hιi (Ψ (σ j))
    disjoint := fun j j' hjj' => by
      beta_reduce
      rw [hrange, hrange]
      exact Z.pairwise_disjoint (σ.injective.ne hjj')
    ratio := fun j => Z.defFn (σ j)
    near := fun j => ⟨O (σ j), hO (σ j)⟩ ⊓ W.interior
    near_interior := fun j x hx => hx.2
    ratio_smooth := fun j => Z.defFn_smooth (σ j)
    ratio_regular := fun j => Z.defFn_regular (σ j)
    zero_subset_near := fun j y hy => by
      have hf : y ∈ C.actualZeroFace_BIFc (σ j) := by
        rw [Z.face_eq]
        exact hy
      exact ⟨hfO (σ j) hf, hint (σ j) hf⟩
    boundary_eq := fun j => (hbdry (σ j)).trans (Z.face_eq (σ j))
    range_eq := fun j => (hrange (σ j)).trans (Z.domain_eq (σ j))
    model := fun j => (Q (σ j)).modelVia_OBD Subtype.val hι hιb hιi (Ψ (σ j)) }, σ,
    fun j => ⟨hrange (σ j), rfl, hbdry (σ j), ?_⟩⟩
  exact SelectedSmoothCore74.modelVia_isRight_iff_OBD Subtype.val hι hιb hιi (Ψ (σ j))

end BoundaryActualZeroDomains_BIFc

end DifferentialGeometry.Geometry.Collapse
