import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimArcProductOBDd
import DifferentialGeometry.Topology.Ehresmann.ArcEndTubeEndOBDd

/-!
# The free end of a slim arc piece, in `W` (lane S-BD2d2, suffix `_OBDd`), group G10e

Lane O-BD1 (by S-BD2d2), hlift, `SlimCutPieces74`. Over `W°` the tube kernel
`exists_arc_end_tube_endpoint_OBDd` (the defining function of the end of a base arc, as a smooth
function `a` of the base point) applies to the slim stage `exists_slimSubmersion_OBDd`; carried to
`W` by the inclusion `val : W° → W` (a local diffeomorphism, an open map) the defining function is
`fn = a ∘ f₃` on the open set `val(U) ⊆ W°`:

* `mfderiv_fn_ne_zero_OBDd`: a function on `W` whose restriction to `W°` has surjective
  differential has non-vanishing differential;
* `BoundaryGaf02ChainE.exists_freeEnd_OBDd`: for either end `t₀ ∈ {0, 1}` of a base arc `γ` of `B₃`
  a smooth `a` on the ambient base space and an open `near ⊆ W°` with the clauses of a free end of
  `ArcEnds74` for the defining function `x ↦ a (f₃ x)`: smooth and regular on `near`, whose zero
  set is the whole end fibre `X₃ ∩ f₃⁻¹{γ t₀}`, whose sublevel is the preimage of the arc.
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

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

omit [ConnectedSpace W.Carrier] in
/-- **A function on `W` whose restriction to `W°` has surjective differential at `u` has
non-vanishing differential at `u`.** -/
theorem mfderiv_fn_ne_zero_OBDd (fn : W.Carrier → ℝ) (hfn : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ fn)
    (u : W.pieceInterior ⊤)
    (hs : Surjective (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fun v : W.pieceInterior ⊤ => fn v.1) u)) :
    mfderiv W.model 𝓘(ℝ, ℝ) fn u.1 ≠ 0 := by
  intro h0
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hval := ((isLocalDiffeomorph_pieceInterior_val W ⊤).contMDiff u).mdifferentiableAt hn
  have hcomp : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fn ∘ (Subtype.val : W.pieceInterior ⊤ → W.Carrier)) u =
      (mfderiv W.model 𝓘(ℝ, ℝ) fn u.1).comp
        (mfderiv (𝓡 3) W.model (Subtype.val : W.pieceInterior ⊤ → W.Carrier) u) :=
    mfderiv_comp u (hfn.mdifferentiableAt hn) hval
  obtain ⟨v, hv⟩ := hs 1
  have h1 : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fun v : W.pieceInterior ⊤ => fn v.1) u v = 1 := hv
  have h2 : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fun v : W.pieceInterior ⊤ => fn v.1) u v = 0 := by
    change mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fn ∘ (Subtype.val : W.pieceInterior ⊤ → W.Carrier)) u v = 0
    rw [hcomp, h0]
    rfl
  exact one_ne_zero (show (1 : ℝ) = 0 from h1.symm.trans h2)

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **The free end of a slim arc piece in `W`**: for either end `t₀ ∈ {0, 1}` of a smooth embedded
base arc `γ` of `B₃`, a smooth `a` on the ambient base space and an open `near ⊆ W°` such that
`fn = a ∘ f₃` is smooth and regular on `near`, `{fn = 0} ∩ near` is the whole end fibre
`X₃ ∩ f₃⁻¹{γ t₀}` and `{fn ≤ 0} ∩ near` is the arc piece `X₃ ∩ f₃⁻¹(γ [0, 1]) ∩ near`. -/
theorem exists_freeEnd_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (P : ProperSmoothSurfaceSubmersion_EFE (𝓡 3) (W.pieceInterior ⊤)
      (dec.bases.base 2) (dec.bases.base 2))
    (hP : ∀ x, P.toFun x = C.slimF_OBDd x)
    (γ : SmoothEmbeddedBaseArc_EFE (dec.bases.base 2)) {t₀ : ℝ} (ht : t₀ = 0 ∨ t₀ = 1) :
    ∃ (a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ)
      (near : TopologicalSpace.Opens W.Carrier),
      ContDiff ℝ ∞ a ∧ (near : Set W.Carrier) ⊆ W.interior ∧
      ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (fun x => a (C.toChain.stageMap 2 x)) near ∧
      (∀ x ∈ near, a (C.toChain.stageMap 2 x) = 0 →
        mfderiv W.model 𝓘(ℝ, ℝ) (fun x => a (C.toChain.stageMap 2 x)) x ≠ 0) ∧
      dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ.toFun t₀} =
        {x | x ∈ near ∧ a (C.toChain.stageMap 2 x) = 0} ∧
      dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' (γ.toFun '' Icc 0 1) ∩ near =
        {x | x ∈ near ∧ a (C.toChain.stageMap 2 x) ≤ 0} := by
  obtain ⟨U, h, a, hUo, hfU, hUB, -, hsurj, hlev, hside, ha, hha⟩ :=
    exists_arc_end_tube_endpoint_OBDd P γ ht
  have hPf : P.toFun = C.slimF_OBDd := funext hP
  have hfs : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun x => a (C.toChain.stageMap 2 x)) :=
    ha.comp_contMDiff (C.contMDiff_stageMap_OBD 2)
  have hnear : IsOpen (Subtype.val '' U : Set W.Carrier) :=
    (W.pieceInterior ⊤).isOpen.isOpenMap_subtype_val U hUo
  have hhx : ∀ u : W.pieceInterior ⊤, h u = a (C.toChain.stageMap 2 u.1) := fun u => by
    rw [hha u, hPf]
    rfl
  refine ⟨a, ⟨Subtype.val '' U, hnear⟩, ha, ?_, hfs.contMDiffOn, ?_, ?_, ?_⟩
  · rintro _ ⟨u, -, rfl⟩
    exact u.2.2
  · rintro _ ⟨u, hu, rfl⟩ hz
    refine mfderiv_fn_ne_zero_OBDd _ hfs u ?_
    have hfun : (fun v : W.pieceInterior ⊤ => a (C.toChain.stageMap 2 v.1)) = h :=
      funext fun v => (hhx v).symm
    rw [hfun]
    exact hsurj u hu
  · ext x
    constructor
    · rintro ⟨hxX, hxy⟩
      let v : W.pieceInterior ⊤ := ⟨x, C.source_two_subset_pieceInterior_OBDd dec hxX⟩
      have hu : v ∈ P.toFun ⁻¹' {γ.toFun t₀} := by
        change P.toFun v = _
        rw [hPf]
        exact hxy
      have h0 : v ∈ {x | x ∈ U ∧ h x = 0} := by
        rw [hlev]
        exact hu
      exact ⟨⟨v, hfU hu, rfl⟩, (hhx v).symm.trans h0.2⟩
    · rintro ⟨⟨u, hu, rfl⟩, hz⟩
      have hz' : h u = 0 := by rw [hhx]; exact hz
      have hmem : u ∈ P.toFun ⁻¹' {γ.toFun t₀} := by
        rw [← hlev]
        exact ⟨hu, hz'⟩
      have hy : C.toChain.stageMap 2 u.1 = γ.toFun t₀ := by
        have h2 : P.toFun u = γ.toFun t₀ := hmem
        rw [hPf] at h2
        exact h2
      refine ⟨C.mem_source_of_stageMap_mem_base_OBDd dec ?_, hy⟩
      have h3 := hUB hu
      rw [hPf] at h3
      exact h3
  · ext x
    constructor
    · rintro ⟨⟨hxX, hxT⟩, ⟨u, hu, rfl⟩⟩
      have hmem : u ∈ U ∩ P.toFun ⁻¹' (γ.toFun '' Icc 0 1) := by
        refine ⟨hu, Set.mem_preimage.2 ?_⟩
        rw [hPf]
        exact hxT
      rw [hside] at hmem
      exact ⟨⟨u, hu, rfl⟩, (hhx u) ▸ hmem.2⟩
    · rintro ⟨⟨u, hu, rfl⟩, hz⟩
      have hz' : h u ≤ 0 := by rw [hhx]; exact hz
      have hmem : u ∈ U ∩ P.toFun ⁻¹' (γ.toFun '' Icc 0 1) := by
        rw [hside]
        exact ⟨hu, hz'⟩
      have hT : C.toChain.stageMap 2 u.1 ∈ γ.toFun '' Icc 0 1 := by
        have h2 : P.toFun u ∈ γ.toFun '' Icc 0 1 := hmem.2
        rw [hPf] at h2
        exact h2
      refine ⟨⟨C.mem_source_of_stageMap_mem_base_OBDd dec ?_, hT⟩, ⟨u, hu, rfl⟩⟩
      have h3 := hUB hu
      rw [hPf] at h3
      exact h3

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
