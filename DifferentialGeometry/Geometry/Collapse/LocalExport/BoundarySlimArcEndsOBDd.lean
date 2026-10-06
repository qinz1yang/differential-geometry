import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimSharedEndOBDd
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimPieceExit74

/-!
# The end data `ArcEnds74` of a slim arc piece, with the defining function exposed as `e ∘ f₃`
(lane S-BD2d2, suffix `_OBDd`), group G10e

Lane O-BD1 (by S-BD2d2), hlift, `SlimCutPieces74`. Boundary twin of `arcEnds_of_sets74` /
`slim_arcEnds_of_product74` (closed route), built END BY END:

* an end `b` whose end value `γ (iccEnd b)` is a face point (`f₃(∂M₁ ∩ X₃)`) is SHARED: its slice
  (the whole fibre `X₃ ∩ f₃⁻¹{y}`, preconnected) is the `neighbourSet` of a neighbour face (the
  hypothesis `hface`, supplied by `exists_neighbourFace_of_face_OBDd`);
* any other end is FREE: `exists_freeEnd_OBDd` gives `fn = a ∘ f₃` with `a` smooth on the whole
  ambient base space (the descended defining function).

`BoundaryGaf02ChainE.exists_arcEnds_OBDd`: the `ArcEnds74` with the two exposed clauses
(`rel3`-style, as `exists_slimExit_rel3_OCL`): for a free end `fn b = a ∘ f₃`, `a` smooth; and the
end is free iff the end value is not a face point.
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

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **The end data of a slim arc piece**: for the piece `X₃ ∩ f₃⁻¹(γ [0, 1])` with whole
preconnected end slices `X₃ ∩ f₃⁻¹{γ (iccEnd b)}`, an `ArcEnds74` whose free ends have defining
function `a ∘ f₃` (`a` smooth on the ambient base space) and whose free ends are exactly those
whose end value is not a face point. -/
theorem exists_arcEnds_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (P : ProperSmoothSurfaceSubmersion_EFE (𝓡 3) (W.pieceInterior ⊤)
      (dec.bases.base 2) (dec.bases.base 2))
    (hP : ∀ x, P.toFun x = C.slimF_OBDd x) {k₀ : ℕ} {E : BoundaryTori W k₀} {Z : ZeroDomains W}
    {Cu : CuspCores W E}
    (hface : ∀ y ∈ C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2),
      IsPreconnected (dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {y}) →
      ∃ F : NeighbourFace Z Cu,
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {y} = neighbourSet F)
    (γ' : SmoothEmbeddedBaseArc_EFE (dec.bases.base 2)) {pieceSet : Set W.Carrier}
    {slice : Bool → Set W.Carrier}
    (hpiece : pieceSet = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' (γ'.toFun '' Icc 0 1))
    (hslice : ∀ b, slice b =
      dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ'.toFun (iccEnd b)})
    (hconn : ∀ b, IsPreconnected (slice b)) :
    ∃ ends : ArcEnds74 Z Cu pieceSet slice,
      (∀ b, ends.kind b = none → ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA
        (Fin S.packet.cusp.count) → ℝ, ContDiff ℝ ∞ a ∧
          ∀ x, ends.fn b x = a (C.toChain.stageMap 2 x)) ∧
      ∀ b, ends.kind b = none ↔
        γ'.toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
          (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2) := by
  classical
  have hend : ∀ b : Bool, ((iccEnd b : Icc (0 : ℝ) 1) : ℝ) = 0 ∨
      ((iccEnd b : Icc (0 : ℝ) 1) : ℝ) = 1 := fun b => by
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hb : ∀ b : Bool, ∃ (kd : Option (NeighbourFace Z Cu))
      (a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ)
      (near : TopologicalSpace.Opens W.Carrier),
      (∀ F, kd = some F → slice b = neighbourSet F) ∧
      (kd = none → (near : Set W.Carrier) ⊆ W.interior) ∧
      (kd = none → ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (fun x => a (C.toChain.stageMap 2 x)) near) ∧
      (kd = none → ∀ x ∈ near, a (C.toChain.stageMap 2 x) = 0 →
        mfderiv W.model 𝓘(ℝ, ℝ) (fun x => a (C.toChain.stageMap 2 x)) x ≠ 0) ∧
      (kd = none → slice b = {x | x ∈ near ∧ a (C.toChain.stageMap 2 x) = 0}) ∧
      (kd = none → pieceSet ∩ near = {x | x ∈ near ∧ a (C.toChain.stageMap 2 x) ≤ 0}) ∧
      (kd = none → ContDiff ℝ ∞ a) ∧
      (kd = none ↔ γ'.toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
        (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) := by
    intro b
    by_cases hy : γ'.toFun (iccEnd b) ∈ C.toChain.stageMap 2 ''
        (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)
    · obtain ⟨F, hF⟩ := hface _ hy ((hslice b) ▸ hconn b)
      refine ⟨some F, fun _ => 0, ⊥, fun F' hF' => ?_, fun h => absurd h (Option.some_ne_none _),
        fun h => absurd h (Option.some_ne_none _), fun h => absurd h (Option.some_ne_none _),
        fun h => absurd h (Option.some_ne_none _), fun h => absurd h (Option.some_ne_none _),
        fun h => absurd h (Option.some_ne_none _), ⟨fun h => absurd h (Option.some_ne_none _),
          fun h => absurd hy h⟩⟩
      cases Option.some.inj hF'
      rw [hslice b]
      exact hF
    · obtain ⟨a, near, ha, hint, hsm, hreg, hlev, hside⟩ :=
        C.exists_freeEnd_OBDd dec P hP γ' (hend b)
      refine ⟨none, a, near, fun F hF => absurd hF.symm (Option.some_ne_none F), fun _ => hint,
        fun _ => hsm, fun _ => hreg, fun _ => (hslice b).trans hlev,
        fun _ => by rw [hpiece]; exact hside, fun _ => ha, ⟨fun _ => hy, fun _ => rfl⟩⟩
  choose kd a near h1 h2 h3 h4 h5 h6 h7 h8 using hb
  exact ⟨{
    kind := kd
    fn := fun b x => a b (C.toChain.stageMap 2 x)
    near := near
    shared_eq := fun b F hk => h1 b F hk
    near_interior := fun b hk => h2 b hk
    fn_smooth := fun b hk => h3 b hk
    fn_regular := fun b hk => h4 b hk
    fn_level := fun b hk => h5 b hk
    fn_eq := fun b hk => h6 b hk },
    fun b hk => ⟨a b, h7 b hk, fun x => rfl⟩, fun b => h8 b⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
