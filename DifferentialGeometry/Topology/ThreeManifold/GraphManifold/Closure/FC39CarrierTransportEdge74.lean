import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportCircle74
import DifferentialGeometry.Topology.Embedding.Diffeomorph

/-!
# Draft 74, D74-6: transport of the edge disk bundle between carriers of the same kind

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G19 (bundle package of `FC39RowsV2.transport74`, second
half of G16). The edge bundle's `fibre_disk` asks for `IsSmoothEmbedding (𝓡∂ 2) W.model ∞ φ`; the
tree composes embeddings with diffeomorphisms of ONE model (`IsSmoothEmbedding.diffeomorph_comp`),
so the transport is stated for carriers of the SAME kind (`W₀.kind = W₁.kind`; the only case in
which a carrier diffeomorphism is used by the rows). Every other field transports as for the
circle bundle (G16):

* `isSmoothEmbedding_comp_carrier_R74`: `e ∘ φ` is a smooth embedding into `W₁` (same kind);
* `Diffeomorph.image_restrictOpens74`: the points of `Φ(U)` with a property of their
  `Φ⁻¹`-preimage are the `Φ`-image of the points of `U` with that property;
* **`EdgeBundle.mapCarrier74 e hk P`**: source `e(P.source)`, projection `P.proj ∘ e⁻¹`, height
  `P.height ∘ e⁻¹`, the same base / level / compact base (rank two, properness and the whole disk
  fibres carried by `e`), with `mapCarrier74_edgePiece` (`M^edge` is the image).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Generic

variable {EN HN EN' HN' : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [NormedAddCommGroup EN'] [NormedSpace ℝ EN'] [TopologicalSpace HN']
  {I : ModelWithCorners ℝ EN HN} {I' : ModelWithCorners ℝ EN' HN'} {N N' : Type*}
  [TopologicalSpace N] [ChartedSpace HN N] [TopologicalSpace N'] [ChartedSpace HN' N']

/-- The points of `Φ(U)` whose `Φ⁻¹`-preimage satisfies `Q` are the `Φ`-image of the points of
`U` satisfying `Q`. -/
theorem _root_.Diffeomorph.image_restrictOpens74 (Φ : N ≃ₘ⟮I, I'⟯ N') (U : Opens N)
    (Q : U → Prop) :
    Subtype.val '' {x : Φ.imageOpens74 U | Q (Φ.restrictOpens74 U x)} =
      Φ '' (Subtype.val '' {y : U | Q y}) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Φ.restrictOpens74 U x, ⟨_, hx, rfl⟩, Φ.apply_symm_apply x.1⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(Φ.restrictOpens74 U).symm y, ?_, rfl⟩
    change Q (Φ.restrictOpens74 U ((Φ.restrictOpens74 U).symm y))
    rw [Diffeomorph.apply_symm_apply]
    exact hy

end Generic

variable {W₀ W₁ : CompactCarrier.{u}}

/-- **A smooth embedding followed by a carrier diffeomorphism** (carriers of the same kind). -/
theorem isSmoothEmbedding_comp_carrier_R74 {EQ HQ : Type*} [NormedAddCommGroup EQ]
    [NormedSpace ℝ EQ] [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ} {Q : Type*}
    [TopologicalSpace Q] [ChartedSpace HQ Q]
    (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier) (hk : W₀.kind = W₁.kind)
    {φ : Q → W₀.Carrier} (hφ : IsSmoothEmbedding IQ W₀.model ∞ φ) :
    IsSmoothEmbedding IQ W₁.model ∞ (e ∘ φ) := by
  cases W₀
  cases W₁
  dsimp only at hk
  subst hk
  exact hφ.diffeomorph_comp e

end GC.GraphManifold.Assembly

namespace GC.GraphManifold.Assembly.FC39P0

attribute [local instance] diskChartsBase_FC39P0

variable {W₀ W₁ : CompactCarrier.{u}}

/-- **The edge disk bundle transported along `e`** (carriers of the same kind; D74-6, bundle
package): source `e(P.source)`, projection `P.proj ∘ e⁻¹`, height `P.height ∘ e⁻¹`, the same base,
level and compact base. -/
def EdgeBundle.mapCarrier74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (hk : W₀.kind = W₁.kind) (P : EdgeBundle W₀) : EdgeBundle W₁ where
  Base := P.Base
  source := e.imageOpens74 P.source
  source_interior := by
    rw [← image_interior_carrier_R74 e]
    exact image_mono P.source_interior
  proj := P.proj.comp ⟨e.restrictOpens74 P.source, (e.restrictOpens74 P.source).continuous⟩
  proj_smooth := P.proj_smooth.comp (e.restrictOpens74 P.source).contMDiff
  proj_submersion x := by
    have hp : MDifferentiableAt W₀.model (𝓡 1) P.proj (e.restrictOpens74 P.source x) :=
      (P.proj_smooth _).mdifferentiableAt (by simp)
    have hr : MDifferentiableAt W₁.model W₀.model (e.restrictOpens74 P.source) x :=
      (e.restrictOpens74 P.source).mdifferentiable (by simp) x
    change Surjective (mfderiv W₁.model (𝓡 1) (P.proj ∘ e.restrictOpens74 P.source) x)
    rw [mfderiv_comp x hp hr]
    exact (P.proj_submersion _).comp (mfderiv_diffeo_bijective_R74 _ x).2
  height := P.height ∘ e.restrictOpens74 P.source
  height_smooth := P.height_smooth.comp (e.restrictOpens74 P.source).contMDiff
  level := P.level
  rank_two x hx := by
    have hp : MDifferentiableAt W₀.model (𝓡 1) P.proj (e.restrictOpens74 P.source x) :=
      (P.proj_smooth _).mdifferentiableAt (by simp)
    have hh : MDifferentiableAt W₀.model 𝓘(ℝ, ℝ) P.height (e.restrictOpens74 P.source x) :=
      (P.height_smooth _).mdifferentiableAt (by simp)
    have hr : MDifferentiableAt W₁.model W₀.model (e.restrictOpens74 P.source) x :=
      (e.restrictOpens74 P.source).mdifferentiable (by simp) x
    have e1 := mfderiv_comp x hp hr
    have e2 := mfderiv_comp x hh hr
    intro ab
    obtain ⟨w, hw⟩ := P.rank_two (e.restrictOpens74 P.source x) hx ab
    obtain ⟨v, rfl⟩ := (mfderiv_diffeo_bijective_R74 (e.restrictOpens74 P.source) x).2 w
    refine ⟨v, ?_⟩
    change (mfderiv W₁.model (𝓡 1) (P.proj ∘ e.restrictOpens74 P.source) x v,
      mfderiv W₁.model 𝓘(ℝ, ℝ) (P.height ∘ e.restrictOpens74 P.source) x v) = ab
    rw [e1, e2]
    exact hw
  proper K hK := by
    have h := e.image_restrictOpens74 P.source (fun y => P.proj y ∈ K ∧ P.height y ≤ P.level)
    change IsCompact (Subtype.val '' {x : e.imageOpens74 P.source |
      P.proj (e.restrictOpens74 P.source x) ∈ K ∧
        P.height (e.restrictOpens74 P.source x) ≤ P.level})
    rw [h]
    exact (P.proper K hK).image e.continuous
  fibre_disk c := by
    obtain ⟨φ, hφ, hr⟩ := P.fibre_disk c
    refine ⟨e ∘ φ, isSmoothEmbedding_comp_carrier_R74 e hk hφ, ?_⟩
    have h := e.image_restrictOpens74 P.source (fun y => P.proj y = c ∧ P.height y ≤ P.level)
    change range (e ∘ φ) = Subtype.val '' {x : e.imageOpens74 P.source |
      P.proj (e.restrictOpens74 P.source x) = c ∧
        P.height (e.restrictOpens74 P.source x) ≤ P.level}
    rw [h, range_comp, hr]
  cbase := P.cbase
  cbase_compact := P.cbase_compact
  cbase_domain := P.cbase_domain

/-- The transported actual edge piece `M^edge` is the image of the edge piece. -/
theorem EdgeBundle.mapCarrier74_edgePiece (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (hk : W₀.kind = W₁.kind) (P : EdgeBundle W₀) :
    (P.mapCarrier74 e hk).edgePiece = e '' P.edgePiece :=
  e.image_restrictOpens74 P.source (fun y => P.proj y ∈ P.cbase ∧ P.height y ≤ P.level)

/-- The transported height and projection are the pulled-back ones. -/
theorem EdgeBundle.mapCarrier74_height (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (hk : W₀.kind = W₁.kind) (P : EdgeBundle W₀) (x : (P.mapCarrier74 e hk).source) :
    (P.mapCarrier74 e hk).height x = P.height (e.restrictOpens74 P.source x) ∧
      (P.mapCarrier74 e hk).proj x = P.proj (e.restrictOpens74 P.source x) :=
  ⟨rfl, rfl⟩

end GC.GraphManifold.Assembly.FC39P0
