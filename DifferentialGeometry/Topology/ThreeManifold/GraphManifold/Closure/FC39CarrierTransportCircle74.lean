import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransport74

/-!
# Draft 74, D74-6: transport of the circle bundle along ONE carrier diffeomorphism

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G16 (bundle package of `FC39RowsV2.transport74`). For a
carrier diffeomorphism `e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier`:

* generic restrictions of a diffeomorphism to open sets: `Diffeomorph.imageOpens74 Φ U`
  (`Φ(U)` as an open set), `Diffeomorph.restrictOpens74 Φ U : Φ(U) ≃ₘ U` (by `Φ⁻¹`),
  `Diffeomorph.restrictPreimage74 Ψ V : Ψ⁻¹(V) ≃ₘ V`;
* **`CircleBundle.mapCarrier74 e R`**: domain `e(R.domain)`, projection `R.proj ∘ e⁻¹`, the same
  base, neighbourhoods and compact base, local trivializations precomposed with the restricted
  diffeomorphism (the projection identity is preserved), with `mapCarrier74_region`
  (`region = e(R.region)`) and `mapCarrier74_fibre` (whole fibres are the images).

The edge bundle is NOT transported here: its field `fibre_disk` needs
`IsSmoothEmbedding (𝓡∂ 2) W₁.model ∞ (e ∘ φ)`, i.e. a composition of an immersion with a
diffeomorphism between DIFFERENT models (`W₀.model`, `W₁.model`); the tree's
`IsSmoothEmbedding.diffeomorph_comp` needs one model on both sides (GAP, recorded).
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

/-- The image of an open set under a diffeomorphism, as an open set. -/
def _root_.Diffeomorph.imageOpens74 (Φ : N ≃ₘ⟮I, I'⟯ N') (U : Opens N) : Opens N' :=
  ⟨Φ '' U, Φ.toHomeomorph.isOpenMap _ U.isOpen⟩

/-- **The restriction of a diffeomorphism to an open set** (inverse direction): `Φ(U) ≃ₘ U`
by `Φ⁻¹`. -/
def _root_.Diffeomorph.restrictOpens74 (Φ : N ≃ₘ⟮I, I'⟯ N') (U : Opens N) :
    Φ.imageOpens74 U ≃ₘ⟮I', I⟯ U where
  toFun y := ⟨Φ.symm y.1, by
    obtain ⟨x, hx, hxy⟩ := y.2
    rw [← hxy, Φ.symm_apply_apply]
    exact hx⟩
  invFun x := ⟨Φ x.1, ⟨x.1, x.2, rfl⟩⟩
  left_inv y := Subtype.ext (Φ.apply_symm_apply y.1)
  right_inv x := Subtype.ext (Φ.symm_apply_apply x.1)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff U _).mp
    (Φ.symm.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff (Φ.imageOpens74 U) _).mp
    (Φ.contMDiff.comp contMDiff_subtype_val)

/-- The restricted diffeomorphism is `Φ⁻¹` on points. -/
theorem _root_.Diffeomorph.restrictOpens74_val (Φ : N ≃ₘ⟮I, I'⟯ N') (U : Opens N)
    (y : Φ.imageOpens74 U) : (Φ.restrictOpens74 U y : N) = Φ.symm y :=
  rfl

/-- **The restriction of a diffeomorphism to the preimage of an open set**: `Ψ⁻¹(V) ≃ₘ V`. -/
def _root_.Diffeomorph.restrictPreimage74 (Φ : N ≃ₘ⟮I, I'⟯ N') (V : Opens N') :
    Opens.comap ⟨Φ, Φ.continuous⟩ V ≃ₘ⟮I, I'⟯ V where
  toFun x := ⟨Φ x.1, x.2⟩
  invFun y := ⟨Φ.symm y.1, by
    change Φ (Φ.symm y.1) ∈ V
    rw [Φ.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext (Φ.symm_apply_apply x.1)
  right_inv y := Subtype.ext (Φ.apply_symm_apply y.1)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff V _).mp
    (Φ.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff (Opens.comap ⟨Φ, Φ.continuous⟩ V) _).mp
    (Φ.symm.contMDiff.comp contMDiff_subtype_val)

end Generic

end GC.GraphManifold.Assembly

namespace GC.GraphManifold.Assembly.FC39P0

variable {W₀ W₁ : CompactCarrier.{u}}

/-- **The circle bundle transported along `e`** (D74-6, bundle package): domain `e(R.domain)`,
projection `R.proj ∘ e⁻¹`, the same base / neighbourhoods / compact base, trivializations
precomposed with the restricted diffeomorphism. -/
def CircleBundle.mapCarrier74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (R : CircleBundle W₀) : CircleBundle W₁ where
  Base := R.Base
  domain := e.imageOpens74 R.domain
  domain_interior := by
    rw [← image_interior_carrier_R74 e]
    exact image_mono R.domain_interior
  proj := R.proj.comp ⟨e.restrictOpens74 R.domain, (e.restrictOpens74 R.domain).continuous⟩
  proj_smooth := R.proj_smooth.comp (e.restrictOpens74 R.domain).contMDiff
  proj_submersion x := by
    have hp : MDifferentiableAt W₀.model (𝓡 2) R.proj (e.restrictOpens74 R.domain x) :=
      (R.proj_smooth _).mdifferentiableAt (by simp)
    have hr : MDifferentiableAt W₁.model W₀.model (e.restrictOpens74 R.domain) x :=
      (e.restrictOpens74 R.domain).mdifferentiable (by simp) x
    change Surjective (mfderiv W₁.model (𝓡 2) (R.proj ∘ e.restrictOpens74 R.domain) x)
    rw [mfderiv_comp x hp hr]
    exact (R.proj_submersion _).comp (mfderiv_diffeo_bijective_R74 _ x).2
  neighborhood := R.neighborhood
  mem_neighborhood := R.mem_neighborhood
  trivialization c := ((e.restrictOpens74 R.domain).restrictPreimage74
    (Opens.comap R.proj (R.neighborhood c))).trans (R.trivialization c)
  projection_trivialization c x := R.projection_trivialization c _
  cbase := R.cbase
  cbase_compact := R.cbase_compact

section CircleTransport

variable (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier) (R : CircleBundle W₀)

/-- The transported domain is the image. -/
theorem CircleBundle.mapCarrier74_domain :
    ((R.mapCarrier74 e).domain : Set W₁.Carrier) = e '' R.domain :=
  rfl

/-- The transported projection is `R.proj ∘ e⁻¹`. -/
theorem CircleBundle.mapCarrier74_proj (x : (R.mapCarrier74 e).domain) :
    (R.mapCarrier74 e).proj x = R.proj (e.restrictOpens74 R.domain x) :=
  rfl

/-- The transported region `M₃` is the image of the region. -/
theorem CircleBundle.mapCarrier74_region :
    (R.mapCarrier74 e).region = e '' R.region := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e.restrictOpens74 R.domain x, ⟨_, hx, rfl⟩, e.apply_symm_apply x.1⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨(e.restrictOpens74 R.domain).symm z, ?_, rfl⟩
    change R.proj (e.restrictOpens74 R.domain ((e.restrictOpens74 R.domain).symm z)) ∈ R.cbase
    rw [Diffeomorph.apply_symm_apply]
    exact hz

/-- The transported whole fibres are the images of the whole fibres. -/
theorem CircleBundle.mapCarrier74_fibre (c : R.Base) :
    (R.mapCarrier74 e).fibre c = e '' R.fibre c := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e.restrictOpens74 R.domain x, ⟨_, hx, rfl⟩, e.apply_symm_apply x.1⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨(e.restrictOpens74 R.domain).symm z, ?_, rfl⟩
    change R.proj (e.restrictOpens74 R.domain ((e.restrictOpens74 R.domain).symm z)) = c
    rw [Diffeomorph.apply_symm_apply]
    exact hz

end CircleTransport

end GC.GraphManifold.Assembly.FC39P0
