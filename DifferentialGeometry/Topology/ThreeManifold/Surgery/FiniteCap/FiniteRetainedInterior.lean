import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreInteriorSmooth
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSelectedManifolds

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold IsManifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev RetainedE3 := EuclideanSpace ℝ (Fin 3)
private abbrev RetainedIC := (𝓡 2).prod 𝓘(ℝ)
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "RetainedQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteRetainedInteriorOpens (R : Set (ConnectedComponents (cutCore f))) : Opens RetainedQ :=
  finiteCapRetained hL hδ f hf hdisj R ⊓ finiteCoreInteriorOpens hL hδ f hf hdisj

theorem finiteRetainedInterior_original_point (R : Set (ConnectedComponents (cutCore f)))
    (q : finiteRetainedInteriorOpens hL hδ f hf hdisj R) :
    finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj
      ((finiteCoreInteriorHomeomorph hL hδ f hf hdisj).symm
        (Opens.inclusion inf_le_right q)) = q.val :=
  congrArg Subtype.val ((finiteCoreInteriorHomeomorph hL hδ f hf hdisj).apply_symm_apply
    (Opens.inclusion inf_le_right q))

def finiteRetainedInteriorOriginalMap (U : Opens M) (R : Set (ConnectedComponents (cutCore f)))
    (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U) :
    finiteRetainedInteriorOpens hL hδ f hf hdisj R → U := by
  intro q
  let x := (finiteCoreInteriorHomeomorph hL hδ f hf hdisj).symm (Opens.inclusion inf_le_right q)
  refine ⟨x.val, ?_⟩
  have hxR : (⟨x.val, interior_subset x.property⟩ : cutCore f) ∈ retainedCore f R := by
    change finiteCapComponentLabel hL hδ f hf hdisj
      (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj x) ∈ R
    rw [finiteRetainedInterior_original_point]
    exact q.property.1
  exact hRet hxR

theorem finiteRetainedInteriorOriginalMap_val (U : Opens M) (R : Set (ConnectedComponents (cutCore f)))
    (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
    (q : finiteRetainedInteriorOpens hL hδ f hf hdisj R) :
    (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet q).val =
      ((finiteCoreInteriorHomeomorph hL hδ f hf hdisj).symm (Opens.inclusion inf_le_right q)).val := rfl

theorem injective_finiteRetainedInteriorOriginalMap (U : Opens M) (R : Set (ConnectedComponents (cutCore f)))
    (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U) :
    Injective (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet) := by
  intro q r he
  let e := finiteCoreInteriorHomeomorph hL hδ f hf hdisj
  have hv := congrArg (fun z : U => z.val) he
  rw [finiteRetainedInteriorOriginalMap_val, finiteRetainedInteriorOriginalMap_val] at hv
  have hx : e.symm (Opens.inclusion inf_le_right q) = e.symm (Opens.inclusion inf_le_right r) := Subtype.ext hv
  exact Subtype.ext (congrArg (fun z : finiteCoreInteriorOpens hL hδ f hf hdisj => z.val) (e.symm.injective hx))

def finiteRetainedInteriorImage (R : Set (ConnectedComponents (cutCore f)))
    (p : coreInteriorDomain f)
    (hp : (⟨p.val, interior_subset p.property⟩ : cutCore f) ∈ retainedCore f R) :
    finiteRetainedInteriorOpens hL hδ f hf hdisj R :=
  ⟨finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj p,
    hp, ⟨⟨p.val, interior_subset p.property⟩, p.property, rfl⟩⟩

theorem finiteRetainedInteriorOriginalMap_image (U : Opens M) (R : Set (ConnectedComponents (cutCore f)))
    (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
    (p : coreInteriorDomain f)
    (hp : (⟨p.val, interior_subset p.property⟩ : cutCore f) ∈ retainedCore f R) :
    finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet
      (finiteRetainedInteriorImage hL hδ f hf hdisj R p hp) = ⟨p.val, hRet hp⟩ := by
  apply Subtype.ext
  change ((finiteCoreInteriorHomeomorph hL hδ f hf hdisj).symm
    (finiteCoreInteriorHomeomorph hL hδ f hf hdisj p)).val = p.val
  rw [Homeomorph.symm_apply_apply]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [ChartedSpace H M] [IsManifold I ∞ M]
variable (hdim : Module.finrank ℝ E = 3)
variable (hs : ∀ i, IsLocalDiffeomorph RetainedIC I ∞ (f i))

include hs in
theorem contMDiff_finiteRetainedInteriorOriginalMap (U : Opens M) (R : Set (ConnectedComponents (cutCore f)))
    (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U) :
    let : ChartedSpace RetainedE3 RetainedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ContMDiff (𝓡 3) I ∞ (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet) := by
  let : ChartedSpace RetainedE3 RetainedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let F := finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs
  apply (ContMDiff.subtypeVal_comp_iff U (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet)).mp
  exact (contMDiff_subtype_val (U := coreInteriorDomain f)).comp
    (F.symm.contMDiff.comp (contMDiff_inclusion inf_le_right))

include hs in
theorem finiteRetainedInteriorOriginalMap_mfderiv (U : Opens M) (R : Set (ConnectedComponents (cutCore f)))
    (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
    (q : finiteRetainedInteriorOpens hL hδ f hf hdisj R) :
    let : ChartedSpace RetainedE3 RetainedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    mfderiv (𝓡 3) I (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet) q =
      mfderiv (𝓡 3) I (finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs).symm
        (Opens.inclusion inf_le_right q) := by
  let : ChartedSpace RetainedE3 RetainedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let V := finiteRetainedInteriorOpens hL hδ f hf hdisj R
  let W := finiteCoreInteriorOpens hL hδ f hf hdisj
  let F := finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs
  let g := finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet
  let j : V → W := Opens.inclusion inf_le_right
  have hj : ContMDiff (𝓡 3) (𝓡 3) ∞ j := contMDiff_inclusion inf_le_right
  have hg : ContMDiff (𝓡 3) I ∞ g := contMDiff_finiteRetainedInteriorOriginalMap hL hδ f hf hdisj I hdim hs U R hRet
  have he : (Subtype.val : U → M) ∘ g = (Subtype.val : coreInteriorDomain f → M) ∘ (F.symm ∘ j) := rfl
  have hd := mfderiv_congr (I := 𝓡 3) (I' := I) (x := q) he
  have hleft : mfderiv (𝓡 3) I ((Subtype.val : U → M) ∘ g) q = mfderiv (𝓡 3) I g q := by
    rw [mfderiv_comp q ((contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiable (by simp) (g q))
      (hg.mdifferentiable (by simp) q), DifferentialGeometry.mfderiv_subtype_val]
    rfl
  have hright : mfderiv (𝓡 3) I ((Subtype.val : coreInteriorDomain f → M) ∘ (F.symm ∘ j)) q =
      mfderiv (𝓡 3) I (F.symm ∘ j) q := by
    rw [mfderiv_comp q ((contMDiff_subtype_val (U := coreInteriorDomain f) (n := ∞)).mdifferentiable (by simp) (F.symm (j q)))
      ((F.symm.contMDiff.comp hj).mdifferentiable (by simp) q), DifferentialGeometry.mfderiv_subtype_val]
    rfl
  have hinner : mfderiv (𝓡 3) I (F.symm ∘ j) q = mfderiv (𝓡 3) I F.symm (j q) := by
    rw [mfderiv_comp q (F.symm.contMDiff.mdifferentiable (by simp) (j q))
      (hj.mdifferentiable (by simp) q), DifferentialGeometry.mfderiv_opens_incl]
    rfl
  exact hleft.symm.trans (hd.trans (hright.trans hinner))

include hs in
theorem isLocalDiffeomorph_finiteRetainedInteriorOriginalMap (U : Opens M) (R : Set (ConnectedComponents (cutCore f)))
    (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U) :
    let : ChartedSpace RetainedE3 RetainedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsLocalDiffeomorph (𝓡 3) I ∞ (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet) := by
  let : ChartedSpace RetainedE3 RetainedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ RetainedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (contMDiff_finiteRetainedInteriorOriginalMap hL hδ f hf hdisj I hdim hs U R hRet) _ (by simpa using hdim.symm)
  intro q
  rw [finiteRetainedInteriorOriginalMap_mfderiv hL hδ f hf hdisj I hdim hs U R hRet q]
  exact ((finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs).symm.mfderivToContinuousLinearEquiv (by simp) _).injective
include hs in
theorem finiteRetainedInteriorOriginalMap_mfderiv_image_comp (U : Opens M) (R : Set (ConnectedComponents (cutCore f)))
    (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
    (p : coreInteriorDomain f)
    (hp : (⟨p.val, interior_subset p.property⟩ : cutCore f) ∈ retainedCore f R) :
    let : ChartedSpace RetainedE3 RetainedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    (mfderiv (𝓡 3) I (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet)
      (finiteRetainedInteriorImage hL hδ f hf hdisj R p hp)).comp
        (mfderiv I (𝓡 3) (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj) p) =
          ContinuousLinearMap.id ℝ (TangentSpace I p) := by
  let : ChartedSpace RetainedE3 RetainedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let V := finiteCoreInteriorOpens hL hδ f hf hdisj
  let F := finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs
  have hd := finiteRetainedInteriorOriginalMap_mfderiv hL hδ f hf hdisj I hdim hs U R hRet
    (finiteRetainedInteriorImage hL hδ f hf hdisj R p hp)
  change mfderiv (𝓡 3) I (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet)
      (finiteRetainedInteriorImage hL hδ f hf hdisj R p hp) = mfderiv (𝓡 3) I F.symm (F p) at hd
  have hold : mfderiv I (𝓡 3) (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj) p =
      mfderiv I (𝓡 3) F p := by
    change mfderiv I (𝓡 3) ((Subtype.val : V → RetainedQ) ∘ F) p = _
    rw [mfderiv_comp _ ((contMDiff_subtype_val (U := V) (n := ∞)).mdifferentiable (by simp) (F p))
      (F.contMDiff.mdifferentiable (by simp) p), DifferentialGeometry.mfderiv_subtype_val]
    rfl
  have hchain := mfderiv_comp p (F.symm.contMDiff.mdifferentiable (by simp) (F p))
    (F.contMDiff.mdifferentiable (by simp) p)
  have he : F.symm ∘ F = id := funext F.symm_apply_apply
  rw [he, mfderiv_id] at hchain
  dsimp only
  rw [hd, hold]
  exact hchain.symm
end DifferentialGeometry.Topology.ThreeManifold.Surgery
