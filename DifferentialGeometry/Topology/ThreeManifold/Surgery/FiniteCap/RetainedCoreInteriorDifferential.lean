import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreSmoothEmbedding
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreDomainSmooth
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDifferential

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev RetInteriorDE3 := EuclideanSpace ℝ (Fin 3)
private abbrev RetInteriorDE2 := EuclideanSpace ℝ (Fin 2)
private abbrev RetInteriorDIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev RetInteriorDIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev RetInteriorDIH := ModelProd RetInteriorDE2 (EuclideanHalfSpace 1)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph RetInteriorDIC I ∞ (f i))
local notation "RetInteriorDQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

include hs in
theorem finiteRetainedCoreInclusion_mfderiv_interior
    (R : Set (ConnectedComponents (cutCore f))) (U : Opens M)
    (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
    (p : retainedCore f R) (hp : p.val.val ∈ interior (cutCore f)) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace RetInteriorDIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : ChartedSpace RetInteriorDE3 RetInteriorDQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    mfderiv RetInteriorDIR (𝓡 3) (finiteRetainedCoreInclusion hL hδ f hf hdisj R) p =
      (mfderiv I (𝓡 3) (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj)
        (⟨p.val.val, hp⟩ : coreInteriorDomain f)).comp
        (mfderiv RetInteriorDIR I (retainedCoreDomainMap f R U hRet) p) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace RetInteriorDIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let : ChartedSpace RetInteriorDE3 RetInteriorDQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let V : Opens (retainedCore f R) :=
    ⟨{q | q.val.val ∈ interior (cutCore f)}, isOpen_interior.preimage (continuous_subtype_val.comp continuous_subtype_val)⟩
  let q : V := ⟨p, hp⟩
  let F : V → coreInteriorDomain f := fun r => ⟨r.val.val.val, r.property⟩
  let Ψ := retainedCoreDomainMap f R U hRet
  let Φ := finiteRetainedCoreInclusion hL hδ f hf hdisj R
  let Ξ := (Subtype.val : finiteCapRetained hL hδ f hf hdisj R → RetInteriorDQ) ∘ Φ
  let old := finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj
  let ambient : retainedCore f R → M := fun r => r.val.val
  have hAmb : ContMDiff RetInteriorDIR I ∞ ambient :=
    (retainedCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj R hs).contMDiff
  have hF : ContMDiff RetInteriorDIR I ∞ F :=
    (ContMDiff.subtypeVal_comp_iff (coreInteriorDomain f) F).mp
      (hAmb.comp (contMDiff_subtype_val (I := RetInteriorDIR) (U := V)))
  have hΦ : ContMDiff RetInteriorDIR (𝓡 3) ∞ Φ :=
    (finiteRetainedCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs R).contMDiff
  have hΞ : ContMDiff RetInteriorDIR (𝓡 3) ∞ Ξ :=
    (contMDiff_subtype_val (I := 𝓡 3) (U := finiteCapRetained hL hδ f hf hdisj R)).comp hΦ
  have hOld : ContMDiff I (𝓡 3) ∞ old := contMDiff_finiteCoreInteriorMap I hdim hL hδ f hf hdisj hs
  have hFder : mfderiv RetInteriorDIR I F q = mfderiv RetInteriorDIR I Ψ p :=
    (mfderiv_comp_open_val RetInteriorDIR I (coreInteriorDomain f) F hF q).symm.trans
      ((DifferentialGeometry.mfderiv_restrict_open
          (I := RetInteriorDIR) (J := I) ambient V q).trans
        (retainedCoreDomainMap_mfderiv I hdim hδ f hf hdisj hs R U hRet p).symm)
  have hcomp : mfderiv RetInteriorDIR (𝓡 3) (Ξ ∘ (Subtype.val : V → retainedCore f R)) q =
      (mfderiv I (𝓡 3) old (F q)).comp (mfderiv RetInteriorDIR I F q) :=
    mfderiv_comp q (hOld.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp))
  exact (mfderiv_comp_open_val RetInteriorDIR (𝓡 3) (finiteCapRetained hL hδ f hf hdisj R) Φ hΦ p).symm.trans
    (((DifferentialGeometry.mfderiv_restrict_open
        (I := RetInteriorDIR) (J := 𝓡 3) Ξ V q).symm.trans hcomp).trans
      (congrArg ((mfderiv I (𝓡 3) old (F q)).comp) hFder))
end DifferentialGeometry.Topology.ThreeManifold.Surgery
