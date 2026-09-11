import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.ModelThreeSmooth
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSmoothOverlap

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev ForwardE3 := EuclideanSpace ℝ (Fin 3)
private abbrev ForwardIC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ ForwardE3 = 2 + 1) := ⟨by simp⟩
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
variable [IsManifold I ∞ M] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))

theorem contDiffOn_finiteCap_to_coreThree
    (hs : ∀ i, ContMDiff ForwardIC I ∞ (f i)) (b : ι × Bool) (p : coreInteriorDomain f) :
    ContDiffOn ℝ ∞
      ((finiteCapOpenChart hL hδ f hf hdisj b).symm.trans
        (finiteCoreThreeChart I hdim hL hδ f hf hdisj p))
      ((finiteCapOpenChart hL hδ f hf hdisj b).symm.trans
        (finiteCoreThreeChart I hdim hL hδ f hf hdisj p)).source := by
  let e := finiteCapOpenChart hL hδ f hf hdisj b
  let c := finiteCoreThreeChart I hdim hL hδ f hf hdisj p
  let old := finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj
  intro x hx
  change x ∈ e.target ∧ e.symm x ∈ c.source at hx
  have hsource : e.symm x ∈ old '' (chartAt H p).source := hx.2
  obtain ⟨q, hq, heq⟩ := hsource
  have hI : e.symm x ∈ finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj := by
    rw [← range_finiteCoreInteriorMap]
    exact ⟨q, heq⟩
  have hA : x ∈ cuttingAnnulus L (precision b.1) := by
    change L < ‖x‖ ∧ ‖x‖ < L + cuttingCollarWidth (precision b.1)
    have him : x ∈ e '' (e.source ∩ finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj) :=
      ⟨e.symm x, ⟨e.map_target hx.1, hI⟩, e.right_inv hx.1⟩
    rw [finiteCapOpenChart_interior_overlap_image hL hδ f hf hdisj b] at him
    exact him
  let a : cuttingAnnulus L (precision b.1) := ⟨x, hA⟩
  let g := finiteCapAnnulusOldMap hL hδ f hf hdisj b
  have hqa : q = g a := by
    apply (isOpenEmbedding_finiteCoreInteriorMap hL hδ f hf hdisj).injective
    exact heq.trans (finiteCapOpenChart_symm_annulus hL hδ f hf hdisj b a)
  have hag : (g a).val ∈ (chartAt H p.val).source := by
    subst q
    simpa only [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hq
  have hg : ContMDiff (𝓡 3) I ∞ (fun z => (g z).val) :=
    (contMDiff_subtype_val (I := I) (U := coreInteriorDomain f)).comp
      (contMDiff_finiteCapAnnulusOldMap hL hδ f hf hdisj hs b)
  have hc : ContMDiffAt I I ∞ (chartAt H p.val) (g a).val :=
    (contMDiffOn_chart (I := I) (n := ∞)).contMDiffAt ((chartAt H p.val).open_source.mem_nhds hag)
  have ht : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (fun z : cuttingAnnulus L (precision b.1) => c (e.symm z.val)) a := by
    have hcomp := (modelThreeDiffeomorph I hdim).contMDiff.contMDiffAt.comp a (hc.comp a hg.contMDiffAt)
    have he : (fun z : cuttingAnnulus L (precision b.1) => c (e.symm z.val)) =
        (fun z => modelThreeDiffeomorph I hdim (chartAt H p.val (g z).val)) := by
      funext z
      exact finiteCoreThreeChart_annulus_transition hL hδ f hf hdisj hdim p b z
    rw [he]
    exact hcomp
  have ht' : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun z => c (e.symm z)) x :=
    (contMDiffAt_subtype_iff (I := 𝓡 3) (I' := 𝓡 3)
      (U := cuttingAnnulus L (precision b.1)) (f := fun z => c (e.symm z)) (x := a)).mp ht
  exact ht'.contDiffAt.contDiffWithinAt
end DifferentialGeometry.Topology.ThreeManifold.Surgery
