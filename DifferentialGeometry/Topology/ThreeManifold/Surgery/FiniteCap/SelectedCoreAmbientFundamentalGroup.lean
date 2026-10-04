import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.SelectedCoreBoundaryCollar
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreCapComplement
import DifferentialGeometry.Topology.VanKampen.BoundaryCollarInjection
import DifferentialGeometry.Topology.Sphere.SphereSimplyConnected

/-!
# SelectedCoreAmbientFundamentalGroup
-/

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open DifferentialGeometry.Geometry.Neck
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
  [LocallyPathConnectedSpace M] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))

omit [Finite ι] [T2Space M] [LocallyPathConnectedSpace M] in
private theorem selectedSphere_paths_thin (R : Set (ConnectedComponents (cutCore f)))
    (x y : SelectedCuttingSpheres hδ f hf hdisj R) :
    Subsingleton (Path.Homotopic.Quotient x y) := by
  let B := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let : SimplyConnectedSpace S2 :=
    DifferentialGeometry.Topology.simplyConnectedSpace_sphere_of_two_le (by norm_num : 2 ≤ 2)
  let e : SelectedCuttingSpheres hδ f hf hdisj R ≃ₜ B × S2 := {
    toEquiv := Equiv.sigmaEquivProd B S2
    continuous_toFun := continuous_sigma (fun b => continuous_const.prodMk continuous_id)
    continuous_invFun := continuous_prod_of_discrete_left.mpr (fun b =>
      @continuous_sigmaMk B (fun b : B => S2) (fun b => inferInstance) b) }
  apply DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_of_homotopyEquiv
    e.toHomotopyEquiv
  exact DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_prod
    DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_of_totallyDisconnected
    (fun x y => inferInstance)

def retainedCoreAmbientInclusion (R : Set (ConnectedComponents (cutCore f))) :
    C(retainedCore f R, M) :=
  ⟨fun p => p.val.val, continuous_subtype_val.comp continuous_subtype_val⟩

include hδ hf hdisj in
theorem injective_fundamentalGroup_retainedCoreAmbientInclusion
    (c : ConnectedComponents (cutCore f)) (x : retainedCore f {c}) :
    Injective (FundamentalGroup.map (retainedCoreAmbientInclusion f {c}) x) := by
  let K : Set M := (Subtype.val : cutCore f → M) '' retainedCore f {c}
  let e : retainedCore f {c} ≃ₜ K :=
    _root_.Topology.IsEmbedding.subtypeVal.homeomorphImage (retainedCore f {c})
  let : PathConnectedSpace (retainedCore f {c}) :=
    retainedCore_singleton_pathConnectedSpace hδ f hdisj hf c
  let : PathConnectedSpace K := e.pathConnectedSpace
  let d := selectedCoreBoundaryCollar hδ f hf hdisj {c}
  have hi := d.injective_fundamentalGroup_map_domain
    (isClosed_selectedCore_ambient hδ f hf hdisj {c})
    (frontier_selectedCore_subset_sphere_range hδ f hf hdisj {c})
    (selectedCoreBoundaryCollar_mem_iff hδ f hf hdisj {c})
    (selectedSphere_paths_thin hδ f hf hdisj {c}) (e x)
  let emap : C(retainedCore f {c}, K) := e
  let einv : C(K, retainedCore f {c}) := e.symm
  have he := DifferentialGeometry.Topology.injective_fundamentalGroup_map_of_leftInverse
    emap einv e.left_inv x
  intro p q hpq
  apply he
  apply hi
  change (Path.Homotopic.Quotient.map p emap).map (VanKampen.subsetToAmbient K) =
    (Path.Homotopic.Quotient.map q emap).map (VanKampen.subsetToAmbient K)
  rw [← Path.Homotopic.Quotient.map_comp, ← Path.Homotopic.Quotient.map_comp]
  exact hpq

end DifferentialGeometry.Topology.ThreeManifold.Surgery
