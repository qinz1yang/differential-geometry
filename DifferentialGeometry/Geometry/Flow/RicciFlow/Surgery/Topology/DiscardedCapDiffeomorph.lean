import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapSmoothDescent
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

noncomputable section
open Set Function Manifold
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

private theorem injective_mfderiv_of_comp_isSmoothEmbedding
    {B D Y : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanHalfSpace 3) B]
    [TopologicalSpace D] [ChartedSpace ThreeSpace D]
    [TopologicalSpace Y] [ChartedSpace ThreeSpace Y]
    {f : D → Y} (hf : ContMDiff ThreeModel ThreeModel ∞ f)
    (j : B → D) (k : B → Y)
    (hj : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ j)
    (hk : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ k)
    (heq : f ∘ j = k) (x : B) :
    Injective (mfderiv ThreeModel ThreeModel f (j x)) := by
  have hd : (mfderiv (𝓡∂ 3) ThreeModel (f ∘ j) x : ThreeSpace →L[ℝ] ThreeSpace) =
      mfderiv (𝓡∂ 3) ThreeModel k x := by rw [heq]
  rw [mfderiv_comp x (hf.mdifferentiable (by simp) _) (hj.contMDiff.mdifferentiable (by simp) _)] at hd
  have hi : Injective ((mfderiv ThreeModel ThreeModel f (j x)).comp
      (mfderiv (𝓡∂ 3) ThreeModel j x)) := by
    rw [hd]
    exact hk.isImmersion.isImmersionAt x |>.mfderiv_injective (by simp)
  change Injective ((mfderiv ThreeModel ThreeModel f (j x)) ∘
    (mfderiv (𝓡∂ 3) ThreeModel j x)) at hi
  exact Function.Injective.of_comp_right
    (f := (mfderiv ThreeModel ThreeModel f (j x)))
    (g := (mfderiv (𝓡∂ 3) ThreeModel j x)) hi
    (DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt
      (𝓡∂ 3) ThreeModel j x (hj.isImmersion.isImmersionAt x) (by simp [ThreeSpace])).surjective

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace ThreeSpace Y] [IsManifold ThreeModel ∞ Y]
  [hCompact : CompactSpace {x : (H.event i).transition.trace.tubes.core //
    x ∉ (H.event i).transition.trace.retainedCore}]
  (fCore : C({x : (H.event i).transition.trace.tubes.core //
    x ∉ (H.event i).transition.trace.retainedCore}, Y))
  (fCap : (b : {b : (H.event i).transition.trace.tubes.Boundary //
    (H.event i).transition.trace.capDiscarded b}) → C(ThreeBall, Y))
  (hboundary : ∀ (b : {b : (H.event i).transition.trace.tubes.Boundary //
      (H.event i).transition.trace.capDiscarded b}) (s : Sphere 2),
    fCap b (sphereToThreeBall s) = fCore
      ⟨(H.event i).transition.trace.tubes.coreBoundarySphere b.1
          ((H.event i).transition.trace.capping.attaching b.1 s),
        (H.event i).transition.trace.capDiscarded_coreBoundarySphere_not_mem_retainedCore
          b.1 b.2 _⟩)

include hCompact in
theorem exists_discardedDesc_diffeomorph_of_collar_profiles
    (hfCore : let : ChartedSpace (EuclideanHalfSpace 3) {x : (H.event i).transition.trace.tubes.core //
          x ∉ (H.event i).transition.trace.retainedCore} :=
        (H.event i).transition.coreOpensCharts (H.event i).transition.trace.discardedCoreOpen
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ fCore)
    (hfCap : let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := (H.event i).transition.ballCharts
      ∀ b, IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (fCap b))
    (hinter : ∀ b, range fCore ∩ range (fCap b) = range (fCap b ∘ sphereToThreeBall))
    (hdisj : Pairwise fun b c => Disjoint (range (fCap b)) (range (fCap c)))
    (hcover : range fCore ∪ (⋃ b, range (fCap b)) = univ)
    (c : (b : {b : (H.event i).transition.trace.tubes.Boundary //
        (H.event i).transition.trace.capDiscarded b}) →
      DifferentialGeometry.Topology.SmoothTwoSidedCollar (𝓡 2) ThreeModel
        (fun s : Sphere 2 =>
          (H.event i).transition.trace.discardedCap b.1 b.2 (sphereToThreeBall s)))
    (hwidth : ∀ b, (c b).radius ≤ cuttingCollarWidth (G.delta b.1.1))
    (capSide : (b : {b : (H.event i).transition.trace.tubes.Boundary //
        (H.event i).transition.trace.capDiscarded b}) →
      {q : Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval (c b).radius //
        q.2.val ≤ 0} → ThreeBall)
    (hcore : ∀ b q (hq : 0 ≤ q.2.val), (c b).toFun q = G.discardedCoreCollar b.1 b.2
      ((H.event i).transition.trace.capping.attaching b.1 q.1,
        ⟨q.2.val, hq, q.2.property.2.trans_le (hwidth b)⟩))
    (hcap : ∀ b q (hq : q.2.val ≤ 0), (c b).toFun q =
      (H.event i).transition.trace.discardedCap b.1 b.2 (capSide b ⟨q, hq⟩))
    (profile : (b : {b : (H.event i).transition.trace.tubes.Boundary //
        (H.event i).transition.trace.capDiscarded b}) →
      Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval (c b).radius → Y)
    (hsmooth : ∀ b, ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (profile b))
    (hprofileCore : ∀ b q (hq : 0 ≤ q.2.val), profile b q = fCore
      ⟨G.coreCollar b.1 ((H.event i).transition.trace.capping.attaching b.1 q.1,
          ⟨q.2.val, hq, q.2.property.2.trans_le (hwidth b)⟩),
        G.coreCollar_not_mem_retainedCore_of_capDiscarded b.1 b.2 sphereNorth _⟩)
    (hprofileCap : ∀ b q (hq : q.2.val ≤ 0), profile b q = fCap b (capSide b ⟨q, hq⟩)) :
    ∃ e : Diffeomorph ThreeModel ThreeModel (H.event i).discarded.Carrier Y ∞,
      (e : (H.event i).discarded.Carrier → Y) =
        (H.event i).transition.trace.discardedDesc fCore fCap hboundary ∧
      (∀ x, e ((H.event i).transition.trace.discardedCoreInclusion x) = fCore x) ∧
      ∀ b x, e ((H.event i).transition.trace.discardedCap b.1 b.2 x) = fCap b x := by
  let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).transition.trace.tubes.core :=
    (H.event i).transition.coreCharts
  let : IsManifold (𝓡∂ 3) ∞ (H.event i).transition.trace.tubes.core :=
    (H.event i).transition.coreSmooth
  let : ChartedSpace (EuclideanHalfSpace 3) {x : (H.event i).transition.trace.tubes.core //
      x ∉ (H.event i).transition.trace.retainedCore} :=
    (H.event i).transition.coreOpensCharts (H.event i).transition.trace.discardedCoreOpen
  let : IsManifold (𝓡∂ 3) ∞ {x : (H.event i).transition.trace.tubes.core //
      x ∉ (H.event i).transition.trace.retainedCore} :=
    inferInstanceAs (IsManifold (𝓡∂ 3) ∞ (H.event i).transition.trace.discardedCoreOpen)
  let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := (H.event i).transition.ballCharts
  let : IsManifold (𝓡∂ 3) ∞ ThreeBall := (H.event i).transition.ballSmooth
  let f := (H.event i).transition.trace.discardedDesc fCore fCap hboundary
  have hf : ContMDiff ThreeModel ThreeModel ∞ f :=
    G.discardedDesc_contMDiff_of_collar_profiles ThreeModel fCore fCap hboundary
      (fun x _ => hfCore.contMDiff x) (fun b x _ => (hfCap b).contMDiff x)
      c hwidth capSide hcore hcap profile hsmooth hprofileCore hprofileCap
  have hD : ∀ y, Injective (mfderiv ThreeModel ThreeModel f y) := by
    intro y
    have hy : y ∈ range (H.event i).transition.trace.discardedCoreInclusion ∪
        ⋃ b : {b : (H.event i).transition.trace.tubes.Boundary //
          (H.event i).transition.trace.capDiscarded b},
          range ((H.event i).transition.trace.discardedCap b.1 b.2) := by
      rw [(H.event i).transition.trace.discardedCoreInclusion_union_discardedCaps]
      exact mem_univ _
    rcases hy with ⟨x, rfl⟩ | hy
    · exact injective_mfderiv_of_comp_isSmoothEmbedding hf _ _ (H.event i).transition.discardedCoreInclusion_isSmoothEmbedding hfCore
        (funext ((H.event i).transition.trace.discardedDesc_core fCore fCap hboundary)) x
    · obtain ⟨b, x, rfl⟩ := mem_iUnion.mp hy
      exact injective_mfderiv_of_comp_isSmoothEmbedding hf _ _ ((H.event i).transition.discardedCap_isSmoothEmbedding b.1 b.2) (hfCap b)
        (funext ((H.event i).transition.trace.discardedDesc_cap fCore fCap hboundary b)) x
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv f hf hD rfl
  have hbij : Bijective f :=
    ⟨(H.event i).transition.trace.discardedDesc_injective_of_cap_intersections fCore fCap hboundary
      hfCore.isEmbedding.injective (fun b => (hfCap b).isEmbedding.injective) hinter hdisj,
      (H.event i).transition.trace.discardedDesc_surjective_of_cover fCore fCap hboundary hcover⟩
  exact ⟨hlocal.diffeomorphOfBijective hbij, rfl,
    (H.event i).transition.trace.discardedDesc_core fCore fCap hboundary,
    (H.event i).transition.trace.discardedDesc_cap fCore fCap hboundary⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord
