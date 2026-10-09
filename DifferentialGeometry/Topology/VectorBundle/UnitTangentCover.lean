import DifferentialGeometry.Topology.VectorBundle.ZeroSectionSplit
import DifferentialGeometry.Topology.VectorBundle.UnitOrientation
import DifferentialGeometry.Topology.VectorBundle.LineSection
import DifferentialGeometry.Topology.Manifold.OrientationCoverComponents
import DifferentialGeometry.Topology.Manifold.BoundaryOrientationVariation
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

/-!
# Unit vectors identify the actual tangent orientation double cover

The derivative of the zero section and the vertical derivative split the actual total tangent
space. An orientation of that space and a unit normal induce a base tangent orientation. Local
vector-bundle coordinates prove continuity, while reversing the normal reverses the orientation.
Compactness turns the resulting bijection into a homeomorphism over the original base.
-/

set_option autoImplicit false

noncomputable section

open Bundle Module Filter Set Function TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.VectorBundle

open DifferentialGeometry.Topology.Manifold

variable {EB F : Type*} [baseNormGroup : NormedAddCommGroup EB] [baseNormSpace : NormedSpace ℝ EB]
  [baseFinite : FiniteDimensional ℝ EB] [fibreNormGroup : NormedAddCommGroup F] [fibreNormSpace :
    NormedSpace ℝ F]
  [fibreFiniteModel : FiniteDimensional ℝ F]
  {B : Type*} [baseTopology : TopologicalSpace B] [baseCharts : ChartedSpace EB B] [baseManifold
    : IsManifold 𝓘(ℝ, EB) ∞ B]
  {V : B → Type*} [totalTopology : TopologicalSpace (TotalSpace F V)]
  [fibreGroups : ∀ b, NormedAddCommGroup (V b)] [fibreInnerProducts : ∀ b, InnerProductSpace ℝ (V
    b)]
  [fibreBundle : FiberBundle F V] [vectorBundle : VectorBundle ℝ F V] [smoothBundle :
    ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)]

private def unitLineEquiv (h1 : finrank ℝ F = 1) (b : B) (u : {u : V b // ‖u‖ = 1}) :
    ℝ ≃L[ℝ] V b := by
  let fibreFinite : FiniteDimensional ℝ (V b) :=
    ((trivializationAt F V b).continuousLinearEquivAt ℝ b
      (FiberBundle.mem_baseSet_trivializationAt F V b)).symm.toLinearEquiv.finiteDimensional
  have hn : u.val ≠ 0 := by
    intro hz
    have hu := u.property
    rw [hz, norm_zero] at hu
    exact zero_ne_one hu
  let bu := FiniteDimensional.basisSingleton (Fin 1)
    ((finrank_fiber_eq (F := F) (V := V) b).trans h1) u.val hn
  exact ((Basis.singleton (Fin 1) ℝ).equiv bu (Equiv.refl _)).toContinuousLinearEquiv

private theorem unitLineEquiv_apply (h1 : finrank ℝ F = 1) (b : B)
    (u : {u : V b // ‖u‖ = 1}) (a : ℝ) : unitLineEquiv h1 b u a = a • u.val := by
  have hn : u.val ≠ 0 := by
    intro hz
    have hu := u.property
    rw [hz, norm_zero] at hu
    exact zero_ne_one hu
  let bu : Basis (Fin 1) ℝ (V b) := FiniteDimensional.basisSingleton (Fin 1)
    ((finrank_fiber_eq (F := F) (V := V) b).trans h1) u.val hn
  have he : unitLineEquiv h1 b u 1 = u.val := by
    change (Basis.singleton (Fin 1) ℝ).equiv bu (Equiv.refl _) 1 = u.val
    have hh := Basis.equiv_apply (Basis.singleton (Fin 1) ℝ) 0 bu (Equiv.refl _)
    simpa only [Basis.singleton_apply, Equiv.refl_apply, bu,
      FiniteDimensional.basisSingleton_apply] using hh
  calc
    unitLineEquiv h1 b u a = unitLineEquiv h1 b u (a • (1 : ℝ)) := by simp
    _ = a • u.val := by rw [map_smul, he]

private def unitSplitEquiv (h1 : finrank ℝ F = 1) (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    (ℝ × EB) ≃L[ℝ] (EB × F) := by
  let fibreFinite : FiniteDimensional ℝ (V z.val.proj) :=
    ((trivializationAt F V z.val.proj).continuousLinearEquivAt ℝ z.val.proj
      (FiberBundle.mem_baseSet_trivializationAt F V
    z.val.proj)).symm.toLinearEquiv.finiteDimensional
  let L := LinearEquiv.ofBijective
    (zeroSectionTangentSplit (F := F) (IB := 𝓘(ℝ, EB)) (V := V) z.val.proj).toLinearMap
    (zeroSectionTangentSplit_bijective (F := F) (IB := 𝓘(ℝ, EB)) (V := V) z.val.proj)
  exact ((unitLineEquiv h1 z.val.proj ⟨z.val.2, z.property⟩).prodCongr
    (ContinuousLinearEquiv.refl ℝ EB)).trans L.toContinuousLinearEquiv

private theorem unitSplitEquiv_apply (h1 : finrank ℝ F = 1)
    (z : {z : TotalSpace F V // ‖z.2‖ = 1}) (a : ℝ) (w : EB) :
    unitSplitEquiv (EB := EB) h1 z (a, w) = zeroSectionTangentSplit
      (F := F) (IB := 𝓘(ℝ, EB)) (V := V) z.val.proj (a • z.val.2, w) := by
  change zeroSectionTangentSplit (F := F) (IB := 𝓘(ℝ, EB)) (V := V) z.val.proj
    (unitLineEquiv h1 z.val.proj ⟨z.val.2, z.property⟩ a, w) = _
  rw [unitLineEquiv_apply]

private def zeroAmbientOrientation
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3) (b : B) :
    Orientation ℝ (EB × F) (Fin 3) := o.orientation (zeroSection F V b)

def unitTangentOrientation (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3)
    (z : {z : TotalSpace F V // ‖z.2‖ = 1}) : Orientation ℝ EB (Fin 2) :=
  normalFirstOrientation (unitSplitEquiv (EB := EB) h1 z).toLinearEquiv
    ((Module.finBasis ℝ EB).reindex (finCongr h2))
    (zeroAmbientOrientation o z.val.proj)

theorem unitTangentOrientation_neg (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3)
    (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    unitTangentOrientation (EB := EB) h2 h1 o ⟨⟨z.val.proj, -z.val.2⟩,
      by simpa using z.property⟩ = -unitTangentOrientation (EB := EB) h2 h1 o z := by
  have he : (unitSplitEquiv (EB := EB) h1 ⟨⟨z.val.proj, -z.val.2⟩,
      by simpa using z.property⟩).toLinearEquiv =
      normalFirstReflection.trans (unitSplitEquiv (EB := EB) h1 z).toLinearEquiv := by
    apply LinearEquiv.ext
    rintro ⟨a, w⟩
    change unitSplitEquiv (EB := EB) h1 _ (a, w) =
      unitSplitEquiv (EB := EB) h1 z (-a, w)
    rw [unitSplitEquiv_apply, unitSplitEquiv_apply]
    congr 1
    exact Prod.ext (by simp) rfl
  unfold unitTangentOrientation
  rw [he]
  exact normalFirstOrientation_reflect_normal _ _ _


def unitTangentCoverMap (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3)
    (z : {z : TotalSpace F V // ‖z.2‖ = 1}) : tangentOrientationCover (M := B) h2 :=
  ⟨z.val.proj, unitTangentOrientation (EB := EB) h2 h1 o z⟩

theorem unitTangentCoverMap_bijective (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3) :
    Function.Bijective (unitTangentCoverMap (EB := EB) h2 h1 o) := by
  constructor
  · rintro ⟨⟨b, u⟩, hu⟩ ⟨⟨c, v⟩, hv⟩ heq
    have hb : b = c := congrArg TotalSpace.proj heq
    subst c
    have hrank : finrank ℝ (V b) = 1 := (finrank_fiber_eq (F := F) (V := V) b).trans h1
    rcases RankOneQuotient.eq_or_eq_neg_of_finrank_eq_one hrank hu hv with hh | hh
    · change v = u at hh
      subst v
      rfl
    · change v = -u at hh
      subst v
      have hq : unitTangentOrientation (EB := EB) h2 h1 o ⟨⟨b, u⟩, hu⟩ =
          unitTangentOrientation (EB := EB) h2 h1 o ⟨⟨b, -u⟩, hv⟩ := by
        change (⟨b, unitTangentOrientation (EB := EB) h2 h1 o ⟨⟨b, u⟩, hu⟩⟩ :
          tangentOrientationCover (M := B) h2) = _ at heq
        exact TotalSpace.mk_injective b heq
      have hn := unitTangentOrientation_neg h2 h1 o ⟨⟨b, u⟩, hu⟩
      exact False.elim (Module.Ray.ne_neg_self _ (hq.trans hn))
  · rintro ⟨b, q⟩
    have hrank : finrank ℝ (V b) = 1 := (finrank_fiber_eq (F := F) (V := V) b).trans h1
    obtain ⟨u, hu⟩ := RankOneQuotient.exists_norm_eq_one_of_finrank_eq_one hrank
    let z : {z : TotalSpace F V // ‖z.2‖ = 1} := ⟨⟨b, u⟩, hu⟩
    have hdim : Fintype.card (Fin 2) = finrank ℝ EB := by simpa using h2.symm
    rcases q.eq_or_eq_neg (unitTangentOrientation (EB := EB) h2 h1 o z) hdim with hh | hh
    · exact ⟨z, congrArg (fun r : Orientation ℝ EB (Fin 2) =>
        (⟨b, r⟩ : tangentOrientationCover (M := B) h2)) hh.symm⟩
    · let zn : {z : TotalSpace F V // ‖z.2‖ = 1} :=
        ⟨⟨b, -u⟩, by simpa using hu⟩
      have hneg : unitTangentOrientation (EB := EB) h2 h1 o zn = q :=
        (unitTangentOrientation_neg h2 h1 o z).trans hh.symm
      exact ⟨zn, congrArg (fun r : Orientation ℝ EB (Fin 2) =>
        (⟨b, r⟩ : tangentOrientationCover (M := B) h2)) hneg⟩


private def unitChartDomain (c : B) : Opens {z : TotalSpace F V // ‖z.2‖ = 1} :=
  ⟨{z | z.val.proj ∈ (chartAt EB c).source ∧
    z.val.proj ∈ (trivializationAt F V c).baseSet ∧
    zeroSection F V z.val.proj ∈
      (chartAt (ModelProd EB F) (zeroSection F V c)).source}, by
    have hp : Continuous (fun z : {z : TotalSpace F V // ‖z.2‖ = 1} => z.val.proj) :=
      (FiberBundle.continuous_proj F V).comp continuous_subtype_val
    exact ((chartAt EB c).open_source.preimage hp).inter
      (((trivializationAt F V c).open_baseSet.preimage hp).inter
        ((chartAt (ModelProd EB F) (zeroSection F V c)).open_source.preimage
          ((Bundle.contMDiff_zeroSection (IB := 𝓘(ℝ, EB)) (n := ∞) ℝ V).continuous.comp hp)))⟩

private def unitChartFrame (h1 : finrank ℝ F = 1) (c : B) (z : unitChartDomain (EB := EB) (F :=
    F) (V := V) c) :
    (ℝ × EB) ≃L[ℝ] (EB × F) :=
  (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (preferredChartTangentEquiv 𝓘(ℝ, EB) c z.val.val.proj z.property.1).symm).trans
      (unitSplitEquiv (EB := EB) h1 z.val)).trans
    (preferredChartTangentEquiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F))
      (zeroSection F V c) (zeroSection F V z.val.val.proj) z.property.2.2)

private theorem unitChartFrame_apply (h1 : finrank ℝ F = 1) (c : B)
    (z : unitChartDomain (EB := EB) (F := F) (V := V) c) (a : ℝ) (w : EB) :
    unitChartFrame (EB := EB) h1 c z (a, w) =
      (w, a • (trivializationAt F V c).continuousLinearMapAt ℝ z.val.val.proj z.val.val.2) := by
  have hz : z.val.val.proj ∈ (chartAt EB c).source ∧
      z.val.val.proj ∈ (trivializationAt F V c).baseSet ∧
      zeroSection F V z.val.val.proj ∈
        (chartAt (ModelProd EB F) (zeroSection F V c)).source := z.property
  change preferredChartTangentEquiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F))
    (zeroSection F V c) (zeroSection F V z.val.val.proj) hz.2.2
    (unitSplitEquiv (EB := EB) h1 z.val
      (a, (preferredChartTangentEquiv 𝓘(ℝ, EB) c z.val.val.proj hz.1).symm w)) = _
  rw [unitSplitEquiv_apply]
  change mfderiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) 𝓘(ℝ, EB × F)
    (extChartAt (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (zeroSection F V c))
    (zeroSection F V z.val.val.proj)
    (zeroSectionTangentSplit (F := F) (IB := 𝓘(ℝ, EB)) (V := V) z.val.val.proj
      (a • z.val.val.2, (preferredChartTangentEquiv 𝓘(ℝ, EB) c z.val.val.proj hz.1).symm w)) = _
  have ht := zeroSectionTangentSplit_chart (F := F) (IB := 𝓘(ℝ, EB)) (V := V)
    c z.val.val.proj (a • z.val.val.2)
    ((preferredChartTangentEquiv 𝓘(ℝ, EB) c z.val.val.proj hz.1).symm w) hz.2.1 hz.1
  exact ht.trans (Prod.ext
    ((preferredChartTangentEquiv 𝓘(ℝ, EB) c z.val.val.proj hz.1).apply_symm_apply w)
    (map_smul _ _ _))

private theorem unitChartFrame_continuous (h1 : finrank ℝ F = 1) (c : B) :
    Continuous (fun z : unitChartDomain (EB := EB) (F := F) (V := V) c =>
      (unitChartFrame (EB := EB) h1 c z : (ℝ × EB) →L[ℝ] (EB × F))) := by
  apply continuous_clm_apply.mpr
  rintro ⟨a, w⟩
  have hc : Continuous (fun z : unitChartDomain (EB := EB) (F := F) (V := V) c =>
      ((trivializationAt F V c) z.val.val).2) :=
    ((trivializationAt F V c).continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun z => (trivializationAt F V c).mem_source.mpr z.property.2.1)).snd
  have he : (fun z : unitChartDomain (EB := EB) (F := F) (V := V) c =>
      (trivializationAt F V c).continuousLinearMapAt ℝ z.val.val.proj z.val.val.2) =
      fun z => ((trivializationAt F V c) z.val.val).2 := by
    funext z
    exact (trivializationAt F V c).continuousLinearMapAt_apply_of_mem ℝ
      z.property.2.1 z.val.val.2
  change Continuous (fun z : unitChartDomain (EB := EB) (F := F) (V := V) c =>
    unitChartFrame (EB := EB) h1 c z (a, w))
  simp_rw [unitChartFrame_apply]
  exact Continuous.congr (continuous_const.prodMk (hc.const_smul a))
    (fun z => Prod.ext rfl (congrArg (fun v : F => a • v) (congrFun he z).symm))

private def unitChartAmbientOrientation
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3) (c : B)
    (z : unitChartDomain (EB := EB) (F := F) (V := V) c) :
    Orientation ℝ (EB × F) (Fin 3) :=
  Orientation.map (Fin 3)
    (preferredChartTangentEquiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (zeroSection F V c)
      (zeroSection F V z.val.val.proj) z.property.2.2).toLinearEquiv
    (zeroAmbientOrientation o z.val.val.proj)

private theorem unitChartAmbientOrientation_locallyConstant
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3) (c : B) :
    IsLocallyConstant (unitChartAmbientOrientation o c) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  have hx : zeroSection F V x.val.val.proj ∈
      (trivializationAt (EB × F) (TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)))
        (zeroSection F V c)).baseSet := x.property.2.2
  obtain ⟨U, hU, hxU, hUs, heq⟩ :=
    o.locally_constant (zeroSection F V c) (zeroSection F V x.val.val.proj) hx
  have hp : Continuous (fun z : unitChartDomain (EB := EB) (F := F) (V := V) c =>
      zeroSection F V z.val.val.proj) :=
    (Bundle.contMDiff_zeroSection (IB := 𝓘(ℝ, EB)) (n := ∞) ℝ V).continuous.comp
      ((FiberBundle.continuous_proj F V).comp
        (continuous_subtype_val.comp continuous_subtype_val))
  refine ⟨(fun z => zeroSection F V z.val.val.proj) ⁻¹' U, hU.preimage hp, hxU, ?_⟩
  intro y hy
  have hh := heq (zeroSection F V y.val.val.proj) hy
  have hyc : zeroSection F V y.val.val.proj ∈
      (chartAt (ModelProd EB F) (zeroSection F V c)).source := y.property.2.2
  have hxc : zeroSection F V x.val.val.proj ∈
      (chartAt (ModelProd EB F) (zeroSection F V c)).source := x.property.2.2
  have ht1 := tangentChartEquiv_eq_preferredChartTangentEquiv
    (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (zeroSection F V c) (zeroSection F V y.val.val.proj) hyc
  have ht2 := tangentChartEquiv_eq_preferredChartTangentEquiv
    (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (zeroSection F V c) (zeroSection F V x.val.val.proj) hxc
  exact (congrArg (fun L => Orientation.map (Fin 3) L
    (o.orientation (zeroSection F V y.val.val.proj))) ht1.symm).trans
      (hh.trans (congrArg (fun L => Orientation.map (Fin 3) L
        (o.orientation (zeroSection F V x.val.val.proj))) ht2))

private theorem unitChartOrientation_eq (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3) (c : B)
    (z : unitChartDomain (EB := EB) (F := F) (V := V) c) :
    Orientation.map (Fin 2)
      (preferredChartTangentEquiv 𝓘(ℝ, EB) c z.val.val.proj z.property.1).toLinearEquiv
      (unitTangentOrientation (EB := EB) h2 h1 o z.val) =
    normalFirstOrientation (unitChartFrame (EB := EB) h1 c z).toLinearEquiv
      ((Module.finBasis ℝ EB).reindex (finCongr h2)) (unitChartAmbientOrientation o c z) := by
  let b := (Module.finBasis ℝ EB).reindex (finCongr h2)
  let g := (preferredChartTangentEquiv 𝓘(ℝ, EB) c z.val.val.proj z.property.1).symm
  let e := (unitSplitEquiv (EB := EB) h1 z.val).toLinearEquiv
  let A := (preferredChartTangentEquiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F))
    (zeroSection F V c) (zeroSection F V z.val.val.proj) z.property.2.2).toLinearEquiv
  have hm := normalFirstOrientation_map
    (((LinearEquiv.refl ℝ ℝ).prodCongr g.toLinearEquiv).trans e) A b
    (zeroAmbientOrientation o z.val.val.proj)
  have hb := normalFirstOrientation_change_boundary e g.toLinearEquiv b b
    (zeroAmbientOrientation o z.val.val.proj)
  exact hb.symm.trans hm.symm

attribute [local instance] DifferentialGeometry.VectorBundle.orientationTopology

private theorem unitChartOrientation_locallyConstant
    (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3) (c : B) :
    IsLocallyConstant (fun z : unitChartDomain (EB := EB) (F := F) (V := V) c =>
      Orientation.map (Fin 2)
        (preferredChartTangentEquiv 𝓘(ℝ, EB) c z.val.val.proj z.property.1).toLinearEquiv
        (unitTangentOrientation (EB := EB) h2 h1 o z.val)) := by
  have hh := normalFirstOrientation_locallyConstant_field
    (unitChartFrame (EB := EB) h1 c) ((Module.finBasis ℝ EB).reindex (finCongr h2))
    (unitChartFrame_continuous h1 c) (unitChartAmbientOrientation o c)
    (unitChartAmbientOrientation_locallyConstant o c)
  convert hh using 1
  funext z
  exact unitChartOrientation_eq h2 h1 o c z

private theorem unitTangentCoverMap_chart (h2 : finrank ℝ EB = 2)
    (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3) (c : B)
    (z : unitChartDomain (EB := EB) (F := F) (V := V) c) :
    let Z := DifferentialGeometry.VectorBundle.orientationCore (tangentBundleCore 𝓘(ℝ, EB) B) h2
    (Z.localTriv (achart EB c) (unitTangentCoverMap (EB := EB) h2 h1 o z.val)).2 =
      Orientation.map (Fin 2)
        (preferredChartTangentEquiv 𝓘(ℝ, EB) c z.val.val.proj z.property.1).toLinearEquiv
        (unitTangentOrientation (EB := EB) h2 h1 o z.val) := by
  have hzc : z.val.val.proj ∈ (chartAt EB c).source := z.property.1
  let q : Orientation ℝ (TangentSpace 𝓘(ℝ, EB) z.val.val.proj) (Fin 2) :=
    unitTangentOrientation (EB := EB) h2 h1 o z.val
  have hh := (tangentOrientation_chart (E := EB) (M := B) h2 c z.val.val.proj hzc q).2
  have ht := continuousLinearEquivAt_trivializationAt_eq_preferredChartTangentEquiv
    (E := EB) (M := B) 𝓘(ℝ, EB) c z.val.val.proj hzc
  exact hh.trans (congrArg
    (fun L : TangentSpace 𝓘(ℝ, EB) z.val.val.proj ≃L[ℝ] EB =>
      Orientation.map (Fin 2) L.toLinearEquiv q) ht)

theorem unitTangentCoverMap_continuous (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3) :
    Continuous (unitTangentCoverMap (EB := EB) h2 h1 o) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let c := x.val.proj
  let U := unitChartDomain (EB := EB) (F := F) (V := V) c
  have hx : x ∈ U := ⟨mem_chart_source EB c, mem_baseSet_trivializationAt F V c,
    mem_chart_source (ModelProd EB F) (zeroSection F V c)⟩
  let Z := DifferentialGeometry.VectorBundle.orientationCore (tangentBundleCore 𝓘(ℝ, EB) B) h2
  let t := Z.localTriv (achart EB c)
  have htx : unitTangentCoverMap (EB := EB) h2 h1 o x ∈ t.source := mem_chart_source EB c
  apply (t.tendsto_nhds_iff htx).mpr
  refine ⟨(FiberBundle.continuous_proj F V).continuousAt.comp
    continuousAt_subtype_val, ?_⟩
  have hfun : (fun z : U => (t (unitTangentCoverMap (EB := EB) h2 h1 o z.val)).2) =
      fun z : U => Orientation.map (Fin 2)
        (preferredChartTangentEquiv 𝓘(ℝ, EB) c z.val.val.proj z.property.1).toLinearEquiv
        (unitTangentOrientation (EB := EB) h2 h1 o z.val) := by
    funext z
    exact unitTangentCoverMap_chart h2 h1 o c z
  have hh : Continuous (fun z : U => (t (unitTangentCoverMap (EB := EB) h2 h1 o z.val)).2) := by
    rw [hfun]
    exact (unitChartOrientation_locallyConstant h2 h1 o c).continuous
  have hhc : ContinuousAt
      ((fun z : {z : TotalSpace F V // ‖z.2‖ = 1} =>
        (t (unitTangentCoverMap (EB := EB) h2 h1 o z)).2) ∘ Subtype.val) (⟨x, hx⟩ : U) :=
    hh.continuousAt
  exact (U.isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff).mp hhc

variable [baseCompact : CompactSpace B] [baseT2 : T2Space B] [continuousMetric :
    IsContinuousRiemannianBundle F V]

def unitTangentCoverHomeomorph (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3) :
    {z : TotalSpace F V // ‖z.2‖ = 1} ≃ₜ tangentOrientationCover (M := B) h2 := by
  let sphereCompact : CompactSpace {z : TotalSpace F V // ‖z.2‖ = 1} :=
    isCompact_iff_compactSpace.mp (isCompact_sphereBundle (F := F) (V := V) 1)
  let orientationT2 : T2Space (tangentOrientationCover (M := B) h2) :=
    tangentOrientationCover_t2Space h2
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective
    (unitTangentCoverMap (EB := EB) h2 h1 o) (unitTangentCoverMap_bijective h2 h1 o))
    (unitTangentCoverMap_continuous h2 h1 o)

theorem unitTangentCoverHomeomorph_proj (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3)
    (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    (unitTangentCoverHomeomorph h2 h1 o z).proj = z.val.proj := rfl

theorem unitTangentCoverHomeomorph_neg (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3)
    (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    unitTangentCoverHomeomorph h2 h1 o ⟨⟨z.val.proj, -z.val.2⟩,
      by simpa using z.property⟩ = tangentOrientationDeck h2
        (unitTangentCoverHomeomorph h2 h1 o z) := by
  exact congrArg (fun q : Orientation ℝ EB (Fin 2) =>
    (⟨z.val.proj, q⟩ : tangentOrientationCover (M := B) h2))
    (unitTangentOrientation_neg h2 h1 o z)

theorem sphere_not_preconnected_of_total_and_base_orientation [baseConnected : ConnectedSpace B]
    (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3)
    (b : ManifoldOrientation 𝓘(ℝ, EB) B 2) :
    ¬ IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1} := by
  intro hs
  let unitPreconnected : PreconnectedSpace {z : TotalSpace F V // ‖z.2‖ = 1} :=
    isPreconnected_iff_preconnectedSpace.mp hs
  let x : B := Classical.choice inferInstance
  obtain ⟨u, hu⟩ := RankOneQuotient.exists_norm_eq_one_of_finrank_eq_one
    ((finrank_fiber_eq (F := F) (V := V) x).trans h1)
  let unitNonempty : Nonempty {z : TotalSpace F V // ‖z.2‖ = 1} := ⟨⟨⟨x, u⟩, hu⟩⟩
  let unitConnected : ConnectedSpace {z : TotalSpace F V // ‖z.2‖ = 1} :=
    { toPreconnectedSpace := unitPreconnected, toNonempty := unitNonempty }
  have hcon := (unitTangentCoverHomeomorph h2 h1 o).surjective.connectedSpace
    (unitTangentCoverHomeomorph h2 h1 o).continuous
  exact tangentOrientationCover_not_connected_of_compatibleOrientation h2 b.orientation
    (isCompatibleOrientation_of_manifoldOrientation (o := b)) hcon

end DifferentialGeometry.Topology.VectorBundle
