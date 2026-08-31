import DifferentialGeometry.Geometry.Exponential.DiagInvReadout
import DifferentialGeometry.Geometry.Exponential.NormalBallHome
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalPhase
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.MetricExtension
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.DiagonalInverseAt
import Mathlib.Topology.OpenPartialHomeomorph.Composition
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

noncomputable def normalTanHome
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    OpenPartialHomeomorph (E × E) (TangentBundle I Y.M) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact (legacyBallChart (I := I) Y x).tangentHome

noncomputable def normalPairHome
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    OpenPartialHomeomorph (E × E) (Y.M × Y.M) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact (legacyBallChart (I := I) Y x).pairHome

omit [NeZero (Module.finrank ℝ E)] in
theorem normalTanHome_apply
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : E × E) (hz : z.1 ∈ normalBall (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    normalTanHome (I := I) Y x z = normalTangent (I := I) Y x z := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  change (legacyBallChart (I := I) Y x).tangentHome z =
    (legacyBallChart (I := I) Y x).tangent z
  apply (legacyBallChart (I := I) Y x).tangentHome_apply
  with_unfolding_all
    change z.1 ∈ Metric.ball 0 (expMapC2Radius (I := I) Y.metric x) at hz
  exact hz

omit [NeZero (Module.finrank ℝ E)] in
theorem normalPairHome_apply
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : E × E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    normalPairHome (I := I) Y x z = normalPair (I := I) Y x z := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact (legacyBallChart (I := I) Y x).pairHome_apply z

omit [NeZero (Module.finrank ℝ E)] in
theorem normalTanHome_source
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalTanHome (I := I) Y x).source =
      Prod.fst ⁻¹' (normalBall (I := I) Y x : Set E) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [normalTanHome, (legacyBallChart (I := I) Y x).tangentHome_source]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem normalPair_source
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalPairHome (I := I) Y x).source =
      (normalBall (I := I) Y x : Set E) ×ˢ
        (normalBall (I := I) Y x : Set E) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [normalPairHome, (legacyBallChart (I := I) Y x).pairHome_source]
  rfl

noncomputable def normalDiagHome
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (e : OpenPartialHomeomorph (E × E) (E × E)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    OpenPartialHomeomorph (TangentBundle I Y.M) (Y.M × Y.M) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact (legacyBallChart (I := I) Y x).tangentHome.symm.trans
    (e.trans (legacyBallChart (I := I) Y x).pairHome)

noncomputable def chartTanHome
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (c : NormalChartAt (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    OpenPartialHomeomorph (E × E) (TangentBundle I Y.M) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact c.tangentHome

noncomputable def chartPairHome
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (c : NormalChartAt (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    OpenPartialHomeomorph (E × E) (Y.M × Y.M) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact c.pairHome

noncomputable def chartDiagHome
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (c : NormalChartAt (I := I) Y x)
    (e : OpenPartialHomeomorph (E × E) (E × E)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    OpenPartialHomeomorph (TangentBundle I Y.M) (Y.M × Y.M) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact (chartTanHome (I := I) Y x c).symm.trans
    (e.trans (chartPairHome (I := I) Y x c))

private theorem pair_mem_target
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : OpenPartialHomeomorph X Y) (e : OpenPartialHomeomorph X X)
    (P : OpenPartialHomeomorph X Z) {w : X}
    (hwP : w ∈ P.source) (hwe : w ∈ e.target) (hwA : e.symm w ∈ A.source) :
    P w ∈ (A.symm.trans (e.trans P)).target := by
  rw [OpenPartialHomeomorph.trans_target]
  constructor
  · rw [OpenPartialHomeomorph.trans_target]
    refine ⟨P.map_source hwP, ?_⟩
    change P.symm (P w) ∈ e.target
    rw [P.left_inv hwP]
    exact hwe
  · change e.symm (P.symm (P w)) ∈ A.source
    rw [P.left_inv hwP]
    exact hwA

omit [NeZero (Module.finrank ℝ E)] in
theorem normalTanHome_inf
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn 𝓘(Real, E × E) I.tangent ∞
      (normalTanHome (I := I) Y x) (normalTanHome (I := I) Y x).source := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  let Φ := normalExpPD (I := I) Y x
  let m : OpenPartialHomeomorph (E × E) (TangentBundle 𝓘(Real, E) E) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm.toOpenPartialHomeomorph
  let t := PartialDiffeomorph.tangentHome Φ (by simp)
  have hm : ContMDiff (𝓘(Real, E).prod 𝓘(Real, E)) 𝓘(Real, E).tangent ∞
      (m : E × E → TangentBundle 𝓘(Real, E) E) := by
    have hm0 := contMDiff_tangentBundleModelSpaceHomeomorph_symm
      (I := 𝓘(Real, E)) (n := (∞ : WithTop ℕ∞))
    unfold ModelProd at hm0
    rw [← chartedSpaceSelf_prod] at hm0
    convert! hm0 using 1
  have ht : ContMDiffOn 𝓘(Real, E).tangent I.tangent ∞
      (t : TangentBundle 𝓘(Real, E) E → TangentBundle I Y.M) t.source := by
    convert! Φ.contMDiffOn_toFun.contMDiffOn_tangentMapWithin
      (m := (∞ : WithTop ℕ∞)) (by simp) Φ.open_source.uniqueMDiffOn using 1
  have hmOn : ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, E))
      𝓘(Real, E).tangent ∞ (m : E × E → TangentBundle 𝓘(Real, E) E) m.source :=
    hm.contMDiffOn
  change ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, E)) I.tangent ∞
    ((t : TangentBundle 𝓘(Real, E) E → TangentBundle I Y.M) ∘
      (m : E × E → TangentBundle 𝓘(Real, E) E))
    (m.source ∩ (m : E × E → TangentBundle 𝓘(Real, E) E) ⁻¹' t.source)
  exact ht.comp' hmOn

omit [NeZero (Module.finrank ℝ E)] in
theorem normalTan_inv_inf
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn I.tangent 𝓘(Real, E × E) ∞
      (normalTanHome (I := I) Y x).symm
      (normalTanHome (I := I) Y x).target := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  let Φ := normalExpPD (I := I) Y x
  let m : OpenPartialHomeomorph (E × E) (TangentBundle 𝓘(Real, E) E) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm.toOpenPartialHomeomorph
  let t := PartialDiffeomorph.tangentHome Φ (by simp)
  have hm : ContMDiff 𝓘(Real, E).tangent
      (𝓘(Real, E).prod 𝓘(Real, E)) ∞
      (m.symm : TangentBundle 𝓘(Real, E) E → E × E) := by
    have hm0 := contMDiff_tangentBundleModelSpaceHomeomorph
      (I := 𝓘(Real, E)) (n := (∞ : WithTop ℕ∞))
    unfold ModelProd at hm0
    rw [← chartedSpaceSelf_prod] at hm0
    convert! hm0 using 1
  have ht : ContMDiffOn I.tangent 𝓘(Real, E).tangent ∞
      (t.symm : TangentBundle I Y.M → TangentBundle 𝓘(Real, E) E) t.target := by
    convert! Φ.contMDiffOn_invFun.contMDiffOn_tangentMapWithin
      (m := (∞ : WithTop ℕ∞)) (by simp) Φ.open_target.uniqueMDiffOn using 1
  have hmOn : ContMDiffOn 𝓘(Real, E).tangent
      (𝓘(Real, E).prod 𝓘(Real, E)) ∞
      (m.symm : TangentBundle 𝓘(Real, E) E → E × E) m.target :=
    hm.contMDiffOn
  change ContMDiffOn I.tangent (𝓘(Real, E).prod 𝓘(Real, E)) ∞
    ((m.symm : TangentBundle 𝓘(Real, E) E → E × E) ∘
      (t.symm : TangentBundle I Y.M → TangentBundle 𝓘(Real, E) E))
    (t.target ∩
      (t.symm : TangentBundle I Y.M → TangentBundle 𝓘(Real, E) E) ⁻¹' m.target)
  exact hmOn.comp' ht

omit [NeZero (Module.finrank ℝ E)] in
theorem normalPairHome_inf
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn 𝓘(Real, E × E) (I.prod I) ∞
      (normalPairHome (I := I) Y x) (normalPairHome (I := I) Y x).source := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  have h := (normalExpPD (I := I) Y x).contMDiffOn_toFun.prodMap
    (normalExpPD (I := I) Y x).contMDiffOn_toFun
  convert! h using 1

omit [NeZero (Module.finrank ℝ E)] in
theorem normalPair_inv_inf
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn (I.prod I) 𝓘(Real, E × E) ∞
      (normalPairHome (I := I) Y x).symm
      (normalPairHome (I := I) Y x).target := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  have h := (normalExpPD (I := I) Y x).contMDiffOn_invFun.prodMap
    (normalExpPD (I := I) Y x).contMDiffOn_invFun
  convert! h using 1

namespace NormalCoordMetricBoundInput

theorem chart_mem_norm_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (k : Nat) (c y : (X.obj k).M)
    (hdist :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      letI : RiemannianBundle
          (fun z : (X.obj k).M ↦ TangentSpace I z) :=
        (X.obj k).riemBundle (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun z : (X.obj k).M ↦ TangentSpace I z) :=
        (X.obj k).riemBundle_cont (I := I)
      letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
      riemannianEDist I c y ≠ ⊤ ∧
        (riemannianEDist I c y).toReal <
          expRadiusGp (I := I) (X.obj k).metric c) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : RiemannianBundle
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    y ∈ (NormalCoordinates.framedChartAt (I := I) (X.obj k).metric c).source ∧
      ‖NormalCoordinates.framedChartAt (I := I) (X.obj k).metric c y‖ ≤
        2 * (riemannianEDist I c y).toReal := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : RiemannianBundle (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  obtain ⟨v, hvTarget, _hvDomain, hvLength, hyExp⟩ :=
    metricBall_subset_normalBall (I := I) (X.obj k).metric c
      (normal_enorm (I := I) (X.obj k)) hdist.1 hdist.2
  have hyRawSource :
      y ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c).source :=
    memNChartSrcOfDist (I := I) (X.obj k).metric c
      (normal_enorm (I := I) (X.obj k)) hdist.1 hdist.2
  have hySource :
      y ∈ (NormalCoordinates.framedChartAt (I := I) (X.obj k).metric c).source := by
    change y ∈ (NormalCoordinates.expMapDiffeo (I := I) (X.obj k).metric c).target at hyRawSource
    change y ∈ (NormalCoordinates.framedExpDiffeo (I := I) (X.obj k).metric c).target
    rw [NormalCoordinates.framedExp_target]
    exact hyRawSource
  have hchartRaw :
      NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c y = v := by
    have hsymm :
        (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c).symm v = y := by
      rw [NormalCoordinates.normalChartAt_symm_apply (I := I) (X.obj k).metric c hvTarget]
      exact hyExp.symm
    rw [← hsymm]
    exact (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c).right_inv hvTarget
  let z : E := (NormalCoordinates.normalFrame (I := I) (X.obj k).metric c).symm
    (show TangentSpace I c from v)
  have hzFrame : NormalCoordinates.normalFrame (I := I) (X.obj k).metric c z =
      (show TangentSpace I c from v) := by
    dsimp only [z]
    exact (NormalCoordinates.normalFrame (I := I) (X.obj k).metric c).apply_symm_apply _
  have hchart :
      NormalCoordinates.framedChartAt (I := I) (X.obj k).metric c y = z := by
    rw [NormalCoordinates.framedChart_apply, hchartRaw]
    with_unfolding_all rfl
  have hnorm : ‖z‖ = Real.sqrt ((X.obj k).metric.inner c
      (show TangentSpace I c from v) (show TangentSpace I c from v)) := by
    calc
      ‖z‖ = Real.sqrt ((X.obj k).metric.inner c
          (NormalCoordinates.normalFrame (I := I) (X.obj k).metric c z)
          (NormalCoordinates.normalFrame (I := I) (X.obj k).metric c z)) :=
        (NormalCoordinates.normalFrame_sqrt (I := I) (X.obj k).metric c z).symm
      _ = Real.sqrt ((X.obj k).metric.inner c
          (show TangentSpace I c from v) (show TangentSpace I c from v)) := by
        rw [hzFrame]
  refine ⟨hySource, ?_⟩
  rw [hchart, hnorm, hvLength]
  have hdistNonneg : 0 ≤ (riemannianEDist I c y).toReal := ENNReal.toReal_nonneg
  nlinarith

theorem raw_chart_mem_norm_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (c y : (X.obj k).M)
    (hdist :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      letI : RiemannianBundle
          (fun z : (X.obj k).M ↦ TangentSpace I z) :=
        (X.obj k).riemBundle (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun z : (X.obj k).M ↦ TangentSpace I z) :=
        (X.obj k).riemBundle_cont (I := I)
      letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
      riemannianEDist I c y ≠ ⊤ ∧
        (riemannianEDist I c y).toReal <
          expRadiusGp (I := I) (X.obj k).metric c) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : RiemannianBundle
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    y ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c).source ∧
      ‖NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c y‖ ≤
        2 * (riemannianEDist I c y).toReal := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : RiemannianBundle (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  obtain ⟨v, hvTarget, _hvDomain, hvLength, hyExp⟩ :=
    metricBall_subset_normalBall (I := I) (X.obj k).metric c
      (normal_enorm (I := I) (X.obj k)) hdist.1 hdist.2
  have hySource :
      y ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c).source :=
    memNChartSrcOfDist (I := I) (X.obj k).metric c
      (normal_enorm (I := I) (X.obj k)) hdist.1 hdist.2
  have hchart :
      NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c y = v := by
    have hsymm :
        (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c).symm v = y := by
      rw [NormalCoordinates.normalChartAt_symm_apply
        (I := I) (X.obj k).metric c hvTarget]
      exact hyExp.symm
    rw [← hsymm]
    exact (NormalCoordinates.normalChartAt
      (I := I) (X.obj k).metric c).right_inv hvTarget
  have hzero : (0 : E) ∈ Metric.ball 0 (h.radius k c) := by
    rw [Metric.mem_ball, dist_self]
    exact h.radius_pos k c
  have hcoercive := (h.metric_equiv k c 0 hzero v).1
  have hmetricZero :
      normalCoordMetric (I := I) (X.obj k) c 0 v v =
        (X.obj k).metric.inner c v v := by
    rw [normalCoordMetric_apply (I := I),
      NormalCoordinates.expMapDiffeo_zero (I := I)]
    exact NormalCoordinates.normalChartAt_metric_pullback_at_origin
      (I := I) (X.obj k).metric c v v
  rw [hmetricZero] at hcoercive
  have hinnerNonneg : 0 ≤ (X.obj k).metric.inner c v v := by
    exact (mul_nonneg (by norm_num) (sq_nonneg ‖v‖)).trans hcoercive
  have hinnerEq :
      (X.obj k).metric.inner c v v = (riemannianEDist I c y).toReal ^ 2 := by
    calc
      (X.obj k).metric.inner c v v =
          Real.sqrt ((X.obj k).metric.inner c v v) ^ 2 :=
        (Real.sq_sqrt hinnerNonneg).symm
      _ = (riemannianEDist I c y).toReal ^ 2 :=
        congrArg (fun t : Real => t ^ 2) hvLength
  rw [hinnerEq] at hcoercive
  rw [hchart]
  refine ⟨hySource, ?_⟩
  have hdistNonneg : 0 ≤ (riemannianEDist I c y).toReal := ENNReal.toReal_nonneg
  by_contra hle
  have hlt : 2 * (riemannianEDist I c y).toReal < ‖v‖ := lt_of_not_ge hle
  have hsq : (2 * (riemannianEDist I c y).toReal) ^ 2 < ‖v‖ ^ 2 :=
    (sq_lt_sq₀ (mul_nonneg (by norm_num) hdistNonneg) (norm_nonneg v)).2 hlt
  nlinarith

end NormalCoordMetricBoundInput

namespace IsNormalDiag

theorem eqOnSource
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {δ δ' : Real}
    {e e' : OpenPartialHomeomorph (E × E) (E × E)}
    (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c))
    (hf : NormalDiagFence (I := I) Y x q e (c := c))
    (h' : IsNormalDiag (I := I) Y hcomplete hconn x q δ' e' (c := c))
    (hf' : NormalDiagFence (I := I) Y x q e' (c := c)) :
    e ≈ e' := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) (c := c) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z (c := c)) at h
  change e'.source = Metric.ball (0 : E × E) q ∧
    e' 0 = 0 ∧
    ContDiffOn Real ∞ (e' : E × E → E × E) e'.source ∧
    Metric.closedBall (0 : E × E) δ' ⊆ e'.target ∧
    ContDiffOn Real ∞ e'.symm e'.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e' z) (c := c) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z (c := c)) at h'
  change ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ Metric.ball (0 : E) c.radius ∧
    (e z).1 ∈ Metric.ball (0 : E) c.radius ∧
    (e z).2 ∈ Metric.ball (0 : E) c.radius at hf
  change ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ Metric.ball (0 : E) c.radius ∧
    (e' z).1 ∈ Metric.ball (0 : E) c.radius ∧
    (e' z).2 ∈ Metric.ball (0 : E) c.radius at hf'
  rcases h with ⟨hsource, _, _, _, _, hdiag⟩
  rcases h' with ⟨hsource', _, _, _, _, hdiag'⟩
  refine ⟨hsource.trans hsource'.symm, ?_⟩
  intro z hz
  have hzBall : z ∈ Metric.ball (0 : E × E) q := by
    rwa [← hsource]
  have hzClosed : z ∈ Metric.closedBall (0 : E × E) q :=
    Metric.ball_subset_closedBall hzBall
  have hzFence := hf z hzClosed
  have hzFence' := hf' z hzClosed
  apply c.pairHome.injOn
  · rw [c.pairHome_source]
    exact ⟨hzFence.2.1, hzFence.2.2⟩
  · rw [c.pairHome_source]
    exact ⟨hzFence'.2.1, hzFence'.2.2⟩
  · rw [c.pairHome_apply, c.pairHome_apply]
    exact (hdiag z hzClosed).trans (hdiag' z hzClosed).symm

noncomputable def toBranch
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    DiagInvBranch (I := I) Y.metric (normal_enorm (I := I) Y) x := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have hdata := h
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) (c := c) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z (c := c)) at h
  rcases h with ⟨hsource, hzero, _heInf, _htarget, hinvInf, hdiag⟩
  let A := chartTanHome (I := I) Y x c
  let P := chartPairHome (I := I) Y x c
  let D := chartDiagHome (I := I) Y x c e
  let u0 : TangentBundle I Y.M := ⟨x, (0 : TangentSpace I x)⟩
  have hzNormal : (0 : E) ∈ Metric.ball 0 c.radius :=
    Metric.mem_ball_self c.radius_pos
  have hA0src : (0 : E × E) ∈ A.source := by
    change (0 : E × E) ∈ c.tangentHome.source
    rw [c.tangentHome_source]
    exact hzNormal
  have hA0 : A 0 = u0 := by
    change c.tangentHome 0 = u0
    rw [c.tangentHome_apply 0 hzNormal]
    convert! c.tangent_zero using 1
  have hP0src : (0 : E × E) ∈ P.source := by
    change (0 : E × E) ∈ c.pairHome.source
    rw [c.pairHome_source]
    exact ⟨hzNormal, hzNormal⟩
  refine
    { hom := D
      zero_mem := ?_
      hom_eq := ?_
      inv_inf := ?_ }
  · change u0 ∈ D.source
    change u0 ∈ (A.symm.trans (e.trans P)).source
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · change u0 ∈ A.target
      rw [← hA0]
      exact A.map_source hA0src
    · change A.symm u0 ∈ (e.trans P).source
      have hAinv0 : A.symm u0 = 0 := by
        rw [← hA0]
        exact A.left_inv hA0src
      rw [hAinv0, OpenPartialHomeomorph.trans_source]
      constructor
      · rw [hsource]
        exact Metric.mem_ball_self (by exact_mod_cast hq)
      · change e 0 ∈ P.source
        rw [hzero]
        exact hP0src
  · intro u hu
    change u ∈ (A.symm.trans (e.trans P)).source at hu
    rw [OpenPartialHomeomorph.trans_source] at hu
    rcases hu with ⟨huA, huRest⟩
    change A.symm u ∈ (e.trans P).source at huRest
    rw [OpenPartialHomeomorph.trans_source] at huRest
    rcases huRest with ⟨hze, _hzP⟩
    let z : E × E := A.symm u
    have hzA : z ∈ A.source := A.map_target huA
    have hzNormal' : z.1 ∈ Metric.ball 0 c.radius := by
      have hzA' : z ∈ c.tangentHome.source := hzA
      rw [c.tangentHome_source] at hzA'
      exact hzA'
    have hztan : normalTangent (I := I) Y x z (c := c) = u := by
      calc
        normalTangent (I := I) Y x z (c := c) = A z :=
          (c.tangentHome_apply z hzNormal').symm
        _ = u := A.right_inv huA
    have hzBall : z ∈ Metric.ball (0 : E × E) q := by
      rw [← hsource]
      exact hze
    have hzClosed : z ∈ Metric.closedBall (0 : E × E) q :=
      Metric.ball_subset_closedBall hzBall
    calc
      D u = P (e z) := rfl
      _ = normalPair (I := I) Y x (e z) (c := c) := c.pairHome_apply (e z)
      _ = diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z (c := c)) := hdiag z hzClosed
      _ = diagExp (I := I) Y.metric (normal_enorm (I := I) Y) u :=
        congrArg (diagExp (I := I) Y.metric (normal_enorm (I := I) Y)) hztan
  · let B := e.trans P
    have hPInv : ContMDiffOn (I.prod I) 𝓘(Real, E × E) ∞
        P.symm P.target := c.pairHome_inv_inf
    have heInv : ContMDiffOn 𝓘(Real, E × E) 𝓘(Real, E × E) ∞
        e.symm e.target := hinvInf.contMDiffOn
    have hBInv : ContMDiffOn (I.prod I) 𝓘(Real, E × E) ∞
        B.symm B.target := by
      change ContMDiffOn (I.prod I) 𝓘(Real, E × E) ∞
        ((e.symm : E × E → E × E) ∘ (P.symm : Y.M × Y.M → E × E))
        (P.target ∩ (P.symm : Y.M × Y.M → E × E) ⁻¹' e.target)
      exact heInv.comp' hPInv
    have hAInf : ContMDiffOn 𝓘(Real, E × E) I.tangent ∞ A A.source :=
      c.tangentHome_inf
    change ContMDiffOn (I.prod I) I.tangent ∞
      ((A : E × E → TangentBundle I Y.M) ∘ (B.symm : Y.M × Y.M → E × E))
      (B.target ∩ (B.symm : Y.M × Y.M → E × E) ⁻¹' A.source)
    exact hAInf.comp' hBInv

@[simp] theorem toBranch_hom
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    (toBranch (I := I) Y hcomplete hconn x hq h).hom =
      chartDiagHome (I := I) Y x c e := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) (c := c) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z (c := c)) at h
  rcases h with ⟨_, _, _, _, _, _⟩
  rfl

theorem full_transport
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c))
    (hf : NormalDiagFence (I := I) Y x q e (c := c)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    c.tangentHome '' Metric.ball (0 : E × E) q =
        (toBranch (I := I) Y hcomplete hconn x hq h).hom.source ∧
      c.pairHome '' e.target =
        (toBranch (I := I) Y hcomplete hconn x hq h).dom ∧
      ∀ w ∈ e.target,
        (toBranch (I := I) Y hcomplete hconn x hq h).inv
            (normalPair (I := I) Y x w (c := c)) =
          normalTangent (I := I) Y x (e.symm w) (c := c) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let A := chartTanHome (I := I) Y x c
  let P := chartPairHome (I := I) Y x c
  have hdata := h
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) (c := c) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z (c := c)) at hdata
  rcases hdata with ⟨hsource, _hzero, _heInf, _htarget, _hinvInf, _hdiag⟩
  have hfence := hf
  change ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ Metric.ball (0 : E) c.radius ∧
    (e z).1 ∈ Metric.ball (0 : E) c.radius ∧
    (e z).2 ∈ Metric.ball (0 : E) c.radius at hfence
  have targetData : ∀ {w : E × E}, w ∈ e.target →
      w ∈ P.source ∧ e.symm w ∈ A.source := by
    intro w hw
    have hzSource : e.symm w ∈ e.source := e.map_target hw
    have hzBall : e.symm w ∈ Metric.ball (0 : E × E) q := by
      rw [← hsource]
      exact hzSource
    have hzFence := hfence (e.symm w) (Metric.ball_subset_closedBall hzBall)
    have hzA : e.symm w ∈ A.source := by
      change e.symm w ∈ c.tangentHome.source
      rw [c.tangentHome_source]
      exact hzFence.1
    have hezP : e (e.symm w) ∈ P.source := by
      change e (e.symm w) ∈ c.pairHome.source
      rw [c.pairHome_source]
      exact ⟨hzFence.2.1, hzFence.2.2⟩
    have hwP : w ∈ P.source := by
      rw [e.right_inv hw] at hezP
      exact hezP
    exact ⟨hwP, hzA⟩
  have hsourceTransport : A '' Metric.ball (0 : E × E) q =
      (toBranch (I := I) Y hcomplete hconn x hq h).hom.source := by
    rw [toBranch_hom]
    ext u
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzFence := hfence z (Metric.ball_subset_closedBall hz)
      have hzA : z ∈ A.source := by
        change z ∈ c.tangentHome.source
        rw [c.tangentHome_source]
        exact hzFence.1
      have hezP : e z ∈ P.source := by
        change e z ∈ c.pairHome.source
        rw [c.pairHome_source]
        exact ⟨hzFence.2.1, hzFence.2.2⟩
      change A z ∈ (A.symm.trans (e.trans P)).source
      rw [OpenPartialHomeomorph.trans_source]
      refine ⟨A.map_source hzA, ?_⟩
      change A.symm (A z) ∈ (e.trans P).source
      rw [A.left_inv hzA, OpenPartialHomeomorph.trans_source]
      exact ⟨by rwa [hsource], hezP⟩
    · intro hu
      change u ∈ (A.symm.trans (e.trans P)).source at hu
      rw [OpenPartialHomeomorph.trans_source] at hu
      rcases hu with ⟨huA, huRest⟩
      change A.symm u ∈ (e.trans P).source at huRest
      rw [OpenPartialHomeomorph.trans_source] at huRest
      refine ⟨A.symm u, ?_, A.right_inv huA⟩
      rw [← hsource]
      exact huRest.1
  have htargetTransport : P '' e.target =
      (toBranch (I := I) Y hcomplete hconn x hq h).dom := by
    unfold DiagInvBranch.dom
    rw [toBranch_hom]
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hwP, hzA⟩ := targetData hw
      change P w ∈ (A.symm.trans (e.trans P)).target
      rw [OpenPartialHomeomorph.trans_target]
      constructor
      · rw [OpenPartialHomeomorph.trans_target]
        refine ⟨P.map_source hwP, ?_⟩
        change P.symm (P w) ∈ e.target
        rwa [P.left_inv hwP]
      · change (e.trans P).symm (P w) ∈ A.source
        change e.symm (P.symm (P w)) ∈ A.source
        rwa [P.left_inv hwP]
    · intro hy
      change y ∈ (A.symm.trans (e.trans P)).target at hy
      rw [OpenPartialHomeomorph.trans_target] at hy
      have hyRest := hy.1
      change y ∈ (e.trans P).target at hyRest
      rw [OpenPartialHomeomorph.trans_target] at hyRest
      exact ⟨P.symm y, hyRest.2, P.right_inv hyRest.1⟩
  refine ⟨hsourceTransport, htargetTransport, ?_⟩
  intro w hw
  obtain ⟨hwP, hzA⟩ := targetData hw
  have hzNormal : (e.symm w).1 ∈ Metric.ball (0 : E) c.radius := by
    change e.symm w ∈ c.tangentHome.source at hzA
    rw [c.tangentHome_source] at hzA
    exact hzA
  unfold DiagInvBranch.inv
  rw [toBranch_hom]
  change (chartDiagHome (I := I) Y x c e).symm
      (c.pair w) = c.tangent (e.symm w)
  rw [← c.pairHome_apply w]
  change A (e.symm (P.symm (P w))) =
    c.tangent (e.symm w)
  rw [P.left_inv hwP]
  exact c.tangentHome_apply (e.symm w) hzNormal

theorem chart_readout
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c))
    (hf : NormalDiagFence (I := I) Y x q e (c := c))
    {w : E × E} (hw : w ∈ e.target) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    (toBranch (I := I) Y hcomplete hconn x hq h).chartReadout c
        (normalPair (I := I) Y x w (c := c)) =
      (e.symm w).2 := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
    (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have hdata := h
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) (c := c) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z (c := c)) at hdata
  have hfence := hf
  change ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ Metric.ball (0 : E) c.radius ∧
    (e z).1 ∈ Metric.ball (0 : E) c.radius ∧
    (e z).2 ∈ Metric.ball (0 : E) c.radius at hfence
  have hzBall : e.symm w ∈ Metric.ball (0 : E × E) q := by
    rw [← hdata.1]
    exact e.map_target hw
  have hzNormal : (e.symm w).1 ∈ Metric.ball (0 : E) c.radius :=
    (hfence (e.symm w) (Metric.ball_subset_closedBall hzBall)).1
  have hzSource : e.symm w ∈ c.tangentHome.source := by
    rw [c.tangentHome_source]
    exact hzNormal
  unfold DiagInvBranch.chartReadout
  rw [(full_transport (I := I) Y hcomplete hconn x hq h hf).2.2 w hw]
  change (c.tangentHome.symm (c.tangent (e.symm w))).2 = (e.symm w).2
  rw [← c.tangentHome_apply (e.symm w) hzNormal]
  rw [c.tangentHome.left_inv hzSource]

theorem target_mem_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c))
    (hf : NormalDiagFence (I := I) Y x q e (c := c)) {w : E × E}
    (hw : w ∈ e.target) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    w.1 ∈ Metric.ball (0 : E) c.radius ∧
      w.2 ∈ Metric.ball (0 : E) c.radius := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have hdata := h
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) (c := c) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z (c := c)) at hdata
  have hfence := hf
  change ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ Metric.ball (0 : E) c.radius ∧
    (e z).1 ∈ Metric.ball (0 : E) c.radius ∧
    (e z).2 ∈ Metric.ball (0 : E) c.radius at hfence
  have hzBall : e.symm w ∈ Metric.ball (0 : E × E) q := by
    rw [← hdata.1]
    exact e.map_target hw
  have hzFence :=
    (hfence (e.symm w) (Metric.ball_subset_closedBall hzBall)).2
  simpa only [e.right_inv hw] using hzFence

theorem symm_fst_eq
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c))
    (hf : NormalDiagFence (I := I) Y x q e (c := c)) {w : E × E}
    (hw : w ∈ e.target) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    (e.symm w).1 = w.1 := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have hdata := h
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) (c := c) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z (c := c)) at hdata
  rcases hdata with ⟨hsource, _hzero, _heInf, _htarget, _hinvInf, hdiag⟩
  have hfence := hf
  change ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ Metric.ball (0 : E) c.radius ∧
    (e z).1 ∈ Metric.ball (0 : E) c.radius ∧
    (e z).2 ∈ Metric.ball (0 : E) c.radius at hfence
  have hzSource : e.symm w ∈ e.source := e.map_target hw
  have hzBall : e.symm w ∈ Metric.ball (0 : E × E) q := by
    rw [← hsource]
    exact hzSource
  have hzFence := hfence (e.symm w) (Metric.ball_subset_closedBall hzBall)
  have hzNormal : (e.symm w).1 ∈ Metric.ball (0 : E) c.radius := hzFence.1
  have hwNormal : w.1 ∈ Metric.ball (0 : E) c.radius := by
    rw [← e.right_inv hw]
    exact hzFence.2.1
  have hfst := congrArg Prod.fst
    (hdiag (e.symm w) (Metric.ball_subset_closedBall hzBall))
  have hmap : c.hom w.1 = c.hom (e.symm w).1 := by
    simpa only [normalPair, normalTangent,
      NormalCoordinates.NormalBallChart.pair,
      NormalCoordinates.NormalBallChart.tangent, diagExp_fst,
      e.right_inv hw] using hfst
  apply c.hom.toPartialEquiv.injOn
  · exact c.ball_subset hzNormal
  · exact c.ball_subset hwNormal
  · exact hmap.symm

theorem inv_pair_normal
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c))
    (hf : NormalDiagFence (I := I) Y x q e (c := c)) {w : E × E}
    (hw : w ∈ e.target) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    (toBranch (I := I) Y hcomplete hconn x hq h).inv
        (normalPair (I := I) Y x w (c := c)) =
      normalTangent (I := I) Y x (w.1, (e.symm w).2) (c := c) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
    (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  rw [(full_transport (I := I) Y hcomplete hconn x hq h hf).2.2 w hw]
  congr 1
  exact Prod.ext (symm_fst_eq (I := I) Y hcomplete hconn x h hf hw) rfl

theorem target_of_pair_mem
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    ∀ {w : E × E}, w ∈ c.pairHome.source →
      normalPair (I := I) Y x w (c := c) ∈
        (toBranch (I := I) Y hcomplete hconn x hq h).dom →
      w ∈ e.target := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  intro w hw hdom
  let A := chartTanHome (I := I) Y x c
  let P := chartPairHome (I := I) Y x c
  unfold DiagInvBranch.dom at hdom
  rw [toBranch_hom (I := I) Y hcomplete hconn x hq h] at hdom
  change P w ∈ (A.symm.trans (e.trans P)).target at hdom
  rw [OpenPartialHomeomorph.trans_target] at hdom
  have hrest := hdom.1
  rw [OpenPartialHomeomorph.trans_target] at hrest
  have htarget : P.symm (P w) ∈ e.target := hrest.2
  rwa [P.left_inv hw] at htarget

theorem target_of_inv_dom
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c))
    {y p : Y.M} :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
      Y.riemBundle (I := I)
    letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun z : Y.M ↦ TangentSpace I z) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    y ∈ c.restrictBall.target →
      p ∈ c.restrictBall.target →
      (y, p) ∈ (toBranch (I := I) Y hcomplete hconn x hq h).dom →
      (c.inv y, c.inv p) ∈ e.target := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
    Y.riemBundle (I := I)
  let : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
    (fun z : Y.M ↦ TangentSpace I z) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  intro hy hp hdom
  have hySource : c.inv y ∈ Metric.ball (0 : E) c.radius := by
    change c.restrictBall.symm y ∈ c.restrictBall.source
    exact c.restrictBall.map_target hy
  have hpSource : c.inv p ∈ Metric.ball (0 : E) c.radius := by
    change c.restrictBall.symm p ∈ c.restrictBall.source
    exact c.restrictBall.map_target hp
  have hcoordSource : (c.inv y, c.inv p) ∈ c.pairHome.source := by
    rw [c.pairHome_source]
    exact ⟨hySource, hpSource⟩
  have hpairEq :
      normalPair (I := I) Y x (c.inv y, c.inv p) (c := c) = (y, p) := by
    change
      (c.restrictBall (c.restrictBall.symm y),
        c.restrictBall (c.restrictBall.symm p)) = (y, p)
    exact Prod.ext (c.restrictBall.right_inv hy) (c.restrictBall.right_inv hp)
  apply target_of_pair_mem (I := I) Y hcomplete hconn x hq h hcoordSource
  rwa [hpairEq]

theorem target_of_chart_dom
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) Y x q e) {y p : Y.M} :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
      Y.riemBundle (I := I)
    letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun z : Y.M ↦ TangentSpace I z) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    y ∈ (NormalCoordinates.normalChartAt (I := I) Y.metric x).source →
      p ∈ (NormalCoordinates.normalChartAt (I := I) Y.metric x).source →
      (y, p) ∈ (toBranch (I := I) Y hcomplete hconn x hq h).dom →
      (NormalCoordinates.normalChartAt (I := I) Y.metric x y,
        NormalCoordinates.normalChartAt (I := I) Y.metric x p) ∈ e.target := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
    Y.riemBundle (I := I)
  let : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
    (fun z : Y.M ↦ TangentSpace I z) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  intro hy hp hdom
  let P := normalPairHome (I := I) Y x
  have htransport := full_transport (I := I) Y hcomplete hconn x hq h hf
  have himage : (y, p) ∈ P '' e.target := by
    change (y, p) ∈
      (legacyBallChart (I := I) Y x).pairHome '' e.target
    rw [htransport.2.1]
    exact hdom
  obtain ⟨w, hw, hwEq⟩ := himage
  have hdata := h
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z) at hdata
  have hwBall : e.symm w ∈ Metric.ball (0 : E × E) q := by
    rw [← hdata.1]
    exact e.map_target hw
  have hfence := hf
  change ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ normalBall (I := I) Y x ∧
    (e z).1 ∈ normalBall (I := I) Y x ∧
    (e z).2 ∈ normalBall (I := I) Y x at hfence
  have hwNormal : w.1 ∈ normalBall (I := I) Y x ∧
      w.2 ∈ normalBall (I := I) Y x := by
    have hout := (hfence (e.symm w)
      (Metric.ball_subset_closedBall hwBall)).2
    simpa only [e.right_inv hw] using hout
  have hwP : w ∈ P.source := by
    change w ∈ (normalPairHome (I := I) Y x).source
    rw [normalPair_source]
    exact hwNormal
  have hleft := P.left_inv hwP
  change
    (NormalCoordinates.normalChartAt (I := I) Y.metric x (P w).1,
      NormalCoordinates.normalChartAt (I := I) Y.metric x (P w).2) = w at hleft
  rw [hwEq] at hleft
  have hcoordSource :
      (NormalCoordinates.normalChartAt (I := I) Y.metric x y,
        NormalCoordinates.normalChartAt (I := I) Y.metric x p) ∈ P.source := by
    rw [hleft]
    exact hwP
  have hpairEq :
      normalPair (I := I) Y x
        (NormalCoordinates.normalChartAt (I := I) Y.metric x y,
          NormalCoordinates.normalChartAt (I := I) Y.metric x p) = (y, p) := by
    change
      ((NormalCoordinates.normalChartAt (I := I) Y.metric x).symm
          (NormalCoordinates.normalChartAt (I := I) Y.metric x y),
        (NormalCoordinates.normalChartAt (I := I) Y.metric x).symm
          (NormalCoordinates.normalChartAt (I := I) Y.metric x p)) = (y, p)
    rw [NormalCoordinates.normalChartAt_left_inv (I := I) Y.metric x hy,
      NormalCoordinates.normalChartAt_left_inv (I := I) Y.metric x hp]
  apply target_of_pair_mem (I := I) Y hcomplete hconn x hq h hcoordSource
  rwa [hpairEq]

theorem pair_mem_of_closed
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c))
    {w : E × E} (hw : w ∈ Metric.closedBall (0 : E × E) ρ) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    (q : Real) < c.radius →
    ρ ≤ δ →
    ρ < c.radius →
      normalPair (I := I) Y x w (c := c) ∈
        (toBranch (I := I) Y hcomplete hconn x hq h).dom := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  intro hqExp hρδ hρExp
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) (c := c) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z (c := c)) at h
  rcases h with ⟨hsource, _hzero, _heInf, htarget, _hinvInf, _hdiag⟩
  let A := chartTanHome (I := I) Y x c
  let P := chartPairHome (I := I) Y x c
  have hwnorm : ‖w‖ ≤ ρ := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  have hwP : w ∈ P.source := by
    change w ∈ c.pairHome.source
    rw [c.pairHome_source]
    constructor
    · change dist w.1 0 < c.radius
      rw [dist_zero_right]
      exact (norm_fst_le w).trans_lt (hwnorm.trans_lt hρExp)
    · change dist w.2 0 < c.radius
      rw [dist_zero_right]
      exact (norm_snd_le w).trans_lt (hwnorm.trans_lt hρExp)
  have hwe : w ∈ e.target :=
    htarget (Metric.closedBall_subset_closedBall hρδ hw)
  have hwinv : e.symm w ∈ e.source := e.map_target hwe
  have hwinvBall : e.symm w ∈ Metric.ball (0 : E × E) q := by
    rw [← hsource]
    exact hwinv
  have hwinvNorm : ‖e.symm w‖ < (q : Real) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hwinvBall
  have hwA : e.symm w ∈ A.source := by
    change e.symm w ∈ c.tangentHome.source
    rw [c.tangentHome_source]
    change dist (e.symm w).1 0 < c.radius
    rw [dist_zero_right]
    exact (norm_fst_le (e.symm w)).trans_lt (hwinvNorm.trans hqExp)
  unfold DiagInvBranch.dom
  change c.pair w ∈ (chartDiagHome (I := I) Y x c e).target
  rw [← c.pairHome_apply w]
  exact pair_mem_target A e P hwP hwe hwA

end IsNormalDiag

def HasNormalBranchDom
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) (q : NNReal) (δ ρ : Real)
    (c : NormalChartAt (I := I) Y x := legacyBallChart (I := I) Y x) :
    Prop := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  exact ∃ hq : 0 < q,
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      ∃ he : IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c),
        ∀ w ∈ Metric.closedBall (0 : E × E) ρ,
          normalPair (I := I) Y x w (c := c) ∈
            (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).dom

def HasNormalBranchInv
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) (q : NNReal) (δ ρ : Real) (η : NNReal)
    (c : NormalChartAt (I := I) Y x := legacyBallChart (I := I) Y x) :
    Prop := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  exact ∃ (hq : 0 < q) (e : OpenPartialHomeomorph (E × E) (E × E)),
    ∃ he : IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c),
      NormalDiagFence (I := I) Y x q e (c := c) ∧
      ApproximatesLinearOn
        (e.symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))
        e.target η ∧
      ∀ w ∈ Metric.closedBall (0 : E × E) ρ,
        normalPair (I := I) Y x w (c := c) ∈
          (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).dom

namespace HasNormalBranchDom

theorem exists_pair_branch
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    (hdom : HasNormalBranchDom (I := I) (X.obj k) hcomplete hconn x q δ ρ)
    {ι : Type*} (a b : ι → (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    ρ / 2 < expRadiusGp (I := I) (X.obj k).metric x →
      (∀ i, max (riemannianEDist I x (a i)) (riemannianEDist I x (b i)) <
        ENNReal.ofReal (ρ / 2)) →
      ∃ B : DiagInvBranch (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k)) x,
        ∀ i, (a i, b i) ∈ B.dom := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  intro hρExp hpairs
  change ∃ hq : 0 < q,
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      ∃ he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e,
        ∀ w ∈ Metric.closedBall (0 : E × E) ρ,
          normalPair (I := I) (X.obj k) x w ∈
            (IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn x hq he).dom at hdom
  obtain ⟨hq, e, he, hclosed⟩ := hdom
  refine ⟨IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn x hq he, ?_⟩
  intro i
  have haLt : riemannianEDist I x (a i) < ENNReal.ofReal (ρ / 2) :=
    (le_max_left _ _).trans_lt (hpairs i)
  have hbLt : riemannianEDist I x (b i) < ENNReal.ofReal (ρ / 2) :=
    (le_max_right _ _).trans_lt (hpairs i)
  have haFin : riemannianEDist I x (a i) ≠ ⊤ :=
    ne_of_lt (haLt.trans ENNReal.ofReal_lt_top)
  have hbFin : riemannianEDist I x (b i) ≠ ⊤ :=
    ne_of_lt (hbLt.trans ENNReal.ofReal_lt_top)
  have haReal : (riemannianEDist I x (a i)).toReal < ρ / 2 :=
    (ENNReal.lt_ofReal_iff_toReal_lt haFin).mp haLt
  have hbReal : (riemannianEDist I x (b i)).toReal < ρ / 2 :=
    (ENNReal.lt_ofReal_iff_toReal_lt hbFin).mp hbLt
  have haControl := hb.raw_chart_mem_norm_le k x (a i) ⟨haFin, haReal.trans hρExp⟩
  have hbControl := hb.raw_chart_mem_norm_le k x (b i) ⟨hbFin, hbReal.trans hρExp⟩
  let wa := NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x (a i)
  let wb := NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x (b i)
  have hwa : ‖wa‖ < ρ := by
    calc
      ‖wa‖ ≤ 2 * (riemannianEDist I x (a i)).toReal := haControl.2
      _ < 2 * (ρ / 2) := mul_lt_mul_of_pos_left haReal (by norm_num)
      _ = ρ := by ring
  have hwb : ‖wb‖ < ρ := by
    calc
      ‖wb‖ ≤ 2 * (riemannianEDist I x (b i)).toReal := hbControl.2
      _ < 2 * (ρ / 2) := mul_lt_mul_of_pos_left hbReal (by norm_num)
      _ = ρ := by ring
  have hwClosed : (wa, wb) ∈ Metric.closedBall (0 : E × E) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le hwa.le hwb.le
  have haTarget : wa ∈
      (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).target :=
    (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).map_source haControl.1
  have hbTarget : wb ∈
      (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).target :=
    (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).map_source hbControl.1
  have haDecode : NormalCoordinates.expMapDiffeo
      (I := I) (X.obj k).metric x wa = a i := by
    calc
      NormalCoordinates.expMapDiffeo (I := I) (X.obj k).metric x wa =
          expMap (I := I) (X.obj k).metric x wa :=
        NormalCoordinates.expMapDiffeo_apply_eq
          (I := I) (X.obj k).metric x haTarget
      _ =
          (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).symm wa :=
        (NormalCoordinates.normalChartAt_symm_apply
          (I := I) (X.obj k).metric x haTarget).symm
      _ = a i :=
        (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).left_inv haControl.1
  have hbDecode : NormalCoordinates.expMapDiffeo
      (I := I) (X.obj k).metric x wb = b i := by
    calc
      NormalCoordinates.expMapDiffeo (I := I) (X.obj k).metric x wb =
          expMap (I := I) (X.obj k).metric x wb :=
        NormalCoordinates.expMapDiffeo_apply_eq
          (I := I) (X.obj k).metric x hbTarget
      _ =
          (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).symm wb :=
        (NormalCoordinates.normalChartAt_symm_apply
          (I := I) (X.obj k).metric x hbTarget).symm
      _ = b i :=
        (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).left_inv hbControl.1
  have hnormalPair : normalPair (I := I) (X.obj k) x (wa, wb) = (a i, b i) := by
    change (NormalCoordinates.expMapDiffeo (I := I) (X.obj k).metric x wa,
      NormalCoordinates.expMapDiffeo (I := I) (X.obj k).metric x wb) = (a i, b i)
    rw [haDecode, hbDecode]
  rw [← hnormalPair]
  exact hclosed (wa, wb) hwClosed

theorem exists_pair_readout
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    (hdom : HasNormalBranchDom (I := I) (X.obj k) hcomplete hconn x q δ ρ)
    {ι : Type*} (a b : ι → (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    ρ / 2 < expRadiusGp (I := I) (X.obj k).metric x →
      (∀ i, max (riemannianEDist I x (a i)) (riemannianEDist I x (b i)) <
        ENNReal.ofReal (ρ / 2)) →
      ∃ B : DiagInvBranch (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k)) x,
        ∀ i, (a i, b i) ∈ B.readDom := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  intro hρExp hpairs
  obtain ⟨B, hB⟩ := exists_pair_branch (I := I) hb k hcomplete hconn x hdom
    a b hρExp hpairs
  refine ⟨B, fun i => ⟨hB i, ?_⟩⟩
  have haLt : riemannianEDist I x (a i) < ENNReal.ofReal (ρ / 2) :=
    (le_max_left _ _).trans_lt (hpairs i)
  have haFin : riemannianEDist I x (a i) ≠ ⊤ :=
    ne_of_lt (haLt.trans ENNReal.ofReal_lt_top)
  have haReal : (riemannianEDist I x (a i)).toReal < ρ / 2 :=
    (ENNReal.lt_ofReal_iff_toReal_lt haFin).mp haLt
  have haSource :=
    (NormalCoordMetricBoundInput.chart_mem_norm_le (I := I)
      k x (a i) ⟨haFin, haReal.trans hρExp⟩).1
  rw [TangentBundle.trivializationAt_baseSet]
  apply NormalCoordinates.exp_target_sub_chart (I := I) (X.obj k).metric x
  change a i ∈
    (NormalCoordinates.framedExpDiffeo (I := I) (X.obj k).metric x).target at haSource
  rw [NormalCoordinates.framedExp_target] at haSource
  exact haSource

end HasNormalBranchDom

namespace NormalChartData

theorem exists_pair_readout
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : NormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    (hdom : HasNormalBranchDom (I := I) (X.obj k) hcomplete hconn
      x q δ ρ (d.chart k x))
    {ι : Type*} (a b : ι → (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    ρ / 2 < (d.chart k x).radius →
      (∀ i, max (riemannianEDist I x (a i)) (riemannianEDist I x (b i)) <
        ENNReal.ofReal (ρ / 2)) →
      ∃ B : DiagInvBranch (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k)) x,
        ∀ i, (a i, b i) ∈ B.chartReadDom (d.chart k x) := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  intro hρChart hpairs
  change ∃ hq : 0 < q,
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      ∃ he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn
          x q δ e (c := d.chart k x),
        ∀ w ∈ Metric.closedBall (0 : E × E) ρ,
          normalPair (I := I) (X.obj k) x w (c := d.chart k x) ∈
            (IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn
              x hq he).dom at hdom
  obtain ⟨hq, e, he, hclosed⟩ := hdom
  let B := IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn x hq he
  refine ⟨B, ?_⟩
  intro i
  have haLt : riemannianEDist I x (a i) < ENNReal.ofReal (ρ / 2) :=
    (le_max_left _ _).trans_lt (hpairs i)
  have hbLt : riemannianEDist I x (b i) < ENNReal.ofReal (ρ / 2) :=
    (le_max_right _ _).trans_lt (hpairs i)
  have hhalfChart :
      ENNReal.ofReal (ρ / 2) < ENNReal.ofReal (d.chart k x).radius :=
    (ENNReal.ofReal_lt_ofReal_iff (d.chart k x).radius_pos).2 hρChart
  have haFin : riemannianEDist I x (a i) ≠ ⊤ :=
    ne_of_lt (haLt.trans ENNReal.ofReal_lt_top)
  have hbFin : riemannianEDist I x (b i) ≠ ⊤ :=
    ne_of_lt (hbLt.trans ENNReal.ofReal_lt_top)
  have haReal : (riemannianEDist I x (a i)).toReal < ρ / 2 :=
    (ENNReal.lt_ofReal_iff_toReal_lt haFin).mp haLt
  have hbReal : (riemannianEDist I x (b i)).toReal < ρ / 2 :=
    (ENNReal.lt_ofReal_iff_toReal_lt hbFin).mp hbLt
  have hρ : 0 < ρ := by
    have hnonneg : 0 ≤ (riemannianEDist I x (a i)).toReal := ENNReal.toReal_nonneg
    linarith
  have haControl :=
    d.readout_mem k hcomplete hconn x (a i) (haLt.trans hhalfChart)
  have hbControl :=
    d.readout_mem k hcomplete hconn x (b i) (hbLt.trans hhalfChart)
  let wa := (d.chart k x).inv (a i)
  let wb := (d.chart k x).inv (b i)
  have hwa : ‖wa‖ < ρ := by
    rw [haControl.2]
    linarith
  have hwb : ‖wb‖ < ρ := by
    rw [hbControl.2]
    linarith
  have hwClosed : (wa, wb) ∈ Metric.closedBall (0 : E × E) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le hwa.le hwb.le
  have haDecode : (d.chart k x).hom wa = a i := by
    change (d.chart k x).hom ((d.chart k x).hom.symm (a i)) = a i
    apply (d.chart k x).hom.right_inv
    obtain ⟨z, hz, hza⟩ := haControl.1
    rw [← hza]
    exact (d.chart k x).hom.map_source ((d.chart k x).ball_subset hz)
  have hbDecode : (d.chart k x).hom wb = b i := by
    change (d.chart k x).hom ((d.chart k x).hom.symm (b i)) = b i
    apply (d.chart k x).hom.right_inv
    obtain ⟨z, hz, hzb⟩ := hbControl.1
    rw [← hzb]
    exact (d.chart k x).hom.map_source ((d.chart k x).ball_subset hz)
  have hnormalPair :
      normalPair (I := I) (X.obj k) x (wa, wb) (c := d.chart k x) =
        (a i, b i) := by
    change ((d.chart k x).hom wa, (d.chart k x).hom wb) = (a i, b i)
    rw [haDecode, hbDecode]
  have hdomPair : (a i, b i) ∈ B.dom := by
    rw [← hnormalPair]
    exact hclosed (wa, wb) hwClosed
  refine ⟨hdomPair, ?_⟩
  change a i ∈ (d.chart k x).hom '' Metric.ball 0 (d.chart k x).radius
  exact haControl.1

end NormalChartData

namespace NormalRadiusProfile

theorem exists_common_dom
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) :
    ∃ (q : NNReal) (δ ρ : Real),
      0 < q ∧ 0 < δ ∧ 0 < ρ ∧ ρ ≤ δ ∧
      4 * (q : Real) < h.phaseRadius R ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      ∀ k (x : (X.obj k).M),
        hd.dist k x (X.obj k).basepoint ≤ R →
        HasNormalBranchDom (I := I) (X.obj k) (hcomplete.complete k)
          (hconn k) x q δ ρ := by
  obtain ⟨q, δ, hq, hqRadius, hδ, hδeq, hall⟩ :=
    h.exists_uniform_diag hcomplete hconn R
  let ρ : Real := min δ ((q : Real) / 2)
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact lt_min hδ (div_pos hqReal (by norm_num))
  have hρδ : ρ ≤ δ := by
    exact min_le_left _ _
  have hρq : ρ < (q : Real) := by
    have hhalf : (q : Real) / 2 < q := by linarith
    exact (min_le_right _ _).trans_lt hhalf
  have hqFloor : (q : Real) < h.ratio * hd.mu R := by
    have hqRadius' := hqRadius
    rw [phaseRadius] at hqRadius'
    nlinarith [h.floor_pos R]
  refine ⟨q, δ, ρ, hq, hδ, hρ, hρδ, hqRadius, hδeq, ?_⟩
  intro k x hx
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn k
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  have hqExp : (q : Real) < expMapC2Radius (I := I) (X.obj k).metric x :=
    hqFloor.trans_le (h.floor_le_exp hx)
  have hρExp : ρ < expMapC2Radius (I := I) (X.obj k).metric x :=
    hρq.trans hqExp
  obtain ⟨e, he⟩ := hall k x hx
  change ∃ hq' : 0 < q,
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      ∃ he : IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k) (hconn k)
          x q δ e,
        ∀ w ∈ Metric.closedBall (0 : E × E) ρ,
          normalPair (I := I) (X.obj k) x w ∈
            (IsNormalDiag.toBranch (I := I) (X.obj k) (hcomplete.complete k)
              (hconn k) x hq' he).dom
  refine ⟨hq, e, he, ?_⟩
  intro w hw
  exact IsNormalDiag.pair_mem_of_closed (I := I) (X.obj k)
    (hcomplete.complete k) (hconn k) x hq he hw hqExp hρδ hρExp

end NormalRadiusProfile

namespace BoundedGeometryNormalData

theorem exists_common_inv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) :
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ (q : NNReal) (δ ρ : Real),
      0 < q ∧ 0 < δ ∧ 0 < ρ ∧ ρ ≤ δ ∧
      4 * (q : Real) < d.phaseRadius R ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (d.phaseK (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      N * (T - PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (d.phaseK (2 * q)) < 1 / 24 ∧
      ∀ k (x : (X.obj k).M),
        hd.dist k x (X.obj k).basepoint ≤ R →
        letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
        letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
        letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
        letI : T2Space (TangentBundle I (X.obj k).M) :=
          (X.obj k).t2TangentBundle
        HasNormalBranchInv (I := I) (X.obj k) (hcomplete.complete k)
          (hconn k) x q δ ρ
          (N * (T - PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
            PhaseFlow.phaseErr (d.phaseK (2 * q)))
          (c := d.chart k x) := by
  let N0 : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  let T0 : NNReal := N0⁻¹
  obtain ⟨q, δ, hq, hqRadius, hδ, hδeq, hinvErr, hall⟩ :=
    d.exists_diag_inv hcomplete hconn R
  let ρ : Real := min δ ((q : Real) / 2)
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact lt_min hδ (div_pos hqReal (by norm_num))
  have hρδ : ρ ≤ δ := min_le_left _ _
  have hρq : ρ < (q : Real) := by
    exact (min_le_right _ _).trans_lt (by linarith)
  refine ⟨q, δ, ρ, hq, hδ, hρ, hρδ, hqRadius, hδeq, hinvErr, ?_⟩
  intro k x hx
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn k
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  have hphaseChart :
      d.phaseRadius R ≤ (d.chart k x).radius / 4 := by
    rw [phaseRadius, d.radius_eq]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hd.mu_antitone hx) d.ratio_pos.le)
      (by norm_num)
  have hqChart : (q : Real) < (d.chart k x).radius := by
    have hrPos := (d.chart k x).radius_pos
    nlinarith [hqRadius, hphaseChart]
  have hρChart : ρ < (d.chart k x).radius := hρq.trans hqChart
  obtain ⟨e, he, hfence, hinvApprox⟩ := hall k x hx
  change ∃ (hq' : 0 < q) (e : OpenPartialHomeomorph (E × E) (E × E)),
    ∃ he : IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k)
        (hconn k) x q δ e (c := d.chart k x),
      NormalDiagFence (I := I) (X.obj k) x q e (c := d.chart k x) ∧
      ApproximatesLinearOn
        (e.symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))
        e.target
        (N0 * (T0 - PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (d.phaseK (2 * q))) ∧
      ∀ w ∈ Metric.closedBall (0 : E × E) ρ,
        normalPair (I := I) (X.obj k) x w (c := d.chart k x) ∈
          (IsNormalDiag.toBranch (I := I) (X.obj k) (hcomplete.complete k)
            (hconn k) x hq' he).dom
  refine ⟨hq, e, he, hfence, hinvApprox, ?_⟩
  intro w hw
  exact IsNormalDiag.pair_mem_of_closed (I := I) (X.obj k)
    (hcomplete.complete k) (hconn k) x hq he hw hqChart hρδ hρChart

theorem exists_common_dom
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) :
    ∃ (q : NNReal) (δ ρ : Real),
      0 < q ∧ 0 < δ ∧ 0 < ρ ∧ ρ ≤ δ ∧
      4 * (q : Real) < d.phaseRadius R ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (d.phaseK (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      ∀ k (x : (X.obj k).M),
        hd.dist k x (X.obj k).basepoint ≤ R →
        letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
        letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
        letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
        letI : T2Space (TangentBundle I (X.obj k).M) :=
          (X.obj k).t2TangentBundle
        HasNormalBranchDom (I := I) (X.obj k) (hcomplete.complete k)
          (hconn k) x q δ ρ (d.chart k x) := by
  let N0 : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  let T0 : NNReal := N0⁻¹
  obtain ⟨q, δ, ρ, hq, hδ, hρ, hρδ, hqRadius, hδeq, _hinvErr, hall⟩ :=
    d.exists_common_inv hcomplete hconn R
  refine ⟨q, δ, ρ, hq, hδ, hρ, hρδ, hqRadius, hδeq, ?_⟩
  intro k x hx
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn k
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  have hInv := hall k x hx
  change ∃ (hq' : 0 < q) (e : OpenPartialHomeomorph (E × E) (E × E)),
    ∃ he : IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k) (hconn k)
        x q δ e (c := d.chart k x),
      NormalDiagFence (I := I) (X.obj k) x q e (c := d.chart k x) ∧
      ApproximatesLinearOn
        (e.symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))
        e.target
        (N0 * (T0 - PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (d.phaseK (2 * q))) ∧
      ∀ w ∈ Metric.closedBall (0 : E × E) ρ,
        normalPair (I := I) (X.obj k) x w (c := d.chart k x) ∈
          (IsNormalDiag.toBranch (I := I) (X.obj k) (hcomplete.complete k)
            (hconn k) x hq' he).dom at hInv
  obtain ⟨hq', e, he, _hfence, _hinvApprox, hclosed⟩ := hInv
  change ∃ hq' : 0 < q,
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      ∃ he : IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k) (hconn k)
          x q δ e (c := d.chart k x),
        ∀ w ∈ Metric.closedBall (0 : E × E) ρ,
          normalPair (I := I) (X.obj k) x w (c := d.chart k x) ∈
            (IsNormalDiag.toBranch (I := I) (X.obj k) (hcomplete.complete k)
              (hconn k) x hq' he).dom
  exact ⟨hq', e, he, hclosed⟩

end BoundedGeometryNormalData

end HCGCompactness
end DifferentialGeometry
