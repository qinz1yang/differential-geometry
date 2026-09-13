import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedOrientedStage
import DifferentialGeometry.Geometry.Neck.NormalizedDatum
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSmoothManifold
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSeparation

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem finrank_threeSpace_eq_three : Module.finrank ℝ ThreeSpace = 3 := by simp

noncomputable def TangentOrientationSection.ofSmoothOrientation {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (o : DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel M) :
    TangentOrientationSection M :=
  TangentOrientationSection.ofManifoldOrientation
    (cast (congrArg (fun n => DifferentialGeometry.ManifoldOrientation ThreeModel M n)
        finrank_threeSpace_eq_three)
      (Classical.choose
        (DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
          ThreeModel o)))

noncomputable def OrientedThreeStage.ofSmoothOrientation (M : Type u) [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
    (o : DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel M) :
    OrientedThreeStage.{u} where
  Carrier := M
  orientation := TangentOrientationSection.ofSmoothOrientation o

noncomputable def OrientedThreeStage.ofFiniteCapQuotient {M : Type u} [TopologicalSpace M]
    {ι : Type u} [Finite ι] {precision : ι → ℝ} {L : ℝ}
    (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, DifferentialGeometry.Geometry.Neck.bufferedCylinder (precision i) → M)
    (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    [charts : ChartedSpace ThreeSpace
      (DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient hL hδ f
        (fun i => (hf i).injective) hdisj)]
    [smooth : IsManifold ThreeModel ∞
      (DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient hL hδ f
        (fun i => (hf i).injective) hdisj)]
    [hausdorff : T2Space
      (DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient hL hδ f
        (fun i => (hf i).injective) hdisj)]
    [compact : CompactSpace
      (DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient hL hδ f
        (fun i => (hf i).injective) hdisj)]
    (o : DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel
      (DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient hL hδ f
        (fun i => (hf i).injective) hdisj)) : OrientedThreeStage.{u} :=
  OrientedThreeStage.ofSmoothOrientation
    (DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient hL hδ f
      (fun i => (hf i).injective) hdisj) o

private def sphereTwoPoint : Sphere 2 :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩

private def tubeDomainCoord (z : TubeDomain) : Sphere 2 × ℝ := (z.1, z.2.1)

private theorem continuous_tubeDomainCoord : Continuous tubeDomainCoord :=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

private theorem tubeDomainCoord_mem_bufferedCylinder (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (z : TubeDomain) :
    tubeDomainCoord z ∈ (DifferentialGeometry.Geometry.Neck.bufferedCylinder δ :
      Set (Sphere 2 × ℝ)) := by
  have hδinv : 1 < δ⁻¹ := (one_lt_inv₀ hδ).mpr hδ1
  have hlow : (-2 : ℝ) ≤ z.2.1 := z.2.2.1
  have hhigh : z.2.1 ≤ (2 : ℝ) := z.2.2.2
  change (-δ⁻¹ - 1 : ℝ) < z.2.1 ∧ z.2.1 < δ⁻¹ + 1
  exact ⟨by linarith, by linarith⟩

def tubeDomainToBufferedCylinder (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    TubeDomain → DifferentialGeometry.Geometry.Neck.bufferedCylinder δ := fun z =>
  ⟨tubeDomainCoord z, tubeDomainCoord_mem_bufferedCylinder δ hδ hδ1 z⟩

theorem continuous_tubeDomainToBufferedCylinder (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Continuous (tubeDomainToBufferedCylinder δ hδ hδ1) :=
  Continuous.subtype_mk continuous_tubeDomainCoord
    (tubeDomainCoord_mem_bufferedCylinder δ hδ hδ1)

theorem tubeDomainToBufferedCylinder_injective (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Injective (tubeDomainToBufferedCylinder δ hδ hδ1) := by
  intro z w hzw
  have hcoord : tubeDomainCoord z = tubeDomainCoord w := congrArg Subtype.val hzw
  have hfst : z.1 = w.1 := congrArg (fun p : Sphere 2 × ℝ => p.1) hcoord
  have hsnd : z.2.1 = w.2.1 := congrArg (fun p : Sphere 2 × ℝ => p.2) hcoord
  exact Prod.ext hfst (Subtype.ext hsnd)

theorem not_exists_levelPreserving_bufferedCylinder_to_tubeDomain (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    ¬∃ g : DifferentialGeometry.Geometry.Neck.bufferedCylinder δ → TubeDomain,
      ∀ q, ((g q).2 : ℝ) = q.val.2 := by
  rintro ⟨g, hg⟩
  have hδinv : 2 < δ⁻¹ := by
    rw [← one_div, lt_div_iff₀ hδ]
    linarith
  have hmem : (sphereTwoPoint, 3) ∈
      (DifferentialGeometry.Geometry.Neck.bufferedCylinder δ : Set (Sphere 2 × ℝ)) :=
    ⟨by linarith [inv_pos.mpr hδ], by linarith⟩
  have hle : ((g ⟨(sphereTwoPoint, 3), hmem⟩).2 : ℝ) ≤ 2 := (g _).2.2.2
  have heq : ((g ⟨(sphereTwoPoint, 3), hmem⟩).2 : ℝ) = 3 := hg _
  linarith

theorem nonempty_source_of_metricCutCapEvent {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) : Nonempty P.Carrier :=
  E.transition.source_nonempty

theorem nontrivial_of_metricCutCapEvent {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) :
    Nonempty E.transition.trace.tubes.Index ∨ Nonempty E.discarded.Carrier :=
  E.transition.trace.nontrivial

theorem nonempty_cutCapTopology_of_metricCutCapEvent {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) :
    Nonempty (CutCapTopology P.Carrier Q.Carrier E.discarded.Carrier E.capped.Carrier) :=
  ⟨E.transition.trace⟩

theorem isEmpty_metricCutCapEvent_of_isEmpty_source {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (hP : IsEmpty P.Carrier) : IsEmpty (MetricCutCapEvent P Q a s) :=
  ⟨fun E => hP.false E.transition.source_nonempty.some⟩

theorem isEmpty_cutCapTopology_pempty : IsEmpty (CutCapTopology PEmpty PEmpty PEmpty PEmpty) :=
  ⟨fun E => by
    rcases E.nontrivial with h | h
    · obtain ⟨a⟩ := h
      exact PEmpty.elim ((E.tubes.tube a) (sphereTwoPoint, ⟨0, by norm_num, by norm_num⟩))
    · exact PEmpty.elim h.some⟩

theorem nonempty_smoothCutCapTransition_of_metricCutCapEvent
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s) :
    Nonempty (SmoothCutCapTransition P Q E.discarded E.capped) :=
  ⟨E.transition⟩

theorem nonempty_incomingSlab_of_metricCutCapEvent {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) : Nonempty (P.IncomingSlab a s) :=
  ⟨E.incoming⟩

theorem nonempty_terminalLimitMetric_of_metricCutCapEvent {P Q : OrientedThreeStage.{u}}
    {a s : ℝ} (E : MetricCutCapEvent P Q a s) :
    Nonempty E.incoming.TerminalLimitMetric :=
  ⟨E.terminal⟩

private noncomputable def threeSpaceSmoothOrientation :
    DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel ThreeSpace :=
  DifferentialGeometry.Topology.Manifold.euclideanSmoothOrientation ThreeSpace
    (Orientation.reindex ℝ ThreeSpace (finCongr finrank_threeSpace_eq_three).symm
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation))

theorem nonempty_tangentOrientationSection_threeSpace :
    Nonempty (TangentOrientationSection ThreeSpace) :=
  ⟨TangentOrientationSection.ofSmoothOrientation threeSpaceSmoothOrientation⟩

private noncomputable def sphereThreeSmoothOrientation :
    DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel (Sphere 3) :=
  DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation ThreeModel
    (cast (congrArg (fun n => DifferentialGeometry.ManifoldOrientation ThreeModel (Sphere 3) n)
        finrank_threeSpace_eq_three.symm)
      (DifferentialGeometry.sphereOrientation 3 (by decide)))

theorem nonempty_orientedThreeStage : Nonempty OrientedThreeStage.{0} :=
  ⟨OrientedThreeStage.ofSmoothOrientation (Sphere 3) sphereThreeSmoothOrientation⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
