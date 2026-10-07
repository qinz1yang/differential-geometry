import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckBoundaryChord
import DifferentialGeometry.Topology.MetricSpace.TruncatedDistanceLevel

noncomputable section

open Bundle Manifold Set Function
open DifferentialGeometry DifferentialGeometry.Geometry
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private theorem capRadius_pos : 0 < standardCapL := by
  rw [standardCapL_eq_transitionEnd]
  exact DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd_pos

def capBoundaryCoordinate (y : Sphere 2) : ThreeSpace := standardCapL • y.val

theorem capBoundaryCoordinate_injective : Injective capBoundaryCoordinate := by
  intro y z h
  apply Subtype.ext
  have hc := congrArg (fun x : ThreeSpace => standardCapL⁻¹ • x) h
  simpa only [capBoundaryCoordinate, smul_smul, inv_mul_cancel₀ capRadius_pos.ne', one_smul]
    using hc

def capBoundaryCorePoint (y : Sphere 2) : standardCapClosedCore :=
  ⟨capBoundaryCoordinate y, by
    change dist (standardCapL • y.val) 0 ≤ standardCapL
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos capRadius_pos,
      norm_eq_of_mem_sphere y, mul_one]⟩

namespace MetricCutCapEvent.PresentedStaticCap

universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D η : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
  (S : E.PresentedStaticCap fixed D m η b)

def boundaryOldPoint (hOld : E.old = E.transition.trace.retainedCore)
    (y : Sphere 2) : E.old :=
  ⟨(S.retainedPoint ⟨(y, 0), le_rfl, inv_pos.mpr S.neck.delta_pos⟩).val,
    hOld.symm ▸ (S.retainedPoint
      ⟨(y, 0), le_rfl, inv_pos.mpr S.neck.delta_pos⟩).property⟩

theorem oldTerminal_boundaryOldPoint (hOld : E.old = E.transition.trace.retainedCore)
    (y : Sphere 2) :
    E.oldTerminal (S.boundaryOldPoint hOld y) = S.neck.boundaryPoint y := by
  apply Subtype.ext
  rw [E.oldTerminal_eq]
  exact S.retained_point_eq ⟨(y, 0), le_rfl, inv_pos.mpr S.neck.delta_pos⟩ (by
    have hp := inv_pos.mpr S.neck.delta_pos
    constructor <;> linarith)

theorem oldOutput_boundaryOldPoint (hOld : E.old = E.transition.trace.retainedCore)
    (y : Sphere 2) :
    E.oldOutput (S.boundaryOldPoint hOld y) =
      S.inclusion (S.witness.capChart (capBoundaryCorePoint y)) := by
  have hret := S.retained_eq ⟨(y, 0), le_rfl, inv_pos.mpr S.neck.delta_pos⟩
  have hactual := E.oldOutput_eq (S.boundaryOldPoint hOld y)
  have heq : E.oldOutput (S.boundaryOldPoint hOld y) =
      S.inclusion (S.witness.retained ⟨(y, 0), le_rfl, inv_pos.mpr S.neck.delta_pos⟩) :=
    Sum.inl.inj (hactual.symm.trans hret)
  rw [heq]
  exact congrArg S.inclusion
    (S.witness.capChart_boundary y (capBoundaryCorePoint y).property).symm

/-- A path on this cap's retained boundary, measured in this event's terminal metric. -/
theorem exists_actual_boundary_curve (hOld : E.old = E.transition.trace.retainedCore)
    (y z : Sphere 2) :
    ∃ σ : ℝ → Sphere 2,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ σ ∧ σ 0 = y ∧ σ 1 = z ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞
        (fun t => E.oldTerminal (S.boundaryOldPoint hOld (σ t))) ∧
      metricPathELength E.terminal.metric
        (fun t => E.oldTerminal (S.boundaryOldPoint hOld (σ t))) 0 1 ≤
        ENNReal.ofReal (Real.pi / Real.sqrt S.neck.scale * ‖(y : ThreeSpace) - z‖) := by
  obtain ⟨σ, hσ, h0, h1, hγ, hlength⟩ := S.neck.exists_boundary_curve y z
  refine ⟨σ, hσ, h0, h1, ?_, ?_⟩
  · simpa only [S.oldTerminal_boundaryOldPoint hOld, Function.comp_def] using hγ
  · simpa only [S.oldTerminal_boundaryOldPoint hOld, Function.comp_def] using hlength

def boundaryExtensionConstant : ℝ≥0 :=
  ⟨Real.pi / (standardCapL * Real.sqrt S.neck.scale),
    le_of_lt (div_pos Real.pi_pos (mul_pos capRadius_pos
      (Real.sqrt_pos.mpr S.neck.scale_pos)))⟩

/-- The boundary scalar data admit a Euclidean extension with the exact same constant.
The truncation is taken in ENNReal before `toReal`, including other components. -/
theorem exists_boundary_distance_extension
    (p : E.incoming.terminalRegularOpen) (N : ℝ≥0) :
    ∃ f : ThreeSpace → ℝ, LipschitzWith S.boundaryExtensionConstant f ∧
      ∀ y : Sphere 2, f (capBoundaryCoordinate y) =
        (min (riemannianEDistOf E.terminal.metric (S.neck.boundaryPoint y) p)
          (N : ℝ≥0∞)).toReal := by
  let data : Sphere 2 → ℝ := fun y =>
    (min (riemannianEDistOf E.terminal.metric (S.neck.boundaryPoint y) p)
      (N : ℝ≥0∞)).toReal
  have hdata (y z : Sphere 2) : edist (data y) (data z) ≤
      riemannianEDistOf E.terminal.metric (S.neck.boundaryPoint y) (S.neck.boundaryPoint z) := by
    let : RiemannianBundle (TangentSpace ThreeModel : E.incoming.terminalRegularOpen → Type _) :=
      ⟨E.terminal.metric.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle ThreeSpace
        (TangentSpace ThreeModel : E.incoming.terminalRegularOpen → Type _) :=
      ⟨E.terminal.metric.inner, E.terminal.metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    let terminalMetricSpace : PseudoEMetricSpace E.incoming.terminalRegularOpen :=
      .ofRiemannianMetric ThreeModel E.incoming.terminalRegularOpen
    have hdist (x z : E.incoming.terminalRegularOpen) :
        @edist E.incoming.terminalRegularOpen terminalMetricSpace.toEDist x z =
          riemannianEDistOf E.terminal.metric x z := rfl
    have h := @EMetric.lipschitzWith_truncated_edist_level
      E.incoming.terminalRegularOpen terminalMetricSpace p N
      (S.neck.boundaryPoint y) (S.neck.boundaryPoint z)
    simpa only [data, ENNReal.coe_one, one_mul, hdist] using h
  let f₀ : ThreeSpace → ℝ := Function.extend capBoundaryCoordinate data (fun _ => 0)
  have hf₀ : LipschitzOnWith S.boundaryExtensionConstant f₀ (range capBoundaryCoordinate) := by
    rintro _ ⟨y, rfl⟩ _ ⟨z, rfl⟩
    change edist (f₀ (capBoundaryCoordinate y)) (f₀ (capBoundaryCoordinate z)) ≤ _
    dsimp only [f₀]
    rw [capBoundaryCoordinate_injective.extend_apply data (fun _ => 0) y,
      capBoundaryCoordinate_injective.extend_apply data (fun _ => 0) z]
    apply ((hdata y z).trans (S.neck.edist_boundaryPoint_le_chord y z)).trans_eq
    rw [edist_dist, dist_eq_norm, capBoundaryCoordinate, capBoundaryCoordinate,
      ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos capRadius_pos]
    have hreal : Real.pi / Real.sqrt S.neck.scale * ‖(y : ThreeSpace) - z‖ =
        (S.boundaryExtensionConstant : ℝ) * (standardCapL * ‖(y : ThreeSpace) - z‖) := by
      change _ = (Real.pi / (standardCapL * Real.sqrt S.neck.scale)) *
        (standardCapL * ‖(y : ThreeSpace) - z‖)
      rw [mul_comm standardCapL (Real.sqrt S.neck.scale), ← div_div,
        ← mul_assoc, div_mul_cancel₀ _ capRadius_pos.ne']
    exact (congrArg ENNReal.ofReal hreal).trans
      ((ENNReal.ofReal_mul S.boundaryExtensionConstant.coe_nonneg).trans
        (by rw [ENNReal.ofReal_coe_nnreal]))
  obtain ⟨f, hf, heq⟩ := hf₀.extend_real
  refine ⟨f, hf, ?_⟩
  intro y
  exact (heq (mem_range_self y)).symm.trans
    (capBoundaryCoordinate_injective.extend_apply data (fun _ => 0) y)

/-- Install the coordinate extension on the SAME actual cap image. This specifies
its actual retained-boundary values; it makes no continuity claim across the seam. -/
theorem exists_actual_cap_distance_extension
    (hOld : E.old = E.transition.trace.retainedCore)
    (p : E.incoming.terminalRegularOpen) (N : ℝ≥0) :
    ∃ (f : ThreeSpace → ℝ) (F : Q.Carrier → ℝ),
      LipschitzWith S.boundaryExtensionConstant f ∧
      (∀ x : standardCapClosedCore, F (S.inclusion (S.witness.capChart x)) = f x.val) ∧
      ∀ y : Sphere 2, F (E.oldOutput (S.boundaryOldPoint hOld y)) =
        (min (riemannianEDistOf E.terminal.metric
          (E.oldTerminal (S.boundaryOldPoint hOld y)) p) (N : ℝ≥0∞)).toReal := by
  obtain ⟨f, hf, hboundary⟩ := S.exists_boundary_distance_extension p N
  let j : standardCapClosedCore → Q.Carrier := fun x => S.inclusion (S.witness.capChart x)
  let : ChartedSpace (EuclideanHalfSpace 3) standardCapClosedCore := S.witness.modelCoreCharts
  let : IsManifold (𝓡∂ 3) ∞ standardCapClosedCore := S.witness.modelCoreSmooth
  have hj : Injective j := S.inclusion_smooth.isEmbedding.injective.comp
    S.witness.capChart_smooth.isEmbedding.injective
  let F : Q.Carrier → ℝ := Function.extend j (fun x => f x.val) (fun _ => 0)
  have hF (x : standardCapClosedCore) : F (j x) = f x.val :=
    hj.extend_apply (fun x => f x.val) (fun _ => 0) x
  refine ⟨f, F, hf, hF, ?_⟩
  intro y
  rw [S.oldOutput_boundaryOldPoint hOld, S.oldTerminal_boundaryOldPoint hOld]
  exact (hF (capBoundaryCorePoint y)).trans (hboundary y)

end MetricCutCapEvent.PresentedStaticCap

namespace GeometricCutoffRecord

universe u

/-- The actual history record supplies both the cap and the retained-core identity. -/
theorem exists_cap_boundary_distance_extension
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
    (R : GeometricCutoffRecord H i parameters) (b : (H.event i).RetainedBoundaryIndex)
    (p : (H.event i).incoming.terminalRegularOpen) (N : ℝ≥0) :
    let S := R.static b
    ∃ (f : ThreeSpace → ℝ) (F : (H.stage i.succ).Carrier → ℝ),
      LipschitzWith S.boundaryExtensionConstant f ∧
      (∀ x : standardCapClosedCore, F (S.inclusion (S.witness.capChart x)) = f x.val) ∧
      ∀ y : Sphere 2, F ((H.event i).oldOutput (S.boundaryOldPoint R.old_eq_retained y)) =
        (min (riemannianEDistOf (H.event i).terminal.metric
          ((H.event i).oldTerminal (S.boundaryOldPoint R.old_eq_retained y)) p)
          (N : ℝ≥0∞)).toReal :=
  (R.static b).exists_actual_cap_distance_extension R.old_eq_retained p N

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
