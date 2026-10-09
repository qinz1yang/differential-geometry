import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformBirthSpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.NativeObservationCertificates

/-!
# S-CH11-FIX11 port of astra `UniformClosedBirthObservationEstimates`（`PortC11P`）

来源：donor `UniformClosedBirthObservationEstimates.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* l.43 陈述里 `metricScalarAt` unknown identifier → 加 `open DifferentialGeometry.Geometry.Curvature`
  （定义在 `Geometry/Curvature/Metric/Defs.lean`）；
* 陈述 binder `I` 不被引用 → `_I`（unusedVariables）。

原路径 `UniformClosedBirthObservationEstimates` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal

namespace GC.GeneralFlow

universe u

/-- Select the complete native analytic packet and nonzero-birth spatial
control before the fine class. The original estimates, outgoing slab, pinching,
marking, and cutoff records all belong to the same supplied history. -/
theorem exists_uniform_closed_birth_observation_estimate_packet :
    ∃ εbar : ℝ, 0 < εbar ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ εbar →
    ∃ (C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0),
      1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 1 ≤ Cs ∧
      0 < τmin ∧ 1 ≤ Cbirth ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
    ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
      0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
      max 1 (max qcan qs) ≤ Qbirth ∧
      0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
    ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
      (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
      K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      K.NoncollapsedBefore κ ε K.horizon →
      NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
      ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
        (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
        K.toHistory.activeStage t ≠ 0 →
        ∀ y : (K.toHistory.stageAt t).Carrier,
          Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
          ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
            ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε := by
  obtain ⟨εa, hεa, analytic⟩ := exists_uniform_observation_estimate_packet.{u}
  obtain ⟨εb, hεb, birth⟩ :=
    RetainedCoreHistory.exists_uniform_spatialCanonicalWitness_at_nonzero_birth.{u}
  refine ⟨min εa εb, lt_min hεa hεb, ?_⟩
  intro ε hε hε11 hεbar
  obtain ⟨C1, C2, C1s, C2s, Cs, τmin, Ctime, Cgrad,
      hC1, hC2, hC1s, hC2s, hCs, hτmin, analytic⟩ :=
    analytic ε hε hε11 (hεbar.trans (min_le_left _ _))
  obtain ⟨Cbirth, hCbirth, birth⟩ := birth ε hε hε11 (hεbar.trans (min_le_right _ _))
  refine ⟨C1, C2, C1s, C2s, Cs, τmin, Cbirth, Ctime, Cgrad,
    hC1, hC2, hC1s, hC2s, hCs, hτmin, hCbirth, ?_⟩
  intro P g B κ hB hκ
  obtain ⟨phi, hphi, pinching⟩ := exists_pinching_certificates_for_identified_histories P g
  obtain ⟨qcan, qs, δa, ρa, ζa, Da, ma, hqcan, hqs, hqsC, hδa, hρa, hζa, hDa, analytic⟩ :=
    analytic P g B κ hB hκ
  let Q : ℝ := max 1 (max qcan qs)
  have hQ : 1 ≤ Q := le_max_left _ _
  have hcanQ : qcan ≤ Q := (le_max_left qcan qs).trans (le_max_right 1 (max qcan qs))
  have hsQ : qs ≤ Q := (le_max_right qcan qs).trans (le_max_right 1 (max qcan qs))
  obtain ⟨Qbirth, δb, ρb, ζb, Db, mb, hQbirth, hδb, hρb, hζb, -, birth⟩ :=
    birth P g κ ε C1s C2s Ctime Cgrad phi Q hκ hε hphi hQ
  refine ⟨qcan, qs, Qbirth, min δa δb, min ρa ρb, min ζa ζb, max Da Db, max ma mb,
    hqcan, hqs, hqsC, hQbirth, lt_min hδa hδb, lt_min hρa hρb, lt_min hζa hζb,
    lt_max_of_lt_left hDa, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδ hρ hΛδ K I p records hKB hrec hnc
  have hacc' := le_min_iff.mp hacc
  have hrad' := max_le_iff.mp hrad
  have hord' := max_le_iff.mp hord
  have hδ' := le_min_iff.mp hδ
  have hρ' := le_min_iff.mp hρ
  have hEst : NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad :=
    analytic p₀ δbound ρbound hacc'.1 hrad'.1 hord'.1 hδ'.1 hρ'.1 hΛδ
      K I p records hKB hrec hnc
  have hpinch := pinching K I p records
  refine ⟨hEst, ?_⟩
  intro t htop hbirth hne y hRy
  obtain ⟨-, -, hspat, hder, hgrad, hnct, -⟩ :=
    hEst.buffered_incoming_certificates hnc hpinch t (T := (t : ℝ)) le_rfl htop Q hcanQ hsQ
  obtain ⟨s, G, -, -, -, hG, hdG, hgG, -, -⟩ :=
    hEst.exists_outgoingSlab_of_lt_horizon t htop
  have hdGQ : G.DerivativeBoundBefore Ctime Q s :=
    fun z v hv hz => hdG z v hv (hcanQ.trans_lt hz)
  have hgGQ : G.GradientBoundBefore Cgrad Q s :=
    fun z v hv hz => hgG z v hv (hcanQ.trans_lt hz)
  exact birth p₀ δbound ρbound hacc'.2 hrad'.2 hord'.2 hδ'.2 hρ'.2 hΛδ
    K I p records hrec hpinch.1 hpinch.2 t htop hbirth hne hspat hder hgrad hnct
    s G hG hdGQ hgGQ y hRy

end GC.GeneralFlow
