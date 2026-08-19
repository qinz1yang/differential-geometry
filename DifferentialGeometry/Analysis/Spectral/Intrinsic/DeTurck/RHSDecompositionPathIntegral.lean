import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSDecompositionArms
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrectionZeroJointSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MovingPairTrace
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnectionDifferenceUniformBounds

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle MeasureTheory intervalIntegral
open scoped BigOperators Manifold Topology ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem unitModel_add_app
    (g : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 (A + B) x v =
      unitModel (I := I) (M := M) g 2 A x v +
        unitModel (I := I) (M := M) g 2 B x v := by
  have hfun : unitModel (I := I) (M := M) g 2 (A + B) x =
      unitModel (I := I) (M := M) g 2 A x +
        unitModel (I := I) (M := M) g 2 B x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]
  rw [hfun, ContinuousMultilinearMap.add_apply]

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem unitModel_sub_app
    (g : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 (A - B) x v =
      unitModel (I := I) (M := M) g 2 A x v -
        unitModel (I := I) (M := M) g 2 B x v := by
  have hfun : unitModel (I := I) (M := M) g 2 (A - B) x =
      unitModel (I := I) (M := M) g 2 A x -
        unitModel (I := I) (M := M) g 2 B x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub]
  rw [hfun, ContinuousMultilinearMap.sub_apply]

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem threeArm_const
    (g : SmoothRiemannianMetric I M) {r : Nat}
    (A : SmoothCcTensor g r 2) {delta delta' : Real} :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun _ => A) (δ := delta) (δ' := delta') := by
  rw [linearizedRicciThreeArmHjoint]
  exact (A.toSection.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono
    (Set.subset_univ _)

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem threeArm_param_smul
    (g : SmoothRiemannianMetric I M) {r : Nat}
    (A : Real -> SmoothCcTensor g r 2) {delta delta' : Real}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g r A
      (δ := delta) (δ' := delta')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun t => t • A t) (δ := delta) (δ' := delta') := by
  rw [linearizedRicciThreeArmHjoint] at hA ⊢
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) r 2
  intro p hp
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x := p.1 with hx
  set e := trivializationAt (TensorRSModel r 2 Real E)
    (fun z : M => TensorRSSpace r 2 I z) x with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace
    (F := TensorRSModel r 2 Real E)
    (E := fun z : M => TensorRSSpace r 2 I z)).mp (hA p hp)
  refine (contMDiffWithinAt_snd.smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ q : M × Real in
        nhdsWithin p ((Set.univ : Set M) ×ˢ
          metricPerturbationPathDomain (δ := delta) (δ' := delta')),
        q.1 ∈ e.baseSet :=
      (continuousWithinAt_fst
        (s := (Set.univ : Set M) ×ˢ
          metricPerturbationPathDomain (δ := delta) (δ' := delta'))
        (p := p))
        (e.open_baseSet.mem_nhds (by
          rw [he]
          exact mem_baseSet_trivializationAt _ _ x))
    filter_upwards [hbase] with q hq
    exact (e.linear Real hq).map_smul q.2 ((A q.2).toSection q.1)
  · exact (e.linear Real (by
      rw [he, ← hx]
      exact mem_baseSet_trivializationAt _ _ x)).map_smul
        p.2 ((A p.2).toSection p.1)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem threeArm_comp
    (g : SmoothRiemannianMetric I M) (a b : Nat)
    (A : Real -> SmoothCcTensor g b 2) (B : SmoothCcTensor g a b)
    {delta delta' : Real}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g b A
      (δ := delta) (δ' := delta')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g a
      (fun t => ccOperatorFieldComp (I := I) (M := M) g a b 2 (A t) B)
      (δ := delta) (δ' := delta') := by
  rw [linearizedRicciThreeArmHjoint] at hA ⊢
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel a Real E)
    (V₁ := fun x : M => Tensor0SSpace a I x)
    (F₂ := Tensor0SModel 2 Real E)
    (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × Real =>
      (show Tensor0SSpace a I p.1 →L[Real] Tensor0SSpace 2 I p.1 from
        (ccOperatorFieldComp (I := I) (M := M) g a b 2 (A p.2) B).toSection p.1))
    (S := metricPerturbationPathDomain (δ := delta) (δ' := delta'))
  intro Y
  have hBY0 : ContMDiff I (I.prod 𝓘(Real, Tensor0SModel b Real E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel b Real E)
        (E := fun z : M => Tensor0SSpace b I z) x
        ((show Tensor0SSpace a I x →L[Real] Tensor0SSpace b I x from
          B.toSection x) (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id) B.toSection.contMDiff Y.contMDiff
  have hBY : ContMDiffOn (I.prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Tensor0SModel b Real E)) ∞
      (fun p : M × Real => TotalSpace.mk' (Tensor0SModel b Real E)
        (E := fun z : M => Tensor0SSpace b I z) p.1
        ((show Tensor0SSpace a I p.1 →L[Real] Tensor0SSpace b I p.1 from
          B.toSection p.1) (Y p.1)))
      ((Set.univ : Set M) ×ˢ
        metricPerturbationPathDomain (δ := delta) (δ' := delta')) :=
    (hBY0.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
  have happ := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hA hBY
  refine happ.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 Real E)
    (E := fun z : M => Tensor0SSpace 2 I z) p.1 t) ?_
  rw [operatorFieldComposition_toSection]
  rfl

private theorem movingMetricPairTraceOperator_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 6
      (fun t => movingMetricPairTraceOperator (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ t))
      (δ := delta) (δ' := delta) := by
  rw [linearizedRicciThreeArmHjoint]
  have hCLM := contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 6 Real E)
    (V₁ := fun x : M => Tensor0SSpace 6 I x)
    (F₂ := Tensor0SModel 2 Real E)
    (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × Real =>
      (show Tensor0SSpace 6 I p.1 →L[Real] Tensor0SSpace 2 I p.1 from
        (movingMetricPairTraceOperator (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ p.2)).toSection p.1))
    (S := metricPerturbationPathDomain (δ := delta) (δ' := delta))
    (fun Y => by
      have hY : ContMDiffOn (I.prod 𝓘(Real, Real))
          (I.prod 𝓘(Real, Tensor0SModel 6 Real E)) ∞
          (fun p : M × Real => TotalSpace.mk' (Tensor0SModel 6 Real E)
            (E := fun z : M => Tensor0SSpace 6 I z) p.1 (Y p.1))
          ((Set.univ : Set M) ×ˢ
            metricPerturbationPathDomain (δ := delta) (δ' := delta)) :=
        Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
      have h4 := cometricDoubleTraceFib_metricPerturbationPath_jointContMDiffOn
        (I := I) (p := 4) g T 0 hdelta hdeltaZ
        (fun p : M × Real => Y p.1) hY
      have h2 := cometricDoubleTraceFib_metricPerturbationPath_jointContMDiffOn
        (I := I) (p := 2) g T 0 hdelta hdeltaZ
        (fun p : M × Real =>
          cometricDoubleTraceFib (I := I)
            (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ p.2) 4 p.1
            (Y p.1)) h4
      refine h2.congr (fun p _ => ?_)
      refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun z : M => Tensor0SSpace 2 I z) p.1 t) ?_
      rfl)
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel 6 2 Real E)
    (E := fun z : M => TensorRSSpace 6 2 I z) p.1 t) ?_
  rfl

theorem edgePairMono_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (G : SmoothCcTensor g 0 4) (sigma : Equiv.Perm (Fin 4)) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => topOrderPairingCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ t) G sigma)
      (δ := delta) (δ' := delta) := by
  have h := threeArm_comp (I := I) (M := M) g 2 6
    (fun t => movingMetricPairTraceOperator (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ t))
    (rsDomDomCongrSection (I := I) (M := M) g 2 6 movingMetricPairTracePermutation
      (slotExtendTwo (I := I) (M := M) g
        (domDomCongrSection (I := I) g
          (sigma.trans (Equiv.swap (0 : Fin 4) 2 *
            Equiv.swap (1 : Fin 4) 3)) G)))
    (movingMetricPairTraceOperator_joint (I := I) (M := M) g T hdelta hdeltaZ)
  simpa only [topOrderPairingCoefficient] using h

theorem edgeLiePair_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (q : Fin 3 -> Equiv.Perm (Fin 4)) (epsilon : Fin 3 -> Real) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hdelta hdeltaZ q epsilon)
      (δ := delta) (δ' := delta) := by
  let G := iteratedCovGrad (I := I) g 0 2 2 T
  have hmono : ∀ sigma : Equiv.Perm (Fin 4),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
        (fun t => topOrderPairingCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ t) G sigma)
        (δ := delta) (δ' := delta) :=
    fun sigma => edgePairMono_joint (I := I) (M := M)
      g T hdelta hdeltaZ G sigma
  have hterm : ∀ i : Fin 3,
      linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
        (fun t => epsilon i • ((1 / 2 : Real) •
          (topOrderPairingCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ t) G (q i) +
            topOrderPairingCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ t) G
              ((q i).trans (Equiv.swap (0 : Fin 4) 1)))))
        (δ := delta) (δ' := delta) := by
    intro i
    exact threeArmJoint_smul (I := I) (M := M) g (epsilon i) _
      (threeArmJoint_smul (I := I) (M := M) g (1 / 2 : Real) _
        (threeArmJoint_add (I := I) (M := M) g _ _
          (hmono (q i))
          (hmono ((q i).trans (Equiv.swap (0 : Fin 4) 1)))))
  have hsum := threeArmJoint_add (I := I) (M := M) g _ _
    (threeArmJoint_add (I := I) (M := M) g _ _ (hterm 0) (hterm 1))
    (hterm 2)
  have hscaled := threeArm_param_smul (I := I) (M := M) g _ hsum
  change linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
    (fun t => t • ∑ i : Fin 3, epsilon i • ((1 / 2 : Real) •
      (topOrderPairingCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ t) G (q i) +
        topOrderPairingCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ t) G
          ((q i).trans (Equiv.swap (0 : Fin 4) 1)))))
      (δ := delta) (δ' := delta)
  simpa only [Fin.sum_univ_three] using hscaled

private theorem ricciHalf_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ricciPalatiniHalfCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ t))
      (δ := delta) (δ' := delta) := by
  have hconn :=
    linearizedRicciConnectionDifferenceOrder0Coeff_jointContMDiffOn_smallPerturbationSet
      (I := I) (M := M) g T 0 hdelta hdeltaZ
  have hriem : linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ricciArmOrder0RiemannCoeff (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ t))
      (δ := delta) (δ' := delta) := by
    rw [linearizedRicciThreeArmHjoint]
    exact ricciArmOrder0RiemannCoeff_metricPerturbationPath_jointContMDiff
      (I := I) (M := M) g T 0 hdelta hdeltaZ
  have hsum := threeArmJoint_add (I := I) (M := M) g _ _ hconn
    (threeArmJoint_smul (I := I) (M := M) g (1 / 2 : Real) _ hriem)
  simpa only [ricciPalatiniHalfCoefficient, linearizedRicciConnectionDifferenceOrder0Coeff] using hsum

private theorem ricciDecomposition0_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ricciDecomposition0 (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ t) (t • T))
      (δ := delta) (δ' := delta) := by
  have hriem := threeArm_const (I := I) (M := M) g
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g g)
    (delta := delta) (delta' := delta)
  have hAA :=
    ricciArmOrder0AACommCoeffField_metricPerturbationPath_threeArmHjoint
      (I := I) (M := M) g T hdelta hdeltaZ
  have hBackground :=
    ricciArmOrder0BackgroundRCommCoeffField_metricPerturbationPath_threeArmHjoint
      (I := I) (M := M) g T hdelta hdeltaZ
  have hBackground0 := threeArm_const (I := I) (M := M) g
    (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g g)
    (delta := delta) (delta' := delta)
  have hBackgroundDiff := threeArmJoint_sub (I := I) (M := M) g _ _ hBackground hBackground0
  have hSwap := threeArm_comp (I := I) (M := M) g 2 2 _
    (ccSlotSwapField (I := I) (M := M) g) hBackgroundDiff
  have hSharp :=
    ricciArmSharpGradKoszulResidualField_metricPerturbationPath_threeArmHjoint
      (I := I) (M := M) g T hdelta hdeltaZ
  have hFold :=
    ricciArmRicciFoldRemainderField_metricPerturbationPath_threeArmHjoint
      (I := I) (M := M) g T hdelta hdeltaZ
  have htail := threeArmJoint_sub (I := I) (M := M) g _ _
    (threeArmJoint_add (I := I) (M := M) g _ _ hSwap
      (threeArmJoint_smul (I := I) (M := M) g (1 / 2 : Real) _ hSharp))
    hFold
  have hinner := threeArmJoint_add (I := I) (M := M) g _ _ hAA htail
  have hall := threeArmJoint_add (I := I) (M := M) g _ _ hriem
    (threeArmJoint_smul (I := I) (M := M) g (2 : Real) _ hinner)
  simpa only [ricciDecomposition0] using hall

private theorem covDeriv_joint
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ t) g_bg)
      (δ := delta) (δ' := delta) := by
  rw [linearizedRicciThreeArmHjoint]
  exact (deTurckLieConnectionDifferenceDerivativeBiContrFib_metricPerturbationPath_jointContMDiffOn
    (I := I) (M := M) g T 0 hdelta hdeltaZ g_bg).congr
      (fun p _ => by rfl)

private theorem endo_joint
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => deTurckLieEndoArmField (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ t) g_bg)
      (δ := delta) (δ' := delta) := by
  have hall := deTurckLieCoeffField_metricPerturbationPath_jointSmooth
    (I := I) (M := M) g T 0 hdelta hdeltaZ g_bg
  have hcov := covDeriv_joint (I := I) (M := M)
    g g_bg T hdelta hdeltaZ
  have hsub := threeArmJoint_sub (I := I) (M := M) g _ _ hall hcov
  simpa only [deTurckLieCoeffField_eq_covDerivArm_add_endoArm,
    add_sub_cancel_left] using hsub

theorem lieDecomposition_joint
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => lieDecomposition0 (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ t) g_bg
        T hdelta hdeltaZ t)
      (δ := delta) (δ' := delta) := by
  exact threeArmJoint_sub (I := I) (M := M) g _ _
    (covDeriv_joint (I := I) (M := M) g g_bg T hdelta hdeltaZ)
    (edgeLiePair_joint (I := I) (M := M)
      g T hdelta hdeltaZ lieDecompositionQ lieDecompositionEps)

theorem rhsDecomposition0_joint
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (rhsDecomposition0 (I := I) (M := M) g g_bg T hdelta hdeltaZ)
      (δ := delta) (δ' := delta) := by
  have hRicci := ricciHalf_joint (I := I) (M := M)
    g T hdelta hdeltaZ
  have hDecomposition := ricciDecomposition0_joint (I := I) (M := M)
    g T hdelta hdeltaZ
  have hLie := lieDecomposition_joint (I := I) (M := M)
    g g_bg T hdelta hdeltaZ
  have hEndo := endo_joint (I := I) (M := M)
    g g_bg T hdelta hdeltaZ
  have hCorr := lieCorrectionZero_path_joint (I := I) (M := M)
    g T 0 hdelta hdeltaZ g_bg
  have hhead := threeArmJoint_add (I := I) (M := M) g _ _
    (threeArmJoint_smul (I := I) (M := M) g (-2 : Real) _ hRicci)
    hDecomposition
  have htail := threeArmJoint_add (I := I) (M := M) g _ _
    (threeArmJoint_add (I := I) (M := M) g _ _ hLie hEndo) hCorr
  have hall := threeArmJoint_add (I := I) (M := M) g _ _ hhead htail
  simpa only [rhsDecomposition0] using hall

def rhsDecomposition0Int
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) :
    SmoothCcTensor g 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 2 2
    (rhsDecomposition0 (I := I) (M := M) g g_bg T hdelta hdeltaZ)
    (metricPerturbationPathDomain (δ := delta) (δ' := delta)) metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hdelta_lt hdelta_lt)
    (rhsDecomposition0_joint (I := I) (M := M) g g_bg T hdelta hdeltaZ)

def rhsDecompositionTopInt
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) :
    SmoothCcTensor g 4 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 4 2
    (rhsDecompositionTop (I := I) (M := M) g g_bg T hdelta hdeltaZ)
    (metricPerturbationPathDomain (δ := delta) (δ' := delta)) metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hdelta_lt hdelta_lt)
    (rhsDecompositionTop_joint (I := I) (M := M) g g_bg T
      hdelta_lt hdelta hdeltaZ)

theorem rhs_sub_zero_decomposition
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) :
    deTurckRHSAtMetricPerturbation (I := I) g g_bg T hdelta_lt hdelta -
        deTurckRHSAtMetricPerturbation (I := I) g g_bg 0 hdelta_lt hdeltaZ =
      operatorFieldApply (I := I) (M := M) g 2 2
          (rhsDecomposition0Int (I := I) (M := M) g g_bg T
            hdelta_lt hdelta hdeltaZ) T +
        operatorFieldApply (I := I) (M := M) g 3 2
          (ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g g_bg T 0
            hdelta_lt hdelta hdelta_lt hdeltaZ)
          (iteratedCovGrad (I := I) g 0 2 1 T) +
        operatorFieldApply (I := I) (M := M) g 4 2
          (rhsDecompositionTopInt (I := I) (M := M) g g_bg T
            hdelta_lt hdelta hdeltaZ)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  classical
  have hSI : Set.uIcc (0 : Real) 1 ⊆
      metricPerturbationPathDomain (δ := delta) (δ' := delta) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hdelta_lt hdelta_lt
  have hSopen : IsOpen (metricPerturbationPathDomain (δ := delta) (δ' := delta)) :=
    metricPerturbationPathDomain_isOpen
  set Psi0 : Real → SmoothCcTensor g 2 2 := fun s =>
    rhsDecomposition0 (I := I) (M := M) g g_bg T hdelta hdeltaZ s with hPsi0def
  set Psi1 : Real → SmoothCcTensor g 3 2 := fun s =>
    ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g_bg T 0 hdelta hdeltaZ s with hPsi1def
  set Psi2 : Real → SmoothCcTensor g 4 2 := fun s =>
    rhsDecompositionTop (I := I) (M := M) g g_bg T hdelta hdeltaZ s with hPsi2def
  have hj0 : linearizedRicciThreeArmHjoint (I := I) (M := M) g 2 Psi0
      (δ := delta) (δ' := delta) := by
    rw [hPsi0def]
    exact rhsDecomposition0_joint (I := I) (M := M)
      g g_bg T hdelta hdeltaZ
  have hj1 : linearizedRicciThreeArmHjoint (I := I) (M := M) g 3 Psi1
      (δ := delta) (δ' := delta) := by
    rw [hPsi1def]
    exact ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M)
      g g_bg T 0 hdelta hdeltaZ
  have hj2 : linearizedRicciThreeArmHjoint (I := I) (M := M) g 4 Psi2
      (δ := delta) (δ' := delta) := by
    rw [hPsi2def]
    exact rhsDecompositionTop_joint (I := I) (M := M)
      g g_bg T hdelta_lt hdelta hdeltaZ
  have hc0 : ∀ x : M, ContinuousOn (fun t : Real =>
      TensorRSSpace.toModel ((Psi0 t).toSection x))
      (metricPerturbationPathDomain (δ := delta) (δ' := delta)) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g 2 2 Psi0
      (metricPerturbationPathDomain (δ := delta) (δ' := delta)) hj0 x
  have hc1 : ∀ x : M, ContinuousOn (fun t : Real =>
      TensorRSSpace.toModel ((Psi1 t).toSection x))
      (metricPerturbationPathDomain (δ := delta) (δ' := delta)) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g 3 2 Psi1
      (metricPerturbationPathDomain (δ := delta) (δ' := delta)) hj1 x
  have hc2 : ∀ x : M, ContinuousOn (fun t : Real =>
      TensorRSSpace.toModel ((Psi2 t).toSection x))
      (metricPerturbationPathDomain (δ := delta) (δ' := delta)) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g 4 2 Psi2
      (metricPerturbationPathDomain (δ := delta) (δ' := delta)) hj2 x
  have hPi0 : rhsDecomposition0Int (I := I) (M := M) g g_bg T
      hdelta_lt hdelta hdeltaZ =
      pathIntegralCoeffField (I := I) (M := M) g 2 2 Psi0
        (metricPerturbationPathDomain (δ := delta) (δ' := delta))
        hSopen hSI hj0 := rfl
  have hPi1 : ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g g_bg T 0
      hdelta_lt hdelta hdelta_lt hdeltaZ =
      pathIntegralCoeffField (I := I) (M := M) g 3 2 Psi1
        (metricPerturbationPathDomain (δ := delta) (δ' := delta))
        hSopen hSI hj1 := rfl
  have hPi2 : rhsDecompositionTopInt (I := I) (M := M) g g_bg T
      hdelta_lt hdelta hdeltaZ =
      pathIntegralCoeffField (I := I) (M := M) g 4 2 Psi2
        (metricPerturbationPathDomain (δ := delta) (δ' := delta))
        hSopen hSI hj2 := rfl
  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, unitModel_sub_app]
  rw [← rhs_chart_sum_one (I := I) g g_bg T 0
      hdelta_lt hdelta hdelta_lt hdeltaZ x,
    ← rhs_chart_sum_zero (I := I) g g_bg T 0
      hdelta_lt hdelta hdelta_lt hdeltaZ x]
  rw [rhsSum_sub_eq_int (I := I) g g_bg T 0
    hdelta_lt hdelta hdelta_lt hdeltaZ x]
  have hI0 : IntervalIntegrable (fun s : Real =>
      unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2 (Psi0 s) T) x ![v 0, v 1])
      volume 0 1 :=
    coeffApp_integrable (I := I) (M := M) g 2 2 Psi0 T
      (metricPerturbationPathDomain (δ := delta) (δ' := delta)) hSI hc0 x ![v 0, v 1]
  have hI1 : IntervalIntegrable (fun s : Real =>
      unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 3 2 (Psi1 s)
          (iteratedCovGrad (I := I) g 0 2 1 T)) x ![v 0, v 1])
      volume 0 1 :=
    coeffApp_integrable (I := I) (M := M) g 3 2 Psi1
      (iteratedCovGrad (I := I) g 0 2 1 T)
      (metricPerturbationPathDomain (δ := delta) (δ' := delta)) hSI hc1 x ![v 0, v 1]
  have hI2 : IntervalIntegrable (fun s : Real =>
      unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 4 2 (Psi2 s)
          (iteratedCovGrad (I := I) g 0 2 2 T)) x ![v 0, v 1])
      volume 0 1 :=
    coeffApp_integrable (I := I) (M := M) g 4 2 Psi2
      (iteratedCovGrad (I := I) g 0 2 2 T)
      (metricPerturbationPathDomain (δ := delta) (δ' := delta)) hSI hc2 x ![v 0, v 1]
  have hintegrand : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : Real) 1 →
      rhsSumSlope (I := I) g g_bg T 0 hdelta_lt hdelta
          hdelta_lt hdeltaZ x (v 0) (v 1) s =
        unitModel (I := I) (M := M) g 2
            (operatorFieldApply (I := I) (M := M) g 2 2 (Psi0 s) T) x ![v 0, v 1] +
          unitModel (I := I) (M := M) g 2
            (operatorFieldApply (I := I) (M := M) g 3 2 (Psi1 s)
              (iteratedCovGrad (I := I) g 0 2 1 T)) x ![v 0, v 1] +
          unitModel (I := I) (M := M) g 2
            (operatorFieldApply (I := I) (M := M) g 4 2 (Psi2 s)
              (iteratedCovGrad (I := I) g 0 2 2 T)) x ![v 0, v 1] := by
    rw [MeasureTheory.ae_iff]
    have hnull : volume ({1} : Set Real) = 0 := by simp
    refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
    rw [Set.mem_setOf_eq, Classical.not_imp] at hs
    obtain ⟨hsmem, hsneq⟩ := hs
    rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at hsmem
    rw [Set.mem_singleton_iff]
    by_contra hne
    have hsIoo : s ∈ Set.Ioo (0 : Real) 1 :=
      ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hne⟩
    refine hsneq ?_
    simpa only [hPsi0def, hPsi1def, hPsi2def, unitModel_add_app] using
      rhsSlope_decomposition (I := I) (M := M) g g_bg T hTsymm
        hdelta_lt hdelta hdeltaZ x (v 0) (v 1) hsIoo
  rw [intervalIntegral.integral_congr_ae hintegrand]
  rw [intervalIntegral.integral_add (hI0.add hI1) hI2,
    intervalIntegral.integral_add hI0 hI1]
  rw [unitModel_add_app, unitModel_add_app, hPi0, hPi1, hPi2]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq (I := I) (M := M) g 2 2 Psi0 T
      (metricPerturbationPathDomain (δ := delta) (δ' := delta)) hSopen hSI hj0 hc0,
    pathIntegralCoeffField_operatorFieldApplication_eq (I := I) (M := M) g 3 2 Psi1
      (iteratedCovGrad (I := I) g 0 2 1 T)
      (metricPerturbationPathDomain (δ := delta) (δ' := delta)) hSopen hSI hj1 hc1,
    pathIntegralCoeffField_operatorFieldApplication_eq (I := I) (M := M) g 4 2 Psi2
      (iteratedCovGrad (I := I) g 0 2 2 T)
      (metricPerturbationPathDomain (δ := delta) (δ' := delta)) hSopen hSI hj2 hc2]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
