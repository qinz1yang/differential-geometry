import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLinearizedRefoldCoreIdentity
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLinearizedRefoldGridWindow
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerIntegral
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldFamilyJointSmoothness
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLieCovDerivFamily
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldEndoArmGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldCovDerivArmPairTrace
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance tensorRSNormedAddCommGroupOfRiemannianBundle
    (r s : ℕ) [Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace r s I y)]
      (x : M) :
    NormedAddCommGroup (Tensor0SBundle.TensorRSSpace r s I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => Tensor0SBundle.TensorRSSpace r s I y) x

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private theorem lrJoint0S_add_local {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (B p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private theorem lrJoint0S_smulFun_local {d : ℕ} {S : Set ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (A : ∀ p : M × ℝ, Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (f p.2 • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hfm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.2) :=
    hf.contMDiff.comp contMDiff_snd
  have hfj : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => f p.2) ((Set.univ : Set M) ×ˢ S) p₀ :=
    (hfm.contMDiffAt).contMDiffWithinAt
  refine (hfj.smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul (f p.2) (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      (f p₀.2) (A p₀)


omit [BoundarylessManifold I M] in
private lemma lrFamilyField_eq (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) (s : ℝ) :
    deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
      ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
        Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
        Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
      ![(-1 : ℝ), -1, 1] s =
      s • ((-1 : ℝ) • ((1 / 2 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                        (Equiv.swap (0 : Fin 4) 1)).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))))
        + (-1 : ℝ) • ((1 / 2 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    ((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                        Equiv.swap (0 : Fin 4) 1).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                          Equiv.swap (0 : Fin 4) 1).trans
                        (Equiv.swap (0 : Fin 4) 1)).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))))
        + (1 : ℝ) • ((1 / 2 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                        (Equiv.swap (0 : Fin 4) 1)).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))))) := by
  rw [deTurckLieCovDerivRefoldPairTraceFamily, Fin.sum_univ_three]
  rfl


private theorem lrFamily_threeArmHjoint (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
        ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
          Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
          Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
        ![(-1 : ℝ), -1, 1] s) (δ := δ) (δ' := δ) := by
  classical
  have hperY : ∀ (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) p.1
          ((show Tensor0SSpace 2 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 from
            (deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
              ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                  Equiv.swap (0 : Fin 4) 1,
                Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
              ![(-1 : ℝ), -1, 1] p.2).toSection p.1) (Y p.1)))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    intro Y
    have hbase : ∀ (X : SmoothCcTensor g₀ 2 6),
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
          (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
            (E := fun z : M => Tensor0SSpace 2 I z) q.1
            (cometricDoubleTraceFib (I := I)
              (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 2 q.1
              (cometricDoubleTraceFib (I := I)
                (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
                ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
                  X.toSection q.1) (Y q.1)))))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
      intro X
      have hXapp : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
          (fun x : M => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
            (E := fun z : M => Tensor0SSpace 6 I z) x
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
              X.toSection x) (Y x))) :=
        ContMDiff.clm_bundle_apply (b := id) X.toSection.contMDiff Y.contMDiff
      have hXjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
          (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
            (E := fun z : M => Tensor0SSpace 6 I z) q.1
            ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
              X.toSection q.1) (Y q.1)))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
        (hXapp.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
      have h4 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
        g₀ T 0 hδ hδZ
        (fun q : M × ℝ => (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
          X.toSection q.1) (Y q.1)) hXjoint
      exact cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2)
        g₀ T 0 hδ hδZ
        (fun q : M × ℝ => cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
            X.toSection q.1) (Y q.1))) h4
    have hP00 := hbase (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
    have hP01 := hbase (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
              (Equiv.swap (0 : Fin 4) 1)).trans
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
    have hP10 := hbase (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          ((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
              Equiv.swap (0 : Fin 4) 1).trans
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
    have hP11 := hbase (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1).trans
              (Equiv.swap (0 : Fin 4) 1)).trans
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
    have hP20 := hbase (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
    have hP21 := hbase (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
              (Equiv.swap (0 : Fin 4) 1)).trans
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
    have hA0 := lrJoint0S_add_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hP00 hP01
    have hH0 := lrJoint0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun _ : ℝ => (1 / 2 : ℝ)) contDiff_const _ hA0
    have hE0 := lrJoint0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun _ : ℝ => (-1 : ℝ)) contDiff_const _ hH0
    have hA1 := lrJoint0S_add_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hP10 hP11
    have hH1 := lrJoint0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun _ : ℝ => (1 / 2 : ℝ)) contDiff_const _ hA1
    have hE1 := lrJoint0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun _ : ℝ => (-1 : ℝ)) contDiff_const _ hH1
    have hA2 := lrJoint0S_add_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hP20 hP21
    have hH2 := lrJoint0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun _ : ℝ => (1 / 2 : ℝ)) contDiff_const _ hA2
    have hE2 := lrJoint0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun _ : ℝ => (1 : ℝ)) contDiff_const _ hH2
    have hZ01 := lrJoint0S_add_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hE0 hE1
    have hZ := lrJoint0S_add_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hZ01 hE2
    have hsmul := lrJoint0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun s : ℝ => s) contDiff_id _ hZ
    refine hsmul.congr (fun q _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SSpace 2 I z) q.1 t) ?_
    have hsmulY : ∀ (c : ℝ) (F : SmoothCcTensor g₀ 2 2),
        (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
          ((c • F).toSection q.1)) (Y q.1) =
        c • ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
          (F.toSection q.1)) (Y q.1)) := by
      intro c F
      rw [show ((c • F).toSection q.1) = c • (F.toSection q.1) from by
        rw [SmoothCcTensor.toSection_smul]; rfl]
      rfl
    have haddY : ∀ (F G : SmoothCcTensor g₀ 2 2),
        (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
          ((F + G).toSection q.1)) (Y q.1) =
        (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
            (F.toSection q.1)) (Y q.1)
          + (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
            (G.toSection q.1)) (Y q.1) := by
      intro F G
      rw [show ((F + G).toSection q.1) = F.toSection q.1 + G.toSection q.1 from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      rfl
    have hPY : ∀ (X : SmoothCcTensor g₀ 2 6),
        (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
            X).toSection q.1)) (Y q.1) =
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 2 q.1
          (cometricDoubleTraceFib (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
            ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
              X.toSection q.1) (Y q.1))) := by
      intro X
      rw [appCcRS_toSection]
      rfl
    rw [lrFamilyField_eq (I := I) (M := M) g₀ T hδ hδZ q.2]
    simp only [hsmulY, haddY, hPY]
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace 2 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 from
        (deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
          ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
            Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
              Equiv.swap (0 : Fin 4) 1,
            Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
          ![(-1 : ℝ), -1, 1] p.2).toSection p.1))
    (S := realizedSmallSet (δ := δ) (δ' := δ)) hperY
  refine hCLM.congr (fun p _ => ?_)
  rfl

private lemma lrWindowOneThree_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {B : ℝ}
    (hB1 : b 1 ≤ B) :
    Combinatorics.boundedFactorGridWindow b 1 3 ≤ 1 + B + B ^ 2 := by
  classical
  have hB0 : 0 ≤ B := le_trans (hb 1) hB1
  have hgrid0 : Combinatorics.boundedFactorGrid b 1 0 = 1 :=
    Combinatorics.boundedFactorGrid_zero b 1
  have hgrid1 : Combinatorics.boundedFactorGrid b 1 1 = b 1 := by
    rw [Combinatorics.boundedFactorGrid]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    rw [show Finset.Nat.antidiagonalTuple 0 1 = ∅ from
      Finset.Nat.antidiagonalTuple_zero_succ 0]
    rw [show Finset.Nat.antidiagonalTuple 1 1 = {![1]} from
      Finset.Nat.antidiagonalTuple_one 1]
    rw [Finset.filter_empty, Finset.sum_empty]
    rw [Finset.filter_singleton]
    rw [if_pos (by decide : ∀ m : Fin 1, (![1] : Fin 1 → ℕ) m ≤ 1)]
    rw [Finset.sum_singleton]
    rw [Fin.prod_univ_one]
    norm_num
  have hgrid2 : Combinatorics.boundedFactorGrid b 1 2 = b 1 * b 1 := by
    rw [Combinatorics.boundedFactorGrid]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [show Finset.Nat.antidiagonalTuple 0 2 = ∅ from
      Finset.Nat.antidiagonalTuple_zero_succ 1]
    rw [show Finset.Nat.antidiagonalTuple 1 2 = {![2]} from
      Finset.Nat.antidiagonalTuple_one 2]
    rw [Finset.filter_empty, Finset.sum_empty]
    rw [Finset.filter_singleton]
    rw [if_neg (by decide : ¬ ∀ m : Fin 1, (![2] : Fin 1 → ℕ) m ≤ 1)]
    rw [Finset.sum_empty]
    have h22 : (Finset.Nat.antidiagonalTuple 2 2).filter
        (fun e : Fin 2 → ℕ => ∀ m, e m ≤ 1) = {![1, 1]} := by
      decide
    rw [h22, Finset.sum_singleton, Fin.prod_univ_two]
    change (0 : ℝ) + 0 + b (![1, 1] 0) * b (![1, 1] 1) = b 1 * b 1
    norm_num
  rw [Combinatorics.boundedFactorGridWindow, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, hgrid0, hgrid1, hgrid2]
  nlinarith [hb 1, hB1, hB0, sq_nonneg (b 1 - B)]


theorem exists_deTurckLieCovDerivArm_basepointBackground_pairTraceResidual_order0_data
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
          (fun s => deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
            - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
              ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
                Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
              ![(-1 : ℝ), -1, 1] s) (δ := δ) (δ' := δ) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
              - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
                ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                  Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
                  Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
                ![(-1 : ℝ), -1, 1] s).toSection x) ≤ Λ ^ 2) ∧
        (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
              - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
                ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                  Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
                  Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
                ![(-1 : ℝ), -1, 1] s)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨Csob0, hCsob0_nn, hCsob0⟩ :=
    exists_sobolev_pointwise_bound_zero_order (I := I) (M := M) g₀ a ha_super
  obtain ⟨Csob1, hCsob1_nn, hCsob1⟩ :=
    exists_sobolev_pointwise_bound_first_order (I := I) (M := M) g₀ a ha_super
  have hΛ0_nn : (0 : ℝ) ≤ (Csob0 * R) ^ 2 := sq_nonneg _
  obtain ⟨C, hC_nn, hpt⟩ :=
    deTurckLieCovDerivArmDifferenceGridWindow (I := I) (M := M) g₀ ((Csob0 * R) ^ 2) hΛ0_nn hδ₁_lt
  obtain ⟨Kflat, hKflat_nn, hKflat⟩ :=
    boundedFactorGridWindow_integral_ballUniform_flat_allOrders (I := I) (M := M) g₀ a
      ha_super hR
  have hcap_nn : (0 : ℝ) ≤ C 0 * (1 + (Csob1 * R) ^ 2 + ((Csob1 * R) ^ 2) ^ 2) := by
    have := hC_nn 0
    positivity
  refine ⟨Real.sqrt (C 0 * (1 + (Csob1 * R) ^ 2 + ((Csob1 * R) ^ 2) ^ 2)),
    Real.sqrt_nonneg _,
    fun i => C i * Kflat i, fun i => mul_nonneg (hC_nn i) (hKflat_nn i), ?_⟩
  intro T hTsymm δ hδ_le hδ hδZ hball
  have hδ_le' : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
  have hT0 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) ≤
        (Csob0 * R) ^ 2 :=
    fun x => hCsob0 T hR hball x
  refine ⟨?_, ?_, ?_⟩
  · exact threeArmHjoint_sub_local (I := I) (M := M) g₀ _ _
      (covDerivArmField_realizedFam_threeArmHjoint (I := I) (M := M) g₀ T hδ hδZ g₀)
      (lrFamily_threeArmHjoint (I := I) (M := M) g₀ T hδ hδZ)
  · intro s hs x
    have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x T hδ
    have h0 := hpt T hTsymm hT0 hδ_le' hδ0 hδ hδZ hs 0 x
    rw [iteratedCovGrad_zero] at h0
    refine le_trans h0 ?_
    rw [Real.sq_sqrt hcap_nn]
    refine mul_le_mul_of_nonneg_left ?_ (hC_nn 0)
    have hb1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) ≤ (Csob1 * R) ^ 2 :=
      hCsob1 T hR hball x
    exact lrWindowOneThree_le
      (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
        ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x))
      (fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _)
      hb1
  · intro i s hs
    have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
    by_cases hM : Nonempty M
    · obtain ⟨x₀⟩ := hM
      have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x₀ T hδ
      have hptx : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
                  - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
                    ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                      Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                        Equiv.swap (0 : Fin 4) 1,
                      Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
                    ![(-1 : ℝ), -1, 1] s)).toSection x) ≤
            C i * Combinatorics.boundedFactorGridWindow
              (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
                ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x)) (i + 1) (i + 3) :=
        fun x => hpt T hTsymm hT0 hδ_le' hδ0 hδ hδZ hs i x
      obtain ⟨hWint, hWbound⟩ := hKflat T hball i
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        2 (2 + i)
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
            - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
              ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                  Equiv.swap (0 : Fin 4) 1,
                Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
              ![(-1 : ℝ), -1, 1] s))
        (fun x => C i * Combinatorics.boundedFactorGridWindow
          (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
            ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x)) (i + 1) (i + 3))
        (hWint.const_mul (C i)) hptx
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      refine le_trans (mul_le_mul_of_nonneg_left hWbound (hC_nn i)) (le_of_eq ?_)
      ring
    · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
      have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
            - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
              ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                  Equiv.swap (0 : Fin 4) 1,
                Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
              ![(-1 : ℝ), -1, 1] s)‖ = 0 :=
        bdNorm_zero_of_isEmpty (I := I) (M := M) g₀ 2 (2 + i) _
      rw [hz]
      have hK_nn : 0 ≤ C i * Kflat i := mul_nonneg (hC_nn i) (hKflat_nn i)
      nlinarith [hwin_nn, hK_nn]


theorem exists_deTurckLieCovDerivArm_basepointBackground_refold_identity_data
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∃ (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ), (∀ i, |ε i| ≤ 1) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ C0da : ℝ → SmoothCcTensor g₀ 2 2,
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0da (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            operatorFieldApply (I := I) (M := M) g₀ 2 2
                (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              operatorFieldApply (I := I) (M := M) g₀ 2 2 (C0da s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2
                  (deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0da s).toSection x) ≤
              Λ ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0da s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨Λ, hΛ_nn, K, hK_nn, hres⟩ :=
    exists_deTurckLieCovDerivArm_basepointBackground_pairTraceResidual_order0_data
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨Λ, hΛ_nn, K, hK_nn,
    ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
      Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
      Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3],
    ![(-1 : ℝ), -1, 1], ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  intro T hTsymm δ hδ_le hδ hδZ hball
  obtain ⟨hjoint, hcap, hwin⟩ := hres T hTsymm hδ_le hδ hδZ hball
  refine ⟨fun s => deTurckLieCovDerivArmField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
    - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
      ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
        Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
        Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
      ![(-1 : ℝ), -1, 1] s, hjoint, ?_, hcap, hwin⟩
  intro s hs
  beta_reduce
  simp only [iteratedCovGrad_zero]
  rw [appCc_sub_left,
    bdLiePairTraceFamily_appCc_eq_familySecondGradient (I := I) (M := M) g₀ T hδ hδZ
      ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
        Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
        Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
      ![(-1 : ℝ), -1, 1] s]
  abel


theorem exists_deTurckLieCovDerivArm_refold_identity_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∃ (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ), (∀ i, |ε i| ≤ 1) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ C0da : ℝ → SmoothCcTensor g₀ 2 2,
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0da (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            operatorFieldApply (I := I) (M := M) g₀ 2 2
                (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg)
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              operatorFieldApply (I := I) (M := M) g₀ 2 2 (C0da s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2
                  (deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0da s).toSection x) ≤
              Λ ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0da s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨Λv, hΛv_nn, Kv, hKv_nn, q, ε, hε, hmov⟩ :=
    exists_deTurckLieCovDerivArm_basepointBackground_refold_identity_data (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  obtain ⟨Λbg, hΛbg_nn, hsup_bg⟩ :=
    deTurckLieDLaCoeffField_realizedFam_rfns_order0_ballUniform (I := I) (M := M)
      g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λz, hΛz_nn, hsup_z⟩ :=
    deTurckLieDLaCoeffField_realizedFam_rfns_order0_ballUniform (I := I) (M := M)
      g₀ g₀ a ha_super hR hδ₀
  obtain ⟨Kd, hKd_nn, henv_d⟩ :=
    exists_deTurckLieCovDerivArm_backgroundDifference_l2JetWindow (I := I) (M := M)
      g₀ g_bg a ha_super hR hδ₀
  have hS_nn : (0 : ℝ) ≤ 2 * Λv ^ 2 + 2 * (2 * Λbg + 2 * Λz) := by positivity
  refine ⟨Real.sqrt (2 * Λv ^ 2 + 2 * (2 * Λbg + 2 * Λz)), Real.sqrt_nonneg _,
    fun i => 2 * Kv i + 2 * Kd i,
    fun i => by have h1 := hKv_nn i; have h2 := hKd_nn i; linarith,
    q, ε, hε, ?_⟩
  intro T hTsymm δ hδ_le hδ hδZ hball
  obtain ⟨C0v, hjv, hidv, hsupv, henvv⟩ := hmov T hTsymm hδ_le hδ hδZ hball
  have hZball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j hj
    have hzero : iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      have h := iteratedCovGrad_sub (I := I) (g := g₀) (r := 0) (s := 2) (j := j) T T
      rw [sub_self, sub_self] at h
      exact h
    rw [hzero, norm_zero]
    exact hR
  refine ⟨fun s => C0v s +
      (deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
        - deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀), ?_, ?_, ?_, ?_⟩
  · exact threeArmHjoint_add_local (I := I) (M := M) g₀ _ _ hjv
      (threeArmHjoint_sub_local (I := I) (M := M) g₀ _ _
        (covDerivArmField_realizedFam_threeArmHjoint (I := I) (M := M) g₀ T hδ hδZ g_bg)
        (covDerivArmField_realizedFam_threeArmHjoint (I := I) (M := M) g₀ T hδ hδZ g₀))
  · intro s hs
    have hsplit : deTurckLieCovDerivArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg =
        deTurckLieCovDerivArmField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ +
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
            - deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀) := by
      rw [add_sub_cancel]
    conv_lhs => rw [hsplit, appCc_add_left, hidv s hs]
    conv_rhs => rw [appCc_add_left]
    abel
  · intro s hs x
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg).toSection x) ≤ Λbg := by
      rw [covDerivArmField_eq_dLaCoeffField]
      exact hsup_bg T 0 hδ_le hδ hδ_le hδZ hball hZball s hs x
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀).toSection x) ≤ Λz := by
      rw [covDerivArmField_eq_dLaCoeffField]
      exact hsup_z T 0 hδ_le hδ hδ_le hδZ hball hZball s hs x
    have hdiff : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((deTurckLieCovDerivArmField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
          - deTurckLieCovDerivArmField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀).toSection x) ≤
        2 * Λbg + 2 * Λz := by
      rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
      refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 2 x _ _) ?_
      have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x
      linarith [h1, h2]
    have hsum : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (((fun s => C0v s +
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
            - deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)) s).toSection x) ≤
        2 * Λv ^ 2 + 2 * (2 * Λbg + 2 * Λz) := by
      rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x _ _) ?_
      have h3 := hsupv s hs x
      linarith [hdiff]
    rw [Real.sq_sqrt hS_nn]
    exact hsum
  · intro i s hs
    have hlin : iteratedCovGrad (I := I) g₀ 2 2 i
        (C0v s +
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
            - deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)) =
        iteratedCovGrad (I := I) g₀ 2 2 i (C0v s) +
          iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              - deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀) :=
      iteratedCovGrad_add (I := I) (g := g₀) (r := 2) (s := 2) (j := i) _ _
    have hv := henvv i s hs
    have hd := henv_d T hδ_le hδ hδZ hball i s hs
    have htri : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (C0v s +
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
            - deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀))‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0v s)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              - deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)‖ ^ 2 := by
      rw [hlin]
      have hn := norm_add_le (iteratedCovGrad (I := I) g₀ 2 2 i (C0v s))
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
            - deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀))
      nlinarith [mul_le_mul hn hn
          (norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i (C0v s) +
            iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
                - deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)))
          (add_nonneg (norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i (C0v s)))
            (norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
                - deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)))),
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i (C0v s)‖ -
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              - deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)‖)]
    refine le_trans htri ?_
    have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
    nlinarith [hv, hd, hwin_nn]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
