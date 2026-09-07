import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.BasisHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set Bundle Manifold
open scoped Manifold ContDiff

private local instance euclideanMeasurableSpace (n : Nat) :
    MeasurableSpace (EuclideanSpace Real (Fin (n + 1))) := borel _
private local instance euclideanBorelSpace (n : Nat) :
    BorelSpace (EuclideanSpace Real (Fin (n + 1))) := ⟨rfl⟩

namespace EuclideanSpace

theorem measurePreserving_tail_prod_head (n : Nat) :
    MeasurePreserving
      (fun x : EuclideanSpace Real (Fin (n + 1)) => ((fun i : Fin n => x i.succ), x 0))
      volume ((volume : Measure (Fin n → Real)).prod volume) := by
  have hsplit := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Real) 0
  have hcoord : MeasurePreserving (EuclideanSpace.equiv (Fin (n + 1)) Real)
      volume (volume : Measure (Fin (n + 1) → Real)) := by
    refine ⟨(EuclideanSpace.equiv (Fin (n + 1)) Real).continuous.measurable, ?_⟩
    rw [← (EuclideanSpace.basisFun (Fin (n + 1)) Real).addHaar_eq_volume,
      Module.Basis.map_addHaar]
    have hb : (EuclideanSpace.basisFun (Fin (n + 1)) Real).toBasis.map
        (EuclideanSpace.equiv (Fin (n + 1)) Real).toLinearEquiv =
        Pi.basisFun Real (Fin (n + 1)) := by
      apply Module.Basis.eq_of_apply_eq
      intro i
      ext j
      simp [Pi.single_apply]
    rw [hb, Module.Basis.addHaar_def, Module.Basis.parallelepiped_basisFun,
      addHaarMeasure_eq_volume_pi]
  have hswap := MeasureTheory.Measure.measurePreserving_swap
    (μ := (volume : Measure Real)) (ν := (volume : Measure (Fin n → Real)))
  convert hswap.comp (hsplit.comp hcoord) using 1
  funext x
  rfl

theorem map_tail_prod_head_volume (n : Nat) :
    Measure.map
      (fun x : EuclideanSpace Real (Fin (n + 1)) => ((fun i : Fin n => x i.succ), x 0))
      volume = ((volume : Measure (Fin n → Real)).prod volume) :=
  (measurePreserving_tail_prod_head n).map_eq

end EuclideanSpace

namespace DifferentialGeometry.Analysis

private noncomputable def euclideanTailHead (n : Nat) :
    EuclideanSpace Real (Fin (n + 1)) ≃L[Real] ((Fin n → Real) × Real) :=
  (EuclideanSpace.equiv (Fin (n + 1)) Real).trans
    ((Fin.consEquivL Real (fun _ : Fin (n + 1) => Real)).symm.trans
      (ContinuousLinearEquiv.prodComm Real Real (Fin n → Real)))

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Integral.Measure

private local instance modelMeasurableSpace (V : Type*) [TopologicalSpace V] :
    MeasurableSpace V := borel V
private local instance modelBorelSpace (V : Type*) [TopologicalSpace V] :
    BorelSpace V := ⟨rfl⟩

theorem modelHaar_eq_det_smul_volume
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    (b : OrthonormalBasis (Fin (Module.finrank Real V)) Real V) :
    modelHaar (E := V) = ENNReal.ofReal |(chartModelBasis V).det b.toBasis| •
      (volume : Measure V) := by
  rw [← b.addHaar_eq_volume]
  exact ((chartModelBasis V).det_smul_addHaar b.toBasis).symm

theorem modelHaar_addHaarScalarFactor_eq_abs_det
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    (b : OrthonormalBasis (Fin (Module.finrank Real V)) Real V) :
    (MeasureTheory.Measure.addHaarScalarFactor (modelHaar (E := V)) volume : Real) =
      |(chartModelBasis V).det b.toBasis| := by
  have h : modelHaar (E := V) =
      Real.toNNReal |(chartModelBasis V).det b.toBasis| • (volume : Measure V) :=
    modelHaar_eq_det_smul_volume b
  simp only [h, MeasureTheory.Measure.addHaarScalarFactor_smul,
    MeasureTheory.Measure.addHaarScalarFactor_self, smul_eq_mul, mul_one,
    Real.coe_toNNReal _ (abs_nonneg _)]

theorem modelHaarScalarFactor_mul_sqrt_det_toMatrix
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    (B : LinearMap.BilinForm Real V)
    (b : OrthonormalBasis (Fin (Module.finrank Real V)) Real V) :
    (MeasureTheory.Measure.addHaarScalarFactor (modelHaar (E := V)) volume : Real) *
        Real.sqrt (LinearMap.BilinForm.toMatrix (chartModelBasis V) B).det =
      Real.sqrt (LinearMap.BilinForm.toMatrix b.toBasis B).det := by
  rw [modelHaar_addHaarScalarFactor_eq_abs_det b]
  exact (B.sqrt_det_toMatrix_basis_change (chartModelBasis V) b.toBasis).symm

theorem modelHaarScalarFactor_mul_chartDensity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (alpha x : M)
    (b : OrthonormalBasis (Fin (Module.finrank Real E)) Real E) :
    (MeasureTheory.Measure.addHaarScalarFactor (modelHaar (E := E)) volume : Real) *
        chartDensity g alpha x =
      Real.sqrt (Matrix.of fun i j => g.inner x
        ((trivializationAt E (TangentSpace I) alpha).symmL Real x (b i))
        ((trivializationAt E (TangentSpace I) alpha).symmL Real x (b j))).det := by
  let L := (trivializationAt E (TangentSpace I) alpha).symmL Real x
  let B := (g.inner x).toBilinForm.comp L.toLinearMap L.toLinearMap
  have h := modelHaarScalarFactor_mul_sqrt_det_toMatrix B b
  have hchart : LinearMap.BilinForm.toMatrix (chartModelBasis E) B =
      chartGramMatrix g alpha x := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, chartGramMatrix_apply]
    rfl
  rw [hchart] at h
  have horth : LinearMap.BilinForm.toMatrix b.toBasis B =
      Matrix.of (fun i j => g.inner x (L (b i)) (L (b j))) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  rw [horth] at h
  exact h

theorem map_tail_prod_head_modelHaar (n : Nat) :
    MeasureTheory.Measure.map
      (fun x : EuclideanSpace Real (Fin (n + 1)) => ((fun i : Fin n => x i.succ), x 0))
      (modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) =
      MeasureTheory.Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) volume •
        ((volume : Measure (Fin n → Real)).prod volume) := by
  conv_lhs =>
    rw [(modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).isAddLeftInvariant_eq_smul volume]
  rw [MeasureTheory.Measure.map_smul]
  congr 1
  exact EuclideanSpace.map_tail_prod_head_volume n

theorem map_tail_prod_head_modelHaar_restrict_half_space (n : Nat) (a : Real) :
    MeasureTheory.Measure.map
      (fun x : EuclideanSpace Real (Fin (n + 1)) => ((fun i : Fin n => x i.succ), x 0))
      ((modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict {x | a < x 0}) =
      MeasureTheory.Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) volume •
        ((volume : Measure (Fin n → Real)).prod (volume.restrict (Ioi a))) := by
  let f : EuclideanSpace Real (Fin (n + 1)) → (Fin n → Real) × Real :=
    fun x => ((fun i => x i.succ), x 0)
  have hf : Measurable f :=
    ((DifferentialGeometry.Analysis.euclideanTailHead n).continuous.measurable)
  have hs : MeasurableSet (univ ×ˢ Ioi a : Set ((Fin n → Real) × Real)) :=
    (isOpen_univ.prod isOpen_Ioi).measurableSet
  have hpre : f ⁻¹' (univ ×ˢ Ioi a) = {x | a < x 0} := by
    ext x
    simp [f]
  rw [← hpre, ← MeasureTheory.Measure.restrict_map hf hs]
  rw [map_tail_prod_head_modelHaar, MeasureTheory.Measure.restrict_smul,
    ← MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_univ]

theorem integral_modelHaar_half_space_eq_integral_prod
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (n : Nat) (a : Real) (f : EuclideanSpace Real (Fin (n + 1)) → F) :
    ∫ x in {x | a < x 0}, f x ∂(modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) =
      (MeasureTheory.Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin (n + 1))))) volume •
        ∫ p, f (WithLp.toLp 2 (Fin.cons p.2 p.1))
          ∂((volume : Measure (Fin n → Real)).prod (volume.restrict (Ioi a))) := by
  let e := DifferentialGeometry.Analysis.euclideanTailHead n
  have hmap := e.toHomeomorph.isClosedEmbedding.integral_map
    (μ := (modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict {x | a < x 0})
    (fun p => f (e.symm p))
  change (∫ p, f (e.symm p) ∂MeasureTheory.Measure.map
    (fun x : EuclideanSpace Real (Fin (n + 1)) => ((fun i => x i.succ), x 0))
    ((modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict {x | a < x 0})) =
      ∫ x in {x | a < x 0}, f (e.symm (e x))
        ∂(modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) at hmap
  simp only [e.symm_apply_apply] at hmap
  rw [map_tail_prod_head_modelHaar_restrict_half_space, integral_smul_nnreal_measure] at hmap
  exact hmap.symm

end DifferentialGeometry.Integral.Measure
