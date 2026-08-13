import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyPair
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivTimeDeriv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivArityBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvBridge
import DifferentialGeometry.Geometry.Connection.LeviCivita.Uniqueness
import Mathlib.Topology.Instances.Matrix
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle

open DifferentialGeometry.Coordinates
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

omit [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem derivNorm_pair_cont
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {t : Real} (ht : t ∈ D.regular) (x₀ : M) (a : ℕ)
    (hc : ∀ slots : Fin (a + 2) →
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      ContinuousAt
        (fun p : (Real × Real) × M ↦
          metricDiffCovDerivAt (I := I) a
              (g_fam p.1.2) (g_fam p.1.1) (g_fam p.1.1) p.2
            (fun j ↦
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt
                (I := I) x₀ (slots j) p.2))
        ((t, t), x₀)) :
    ContinuousAt
      (fun p : (Real × Real) × M ↦
        metricDerivNorm (I := I) a
          (g_fam p.1.2) (g_fam p.1.1) (g_fam p.1.1) p.2)
      ((t, t), x₀) := by
  classical
  let Idx :=
    DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E
  let frame : Idx → (x : M) → TangentSpace I x :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀
  let U := DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x₀
  have hxU : x₀ ∈ U := by
    simpa [U] using
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x₀
  have hUo : IsOpen U := by
    simpa [U] using
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open (I := I) x₀
  have hframe :
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame U := by
    simpa [frame, U] using
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame
        (I := I) x₀
  let Gm : (Real × Real) × M → Matrix Idx Idx Real :=
    fun p ↦ Matrix.of fun i j ↦
      (g_fam p.1.1).inner p.2 (frame i p.2) (frame j p.2)
  have hGmEnt (i j : Idx) :
      ContinuousAt (fun p : (Real × Real) × M ↦ Gm p i j) ((t, t), x₀) := by
    have hs := (hG.frameCompSmooth frame hframe i j).contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds ht) (hUo.mem_nhds hxU))
    have hm : ContinuousAt
        (fun p : (Real × Real) × M ↦ (p.1.1, p.2))
        ((t, t), x₀) :=
      (continuousAt_fst.fst.prodMk continuousAt_snd)
    exact ContinuousAt.comp'
      (f := fun p : (Real × Real) × M ↦ (p.1.1, p.2))
      (g := fun q : Real × M ↦
        (g_fam q.1).inner q.2 (frame i q.2) (frame j q.2))
      hs.continuousAt hm
  have hGmc : ContinuousAt Gm ((t, t), x₀) :=
    continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ hGmEnt i j
  have hdetne : ∀ p, p.2 ∈ U → (Gm p).det ≠ 0 := by
    intro p hp hdet0
    obtain ⟨c, hc0, hcv⟩ :=
      (Matrix.exists_mulVec_eq_zero_iff (M := Gm p)).2 hdet0
    let basis := hframe.toBasisAt hp
    let w : TangentSpace I p.2 := ∑ i, c i • basis i
    have hrow0 : ∀ i, (g_fam p.1.1).inner p.2 (basis i) w = 0 := by
      intro i
      have hsum : (g_fam p.1.1).inner p.2 (basis i) w =
          ∑ j, Gm p i j * c j := by
        simp only [w, map_sum, map_smul, smul_eq_mul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [Gm, Matrix.of_apply, basis, IsLocalFrameOn.toBasisAt_coe]
        ring
      rw [hsum]
      simpa [Matrix.mulVec, dotProduct] using congrFun hcv i
    have hinner : (g_fam p.1.1).inner p.2 w w = 0 := by
      have hw_sum : w = ∑ i, c i • basis i := rfl
      calc
        (g_fam p.1.1).inner p.2 w w =
            (g_fam p.1.1).inner p.2 w (∑ i, c i • basis i) :=
          congrArg ((g_fam p.1.1).inner p.2 w) hw_sum
        _ = ∑ i, c i * (g_fam p.1.1).inner p.2 w (basis i) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]
        _ = ∑ i, c i * (g_fam p.1.1).inner p.2 (basis i) w := by
          exact Finset.sum_congr rfl fun i _ ↦ by
            rw [(g_fam p.1.1).symm p.2 w (basis i)]
        _ = 0 := Finset.sum_eq_zero fun i _ ↦ by rw [hrow0 i, mul_zero]
    have hwne : w ≠ 0 := by
      intro hw
      apply hc0
      have hall := Fintype.linearIndependent_iff.1 basis.linearIndependent c
        (by simpa [w] using hw)
      exact funext hall
    exact absurd hinner (ne_of_gt ((g_fam p.1.1).pos p.2 w hwne))
  have hGinvc : ContinuousAt (fun p ↦ (Gm p)⁻¹) ((t, t), x₀) := by
    have hdetc : ContinuousAt (fun p ↦ (Gm p).det) ((t, t), x₀) :=
      (continuous_id.matrix_det).continuousAt.comp hGmc
    have hadjc : ContinuousAt (fun p ↦ (Gm p).adjugate) ((t, t), x₀) :=
      (continuous_id.matrix_adjugate).continuousAt.comp hGmc
    have hmain := (hdetc.inv₀ (hdetne ((t, t), x₀) hxU)).smul hadjc
    simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using hmain
  have hGinvEnt (i j : Idx) :
      ContinuousAt (fun p ↦ (Gm p)⁻¹ i j) ((t, t), x₀) :=
    continuousAt_pi.1 (continuousAt_pi.1 hGinvc i) j
  let q : (Real × Real) × M → Real := fun p ↦
    ∑ I₀ : Fin (a + 2) → Idx, ∑ J₀ : Fin (a + 2) → Idx,
      (∏ z : Fin (a + 2), (Gm p)⁻¹ (I₀ z) (J₀ z)) *
        metricDiffCovDerivAt (I := I) a
            (g_fam p.1.2) (g_fam p.1.1) (g_fam p.1.1) p.2
          (fun z ↦ frame (I₀ z) p.2) *
        metricDiffCovDerivAt (I := I) a
            (g_fam p.1.2) (g_fam p.1.1) (g_fam p.1.1) p.2
          (fun z ↦ frame (J₀ z) p.2)
  have hq : ContinuousAt q ((t, t), x₀) := by
    refine tendsto_finset_sum _ fun I₀ _ ↦ tendsto_finset_sum _ fun J₀ _ ↦ ?_
    have hp : ContinuousAt
        (fun p ↦ ∏ z : Fin (a + 2), (Gm p)⁻¹ (I₀ z) (J₀ z))
        ((t, t), x₀) :=
      tendsto_finset_prod _ fun z _ ↦ hGinvEnt (I₀ z) (J₀ z)
    exact (hp.mul (by simpa [frame, Idx] using hc I₀)).mul
      (by simpa [frame, Idx] using hc J₀)
  have heq :
      (fun p : (Real × Real) × M ↦
        metricDerivNorm (I := I) a
          (g_fam p.1.2) (g_fam p.1.1) (g_fam p.1.1) p.2) =ᶠ[𝓝 ((t, t), x₀)]
        fun p ↦ Real.sqrt (q p) := by
    have hregN : ((D.regular ×ˢ D.regular) ×ˢ U) ∈
        𝓝 ((t, t), x₀) :=
      prod_mem_nhds
        (prod_mem_nhds (D.regular_isOpen.mem_nhds ht)
          (D.regular_isOpen.mem_nhds ht))
        (hUo.mem_nhds hxU)
    filter_upwards [hregN] with p hp
    let basis := hframe.toBasisAt hp.2
    have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I)
        (g_fam p.1.1) p.2 basis (fun i j ↦ (Gm p)⁻¹ i j) := by
      have hunit : IsUnit (Gm p).det := isUnit_iff_ne_zero.2 (hdetne p hp.2)
      intro i j
      have hGb (r s : Idx) :
          (g_fam p.1.1).inner p.2 (basis r) (basis s) = Gm p r s := by
        simp [basis, Gm, IsLocalFrameOn.toBasisAt_coe]
      constructor
      · rw [Finset.sum_congr rfl fun k _ ↦ by rw [hGb k j],
          ← Matrix.mul_apply, Matrix.nonsing_inv_mul (Gm p) hunit, Matrix.one_apply]
      · rw [Finset.sum_congr rfl fun k _ ↦ by rw [hGb i k],
          ← Matrix.mul_apply, Matrix.mul_nonsing_inv (Gm p) hunit, Matrix.one_apply]
    unfold metricDerivNorm q
    rw [Tensor0SBundle.normSq0S_eq_coord (I := I)
      (g_fam p.1.1) p.2 (a + 2) basis (fun i j ↦ (Gm p)⁻¹ i j)
      hinv (metricDiffCovDerivAt (I := I) a
        (g_fam p.1.2) (g_fam p.1.1) (g_fam p.1.1) p.2)]
    unfold Tensor0SBundle.coordInner0S
    refine congrArg Real.sqrt (Finset.sum_congr rfl fun I₀ _ ↦
      Finset.sum_congr rfl fun J₀ _ ↦ ?_)
    simp only [Tensor0SBundle.tensor0SComponent_apply, basis,
      IsLocalFrameOn.toBasisAt_coe]
  simpa only [Function.comp_def] using
    (Real.continuous_sqrt.continuousAt.comp hq).congr_of_eventuallyEq heq

omit [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem metric0_pair_cont
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {t : Real} (ht : t ∈ D.regular) (x₀ : M) :
    ContinuousAt
      (fun p : (Real × Real) × M ↦
        metricDerivNorm (I := I) 0
          (g_fam p.1.2) (g_fam p.1.1) (g_fam p.1.1) p.2)
      ((t, t), x₀) := by
  classical
  let Idx :=
    DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E
  let frame : Idx → (x : M) → TangentSpace I x :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀
  let U := DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x₀
  have hxU : x₀ ∈ U := by
    simpa [U] using
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x₀
  have hUo : IsOpen U := by
    simpa [U] using
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open (I := I) x₀
  have hframe :
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame U := by
    simpa [frame, U] using
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame
        (I := I) x₀
  apply derivNorm_pair_cont (I := I) g_fam hG ht x₀ 0
  intro slots
  let i : Idx := slots 0
  let j : Idx := slots 1
  have hs := (hG.frameCompSmooth frame hframe i j).contMDiffAt
    (prod_mem_nhds (D.regular_isOpen.mem_nhds ht) (hUo.mem_nhds hxU))
  have hvar : ContinuousAt
      (fun p : (Real × Real) × M ↦
        (g_fam p.1.2).inner p.2 (frame i p.2) (frame j p.2))
      ((t, t), x₀) := by
    exact ContinuousAt.comp'
      (f := fun p : (Real × Real) × M ↦ (p.1.2, p.2))
      (g := fun q : Real × M ↦
        (g_fam q.1).inner q.2 (frame i q.2) (frame j q.2))
      hs.continuousAt (continuousAt_fst.snd.prodMk continuousAt_snd)
  have hbase : ContinuousAt
      (fun p : (Real × Real) × M ↦
        (g_fam p.1.1).inner p.2 (frame i p.2) (frame j p.2))
      ((t, t), x₀) := by
    exact ContinuousAt.comp'
      (f := fun p : (Real × Real) × M ↦ (p.1.1, p.2))
      (g := fun q : Real × M ↦
        (g_fam q.1).inner q.2 (frame i q.2) (frame j q.2))
      hs.continuousAt (continuousAt_fst.fst.prodMk continuousAt_snd)
  simpa only [metricDiffCovDerivAt, metricCovDeriv,
    Tensor0SBundle.metricTensorField_apply, Pi.sub_apply,
    ContinuousMultilinearMap.sub_apply, frame, Idx, i, j] using hvar.sub hbase

omit [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem metric1_pair_cont
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {t : Real} (ht : t ∈ D.regular) (x₀ : M) :
    ContinuousAt
      (fun p : (Real × Real) × M ↦
        metricDerivNorm (I := I) 1
          (g_fam p.1.2) (g_fam p.1.1) (g_fam p.1.1) p.2)
      ((t, t), x₀) := by
  classical
  let Idx :=
    DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E
  let frame : Idx → (x : M) → TangentSpace I x :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀
  let U := DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x₀
  have hxU : x₀ ∈ U := by
    simpa [U] using
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x₀
  have hUo : IsOpen U := by
    simpa [U] using
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open (I := I) x₀
  have hframe :
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame U := by
    simpa [frame, U] using
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame
        (I := I) x₀
  have hframe1 : IsLocalFrameOn I E 1 frame U := by
    simpa [frame, U] using
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one
        (I := I) x₀
  let mb : (Real × Real) × M → Idx → Idx → Real := fun p i j ↦
    (g_fam p.1.1).inner p.2 (frame i p.2) (frame j p.2)
  let mv : (Real × Real) × M → Idx → Idx → Real := fun p i j ↦
    (g_fam p.1.2).inner p.2 (frame i p.2) (frame j p.2)
  let db : (Real × Real) × M → Idx → Idx → Idx → Real :=
    fun p d i j ↦ extDerivFun (I := I)
      (fun y : M ↦ (g_fam p.1.1).inner y (frame i y) (frame j y))
      p.2 (frame d p.2)
  let dv : (Real × Real) × M → Idx → Idx → Idx → Real :=
    fun p d i j ↦ extDerivFun (I := I)
      (fun y : M ↦ (g_fam p.1.2).inner y (frame i y) (frame j y))
      p.2 (frame d p.2)
  let Gm : (Real × Real) × M → Matrix Idx Idx Real :=
    fun p ↦ Matrix.of fun i j ↦ mb p i j
  have hmBase (i j : Idx) : ContinuousAt (fun p ↦ mb p i j) ((t, t), x₀) := by
    have hs := (hG.frameCompSmooth frame hframe i j).contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds ht) (hUo.mem_nhds hxU))
    exact ContinuousAt.comp'
      (f := fun p : (Real × Real) × M ↦ (p.1.1, p.2))
      (g := fun q : Real × M ↦
        (g_fam q.1).inner q.2 (frame i q.2) (frame j q.2))
      hs.continuousAt (continuousAt_fst.fst.prodMk continuousAt_snd)
  have hmVar (i j : Idx) : ContinuousAt (fun p ↦ mv p i j) ((t, t), x₀) := by
    have hs := (hG.frameCompSmooth frame hframe i j).contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds ht) (hUo.mem_nhds hxU))
    exact ContinuousAt.comp'
      (f := fun p : (Real × Real) × M ↦ (p.1.2, p.2))
      (g := fun q : Real × M ↦
        (g_fam q.1).inner q.2 (frame i q.2) (frame j q.2))
      hs.continuousAt (continuousAt_fst.snd.prodMk continuousAt_snd)
  have hdb (d i j : Idx) : ContinuousAt (fun p ↦ db p d i j) ((t, t), x₀) := by
    have hs := (hG.frameCompSmooth frame hframe i j).contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds ht) (hUo.mem_nhds hxU))
    have hd := prodExtDerivAt_inf (I := I) hs
      ((hframe.contMDiffAt hUo hxU d))
    exact ContinuousAt.comp'
      (f := fun p : (Real × Real) × M ↦ (p.1.1, p.2))
      (g := fun q : Real × M ↦ extDerivFun (I := I)
        (fun y : M ↦ (g_fam q.1).inner y (frame i y) (frame j y))
        q.2 (frame d q.2))
      hd.continuousAt (continuousAt_fst.fst.prodMk continuousAt_snd)
  have hdv (d i j : Idx) : ContinuousAt (fun p ↦ dv p d i j) ((t, t), x₀) := by
    have hs := (hG.frameCompSmooth frame hframe i j).contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds ht) (hUo.mem_nhds hxU))
    have hd := prodExtDerivAt_inf (I := I) hs
      ((hframe.contMDiffAt hUo hxU d))
    exact ContinuousAt.comp'
      (f := fun p : (Real × Real) × M ↦ (p.1.2, p.2))
      (g := fun q : Real × M ↦ extDerivFun (I := I)
        (fun y : M ↦ (g_fam q.1).inner y (frame i y) (frame j y))
        q.2 (frame d q.2))
      hd.continuousAt (continuousAt_fst.snd.prodMk continuousAt_snd)
  have hGmc : ContinuousAt Gm ((t, t), x₀) :=
    continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ by
      simpa [Gm, Matrix.of_apply] using hmBase i j
  have hdetne : ∀ p, p.2 ∈ U → (Gm p).det ≠ 0 := by
    intro p hp hdet0
    obtain ⟨c, hc0, hcv⟩ :=
      (Matrix.exists_mulVec_eq_zero_iff (M := Gm p)).2 hdet0
    let basis := hframe.toBasisAt hp
    let w : TangentSpace I p.2 := ∑ i, c i • basis i
    have hrow0 : ∀ i, (g_fam p.1.1).inner p.2 (basis i) w = 0 := by
      intro i
      have hsum : (g_fam p.1.1).inner p.2 (basis i) w =
          ∑ j, Gm p i j * c j := by
        simp only [w, map_sum, map_smul, smul_eq_mul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [Gm, Matrix.of_apply, mb, basis,
          IsLocalFrameOn.toBasisAt_coe]
        ring
      rw [hsum]
      simpa [Matrix.mulVec, dotProduct] using congrFun hcv i
    have hinner : (g_fam p.1.1).inner p.2 w w = 0 := by
      have hw_sum : w = ∑ i, c i • basis i := rfl
      calc
        (g_fam p.1.1).inner p.2 w w =
            (g_fam p.1.1).inner p.2 w (∑ i, c i • basis i) :=
          congrArg ((g_fam p.1.1).inner p.2 w) hw_sum
        _ = ∑ i, c i * (g_fam p.1.1).inner p.2 w (basis i) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]
        _ = ∑ i, c i * (g_fam p.1.1).inner p.2 (basis i) w := by
          exact Finset.sum_congr rfl fun i _ ↦ by
            rw [(g_fam p.1.1).symm p.2 w (basis i)]
        _ = 0 := Finset.sum_eq_zero fun i _ ↦ by rw [hrow0 i, mul_zero]
    have hwne : w ≠ 0 := by
      intro hw
      apply hc0
      have hall := Fintype.linearIndependent_iff.1 basis.linearIndependent c
        (by simpa [w] using hw)
      exact funext hall
    exact absurd hinner (ne_of_gt ((g_fam p.1.1).pos p.2 w hwne))
  have hGinvc : ContinuousAt (fun p ↦ (Gm p)⁻¹) ((t, t), x₀) := by
    have hdetc : ContinuousAt (fun p ↦ (Gm p).det) ((t, t), x₀) :=
      (continuous_id.matrix_det).continuousAt.comp hGmc
    have hadjc : ContinuousAt (fun p ↦ (Gm p).adjugate) ((t, t), x₀) :=
      (continuous_id.matrix_adjugate).continuousAt.comp hGmc
    simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using
      (hdetc.inv₀ (hdetne ((t, t), x₀) hxU)).smul hadjc
  have hGinv (i j : Idx) : ContinuousAt (fun p ↦ (Gm p)⁻¹ i j) ((t, t), x₀) :=
    continuousAt_pi.1 (continuousAt_pi.1 hGinvc i) j
  let gamma : (Real × Real) × M → Idx → Idx → Idx → Real :=
    fun p d i k ↦ (1 / 2 : Real) * ∑ l : Idx, (Gm p)⁻¹ k l *
      (db p d i l + db p i d l - db p l d i)
  have hgamma (d i k : Idx) :
      ContinuousAt (fun p ↦ gamma p d i k) ((t, t), x₀) := by
    exact continuousAt_const.mul (tendsto_finset_sum _ fun l _ ↦
      (hGinv k l).mul (((hdb d i l).add (hdb i d l)).sub (hdb l d i)))
  let rhs : (Real × Real) × M → Idx → Idx → Idx → Real :=
    fun p d i j ↦
      dv p d i j - db p d i j -
        ∑ k : Idx, gamma p d i k * (mv p k j - mb p k j) -
        ∑ k : Idx, gamma p d j k * (mv p i k - mb p i k)
  have hrhs (d i j : Idx) : ContinuousAt (fun p ↦ rhs p d i j) ((t, t), x₀) := by
    exact ((hdv d i j).sub (hdb d i j)).sub
      (tendsto_finset_sum _ fun k _ ↦
        (hgamma d i k).mul ((hmVar k j).sub (hmBase k j))) |>.sub
      (tendsto_finset_sum _ fun k _ ↦
        (hgamma d j k).mul ((hmVar i k).sub (hmBase i k)))
  apply derivNorm_pair_cont (I := I) g_fam hG ht x₀ 1
  intro slots
  let d : Idx := slots 0
  let i : Idx := slots 1
  let j : Idx := slots 2
  refine (hrhs d i j).congr_of_eventuallyEq ?_
  have hregN : ((D.regular ×ˢ D.regular) ×ˢ U) ∈
      𝓝 ((t, t), x₀) :=
    prod_mem_nhds
      (prod_mem_nhds (D.regular_isOpen.mem_nhds ht)
        (D.regular_isOpen.mem_nhds ht))
      (hUo.mem_nhds hxU)
  filter_upwards [hregN] with p hp
  let basis := hframe.toBasisAt hp.2
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I)
      (g_fam p.1.1) p.2 basis (fun r s ↦ (Gm p)⁻¹ r s) := by
    have hunit : IsUnit (Gm p).det := isUnit_iff_ne_zero.2 (hdetne p hp.2)
    intro r s
    have hGb (u v : Idx) :
        (g_fam p.1.1).inner p.2 (basis u) (basis v) = Gm p u v := by
      simp [basis, Gm, mb, IsLocalFrameOn.toBasisAt_coe]
    constructor
    · rw [Finset.sum_congr rfl fun k _ ↦ by rw [hGb k s],
        ← Matrix.mul_apply, Matrix.nonsing_inv_mul (Gm p) hunit, Matrix.one_apply]
    · rw [Finset.sum_congr rfl fun k _ ↦ by rw [hGb r k],
        ← Matrix.mul_apply, Matrix.mul_nonsing_inv (Gm p) hunit, Matrix.one_apply]
  have hchr (a b c : Idx) :
      christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) (g_fam p.1.1))
          frame hframe1 p.2 a b c = gamma p a b c := by
    simpa [gamma, db, frame, Gm, mb, basis] using
      coordinateFrame_christoffel_formula_point_of_isLeviCivita
        (I := I) (g := g_fam p.1.1)
        (leviCivitaConnectionOfMetric_isLeviCivita (I := I) (g_fam p.1.1))
        x₀ hp.2 (fun r s ↦ (Gm p)⁻¹ r s) hinv a b c
  have hconn (a b : Idx) :
      ((leviCivitaConnectionOfMetric (I := I) (g_fam p.1.1))
          (frame b) p.2) (frame a p.2) =
        ∑ c : Idx, gamma p a b c • frame c p.2 := by
    rw [covariantDerivative_eq_sum_christoffel
      (I := I) (leviCivitaConnectionOfMetric (I := I) (g_fam p.1.1))
      frame hframe1 hp.2 a b]
    exact Finset.sum_congr rfl fun c _ ↦
      congrArg (fun z : Real ↦ z • frame c p.2) (hchr a b c)
  have hslots : slots =
      (Fin.cons d (fun q : Fin 2 ↦ if q = 0 then i else j) : Fin 3 → Idx) := by
    funext z
    fin_cases z <;> rfl
  have hv := metricCovDeriv_one_component_localFrame (I := I)
    (g_fam p.1.2) (g_fam p.1.1) frame hframe hUo hp.2 d i j
  have hb := metricCovDeriv_one_component_localFrame (I := I)
    (g_fam p.1.1) (g_fam p.1.1) frame hframe hUo hp.2 d i j
  rw [Tensor0SBundle.component0S_apply] at hv hb
  simp only [IsLocalFrameOn.toBasisAt_coe] at hv hb
  rw [hslots]
  change
    ((metricCovDeriv (I := I) (g_fam p.1.2) (g_fam p.1.1) 1 p.2 -
        metricCovDeriv (I := I) (g_fam p.1.1) (g_fam p.1.1) 1 p.2)
      (fun z ↦ frame
        ((Fin.cons d (fun q : Fin 2 ↦ if q = 0 then i else j) : Fin 3 → Idx) z) p.2)) =
      rhs p d i j
  change
    (metricCovDeriv (I := I) (g_fam p.1.2) (g_fam p.1.1) 1 p.2)
        (fun z ↦ frame
          ((Fin.cons d (fun q : Fin 2 ↦ if q = 0 then i else j) : Fin 3 → Idx) z) p.2) -
      (metricCovDeriv (I := I) (g_fam p.1.1) (g_fam p.1.1) 1 p.2)
        (fun z ↦ frame
          ((Fin.cons d (fun q : Fin 2 ↦ if q = 0 then i else j) : Fin 3 → Idx) z) p.2) =
      rhs p d i j
  rw [hv, hb, hconn d i, hconn d j]
  simp only [map_sum, map_smul, smul_eq_mul]
  suffices h :
      dv p d i j -
            ((∑ k, gamma p d i k * mv p k j) +
              ∑ k, gamma p d j k * mv p i k) -
          (db p d i j -
            ((∑ k, gamma p d i k * mb p k j) +
              ∑ k, gamma p d j k * mb p i k)) =
        dv p d i j - db p d i j -
            ∑ k, gamma p d i k * (mv p k j - mb p k j) -
          ∑ k, gamma p d j k * (mv p i k - mb p i k)
    by simpa [rhs, mv, mb, dv, db] using h
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

section Compact

variable [CompactSpace M]

omit [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem metric_pair_event
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {t : Real} (ht : t ∈ D.regular) {ε : Real} (hε : 0 < ε) :
    ∀ᶠ q in 𝓝 (t, t), ∀ y : M, ∀ a : ℕ, a ≤ 1 →
      metricDerivNorm (I := I) a
        (g_fam q.2) (g_fam q.1) (g_fam q.1) y < ε := by
  classical
  have hlocal : ∀ x : M,
      ∃ V : Set (Real × Real), V ∈ 𝓝 (t, t) ∧
        ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
          ∀ q ∈ V, ∀ y ∈ W, ∀ a : ℕ, a ≤ 1 →
            metricDerivNorm (I := I) a
              (g_fam q.2) (g_fam q.1) (g_fam q.1) y < ε := by
    intro x
    have h0 := metric0_pair_cont (I := I) g_fam hG ht x
    have h1 := metric1_pair_cont (I := I) g_fam hG ht x
    have hs0 : ∀ᶠ p : (Real × Real) × M in 𝓝 ((t, t), x),
        metricDerivNorm (I := I) 0
          (g_fam p.1.2) (g_fam p.1.1) (g_fam p.1.1) p.2 < ε := by
      exact h0.eventually_lt_const (by
        simpa only [metricDerivNorm_self] using hε)
    have hs1 : ∀ᶠ p : (Real × Real) × M in 𝓝 ((t, t), x),
        metricDerivNorm (I := I) 1
          (g_fam p.1.2) (g_fam p.1.1) (g_fam p.1.1) p.2 < ε := by
      exact h1.eventually_lt_const (by
        simpa only [metricDerivNorm_self] using hε)
    obtain ⟨V, W, hVo, htV, hWo, hxW, hVW⟩ :=
      mem_nhds_prod_iff'.mp (Filter.inter_mem hs0 hs1)
    refine ⟨V, hVo.mem_nhds htV, W, hWo, hxW, ?_⟩
    intro q hq y hy a ha
    have hp := hVW (show (q, y) ∈ V ×ˢ W from ⟨hq, hy⟩)
    have ha01 : a = 0 ∨ a = 1 := by omega
    rcases ha01 with rfl | rfl
    · exact hp.1
    · exact hp.2
  choose V hV W hWo hxW hsmall using hlocal
  obtain ⟨F, _, hF⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).elim_nhds_subcover W
      (fun x _ ↦ (hWo x).mem_nhds (hxW x))
  have htime : ∀ᶠ q in 𝓝 (t, t), ∀ x ∈ F, q ∈ V x :=
    (Finset.eventually_all
      (I := F) (l := 𝓝 (t, t)) (p := fun x q ↦ q ∈ V x)).2
      (fun x _ ↦ hV x)
  filter_upwards [htime] with q hq
  intro y a ha
  obtain ⟨x, hxF, hyW⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
  exact hsmall x q (hq x hxF) y hyW a ha

omit [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem metric_c1_span
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {a b ε : Real}
    (hab : Set.Icc a b ⊆ D.regular)
    (hε : 0 < ε) :
    ∃ ρ : Real, 0 < ρ ∧
      ∀ base ∈ Set.Icc a b, ∀ var ∈ Set.Icc a b,
        |var - base| ≤ ρ →
          metricDerivNormSupOn (I := I) Set.univ 1
            (g_fam var) (g_fam base) (g_fam base) ≤ ε := by
  classical
  by_cases hK : Set.Icc a b = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro base hbase
    simp [hK] at hbase
  have hrad : ∀ t ∈ Set.Icc a b,
      ∃ r : Real, 0 < r ∧
        ∀ base var : Real,
          dist base t < r → dist var t < r →
          ∀ y : M, ∀ n : ℕ, n ≤ 1 →
            metricDerivNorm (I := I) n
              (g_fam var) (g_fam base) (g_fam base) y < ε := by
    intro t ht
    have hevent := metric_pair_event (I := I) g_fam hG (hab ht) hε
    obtain ⟨Vb, Vv, hVbo, htVb, hVvo, htVv, hprod⟩ :=
      mem_nhds_prod_iff'.mp hevent
    obtain ⟨rb, hrb, hballb⟩ := Metric.isOpen_iff.mp hVbo t htVb
    obtain ⟨rv, hrv, hballv⟩ := Metric.isOpen_iff.mp hVvo t htVv
    refine ⟨min rb rv, lt_min hrb hrv, ?_⟩
    intro base var hb hv y n hn
    have hb' : base ∈ Metric.ball t rb :=
      hb.trans_le (min_le_left _ _)
    have hv' : var ∈ Metric.ball t rv :=
      hv.trans_le (min_le_right _ _)
    have hq : (base, var) ∈ Vb ×ˢ Vv := ⟨hballb hb', hballv hv'⟩
    exact (hprod hq) y n hn
  choose r hr hlocal using hrad
  let W : Set.Icc a b → Set Real := fun t ↦ Metric.ball (t : Real) (r t t.2 / 2)
  have hWo : ∀ t, IsOpen (W t) := fun _ ↦ Metric.isOpen_ball
  have hcover : Set.Icc a b ⊆ ⋃ t, W t := by
    intro t ht
    exact Set.mem_iUnion.2 ⟨⟨t, ht⟩, Metric.mem_ball_self (half_pos (hr t ht))⟩
  obtain ⟨S, hS⟩ := isCompact_Icc.elim_finite_subcover W hWo hcover
  have hSne : S.Nonempty := by
    obtain ⟨t₀, ht₀⟩ := Set.nonempty_iff_ne_empty.2 hK
    obtain ⟨t, htS, _⟩ := Set.mem_iUnion₂.mp (hS ht₀)
    exact ⟨t, htS⟩
  let ρ : Real := S.inf' hSne (fun t ↦ r t t.2 / 2)
  have hρpos : 0 < ρ := by
    rw [show ρ = S.inf' hSne (fun t ↦ r t t.2 / 2) from rfl,
      Finset.lt_inf'_iff]
    intro t htS
    exact half_pos (hr t t.2)
  have hρle : ∀ t ∈ S, ρ ≤ r t t.2 / 2 := by
    intro t htS
    exact Finset.inf'_le _ htS
  refine ⟨ρ, hρpos, ?_⟩
  intro base hbase var _hvar hdist
  obtain ⟨t, htS, hbaseW⟩ := Set.mem_iUnion₂.mp (hS hbase)
  have hb : dist base (t : Real) < r t t.2 :=
    hbaseW.trans_le (half_le_self (hr t t.2).le)
  have hvb : dist var base ≤ ρ := by
    simpa only [Real.dist_eq] using hdist
  have hv : dist var (t : Real) < r t t.2 := by
    calc
      dist var (t : Real) ≤ dist var base + dist base (t : Real) := dist_triangle _ _ _
      _ < r t t.2 / 2 + r t t.2 / 2 :=
        add_lt_add_of_le_of_lt (hvb.trans (hρle t htS)) hbaseW
      _ = r t t.2 := by ring
  have hpoint : ∀ n : ℕ, n ≤ 1 → ∀ y ∈ (Set.univ : Set M),
      metricDerivNorm (I := I) n
        (g_fam var) (g_fam base) (g_fam base) y ≤ ε := by
    intro n hn y _
    exact (hlocal t t.2 base var hb hv y n hn).le
  exact metricDerivNormSupOn_le_of_forall
    (I := I) Set.univ 1 (g_fam var) (g_fam base) (g_fam base)
    ε hε.le hpoint

end Compact

omit [FiniteDimensional Real E] [I.Boundaryless] [SigmaCompactSpace M]
  [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem metricCov_cont
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (q : SmoothRiemannianMetric I M) {t : Real} (ht : t ∈ D.regular)
    {Idx : Type*}
    {u : Set M} (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (a : ℕ) (slots : Fin (a + 2) → Idx) :
    ContinuousAt
      (fun p : Real × M =>
        metricCovDeriv (I := I) (g_fam p.1) q a p.2
          (fun j => frame (slots j) p.2))
      (t, x) := by
  classical
  obtain ⟨sec, hsec⟩ :=
    hframe.exists_contMDiffSection_eqOn_nhd hu hx
  let V : Fin (a + 2) →
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
    fun j => sec (slots j)
  have htower :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
        (∞ : WithTop ℕ∞)
        (fun p : Real × M =>
          metricCovDeriv (I := I) (g_fam p.1) q a p.2
            (fun j => V j p.2))
        (t, x) := by
    have hbase :
        ∀ W : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
            (TangentSpace I : M → Type _),
          ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
            (∞ : WithTop ℕ∞)
            (fun p : Real × M =>
              (Tensor0SBundle.metricTensorField (I := I) (g_fam p.1)) p.2
                (fun j => W j p.2))
            (t, x) := by
      intro W
      simpa only [Tensor0SBundle.metricTensorField_apply] using
        hG.pairSmoothAt (D.regular_isOpen.mem_nhds ht) W
    simpa only [metricCovDeriv_eq_covDerivOfField] using
      covDerivOfField_eval_contMDiffAt (I := I) q
        (fun t => Tensor0SBundle.metricTensorField (I := I) (g_fam t))
        hbase a V
  have hev : ∀ᶠ y in 𝓝 x, ∀ j : Fin (a + 2),
      V j y = frame (slots j) y :=
    hsec.mono fun y hy j => hy (slots j)
  refine htower.continuousAt.congr_of_eventuallyEq ?_
  have hev' : ∀ᶠ p : Real × M in 𝓝 (t, x),
      ∀ j : Fin (a + 2), V j p.2 = frame (slots j) p.2 :=
    (continuous_snd.tendsto (t, x)).eventually hev
  filter_upwards [hev'] with p hp
  congr 1
  funext j
  exact (hp j).symm

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricCov_smooth
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime)
    {Idx : Type*}
    {u : Set M} (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (a : ℕ) (slots : Fin (a + 2) → Idx) :
    ContinuousAt
      (fun p : Real × M =>
        metricCovDeriv (I := I) (g_fam p.1) (g_fam (T : Real)) a p.2
          (fun j => frame (slots j) p.2))
      ((T : Real), x) :=
  metricCov_cont (I := I) g_fam hG (g_fam (T : Real)) T.2
    frame hframe hu hx a slots

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem metric_c_patch
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) (a : ℕ) (x : M)
    {ε : Real} (hε : 0 < ε) :
    ∃ V : Set Real, V ∈ 𝓝 (T : Real) ∧
      ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
        ∀ t ∈ V, ∀ y ∈ W,
          metricDerivNorm (I := I) a
            (g_fam t) (g_fam (T : Real)) (g_fam (T : Real)) y < ε := by
  classical
  obtain ⟨basisE, u, Cu, huOpen, hxu, huSub, hCu, hnorm⟩ :=
    metricDerivNorm_le_compSq_uniform (I := I) (g_fam (T : Real)) a x
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let frame := e.localFrame basisE
  have hxe : x ∈ e.baseSet := by
    simp [e]
  have hframe :
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame e.baseSet := by
    simpa [frame] using
      e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) basisE
  let c :
      (Real × M) →
        (Fin (a + 2) → Fin (Module.finrank Real E)) → Real :=
    fun p I0 =>
      metricCovDeriv (I := I) (g_fam p.1) (g_fam (T : Real)) a p.2
          (fun j => frame (I0 j) p.2) -
        metricCovDeriv (I := I) (g_fam (T : Real)) (g_fam (T : Real)) a p.2
          (fun j => frame (I0 j) p.2)
  let q : Real × M → Real :=
    fun p => Cu * Real.sqrt (∑ I0, (c p I0) ^ 2)
  have hc (I0 : Fin (a + 2) → Fin (Module.finrank Real E)) :
      ContinuousAt (fun p : Real × M => c p I0) ((T : Real), x) := by
    have hmove :=
      metricCov_smooth (I := I) g_fam hG T frame hframe e.open_baseSet hxe a I0
    have hwhole :=
      metricCov_smooth (I := I) g_fam hG T frame hframe e.open_baseSet hxe a I0
    have hfix :
        ContinuousAt
          (fun p : Real × M =>
            metricCovDeriv (I := I) (g_fam (T : Real)) (g_fam (T : Real)) a p.2
              (fun j => frame (I0 j) p.2))
          ((T : Real), x) := by
      have hconst :
          ContinuousAt (fun _ : Real × M => (T : Real)) ((T : Real), x) :=
        continuousAt_const
      have hsnd :
          ContinuousAt (fun p : Real × M => p.2) ((T : Real), x) :=
        continuousAt_snd
      have hmap :
          ContinuousAt (fun p : Real × M => ((T : Real), p.2)) ((T : Real), x) :=
        hconst.prodMk hsnd
      exact ContinuousAt.comp'
        (f := fun p : Real × M => ((T : Real), p.2))
        (g := fun q : Real × M =>
          metricCovDeriv (I := I) (g_fam q.1) (g_fam (T : Real)) a q.2
            (fun j => frame (I0 j) q.2))
        hwhole hmap
    exact hmove.sub hfix
  have hsum :
      ContinuousAt
        (fun p : Real × M => ∑ I0, (c p I0) ^ 2)
        ((T : Real), x) := by
    exact tendsto_finset_sum Finset.univ fun I0 _ => (hc I0).pow 2
  have hq : ContinuousAt q ((T : Real), x) := by
    exact continuousAt_const.mul
      (Real.continuous_sqrt.continuousAt.comp hsum)
  have hq0 : q ((T : Real), x) = 0 := by
    simp [q, c]
  have hsmall : {p : Real × M | q p < ε} ∈ 𝓝 ((T : Real), x) := by
    exact hq.eventually_lt_const (by simpa only [hq0] using hε)
  have huNhd : (Set.univ ×ˢ u : Set (Real × M)) ∈ 𝓝 ((T : Real), x) :=
    prod_mem_nhds Filter.univ_mem (huOpen.mem_nhds hxu)
  have htarget :
      ({p : Real × M | q p < ε} ∩ (Set.univ ×ˢ u)) ∈
        𝓝 ((T : Real), x) :=
    Filter.inter_mem hsmall huNhd
  obtain ⟨V, W, hVOpen, hTV, hWOpen, hxW, hVW⟩ :=
    mem_nhds_prod_iff'.mp htarget
  refine ⟨V, hVOpen.mem_nhds hTV, W, hWOpen, hxW, ?_⟩
  intro t ht y hy
  have hty : (t, y) ∈ V ×ˢ W := ⟨ht, hy⟩
  have hpair := hVW hty
  have hyu : y ∈ u := hpair.2.2
  have hye : y ∈ e.baseSet := by
    simpa only [e] using huSub hyu
  have hle :=
    hnorm (g_fam t) (g_fam (T : Real)) y hyu (by simpa only [e] using hye)
  have hle' :
      metricDerivNorm (I := I) a
          (g_fam t) (g_fam (T : Real)) (g_fam (T : Real)) y
        ≤ q (t, y) := by
    simpa only [q, c, frame, e, Tensor0SBundle.component0S_apply,
      IsLocalFrameOn.toBasisAt_coe] using hle
  exact lt_of_le_of_lt hle' hpair.1

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem metric_c1_patch
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) (x : M)
    {ε : Real} (hε : 0 < ε) :
    ∃ V : Set Real, V ∈ 𝓝 (T : Real) ∧
      ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
        ∀ t ∈ V, ∀ y ∈ W, ∀ a : ℕ, a ≤ 1 →
          metricDerivNorm (I := I) a
            (g_fam t) (g_fam (T : Real)) (g_fam (T : Real)) y < ε := by
  obtain ⟨V0, hV0, W0, hW0Open, hxW0, h0⟩ :=
    metric_c_patch (I := I) g_fam hG T 0 x hε
  obtain ⟨V1, hV1, W1, hW1Open, hxW1, h1⟩ :=
    metric_c_patch (I := I) g_fam hG T 1 x hε
  refine ⟨V0 ∩ V1, Filter.inter_mem hV0 hV1,
    W0 ∩ W1, hW0Open.inter hW1Open, ⟨hxW0, hxW1⟩, ?_⟩
  intro t ht y hy a ha
  have ha' : a = 0 ∨ a = 1 := by
    omega
  rcases ha' with rfl | rfl
  · exact h0 t ht.1 y hy.1
  · exact h1 t ht.2 y hy.2

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem metric_b_patch
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) {t : Real} (ht : t ∈ D.regular) (a : ℕ) (x : M) :
    ∃ V : Set Real, V ∈ 𝓝 t ∧
      ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
        ∃ C : Real, 0 ≤ C ∧ ∀ r ∈ V, ∀ y ∈ W,
          metricDerivNorm (I := I) a
            (g_fam r) (g_fam (T : Real)) (g_fam (T : Real)) y ≤ C := by
  classical
  obtain ⟨basisE, u, Cu, huOpen, hxu, huSub, hCu, hnorm⟩ :=
    metricDerivNorm_le_compSq_uniform (I := I) (g_fam (T : Real)) a x
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let frame := e.localFrame basisE
  have hxe : x ∈ e.baseSet := by
    simp [e]
  have hframe :
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame e.baseSet := by
    simpa [frame] using
      e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) basisE
  let c :
      (Real × M) →
        (Fin (a + 2) → Fin (Module.finrank Real E)) → Real :=
    fun p I0 =>
      metricCovDeriv (I := I) (g_fam p.1) (g_fam (T : Real)) a p.2
          (fun j => frame (I0 j) p.2) -
        metricCovDeriv (I := I) (g_fam (T : Real)) (g_fam (T : Real)) a p.2
          (fun j => frame (I0 j) p.2)
  let b : Real × M → Real :=
    fun p => Cu * Real.sqrt (∑ I0, (c p I0) ^ 2)
  have hc (I0 : Fin (a + 2) → Fin (Module.finrank Real E)) :
      ContinuousAt (fun p : Real × M => c p I0) (t, x) := by
    have hmove :=
      metricCov_cont (I := I) g_fam hG (g_fam (T : Real)) ht
        frame hframe e.open_baseSet hxe a I0
    have hwhole :=
      metricCov_cont (I := I) g_fam hG (g_fam (T : Real)) T.2
        frame hframe e.open_baseSet hxe a I0
    have hfix :
        ContinuousAt
          (fun p : Real × M =>
            metricCovDeriv (I := I) (g_fam (T : Real)) (g_fam (T : Real)) a p.2
              (fun j => frame (I0 j) p.2))
          (t, x) := by
      have hconst :
          ContinuousAt (fun _ : Real × M => (T : Real)) (t, x) :=
        continuousAt_const
      have hsnd :
          ContinuousAt (fun p : Real × M => p.2) (t, x) :=
        continuousAt_snd
      have hmap :
          ContinuousAt (fun p : Real × M => ((T : Real), p.2)) (t, x) :=
        hconst.prodMk hsnd
      exact ContinuousAt.comp'
        (f := fun p : Real × M => ((T : Real), p.2))
        (g := fun q : Real × M =>
          metricCovDeriv (I := I) (g_fam q.1) (g_fam (T : Real)) a q.2
            (fun j => frame (I0 j) q.2))
        hwhole hmap
    exact hmove.sub hfix
  have hsum :
      ContinuousAt
        (fun p : Real × M => ∑ I0, (c p I0) ^ 2)
        (t, x) := by
    exact tendsto_finset_sum Finset.univ fun I0 _ => (hc I0).pow 2
  have hb : ContinuousAt b (t, x) := by
    exact continuousAt_const.mul
      (Real.continuous_sqrt.continuousAt.comp hsum)
  have hb_nn : 0 ≤ b (t, x) := by
    exact mul_nonneg (zero_le_one.trans hCu) (Real.sqrt_nonneg _)
  have hsmall : {p : Real × M | b p < b (t, x) + 1} ∈ 𝓝 (t, x) := by
    exact hb.eventually_lt_const (by linarith)
  have huNhd : (Set.univ ×ˢ u : Set (Real × M)) ∈ 𝓝 (t, x) :=
    prod_mem_nhds Filter.univ_mem (huOpen.mem_nhds hxu)
  have htarget :
      ({p : Real × M | b p < b (t, x) + 1} ∩ (Set.univ ×ˢ u)) ∈
        𝓝 (t, x) :=
    Filter.inter_mem hsmall huNhd
  obtain ⟨V, W, hVOpen, htV, hWOpen, hxW, hVW⟩ :=
    mem_nhds_prod_iff'.mp htarget
  refine ⟨V, hVOpen.mem_nhds htV, W, hWOpen, hxW,
    b (t, x) + 1, by linarith, ?_⟩
  intro r hr y hy
  have hry : (r, y) ∈ V ×ˢ W := ⟨hr, hy⟩
  have hpair := hVW hry
  have hyu : y ∈ u := hpair.2.2
  have hye : y ∈ e.baseSet := by
    simpa only [e] using huSub hyu
  have hle :=
    hnorm (g_fam r) (g_fam (T : Real)) y hyu (by simpa only [e] using hye)
  have hle' :
      metricDerivNorm (I := I) a
          (g_fam r) (g_fam (T : Real)) (g_fam (T : Real)) y
        ≤ b (r, y) := by
    simpa only [b, c, frame, e, Tensor0SBundle.component0S_apply,
      IsLocalFrameOn.toBasisAt_coe] using hle
  exact hle'.trans hpair.1.le

section Compact

variable [CompactSpace M]

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem metric_b_event
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) {t : Real} (ht : t ∈ D.regular) (a : ℕ) :
    ∃ C : Real, 0 ≤ C ∧ ∀ᶠ r in 𝓝 t, ∀ y : M,
      metricDerivNorm (I := I) a
        (g_fam r) (g_fam (T : Real)) (g_fam (T : Real)) y ≤ C := by
  classical
  choose V hV W hWOpen hxW C hC hloc using
    fun x : M => metric_b_patch (I := I) g_fam hG T ht a x
  obtain ⟨F, _, hF⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).elim_nhds_subcover W
      (fun x _ => (hWOpen x).mem_nhds (hxW x))
  refine ⟨∑ x ∈ F, C x,
    Finset.sum_nonneg fun x _ => hC x, ?_⟩
  have htime :
      ∀ᶠ r in 𝓝 t, ∀ x ∈ F, r ∈ V x := by
    exact
      (Finset.eventually_all
        (I := F)
        (l := 𝓝 t)
        (p := fun x r => r ∈ V x)).2
        (fun x _ => hV x)
  filter_upwards [htime] with r hr
  intro y
  obtain ⟨x, hxF, hyW⟩ :=
    Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
  exact (hloc x r (hr x hxF) y hyW).trans
    (Finset.single_le_sum (fun z _ => hC z) hxF)

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem metric_b_compact
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) {K : Set Real} (hK : IsCompact K)
    (hKreg : K ⊆ D.regular) (a : ℕ) :
    ∃ C : Real, 0 ≤ C ∧ ∀ t ∈ K, ∀ y : M,
      metricDerivNorm (I := I) a
        (g_fam t) (g_fam (T : Real)) (g_fam (T : Real)) y ≤ C := by
  classical
  choose C hC hbound using fun t : {t : Real // t ∈ K} =>
    metric_b_event (I := I) g_fam hG T (hKreg t.2) a
  choose O hOsub hOopen htO using fun t : {t : Real // t ∈ K} =>
    mem_nhds_iff.mp (hbound t)
  have hcover : K ⊆ ⋃ t : {t : Real // t ∈ K}, O t := by
    intro t ht
    exact Set.mem_iUnion.2 ⟨⟨t, ht⟩, htO ⟨t, ht⟩⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover O hOopen hcover
  refine ⟨∑ t ∈ F, C t,
    Finset.sum_nonneg fun t _ => hC t, ?_⟩
  intro t ht y
  obtain ⟨r, hrF, htO'⟩ := Set.mem_iUnion₂.mp (hF ht)
  exact (hOsub r htO' y).trans
    (Finset.single_le_sum (fun z _ => hC z) hrF)

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metric_cp_bdd
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) {K : Set Real} (hK : IsCompact K)
    (hKreg : K ⊆ D.regular) :
    ∃ C : ℕ → Real, (∀ p, 0 ≤ C p) ∧ ∀ (p : ℕ) (t : Real), t ∈ K →
      metricDerivNormSupOn (I := I) Set.univ p
        (g_fam t) (g_fam (T : Real)) (g_fam (T : Real)) ≤ C p := by
  classical
  choose B hB hbound using fun a : ℕ =>
    metric_b_compact (I := I) g_fam hG T hK hKreg a
  refine ⟨fun p => ∑ a ∈ Finset.range (p + 1), B a,
    fun p => Finset.sum_nonneg fun a _ => hB a, ?_⟩
  intro p t ht
  apply metricDerivNormSupOn_le_of_forall
  · exact Finset.sum_nonneg fun a _ => hB a
  · intro a ha y _
    exact (hbound a t ht y).trans
      (Finset.single_le_sum (fun j _ => hB j)
        (by simp only [Finset.mem_range]; omega))

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem metric_c_event
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) (a : ℕ)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (T : Real), ∀ y : M,
      metricDerivNorm (I := I) a
        (g_fam t) (g_fam (T : Real)) (g_fam (T : Real)) y < ε := by
  classical
  choose V hV W hWOpen hxW hloc using
    fun x : M => metric_c_patch (I := I) g_fam hG T a x hε
  obtain ⟨F, _, hF⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).elim_nhds_subcover W
      (fun x _ => (hWOpen x).mem_nhds (hxW x))
  have htime :
      ∀ᶠ t in 𝓝 (T : Real), ∀ x ∈ F, t ∈ V x := by
    exact
      (Finset.eventually_all
        (I := F)
        (l := 𝓝 (T : Real))
        (p := fun x t => t ∈ V x)).2
        (fun x _ => hV x)
  filter_upwards [htime] with t ht
  intro y
  obtain ⟨x, hxF, hyW⟩ :=
    Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
  exact hloc x t (ht x hxF) y hyW

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metric_cp_tendsto
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) (p : ℕ) :
    Filter.Tendsto
      (fun t : Real =>
        metricDerivNormSupOn (I := I) Set.univ p
          (g_fam t) (g_fam (T : Real)) (g_fam (T : Real)))
      (𝓝 (T : Real)) (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have htime :
      ∀ᶠ t in 𝓝 (T : Real),
        ∀ a ∈ Finset.range (p + 1), ∀ y : M,
          metricDerivNorm (I := I) a
            (g_fam t) (g_fam (T : Real)) (g_fam (T : Real)) y < ε / 2 := by
    exact
      (Finset.eventually_all
        (I := Finset.range (p + 1))
        (l := 𝓝 (T : Real))
        (p := fun a t => ∀ y : M,
          metricDerivNorm (I := I) a
            (g_fam t) (g_fam (T : Real)) (g_fam (T : Real)) y < ε / 2)).2
        (fun a _ => metric_c_event (I := I) g_fam hG T a hε2)
  filter_upwards [htime] with t ht
  have hpoint :
      ∀ a : ℕ, a ≤ p → ∀ y ∈ (Set.univ : Set M),
        metricDerivNorm (I := I) a
            (g_fam t) (g_fam (T : Real)) (g_fam (T : Real)) y
          ≤ ε / 2 := by
    intro a ha y _
    exact (ht a (by simp only [Finset.mem_range]; omega) y).le
  have hsup :
      metricDerivNormSupOn (I := I) Set.univ p
          (g_fam t) (g_fam (T : Real)) (g_fam (T : Real))
        ≤ ε / 2 :=
    metricDerivNormSupOn_le_of_forall
      (I := I) Set.univ p
      (g_fam t) (g_fam (T : Real)) (g_fam (T : Real))
      (ε / 2) hε2.le hpoint
  have hnonneg :
      0 ≤ metricDerivNormSupOn (I := I) Set.univ p
        (g_fam t) (g_fam (T : Real)) (g_fam (T : Real)) := by
    unfold metricDerivNormSupOn
    apply Real.sSup_nonneg
    rintro r ⟨a, ha, y, hy, rfl⟩
    exact Real.sqrt_nonneg _
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
    hsup.trans_lt (half_lt_self hε)

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metric_c1_tendsto
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) :
    Filter.Tendsto
      (fun t : Real =>
        metricDerivNormSupOn (I := I) Set.univ 1
          (g_fam t) (g_fam (T : Real)) (g_fam (T : Real)))
      (𝓝 (T : Real)) (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  choose V hV W hWOpen hxW hloc using
    fun x : M => metric_c1_patch (I := I) g_fam hG T x hε2
  obtain ⟨F, _, hF⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).elim_nhds_subcover W
      (fun x _ => (hWOpen x).mem_nhds (hxW x))
  have htime :
      ∀ᶠ t in 𝓝 (T : Real), ∀ x ∈ F, t ∈ V x := by
    exact
      (Finset.eventually_all
        (I := F)
        (l := 𝓝 (T : Real))
        (p := fun x t => t ∈ V x)).2
        (fun x _ => hV x)
  filter_upwards [htime] with t ht
  have hpoint :
      ∀ a : ℕ, a ≤ 1 → ∀ y ∈ (Set.univ : Set M),
        metricDerivNorm (I := I) a
            (g_fam t) (g_fam (T : Real)) (g_fam (T : Real)) y
          ≤ ε / 2 := by
    intro a ha y _
    obtain ⟨x, hxF, hyW⟩ :=
      Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
    exact (hloc x t (ht x hxF) y hyW a ha).le
  have hsup :
      metricDerivNormSupOn (I := I) Set.univ 1
          (g_fam t) (g_fam (T : Real)) (g_fam (T : Real))
        ≤ ε / 2 :=
    metricDerivNormSupOn_le_of_forall
      (I := I) Set.univ 1
      (g_fam t) (g_fam (T : Real)) (g_fam (T : Real))
      (ε / 2) hε2.le hpoint
  have hnonneg :
      0 ≤ metricDerivNormSupOn (I := I) Set.univ 1
        (g_fam t) (g_fam (T : Real)) (g_fam (T : Real)) := by
    unfold metricDerivNormSupOn
    apply Real.sSup_nonneg
    rintro r ⟨a, ha, y, hy, rfl⟩
    exact Real.sqrt_nonneg _
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
    hsup.trans_lt (half_lt_self hε)

end Compact

end HCGCompactness
end DifferentialGeometry

end
