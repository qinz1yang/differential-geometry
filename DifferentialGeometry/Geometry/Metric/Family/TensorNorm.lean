import DifferentialGeometry.Geometry.Metric.Family.Basic
import DifferentialGeometry.Geometry.Connection.ChartBridge.Metric.InverseGram
import DifferentialGeometry.Tensor.RSTensor.Coordinates.BasisEvaluation
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem continuous_normSq0S_family
    {s : Nat} {K : Set Real}
    (g : Real → SmoothRiemannianMetric I M)
    (A : (t : Real) → (x : M) → Tensor0SSpace s I x)
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => metricTensorField (I := I) (g t) x))
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A) :
    Continuous
      (fun q : {t : Real // t ∈ K} × M ↦
        normSq0S (I := I) (g q.1.1) q.2 s (A q.1.1 q.2)) := by
  classical
  unfold tensor0SFamilyContinuousOnSet at hA
  rw [continuous_iff_continuousAt] at hA ⊢
  intro q₀
  let e := trivializationAt E (TangentSpace I : M → Type _) q₀.2
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
  have hx₀ : q₀.2 ∈ e.baseSet := by
    simpa only [e] using
      mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) q₀.2
  let Gm : ({t : Real // t ∈ K} × M) →
      Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    fun q ↦ DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g q.1.1) q₀.2 q.2
  have hopen : {q : {t : Real // t ∈ K} × M | q.2 ∈ e.baseSet} ∈ nhds q₀ := by
    exact (e.open_baseSet.preimage continuous_snd).mem_nhds hx₀
  have hGmEnt : ∀ i j : Fin (Module.finrank Real E),
      ContinuousAt (fun q ↦ Gm q i j) q₀ := by
    intro i j
    have hcoord := (show Continuous _ from hg).continuousAt (x := q₀)
    rw [FiberBundle.continuousAt_totalSpace] at hcoord
    let idx : Fin 2 → Fin (Module.finrank ℝ E) := ![i, j]
    have hval := continuousAt_pi.1
      ((eval0SCLE (E := E) 2).continuous.continuousAt.comp hcoord.2) idx
    convert hval using 1
    funext q
    dsimp only [Function.comp_apply]
    rw [eval0SCLE_apply]
    change _ = metricTensorField (I := I) (g q.1.1) q.2
      (fun k : Fin 2 => e.symmL ℝ q.2 (b (idx k)))
    rw [metricTensorField_apply]
    rfl
  have hGmc : ContinuousAt Gm q₀ :=
    continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ hGmEnt i j
  have hdetne : (Gm q₀).det ≠ 0 := by
    exact ne_of_gt
      (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) (g q₀.1.1) q₀.2 hx₀)
  have hGinvc : ContinuousAt (fun q ↦ (Gm q)⁻¹) q₀ := by
    have hdetc : ContinuousAt (fun q ↦ (Gm q).det) q₀ :=
      (continuous_id.matrix_det).continuousAt.comp hGmc
    have hadjc : ContinuousAt (fun q ↦ (Gm q).adjugate) q₀ :=
      (continuous_id.matrix_adjugate).continuousAt.comp hGmc
    have hcramer : ContinuousAt
        (fun q ↦ ((Gm q).det)⁻¹ • (Gm q).adjugate) q₀ :=
      (hdetc.inv₀ hdetne).smul hadjc
    have heq : (fun q ↦ (Gm q)⁻¹) =
        fun q ↦ ((Gm q).det)⁻¹ • (Gm q).adjugate := by
      funext q
      rw [Matrix.inv_def, Ring.inverse_eq_inv]
    rw [heq]
    exact hcramer
  have hGinvEnt : ∀ i j : Fin (Module.finrank Real E),
      ContinuousAt (fun q ↦ (Gm q)⁻¹ i j) q₀ := fun i j ↦
    continuousAt_pi.1 (continuousAt_pi.1 hGinvc i) j
  have hcoord := hA q₀
  rw [FiberBundle.continuousAt_totalSpace] at hcoord
  have hmodel : ContinuousAt
      (fun q : {t : Real // t ∈ K} × M ↦
        (trivializationAt (Tensor0SModel s Real E)
          (fun x : M ↦ Tensor0SSpace s I x) q₀.2
            ⟨q.2, A q.1.1 q.2⟩).2) q₀ := by
    exact hcoord.2
  have hslots : ∀ idx : Fin s → Fin (Module.finrank Real E),
      ContinuousAt
        (fun q : {t : Real // t ∈ K} × M ↦
          A q.1.1 q.2
            (fun k : Fin s ↦ e.symmL Real q.2 (b (idx k)))) q₀ := by
    intro idx
    have heval : ContinuousAt
        (fun q : {t : Real // t ∈ K} × M ↦
          eval0SCLE (E := E) s
            ((trivializationAt (Tensor0SModel s Real E)
              (fun x : M ↦ Tensor0SSpace s I x) q₀.2
                ⟨q.2, A q.1.1 q.2⟩).2) idx) q₀ := by
      have hall := (eval0SCLE (E := E) s).continuous.continuousAt.comp hmodel
      exact continuousAt_pi.1 hall idx
    have heq :
        (fun q : {t : Real // t ∈ K} × M ↦
          eval0SCLE (E := E) s
            ((trivializationAt (Tensor0SModel s Real E)
              (fun x : M ↦ Tensor0SSpace s I x) q₀.2
                ⟨q.2, A q.1.1 q.2⟩).2) idx) =
          fun q ↦ A q.1.1 q.2
            (fun k : Fin s ↦ e.symmL Real q.2 (b (idx k))) := by
      funext q
      rw [eval0SCLE_apply]
      change
        ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) s q.2
          (A q.1.1 q.2)).compContinuousLinearMap
          (fun _ : Fin s ↦ e.symmL Real q.2))
            (fun k : Fin s ↦ b (idx k)) = _
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      rw [tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]
    rw [heq] at heval
    exact heval
  have hF : ContinuousAt
      (fun q : {t : Real // t ∈ K} × M ↦
        ∑ I₀ : Fin s → Fin (Module.finrank Real E),
          ∑ J₀ : Fin s → Fin (Module.finrank Real E),
            (∏ a : Fin s, (Gm q)⁻¹ (I₀ a) (J₀ a)) *
              (A q.1.1 q.2 (fun a : Fin s ↦ e.symmL Real q.2 (b (I₀ a)))) *
              (A q.1.1 q.2 (fun a : Fin s ↦ e.symmL Real q.2 (b (J₀ a))))) q₀ := by
    refine tendsto_finsetSum _ fun I₀ _ ↦ tendsto_finsetSum _ fun J₀ _ ↦ ?_
    have hp : ContinuousAt
        (fun q ↦ ∏ a : Fin s, (Gm q)⁻¹ (I₀ a) (J₀ a)) q₀ :=
      tendsto_finsetProd _ fun a _ ↦ hGinvEnt (I₀ a) (J₀ a)
    exact (hp.mul (hslots I₀)).mul (hslots J₀)
  have hev :
      (fun q : {t : Real // t ∈ K} × M ↦
        normSq0S (I := I) (g q.1.1) q.2 s (A q.1.1 q.2)) =ᶠ[nhds q₀]
      fun q ↦
        ∑ I₀ : Fin s → Fin (Module.finrank Real E),
          ∑ J₀ : Fin s → Fin (Module.finrank Real E),
            (∏ a : Fin s, (Gm q)⁻¹ (I₀ a) (J₀ a)) *
              (A q.1.1 q.2 (fun a : Fin s ↦ e.symmL Real q.2 (b (I₀ a)))) *
              (A q.1.1 q.2 (fun a : Fin s ↦ e.symmL Real q.2 (b (J₀ a)))) := by
    filter_upwards [hopen] with q hq
    have hinv : MetricInverseInBasis (I := I) (g q.1.1) q.2
        (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) q₀.2 hq)
        (fun i j ↦ (Gm q)⁻¹ i j) := by
      simpa only [Gm, chartInvGramMatrix] using
        chartInvGram_inverse (I := I) (g q.1.1) q₀.2 hq
    rw [normSq0S_eq_coord (I := I) (g q.1.1) q.2 s
      (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) q₀.2 hq)
      (fun i j ↦ (Gm q)⁻¹ i j) hinv (A q.1.1 q.2)]
    unfold coordInner0S
    refine Finset.sum_congr rfl fun I₀ _ ↦ Finset.sum_congr rfl fun J₀ _ ↦ ?_
    rw [tensor0SComponent_apply, tensor0SComponent_apply]
    have hI :
        (fun a : Fin s => DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) q₀.2 hq (I₀ a)) =
          fun a : Fin s => e.symmL Real q.2 (b (I₀ a)) := by
      funext a
      rw [DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply]
      rfl
    have hJ :
        (fun a : Fin s => DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) q₀.2 hq (J₀ a)) =
          fun a : Fin s => e.symmL Real q.2 (b (J₀ a)) := by
      funext a
      rw [DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply]
      rfl
    rw [hI, hJ]
  exact hF.congr hev.symm

theorem exists_normSq0S_le_of_isCompact
    {s : ℕ} {K : Set ℝ} {L : Set M}
    (g : ℝ → SmoothRiemannianMetric I M)
    (A : (t : ℝ) → (x : M) → Tensor0SSpace s I x)
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => metricTensorField (I := I) (g t) x))
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A)
    (hK : IsCompact K) (hL : IsCompact L) :
    ∃ C : ℝ, ∀ t ∈ K, ∀ x ∈ L, normSq0S (g t) x s (A t x) ≤ C := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc := continuous_normSq0S_family g A hg hA
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    ((isCompact_univ.prod hL).bddAbove_image hc.continuousOn)
  exact ⟨C, fun t ht x hx => hC _ ⟨(⟨t, ht⟩, x), ⟨mem_univ _, hx⟩, rfl⟩⟩

end DifferentialGeometry.Tensor0SBundle
