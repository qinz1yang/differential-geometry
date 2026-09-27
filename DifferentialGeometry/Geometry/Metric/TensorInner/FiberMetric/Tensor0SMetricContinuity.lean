import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]

theorem tensor0SField_eval_cmdAt_slots {s : ℕ}
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    {x₀ : M} (v : Fin s -> (∀ y : M, TangentSpace I y))
    (hv : ∀ a : Fin s, ContMDiffAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (fun y : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) y (v a y)) x₀) :
    ContMDiffAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun y : M => α y (fun a : Fin s => v a y)) x₀ := by
  have hα_top := α.contMDiff x₀
  have hEval := TensorMultilinear.contMDiffAt_section_apply
    (I := I) (M := M) (n := s) (x₀ := x₀)
    (T := fun y : M => α y) hα_top (v := v) (hv := hv)
  let h : ContMDiffAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun y : M => α y (fun a : Fin s => v a y)) x₀ := hEval
  exact h

section NormSqContinuity

variable (g : DifferentialGeometry.SmoothRiemannianMetric I M)

private noncomputable def gramMatrix (g : SmoothRiemannianMetric I M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (y : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j => g.inner y (e.localFrame b i y) (e.localFrame b j y)

omit [FiniteDimensional ℝ E] in
private theorem gramMatrix_det_ne_zero
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {y : M} (hy : y ∈ e.baseSet) :
    (gramMatrix (I := I) (M := M) g e b y).det ≠ 0 := by
  intro hdet0
  obtain ⟨c, hc0, hcv⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := gramMatrix (I := I) (M := M) g e b y)).2 hdet0
  set w : TangentSpace I y := ∑ i, c i • e.localFrame b i y with hw
  have hrow0 : ∀ i, (g.inner y (e.localFrame b i y)) w = 0 := by
    intro i
    have h1 : (g.inner y (e.localFrame b i y)) w =
        ∑ j, gramMatrix (I := I) (M := M) g e b y i j * c j := by
      rw [hw, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      simp only [gramMatrix, Matrix.of_apply]
    have h2 : (∑ j, gramMatrix (I := I) (M := M) g e b y i j * c j) = 0 := by
      simpa [Matrix.mulVec, dotProduct] using congrFun hcv i
    rw [h1, h2]
  have hinner : g.inner y w w = 0 := by
    have hout : (g.inner y) w = ∑ i, c i • ((g.inner y) (e.localFrame b i y)) := by
      rw [hw, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    calc g.inner y w w = (∑ i, c i • ((g.inner y) (e.localFrame b i y))) w := by rw [hout]
      _ = ∑ i, c i • ((g.inner y (e.localFrame b i y)) w) := by
          rw [sum_apply]
          exact Finset.sum_congr rfl fun i _ => by
            rw [smul_apply]
      _ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [hrow0 i, smul_zero]
  have hwne : w ≠ 0 := by
    intro hw0
    apply hc0
    have hz : ∑ i, c i • e.basisAt b hy i = 0 := by
      rw [← hw0, hw]
      exact Finset.sum_congr rfl fun i _ => by
        rw [e.localFrame_apply_of_mem_baseSet b hy]
    have hall := Fintype.linearIndependent_iff.1 (e.basisAt b hy).linearIndependent c hz
    funext i
    exact hall i
  exact absurd hinner (ne_of_gt (g.pos y w hwne))

omit [FiniteDimensional ℝ E] in
private theorem gramMatrix_metricInverseInBasis
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {y : M} (hy : y ∈ e.baseSet) :
    MetricInverseInBasis (I := I) g y (e.basisAt b hy)
      (fun i j => (gramMatrix (I := I) (M := M) g e b y)⁻¹ i j) := by
  have hunit : IsUnit (gramMatrix (I := I) (M := M) g e b y).det :=
    isUnit_iff_ne_zero.2 (gramMatrix_det_ne_zero (I := I) (M := M) g e b hy)
  have hGb : ∀ i' j' : Fin (Module.finrank ℝ E),
      g.inner y (e.basisAt b hy i') (e.basisAt b hy j') =
        gramMatrix (I := I) (M := M) g e b y i' j' := by
    intro i' j'
    simp [gramMatrix, e.localFrame_apply_of_mem_baseSet b hy]
  intro i j
  constructor
  · have : (∑ k, (gramMatrix (I := I) (M := M) g e b y)⁻¹ i k *
        gramMatrix (I := I) (M := M) g e b y k j) =
        ((gramMatrix (I := I) (M := M) g e b y)⁻¹ *
          gramMatrix (I := I) (M := M) g e b y) i j :=
      (Matrix.mul_apply).symm
    rw [Finset.sum_congr rfl fun k _ => by rw [hGb k j], this,
      Matrix.nonsing_inv_mul (gramMatrix (I := I) (M := M) g e b y) hunit, Matrix.one_apply]
  · have : (∑ k, gramMatrix (I := I) (M := M) g e b y i k *
        (gramMatrix (I := I) (M := M) g e b y)⁻¹ k j) =
        (gramMatrix (I := I) (M := M) g e b y *
          (gramMatrix (I := I) (M := M) g e b y)⁻¹) i j :=
      (Matrix.mul_apply).symm
    rw [Finset.sum_congr rfl fun k _ => by rw [hGb i k], this,
      Matrix.mul_nonsing_inv (gramMatrix (I := I) (M := M) g e b y) hunit, Matrix.one_apply]

private theorem continuousAt_gramMatrix_inv
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {x₀ : M} (hx₀ : x₀ ∈ e.baseSet) :
    ContinuousAt (fun y : M => (gramMatrix (I := I) (M := M) g e b y)⁻¹) x₀ := by
  have hGmEnt : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousAt (fun y : M => gramMatrix (I := I) (M := M) g e b y i j) x₀ := by
    intro i j
    have h2 := (tensor0SField_eval_cmdAt_slots (I := I) (M := M)
      (α := metricTensorField (I := I) g)
      (v := fun a y => e.localFrame b ((![i, j] : Fin 2 → Fin (Module.finrank ℝ E)) a) y)
      (hv := fun a => contMDiffAt_localFrame_of_mem (I := I)
        (n := (∞ : WithTop ℕ∞)) (e := e) (b := b)
        (i := (![i, j] : Fin 2 → Fin (Module.finrank ℝ E)) a) hx₀)).continuousAt
    have heq : (fun y : M => metricTensorField (I := I) g y
        (fun a : Fin 2 => e.localFrame b ((![i, j] : Fin 2 → _) a) y)) =
        fun y : M => gramMatrix (I := I) (M := M) g e b y i j := by
      funext y
      rw [metricTensorField_apply]
      simp [gramMatrix]
    rwa [heq] at h2
  have hGmc : ContinuousAt (gramMatrix (I := I) (M := M) g e b) x₀ :=
    continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => hGmEnt i j
  have hdetc : ContinuousAt (fun y => (gramMatrix (I := I) (M := M) g e b y).det) x₀ :=
    (continuous_id.matrix_det).continuousAt.comp hGmc
  have hadjc : ContinuousAt (fun y => (gramMatrix (I := I) (M := M) g e b y).adjugate) x₀ :=
    (continuous_id.matrix_adjugate).continuousAt.comp hGmc
  have h1 : ContinuousAt (fun y =>
      ((gramMatrix (I := I) (M := M) g e b y).det)⁻¹ •
        (gramMatrix (I := I) (M := M) g e b y).adjugate) x₀ :=
    (hdetc.inv₀ (gramMatrix_det_ne_zero (I := I) (M := M) g e b hx₀)).smul hadjc
  have hfun : (fun y => (gramMatrix (I := I) (M := M) g e b y)⁻¹) =
      fun y => ((gramMatrix (I := I) (M := M) g e b y).det)⁻¹ •
        (gramMatrix (I := I) (M := M) g e b y).adjugate := by
    funext y
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [hfun]
  exact h1

theorem normSq0S_contAt {s : ℕ}
    (T : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) :
    ContinuousAt (fun y : M => normSq0S (I := I) g y s (T y)) x₀ := by
  classical
  set e := trivializationAt E (TangentSpace I : M -> Type _) x₀ with he
  set b := Module.finBasis ℝ E with hb
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  set Gm : M -> Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun y => Matrix.of fun i j =>
      g.inner y (e.localFrame b i y) (e.localFrame b j y) with hGm
  have hslots : ∀ (s' : ℕ)
      (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s')
      (I0 : Fin s' -> Fin (Module.finrank ℝ E)),
      ContinuousAt (fun y : M => A y (fun a : Fin s' => e.localFrame b (I0 a) y)) x₀ := by
    intro s' A I0
    exact (tensor0SField_eval_cmdAt_slots (I := I) (M := M) (α := A)
      (v := fun a y => e.localFrame b (I0 a) y)
      (hv := fun a => contMDiffAt_localFrame_of_mem (I := I)
        (n := (∞ : WithTop ℕ∞)) (e := e) (b := b) (i := I0 a) hx₀)).continuousAt
  have hGinvEnt : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousAt (fun y => (Gm y)⁻¹ i j) x₀ := by
    intro i j
    have h := continuousAt_gramMatrix_inv (I := I) (M := M) g e b hx₀
    have h' : ContinuousAt (fun y : M =>
        (gramMatrix (I := I) (M := M) g e b y)⁻¹ i j) x₀ :=
      continuousAt_pi.1 (continuousAt_pi.1 h i) j
    simpa only [hGm, gramMatrix] using h'
  have hinvw : ∀ y (hy : y ∈ e.baseSet),
      MetricInverseInBasis (I := I) g y (e.basisAt b hy) (fun i j => (Gm y)⁻¹ i j) := by
    intro y hy
    have h := gramMatrix_metricInverseInBasis (I := I) (M := M) g e b hy
    simpa only [hGm, gramMatrix] using h
  have hF : ContinuousAt (fun y : M =>
      ∑ I0 : Fin s -> Fin (Module.finrank ℝ E),
        ∑ J0 : Fin s -> Fin (Module.finrank ℝ E),
          (∏ a : Fin s, (Gm y)⁻¹ (I0 a) (J0 a)) *
              (T y fun a : Fin s => e.localFrame b (I0 a) y) *
            (T y fun a : Fin s => e.localFrame b (J0 a) y)) x₀ := by
    refine tendsto_finsetSum _ fun I0 _ => tendsto_finsetSum _ fun J0 _ => ?_
    have hprod : ContinuousAt (fun y => ∏ a : Fin s, (Gm y)⁻¹ (I0 a) (J0 a)) x₀ :=
      tendsto_finsetProd _ fun a _ => hGinvEnt (I0 a) (J0 a)
    exact (hprod.mul (hslots s T I0)).mul (hslots s T J0)
  have hev : (fun y : M => normSq0S (I := I) g y s (T y)) =ᶠ[nhds x₀]
      fun y : M =>
        ∑ I0 : Fin s -> Fin (Module.finrank ℝ E),
          ∑ J0 : Fin s -> Fin (Module.finrank ℝ E),
            (∏ a : Fin s, (Gm y)⁻¹ (I0 a) (J0 a)) *
                (T y fun a : Fin s => e.localFrame b (I0 a) y) *
              (T y fun a : Fin s => e.localFrame b (J0 a) y) := by
    filter_upwards [e.open_baseSet.mem_nhds hx₀] with y hy
    rw [normSq0S_eq_coord (I := I) g y s (e.basisAt b hy)
      (fun i j => (Gm y)⁻¹ i j) (hinvw y hy) (T y)]
    unfold coordInner0S
    refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun J0 _ => ?_
    rw [tensor0SComponent_apply, tensor0SComponent_apply]
    have h1 : (T y) (fun a : Fin s => (e.basisAt b hy) (I0 a)) =
        (T y) fun a : Fin s => e.localFrame b (I0 a) y :=
      congrArg (T y) (funext fun a => (e.localFrame_apply_of_mem_baseSet b hy).symm)
    have h2 : (T y) (fun a : Fin s => (e.basisAt b hy) (J0 a)) =
        (T y) fun a : Fin s => e.localFrame b (J0 a) y :=
      congrArg (T y) (funext fun a => (e.localFrame_apply_of_mem_baseSet b hy).symm)
    rw [h1, h2]
  exact hF.congr hev.symm

theorem normSq0S_cont {s : ℕ}
    (T : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Continuous (fun y : M => normSq0S (I := I) g y s (T y)) :=
  continuous_iff_continuousAt.2 fun x₀ => normSq0S_contAt (I := I) g T x₀

theorem normSq0S_total_cont {s : ℕ} :
    Continuous (fun p : Bundle.TotalSpace (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) =>
      normSq0S (I := I) g p.proj s p.2) := by
  classical
  rw [continuous_iff_continuousAt]
  intro p₀
  set x₀ : M := p₀.proj with hx₀eq
  set e := trivializationAt E (TangentSpace I : M → Type _) x₀ with he
  set b := Module.finBasis ℝ E with hb
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  let P := Bundle.TotalSpace (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
  let Q := {p : P // p.proj ∈ e.baseSet}
  have hproj : Continuous (fun p : P => p.proj) := by
    simpa only [P] using
      (FiberBundle.continuous_proj (F := Tensor0SModel s ℝ E)
        (E := fun x : M => Tensor0SSpace s I x))
  have hbase : {p : P | p.proj ∈ e.baseSet} ∈ nhds p₀ :=
    hproj.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hx₀)
  have hbQ : Continuous (fun q : Q => q.1.proj) := hproj.comp continuous_subtype_val
  have hT : Continuous (fun q : Q => Bundle.TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun x : M => Tensor0SSpace s I x) q.1.proj q.1.2) := by
    have hfun : (fun q : Q => Bundle.TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun x : M => Tensor0SSpace s I x) q.1.proj q.1.2) =
        fun q : Q => q.1 := rfl
    rw [hfun]
    exact continuous_subtype_val
  have hslot : ∀ I0 : Fin s → Fin (Module.finrank ℝ E),
      Continuous (fun q : Q =>
        q.1.2 (fun a : Fin s => e.localFrame b (I0 a) q.1.proj)) := by
    intro I0
    refine TensorMultilinear.continuous_section_apply_base (𝕜 := ℝ) (I := I) (M := M)
      (fun q : Q => q.1.proj) hbQ (fun q : Q => q.1.2) hT
      (fun a q => e.localFrame b (I0 a) q.1.proj) ?_
    intro a
    have hsec : ContinuousOn (fun y : M => Bundle.TotalSpace.mk' E
        (E := fun x : M => TangentSpace I x) y (e.localFrame b (I0 a) y)) e.baseSet := by
      refine continuousOn_of_forall_continuousAt fun y hy => ?_
      exact (contMDiffAt_localFrame_of_mem (I := I) (n := (∞ : WithTop ℕ∞))
        (e := e) (b := b) (i := I0 a) hy).continuousAt
    exact hsec.comp_continuous hbQ (fun q => q.2)
  have hinv : ∀ i j : Fin (Module.finrank ℝ E), Continuous (fun q : Q =>
      (gramMatrix (I := I) (M := M) g e b q.1.proj)⁻¹ i j) := by
    intro i j
    have hcont : ContinuousOn (fun y : M =>
        (gramMatrix (I := I) (M := M) g e b y)⁻¹ i j) e.baseSet :=
      continuousOn_of_forall_continuousAt fun y hy =>
        continuousAt_pi.1 (continuousAt_pi.1
          (continuousAt_gramMatrix_inv (I := I) (M := M) g e b hy) i) j
    exact hcont.comp_continuous hbQ fun q => q.2
  have heq : (fun q : Q => normSq0S (I := I) g q.1.proj s q.1.2) =
      fun q : Q => ∑ I0 : Fin s → Fin (Module.finrank ℝ E),
        ∑ J0 : Fin s → Fin (Module.finrank ℝ E),
          (∏ a : Fin s, (gramMatrix (I := I) (M := M) g e b q.1.proj)⁻¹ (I0 a) (J0 a)) *
            q.1.2 (fun a : Fin s => e.localFrame b (I0 a) q.1.proj) *
            q.1.2 (fun a : Fin s => e.localFrame b (J0 a) q.1.proj) := by
    funext q
    rw [normSq0S_eq_coord (I := I) g q.1.proj s (e.basisAt b q.2)
      (fun i j => (gramMatrix (I := I) (M := M) g e b q.1.proj)⁻¹ i j)
      (gramMatrix_metricInverseInBasis (I := I) (M := M) g e b q.2) q.1.2]
    unfold coordInner0S
    refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun J0 _ => ?_
    rw [tensor0SComponent_apply, tensor0SComponent_apply]
    have h1 : q.1.2 (fun a : Fin s => (e.basisAt b q.2) (I0 a)) =
        q.1.2 (fun a : Fin s => e.localFrame b (I0 a) q.1.proj) :=
      congrArg (q.1.2) (funext fun a => (e.localFrame_apply_of_mem_baseSet b q.2).symm)
    have h2 : q.1.2 (fun a : Fin s => (e.basisAt b q.2) (J0 a)) =
        q.1.2 (fun a : Fin s => e.localFrame b (J0 a) q.1.proj) :=
      congrArg (q.1.2) (funext fun a => (e.localFrame_apply_of_mem_baseSet b q.2).symm)
    rw [h1, h2]
  have hQ : Continuous (fun q : Q => normSq0S (I := I) g q.1.proj s q.1.2) := by
    rw [heq]
    refine continuous_finsetSum _ fun I0 _ => continuous_finsetSum _ fun J0 _ => ?_
    have hprod : Continuous (fun q : Q =>
        ∏ a : Fin s, (gramMatrix (I := I) (M := M) g e b q.1.proj)⁻¹ (I0 a) (J0 a)) :=
      continuous_finsetProd _ fun a _ => hinv (I0 a) (J0 a)
    exact (hprod.mul (hslot I0)).mul (hslot J0)
  have hlocal : ContinuousOn (fun p : P => normSq0S (I := I) g p.proj s p.2)
      {p : P | p.proj ∈ e.baseSet} := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hQ
  exact hlocal.continuousAt hbase

end NormSqContinuity

end

end Tensor0SBundle
end DifferentialGeometry
