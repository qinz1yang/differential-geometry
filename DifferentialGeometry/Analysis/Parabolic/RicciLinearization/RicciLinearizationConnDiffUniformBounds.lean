import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CorrFieldChristoffelCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Geometry.Curvature.CovDerivConnDiffQuadraticBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Analysis.Elliptic.MetricBounds

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private def cdPerm2_10 : Equiv.Perm (Fin 2) :=
  ⟨![1, 0], ![1, 0], by decide, by decide⟩

private def cdPerm3_102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def cdPerm3_120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

private def cdPerm4_0312 : Equiv.Perm (Fin 4) :=
  ⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩

private def cdPerm4_0213 : Equiv.Perm (Fin 4) :=
  ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide, by decide⟩

private def cdPerm4_2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def cdPerm4_1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def cdPerm4_1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def cdPerm4_3012 : Equiv.Perm (Fin 4) :=
  ⟨![3, 0, 1, 2], ![1, 2, 3, 0], by decide, by decide⟩

private def cdPerm4_2013 : Equiv.Perm (Fin 4) :=
  ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩

private def cdPerm4_3201 : Equiv.Perm (Fin 4) :=
  ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

private def cdPerm4_3102 : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩

private def cdPerm4_2103 : Equiv.Perm (Fin 4) :=
  ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

private def cdPerm4_0231 : Equiv.Perm (Fin 4) :=
  ⟨![0, 2, 3, 1], ![0, 3, 1, 2], by decide, by decide⟩

private def cdPerm4_0321 : Equiv.Perm (Fin 4) :=
  ⟨![0, 3, 2, 1], ![0, 3, 2, 1], by decide, by decide⟩

section JointSmoothness

private theorem jointField_add {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_add (A p) (B p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)).symm

private theorem jointField_sub {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_sub (A p) (B p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)).symm

private theorem jointField_smul {d : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (a • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := a)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_smul a (A p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)).symm

private theorem jointField_neg {d : ℕ} {S : Set ℝ}
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (-A p))
      ((Set.univ : Set M) ×ˢ S) := by
  have h := jointField_smul (I := I) (M := M) (d := d) (S := S) (-1 : ℝ) A hA
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 t) ?_
  rw [neg_one_smul]

private theorem slotPermField_jointContMDiffOn {d : ℕ} (ρ : Equiv.Perm (Fin d)) {S : Set ℝ}
    (Z : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (Z p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1
        (slotPermCLM (I := I) ρ p.1 (Z p)))
      ((Set.univ : Set M) ×ˢ S) := by
  have h := domDomCongrField_jointContMDiffOn (I := I) ρ (S := S) Z hZ
  refine h.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 t)
    (slotPermCLM_apply (I := I) ρ p.1 (Z p))

set_option backward.isDefEq.respectTransparency false in

private theorem tensorProdField_jointContMDiffOn (m k : ℕ) {S : Set ℝ}
    (P : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace m I p.1)
    (Q : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace k I p.1)
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel m ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel m ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace m I z) p.1 (P p))
      ((Set.univ : Set M) ×ˢ S))
    (hQ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel k ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel k ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace k I z) p.1 (Q p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + k) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + k) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + k) I z) p.1
        (tensorProdWithCLM (I := I) m k p.1 (P p) (Q p)))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) m
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) k
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (m + k)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hP' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel m ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace m I z)).mp (hP p₀ hp₀)
  have hQ' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel k ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace k I z)).mp (hQ p₀ hp₀)
  have h_combine : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + k) ℝ E) ∞
      (fun p : M × ℝ => Bundle.continuousMultilinearMap.modelProductL (𝕜 := ℝ) (F := E) m k
        ((trivializationAt (Tensor0SBundle.Tensor0SModel m ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace m I z) x₀ ⟨p.1, P p⟩).2)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀ ⟨p.1, Q p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    ((contMDiffWithinAt_const (c := Bundle.continuousMultilinearMap.modelProductL
        (𝕜 := ℝ) (F := E) m k)).clm_apply hP'.2).clm_apply hQ'.2
  have hpointwise : ∀ p : M × ℝ,
      p.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
      (trivializationAt (Tensor0SBundle.Tensor0SModel (m + k) ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace (m + k) I z) x₀
        ⟨p.1, tensorProdWithCLM (I := I) m k p.1 (P p) (Q p)⟩).2 =
      Bundle.continuousMultilinearMap.modelProductL (𝕜 := ℝ) (F := E) m k
        ((trivializationAt (Tensor0SBundle.Tensor0SModel m ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace m I z) x₀ ⟨p.1, P p⟩).2)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀ ⟨p.1, Q p⟩).2) := by
    intro p hx
    apply ContinuousMultilinearMap.ext
    intro v
    rw [Bundle.continuousMultilinearMap.modelProductL_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    set symmL := (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.1 with hsymmL
    change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
        (Tensor0SBundle.Tensor0SSpace.toModel (P p))
        (Tensor0SBundle.Tensor0SSpace.toModel (Q p)))
        (fun i => symmL (v i)) = _
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl
  refine h_combine.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact hpointwise p hx
  · exact hpointwise p₀ (by rw [← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)

set_option backward.isDefEq.respectTransparency false in

private theorem connContrField_jointContMDiffOn (m k : ℕ) {S : Set ℝ}
    (Bf : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace 1 (k + 1) I p.1)
    (hBf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (k + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (k + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (k + 1) I z) p.1 (Bf p))
      ((Set.univ : Set M) ×ˢ S))
    (Df : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (m + 1) I p.1)
    (hDf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1) I z) p.1 (Df p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + 1 + k) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1 + k) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k) I z) p.1
        (connContrCLM (I := I) m k p.1 (Bf p) (Df p)))
      ((Set.univ : Set M) ×ˢ S) := by
  have hΨ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (m + 1 + k + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (m + 1 + k + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I z) p.1
        (show Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I p.1 from
          (tensorProdWithCLM (I := I) (m + 1) (k + 1) p.1 (Df p)).comp
            (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (k + 1) I p.1 from Bf p)))
      ((Set.univ : Set M) ×ˢ S) := by
    apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
      (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)
      (F₂ := Tensor0SBundle.Tensor0SModel (m + 1 + k + 1) ℝ E)
      (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k + 1) I z)
      (φ := fun p : M × ℝ =>
        (tensorProdWithCLM (I := I) (m + 1) (k + 1) p.1 (Df p)).comp
          (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (k + 1) I p.1 from Bf p))
      (S := S)
    intro om
    have homj : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) p.1 (om p.1))
        ((Set.univ : Set M) ×ˢ S) :=
      om.contMDiff.comp_contMDiffOn contMDiffOn_fst
    have hBom : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (k + 1) ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (k + 1) ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace (k + 1) I z) p.1
          ((show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (k + 1) I p.1 from Bf p) (om p.1)))
        ((Set.univ : Set M) ×ˢ S) :=
      ContMDiffOn.clm_bundle_apply (b := Prod.fst) hBf homj
    have hprod := tensorProdField_jointContMDiffOn (I := I) (M := M) (m + 1) (k + 1) (S := S)
      (fun p => Df p)
      (fun p => (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (k + 1) I p.1 from Bf p) (om p.1))
      hDf hBom
    refine hprod.congr (fun p _ => ?_)
    exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1 + k + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k + 1) I z) p.1 t) rfl
  have hTr := contractTraceField_jointContMDiffOn (I := I) 0 (m + 1 + k) (S := S)
    (fun p : M × ℝ =>
      (show Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I p.1 from
        (tensorProdWithCLM (I := I) (m + 1) (k + 1) p.1 (Df p)).comp
          (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (k + 1) I p.1 from Bf p)))
    hΨ
  have hunit : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) p.1
        (Integral.Connection.unitZeroSec (I := I) (M := M) p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    (Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hEval := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hTr hunit
  refine hEval.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1 + k) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k) I z) p.1 t) rfl

set_option backward.isDefEq.respectTransparency false in

private theorem connDiffSection_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 2 I z) p.1
        ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hCLM := contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun p : M × ℝ =>
      (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 from
          raisedKoszulFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1).comp
        ((g0FlatCLM (I := I) g₀ p.1).comp
          (inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)))
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun om => by
      have homj : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
            (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) p.1 (om p.1))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
        om.contMDiff.comp_contMDiffOn contMDiffOn_fst
      have hsharpom := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
        (inverseMetricSharpField_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') homj
      have hflatj : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
          (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
            (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) p.1
            (g0FlatCLM (I := I) g₀ p.1))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
        (g0FlatField_contMDiff (I := I) g₀).comp_contMDiffOn contMDiffOn_fst
      have hflatom := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hflatj hsharpom
      have hkosom := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
        (corrField_raisedKoszulFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') hflatom
      refine hkosom.congr (fun p _ => ?_)
      exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) rfl)
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 2 I z) p.1 t) ?_
  rw [connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' p.2)]
  rw [appCcRS_toSection, raisedKoszul_toSection, sharpFlatEndoCc_toSection]
  rfl

private theorem covGradConnDiff_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 3 I z) p.1
        ((covGrad (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀)).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have h := covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ 1 2
    (fun s => connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)
    (realizedSmallSet (δ := δ) (δ' := δ'))
    (connDiffSection_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ')
  exact h

set_option backward.isDefEq.respectTransparency false in

private theorem order1CLM_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Z : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 3 I p.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Z p))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1
        (linearizedRicciConnDiffOrder1CLM (I := I) p.1
          ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀).toSection p.1)
          (Z p)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  set S := realizedSmallSet (δ := δ) (δ' := δ') with hS
  set Af : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace 1 2 I p.1 :=
    fun p => (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀).toSection p.1
    with hAf
  have hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 2 I z) p.1 (Af p))
      ((Set.univ : Set M) ×ˢ S) :=
    connDiffSection_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hpre102 := slotPermField_jointContMDiffOn (I := I) cdPerm3_102 (S := S) Z hZ
  have hpre120 := slotPermField_jointContMDiffOn (I := I) cdPerm3_120 (S := S) Z hZ
  have h₁ := slotPermField_jointContMDiffOn (I := I) cdPerm4_0312 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_102 p.1 (Z p)) hpre102)
  have h₂ := slotPermField_jointContMDiffOn (I := I) cdPerm4_0213 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_120 p.1 (Z p)) hpre120)
  have h₃ := slotPermField_jointContMDiffOn (I := I) cdPerm4_2301 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA (fun p => Z p) hZ)
  have h₄ := slotPermField_jointContMDiffOn (I := I) cdPerm4_1302 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_102 p.1 (Z p)) hpre102)
  have h₅ := slotPermField_jointContMDiffOn (I := I) cdPerm4_1203 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_120 p.1 (Z p)) hpre120)
  have hsum := jointField_neg (I := I) (M := M) (d := 4) (S := S) _
    (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _
      (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _
        (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _
          (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _ h₁ h₂) h₃) h₄) h₅)
  refine hsum.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 t) rfl

set_option backward.isDefEq.respectTransparency false in

private theorem order0CLM_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Z : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 2 I p.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Z p))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1
        (linearizedRicciConnDiffOrder0CLM (I := I) p.1
          ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀).toSection p.1)
          ((covGrad (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀)).toSection p.1)
          (Z p)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  set S := realizedSmallSet (δ := δ) (δ' := δ') with hS
  set Af : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace 1 2 I p.1 :=
    fun p => (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀).toSection p.1
    with hAf
  set DAf : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace 1 3 I p.1 :=
    fun p => (covGrad (I := I) (M := M) g₀ 1 2
      (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀)).toSection p.1
    with hDAf
  have hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 2 I z) p.1 (Af p))
      ((Set.univ : Set M) ×ˢ S) :=
    connDiffSection_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hDA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 3 I z) p.1 (DAf p))
      ((Set.univ : Set M) ×ˢ S) :=
    covGradConnDiff_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hZswap := slotPermField_jointContMDiffOn (I := I) cdPerm2_10 (S := S) Z hZ
  have hinnJ := connContrField_jointContMDiffOn (I := I) 1 1 (S := S) Af hA (fun p => Z p) hZ
  have hinnJ' := connContrField_jointContMDiffOn (I := I) 1 1 (S := S) Af hA
    (fun p => slotPermCLM (I := I) cdPerm2_10 p.1 (Z p)) hZswap
  have hu₃ := slotPermField_jointContMDiffOn (I := I) cdPerm4_3201 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_102 p.1
        (connContrCLM (I := I) 1 1 p.1 (Af p) (Z p)))
      (slotPermField_jointContMDiffOn (I := I) cdPerm3_102 (S := S) _ hinnJ))
  have hu₄ := slotPermField_jointContMDiffOn (I := I) cdPerm4_2301 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_102 p.1
        (connContrCLM (I := I) 1 1 p.1 (Af p) (slotPermCLM (I := I) cdPerm2_10 p.1 (Z p))))
      (slotPermField_jointContMDiffOn (I := I) cdPerm3_102 (S := S) _ hinnJ'))
  have hu₅ := slotPermField_jointContMDiffOn (I := I) cdPerm4_3102 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_120 p.1
        (connContrCLM (I := I) 1 1 p.1 (Af p) (Z p)))
      (slotPermField_jointContMDiffOn (I := I) cdPerm3_120 (S := S) _ hinnJ))
  have hu₆ := slotPermField_jointContMDiffOn (I := I) cdPerm4_1302 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => connContrCLM (I := I) 1 1 p.1 (Af p) (slotPermCLM (I := I) cdPerm2_10 p.1 (Z p)))
      hinnJ')
  have hu₇ := slotPermField_jointContMDiffOn (I := I) cdPerm4_1203 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => connContrCLM (I := I) 1 1 p.1 (Af p) (Z p))
      hinnJ)
  have hu₈ := slotPermField_jointContMDiffOn (I := I) cdPerm4_2103 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_120 p.1
        (connContrCLM (I := I) 1 1 p.1 (Af p) (slotPermCLM (I := I) cdPerm2_10 p.1 (Z p))))
      (slotPermField_jointContMDiffOn (I := I) cdPerm3_120 (S := S) _ hinnJ'))
  have hu₁ := slotPermField_jointContMDiffOn (I := I) cdPerm4_3012 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 1 2 (S := S) DAf hDA (fun p => Z p) hZ)
  have hu₂ := slotPermField_jointContMDiffOn (I := I) cdPerm4_2013 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 1 2 (S := S) DAf hDA
      (fun p => slotPermCLM (I := I) cdPerm2_10 p.1 (Z p)) hZswap)
  have hsum := jointField_sub (I := I) (M := M) (d := 4) (S := S) _ _
    (jointField_sub (I := I) (M := M) (d := 4) (S := S) _ _
      (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _
        (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _
          (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _
            (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _
              (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _ hu₃ hu₄) hu₅) hu₆) hu₇)
        hu₈) hu₁) hu₂
  refine hsum.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 t) rfl

set_option backward.isDefEq.respectTransparency false in

private theorem fourTrace_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Z : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 4 I p.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 (Z p))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (ricciCometricFourTraceCLM (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Z p)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  set S := realizedSmallSet (δ := δ) (δ' := δ') with hS
  have ha := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p => slotPermCLM (I := I) cdPerm4_0231 p.1 (Z p))
    (slotPermField_jointContMDiffOn (I := I) cdPerm4_0231 (S := S) Z hZ)
  have hb := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p => slotPermCLM (I := I) cdPerm4_0321 p.1 (Z p))
    (slotPermField_jointContMDiffOn (I := I) cdPerm4_0321 (S := S) Z hZ)
  have hc := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p => Z p) hZ
  have hd := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p => slotPermCLM (I := I) cdPerm4_2301 p.1 (Z p))
    (slotPermField_jointContMDiffOn (I := I) cdPerm4_2301 (S := S) Z hZ)
  have hcomb := jointField_smul (I := I) (M := M) (d := 2) (S := S) ((1 : ℝ) / 2) _
    (jointField_sub (I := I) (M := M) (d := 2) (S := S) _ _
      (jointField_sub (I := I) (M := M) (d := 2) (S := S) _ _
        (jointField_add (I := I) (M := M) (d := 2) (S := S) _ _ ha hb) hc) hd)
  refine hcomb.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) rfl

set_option backward.isDefEq.respectTransparency false in

theorem linearizedRicciConnDiffOrder1Fib_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1
        (linearizedRicciConnDiffOrder1Fib (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun p : M × ℝ => linearizedRicciConnDiffOrder1Fib (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  have hYj : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hE1 := order1CLM_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    (fun p => Y p.1) hYj
  have hCK := fourTrace_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    (fun p => linearizedRicciConnDiffOrder1CLM (I := I) p.1
      ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀).toSection p.1)
      (Y p.1))
    hE1
  refine hCK.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 8000 in

theorem linearizedRicciConnDiffOrder0Fib_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (linearizedRicciConnDiffOrder0Fib (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun p : M × ℝ => linearizedRicciConnDiffOrder0Fib (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  have hYj : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hE0 := order0CLM_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    (fun p => Y p.1) hYj
  have hCK := fourTrace_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    (fun p => linearizedRicciConnDiffOrder0CLM (I := I) p.1
      ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀).toSection p.1)
      ((covGrad (I := I) (M := M) g₀ 1 2
          (connDiffSection (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀)).toSection p.1)
      (Y p.1))
    hE0
  refine hCK.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) rfl

set_option linter.unusedSectionVars false in

theorem linearizedRicciConnDiffOrder0Coeff_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ') (δ := δ) (δ' := δ') := by
  have h := linearizedRicciConnDiffOrder0Fib_realizedFam_jointContMDiffOn
    (I := I) g₀ T T' hδ hδ'
  refine h.congr (fun p _ => ?_)
  rfl

set_option linter.unusedSectionVars false in

theorem linearizedRicciConnDiffOrder1Coeff_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ') (δ := δ) (δ' := δ') := by
  have h := linearizedRicciConnDiffOrder1Fib_realizedFam_jointContMDiffOn
    (I := I) g₀ T T' hδ hδ'
  refine h.congr (fun p _ => ?_)
  rfl

end JointSmoothness

section UniformBound

set_option linter.unusedSectionVars false in

private lemma flat_toModel_apply (g₀ : SmoothRiemannianMetric I M) (x : M)
    (uu : TangentSpace I x) (v : Fin 1 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x uu) v =
      g₀.inner x uu ((v 0 : E) : TangentSpace I x) := by
  have h1 : Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x uu) v =
      (g0FlatCLM (I := I) g₀ x uu) (fun j : Fin 1 => ((v j : E) : TangentSpace I x)) := rfl
  rw [h1]
  have h2 : (fun j : Fin 1 => ((v j : E) : TangentSpace I x)) =
      (fun _ : Fin 1 => ((v 0 : E) : TangentSpace I x)) := by
    funext j
    fin_cases j
    rfl
  rw [h2]
  rw [show (g0FlatCLM (I := I) g₀ x uu) (fun _ : Fin 1 => ((v 0 : E) : TangentSpace I x)) =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x uu) ((v 0 : E) : TangentSpace I x)
    from (cotangentToDual_apply (I := I) (x := x) _ _).symm]
  rw [cotangentToDual_g0FlatCLM]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in

private lemma dualPair_sum_swap (g₀ : SmoothRiemannianMetric I M) (x : M)
    (F : Tensor0SBundle.Tensor0SModel 1 ℝ E → E → ℝ)
    (hFβ : ∀ z : E, IsLinearMap ℝ (fun β => F β z))
    (hFz : ∀ β, IsLinearMap ℝ (fun z : E => F β z))
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a) :
    (∑ i : Fin (Module.finrank ℝ E),
        F (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i)) ((Module.finBasis ℝ E) i)) =
      ∑ a : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E)) := by
  classical
  have hcdual : ∀ i : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).cDualBasis i) =
        LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i) := by
    intro i
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) i
  have hexp : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis i) =
        ∑ a : Fin n, ((Module.finBasis ℝ E).coord i ((e a : E))) •
          Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a)) := by
    intro i
    apply ContinuousMultilinearMap.ext
    intro v
    rw [Tensor0SBundle.model_covectorOfCLM_apply, hcdual i]
    have hRHS : (∑ a : Fin n, ((Module.finBasis ℝ E).coord i ((e a : E))) •
          Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) v =
        ∑ a : Fin n, ((Module.finBasis ℝ E).coord i ((e a : E))) *
          g₀.inner x (e a) ((v 0 : E) : TangentSpace I x) := by
      rw [ContinuousMultilinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [ContinuousMultilinearMap.smul_apply, flat_toModel_apply, smul_eq_mul]
    rw [hRHS]
    have hv0 : ((v 0 : E) : TangentSpace I x) =
        ∑ a : Fin n, g₀.inner x (e a) ((v 0 : E) : TangentSpace I x) • e a :=
      hrepr ((v 0 : E) : TangentSpace I x)
    calc LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i) (v 0)
        = (Module.finBasis ℝ E).coord i (v 0) := rfl
      _ = (Module.finBasis ℝ E).coord i
            (∑ a : Fin n, g₀.inner x (e a) ((v 0 : E) : TangentSpace I x) • ((e a : E))) := by
          exact congrArg ((Module.finBasis ℝ E).coord i) hv0
      _ = ∑ a : Fin n, g₀.inner x (e a) ((v 0 : E) : TangentSpace I x) *
            (Module.finBasis ℝ E).coord i ((e a : E)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [map_smul, smul_eq_mul]
      _ = ∑ a : Fin n, (Module.finBasis ℝ E).coord i ((e a : E)) *
            g₀.inner x (e a) ((v 0 : E) : TangentSpace I x) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          ring
  calc (∑ i : Fin (Module.finrank ℝ E),
        F (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i)) ((Module.finBasis ℝ E) i))
      = ∑ i : Fin (Module.finrank ℝ E), ∑ a : Fin n,
          ((Module.finBasis ℝ E).coord i ((e a : E))) *
            F (Tensor0SBundle.Tensor0SSpace.toModel
                (g0FlatCLM (I := I) g₀ x (e a))) ((Module.finBasis ℝ E) i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hexp i]
        set ℓ := IsLinearMap.mk' (fun β => F β ((Module.finBasis ℝ E) i))
          (hFβ ((Module.finBasis ℝ E) i)) with hℓ
        have hFℓ : ∀ β, F β ((Module.finBasis ℝ E) i) = ℓ β := fun β => rfl
        rw [hFℓ, map_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [map_smul, smul_eq_mul, ← hFℓ]
    _ = ∑ a : Fin n, ∑ i : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).coord i ((e a : E))) *
            F (Tensor0SBundle.Tensor0SSpace.toModel
                (g0FlatCLM (I := I) g₀ x (e a))) ((Module.finBasis ℝ E) i) :=
        Finset.sum_comm
    _ = ∑ a : Fin n,
          F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E)) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        set ℓ := IsLinearMap.mk'
          (fun z : E => F (Tensor0SBundle.Tensor0SSpace.toModel
            (g0FlatCLM (I := I) g₀ x (e a))) z)
          (hFz (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a)))) with hℓ
        have hFℓ : ∀ z, F (Tensor0SBundle.Tensor0SSpace.toModel
            (g0FlatCLM (I := I) g₀ x (e a))) z = ℓ z := fun z => rfl
        calc (∑ i : Fin (Module.finrank ℝ E),
              ((Module.finBasis ℝ E).coord i ((e a : E))) *
                F (Tensor0SBundle.Tensor0SSpace.toModel
                    (g0FlatCLM (I := I) g₀ x (e a))) ((Module.finBasis ℝ E) i))
            = ∑ i : Fin (Module.finrank ℝ E),
                ℓ (((Module.finBasis ℝ E).coord i ((e a : E))) • (Module.finBasis ℝ E) i) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [map_smul, smul_eq_mul, ← hFℓ]
          _ = ℓ (∑ i : Fin (Module.finrank ℝ E),
                ((Module.finBasis ℝ E).coord i ((e a : E))) • (Module.finBasis ℝ E) i) :=
              (map_sum ℓ _ _).symm
          _ = F (Tensor0SBundle.Tensor0SSpace.toModel
                (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E)) := by
              rw [← hFℓ]
              congr 1
              have hbe := (Module.finBasis ℝ E).sum_repr ((e a : E))
              calc (∑ i : Fin (Module.finrank ℝ E),
                    ((Module.finBasis ℝ E).coord i ((e a : E))) • (Module.finBasis ℝ E) i)
                  = ∑ i : Fin (Module.finrank ℝ E),
                      ((Module.finBasis ℝ E).repr ((e a : E)) i) • (Module.finBasis ℝ E) i := by
                    refine Finset.sum_congr rfl (fun i _ => ?_)
                    rw [Module.Basis.coord_apply]
                _ = (e a : E) := hbe

private def fibPointwiseBound (g₀ : SmoothRiemannianMetric I M) (x : M) (d : ℕ) (c : ℝ)
    (Z : Tensor0SBundle.Tensor0SSpace d I x) : Prop :=
  0 ≤ c ∧ ∀ w : Fin d → TangentSpace I x,
    |Tensor0SBundle.Tensor0SSpace.toModel Z (fun j => (w j : E))| ≤
      c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j))

set_option linter.unusedSectionVars false in

private lemma fibPointwiseBound_coframe (g₀ : SmoothRiemannianMetric I M) (x : M) (d : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin d → Fin n) :
    fibPointwiseBound (I := I) g₀ x d 1 (coframeS (I := I) (M := M) g₀ x d e K) := by
  refine ⟨zero_le_one, ?_⟩
  intro w
  have hval : Tensor0SBundle.Tensor0SSpace.toModel
      (coframeS (I := I) (M := M) g₀ x d e K) (fun j => (w j : E)) =
      coframeS (I := I) (M := M) g₀ x d e K (fun j => w j) := rfl
  rw [hval, coframeS_apply, one_mul, Finset.abs_prod]
  refine Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => ?_)
  have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (K j)) (w j)
  have h1 : g₀.inner x (e (K j)) (e (K j)) = 1 := by rw [horth (K j) (K j)]; simp
  rw [h1, Real.sqrt_one, one_mul] at hcs
  exact hcs

set_option linter.unusedSectionVars false in

private lemma fibPointwiseBound_slotPerm (g₀ : SmoothRiemannianMetric I M) (x : M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) {c : ℝ} {Z : Tensor0SBundle.Tensor0SSpace d I x}
    (hZ : fibPointwiseBound (I := I) g₀ x d c Z) :
    fibPointwiseBound (I := I) g₀ x d c (slotPermCLM (I := I) ρ x Z) := by
  refine ⟨hZ.1, ?_⟩
  intro w
  have hsp : Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) ρ x Z)
      (fun j => (w j : E)) =
      (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Z))
        (fun j => (w j : E)) := by
    rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [hsp, ContinuousMultilinearMap.domDomCongr_apply]
  have hb := hZ.2 (fun j => w (ρ j))
  refine le_trans hb (le_of_eq ?_)
  congr 1
  exact Equiv.prod_comp ρ (fun j => Real.sqrt (g₀.inner x (w j) (w j)))

set_option linter.unusedSectionVars false in

private lemma fibPointwiseBound_prod_nonneg (g₀ : SmoothRiemannianMetric I M) (x : M) {d : ℕ}
    (w : Fin d → TangentSpace I x) :
    0 ≤ ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) :=
  Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)

set_option linter.unusedSectionVars false in

private lemma connDiff_flat_factor_bound (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    {CA : ℝ}
    (hpwA : ∀ v w : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w)) ≤
        CA * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w))
    (a : Fin n) (v : Fin 2 → TangentSpace I x) :
    |(Tensor0SBundle.TensorRSSpace.toModel (connDiffFib (I := I) g₁ g₀ x)
        (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
        (fun j => (v j : E))| ≤
      CA * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1))) := by
  have h1 : Tensor0SBundle.TensorRSSpace.toModel (connDiffFib (I := I) g₁ g₀ x)
      (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          connDiffFib (I := I) g₁ g₀ x) (g0FlatCLM (I := I) g₀ x (e a))) :=
    (toModel_tensorRS_apply (I := I) 1 2 x (connDiffFib (I := I) g₁ g₀ x)
      (g0FlatCLM (I := I) g₀ x (e a))).symm
  rw [h1]
  have h2 : Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) (g0FlatCLM (I := I) g₀ x (e a)))
      (fun j => (v j : E)) =
      ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) (g0FlatCLM (I := I) g₀ x (e a))) (fun j => v j) := rfl
  rw [h2, connDiffFib_apply_eval]
  rw [show (g0FlatCLM (I := I) g₀ x (e a))
      (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) (v 1)) =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x (e a))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) (v 1)) from
    (cotangentToDual_apply (I := I) (x := x) _ _).symm]
  rw [cotangentToDual_g0FlatCLM]
  have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e a)
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) (v 1))
  have h1a : g₀.inner x (e a) (e a) = 1 := by rw [horth a a]; simp
  rw [h1a, Real.sqrt_one, one_mul] at hcs
  refine le_trans hcs (le_trans (hpwA (v 0) (v 1)) (le_of_eq ?_))
  ring

set_option linter.unusedSectionVars false in

private lemma fibPointwiseBound_connContr21 (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a)
    (B : Tensor0SBundle.TensorRSSpace 1 2 I x) {CB : ℝ} (hCB : 0 ≤ CB)
    (hB : ∀ (a : Fin n) (v : Fin 2 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel B
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        CB * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1))))
    {c : ℝ} {D : Tensor0SBundle.Tensor0SSpace 3 I x}
    (hD : fibPointwiseBound (I := I) g₀ x 3 c D) :
    fibPointwiseBound (I := I) g₀ x 4 ((n : ℝ) * CB * c) (connContrCLM (I := I) 2 1 x B D) := by
  refine ⟨mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCB) hD.1, ?_⟩
  intro w
  rw [connContrCLM_toModel_apply (I := I) 2 1 x B D (fun j => (w j : E))]
  have hfirst : ∀ z : E,
      (Fin.cons z (fun j => (w j : E)) ∘ Fin.castAdd 2 : Fin 3 → E) =
        ![z, (w 0 : E), (w 1 : E)] := by
    intro z
    funext j
    fin_cases j <;> rfl
  have hlast : ∀ z : E,
      (Fin.cons z (fun j => (w j : E)) ∘ Fin.natAdd 3 : Fin 2 → E) =
        ![(w 2 : E), (w 3 : E)] := by
    intro z
    funext j
    fin_cases j <;> rfl
  simp only [hfirst, hlast]
  set F : Tensor0SBundle.Tensor0SModel 1 ℝ E → E → ℝ := fun β z =>
    Tensor0SBundle.Tensor0SSpace.toModel D ![z, (w 0 : E), (w 1 : E)] *
      (Tensor0SBundle.TensorRSSpace.toModel B β) ![(w 2 : E), (w 3 : E)] with hF
  have hFβ : ∀ z : E, IsLinearMap ℝ (fun β => F β z) := by
    intro z
    constructor
    · intro β₁ β₂
      rw [hF]
      simp only [map_add, ContinuousMultilinearMap.add_apply, mul_add]
    · intro cc β
      rw [hF]
      simp only [map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring
  have hFz : ∀ β, IsLinearMap ℝ (fun z : E => F β z) := by
    intro β
    constructor
    · intro z₁ z₂
      rw [hF]
      simp only
      rw [show (![z₁ + z₂, (w 0 : E), (w 1 : E)] : Fin 3 → E) =
          Fin.cons (z₁ + z₂) ![(w 0 : E), (w 1 : E)] from rfl]
      rw [show (![z₁, (w 0 : E), (w 1 : E)] : Fin 3 → E) =
          Fin.cons z₁ ![(w 0 : E), (w 1 : E)] from rfl]
      rw [show (![z₂, (w 0 : E), (w 1 : E)] : Fin 3 → E) =
          Fin.cons z₂ ![(w 0 : E), (w 1 : E)] from rfl]
      rw [show Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons (z₁ + z₂) ![(w 0 : E), (w 1 : E)]) =
          Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z₁ ![(w 0 : E), (w 1 : E)]) +
            Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z₂ ![(w 0 : E), (w 1 : E)]) from
        (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.cons_add _ z₁ z₂]
      ring
    · intro cc z
      rw [hF]
      simp only
      rw [show (![cc • z, (w 0 : E), (w 1 : E)] : Fin 3 → E) =
          Fin.cons (cc • z) ![(w 0 : E), (w 1 : E)] from rfl]
      rw [show (![z, (w 0 : E), (w 1 : E)] : Fin 3 → E) =
          Fin.cons z ![(w 0 : E), (w 1 : E)] from rfl]
      rw [show Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons (cc • z) ![(w 0 : E), (w 1 : E)]) =
          cc • Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z ![(w 0 : E), (w 1 : E)]) from
        (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.cons_smul _ cc z]
      rw [smul_eq_mul, smul_eq_mul]
      ring
  rw [show (∑ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D ![((Module.finBasis ℝ E) i), (w 0 : E), (w 1 : E)] *
        (Tensor0SBundle.TensorRSSpace.toModel B
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i)))
          ![(w 2 : E), (w 3 : E)]) =
      ∑ a : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E)) from
    dualPair_sum_swap (I := I) g₀ x F hFβ hFz e horth hrepr]
  have hterm : ∀ a : Fin n,
      |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))| ≤
        CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
    intro a
    rw [hF]
    simp only
    rw [abs_mul]
    have hDterm : |Tensor0SBundle.Tensor0SSpace.toModel D ![((e a : E)), (w 0 : E), (w 1 : E)]| ≤
        c * (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) := by
      have harg : (![((e a : E)), (w 0 : E), (w 1 : E)] : Fin 3 → E) =
          (fun j => ((![e a, w 0, w 1] : Fin 3 → TangentSpace I x) j : E)) := by
        funext j
        fin_cases j <;> rfl
      rw [harg]
      have hb := hD.2 ![e a, w 0, w 1]
      have hprod : (∏ j, Real.sqrt (g₀.inner x ((![e a, w 0, w 1] : Fin 3 → TangentSpace I x) j)
          ((![e a, w 0, w 1] : Fin 3 → TangentSpace I x) j))) =
          Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1)) := by
        rw [Fin.prod_univ_three]
        have h1a : g₀.inner x (e a) (e a) = 1 := by rw [horth a a]; simp
        rw [show ((![e a, w 0, w 1] : Fin 3 → TangentSpace I x) 0) = e a from rfl,
          show ((![e a, w 0, w 1] : Fin 3 → TangentSpace I x) 1) = w 0 from rfl,
          show ((![e a, w 0, w 1] : Fin 3 → TangentSpace I x) 2) = w 1 from rfl,
          h1a, Real.sqrt_one, one_mul]
      rw [hprod] at hb
      exact hb
    have hBterm : |(Tensor0SBundle.TensorRSSpace.toModel B
        (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
        ![(w 2 : E), (w 3 : E)]| ≤
        CB * (Real.sqrt (g₀.inner x (w 2) (w 2)) * Real.sqrt (g₀.inner x (w 3) (w 3))) := by
      have harg : (![(w 2 : E), (w 3 : E)] : Fin 2 → E) =
          (fun j => ((![w 2, w 3] : Fin 2 → TangentSpace I x) j : E)) := by
        funext j
        fin_cases j <;> rfl
      rw [harg]
      exact hB a ![w 2, w 3]
    calc |Tensor0SBundle.Tensor0SSpace.toModel D ![((e a : E)), (w 0 : E), (w 1 : E)]| *
          |(Tensor0SBundle.TensorRSSpace.toModel B
              (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
              ![(w 2 : E), (w 3 : E)]|
        ≤ (c * (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1)))) *
            (CB * (Real.sqrt (g₀.inner x (w 2) (w 2)) * Real.sqrt (g₀.inner x (w 3) (w 3)))) :=
          mul_le_mul hDterm hBterm (abs_nonneg _)
            (mul_nonneg hD.1 (by positivity))
      _ = CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
          rw [Fin.prod_univ_four]
          ring
  calc |∑ a : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))|
      ≤ ∑ a : Fin n,
          |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin n, CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) :=
        Finset.sum_le_sum (fun a _ => hterm a)
    _ = (n : ℝ) * CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

set_option linter.unusedSectionVars false in

private lemma fibPointwiseBound_connContr11 (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a)
    (B : Tensor0SBundle.TensorRSSpace 1 2 I x) {CB : ℝ} (hCB : 0 ≤ CB)
    (hB : ∀ (a : Fin n) (v : Fin 2 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel B
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        CB * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1))))
    {c : ℝ} {D : Tensor0SBundle.Tensor0SSpace 2 I x}
    (hD : fibPointwiseBound (I := I) g₀ x 2 c D) :
    fibPointwiseBound (I := I) g₀ x 3 ((n : ℝ) * CB * c) (connContrCLM (I := I) 1 1 x B D) := by
  refine ⟨mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCB) hD.1, ?_⟩
  intro w
  rw [connContrCLM_toModel_apply (I := I) 1 1 x B D (fun j => (w j : E))]
  have hfirst : ∀ z : E,
      (Fin.cons z (fun j => (w j : E)) ∘ Fin.castAdd 2 : Fin 2 → E) = ![z, (w 0 : E)] := by
    intro z
    funext j
    fin_cases j <;> rfl
  have hlast : ∀ z : E,
      (Fin.cons z (fun j => (w j : E)) ∘ Fin.natAdd 2 : Fin 2 → E) =
        ![(w 1 : E), (w 2 : E)] := by
    intro z
    funext j
    fin_cases j <;> rfl
  simp only [hfirst, hlast]
  set F : Tensor0SBundle.Tensor0SModel 1 ℝ E → E → ℝ := fun β z =>
    Tensor0SBundle.Tensor0SSpace.toModel D ![z, (w 0 : E)] *
      (Tensor0SBundle.TensorRSSpace.toModel B β) ![(w 1 : E), (w 2 : E)] with hF
  have hFβ : ∀ z : E, IsLinearMap ℝ (fun β => F β z) := by
    intro z
    constructor
    · intro β₁ β₂
      rw [hF]
      simp only [map_add, ContinuousMultilinearMap.add_apply, mul_add]
    · intro cc β
      rw [hF]
      simp only [map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring
  have hFz : ∀ β, IsLinearMap ℝ (fun z : E => F β z) := by
    intro β
    constructor
    · intro z₁ z₂
      rw [hF]
      simp only
      rw [show (![z₁ + z₂, (w 0 : E)] : Fin 2 → E) = Fin.cons (z₁ + z₂) ![(w 0 : E)] from rfl,
        show (![z₁, (w 0 : E)] : Fin 2 → E) = Fin.cons z₁ ![(w 0 : E)] from rfl,
        show (![z₂, (w 0 : E)] : Fin 2 → E) = Fin.cons z₂ ![(w 0 : E)] from rfl]
      rw [show Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons (z₁ + z₂) ![(w 0 : E)]) =
          Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z₁ ![(w 0 : E)]) +
            Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z₂ ![(w 0 : E)]) from
        (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.cons_add _ z₁ z₂]
      ring
    · intro cc z
      rw [hF]
      simp only
      rw [show (![cc • z, (w 0 : E)] : Fin 2 → E) = Fin.cons (cc • z) ![(w 0 : E)] from rfl,
        show (![z, (w 0 : E)] : Fin 2 → E) = Fin.cons z ![(w 0 : E)] from rfl]
      rw [show Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons (cc • z) ![(w 0 : E)]) =
          cc • Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z ![(w 0 : E)]) from
        (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.cons_smul _ cc z]
      rw [smul_eq_mul, smul_eq_mul]
      ring
  rw [show (∑ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D ![((Module.finBasis ℝ E) i), (w 0 : E)] *
        (Tensor0SBundle.TensorRSSpace.toModel B
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i)))
          ![(w 1 : E), (w 2 : E)]) =
      ∑ a : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E)) from
    dualPair_sum_swap (I := I) g₀ x F hFβ hFz e horth hrepr]
  have hterm : ∀ a : Fin n,
      |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))| ≤
        CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
    intro a
    rw [hF]
    simp only
    rw [abs_mul]
    have hDterm : |Tensor0SBundle.Tensor0SSpace.toModel D ![((e a : E)), (w 0 : E)]| ≤
        c * Real.sqrt (g₀.inner x (w 0) (w 0)) := by
      have harg : (![((e a : E)), (w 0 : E)] : Fin 2 → E) =
          (fun j => ((![e a, w 0] : Fin 2 → TangentSpace I x) j : E)) := by
        funext j
        fin_cases j <;> rfl
      rw [harg]
      have hb := hD.2 ![e a, w 0]
      have hprod : (∏ j, Real.sqrt (g₀.inner x ((![e a, w 0] : Fin 2 → TangentSpace I x) j)
          ((![e a, w 0] : Fin 2 → TangentSpace I x) j))) =
          Real.sqrt (g₀.inner x (w 0) (w 0)) := by
        rw [Fin.prod_univ_two]
        have h1a : g₀.inner x (e a) (e a) = 1 := by rw [horth a a]; simp
        rw [show ((![e a, w 0] : Fin 2 → TangentSpace I x) 0) = e a from rfl,
          show ((![e a, w 0] : Fin 2 → TangentSpace I x) 1) = w 0 from rfl,
          h1a, Real.sqrt_one, one_mul]
      rw [hprod] at hb
      exact hb
    have hBterm : |(Tensor0SBundle.TensorRSSpace.toModel B
        (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
        ![(w 1 : E), (w 2 : E)]| ≤
        CB * (Real.sqrt (g₀.inner x (w 1) (w 1)) * Real.sqrt (g₀.inner x (w 2) (w 2))) := by
      have harg : (![(w 1 : E), (w 2 : E)] : Fin 2 → E) =
          (fun j => ((![w 1, w 2] : Fin 2 → TangentSpace I x) j : E)) := by
        funext j
        fin_cases j <;> rfl
      rw [harg]
      exact hB a ![w 1, w 2]
    calc |Tensor0SBundle.Tensor0SSpace.toModel D ![((e a : E)), (w 0 : E)]| *
          |(Tensor0SBundle.TensorRSSpace.toModel B
              (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
              ![(w 1 : E), (w 2 : E)]|
        ≤ (c * Real.sqrt (g₀.inner x (w 0) (w 0))) *
            (CB * (Real.sqrt (g₀.inner x (w 1) (w 1)) * Real.sqrt (g₀.inner x (w 2) (w 2)))) :=
          mul_le_mul hDterm hBterm (abs_nonneg _)
            (mul_nonneg hD.1 (by positivity))
      _ = CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
          rw [Fin.prod_univ_three]
          ring
  calc |∑ a : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))|
      ≤ ∑ a : Fin n,
          |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin n, CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) :=
        Finset.sum_le_sum (fun a _ => hterm a)
    _ = (n : ℝ) * CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

set_option linter.unusedSectionVars false in

private lemma fibPointwiseBound_connContr12 (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a)
    (B : Tensor0SBundle.TensorRSSpace 1 3 I x) {CB : ℝ} (hCB : 0 ≤ CB)
    (hB : ∀ (a : Fin n) (v : Fin 3 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel B
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        CB * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1)) *
          Real.sqrt (g₀.inner x (v 2) (v 2))))
    {c : ℝ} {D : Tensor0SBundle.Tensor0SSpace 2 I x}
    (hD : fibPointwiseBound (I := I) g₀ x 2 c D) :
    fibPointwiseBound (I := I) g₀ x 4 ((n : ℝ) * CB * c) (connContrCLM (I := I) 1 2 x B D) := by
  refine ⟨mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCB) hD.1, ?_⟩
  intro w
  rw [connContrCLM_toModel_apply (I := I) 1 2 x B D (fun j => (w j : E))]
  have hfirst : ∀ z : E,
      (Fin.cons z (fun j => (w j : E)) ∘ Fin.castAdd 3 : Fin 2 → E) = ![z, (w 0 : E)] := by
    intro z
    funext j
    fin_cases j <;> rfl
  have hlast : ∀ z : E,
      (Fin.cons z (fun j => (w j : E)) ∘ Fin.natAdd 2 : Fin 3 → E) =
        ![(w 1 : E), (w 2 : E), (w 3 : E)] := by
    intro z
    funext j
    fin_cases j <;> rfl
  simp only [hfirst, hlast]
  set F : Tensor0SBundle.Tensor0SModel 1 ℝ E → E → ℝ := fun β z =>
    Tensor0SBundle.Tensor0SSpace.toModel D ![z, (w 0 : E)] *
      (Tensor0SBundle.TensorRSSpace.toModel B β) ![(w 1 : E), (w 2 : E), (w 3 : E)] with hF
  have hFβ : ∀ z : E, IsLinearMap ℝ (fun β => F β z) := by
    intro z
    constructor
    · intro β₁ β₂
      rw [hF]
      simp only [map_add, ContinuousMultilinearMap.add_apply, mul_add]
    · intro cc β
      rw [hF]
      simp only [map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring
  have hFz : ∀ β, IsLinearMap ℝ (fun z : E => F β z) := by
    intro β
    constructor
    · intro z₁ z₂
      rw [hF]
      simp only
      rw [show (![z₁ + z₂, (w 0 : E)] : Fin 2 → E) = Fin.cons (z₁ + z₂) ![(w 0 : E)] from rfl,
        show (![z₁, (w 0 : E)] : Fin 2 → E) = Fin.cons z₁ ![(w 0 : E)] from rfl,
        show (![z₂, (w 0 : E)] : Fin 2 → E) = Fin.cons z₂ ![(w 0 : E)] from rfl]
      rw [show Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons (z₁ + z₂) ![(w 0 : E)]) =
          Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z₁ ![(w 0 : E)]) +
            Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z₂ ![(w 0 : E)]) from
        (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.cons_add _ z₁ z₂]
      ring
    · intro cc z
      rw [hF]
      simp only
      rw [show (![cc • z, (w 0 : E)] : Fin 2 → E) = Fin.cons (cc • z) ![(w 0 : E)] from rfl,
        show (![z, (w 0 : E)] : Fin 2 → E) = Fin.cons z ![(w 0 : E)] from rfl]
      rw [show Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons (cc • z) ![(w 0 : E)]) =
          cc • Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z ![(w 0 : E)]) from
        (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.cons_smul _ cc z]
      rw [smul_eq_mul, smul_eq_mul]
      ring
  rw [show (∑ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D ![((Module.finBasis ℝ E) i), (w 0 : E)] *
        (Tensor0SBundle.TensorRSSpace.toModel B
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i)))
          ![(w 1 : E), (w 2 : E), (w 3 : E)]) =
      ∑ a : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E)) from
    dualPair_sum_swap (I := I) g₀ x F hFβ hFz e horth hrepr]
  have hterm : ∀ a : Fin n,
      |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))| ≤
        CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
    intro a
    rw [hF]
    simp only
    rw [abs_mul]
    have hDterm : |Tensor0SBundle.Tensor0SSpace.toModel D ![((e a : E)), (w 0 : E)]| ≤
        c * Real.sqrt (g₀.inner x (w 0) (w 0)) := by
      have harg : (![((e a : E)), (w 0 : E)] : Fin 2 → E) =
          (fun j => ((![e a, w 0] : Fin 2 → TangentSpace I x) j : E)) := by
        funext j
        fin_cases j <;> rfl
      rw [harg]
      have hb := hD.2 ![e a, w 0]
      have hprod : (∏ j, Real.sqrt (g₀.inner x ((![e a, w 0] : Fin 2 → TangentSpace I x) j)
          ((![e a, w 0] : Fin 2 → TangentSpace I x) j))) =
          Real.sqrt (g₀.inner x (w 0) (w 0)) := by
        rw [Fin.prod_univ_two]
        have h1a : g₀.inner x (e a) (e a) = 1 := by rw [horth a a]; simp
        rw [show ((![e a, w 0] : Fin 2 → TangentSpace I x) 0) = e a from rfl,
          show ((![e a, w 0] : Fin 2 → TangentSpace I x) 1) = w 0 from rfl,
          h1a, Real.sqrt_one, one_mul]
      rw [hprod] at hb
      exact hb
    have hBterm : |(Tensor0SBundle.TensorRSSpace.toModel B
        (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
        ![(w 1 : E), (w 2 : E), (w 3 : E)]| ≤
        CB * (Real.sqrt (g₀.inner x (w 1) (w 1)) * Real.sqrt (g₀.inner x (w 2) (w 2)) *
          Real.sqrt (g₀.inner x (w 3) (w 3))) := by
      have harg : (![(w 1 : E), (w 2 : E), (w 3 : E)] : Fin 3 → E) =
          (fun j => ((![w 1, w 2, w 3] : Fin 3 → TangentSpace I x) j : E)) := by
        funext j
        fin_cases j <;> rfl
      rw [harg]
      exact hB a ![w 1, w 2, w 3]
    calc |Tensor0SBundle.Tensor0SSpace.toModel D ![((e a : E)), (w 0 : E)]| *
          |(Tensor0SBundle.TensorRSSpace.toModel B
              (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
              ![(w 1 : E), (w 2 : E), (w 3 : E)]|
        ≤ (c * Real.sqrt (g₀.inner x (w 0) (w 0))) *
            (CB * (Real.sqrt (g₀.inner x (w 1) (w 1)) * Real.sqrt (g₀.inner x (w 2) (w 2)) *
              Real.sqrt (g₀.inner x (w 3) (w 3)))) :=
          mul_le_mul hDterm hBterm (abs_nonneg _)
            (mul_nonneg hD.1 (by positivity))
      _ = CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
          rw [Fin.prod_univ_four]
          ring
  calc |∑ a : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))|
      ≤ ∑ a : Fin n,
          |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin n, CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) :=
        Finset.sum_le_sum (fun a _ => hterm a)
    _ = (n : ℝ) * CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

set_option linter.unusedSectionVars false in

private lemma cometricDoubleTrace_toModel_bound (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a)
    {q : ℝ} (_hq : 0 ≤ q)
    (hqb : ∀ b : Fin n,
      Real.sqrt (g₀.inner x
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)))
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)))) ≤ q)
    {c : ℝ} {Z : Tensor0SBundle.Tensor0SSpace 4 I x}
    (hZ : fibPointwiseBound (I := I) g₀ x 4 c Z)
    (w : Fin 2 → TangentSpace I x) :
    |Tensor0SBundle.Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₁ 2 x Z)
        (fun j => (w j : E))| ≤
      (n : ℝ) * q * c *
        (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) := by
  rw [cometricDoubleTraceFib_toModel, modelDoubleTrace_apply]
  set F : Tensor0SBundle.Tensor0SModel 1 ℝ E → E → ℝ := fun β z =>
    Tensor0SBundle.Tensor0SSpace.toModel Z
      (Fin.cons (cometricLmodel (I := I) g₁ x β)
        (Fin.cons z ![(w 0 : E), (w 1 : E)])) with hF
  have hFβ : ∀ z : E, IsLinearMap ℝ (fun β => F β z) := by
    intro z
    constructor
    · intro β₁ β₂
      rw [hF]
      simp only [map_add]
      exact (Tensor0SBundle.Tensor0SSpace.toModel Z).toMultilinearMap.cons_add _ _ _
    · intro cc β
      rw [hF]
      simp only [map_smul]
      exact (Tensor0SBundle.Tensor0SSpace.toModel Z).toMultilinearMap.cons_smul _ _ _
  have hFz : ∀ β, IsLinearMap ℝ (fun z : E => F β z) := by
    intro β
    have hupd : ∀ z : E,
        (Fin.cons (cometricLmodel (I := I) g₁ x β)
          (Fin.cons z ![(w 0 : E), (w 1 : E)]) : Fin 4 → E) =
        Function.update (Fin.cons (cometricLmodel (I := I) g₁ x β)
          (Fin.cons (0 : E) ![(w 0 : E), (w 1 : E)])) 1 z := by
      intro z
      funext j
      fin_cases j <;> rfl
    constructor
    · intro z₁ z₂
      rw [hF]
      simp only
      rw [hupd (z₁ + z₂), hupd z₁, hupd z₂]
      exact (Tensor0SBundle.Tensor0SSpace.toModel Z).map_update_add _ 1 z₁ z₂
    · intro cc z
      rw [hF]
      simp only
      rw [hupd (cc • z), hupd z, smul_eq_mul]
      have := (Tensor0SBundle.Tensor0SSpace.toModel Z).map_update_smul
        (Fin.cons (cometricLmodel (I := I) g₁ x β)
          (Fin.cons (0 : E) ![(w 0 : E), (w 1 : E)])) 1 cc z
      rw [this, smul_eq_mul]
  have hswap : (∑ k : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel Z
        (Fin.cons (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) (fun j => (w j : E))))) =
      ∑ b : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e b))) ((e b : E)) := by
    have hargs : ∀ (z : E) (β : Tensor0SBundle.Tensor0SModel 1 ℝ E),
        (Fin.cons (cometricLmodel (I := I) g₁ x β) (Fin.cons z (fun j => (w j : E))) :
          Fin 4 → E) =
        Fin.cons (cometricLmodel (I := I) g₁ x β) (Fin.cons z ![(w 0 : E), (w 1 : E)]) := by
      intro z β
      funext j
      fin_cases j <;> rfl
    have hpre : (∑ k : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel Z
          (Fin.cons (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) (fun j => (w j : E))))) =
        ∑ k : Fin (Module.finrank ℝ E),
          F (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) ((Module.finBasis ℝ E) k) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hF]
      simp only
      rw [hargs]
    rw [hpre]
    exact dualPair_sum_swap (I := I) g₀ x F hFβ hFz e horth hrepr
  rw [hswap]
  have hterm : ∀ b : Fin n,
      |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e b))) ((e b : E))| ≤
        q * c * (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) := by
    intro b
    rw [hF]
    simp only
    have hcml : cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e b))) =
        inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)) := by
      exact congrArg (inverseMetricSharpFib (I := I) g₁ x)
        (Tensor0SBundle.Tensor0SSpace.ofModel_toModel (g0FlatCLM (I := I) g₀ x (e b)))
    rw [hcml]
    set qb : TangentSpace I x :=
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)) with hqbdef
    have harg : (Fin.cons ((qb : TangentSpace I x) : E)
        (Fin.cons ((e b : E)) ![(w 0 : E), (w 1 : E)]) : Fin 4 → E) =
        (fun j => ((![qb, e b, w 0, w 1] : Fin 4 → TangentSpace I x) j : E)) := by
      funext j
      fin_cases j <;> rfl
    rw [harg]
    have hb := hZ.2 ![qb, e b, w 0, w 1]
    have hprod : (∏ j, Real.sqrt (g₀.inner x ((![qb, e b, w 0, w 1] : Fin 4 → TangentSpace I x) j)
        ((![qb, e b, w 0, w 1] : Fin 4 → TangentSpace I x) j))) =
        Real.sqrt (g₀.inner x qb qb) *
          (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) := by
      rw [Fin.prod_univ_four]
      have h1b : g₀.inner x (e b) (e b) = 1 := by rw [horth b b]; simp
      rw [show ((![qb, e b, w 0, w 1] : Fin 4 → TangentSpace I x) 0) = qb from rfl,
        show ((![qb, e b, w 0, w 1] : Fin 4 → TangentSpace I x) 1) = e b from rfl,
        show ((![qb, e b, w 0, w 1] : Fin 4 → TangentSpace I x) 2) = w 0 from rfl,
        show ((![qb, e b, w 0, w 1] : Fin 4 → TangentSpace I x) 3) = w 1 from rfl,
        h1b, Real.sqrt_one]
      ring
    rw [hprod] at hb
    refine le_trans hb ?_
    have hqb_le := hqb b
    rw [← hqbdef] at hqb_le
    have hwprod : 0 ≤ Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc c * (Real.sqrt (g₀.inner x qb qb) *
          (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))))
        ≤ c * (q * (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hZ.1
          exact mul_le_mul_of_nonneg_right hqb_le hwprod
      _ = q * c * (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) := by
          ring
  calc |∑ b : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e b))) ((e b : E))|
      ≤ ∑ b : Fin n,
          |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e b))) ((e b : E))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : Fin n, q * c *
          (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) :=
        Finset.sum_le_sum (fun b _ => hterm b)
    _ = (n : ℝ) * q * c *
          (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

set_option linter.unusedSectionVars false in

private lemma fourTrace_toModel_bound (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a)
    {q : ℝ} (hq : 0 ≤ q)
    (hqb : ∀ b : Fin n,
      Real.sqrt (g₀.inner x
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)))
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)))) ≤ q)
    {c : ℝ} {Z : Tensor0SBundle.Tensor0SSpace 4 I x}
    (hZ : fibPointwiseBound (I := I) g₀ x 4 c Z)
    (w : Fin 2 → TangentSpace I x) :
    |Tensor0SBundle.Tensor0SSpace.toModel
        (ricciCometricFourTraceCLM (I := I) g₁ x Z) (fun j => (w j : E))| ≤
      2 * (n : ℝ) * q * c *
        (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) := by
  have hexpand : ricciCometricFourTraceCLM (I := I) g₁ x Z =
      ((1 : ℝ) / 2) •
        (cometricDoubleTraceFib (I := I) g₁ 2 x (slotPermCLM (I := I) cdPerm4_0231 x Z)
          + cometricDoubleTraceFib (I := I) g₁ 2 x (slotPermCLM (I := I) cdPerm4_0321 x Z)
          - cometricDoubleTraceFib (I := I) g₁ 2 x Z
          - cometricDoubleTraceFib (I := I) g₁ 2 x (slotPermCLM (I := I) cdPerm4_2301 x Z)) := rfl
  rw [hexpand, Tensor0SBundle.Tensor0SSpace.toModel_smul,
    Tensor0SBundle.Tensor0SSpace.toModel_sub, Tensor0SBundle.Tensor0SSpace.toModel_sub,
    Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply]
  set t₁ := Tensor0SBundle.Tensor0SSpace.toModel
    (cometricDoubleTraceFib (I := I) g₁ 2 x (slotPermCLM (I := I) cdPerm4_0231 x Z))
    (fun j => (w j : E)) with ht₁
  set t₂ := Tensor0SBundle.Tensor0SSpace.toModel
    (cometricDoubleTraceFib (I := I) g₁ 2 x (slotPermCLM (I := I) cdPerm4_0321 x Z))
    (fun j => (w j : E)) with ht₂
  set t₃ := Tensor0SBundle.Tensor0SSpace.toModel
    (cometricDoubleTraceFib (I := I) g₁ 2 x Z) (fun j => (w j : E)) with ht₃
  set t₄ := Tensor0SBundle.Tensor0SSpace.toModel
    (cometricDoubleTraceFib (I := I) g₁ 2 x (slotPermCLM (I := I) cdPerm4_2301 x Z))
    (fun j => (w j : E)) with ht₄
  set W : ℝ := Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1)) with hW
  have hW_nn : 0 ≤ W := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hb₁ : |t₁| ≤ (n : ℝ) * q * c * W :=
    cometricDoubleTrace_toModel_bound (I := I) g₀ g₁ x e horth hrepr hq hqb
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_0231 hZ) w
  have hb₂ : |t₂| ≤ (n : ℝ) * q * c * W :=
    cometricDoubleTrace_toModel_bound (I := I) g₀ g₁ x e horth hrepr hq hqb
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_0321 hZ) w
  have hb₃ : |t₃| ≤ (n : ℝ) * q * c * W :=
    cometricDoubleTrace_toModel_bound (I := I) g₀ g₁ x e horth hrepr hq hqb hZ w
  have hb₄ : |t₄| ≤ (n : ℝ) * q * c * W :=
    cometricDoubleTrace_toModel_bound (I := I) g₀ g₁ x e horth hrepr hq hqb
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_2301 hZ) w
  have htotal : |t₁ + t₂ - t₃ - t₄| ≤ 4 * ((n : ℝ) * q * c * W) := by
    have h12 : |t₁ + t₂| ≤ |t₁| + |t₂| := abs_add_le t₁ t₂
    have h123 : |t₁ + t₂ - t₃| ≤ |t₁ + t₂| + |t₃| := by
      rw [sub_eq_add_neg]
      refine le_trans (abs_add_le _ _) (le_of_eq ?_)
      rw [abs_neg]
    have h1234 : |t₁ + t₂ - t₃ - t₄| ≤ |t₁ + t₂ - t₃| + |t₄| := by
      rw [sub_eq_add_neg (t₁ + t₂ - t₃) t₄]
      refine le_trans (abs_add_le _ _) (le_of_eq ?_)
      rw [abs_neg]
    linarith
  rw [smul_eq_mul, abs_mul, show |(1 : ℝ) / 2| = 1 / 2 from by norm_num]
  calc (1 / 2 : ℝ) * |t₁ + t₂ - t₃ - t₄| ≤ (1 / 2 : ℝ) * (4 * ((n : ℝ) * q * c * W)) :=
        mul_le_mul_of_nonneg_left htotal (by norm_num)
    _ = 2 * (n : ℝ) * q * c * W := by ring

set_option linter.unusedSectionVars false in

private lemma fibPointwiseBound_order1CLM (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a)
    (A : Tensor0SBundle.TensorRSSpace 1 2 I x) {CA : ℝ} (hCA : 0 ≤ CA)
    (hAf : ∀ (a : Fin n) (v : Fin 2 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel A
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        CA * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1))))
    {c : ℝ} {D : Tensor0SBundle.Tensor0SSpace 3 I x}
    (hD : fibPointwiseBound (I := I) g₀ x 3 c D) :
    fibPointwiseBound (I := I) g₀ x 4 (5 * ((n : ℝ) * CA * c))
      (linearizedRicciConnDiffOrder1CLM (I := I) x A D) := by
  have h₁ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_0312
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_102 hD))
  have h₂ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_0213
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_120 hD))
  have h₃ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_2301
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf hD)
  have h₄ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_1302
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_102 hD))
  have h₅ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_1203
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_120 hD))
  have hval : linearizedRicciConnDiffOrder1CLM (I := I) x A D =
      -(slotPermCLM (I := I) cdPerm4_0312 x
          (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_102 x D))
        + slotPermCLM (I := I) cdPerm4_0213 x
          (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_120 x D))
        + slotPermCLM (I := I) cdPerm4_2301 x (connContrCLM (I := I) 2 1 x A D)
        + slotPermCLM (I := I) cdPerm4_1302 x
          (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_102 x D))
        + slotPermCLM (I := I) cdPerm4_1203 x
          (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_120 x D))) := rfl
  refine ⟨mul_nonneg (by norm_num)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCA) hD.1), ?_⟩
  intro w
  rw [hval, Tensor0SBundle.Tensor0SSpace.toModel_neg, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [ContinuousMultilinearMap.neg_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, abs_neg]
  set P4 : ℝ := ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) with hP4
  have hP4nn : 0 ≤ P4 := fibPointwiseBound_prod_nonneg (I := I) g₀ x w
  have b₁ := h₁.2 w
  have b₂ := h₂.2 w
  have b₃ := h₃.2 w
  have b₄ := h₄.2 w
  have b₅ := h₅.2 w
  rw [← hP4] at b₁ b₂ b₃ b₄ b₅
  set v₁ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_0312 x
      (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_102 x D)))
    (fun j => (w j : E)) with hv₁
  set v₂ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_0213 x
      (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_120 x D)))
    (fun j => (w j : E)) with hv₂
  set v₃ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_2301 x (connContrCLM (I := I) 2 1 x A D))
    (fun j => (w j : E)) with hv₃
  set v₄ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_1302 x
      (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_102 x D)))
    (fun j => (w j : E)) with hv₄
  set v₅ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_1203 x
      (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_120 x D)))
    (fun j => (w j : E)) with hv₅
  have habs : |v₁ + v₂ + v₃ + v₄ + v₅| ≤ |v₁| + |v₂| + |v₃| + |v₄| + |v₅| := by
    have i1 : |v₁ + v₂| ≤ |v₁| + |v₂| := abs_add_le _ _
    have i2 : |v₁ + v₂ + v₃| ≤ |v₁ + v₂| + |v₃| := abs_add_le _ _
    have i3 : |v₁ + v₂ + v₃ + v₄| ≤ |v₁ + v₂ + v₃| + |v₄| := abs_add_le _ _
    have i4 : |v₁ + v₂ + v₃ + v₄ + v₅| ≤ |v₁ + v₂ + v₃ + v₄| + |v₅| := abs_add_le _ _
    linarith
  calc |v₁ + v₂ + v₃ + v₄ + v₅| ≤ |v₁| + |v₂| + |v₃| + |v₄| + |v₅| := habs
    _ ≤ 5 * ((n : ℝ) * CA * c) * P4 := by linarith

set_option linter.unusedSectionVars false in

private lemma fibPointwiseBound_order0CLM (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a)
    (A : Tensor0SBundle.TensorRSSpace 1 2 I x) {CA : ℝ} (hCA : 0 ≤ CA)
    (hAf : ∀ (a : Fin n) (v : Fin 2 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel A
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        CA * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1))))
    (DA : Tensor0SBundle.TensorRSSpace 1 3 I x) {CDA : ℝ} (hCDA : 0 ≤ CDA)
    (hDAf : ∀ (a : Fin n) (v : Fin 3 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel DA
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        CDA * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1)) *
          Real.sqrt (g₀.inner x (v 2) (v 2))))
    {c : ℝ} {D : Tensor0SBundle.Tensor0SSpace 2 I x}
    (hD : fibPointwiseBound (I := I) g₀ x 2 c D) :
    fibPointwiseBound (I := I) g₀ x 4
      (6 * ((n : ℝ) * CA * ((n : ℝ) * CA * c)) + 2 * ((n : ℝ) * CDA * c))
      (linearizedRicciConnDiffOrder0CLM (I := I) x A DA D) := by
  have hDswap := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm2_10 hD
  have hinn := fibPointwiseBound_connContr11 (I := I) g₀ x e horth hrepr A hCA hAf hD
  have hinn' := fibPointwiseBound_connContr11 (I := I) g₀ x e horth hrepr A hCA hAf hDswap
  have hu₃ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_3201
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_102 hinn))
  have hu₄ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_2301
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_102 hinn'))
  have hu₅ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_3102
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_120 hinn))
  have hu₆ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_1302
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf hinn')
  have hu₇ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_1203
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf hinn)
  have hu₈ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_2103
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_120 hinn'))
  have hu₁ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_3012
    (fibPointwiseBound_connContr12 (I := I) g₀ x e horth hrepr DA hCDA hDAf hD)
  have hu₂ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_2013
    (fibPointwiseBound_connContr12 (I := I) g₀ x e horth hrepr DA hCDA hDAf hDswap)
  have hval : linearizedRicciConnDiffOrder0CLM (I := I) x A DA D =
      (slotPermCLM (I := I) cdPerm4_3201 x
          (connContrCLM (I := I) 2 1 x A
            (slotPermCLM (I := I) cdPerm3_102 x (connContrCLM (I := I) 1 1 x A D)))
        + slotPermCLM (I := I) cdPerm4_2301 x
          (connContrCLM (I := I) 2 1 x A
            (slotPermCLM (I := I) cdPerm3_102 x
              (connContrCLM (I := I) 1 1 x A (slotPermCLM (I := I) cdPerm2_10 x D))))
        + slotPermCLM (I := I) cdPerm4_3102 x
          (connContrCLM (I := I) 2 1 x A
            (slotPermCLM (I := I) cdPerm3_120 x (connContrCLM (I := I) 1 1 x A D)))
        + slotPermCLM (I := I) cdPerm4_1302 x
          (connContrCLM (I := I) 2 1 x A
            (connContrCLM (I := I) 1 1 x A (slotPermCLM (I := I) cdPerm2_10 x D)))
        + slotPermCLM (I := I) cdPerm4_1203 x
          (connContrCLM (I := I) 2 1 x A (connContrCLM (I := I) 1 1 x A D))
        + slotPermCLM (I := I) cdPerm4_2103 x
          (connContrCLM (I := I) 2 1 x A
            (slotPermCLM (I := I) cdPerm3_120 x
              (connContrCLM (I := I) 1 1 x A (slotPermCLM (I := I) cdPerm2_10 x D)))))
      - slotPermCLM (I := I) cdPerm4_3012 x (connContrCLM (I := I) 1 2 x DA D)
      - slotPermCLM (I := I) cdPerm4_2013 x
          (connContrCLM (I := I) 1 2 x DA (slotPermCLM (I := I) cdPerm2_10 x D)) := rfl
  refine ⟨add_nonneg
    (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCA)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCA) hD.1)))
    (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCDA) hD.1)), ?_⟩
  intro w
  rw [hval, Tensor0SBundle.Tensor0SSpace.toModel_sub, Tensor0SBundle.Tensor0SSpace.toModel_sub,
    Tensor0SBundle.Tensor0SSpace.toModel_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply]
  set P4 : ℝ := ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) with hP4
  have hP4nn : 0 ≤ P4 := fibPointwiseBound_prod_nonneg (I := I) g₀ x w
  have b₃ := hu₃.2 w
  have b₄ := hu₄.2 w
  have b₅ := hu₅.2 w
  have b₆ := hu₆.2 w
  have b₇ := hu₇.2 w
  have b₈ := hu₈.2 w
  have b₁ := hu₁.2 w
  have b₂ := hu₂.2 w
  rw [← hP4] at b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
  set y₃ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_3201 x
      (connContrCLM (I := I) 2 1 x A
        (slotPermCLM (I := I) cdPerm3_102 x (connContrCLM (I := I) 1 1 x A D))))
    (fun j => (w j : E)) with hy₃
  set y₄ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_2301 x
      (connContrCLM (I := I) 2 1 x A
        (slotPermCLM (I := I) cdPerm3_102 x
          (connContrCLM (I := I) 1 1 x A (slotPermCLM (I := I) cdPerm2_10 x D)))))
    (fun j => (w j : E)) with hy₄
  set y₅ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_3102 x
      (connContrCLM (I := I) 2 1 x A
        (slotPermCLM (I := I) cdPerm3_120 x (connContrCLM (I := I) 1 1 x A D))))
    (fun j => (w j : E)) with hy₅
  set y₆ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_1302 x
      (connContrCLM (I := I) 2 1 x A
        (connContrCLM (I := I) 1 1 x A (slotPermCLM (I := I) cdPerm2_10 x D))))
    (fun j => (w j : E)) with hy₆
  set y₇ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_1203 x
      (connContrCLM (I := I) 2 1 x A (connContrCLM (I := I) 1 1 x A D)))
    (fun j => (w j : E)) with hy₇
  set y₈ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_2103 x
      (connContrCLM (I := I) 2 1 x A
        (slotPermCLM (I := I) cdPerm3_120 x
          (connContrCLM (I := I) 1 1 x A (slotPermCLM (I := I) cdPerm2_10 x D)))))
    (fun j => (w j : E)) with hy₈
  set y₁ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_3012 x (connContrCLM (I := I) 1 2 x DA D))
    (fun j => (w j : E)) with hy₁
  set y₂ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_2013 x
      (connContrCLM (I := I) 1 2 x DA (slotPermCLM (I := I) cdPerm2_10 x D)))
    (fun j => (w j : E)) with hy₂
  have habs : |y₃ + y₄ + y₅ + y₆ + y₇ + y₈ - y₁ - y₂| ≤
      |y₃| + |y₄| + |y₅| + |y₆| + |y₇| + |y₈| + |y₁| + |y₂| := by
    have i1 : |y₃ + y₄| ≤ |y₃| + |y₄| := abs_add_le _ _
    have i2 : |y₃ + y₄ + y₅| ≤ |y₃ + y₄| + |y₅| := abs_add_le _ _
    have i3 : |y₃ + y₄ + y₅ + y₆| ≤ |y₃ + y₄ + y₅| + |y₆| := abs_add_le _ _
    have i4 : |y₃ + y₄ + y₅ + y₆ + y₇| ≤ |y₃ + y₄ + y₅ + y₆| + |y₇| := abs_add_le _ _
    have i5 : |y₃ + y₄ + y₅ + y₆ + y₇ + y₈| ≤ |y₃ + y₄ + y₅ + y₆ + y₇| + |y₈| := abs_add_le _ _
    have i6 : |y₃ + y₄ + y₅ + y₆ + y₇ + y₈ - y₁| ≤ |y₃ + y₄ + y₅ + y₆ + y₇ + y₈| + |y₁| := by
      rw [sub_eq_add_neg]
      refine le_trans (abs_add_le _ _) (le_of_eq ?_)
      rw [abs_neg]
    have i7 : |y₃ + y₄ + y₅ + y₆ + y₇ + y₈ - y₁ - y₂| ≤
        |y₃ + y₄ + y₅ + y₆ + y₇ + y₈ - y₁| + |y₂| := by
      rw [sub_eq_add_neg (y₃ + y₄ + y₅ + y₆ + y₇ + y₈ - y₁) y₂]
      refine le_trans (abs_add_le _ _) (le_of_eq ?_)
      rw [abs_neg]
    linarith
  calc |y₃ + y₄ + y₅ + y₆ + y₇ + y₈ - y₁ - y₂|
      ≤ |y₃| + |y₄| + |y₅| + |y₆| + |y₇| + |y₈| + |y₁| + |y₂| := habs
    _ ≤ (6 * ((n : ℝ) * CA * ((n : ℝ) * CA * c)) + 2 * ((n : ℝ) * CDA * c)) * P4 := by
        have e1 : (6 * ((n : ℝ) * CA * ((n : ℝ) * CA * c)) + 2 * ((n : ℝ) * CDA * c)) * P4 =
            ((n : ℝ) * CA * ((n : ℝ) * CA * c) * P4) * 6 + ((n : ℝ) * CDA * c * P4) * 2 := by
          ring
        rw [e1]
        linarith

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option maxRecDepth 16000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- A pointwise background-covariant metric `2`-jet envelope uniformly bounds
the order-zero and order-one connection-difference coefficients in the
linearized Ricci tensor.  This low-regularity coefficient engine does not use
a high Sobolev-order hypothesis. -/
theorem ricci_coeff_rfns_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δc : ℝ} (hδc_le : δc ≤ max δ₀ 0)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δc)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle
                (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            (show Tensor0SBundle.TensorRSSpace 2 2 I x from
              linearizedRicciConnDiffOrder0Fib (I := I) g₀ g₁ x) ≤ C ∧
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            (show Tensor0SBundle.TensorRSSpace 3 2 I x from
              linearizedRicciConnDiffOrder1Fib (I := I) g₀ g₁ x) ≤ C := by
  classical
  set δm : ℝ := max δ₀ 0 with hδm_def
  have hδm_nn : 0 ≤ δm := le_max_right _ _
  have hδm_lt : δm < 1 := max_lt hδ₀ one_pos
  have hqpos : (0 : ℝ) < 1 - δm := by linarith
  obtain ⟨C₀, hC₀0, hpw⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδm_nn hδm_lt
  obtain ⟨Ccd, hCcd0, hcd⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  set nn : ℝ := (Module.finrank ℝ E : ℝ) with hnn
  have hnn0 : 0 ≤ nn := Nat.cast_nonneg _
  set q : ℝ := 1 / (1 - δm) with hqdef
  have hq0 : 0 ≤ q := le_of_lt (div_pos one_pos hqpos)
  set Mc1 : ℝ := 2 * nn * q * (5 * (nn * (C₀ * B) * 1)) with hMc1
  set Mc0 : ℝ := 2 * nn * q *
    (6 * (nn * (C₀ * B) * (nn * (C₀ * B) * 1)) + 2 * (nn * Ccd * 1)) with hMc0
  have hMc1_nn : 0 ≤ Mc1 := by rw [hMc1]; positivity
  have hMc0_nn : 0 ≤ Mc0 := by rw [hMc0]; positivity
  refine ⟨max (nn ^ 2 * nn ^ 2 * Mc0 ^ 2) (nn ^ 3 * nn ^ 2 * Mc1 ^ 2),
    le_trans (by positivity) (le_max_left _ _), ?_⟩
  intro g₁ P htie δc hδc_le hbound x henv
  letI instT3 : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  have hboundm : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δm := by
    intro y v w'
    refine le_trans (hbound y v w') ?_
    have hnnw : 0 ≤ Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w' w') :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc δc * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w' w')
        = δc * (Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w' w')) := by ring
      _ ≤ δm * (Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w' w')) :=
          mul_le_mul_of_nonneg_right hδc_le hnnw
      _ = δm * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w' w') := by ring
  obtain ⟨n', e, bse, hn, hbse, horth, hpars, hrepr_v, hlastw⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n' = Module.finrank ℝ E := by rw [hn]; rfl
  subst hnE
  set G : ℝ := ‖(iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  have hG_le : G ≤ B := by
    have hterms : ∀ k ∈ Finset.range 3, 0 ≤
        (letI : Bundle.RiemannianBundle
            (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
        ‖(iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x‖) := by
      intro k _
      letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
      exact norm_nonneg _
    exact le_trans (Finset.single_le_sum hterms
      (show (1 : ℕ) ∈ Finset.range 3 from Finset.mem_range.mpr (by norm_num))) henv
  have hpwA : ∀ v w' : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w')
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w')) ≤
        C₀ * G * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w' w') := by
    intro v w'
    have h := hpw g₁ P htie (le_refl δm) hδm_nn hboundm x v w'
    rw [← hG_def] at h
    exact h
  have hpwA' : ∀ (a : Fin (Module.finrank ℝ E)) (v : Fin 2 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel (connDiffFib (I := I) g₁ g₀ x)
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        (C₀ * G) * (Real.sqrt (g₀.inner x (v 0) (v 0)) *
          Real.sqrt (g₀.inner x (v 1) (v 1))) := by
    refine connDiff_flat_factor_bound (I := I) g₀ g₁ x e horth ?_
    intro v w'
    have h := hpwA v w'
    calc Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w')
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w'))
        ≤ C₀ * G * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w' w') := h
      _ = (C₀ * G) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w' w') := by ring
  have hqb : ∀ b : Fin (Module.finrank ℝ E),
      Real.sqrt (g₀.inner x
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)))
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)))) ≤ q := by
    intro b
    have h := sqrt_inner_inverseMetricSharpFib_g0FlatCLM_le (I := I) (M := M) g₀ g₁
      (fun y => ccTensorBilinSymm (I := I) g₀ P y) htie hδm_lt hδm_nn hboundm x (e b)
    have h1b : g₀.inner x (e b) (e b) = 1 := by rw [horth b b]; simp
    rw [h1b, Real.sqrt_one, mul_one] at h
    exact h
  have hDAf : ∀ (a : Fin (Module.finrank ℝ E)) (v : Fin 3 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel
          ((covGrad (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) g₁ g₀)).toSection x)
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        Ccd * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1)) *
          Real.sqrt (g₀.inner x (v 2) (v 2))) := by
    intro a v
    set omg : Tensor0SBundle.Tensor0SSpace 1 I x := g0FlatCLM (I := I) g₀ x (e a) with homg
    have h1 : Tensor0SBundle.TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
        (Tensor0SBundle.Tensor0SSpace.toModel omg) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
            omg) :=
      (toModel_tensorRS_apply (I := I) 1 3 x _ omg).symm
    rw [h1]
    obtain ⟨om, hom⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (V := fun y : M => Tensor0SBundle.Tensor0SSpace 1 I y) x omg
    set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x (v 0),
        smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩ with hX
    set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x (v 1),
        smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩ with hY
    set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x (v 2),
        smoothExtensionTangent_contMDiff (I := I) x (v 2)⟩ with hZ
    have hXx : X x = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
    have hYx : Y x = v 1 := smoothExtensionTangent_eq (I := I) x (v 1)
    have hZx : Z x = v 2 := smoothExtensionTangent_eq (I := I) x (v 2)
    have hbr := connDiffSection_covGrad_eq_covDerivConnDiff (I := I) g₁ g₀ om X Y Z x
    rw [hom, hXx, hYx, hZx] at hbr
    have hargs : (fun j : Fin 3 => (v j : E)) =
        (Fin.cons (v 0) (Fin.cons (v 1) ![v 2]) : Fin 3 → TangentSpace I x) := by
      funext j
      fin_cases j <;> rfl
    rw [hargs, hbr]
    set vec : TangentSpace I x := covDerivConnDiff (I := I) g₀ g₁ X Z Y x with hvec
    rw [show omg (fun _ : Fin 1 => vec) =
        cotangentToDual (I := I) (x := x) omg vec from
      (cotangentToDual_apply (I := I) (x := x) omg vec).symm]
    rw [homg, cotangentToDual_g0FlatCLM]
    have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e a) vec
    have h1a : g₀.inner x (e a) (e a) = 1 := by rw [horth a a]; simp
    rw [h1a, Real.sqrt_one, one_mul] at hcs
    refine le_trans hcs ?_
    have hengine := hcd g₁ P hδc_le hbound htie x henv (v 0) (v 2) (v 1)
    have hveceq : covDerivConnDiff (I := I) g₀ g₁
        (smoothExtensionTangent (I := I) x (v 0))
        (smoothExtensionTangent (I := I) x (v 2))
        (smoothExtensionTangent (I := I) x (v 1)) x = vec := rfl
    rw [hveceq] at hengine
    refine le_trans hengine (le_of_eq ?_)
    ring
  set A : Tensor0SBundle.TensorRSSpace 1 2 I x :=
    (connDiffSection (I := I) g₁ g₀).toSection x with hAset
  set DAv : Tensor0SBundle.TensorRSSpace 1 3 I x :=
    (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x with hDAset
  have hCA_nn : 0 ≤ C₀ * G := mul_nonneg hC₀0 hG_nn
  have hCAB : C₀ * G ≤ C₀ * B := mul_le_mul_of_nonneg_left hG_le hC₀0
  have hO1 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from
        linearizedRicciConnDiffOrder1Fib (I := I) g₀ g₁ x) ≤ nn ^ 3 * nn ^ 2 * Mc1 ^ 2 := by
    rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 3 2 x
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from
        linearizedRicciConnDiffOrder1Fib (I := I) g₀ g₁ x) e bse rfl hbse horth]
    have hcompb : ∀ (K : Fin 3 → Fin (Module.finrank ℝ E))
        (J : Fin 2 → Fin (Module.finrank ℝ E)),
        (fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
          (show Tensor0SBundle.TensorRSSpace 3 2 I x from
            linearizedRicciConnDiffOrder1Fib (I := I) g₀ g₁ x)
          (Module.finrank ℝ E) e K J) ^ 2 ≤ Mc1 ^ 2 := by
      intro K J
      have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
          (show Tensor0SBundle.TensorRSSpace 3 2 I x from
            linearizedRicciConnDiffOrder1Fib (I := I) g₀ g₁ x)
          (Module.finrank ℝ E) e K J =
          Tensor0SBundle.Tensor0SSpace.toModel
            (ricciCometricFourTraceCLM (I := I) g₁ x
              (linearizedRicciConnDiffOrder1CLM (I := I) x A
                (coframeS (I := I) (M := M) g₀ x 3 e K)))
            (fun j => ((e (J j) : TangentSpace I x) : E)) := rfl
      have hfpb := fibPointwiseBound_order1CLM (I := I) g₀ x e horth hrepr_v A hCA_nn hpwA'
        (fibPointwiseBound_coframe (I := I) g₀ x 3 e horth K)
      have hb := fourTrace_toModel_bound (I := I) g₀ g₁ x e horth hrepr_v hq0 hqb hfpb
        (fun j => e (J j))
      have hJ0 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
      have hJ1 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by rw [horth (J 1) (J 1)]; simp
      rw [hJ0, hJ1, Real.sqrt_one, mul_one, mul_one] at hb
      have hb2 : |Tensor0SBundle.Tensor0SSpace.toModel
          (ricciCometricFourTraceCLM (I := I) g₁ x
            (linearizedRicciConnDiffOrder1CLM (I := I) x A
              (coframeS (I := I) (M := M) g₀ x 3 e K)))
          (fun j => ((e (J j) : TangentSpace I x) : E))| ≤ Mc1 := by
        refine le_trans hb ?_
        rw [hMc1, hnn]
        have hkey : (0 : ℝ) ≤ 10 * (Module.finrank ℝ E : ℝ) ^ 2 * q * (C₀ * B - C₀ * G) :=
          mul_nonneg (mul_nonneg (by positivity) hq0) (sub_nonneg.mpr hCAB)
        linarith [hkey]
      rw [hcomp]
      have h2 := abs_le.mp hb2
      exact sq_le_sq' h2.1 h2.2
    calc (∑ K : Fin 3 → Fin (Module.finrank ℝ E), ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
          (fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
            (show Tensor0SBundle.TensorRSSpace 3 2 I x from
              linearizedRicciConnDiffOrder1Fib (I := I) g₀ g₁ x)
            (Module.finrank ℝ E) e K J) ^ 2)
        ≤ ∑ _K : Fin 3 → Fin (Module.finrank ℝ E), ∑ _J : Fin 2 → Fin (Module.finrank ℝ E),
            Mc1 ^ 2 :=
          Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => hcompb K J))
      _ = nn ^ 3 * nn ^ 2 * Mc1 ^ 2 := by
          rw [Finset.sum_const, Finset.sum_const]
          simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_pow]
          rw [hnn]
          ring
  have hO0 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        linearizedRicciConnDiffOrder0Fib (I := I) g₀ g₁ x) ≤ nn ^ 2 * nn ^ 2 * Mc0 ^ 2 := by
    rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 2 2 x
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        linearizedRicciConnDiffOrder0Fib (I := I) g₀ g₁ x) e bse rfl hbse horth]
    have hcompb : ∀ (K : Fin 2 → Fin (Module.finrank ℝ E))
        (J : Fin 2 → Fin (Module.finrank ℝ E)),
        (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
          (show Tensor0SBundle.TensorRSSpace 2 2 I x from
            linearizedRicciConnDiffOrder0Fib (I := I) g₀ g₁ x)
          (Module.finrank ℝ E) e K J) ^ 2 ≤ Mc0 ^ 2 := by
      intro K J
      have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
          (show Tensor0SBundle.TensorRSSpace 2 2 I x from
            linearizedRicciConnDiffOrder0Fib (I := I) g₀ g₁ x)
          (Module.finrank ℝ E) e K J =
          Tensor0SBundle.Tensor0SSpace.toModel
            (ricciCometricFourTraceCLM (I := I) g₁ x
              (linearizedRicciConnDiffOrder0CLM (I := I) x A DAv
                (coframeS (I := I) (M := M) g₀ x 2 e K)))
            (fun j => ((e (J j) : TangentSpace I x) : E)) := rfl
      have hfpb := fibPointwiseBound_order0CLM (I := I) g₀ x e horth hrepr_v A hCA_nn hpwA'
        DAv hCcd0 hDAf (fibPointwiseBound_coframe (I := I) g₀ x 2 e horth K)
      have hb := fourTrace_toModel_bound (I := I) g₀ g₁ x e horth hrepr_v hq0 hqb hfpb
        (fun j => e (J j))
      have hJ0 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
      have hJ1 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by rw [horth (J 1) (J 1)]; simp
      rw [hJ0, hJ1, Real.sqrt_one, mul_one, mul_one] at hb
      have hb2 : |Tensor0SBundle.Tensor0SSpace.toModel
          (ricciCometricFourTraceCLM (I := I) g₁ x
            (linearizedRicciConnDiffOrder0CLM (I := I) x A DAv
              (coframeS (I := I) (M := M) g₀ x 2 e K)))
          (fun j => ((e (J j) : TangentSpace I x) : E))| ≤ Mc0 := by
        refine le_trans hb ?_
        rw [hMc0, hnn]
        have hsq : C₀ * G * (C₀ * G) ≤ C₀ * B * (C₀ * B) :=
          mul_le_mul hCAB hCAB hCA_nn (le_trans hCA_nn hCAB)
        have hkey : (0 : ℝ) ≤ 12 * (Module.finrank ℝ E : ℝ) ^ 3 * q *
            (C₀ * B * (C₀ * B) - C₀ * G * (C₀ * G)) :=
          mul_nonneg (mul_nonneg (by positivity) hq0) (sub_nonneg.mpr hsq)
        linarith [hkey]
      rw [hcomp]
      have h2 := abs_le.mp hb2
      exact sq_le_sq' h2.1 h2.2
    calc (∑ K : Fin 2 → Fin (Module.finrank ℝ E), ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
          (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
            (show Tensor0SBundle.TensorRSSpace 2 2 I x from
              linearizedRicciConnDiffOrder0Fib (I := I) g₀ g₁ x)
            (Module.finrank ℝ E) e K J) ^ 2)
        ≤ ∑ _K : Fin 2 → Fin (Module.finrank ℝ E), ∑ _J : Fin 2 → Fin (Module.finrank ℝ E),
            Mc0 ^ 2 :=
          Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => hcompb K J))
      _ = nn ^ 2 * nn ^ 2 * Mc0 ^ 2 := by
          rw [Finset.sum_const, Finset.sum_const]
          simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_pow]
          rw [hnn]
          ring
  exact ⟨le_trans hO0 (le_max_left _ _), le_trans hO1 (le_max_right _ _)⟩

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_linearizedRicciConnDiffCoeff_realizedFam_sqrt_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤
            Λ ∧
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤
            Λ := by
  classical
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) (M := M) g₀ a ha_super
  obtain ⟨C, hC0, hcore⟩ :=
    ricci_coeff_rfns_le (I := I) (M := M) g₀ hδ₀ (Csob * R)
      (by positivity)
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs_mem y v w
  have hδs_raw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  obtain ⟨hs0, hs1⟩ := hs
  have habs_eq : |1 - s| * δ' + |s| * δ = (1 - s) * δ' + s * δ := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
  have hsmall_le : |1 - s| * δ' + |s| * δ ≤ max δ₀ 0 := by
    rw [habs_eq]
    have h1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le (by linarith)
    have h2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have hδ₀_le : δ₀ ≤ max δ₀ 0 := le_max_left _ _
    nlinarith [h1, h2, hδ₀_le]
  have henv := hCsob T T' hR hTball hT'ball s ⟨hs0, hs1⟩ x
  have hmain := hcore (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) htie hsmall_le hδs_raw x henv
  constructor
  · have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (show Tensor0SBundle.TensorRSSpace 2 2 I x from
            linearizedRicciConnDiffOrder0Fib (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) x) := rfl
    rw [h0]
    exact Real.sqrt_le_sqrt hmain.1
  · have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
          (show Tensor0SBundle.TensorRSSpace 3 2 I x from
            linearizedRicciConnDiffOrder1Fib (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) x) := rfl
    rw [h1]
    exact Real.sqrt_le_sqrt hmain.2

end UniformBound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
