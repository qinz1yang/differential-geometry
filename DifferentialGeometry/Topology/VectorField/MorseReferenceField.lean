import DifferentialGeometry.Topology.Morse.EulerCharacteristic
import DifferentialGeometry.Topology.VectorField.RiemannianGradientBoundary
import DifferentialGeometry.Topology.VectorField.RiemannianGradientIndex
import DifferentialGeometry.Geometry.Metric.Construction.Existence

set_option autoImplicit false
noncomputable section
open Set Filter Bundle
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.VectorField
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_outward_gradient_indexSum_eq_eulerChar
    (g : SmoothRiemannianMetric (𝓡∂ (n + 1)) M) :
    ∃ f : C^∞⟮𝓡∂ (n + 1), M; ℝ⟯,
      (∀ x, f x ≤ 0) ∧
      (∀ x, f x = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint x) ∧
      (∀ x, IsCriticalPointAt (𝓡∂ (n + 1)) f x →
        IsNondegenerateCriticalPointAt (𝓡∂ (n + 1)) f x) ∧
      ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
        (fun x => (⟨x,gradientFun g f x⟩ : TangentBundle (𝓡∂ (n + 1)) M)) ∧
      (∀ x, (𝓡∂ (n + 1)).IsBoundaryPoint x →
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (gradientFun g f x) < 0) ∧
      ∃ hfinite : {x | gradientFun g f x = 0}.Finite,
      ∃ hinterior : ∀ x, gradientFun g f x = 0 → (𝓡∂ (n + 1)).IsInteriorPoint x,
      ∃ hisolated : ∀ x, gradientFun g f x = 0 →
        HasContinuousIsolatedZero (𝓡∂ (n + 1)) (gradientFun g f) x,
        (∀ x (hx : gradientFun g f x = 0),
          LinearMap.det (linearizationAtZero
            ((gradientFun_contMDiffAt g f.contMDiff.contMDiffAt).mdifferentiableAt (by simp))
            hx).toLinearMap ≠ 0) ∧
        ∀ (K : Type) [Field K], DifferentialGeometry.Homology.finiteHomologyType K (TopCat.of M) ∧
          (∑ p : hfinite.toFinset, interiorIndex (𝓡∂ (n + 1)) (gradientFun g f) p
            (hisolated p (hfinite.mem_toFinset.mp p.property))
            (hinterior p (hfinite.mem_toFinset.mp p.property))) =
              DifferentialGeometry.Homology.eulerChar K (TopCat.of M) := by
  classical
  obtain ⟨f,hf,hneg,hzero,_,hcrit,_,hcfinite,hχ⟩ :=
    DifferentialGeometry.Morse.exists_relative_morse_eulerChar (M := M) (n := n)
  let fs : C^∞⟮𝓡∂ (n + 1), M; ℝ⟯ := ⟨f,hf⟩
  have heq (x : M) : gradientFun g fs x = 0 ↔ IsCriticalPointAt (𝓡∂ (n + 1)) f x :=
    gradientFun_eq_zero_iff_mfderiv_eq_zero g f x
  have hset : {x | gradientFun g fs x = 0} = {x | IsCriticalPointAt (𝓡∂ (n + 1)) f x} :=
    Set.ext heq
  have hzfinite : {x | gradientFun g fs x = 0}.Finite := hset.symm ▸ hcfinite
  have hinterior (x : M) (hx : gradientFun g fs x = 0) :
      (𝓡∂ (n + 1)).IsInteriorPoint x := (hcrit x ((heq x).mp hx)).1
  have hisolated (x : M) (hx : gradientFun g fs x = 0) :
      HasContinuousIsolatedZero (𝓡∂ (n + 1)) (gradientFun g fs) x :=
    hasContinuousIsolatedZero_gradientFun_of_hessian_nondegenerate (𝓡∂ (n + 1)) g
      (hinterior x hx) hf.contMDiffAt ((hcrit x ((heq x).mp hx)).2.1)
      ((hcrit x ((heq x).mp hx)).2.2)
  refine ⟨fs,hneg,hzero,fun x hx => (hcrit x hx).2,gradientFun_smooth g hf,?_,
    hzfinite,hinterior,hisolated,?_,?_⟩
  · intro x hx
    apply proj_gradientFun_neg_of_nonpos g (hf.mdifferentiableAt (by simp)) hx
      ((hzero x).mpr hx) (Eventually.of_forall hneg)
    intro hdf
    exact ((𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint x).mp
      (hcrit x hdf).1 hx
  · intro x hx
    have hc := (heq x).mp hx
    erw [linearizationAtZero_gradientFun_eq_fderivInChart g (hinterior x hx) hf.contMDiffAt hc]
    exact det_fderiv_gradientInChart_ne_zero g (hinterior x hx) hf.contMDiffAt hc (hcrit x hc).2.2
  · intro K instK
    refine ⟨(hχ K).1,?_⟩
    have hs : hzfinite.toFinset = hcfinite.toFinset := Set.Finite.toFinset_inj.mpr hset
    let q : M → ℤ := fun p => (-1 : ℤ)^sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡∂ (n + 1)) p).symm y)) (extChartAt (𝓡∂ (n + 1)) p p))
    calc
      _ = ∑ p : hzfinite.toFinset, q p := by
        apply Finset.sum_congr rfl
        intro p _
        exact interiorIndex_gradientFun_eq_neg_one_pow_sigNeg (𝓡∂ (n + 1)) g
          (hinterior p (hzfinite.mem_toFinset.mp p.property)) hf.contMDiffAt
          (hcrit p ((heq p).mp (hzfinite.mem_toFinset.mp p.property))).2.2 _
      _ = ∑ p ∈ hzfinite.toFinset, q p := Finset.sum_coe_sort hzfinite.toFinset q
      _ = _ := by rw [hs]; exact (hχ K).2.symm

end DifferentialGeometry.VectorField

namespace DifferentialGeometry.VectorField
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_outward_vectorField_indexSum_eq_eulerChar :
    ∃ V : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x,
    ∃ hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x => (⟨x,V x⟩ : TangentBundle (𝓡∂ (n + 1)) M)),
      (∃ (g : SmoothRiemannianMetric (𝓡∂ (n + 1)) M)
        (f : C^∞⟮𝓡∂ (n + 1), M; ℝ⟯), V = gradientFun g f ∧
        (∀ x, f x ≤ 0) ∧ (∀ x, f x = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint x) ∧
        ∀ x, IsCriticalPointAt (𝓡∂ (n + 1)) f x →
          IsNondegenerateCriticalPointAt (𝓡∂ (n + 1)) f x) ∧
      (∀ x, (𝓡∂ (n + 1)).IsBoundaryPoint x →
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V x) < 0) ∧
      ∃ hfinite : {x | V x = 0}.Finite,
      ∃ hinterior : ∀ x, V x = 0 → (𝓡∂ (n + 1)).IsInteriorPoint x,
      ∃ hisolated : ∀ x, V x = 0 → HasContinuousIsolatedZero (𝓡∂ (n + 1)) V x,
        (∀ x (hx : V x = 0), LinearMap.det
          (linearizationAtZero (hV.contMDiffAt.mdifferentiableAt (by simp)) hx).toLinearMap ≠ 0) ∧
        ∀ (K : Type) [Field K], DifferentialGeometry.Homology.finiteHomologyType K (TopCat.of M) ∧
          (∑ p : hfinite.toFinset, interiorIndex (𝓡∂ (n + 1)) V p
            (hisolated p (hfinite.mem_toFinset.mp p.property))
            (hinterior p (hfinite.mem_toFinset.mp p.property))) =
              DifferentialGeometry.Homology.eulerChar K (TopCat.of M) := by
  obtain ⟨g⟩ := DifferentialGeometry.Geometry.nonempty_contMDiffRiemannianMetric_of_sigmaCompact
    (I := 𝓡∂ (n + 1)) (M := M)
  obtain ⟨f,hneg,hzero,hnd,hV,hout,hfinite,hinterior,hisolated,hdet,hχ⟩ :=
    exists_outward_gradient_indexSum_eq_eulerChar g
  exact ⟨gradientFun g f,hV,⟨g,f,rfl,hneg,hzero,hnd⟩,hout,
    hfinite,hinterior,hisolated,hdet,hχ⟩

end DifferentialGeometry.VectorField
