import DifferentialGeometry.Topology.Morse.ClosedEulerCharacteristic
import DifferentialGeometry.Topology.VectorField.RiemannianGradientIndex
import DifferentialGeometry.Topology.VectorField.RiemannianGradientBoundary
import DifferentialGeometry.Topology.VectorField.IndexSum
import DifferentialGeometry.Geometry.Metric.Construction.Existence

set_option autoImplicit false
noncomputable section
open Set Bundle
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Topology.Morse
namespace Poincare.VectorField
variable {d : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

theorem exists_closed_vectorField_interiorIndexSum_eq_eulerChar :
    ∃ V : ∀ x : M, TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      ∃ hfinite : {x | V x = 0}.Finite,
      ∃ hisolated : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x,
      ∃ hinterior : ∀ x, V x = 0 → I.IsInteriorPoint x,
        ∀ (K : Type) [Field K],
          interiorIndexSum I V hfinite hisolated hinterior =
            Poincare.Homology.eulerChar K (TopCat.of M) := by
  classical
  obtain ⟨g⟩ := DifferentialGeometry.Geometry.nonempty_contMDiffRiemannianMetric_of_sigmaCompact
    (I := I) (M := M)
  obtain ⟨f, hf, hnd, _, hfinite, hχ⟩ := Poincare.Morse.exists_morse_eulerChar I (M := M)
  let fs : C^∞⟮I, M; ℝ⟯ := ⟨f, hf⟩
  let V := gradientFun g fs
  have heq (x : M) : V x = 0 ↔ IsCriticalPointAt I f x :=
    gradientFun_eq_zero_iff_mfderiv_eq_zero g f x
  have hset : {x | V x = 0} = {x | IsCriticalPointAt I f x} := Set.ext heq
  have hVf : {x | V x = 0}.Finite := hset.symm ▸ hfinite
  have hVI (x : M) (_hx : V x = 0) : I.IsInteriorPoint x :=
    BoundarylessManifold.isInteriorPoint
  have hVi (x : M) (hx : V x = 0) : HasContinuousIsolatedZero I V x :=
    hasContinuousIsolatedZero_gradientFun_of_hessian_nondegenerate I g (hVI x hx)
      hf.contMDiffAt ((heq x).mp hx) (hnd x ((heq x).mp hx)).2
  refine ⟨V, gradientFun_smooth g hf, hVf, hVi, hVI, ?_⟩
  intro K instK
  let q : M → ℤ := fun p => (-1 : ℤ)^sigNeg (chartHessianAt
    (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p))
  have hs : hVf.toFinset = hfinite.toFinset := Set.Finite.toFinset_inj.mpr hset
  calc
    _ = ∑ p : hVf.toFinset, q p := by
      apply Finset.sum_congr rfl
      intro p _
      exact interiorIndex_gradientFun_eq_neg_one_pow_sigNeg I g
        (hVI p (hVf.mem_toFinset.mp p.property)) hf.contMDiffAt
        (hnd p ((heq p).mp (hVf.mem_toFinset.mp p.property))).2 _
    _ = ∑ p ∈ hVf.toFinset, q p := Finset.sum_coe_sort hVf.toFinset q
    _ = _ := by rw [hs]; exact (hχ K).2.symm

end Poincare.VectorField
