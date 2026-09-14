import DifferentialGeometry.Topology.Homology.SphereHomologyVanishing
import DifferentialGeometry.Topology.Homology.LocalCharts
import DifferentialGeometry.Topology.Homology.ContractibleCoverOne
import DifferentialGeometry.Topology.Homology.RelativeEmpty
import Mathlib.Analysis.Normed.Module.FiniteDimension

section

noncomputable section

open CategoryTheory ContinuousMap Metric Module Set

universe u

namespace DifferentialGeometry.Topology

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def integralEuclideanLocalTopZeroEquiv (n : ℕ) (hd : finrank ℝ E = n + 2) :
    integralLocalHomology (n + 2) (0 : E) ≃ₗ[ℤ] ℤ :=
  ((integralRelativeConnectingEquivOfContractible (n + 1) (by omega)
    ({0}ᶜ : Set E)).trans (integralPuncturedSpaceSphereHomologyEquiv E (n + 1))).trans
      (integralSphereTopHomologyEquiv n E hd)

def integralEuclideanLocalTopEquiv (n : ℕ) (hd : finrank ℝ E = n + 2) (x : E) :
    integralLocalHomology (n + 2) x ≃ₗ[ℤ] ℤ := by
  let e : E ≃ₜ E := Homeomorph.addRight (-x)
  have hx : e x = 0 := add_neg_cancel x
  have h := (integralLocalHomologyHomeomorphIso (n + 2) e x).toLinearEquiv
  rw [hx] at h
  exact h.trans (integralEuclideanLocalTopZeroEquiv E n hd)

def integralManifoldLocalTopEquiv (n : ℕ) (hd : finrank ℝ E = n + 2)
    (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (x : M) :
    integralLocalHomology (n + 2) x ≃ₗ[ℤ] ℤ :=
  (integralLocalHomologyChartIso (Y := E) (n + 2) x).toLinearEquiv.trans
    (integralEuclideanLocalTopEquiv E n hd (chartAt E x x))

def integralEuclideanLocalTopGenerator (n : ℕ) (hd : finrank ℝ E = n + 2) (x : E) :
    integralLocalHomology (n + 2) x :=
  (integralEuclideanLocalTopEquiv E n hd x).symm 1


theorem integralEuclideanLocalTopGenerator_coordinate (n : ℕ) (hd : finrank ℝ E = n + 2)
    (x : E) :
    integralEuclideanLocalTopEquiv E n hd x (integralEuclideanLocalTopGenerator E n hd x) = 1 :=
  (integralEuclideanLocalTopEquiv E n hd x).apply_symm_apply 1


theorem integralEuclideanLocalTopGenerator_zsmul_bijective (n : ℕ)
    (hd : finrank ℝ E = n + 2) (x : E) :
    Function.Bijective (fun z : ℤ => z • integralEuclideanLocalTopGenerator E n hd x) := by
  have hfun : (fun z : ℤ => z • integralEuclideanLocalTopGenerator E n hd x) =
      ⇑(integralEuclideanLocalTopEquiv E n hd x).symm := by
    funext z
    apply (integralEuclideanLocalTopEquiv E n hd x).injective
    rw [map_zsmul, integralEuclideanLocalTopGenerator_coordinate, smul_eq_mul, mul_one,
      LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (integralEuclideanLocalTopEquiv E n hd x).symm.bijective


theorem integralEuclideanLocalTopGenerator_ne_zero (n : ℕ) (hd : finrank ℝ E = n + 2) (x : E) :
    integralEuclideanLocalTopGenerator E n hd x ≠ 0 := by
  intro h
  have hh := congrArg (integralEuclideanLocalTopEquiv E n hd x) h
  rw [integralEuclideanLocalTopGenerator_coordinate, map_zero] at hh
  exact one_ne_zero hh


def integralManifoldLocalTopGenerator (n : ℕ) (hd : finrank ℝ E = n + 2)
    (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (x : M) :
    integralLocalHomology (n + 2) x :=
  (integralManifoldLocalTopEquiv E n hd M x).symm 1


theorem integralManifoldLocalTopGenerator_coordinate (n : ℕ) (hd : finrank ℝ E = n + 2)
    (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (x : M) :
    integralManifoldLocalTopEquiv E n hd M x (integralManifoldLocalTopGenerator E n hd M x) = 1 :=
  (integralManifoldLocalTopEquiv E n hd M x).apply_symm_apply 1


theorem integralManifoldLocalTopGenerator_zsmul_bijective (n : ℕ)
    (hd : finrank ℝ E = n + 2) (M : Type u) [TopologicalSpace M] [T1Space M]
    [ChartedSpace E M] (x : M) :
    Function.Bijective (fun z : ℤ => z • integralManifoldLocalTopGenerator E n hd M x) := by
  have hfun : (fun z : ℤ => z • integralManifoldLocalTopGenerator E n hd M x) =
      ⇑(integralManifoldLocalTopEquiv E n hd M x).symm := by
    funext z
    apply (integralManifoldLocalTopEquiv E n hd M x).injective
    rw [map_zsmul, integralManifoldLocalTopGenerator_coordinate, smul_eq_mul, mul_one,
      LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (integralManifoldLocalTopEquiv E n hd M x).symm.bijective


theorem integralManifoldLocalTopGenerator_ne_zero (n : ℕ) (hd : finrank ℝ E = n + 2)
    (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (x : M) :
    integralManifoldLocalTopGenerator E n hd M x ≠ 0 := by
  intro h
  have hh := congrArg (integralManifoldLocalTopEquiv E n hd M x) h
  rw [integralManifoldLocalTopGenerator_coordinate, map_zero] at hh
  exact one_ne_zero hh

end DifferentialGeometry.Topology

end

end

section

noncomputable section

open CategoryTheory Metric Module Set

universe u

namespace DifferentialGeometry.Topology

private def innerProductLocalTopEquiv
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    integralLocalHomology (finrank ℝ E) (0 : E) ≃ₗ[ℤ] ℤ := by
  by_cases hlarge : 2 ≤ finrank ℝ E
  · have hd : finrank ℝ E = (finrank ℝ E - 2) + 2 := by omega
    rw [hd]
    exact integralEuclideanLocalTopZeroEquiv E (finrank ℝ E - 2) hd
  by_cases hzero : finrank ℝ E = 0
  · have hempty : ({0}ᶜ : Set E) = ∅ := by
      ext x
      constructor
      · intro hx
        exact (hx (finrank_zero_iff_forall_zero.mp hzero x)).elim
      · intro hx
        exact hx.elim
    change integralRelativeHomology (finrank ℝ E) ({0}ᶜ : Set E) ≃ₗ[ℤ] ℤ
    rw [hzero, hempty]
    exact (integralAbsoluteToRelativeEmptyEquiv 0 E).symm.trans
      (integralSingularHomologyZeroEquiv (X := E))
  have hone : finrank ℝ E = 1 := by omega
  change integralRelativeHomology (finrank ℝ E) ({0}ᶜ : Set E) ≃ₗ[ℤ] ℤ
  rw [hone]
  exact (((integralRelativeConnectingZeroKernelEquiv ({0}ᶜ : Set E)).trans
    (integralZeroMapKernelReducedEquiv (singularSubspaceInclusion ({0}ᶜ : Set E)))).trans
      (integralReducedZeroHomotopyEquiv (puncturedSpaceSphereHomotopyEquiv E))).trans
        (integralZeroSphereReducedEquiv hone)

theorem exists_integralLocalHomology_generator
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (p : E) :
    ∃ c : integralLocalHomology (finrank ℝ E) p,
      Function.Bijective (fun k : ℤ => k • c) := by
  let ι := Module.Free.ChooseBasisIndex ℝ E
  let b : Basis ι ℝ E := Module.Free.chooseBasis ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ ι :=
    b.equivFunL.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let h := e.toHomeomorph.trans (Homeomorph.subRight (e p))
  have hp : h p = 0 := sub_self (e p)
  have he := (integralLocalHomologyHomeomorphIso (finrank ℝ E) h p).toLinearEquiv
  rw [hp] at he
  have hzero : integralLocalHomology (finrank ℝ E) (0 : EuclideanSpace ℝ ι) ≃ₗ[ℤ] ℤ := by
    rw [e.toLinearEquiv.finrank_eq]
    exact innerProductLocalTopEquiv (EuclideanSpace ℝ ι)
  let f := he.trans hzero
  let c := f.symm 1
  have hmap (k : ℤ) : f (k • c) = k := by
    rw [map_zsmul]
    change k • f (f.symm 1) = k
    rw [f.apply_symm_apply]
    exact mul_one k
  refine ⟨c, ?_, ?_⟩
  · intro k l hkl
    exact (hmap k).symm.trans ((congrArg f hkl).trans (hmap l))
  · intro a
    exact ⟨f a, f.injective (hmap (f a))⟩

end DifferentialGeometry.Topology

end

end
