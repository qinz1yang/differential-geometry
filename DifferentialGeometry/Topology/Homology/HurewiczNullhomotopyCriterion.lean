import DifferentialGeometry.Topology.Homology.HurewiczSphereCriterion
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section

open ContinuousMap Metric

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]


def sphereClosedBallInclusion (n : ℕ) :
    C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      closedBall (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) where
  toFun v := ⟨v.val, sphere_subset_closedBall v.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _


theorem zerothHomotopy_mk_eq_const_iff_nullhomotopic [PathConnectedSpace X] (n : ℕ) (x : X)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    ZerothHomotopy.mk f = ZerothHomotopy.mk (ContinuousMap.const _ x) ↔ f.Nullhomotopic := by
  constructor
  · intro h
    exact ⟨x, (homotopic_iff_joined _ _).mpr (Quotient.exact h)⟩
  · rintro ⟨y, hy⟩
    refine Quotient.sound ((homotopic_iff_joined _ _).mp hy |>.trans ?_)
    exact ⟨⟨ContinuousMap.const'.comp (PathConnectedSpace.somePath y x).toContinuousMap,
      by simp, by simp⟩⟩


theorem nullhomotopic_of_freeSphereHomologyImage_eq_zero_of_ballExtension (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (h : ∀ f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
      freeSphereHomologyImage n c (ZerothHomotopy.mk f) = 0 →
        ∃ u : C(closedBall (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
          u.comp (sphereClosedBallInclusion n) = f)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X))
    (hf : freeSphereHomologyImage n c (ZerothHomotopy.mk f) = 0) :
    f.Nullhomotopic := by
  have hcontr : ContractibleSpace (closedBall (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
    contractibleSpace_closedBall (x := (0 : EuclideanSpace ℝ (Fin (n + 2)))) (r := 1)
      (by norm_num)
  obtain ⟨u, hu⟩ := h f hf
  have hincl : (sphereClosedBallInclusion n).Nullhomotopic := by
    simpa using (@id_nullhomotopic (closedBall (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) _
      hcontr).comp_left (sphereClosedBallInclusion n)
  rw [← hu]
  exact hincl.comp_right u


theorem mk_eq_const_of_freeSphereHomologyImage_eq_zero_of_ballExtension [PathConnectedSpace X]
    (n : ℕ) (x : X) (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (h : ∀ f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
      freeSphereHomologyImage n c (ZerothHomotopy.mk f) = 0 →
        ∃ u : C(closedBall (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
          u.comp (sphereClosedBallInclusion n) = f)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X))
    (hf : freeSphereHomologyImage n c (ZerothHomotopy.mk f) = 0) :
    ZerothHomotopy.mk f = ZerothHomotopy.mk (ContinuousMap.const _ x) :=
  (zerothHomotopy_mk_eq_const_iff_nullhomotopic n x f).mpr
    (nullhomotopic_of_freeSphereHomologyImage_eq_zero_of_ballExtension n c h f hf)


theorem forall_sphereHurewicz_eq_zero_of_injective (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (hinj : Function.Injective (sphereHurewicz n x c))
    (a : HomotopyGroup (Fin (n + 1)) X x) (ha : sphereHurewicz n x c a = 0) : a = 1 :=
  hinj (by rw [ha, sphereHurewicz_one])


theorem forall_freeSphereHomologyImage_eq_zero_imp_mk_eq_iff_integralLiftedSphereGenerator
    (n : ℕ) (x : X) (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (hc : IsSphereHomologyGenerator n c) :
    (∀ f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
        freeSphereHomologyImage n c (ZerothHomotopy.mk f) = 0 →
          ZerothHomotopy.mk f = ZerothHomotopy.mk (ContinuousMap.const _ x)) ↔
      (∀ f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
        freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
          (ZerothHomotopy.mk f) = 0 →
          ZerothHomotopy.mk f = ZerothHomotopy.mk (ContinuousMap.const _ x)) := by
  rcases (isSphereHomologyGenerator_iff_eq_or_eq_neg_integralLiftedSphereGenerator n c).mp hc
    with rfl | hneg
  · exact Iff.rfl
  · have hneg' : freeSphereHomologyImage (X := X) n (-integralLiftedSphereGenerator.{u} n) =
        fun a => -freeSphereHomologyImage (X := X) n (integralLiftedSphereGenerator.{u} n) a := by
      funext a
      simpa using freeSphereHomologyImage_zsmul (X := X) n (-1)
        (integralLiftedSphereGenerator.{u} n) a
    rw [hneg]
    have hiff : ∀ f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
        (freeSphereHomologyImage (X := X) n (-integralLiftedSphereGenerator.{u} n)
            (ZerothHomotopy.mk f) = 0) ↔
          (freeSphereHomologyImage (X := X) n (integralLiftedSphereGenerator.{u} n)
            (ZerothHomotopy.mk f) = 0) := by
      intro f
      rw [congrFun hneg' (ZerothHomotopy.mk f), neg_eq_zero]
    exact ⟨fun h f hf => h f ((hiff f).mpr hf), fun h f hf => h f ((hiff f).mp hf)⟩

end DifferentialGeometry.Topology
