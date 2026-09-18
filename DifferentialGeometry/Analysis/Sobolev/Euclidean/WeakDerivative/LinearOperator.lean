import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

theorem exists_continuousLinearMap_hasWeakPartialDeriv
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {d : ℕ} {Ω Ω₀ : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ₀ : IsOpen Ω₀) (hsub : Ω₀ ⊆ Ω) (j : Fin d)
    (A : X →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω)) (C : ℝ≥0)
    (hderiv : ∀ x : X, ∃ g : Lp ℝ 2 (volume.restrict Ω₀),
      DeGiorgi.HasWeakPartialDeriv j g (A x) Ω₀ ∧ ‖g‖ ≤ (C : ℝ) * ‖x‖) :
    ∃ D : X →L[ℝ] Lp ℝ 2 (volume.restrict Ω₀),
      (∀ x, DeGiorgi.HasWeakPartialDeriv j (D x) (A x) Ω₀) ∧ ‖D‖ ≤ (C : ℝ) := by
  classical
  choose F hF hnorm using hderiv
  have hA (x : X) : LocallyIntegrable (A x) (volume.restrict Ω₀) :=
    ((Lp.memLp (A x)).mono_measure (Measure.restrict_mono hsub le_rfl)).locallyIntegrable
      (by norm_num)
  have hFloc (x : X) : LocallyIntegrable (F x) (volume.restrict Ω₀) :=
    (Lp.memLp (F x)).locallyIntegrable (by norm_num)
  let D₀ : X →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω₀) :=
    { toFun := F
      map_add' := by
        intro x y
        have hs := (hF x).add (hF y) (hA x) (hA y) (hFloc x) (hFloc y)
        have hs' : DeGiorgi.HasWeakPartialDeriv j (F x + F y : Lp ℝ 2 (volume.restrict Ω₀)) (A (x + y)) Ω₀ := by
          rw [map_add]
          exact hs.congr_ae
            ((Lp.coeFn_add (A x) (A y)).symm.filter_mono
              (ae_mono (Measure.restrict_mono hsub le_rfl)))
            (Lp.coeFn_add (F x) (F y)).symm
        exact Lp.ext (DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₀ (hF (x + y)) hs'
          (hFloc (x + y)) ((Lp.memLp (F x + F y)).locallyIntegrable (by norm_num)))
      map_smul' := by
        intro c x
        have hs := (hF x).const_smul c
        have hs' : DeGiorgi.HasWeakPartialDeriv j (c • F x : Lp ℝ 2 (volume.restrict Ω₀)) (A (c • x)) Ω₀ := by
          rw [map_smul]
          exact hs.congr_ae
            ((Lp.coeFn_smul c (A x)).symm.filter_mono
              (ae_mono (Measure.restrict_mono hsub le_rfl)))
            (Lp.coeFn_smul c (F x)).symm
        exact Lp.ext (DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₀ (hF (c • x)) hs'
          (hFloc (c • x)) ((Lp.memLp (c • F x)).locallyIntegrable (by norm_num))) }
  let D := D₀.mkContinuous C (fun x => hnorm x)
  refine ⟨D, hF, ?_⟩
  exact ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg hnorm

end DifferentialGeometry.Analysis.Sobolev.Euclidean
