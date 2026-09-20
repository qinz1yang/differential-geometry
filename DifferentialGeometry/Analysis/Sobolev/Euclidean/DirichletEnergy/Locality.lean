import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Locality
import DifferentialGeometry.Analysis.Integration.Integral.Comparison
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Finite ι]
variable {Ω U : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem weakGrad_columns_ae_eq_of_ae_eq
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hU : IsOpen U) (hsub : U ⊆ Ω)
    {f g : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness p (fun x => f x i) Ω)
    (hg : ∀ i, DeGiorgi.MemW1pWitness p (fun x => g x i) Ω)
    (hfg : f =ᵐ[volume.restrict U] g) :
    ∀ᵐ x ∂volume.restrict U, ∀ j : Fin d,
      WithLp.toLp 2 (fun i => (hf i).weakGrad x j) =
        WithLp.toLp 2 (fun i => (hg i).weakGrad x j) := by
  have heq (i : ι) : (hf i).weakGrad =ᵐ[volume.restrict U] (hg i).weakGrad :=
    DeGiorgi.MemW1pWitness.weakGrad_ae_eq_of_ae_eq hp hU hsub (hf i) (hg i)
      (hfg.mono fun x hx => congrArg (fun z : F => z i) hx)
  filter_upwards [ae_all_iff.mpr heq] with x hx
  intro j
  congr 1
  funext i
  rw [hx i]

theorem quadratic_weakGrad_columns_ae_eq_of_ae_eq
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hU : IsOpen U) (hsub : U ⊆ Ω)
    {f g : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness p (fun x => f x i) Ω)
    (hg : ∀ i, DeGiorgi.MemW1pWitness p (fun x => g x i) Ω)
    (hfg : f =ᵐ[volume.restrict U] g)
    (A : E → F → F →L[ℝ] F →L[ℝ] ℝ) :
    ∀ᵐ x ∂volume.restrict U, ∀ j : Fin d,
      A x (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) =
      A x (g x) (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hg i).weakGrad x j)) := by
  filter_upwards [hfg, weakGrad_columns_ae_eq_of_ae_eq hp hU hsub hf hg hfg] with x hx hgrad
  intro j
  rw [hx, hgrad j]

theorem sum_integral_quadratic_weakGrad_closedBall_le_of_ae_eq_on_collar
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hΩ : IsOpen Ω)
    {f g : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness p (fun x => f x i) Ω)
    (hg : ∀ i, DeGiorgi.MemW1pWitness p (fun x => g x i) Ω)
    (A : E → F → F →L[ℝ] F →L[ℝ] ℝ)
    {c : E} {r R : ℝ} (hrR : r ≤ R) (hball : Metric.closedBall c R ⊆ Ω)
    (hfg : f =ᵐ[volume.restrict (Ω \ Metric.closedBall c r)] g)
    (hfi : ∀ j : Fin d, IntegrableOn
      (fun x => A x (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) (Metric.closedBall c R))
    (hgi : ∀ j : Fin d, IntegrableOn
      (fun x => A x (g x) (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))) (Metric.closedBall c R))
    (hle : (∑ j : Fin d, ∫ x in Metric.closedBall c R,
      A x (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) ≤
      ∑ j : Fin d, ∫ x in Metric.closedBall c R,
        A x (g x) (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))) :
    (∑ j : Fin d, ∫ x in Metric.closedBall c r,
      A x (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) ≤
      ∑ j : Fin d, ∫ x in Metric.closedBall c r,
        A x (g x) (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hg i).weakGrad x j)) := by
  let Ef (j : Fin d) (x : E) := A x (f x)
    (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
  let Eg (j : Fin d) (x : E) := A x (g x)
    (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
  have hsub : Metric.closedBall c r ⊆ Metric.closedBall c R := Metric.closedBall_subset_closedBall hrR
  have hcollar : ∀ᵐ x ∂volume.restrict (Ω \ Metric.closedBall c r),
      ∀ j, Ef j x = Eg j x :=
    quadratic_weakGrad_columns_ae_eq_of_ae_eq hp (hΩ.sdiff Metric.isClosed_closedBall)
      sdiff_subset hf hg hfg A
  have hrestrict : ∀ᵐ x ∂volume.restrict (Metric.closedBall c R \ Metric.closedBall c r),
      ∀ j, Ef j x = Eg j x :=
    ae_restrict_of_ae_restrict_of_subset (sdiff_subset_sdiff_left hball) hcollar
  have hsum : (fun x => ∑ j, Ef j x) =ᵐ[volume.restrict
      (Metric.closedBall c R \ Metric.closedBall c r)] (fun x => ∑ j, Eg j x) :=
    hrestrict.mono fun x hx => Finset.sum_congr rfl fun j _ => hx j
  have hEfR : IntegrableOn (fun x => ∑ j, Ef j x) (Metric.closedBall c R) :=
    integrable_finsetSum _ fun j _ => hfi j
  have hEgR : IntegrableOn (fun x => ∑ j, Eg j x) (Metric.closedBall c R) :=
    integrable_finsetSum _ fun j _ => hgi j
  have hleR : (∫ x in Metric.closedBall c R, ∑ j, Ef j x) ≤
      ∫ x in Metric.closedBall c R, ∑ j, Eg j x := by
    rw [integral_finsetSum _ (fun j _ => hfi j), integral_finsetSum _ (fun j _ => hgi j)]
    exact hle
  have h := setIntegral_le_of_ae_eq_on_sdiff measurableSet_closedBall hsub hEfR hEgR hsum hleR
  rw [integral_finsetSum _ (fun j _ => (hfi j).mono_set hsub),
    integral_finsetSum _ (fun j _ => (hgi j).mono_set hsub)] at h
  exact h

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
