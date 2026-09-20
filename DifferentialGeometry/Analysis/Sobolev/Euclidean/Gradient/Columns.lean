import DifferentialGeometry.Analysis.Integration.Lp.EuclideanColumns
import Mathlib.Analysis.Calculus.Rademacher
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.SmoothTests

noncomputable section

open Filter MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem euclideanColumn_gradLpOfWitness_coeFn
    {Ω : Set E} {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω) (j : Fin d) :
    (Lp.euclideanColumn (fun i => DeGiorgi.gradLpOfWitness (hf i)) j : E → F)
      =ᵐ[volume.restrict Ω] (fun x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) := by
  have hg : ∀ᵐ x ∂volume.restrict Ω, ∀ i,
      DeGiorgi.gradLpOfWitness (hf i) x = (hf i).weakGrad x :=
    ae_all_iff.mpr fun i => (hf i).weakGrad_memLp.coeFn_toLp
  filter_upwards [Lp.euclideanColumn_coeFn
    (fun i => DeGiorgi.gradLpOfWitness (hf i)) j, hg] with x hx hg
  exact hx.trans (PiLp.ext fun i => congrArg (fun z : E => z j) (hg i))

theorem euclideanColumn_gradLpOfWitness_eq_fderiv_ae
    {Ω : Set E} {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hs : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hrep : ∀ i j, (fun x => (hs i).weakGrad x j) =ᵐ[volume.restrict Ω]
      (fun x => fderiv ℝ (fun y => f y i) x (EuclideanSpace.single j 1))) (j : Fin d) :
    (Lp.euclideanColumn (fun i => DeGiorgi.gradLpOfWitness (hs i)) j : E → F)
      =ᵐ[volume.restrict Ω] (fun x => fderiv ℝ f x (EuclideanSpace.single j 1)) := by
  have hrepj : ∀ᵐ x ∂volume.restrict Ω, ∀ i,
      (hs i).weakGrad x j =
        fderiv ℝ (fun y => f y i) x (EuclideanSpace.single j 1) :=
    ae_all_iff.mpr fun i => hrep i j
  filter_upwards [euclideanColumn_gradLpOfWitness_coeFn hs j,
    ae_restrict_of_ae (s := Ω) hf.ae_differentiableAt, hrepj] with x hx hdiff hrepj
  rw [hx]
  apply PiLp.ext
  intro i
  change (hs i).weakGrad x j = (fderiv ℝ f x (EuclideanSpace.single j 1)) i
  rw [hrepj i]
  have hchain : fderiv ℝ (fun y => f y i) x =
      (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ f x) :=
    ((ContinuousLinearMap.hasFDerivAt (EuclideanSpace.proj (𝕜 := ℝ) i)).comp x
      hdiff.hasFDerivAt).fderiv
  rw [hchain]
  rfl

theorem exists_lp_gradient_columns_of_tendsto_inner
    {Ω : Set E} (f : ℕ → E → F) (v : E → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2 (fun x => f n x i) Ω)
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω)
    (K : ℕ → ℝ≥0) (hf : ∀ n, LipschitzWith (K n) (f n))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[volume.restrict Ω]
      (fun x => fderiv ℝ (fun y => f n y i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : Lp E 2 (volume.restrict Ω)),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z))) :
    ∃ (A : Fin d → ℕ → Lp F 2 (volume.restrict Ω))
      (A₀ : Fin d → Lp F 2 (volume.restrict Ω)),
      (∀ j n, (A j n : E → F) =ᵐ[volume.restrict Ω]
        (fun x => fderiv ℝ (f n) x (EuclideanSpace.single j 1))) ∧
      (∀ j, (A₀ j : E → F) =ᵐ[volume.restrict Ω]
        (fun x => WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ∧
      ∀ j (L : Lp F 2 (volume.restrict Ω) →L[ℝ] ℝ),
        Tendsto (fun n => L (A j n)) atTop (𝓝 (L (A₀ j))) := by
  refine ⟨(fun j n => Lp.euclideanColumn
    (fun i => DeGiorgi.gradLpOfWitness (hs n i)) j),
    (fun j => Lp.euclideanColumn (fun i => DeGiorgi.gradLpOfWitness (hv i)) j), ?_, ?_, ?_⟩
  · intro j n
    exact euclideanColumn_gradLpOfWitness_eq_fderiv_ae (hf n) (hs n) (hrep n) j
  · intro j
    exact euclideanColumn_gradLpOfWitness_coeFn hv j
  · intro j L
    exact Lp.tendsto_dual_euclideanColumn_of_tendsto_inner
      (fun i n => DeGiorgi.gradLpOfWitness (hs n i))
      (fun i => DeGiorgi.gradLpOfWitness (hv i)) hweak j L

end DifferentialGeometry.Analysis.Sobolev.Euclidean
