import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich.Vector
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroBoundaryGraph

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

theorem rellich_kondrachov_W01p_sub_seq_euclidean_closed_image
    {ι : Type*} [Fintype ι]
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι)
    (hb : MemLp b p (volume.restrict Ω))
    (hu_mem : ∀ i n, DeGiorgi.MemW01p p (fun x => u n x i - b x i) Ω)
    (R : ι → ℝ)
    (hu_bdd_fun : ∀ i n, eLpNorm (fun x => u n x i - b x i) p
      (volume.restrict Ω) ≤ ENNReal.ofReal (R i))
    (hu_bdd_grad : ∀ i n, ∑ j : Fin d,
      eLpNorm (fun x => (Classical.choose (hu_mem i n).2).weakGrad x j)
        p (volume.restrict Ω) ≤ ENNReal.ofReal (R i))
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsClosed K)
    (huK : ∀ n, ∀ᵐ x ∂volume.restrict Ω, u n x ∈ K) :
    ∃ (φ : ℕ → ℕ) (v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι),
      StrictMono φ ∧ MemLp v p (volume.restrict Ω) ∧
      Tendsto (fun n => eLpNorm (fun x => u (φ n) x - v x) p
        (volume.restrict Ω)) atTop (𝓝 0) ∧
      (∀ᵐ x ∂volume.restrict Ω, Tendsto (fun n => u (φ n) x) atTop (𝓝 (v x))) ∧
      ∀ᵐ x ∂volume.restrict Ω, v x ∈ K := by
  classical
  obtain ⟨φ, w, hφ, hw, hlim⟩ := rellich_kondrachov_W01p_seq_euclidean
    hΩ_open hΩ_bdd hp_one hp_top (fun n x => u n x - b x)
    hu_mem R hu_bdd_fun hu_bdd_grad
  let v := fun x => w x + b x
  have hv : MemLp v p (volume.restrict Ω) := hw.add hb
  have hum (n : ℕ) : MemLp (u n) p (volume.restrict Ω) := by
    have hsub : MemLp (fun x => u n x - b x) p (volume.restrict Ω) :=
      MemLp.of_eval_piLp (fun i => (hu_mem i n).1.1)
    convert hsub.add hb using 1
    ext x
    exact (sub_add_cancel _ _).symm
  have hlimv : Tendsto (fun n => eLpNorm (fun x => u (φ n) x - v x) p
      (volume.restrict Ω)) atTop (𝓝 0) := by
    have heq (n : ℕ) : (fun x => u (φ n) x - b x - w x) =
        (fun x => u (φ n) x - v x) := by
      funext x
      dsimp only [v]
      abel
    simpa only [heq] using hlim
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hp_one))
    (fun n => (hum (φ n)).aestronglyMeasurable) hv.aestronglyMeasurable hlimv
  obtain ⟨ψ, hψ, hae⟩ := hmeasure.exists_seq_tendsto_ae
  refine ⟨φ ∘ ψ, v, hφ.comp hψ, hv, hlimv.comp hψ.tendsto_atTop, hae, ?_⟩
  filter_upwards [hae, ae_all_iff.mpr huK] with x hx hKx
  exact hK.mem_of_tendsto hx (Eventually.of_forall fun n => hKx (φ (ψ n)))

end DifferentialGeometry.Analysis.Sobolev

end

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

theorem rellich_kondrachov_H01_sub_seq_euclidean_closed_image
    {ι : Type*} [Fintype ι]
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (u : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι)
    (hb : MemLp b 2 (volume.restrict Ω))
    (hu_mem : ∀ i n, DeGiorgi.MemW01p 2 (fun x => u n x i - b x i) Ω)
    (R : ι → ℝ)
    (hu_bdd_fun : ∀ i n, eLpNorm (fun x => u n x i - b x i) 2
      (volume.restrict Ω) ≤ ENNReal.ofReal (R i))
    (hu_bdd_grad : ∀ i n, ∑ j : Fin d,
      eLpNorm (fun x => (Classical.choose (hu_mem i n).2).weakGrad x j)
        2 (volume.restrict Ω) ≤ ENNReal.ofReal (R i))
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsClosed K)
    (huK : ∀ n, ∀ᵐ x ∂volume.restrict Ω, u n x ∈ K) :
    ∃ (φ : ℕ → ℕ) (v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι),
      StrictMono φ ∧ MemLp v 2 (volume.restrict Ω) ∧
      (∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - b x i) Ω) ∧
      Tendsto (fun n => eLpNorm (fun x => u (φ n) x - v x) 2
        (volume.restrict Ω)) atTop (𝓝 0) ∧
      (∀ᵐ x ∂volume.restrict Ω, Tendsto (fun n => u (φ n) x) atTop (𝓝 (v x))) ∧
      ∀ᵐ x ∂volume.restrict Ω, v x ∈ K := by
  obtain ⟨φ, v, hφ, hv, hlim, hae, hvK⟩ :=
    rellich_kondrachov_W01p_sub_seq_euclidean_closed_image hΩ_open hΩ_bdd
      (by norm_num) (by norm_num) u b hb hu_mem R hu_bdd_fun hu_bdd_grad hK huK
  refine ⟨φ, v, hφ, hv, ?_, hlim, hae, hvK⟩
  exact Euclidean.memW01p_sub_of_tendsto_L2 hΩ_open hb hv
    (fun i n => hu_mem i (φ n)) (fun i => ENNReal.ofReal (R i))
    (fun _ => ENNReal.ofReal_ne_top) (fun i n => hu_bdd_grad i (φ n)) hlim

end DifferentialGeometry.Analysis.Sobolev

end
