import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

private theorem rellich_kondrachov_W01p_seq_finset
    {ι : Type*} (s : Finset ι)
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ι → ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hu_mem : ∀ i n, DeGiorgi.MemW01p p (u i n) Ω)
    (R : ι → ℝ)
    (hu_bdd_fun : ∀ i n, eLpNorm (u i n) p (volume.restrict Ω) ≤ ENNReal.ofReal (R i))
    (hu_bdd_grad : ∀ i n, ∑ j : Fin d,
      eLpNorm (fun x => (Classical.choose (hu_mem i n).2).weakGrad x j)
        p (volume.restrict Ω) ≤ ENNReal.ofReal (R i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i ∈ s,
      ∃ v : EuclideanSpace ℝ (Fin d) → ℝ, MemLp v p (volume.restrict Ω) ∧
        Tendsto (fun n => eLpNorm (fun x => u i (φ n) x - v x) p
          (volume.restrict Ω)) atTop (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨φ, hφ, hconv⟩ := ih
    obtain ⟨ψ, hψ, v, hv, hlim⟩ := rellich_kondrachov_W01p_seq
      (d := d) (Ω := Ω) (p := p) (u := fun n => u i (φ n)) (R := R i)
      hΩ_open hΩ_bdd hp_one hp_top (fun n => hu_mem i (φ n))
      (fun n => hu_bdd_fun i (φ n)) (fun n => hu_bdd_grad i (φ n))
    refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨v, hv, hlim⟩
    · obtain ⟨w, hw, hwlim⟩ := hconv j hj
      exact ⟨w, hw, hwlim.comp hψ.tendsto_atTop⟩

theorem rellich_kondrachov_W01p_seq_coordinates
    {ι : Type*} [Finite ι]
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ι → ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hu_mem : ∀ i n, DeGiorgi.MemW01p p (u i n) Ω)
    (R : ι → ℝ)
    (hu_bdd_fun : ∀ i n, eLpNorm (u i n) p (volume.restrict Ω) ≤ ENNReal.ofReal (R i))
    (hu_bdd_grad : ∀ i n, ∑ j : Fin d,
      eLpNorm (fun x => (Classical.choose (hu_mem i n).2).weakGrad x j)
        p (volume.restrict Ω) ≤ ENNReal.ofReal (R i)) :
    ∃ (φ : ℕ → ℕ) (v : ι → EuclideanSpace ℝ (Fin d) → ℝ), StrictMono φ ∧
      (∀ i, MemLp (v i) p (volume.restrict Ω)) ∧
      ∀ i, Tendsto (fun n => eLpNorm (fun x => u i (φ n) x - v i x) p
        (volume.restrict Ω)) atTop (𝓝 0) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨φ, hφ, h⟩ := rellich_kondrachov_W01p_seq_finset Finset.univ
    hΩ_open hΩ_bdd hp_one hp_top u hu_mem R hu_bdd_fun hu_bdd_grad
  choose v hv ht using fun i => h i (Finset.mem_univ i)
  exact ⟨φ, v, hφ, hv, ht⟩

private theorem euclidean_norm_le_sum_norm {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℝ ι) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  classical
  have hsum : (∑ i, EuclideanSpace.single i (v i)) = v := by
    ext j
    simp
  calc
    ‖v‖ = ‖∑ i, EuclideanSpace.single i (v i)‖ := by rw [hsum]
    _ ≤ ∑ i, ‖EuclideanSpace.single i (v i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ := by simp only [PiLp.norm_single]

theorem rellich_kondrachov_W01p_seq_euclidean
    {ι : Type*} [Fintype ι]
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι)
    (hu_mem : ∀ i n, DeGiorgi.MemW01p p (fun x => u n x i) Ω)
    (R : ι → ℝ)
    (hu_bdd_fun : ∀ i n, eLpNorm (fun x => u n x i) p (volume.restrict Ω) ≤ ENNReal.ofReal (R i))
    (hu_bdd_grad : ∀ i n, ∑ j : Fin d,
      eLpNorm (fun x => (Classical.choose (hu_mem i n).2).weakGrad x j)
        p (volume.restrict Ω) ≤ ENNReal.ofReal (R i)) :
    ∃ (φ : ℕ → ℕ) (v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι), StrictMono φ ∧
      MemLp v p (volume.restrict Ω) ∧
      Tendsto (fun n => eLpNorm (fun x => u (φ n) x - v x) p
        (volume.restrict Ω)) atTop (𝓝 0) := by
  classical
  obtain ⟨φ, w, hφ, hw, ht⟩ := rellich_kondrachov_W01p_seq_coordinates
    hΩ_open hΩ_bdd hp_one hp_top (fun i n x => u n x i) hu_mem R hu_bdd_fun hu_bdd_grad
  let v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι :=
    fun x => WithLp.toLp 2 (fun i => w i x)
  have hv : MemLp v p (volume.restrict Ω) := MemLp.of_eval_piLp hw
  refine ⟨φ, v, hφ, hv, ?_⟩
  have hbound (n : ℕ) : eLpNorm (fun x => u (φ n) x - v x) p (volume.restrict Ω) ≤
      ∑ i, eLpNorm (fun x => u (φ n) x i - w i x) p (volume.restrict Ω) := by
    calc
      eLpNorm (fun x => u (φ n) x - v x) p (volume.restrict Ω) ≤
          eLpNorm (∑ i, fun x => ‖u (φ n) x i - w i x‖) p (volume.restrict Ω) := by
        apply eLpNorm_mono_real
        intro x
        simpa only [Finset.sum_apply, PiLp.sub_apply, v, PiLp.toLp_apply] using
          euclidean_norm_le_sum_norm (u (φ n) x - v x)
      _ ≤ ∑ i, eLpNorm (fun x => ‖u (φ n) x i - w i x‖) p (volume.restrict Ω) :=
        eLpNorm_sum_le (fun i _ => (((hu_mem i (φ n)).1.1).sub (hw i)).aestronglyMeasurable.norm)
          hp_one
      _ = _ := by simp only [eLpNorm_norm]
  have hsum : Tendsto (fun n => ∑ i, eLpNorm (fun x => u (φ n) x i - w i x) p
      (volume.restrict Ω)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => ht i)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) hbound

end DifferentialGeometry.Analysis.Sobolev
