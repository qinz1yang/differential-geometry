import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialGraph
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Iterated

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {T : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memWkp_toFun_of_weak_partial_tree
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hT : 0 < T) (hΩ : IsOpen Ω)
    (W : ∀ m : ℕ, (Fin m → Fin d) → timeH1 (Lp ℝ p (volume.restrict Ω)) T)
    (hweak : ∀ m β i, ∀ᵐ t ∂timeMeasure T, DeGiorgi.HasWeakPartialDeriv i
      ((W (m + 1) (Fin.cons i β)).toFun t) ((W m β).toFun t) Ω) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ N : ℕ,
      MemWkp N p ((W 0 (fun i => Fin.elim0 i)).toFun t) Ω := by
  intro t ht N
  apply memWkp_of_weak_partial_tree (Fact.out : 1 ≤ p) hΩ
    (fun m β z => (W m β).toFun t z) (fun m β => Lp.memLp ((W m β).toFun t)) ?_ N
  intro m β i
  exact hasWeakPartialDeriv_of_continuousOn_Lp
    (closure_interior_Icc hT.ne).symm.subset i
    (W m β).toFun (W (m + 1) (Fin.cons i β)).toFun
    (W m β).continuousOn_toFun (W (m + 1) (Fin.cons i β)).continuousOn_toFun
    (hweak m β i) t ht

theorem exists_contDiffOn_ae_eq_toFun_of_weak_partial_tree
    (hT : 0 < T) (hΩ : IsOpen Ω)
    (W : ∀ m : ℕ, (Fin m → Fin d) → timeH1 (Lp ℝ 2 (volume.restrict Ω)) T)
    (hweak : ∀ m β i, ∀ᵐ t ∂timeMeasure T, DeGiorgi.HasWeakPartialDeriv i
      ((W (m + 1) (Fin.cons i β)).toFun t) ((W m β).toFun t) Ω) :
    ∀ t ∈ Icc (0 : ℝ) T, ∃ v : E → ℝ,
      ContDiffOn ℝ (∞ : WithTop ℕ∞) v Ω ∧
        ((W 0 (fun i => Fin.elim0 i)).toFun t : E → ℝ) =ᵐ[volume.restrict Ω] v := by
  intro t ht
  exact Sobolev.EuclideanIteratedEmbedding.exists_contDiffOn_ae_eq_of_forall_memWkp_two hΩ
    (memWkp_toFun_of_weak_partial_tree hT hΩ W hweak t ht)

theorem tendsto_wkpNorm_sub_toFun_of_weak_partial_tree
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hT : 0 < T) (hΩ : IsOpen Ω)
    (W : ∀ m : ℕ, (Fin m → Fin d) → timeH1 (Lp ℝ p (volume.restrict Ω)) T)
    (hweak : ∀ m β i, ∀ᵐ t ∂timeMeasure T, DeGiorgi.HasWeakPartialDeriv i
      ((W (m + 1) (Fin.cons i β)).toFun t) ((W m β).toFun t) Ω) :
    ∀ N : ℕ, ∀ t₀ ∈ Icc (0 : ℝ) T,
      Tendsto (fun t => (iteratedWeakSobolevNorm N p
        (fun z => (W 0 (fun i => Fin.elim0 i)).toFun t z -
          (W 0 (fun i => Fin.elim0 i)).toFun t₀ z) Ω).toReal)
        (𝓝[Icc (0 : ℝ) T] t₀) (𝓝 0) := by
  intro N t₀ ht₀
  apply tendsto_wkpNorm_sub_of_finite_weak_partial_tree hΩ N
    (fun m β => (W m β).toFun) (fun m _ β => (W m β).continuousOn_toFun) ?_ ht₀
  intro m hm β i
  exact hasWeakPartialDeriv_of_continuousOn_Lp
    (closure_interior_Icc hT.ne).symm.subset i
    (W m β).toFun (W (m + 1) (Fin.cons i β)).toFun
    (W m β).continuousOn_toFun (W (m + 1) (Fin.cons i β)).continuousOn_toFun
    (hweak m β i)


end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
