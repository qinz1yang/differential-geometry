import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.Piece
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Cover

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem kochLammFluxPiece_int {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x c : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) {S : Set V}
    (hS : S ⊆ Metric.ball c R) :
    Integrable (fun z : ℝ × V ↦ kochLammFluxKernel (R ^ 2) w x z • f z)
      (kochLammTailMeasure (V := V) R S) := by
  let μ := kochLammTailMeasure (V := V) R S
  have hk : MemLp (kochLammFluxKernel (R ^ 2) w x)
      (ENNReal.ofReal (kochLammPDual V)) μ :=
    (kochLammFluxKernel_memLp (V := V) (t := R ^ 2) w x).mono_measure
      (kochLammTailTerm_le (V := V) R S)
  have hf : MemLp f (ENNReal.ofReal (kochLammPReal V)) μ := by
    simpa only [kochLammPReal_ofReal] using
      (kochLammFluxPiece_mem (V := V) h c hR hRT hS)
  let : ENNReal.HolderConjugate
      (ENNReal.ofReal (kochLammPDual V)) (ENNReal.ofReal (kochLammPReal V)) :=
    (kochLammPDual_holder (V := V)).ennrealOfReal
  exact memLp_one_iff_integrable.mp (hf.smul hk)

omit [CompleteSpace F] in
theorem kochLammFluxCover_est {T R k : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    (s : Finset V) {S : Set V} (hSm : MeasurableSet S)
    (hcover : S ⊆ ⋃ c ∈ s, Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    Integrable (fun z : ℝ × V ↦ kochLammFluxKernel (R ^ 2) w x z • f z)
        (kochLammTailMeasure (V := V) R S) ∧
      ‖kochLammFluxPiece1 R w f x S‖ ≤
        (s.card : ℝ) *
          (‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
            (kochLammFluxTailC V * (Aₚ : ℝ))) := by
  classical
  let D : ℝ :=
    ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
      (kochLammFluxTailC V * (Aₚ : ℝ))
  induction s using Finset.induction_on generalizing S with
  | empty =>
      have hS0 : S = ∅ := by
        simpa using hcover
      subst S
      constructor <;> simp [kochLammTailMeasure, kochLammFluxPiece1]
  | @insert c s hc ih =>
      let S₀ : Set V := S ∩ Metric.ball c R
      let S₁ : Set V := S \ Metric.ball c R
      have hS₀m : MeasurableSet S₀ :=
        hSm.inter Metric.isOpen_ball.measurableSet
      have hS₁m : MeasurableSet S₁ :=
        hSm.diff Metric.isOpen_ball.measurableSet
      have hdisj : Disjoint S₀ S₁ := by
        apply Set.disjoint_left.mpr
        intro y hy₀ hy₁
        have hy₀' : y ∈ S ∧ y ∈ Metric.ball c R := by
          simpa only [S₀, Set.mem_inter_iff] using hy₀
        have hy₁' : y ∈ S ∧ y ∉ Metric.ball c R := by
          simpa only [S₁, Set.mem_sdiff] using hy₁
        exact hy₁'.2 hy₀'.2
      have hsplit : S₀ ∪ S₁ = S := by
        ext y
        simp only [S₀, S₁, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
        tauto
      have hS₀ball : S₀ ⊆ Metric.ball c R := by
        intro y hy
        exact hy.2
      have hfar₀ : ∀ y ∈ S₀, k * R ≤ ‖x - y‖ := by
        intro y hy
        exact hfar y hy.1
      have hcover' : S ⊆
          Metric.ball c R ∪ ⋃ d ∈ s, Metric.ball d R := by
        simpa only [Finset.set_biUnion_insert] using hcover
      have hcover₁ : S₁ ⊆ ⋃ d ∈ s, Metric.ball d R := by
        intro y hy
        have hy' : y ∈ S ∧ y ∉ Metric.ball c R := by
          simpa only [S₁, Set.mem_sdiff] using hy
        exact (hcover' hy'.1).resolve_left hy'.2
      have hfar₁ : ∀ y ∈ S₁, k * R ≤ ‖x - y‖ := by
        intro y hy
        exact hfar y hy.1
      have hint₀ := kochLammFluxPiece_int (V := V) h w x c hR hRT hS₀ball
      obtain ⟨hint₁, hnorm₁⟩ := ih hS₁m hcover₁ hfar₁
      have hnorm₀ : ‖kochLammFluxPiece1 R w f x S₀‖ ≤ D := by
        simpa only [D] using
          (kochLammFluxPiece_norm (V := V) h w x c hR hk hRT
            hS₀m hS₀ball hfar₀)
      have hμ : kochLammTailMeasure (V := V) R S =
          kochLammTailMeasure (V := V) R S₀ + kochLammTailMeasure (V := V) R S₁ := by
        rw [← hsplit]
        exact kochLammTail_union (V := V) hdisj hS₁m
      have hint : Integrable
          (fun z : ℝ × V ↦ kochLammFluxKernel (R ^ 2) w x z • f z)
          (kochLammTailMeasure (V := V) R S) := by
        rw [hμ]
        exact hint₀.add_measure hint₁
      have hpiece : kochLammFluxPiece1 R w f x S =
          kochLammFluxPiece1 R w f x S₀ + kochLammFluxPiece1 R w f x S₁ := by
        unfold kochLammFluxPiece1
        rw [hμ, integral_add_measure hint₀ hint₁]
      refine ⟨hint, ?_⟩
      rw [hpiece]
      calc
        ‖kochLammFluxPiece1 R w f x S₀ + kochLammFluxPiece1 R w f x S₁‖ ≤
            ‖kochLammFluxPiece1 R w f x S₀‖ + ‖kochLammFluxPiece1 R w f x S₁‖ :=
          norm_add_le _ _
        _ ≤ D + (s.card : ℝ) * D := add_le_add hnorm₀ hnorm₁
        _ = ((insert c s).card : ℝ) * D := by
          rw [Finset.card_insert_of_notMem hc]
          norm_num
          ring

omit [CompleteSpace F] in
theorem kochLammFluxCover_norm {T R k : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    (s : Finset V) {S : Set V} (hSm : MeasurableSet S)
    (hcover : S ⊆ ⋃ c ∈ s, Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    ‖kochLammFluxPiece1 R w f x S‖ ≤
      (s.card : ℝ) *
        (‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
          (kochLammFluxTailC V * (Aₚ : ℝ))) :=
  (kochLammFluxCover_est (V := V) h w x hR hk hRT s hSm hcover hfar).2

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
