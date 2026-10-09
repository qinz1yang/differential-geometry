import DifferentialGeometry.Geometry.Fibration.FinitePacketSupport
import DifferentialGeometry.Geometry.Fibration.FinitePacketCalculus
import DifferentialGeometry.Geometry.Fibration.FinitePacketRank
import DifferentialGeometry.Geometry.Fibration.FinitePacketCoverage
import DifferentialGeometry.Geometry.Fibration.FinitePacketParameters

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Fibration

/-- A strict error budget for the actual fixed joint profiles on the SAME source set. -/
theorem finite_joint_packet_strict_error {E V ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    {Δ : ℝ} (hΔ : 1 ≤ Δ) (s : ι → ℝ) (hs : ∀ j, s j ∈ Icc (1 / 2) 2)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) (hu : ∀ j, ‖u j‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (U V₀ : V → E) (D : Set V) {ε L τ : ℝ} (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hU : ∀ x ∈ D, DifferentiableAt ℝ U x)
    (hV : ∀ x ∈ D, DifferentiableAt ℝ V₀ x)
    (hclose : ∀ x ∈ D, ‖U x - V₀ x‖ ≤ ε)
    (hDclose : ∀ x ∈ D, ‖fderiv ℝ U x - fderiv ℝ V₀ x‖ ≤ ε)
    (hDV : ∀ x ∈ D, ‖fderiv ℝ V₀ x‖ ≤ L)
    (hbudget : let N : ℝ := (Fintype.card ι : ℝ) + 1
      let K := 10 * N ^ 2 * DifferentialGeometry.Analysis.edgeProfileDerivativeBound ^ 3
      (Real.sqrt N * (2 + 20 * K) + (24 * Real.sqrt N * K / Δ) * L) * ε < τ) :
    let W := DifferentialGeometry.Analysis.fixedJointCutoffNetwork Δ s u v
    ∀ x ∈ D, ‖W (U x) - W (V₀ x)‖ < τ ∧
      ‖fderiv ℝ (W ∘ U) x - fderiv ℝ (W ∘ V₀) x‖ < τ := by
  have h := (finite_joint_packet_c1_on hΔ s hs u v hu hv U V₀ D hε hL hU hV
    hclose hDclose hDV).2
  dsimp only
  intro x hx
  have hb := (h x hx).trans_lt hbudget
  exact ⟨(le_max_left _ _).trans_lt hb, (le_max_right _ _).trans_lt hb⟩

/-- All upper-bound nodes have actual positive predecessor-dependent choices. -/
theorem exists_dependent_small_packet_parameters {ι κ : Type*} [Finite ι]
    {r : ι → ι → Prop} (hacyclic : ∀ i, ¬ Relation.TransGen r i i)
    (upper : ι → Finset κ) (bound : ∀ i, (∀ j, r j i → ℝ) → κ → ℝ)
    (hbound : ∀ i v j, j ∈ upper i → 0 < bound i v j) :
    ∃ f : ι → ℝ, ∀ i, 0 < f i ∧ ∀ j ∈ upper i, f i < bound i (fun j _ => f j) j := by
  obtain ⟨f, hf⟩ := finite_packet_parameters hacyclic (fun _ => 0) upper (fun _ => ∅)
    bound (fun _ _ => 0) (fun _ _ => 1) (fun i _ v j hj => hbound i v j hj)
    (by intro i hi; simp at hi)
  exact ⟨f, fun i => (hf i).1 rfl⟩

end DifferentialGeometry.Geometry.Fibration
noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace
namespace DifferentialGeometry.Geometry.Fibration
/-- SAME actual graph supplies rank and the original-image closed-ball coverage. -/
theorem finite_packet_cloud_and_rank {V E H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (F : V → H) (η : V → E) (D : Set V) (Φ : E → H) (Q : H →L[ℝ] E)
    (hQ : ‖Q‖ ≤ 1) (hgraph : ∀ u, Q (Φ u) = u) (p : V) (hp : p ∈ D)
    {σ Γ r B e a b l : ℝ} (hσ : 0 < σ) (hΓ : 0 < Γ) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hrlow : σ / 2 ≤ r) (hrhigh : r ≤ 2 * σ)
    (hebudget : e ≤ Γ * σ / 24) (hcurv : B * σ ≤ Γ ^ 3 / 6)
    (hreg : ∀ u ∈ closedBall (Q (F p)) (r / Γ), ContDiffAt ℝ 2 Φ u)
    (hsecond : ∀ u ∈ closedBall (Q (F p)) (r / Γ), ‖iteratedFDeriv ℝ 2 Φ u‖ ≤ B)
    (hcoord : ∀ q ∈ D, Q (F q) = η q)
    (happrox : ∀ q ∈ D, dist (F q) (Φ (η q)) ≤ e)
    (hcover : ∀ u ∈ closedBall (Q (F p)) (r / Γ), ∃ q ∈ D, η q = u)
    (ha : 0 < a) (hea : e < a) (hl : ∀ z, a * ‖z‖ ≤ ‖(fderiv ℝ η p).adjoint z‖)
    (hT : ‖fderiv ℝ Φ (η p)‖ ≤ b) (hL : ‖fderiv ℝ η p‖ ≤ l)
    (herror : ‖fderiv ℝ F p - (fderiv ℝ Φ (η p)).comp (fderiv ℝ η p)‖ ≤ e) :
    let T := fderiv ℝ Φ (η p)
    let P := T.range.orthogonalProjectionOnto.comp (fderiv ℝ F p)
    Function.Surjective P ∧ ‖fderiv ℝ F p - T.range.subtypeL.comp P‖ ≤ e ∧
      hausdorffDist (F '' D ∩ closedBall (F p) (r / Γ))
        ((fun v => F p + fderiv ℝ Φ (Q (F p)) v) '' (univ : Set E) ∩
          closedBall (F p) (r / Γ)) ≤ Γ * r := by
  have hΦ : DifferentiableAt ℝ Φ (η p) := by
    have hr : 0 < r := by linarith
    have hh := hreg (Q (F p)) (mem_closedBall_self (div_pos hr hΓ).le)
    rw [hcoord p hp] at hh
    exact hh.differentiableAt (by norm_num)
  have hrank := finite_packet_actual_graph_rank Φ Q hQ hgraph η F p hΦ ha hea hl hT hL herror
  refine ⟨hrank.1, hrank.2.1, ?_⟩
  exact finite_packet_original_image_coverage F η D Φ Q
    (fun z => (Q.le_opNorm z).trans (mul_le_of_le_one_left (norm_nonneg _) hQ))
    hgraph p hp hσ hΓ hB he hrlow hrhigh hebudget hcurv hreg hsecond hcoord happrox hcover

end DifferentialGeometry.Geometry.Fibration
