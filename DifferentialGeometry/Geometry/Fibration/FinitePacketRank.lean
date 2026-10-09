import DifferentialGeometry.Analysis.Calculus.CutoffAdjustment
import DifferentialGeometry.Analysis.Calculus.AdjustmentProjections
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

import DifferentialGeometry.Analysis.InnerProductSpace.PrunedGraphRank
import DifferentialGeometry.Analysis.InnerProductSpace.FiniteNormalReduction

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff Topology InnerProductSpace BigOperators

namespace DifferentialGeometry.Geometry.Fibration

variable {V E H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ E]

/-- The actual graph identity produces the lower margin of its actual differential. -/
theorem finite_packet_actual_graph_rank (Φ : E → H) (Q : H →L[ℝ] E)
    (hQ : ‖Q‖ ≤ 1) (hgraph : ∀ u, Q (Φ u) = u)
    (η : V → E) (f : V → H) (x : V)
    (hΦ : DifferentiableAt ℝ Φ (η x)) {a e b l : ℝ}
    (ha : 0 < a) (he : e < a)
    (hl : ∀ z, a * ‖z‖ ≤ ‖(fderiv ℝ η x).adjoint z‖)
    (hT : ‖fderiv ℝ Φ (η x)‖ ≤ b) (hL : ‖fderiv ℝ η x‖ ≤ l)
    (herror : ‖fderiv ℝ f x - (fderiv ℝ Φ (η x)).comp (fderiv ℝ η x)‖ ≤ e) :
    let T := fderiv ℝ Φ (η x)
    let P := T.range.orthogonalProjectionOnto.comp (fderiv ℝ f x)
    Function.Surjective P ∧ ‖fderiv ℝ f x - T.range.subtypeL.comp P‖ ≤ e ∧
      ∀ v ∈ P.kerᗮ, (a - e) * ‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ (b * l + e) * ‖v‖ := by
  have hQT : Q.comp (fderiv ℝ Φ (η x)) = ContinuousLinearMap.id ℝ E := by
    have hh : (Q ∘ Φ) = id := funext hgraph
    have hd := fderiv_comp (η x) Q.differentiableAt hΦ
    rw [hh, fderiv_id, ContinuousLinearMap.fderiv] at hd
    exact hd.symm
  have hlower (z : E) : ‖z‖ ≤ ‖fderiv ℝ Φ (η x) z‖ := by
    have hz := congrArg (fun A : E →L[ℝ] E => A z) hQT
    calc
      ‖z‖ = ‖Q (fderiv ℝ Φ (η x) z)‖ := congrArg norm hz.symm
      _ ≤ ‖Q‖ * ‖fderiv ℝ Φ (η x) z‖ := Q.le_opNorm _
      _ ≤ ‖fderiv ℝ Φ (η x) z‖ := mul_le_of_le_one_left (norm_nonneg _) hQ
  exact ContinuousLinearMap.projected_range_surjective_of_approximation _ _ _ ha he hl
    hlower hT hL herror

/-- Actual pruning identities are differentiated; derivative commutation is not assumed. -/
theorem finite_packet_actual_pruned_rank (Φ : E → H) (K : H →L[ℝ] H)
    (Q : H →L[ℝ] E) (hK : ‖K‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hgraph : ∀ u, Q (K (Φ u)) = u)
    (η : V → E) (f : V → H) (x : V) (hf : DifferentiableAt ℝ f x)
    (hfixed : ∀ y, K (f y) = f y) (hΦ : DifferentiableAt ℝ Φ (η x))
    {a e b l : ℝ} (ha : 0 < a) (he : e < a)
    (hl : ∀ z, a * ‖z‖ ≤ ‖(fderiv ℝ η x).adjoint z‖)
    (hT : ‖fderiv ℝ Φ (η x)‖ ≤ b) (hL : ‖fderiv ℝ η x‖ ≤ l)
    (herror : ‖fderiv ℝ f x - (fderiv ℝ Φ (η x)).comp (fderiv ℝ η x)‖ ≤ e) :
    let T := K.comp (fderiv ℝ Φ (η x))
    let P := T.range.orthogonalProjectionOnto.comp (fderiv ℝ f x)
    Function.Surjective P ∧ ‖fderiv ℝ f x - T.range.subtypeL.comp P‖ ≤ e ∧
      ∀ v ∈ P.kerᗮ, (a - e) * ‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ (b * l + e) * ‖v‖ := by
  have hQT : Q.comp (K.comp (fderiv ℝ Φ (η x))) = ContinuousLinearMap.id ℝ E := by
    have hd := ((Q.hasFDerivAt.comp (η x) (K.hasFDerivAt.comp (η x) hΦ.hasFDerivAt)))
    have hh : (fun u => Q (K (Φ u))) = id := funext hgraph
    change HasFDerivAt (fun u => Q (K (Φ u)))
      (Q.comp (K.comp (fderiv ℝ Φ (η x)))) (η x) at hd
    rw [hh] at hd
    exact hd.unique (hasFDerivAt_id (η x))
  have hKD : K.comp (fderiv ℝ f x) = fderiv ℝ f x := by
    have hd := K.hasFDerivAt.comp x hf.hasFDerivAt
    have hh : (K ∘ f) = f := funext hfixed
    rw [hh] at hd
    exact hd.unique hf.hasFDerivAt
  exact ContinuousLinearMap.pruned_graph_range_surjective_of_approximation _ _ _ _ _
    hK hQ hQT hKD ha he hl hT hL herror

/-- Actual positive weights are normalized before the finite normal reduction. -/
theorem finite_packet_normalized_normal_reduction [FiniteDimensional ℝ H]
    {A : Type*} (S : Finset A) (hS : S.Nonempty) (L : A → Submodule ℝ H)
    (x : A → H) (w : A → ℝ) (hw : ∀ i ∈ S, 0 < w i)
    {k : ℕ} (hdim : ∀ i ∈ S, Module.finrank ℝ (L i) ≤ k) (z : H) :
    let weights := fun i => w i / ∑ j ∈ S, w j
    let V := S.sup (fun i => ℝ ∙ x i ⊔ L i)
    let O : H →L[ℝ] H := ∑ i ∈ S, weights i • (L i)ᗮ.starProjection
    let Q := (⨆ a ∈ Ici (1 / 2 : ℝ), Module.End.eigenspace O.toLinearMap a).starProjection
    Module.finrank ℝ V ≤ S.card * (k + 1) ∧
      Module.finrank ℝ (ContinuousLinearMap.id ℝ H - O).range ≤ S.card * k ∧
      Set.MapsTo O V V ∧ (∀ v ∈ Vᗮ, O v = v) ∧ (∀ v ∈ Vᗮ, Q v = v) ∧
      Vᗮ.starProjection (∑ i ∈ S, weights i • Q (z - x i)) = Vᗮ.starProjection z := by
  classical
  have hsum : 0 < ∑ j ∈ S, w j := Finset.sum_pos (fun j hj => hw j hj) hS
  have hnorm : ∑ i ∈ S, w i / ∑ j ∈ S, w j = 1 := by
    rw [← Finset.sum_div, div_self hsum.ne']
  exact Submodule.finite_affine_family_normal_reduction S L x
    (fun i => w i / ∑ j ∈ S, w j) hnorm hdim (Ici (1 / 2 : ℝ)) (by norm_num) z

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] in
/-- The literal adjustment retains its complementary projection and only enlarges fibres. -/
theorem finite_packet_adjustment_ledger {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (K : H →L[ℝ] Z) (J : E →L[ℝ] H) (hKJ : K.comp J = 0)
    (ψ : H → ℝ) (v : H → E) (f : V → H) {x : V}
    (hf : DifferentiableAt ℝ f x) (hψ : DifferentiableAt ℝ ψ (f x))
    (hv : DifferentiableAt ℝ v (f x)) :
    let Ψ := fun y => y + ψ y • J (v y)
    K ∘ Ψ = K ∧
      (∀ p q, f p = f q → (Ψ ∘ f) p = (Ψ ∘ f) q) ∧
      (fderiv ℝ f x).ker ≤ (fderiv ℝ (Ψ ∘ f) x).ker := by
  dsimp only
  refine ⟨DifferentialGeometry.Analysis.retained_projection_cutoff_adjustment K J hKJ ψ v,
    ?_, ?_⟩
  · intro p q hpq
    exact congrArg (fun y => y + ψ y • J (v y)) hpq
  · apply DifferentialGeometry.Analysis.ker_fderiv_le_ker_postcomp hf
    exact differentiableAt_id.add (hψ.smul (J.differentiableAt.comp (f x) hv))

end DifferentialGeometry.Geometry.Fibration

namespace DifferentialGeometry.Geometry.Fibration

open DifferentialGeometry.Analysis

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem finite_packet_orthogonal_cutoff_adjustment_value_derivative_le
    (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    {f : E → H} {ψ : H → ℝ} {P : Q → Q} {x : E} (A : Q →L[ℝ] Q)
    (hf : DifferentiableAt ℝ f x) (hψ : DifferentiableAt ℝ ψ (f x))
    (hP : DifferentiableAt ℝ P (Q.orthogonalProjectionOnto (f x))) {a b L d e ρ : ℝ}
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hd : 0 ≤ d) (hρ : 0 < ρ)
    (hcutoff : 0 ≤ ψ (f x) ∧ ψ (f x) ≤ 1)
    (hvalue : ‖P (Q.orthogonalProjectionOnto (f x)) - Q.orthogonalProjectionOnto (f x)‖ ≤ a * ρ)
    (hcutoffDeriv : ‖fderiv ℝ ψ (f x)‖ ≤ b / ρ) (hfirst : ‖fderiv ℝ f x‖ ≤ L)
    (hcomparison : ‖fderiv ℝ P (Q.orthogonalProjectionOnto (f x)) - A‖ ≤ d)
    (hnormal : ‖(ContinuousLinearMap.id ℝ Q - A).comp
      (Q.orthogonalProjectionOnto.comp (fderiv ℝ f x))‖ ≤ e) :
    let g : E → H := fun y => f y + ψ (f y) • Q.subtypeL
      (P (Q.orthogonalProjectionOnto (f y)) - Q.orthogonalProjectionOnto (f y))
    ‖g x - f x‖ ≤ a * ρ ∧ ‖fderiv ℝ g x - fderiv ℝ f x‖ ≤ a * b * L + d * L + e := by
  exact projected_cutoff_adjustment_value_derivative_le Q.orthogonalProjectionOnto Q.subtypeL A
    Q.orthogonalProjectionOnto_norm_le Q.norm_subtypeL_le hf hψ hP hb hL hd hρ
    hcutoff hvalue hcutoffDeriv hfirst hcomparison hnormal

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace H] in
theorem finite_packet_orthogonal_cutoff_retains_complement
    (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    (ψ : H → ℝ) (v : H → Q) :
    (fun x => Qᗮ.starProjection (x + ψ x • Q.subtypeL (v x))) = Qᗮ.starProjection := by
  apply retained_projection_cutoff_adjustment
  ext x
  exact Q.starProjection_orthogonal_apply_eq_zero x.property

omit [CompleteSpace H] in
theorem finite_packet_cutoff_postcomposition_fiber_kernel_inclusions {f : E → H} {Ψ : H → H} {x : E}
    (hf : DifferentiableAt ℝ f x) (hΨ : DifferentiableAt ℝ Ψ (f x)) :
    (∀ p q, f p = f q → (Ψ ∘ f) p = (Ψ ∘ f) q) ∧
      (fderiv ℝ f x).ker ≤ (fderiv ℝ (Ψ ∘ f) x).ker := by
  exact ⟨fun _ _ h => congrArg Ψ h, ker_fderiv_le_ker_postcomp hf hΨ⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace H] in
theorem finite_packet_nested_orthogonal_cutoff_factor (Q₂ Q₃ : Submodule ℝ H)
    [Q₂.HasOrthogonalProjection] [Q₃.HasOrthogonalProjection] (hle : Q₃ ≤ Q₂)
    (φ : H → ℝ) (P : H → H) :
    (fun x => Q₂.starProjection (x + φ (Q₂.starProjection x) •
      Q₃.starProjection (P (Q₃.starProjection x) - Q₃.starProjection x))) =
      (fun y => y + φ y • (Q₂.starProjection.comp Q₃.starProjection)
        (P (Q₃.starProjection y) - Q₃.starProjection y)) ∘ Q₂.starProjection := by
  exact factor_projection_cutoff_adjustment Q₂.starProjection Q₃.starProjection
    Q₃.starProjection Q₃.starProjection
    (Submodule.starProjection_comp_starProjection_of_le hle).symm
    (φ ∘ Q₂.starProjection) φ rfl P

end DifferentialGeometry.Geometry.Fibration
