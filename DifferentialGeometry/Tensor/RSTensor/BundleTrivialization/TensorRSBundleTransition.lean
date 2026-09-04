import DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.TensorRSBundleLocalityIdentities
import DifferentialGeometry.Tensor.RSTensor.Norm.Operator
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Hom

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry.Tensor

open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tensorRS_trivializationAt_continuousLinearMapAt_eq_continuousLinearEquiv_on_locality
    (r s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source) :
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b :
        TensorRSSpace r s I b →L[ℝ] TensorRSModel r s ℝ E) =
      (tensorRSSpaceContinuousLinearEquiv (𝕜 := ℝ) (M := M) (I := I) r s
        b).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro T
  apply ContinuousLinearMap.ext
  intro D_α
  have h_subB := tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
    (I := I) (M := M) (r := r) (s := s) (b₀ := b₀) (b := b)
    (h_chart := h_chart) (h_src := h_src) (T := T) (D_α := D_α)
  change (((trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b T)
        D_α : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (tensorRSSpaceContinuousLinearEquiv (𝕜 := ℝ) (M := M) (I := I) r s b T) D_α
  rw [h_subB]
  rfl

theorem tensorRS_trivializationAt_continuousLinearMapAt_norm_eq_on_locality
    (r s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source)
    (T : TensorRSSpace r s I b) :
    ‖((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b T :
        TensorRSModel r s ℝ E)‖ = ‖T‖ := by
  rw [tensorRS_trivializationAt_continuousLinearMapAt_eq_continuousLinearEquiv_on_locality
    (I := I) (M := M) r s b₀ h_chart h_src]
  exact tensorRSSpace_continuousLinearEquiv_norm_apply (𝕜 := ℝ) (I := I) (M := M) r s b T

theorem tensorRS_trivializationAt_continuousLinearMapAt_norm_le_coordChangeL_norm_on_locality
    (r s : ℕ) (α : M) {b₀ b : M}
    (hb_α : b ∈ (chartAt H α).source)
    (hb_b₀ : b ∈ (chartAt H b₀).source)
    (h_chart : chartAt H b = chartAt H b₀)
    (T : TensorRSSpace r s I b) :
    ‖((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b T :
        TensorRSModel r s ℝ E)‖ ≤
      ‖((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).coordChangeL ℝ
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) b :
            TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)‖ * ‖T‖ := by
  have hb_tan_α : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
    exact hb_α
  have hb_tan_b₀ : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]
    exact hb_b₀
  have hb_α' : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := ⟨hb_tan_α, hb_tan_α⟩
  have hb_b₀' : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) b₀).baseSet := ⟨hb_tan_b₀, hb_tan_b₀⟩
  have h_eq :
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b T :
          TensorRSModel r s ℝ E) =
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) b₀).coordChangeL ℝ
          (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α) b :
              TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b T) := by
    set eα := trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α with heα
    set eb₀ := trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) b₀ with heb₀
    have h_cc :
        (eb₀.coordChangeL ℝ eα b : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
          (eb₀.continuousLinearMapAt ℝ b T) =
        eα.continuousLinearMapAt ℝ b
          (eb₀.symmL ℝ b (eb₀.continuousLinearMapAt ℝ b T)) := by
      change (eb₀.coordChangeL ℝ eα b) (eb₀.continuousLinearMapAt ℝ b T) = _
      rw [Trivialization.coordChangeL_apply _ _ ⟨hb_b₀', hb_α'⟩]
      rw [eb₀.symmL_apply hb_b₀' (eb₀.continuousLinearMapAt ℝ b T)]
      simp only [Bundle.Trivialization.continuousLinearMapAt_apply,
          Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_α',
          Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_b₀']
    have h_inv : eb₀.symmL ℝ b (eb₀.continuousLinearMapAt ℝ b T) = T :=
      Trivialization.symmL_continuousLinearMapAt (R := ℝ) eb₀ hb_b₀' T
    rw [h_cc, h_inv]
  have h_norm_T :
      ‖((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b T :
          TensorRSModel r s ℝ E)‖ = ‖T‖ :=
    tensorRS_trivializationAt_continuousLinearMapAt_norm_eq_on_locality
      (I := I) (M := M) r s b₀ h_chart hb_b₀ T
  rw [h_eq]
  have h_le_op := ContinuousLinearMap.le_opNorm
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).coordChangeL ℝ
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α) b :
          TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b T)
  rw [h_norm_T] at h_le_op
  exact h_le_op

theorem tensorRS_trivializationAt_symmL_norm_eq_coordChangeL_norm_on_locality
    (r s : ℕ) (α : M) {b₀ b : M}
    (hb_α : b ∈ (chartAt H α).source)
    (hb_b₀ : b ∈ (chartAt H b₀).source)
    (h_chart : chartAt H b = chartAt H b₀)
    (D : TensorRSModel r s ℝ E) :
    ‖((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b D :
        TensorRSSpace r s I b)‖ =
      ‖((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).coordChangeL ℝ
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀) b :
            TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) D‖ := by
  have hb_tan_α : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
    exact hb_α
  have hb_tan_b₀ : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]
    exact hb_b₀
  have hb_α' : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := ⟨hb_tan_α, hb_tan_α⟩
  have hb_b₀' : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) b₀).baseSet := ⟨hb_tan_b₀, hb_tan_b₀⟩
  have h_apply :
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).coordChangeL ℝ
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀) b :
            TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) D =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b D) := by
    change ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).coordChangeL ℝ
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀) b) D =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b D)
    rw [Trivialization.coordChangeL_apply _ _ ⟨hb_α', hb_b₀'⟩]
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_b₀',
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL_apply hb_α' D]
  have h_locality_clm :=
    tensorRS_trivializationAt_continuousLinearMapAt_eq_continuousLinearEquiv_on_locality
      (I := I) (M := M) r s b₀ h_chart hb_b₀
  have h_appl :
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b
          ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b D) =
        (tensorRSSpaceContinuousLinearEquiv (𝕜 := ℝ) (M := M) (I := I) r s b)
          ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b D) := by
    have := congrArg (fun (f : TensorRSSpace r s I b →L[ℝ] TensorRSModel r s ℝ E) =>
        f ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b D)) h_locality_clm
    simpa using this
  have h_norm_eq :
      ‖((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b D :
          TensorRSSpace r s I b)‖ =
        ‖tensorRSSpaceContinuousLinearEquiv (𝕜 := ℝ) (M := M) (I := I) r s b
          ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b D)‖ :=
    (tensorRSSpace_continuousLinearEquiv_norm_apply (𝕜 := ℝ) (I := I) (M := M)
      r s b _).symm
  rw [h_norm_eq, h_apply, h_appl]

theorem tensorRS_coordChangeL_continuousOn (r s : ℕ) (α β : M) :
    ContinuousOn
      (fun b : M => ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).coordChangeL ℝ
          (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) β) b :
              TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
  have h_smooth :
      ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) ∞
        (fun b : M => ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).coordChangeL ℝ
            (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) β) b :
                TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E))
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet ∩
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) β).baseSet) :=
    contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I)
      (F := TensorRSModel r s ℝ E)
      (E := fun y : M => TensorRSSpace r s I y)
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α)
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) β)
  have h_base_α : (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet =
      (chartAt H α).source := by
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [inter_self, TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
  have h_base_β : (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) β).baseSet =
      (chartAt H β).source := by
    change (trivializationAt E (TangentSpace I) β).baseSet ∩
        (trivializationAt E (TangentSpace I) β).baseSet = (chartAt H β).source
    rw [inter_self, TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) β]
  rw [h_base_α, h_base_β] at h_smooth
  exact h_smooth.continuousOn

theorem tensorRS_coordChangeL_continuousAt
    (r s : ℕ) (α β x : M)
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source) :
    ContinuousAt
      (fun b => ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).coordChangeL ℝ
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) β) b :
        TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) x :=
  (tensorRS_coordChangeL_continuousOn (I := I) (M := M) r s α β).continuousAt
    (((chartAt H α).open_source.inter (chartAt H β).open_source).mem_nhds ⟨hxα, hxβ⟩)

end DifferentialGeometry.Tensor

end
