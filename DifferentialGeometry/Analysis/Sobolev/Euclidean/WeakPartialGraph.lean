import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness
import DifferentialGeometry.Analysis.Integration.Lp.Product
import Mathlib.Analysis.LocallyConvex.WeakSpace
import DifferentialGeometry.Analysis.InnerProductSpace.WeakCompactness
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z} {Ω : Set (EuclideanSpace ℝ (Fin d))}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "X" => Lp ℝ p (μ.prod (volume.restrict Ω))

theorem ae_hasWeakPartialDeriv_of_tendsto_Lp
    (hp : p ≠ ⊤) (k : Fin d)
    {U V : ℕ → X} {u v : X}
    (hU : Tendsto U atTop (𝓝 u)) (hV : Tendsto V atTop (𝓝 v))
    (hweak : ∀ n, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => V n (t, x)) (fun x => U n (t, x)) Ω) :
    ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => v (t, x)) (fun x => u (t, x)) Ω := by
  obtain ⟨σ, hσ, hσU⟩ := Lp.exists_subseq_tendsto_eLpNorm_prodMk_left hp hU
  obtain ⟨τ, hτ, hτV⟩ := Lp.exists_subseq_tendsto_eLpNorm_prodMk_left hp
    (hV.comp hσ.tendsto_atTop)
  have hUi := ae_all_iff.mpr (fun n => (Lp.memLp (U n)).prodMk_left hp)
  have hVi := ae_all_iff.mpr (fun n => (Lp.memLp (V n)).prodMk_left hp)
  have hwi := ae_all_iff.mpr hweak
  filter_upwards [hσU, hτV, hUi, hVi, hwi,
    (Lp.memLp u).prodMk_left hp, (Lp.memLp v).prodMk_left hp]
    with t htU htV htUi htVi htweak htu htv
  exact hasWeakPartialDeriv_of_tendsto_eLpNorm (Fact.out : 1 ≤ p) k
    (fun n => htUi (σ (τ n))) (fun n => htVi (σ (τ n))) htu htv
    (fun n => htweak (σ (τ n))) (htU.comp hτ.tendsto_atTop) htV

theorem isClosed_setOf_ae_hasWeakPartialDeriv
    (hp : p ≠ ⊤) (k : Fin d) :
    IsClosed {w : X × X | ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => w.2 (t, x)) (fun x => w.1 (t, x)) Ω} := by
  apply isSeqClosed_iff_isClosed.mp
  intro w v hw hlim
  exact ae_hasWeakPartialDeriv_of_tendsto_Lp hp k
    ((continuous_fst.tendsto v).comp hlim) ((continuous_snd.tendsto v).comp hlim) hw

end DifferentialGeometry.Analysis.Sobolev.Euclidean


namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z} {Ω : Set (EuclideanSpace ℝ (Fin d))}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "X" => Lp ℝ p (μ.prod (volume.restrict Ω))

omit [Fact (1 ≤ p)] in
private theorem coeFn_smul_add (a b : ℝ) (u v : X) :
    (a • u + b • v : X) =ᵐ[μ.prod (volume.restrict Ω)]
      fun z => a * u z + b * v z := by
  filter_upwards [Lp.coeFn_add (a • u) (b • v), Lp.coeFn_smul a u, Lp.coeFn_smul b v]
    with z hz ha hb
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hz ha hb
  rw [hz, ha, hb]

private theorem integral_linear_combination_mul
    {f g : E → ℝ}
    (hf : MemLp f p (volume.restrict Ω)) (hg : MemLp g p (volume.restrict Ω))
    {φ : E → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (a b : ℝ) :
    (∫ x in Ω, (a * f x + b * g x) * φ x) =
      a * (∫ x in Ω, f x * φ x) + b * (∫ x in Ω, g x * φ x) := by
  have hfφ : Integrable (fun x => f x * φ x) (volume.restrict Ω) :=
    (hf.locallyIntegrable (Fact.out : 1 ≤ p)).integrable_smul_right_of_hasCompactSupport hφ hφc
  have hgφ : Integrable (fun x => g x * φ x) (volume.restrict Ω) :=
    (hg.locallyIntegrable (Fact.out : 1 ≤ p)).integrable_smul_right_of_hasCompactSupport hφ hφc
  simp_rw [add_mul, mul_assoc]
  rw [integral_add (hfφ.const_mul a) (hgφ.const_mul b), integral_const_mul, integral_const_mul]

theorem convex_setOf_ae_hasWeakPartialDeriv
    (hp : p ≠ ⊤) (k : Fin d) :
    Convex ℝ {w : X × X | ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => w.2 (t, x)) (fun x => w.1 (t, x)) Ω} := by
  intro A hA B hB a b _ _ _
  have hleft := Measure.ae_ae_of_ae_prod (coeFn_smul_add a b A.1 B.1)
  have hright := Measure.ae_ae_of_ae_prod (coeFn_smul_add a b A.2 B.2)
  filter_upwards [hA, hB, hleft, hright,
    (Lp.memLp A.1).prodMk_left hp, (Lp.memLp A.2).prodMk_left hp,
    (Lp.memLp B.1).prodMk_left hp, (Lp.memLp B.2).prodMk_left hp]
    with t htA htB htleft htright hA₁ hA₂ hB₁ hB₂
  intro φ hφ hφc hφs
  have hdφ : Continuous (fun x : E => fderiv ℝ φ x (EuclideanSpace.single k 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφc := hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k 1)
  change (∫ x in Ω, (a • A.1 + b • B.1 : X) (t, x) *
    fderiv ℝ φ x (EuclideanSpace.single k 1)) =
      -∫ x in Ω, (a • A.2 + b • B.2 : X) (t, x) * φ x
  calc
    _ = ∫ x in Ω, (a * A.1 (t, x) + b * B.1 (t, x)) *
        fderiv ℝ φ x (EuclideanSpace.single k 1) := by
      apply integral_congr_ae
      filter_upwards [htleft] with x hx
      rw [hx]
    _ = a * (∫ x in Ω, A.1 (t, x) * fderiv ℝ φ x (EuclideanSpace.single k 1)) +
        b * (∫ x in Ω, B.1 (t, x) * fderiv ℝ φ x (EuclideanSpace.single k 1)) :=
      integral_linear_combination_mul hA₁ hB₁ hdφ hdφc a b
    _ = -(a * (∫ x in Ω, A.2 (t, x) * φ x) + b * (∫ x in Ω, B.2 (t, x) * φ x)) := by
      rw [htA φ hφ hφc hφs, htB φ hφ hφc hφs]
      ring
    _ = -(∫ x in Ω, (a * A.2 (t, x) + b * B.2 (t, x)) * φ x) := by
      rw [integral_linear_combination_mul hA₂ hB₂ hφ.continuous hφc a b]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [htright] with x hx
      rw [hx]

theorem isClosed_toWeakSpace_setOf_ae_hasWeakPartialDeriv
    (hp : p ≠ ⊤) (k : Fin d) :
    IsClosed ((toWeakSpace ℝ (X × X)) ''
      {w : X × X | ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
        (fun x => w.2 (t, x)) (fun x => w.1 (t, x)) Ω}) := by
  rw [← closure_eq_iff_isClosed]
  rw [← (convex_setOf_ae_hasWeakPartialDeriv hp k).toWeakSpace_closure ℝ,
    (isClosed_setOf_ae_hasWeakPartialDeriv hp k).closure_eq]

theorem ae_hasWeakPartialDeriv_of_tendsto_weak
    (hp : p ≠ ⊤) (k : Fin d)
    {A : Type*} {l : Filter A} [NeBot l]
    {U V : A → X} {u v : X}
    (hlim : Tendsto (fun a => toWeakSpace ℝ (X × X) (U a, V a)) l
      (𝓝 (toWeakSpace ℝ (X × X) (u, v))))
    (hweak : ∀ᶠ a in l, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => V a (t, x)) (fun x => U a (t, x)) Ω) :
    ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => v (t, x)) (fun x => u (t, x)) Ω := by
  have hmem := (isClosed_toWeakSpace_setOf_ae_hasWeakPartialDeriv hp k).mem_of_tendsto hlim
    (hweak.mono fun a ha => ⟨(U a, V a), ha, rfl⟩)
  obtain ⟨w, hw, heq⟩ := hmem
  have hEq : w = (u, v) := (toWeakSpace ℝ (X × X)).injective heq
  subst w
  exact hw

end DifferentialGeometry.Analysis.Sobolev.Euclidean


namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z} {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "X" => Lp ℝ 2 (μ.prod (volume.restrict Ω))

private theorem tendsto_weak_prod_of_tendsto_inner
    {A : Type*} {l : Filter A} {U V : A → X} {u v : X}
    (hU : Tendsto U l (𝓝 u))
    (hV : ∀ z, Tendsto (fun a => inner ℝ (V a) z) l (𝓝 (inner ℝ v z))) :
    Tendsto (fun a => toWeakSpace ℝ (X × X) (U a, V a)) l
      (𝓝 (toWeakSpace ℝ (X × X) (u, v))) := by
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto _
    (separatingDual_iff_injective.mp (inferInstance : SeparatingDual ℝ (X × X)))).mpr
  intro F
  change Tendsto (fun a => F (U a, V a)) l (𝓝 (F (u, v)))
  let F₁ : X →L[ℝ] ℝ := F.comp (ContinuousLinearMap.inl ℝ X X)
  let F₂ : X →L[ℝ] ℝ := F.comp (ContinuousLinearMap.inr ℝ X X)
  have hF₂ (w : X) : F₂ w = inner ℝ w ((_root_.InnerProductSpace.toDual ℝ X).symm F₂) := by
    rw [real_inner_comm, _root_.InnerProductSpace.toDual_symm_apply]
  have h₂ : Tendsto (fun a => F₂ (V a)) l (𝓝 (F₂ v)) := by
    simpa only [hF₂] using hV ((_root_.InnerProductSpace.toDual ℝ X).symm F₂)
  have hsplit (x y : X) : F (x, y) = F₁ x + F₂ y := by
    change F (x, y) = F (x, 0) + F (0, y)
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  simpa only [hsplit, Function.comp_apply] using ((F₁.continuous.tendsto u).comp hU).add h₂

theorem exists_ae_hasWeakPartialDeriv_of_norm_bounded
    [TopologicalSpace.SeparableSpace X]
    (k : Fin d) {U V : ℕ → X} {u : X} {C : ℝ}
    (hU : Tendsto U atTop (𝓝 u)) (hV : ∀ n, ‖V n‖ ≤ C)
    (hweak : ∀ n, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => V n (t, x)) (fun x => U n (t, x)) Ω) :
    ∃ v : X, ‖v‖ ≤ C ∧ ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => v (t, x)) (fun x => u (t, x)) Ω := by
  obtain ⟨σ, v, hσ, hlim⟩ :=
    DifferentialGeometry.Analysis.InnerProductSpace.exists_weakly_convergent_subsequence_of_norm_bounded V hV
  have hC : 0 ≤ C := (norm_nonneg (V 0)).trans (hV 0)
  have hvC : ‖v‖ ≤ C := by
    have hvv : inner ℝ v v ≤ C * ‖v‖ := le_of_tendsto (hlim v) (Eventually.of_forall fun n =>
      (real_inner_le_norm (V (σ n)) v).trans (mul_le_mul_of_nonneg_right (hV (σ n)) (norm_nonneg v)))
    rw [real_inner_self_eq_norm_sq] at hvv
    nlinarith [norm_nonneg v]
  refine ⟨v, hvC, ?_⟩
  apply ae_hasWeakPartialDeriv_of_tendsto_weak (by norm_num) k
    (tendsto_weak_prod_of_tendsto_inner (hU.comp hσ.tendsto_atTop) hlim)
  exact Eventually.of_forall fun n => hweak (σ n)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
