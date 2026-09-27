import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.Control
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Matrix

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Fintype Idx] [DecidableEq Idx] in
private theorem gramE_entry_continuousOn
    (e : Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e]
    (g : SmoothRiemannianMetric I M) (basis : Module.Basis Idx ℝ E)
    (i j : Idx) :
    ContinuousOn (fun x => PDE.RicciFlow.gramE e g basis x i j) e.baseSet := by
  classical
  have h := (PDE.RicciFlow.gCompField_mdiffOn e g basis ![i, j]).continuousOn
  simpa [PDE.RicciFlow.gramE, PDE.RicciFlow.frameComp0S_apply, Tensor0SBundle.metricTensorField_apply] using h

omit [Fintype Idx] [DecidableEq Idx] in
theorem exists_pos_bound_localFrame_on_compact [Finite Idx]
    (e : Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e]
    (g : SmoothRiemannianMetric I M) (basis : Module.Basis Idx ℝ E)
    {K : Set M} (hK : IsCompact K) (hKchart : K ⊆ e.baseSet) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ K, ∀ i : Idx,
      Real.sqrt (g.inner x (e.localFrame basis i x) (e.localFrame basis i x)) ≤ R := by
  classical
  let _ := Fintype.ofFinite Idx
  have hbound (i : Idx) : ∃ C : ℝ, ∀ x ∈ K,
      Real.sqrt (PDE.RicciFlow.gramE e g basis x i i) ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (((gramE_entry_continuousOn e g basis i i).mono hKchart).sqrt)
    exact ⟨C, fun x hx => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hC x hx⟩
  choose C hC using hbound
  refine ⟨1 + ∑ i, max (C i) 0, by positivity, fun x hx i => ?_⟩
  calc
    _ ≤ C i := hC i x hx
    _ ≤ max (C i) 0 := le_max_left _ _
    _ ≤ ∑ j, max (C j) 0 :=
      Finset.single_le_sum (fun j _ => le_max_right (C j) 0) (Finset.mem_univ i)
    _ ≤ _ := by linarith

omit [DecidableEq Idx] in
theorem exists_pos_mul_dotProduct_le_gramE
    (e : Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e]
    (g : SmoothRiemannianMetric I M) (basis : Module.Basis Idx ℝ E)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ e.baseSet) :
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ K, ∀ ξ : Idx → ℝ,
      c * (ξ ⬝ᵥ ξ) ≤ ξ ⬝ᵥ PDE.RicciFlow.gramE e g basis b *ᵥ ξ := by
  classical
  let V := EuclideanSpace ℝ Idx
  let Q : M × V → ℝ := fun p => p.2.ofLp ⬝ᵥ PDE.RicciFlow.gramE e g basis p.1 *ᵥ p.2.ofLp
  have hcont : ContinuousOn Q (K ×ˢ (Set.univ : Set V)) := by
    apply continuousOn_finsetSum
    intro i _
    apply ContinuousOn.mul
    · exact ((PiLp.continuous_apply 2 _ i).comp continuous_snd).continuousOn
    · change ContinuousOn (fun a : M × V => ∑ j, PDE.RicciFlow.gramE e g basis a.1 i j * a.2 j) _
      apply continuousOn_finsetSum
      intro j _
      exact (((gramE_entry_continuousOn e g basis i j).mono hKchart).comp
        continuous_fst.continuousOn (fun _ hp => hp.1)).mul
          (((PiLp.continuous_apply 2 _ j).comp continuous_snd).continuousOn)
  have hnorm (v : V) : ‖v‖ ^ 2 = v.ofLp ⬝ᵥ v.ofLp := by
    simpa only [dotProduct, ← sq] using EuclideanSpace.real_norm_sq_eq v
  have hsphere (v : V) (hv : v ≠ 0) : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hQscale (b : M) (v : V) (r : ℝ) : Q (b, r • v) = r ^ 2 * Q (b, v) := by
    change (r • v.ofLp) ⬝ᵥ PDE.RicciFlow.gramE e g basis b *ᵥ (r • v.ofLp) = _
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  by_cases hnonempty : (K ×ˢ Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨p, hp, hmin⟩ := (hK.prod (isCompact_sphere (0 : V) 1)).exists_isMinOn hnonempty
      (hcont.mono (Set.prod_mono_right (Set.subset_univ _)))
    have hpne : p.2.ofLp ≠ 0 := by
      intro heq
      have hz : p.2 = 0 := (WithLp.ofLp_injective 2) heq
      have : (0 : ℝ) = 1 := by simpa only [hz, Metric.mem_sphere, dist_self] using hp.2
      exact zero_ne_one this
    have hpQ : 0 < Q p := by
      simpa only [Q, star_trivial] using
        (PDE.RicciFlow.gramE_posDef e g basis (hKchart hp.1)).dotProduct_mulVec_pos hpne
    refine ⟨Q p, hpQ, fun b hb ξ => ?_⟩
    let v : V := WithLp.toLp 2 ξ
    by_cases hv : v = 0
    · have hξ : ξ = 0 := congrArg WithLp.ofLp hv
      simp only [hξ, dotProduct_zero, mul_zero, Matrix.mulVec_zero, le_refl]
    · have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hlower : Q p ≤ Q (b, ‖v‖⁻¹ • v) :=
        hmin (show (b, ‖v‖⁻¹ • v) ∈ K ×ˢ Metric.sphere (0 : V) 1 from ⟨hb, hsphere v hv⟩)
      rw [hQscale] at hlower
      have hmul := mul_le_mul_of_nonneg_right hlower (sq_nonneg ‖v‖)
      have hcancel : (‖v‖⁻¹ ^ 2 * Q (b, v)) * ‖v‖ ^ 2 = Q (b, v) := by
        field_simp
      rw [hcancel, hnorm] at hmul
      exact hmul
  · refine ⟨1, zero_lt_one, fun b hb ξ => ?_⟩
    let v : V := WithLp.toLp 2 ξ
    have hv : v = 0 := by
      by_contra hv
      exact hnonempty ⟨(b, ‖v‖⁻¹ • v), hb, hsphere v hv⟩
    have hξ : ξ = 0 := congrArg WithLp.ofLp hv
    simp only [hξ, dotProduct_zero, mul_zero, Matrix.mulVec_zero, le_refl]

theorem exists_abs_gramInv_le_of_lower_bound
    (e : Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e]
    (gRef : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx ℝ E)
    {K : Set M} (hK : IsCompact K) (hKchart : K ⊆ e.baseSet)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ g : SmoothRiemannianMetric I M,
      (∀ v : TangentSpace I y, lam * gRef.inner y v v ≤ g.inner y v v) →
        ∀ i j : Idx,
          |(PDE.RicciFlow.gramE e g basis y)⁻¹ i j| ≤ C := by
  classical
  obtain ⟨c, hc, hbound⟩ := exists_pos_mul_dotProduct_le_gramE e gRef basis hK hKchart
  refine ⟨Real.sqrt (Fintype.card Idx) / (lam * c),
    div_nonneg (Real.sqrt_nonneg _) (mul_pos hlam hc).le, fun y hy g hlow i j => ?_⟩
  have hquad (v : Idx → ℝ) :
      lam * c * (v ⬝ᵥ v) ≤ v ⬝ᵥ PDE.RicciFlow.gramE e g basis y *ᵥ v := by
    calc
      lam * c * (v ⬝ᵥ v) = lam * (c * (v ⬝ᵥ v)) := mul_assoc _ _ _
      _ ≤ lam * (v ⬝ᵥ PDE.RicciFlow.gramE e gRef basis y *ᵥ v) :=
        mul_le_mul_of_nonneg_left (hbound y hy v) hlam.le
      _ ≤ v ⬝ᵥ PDE.RicciFlow.gramE e g basis y *ᵥ v := by
        rw [PDE.RicciFlow.gramE_dotVec, PDE.RicciFlow.gramE_dotVec]
        exact hlow _
  have hnorm := PDE.RicciFlow.ginv_compL2_le e g basis (lam * c)
    (mul_pos hlam hc) hquad
  calc
    |(PDE.RicciFlow.gramE e g basis y)⁻¹ i j| =
        |PDE.RicciFlow.ginvCompField e g basis y ![i, j]| := by
      simp only [PDE.RicciFlow.ginvCompField, Matrix.cons_val_zero, Matrix.cons_val_one]
    _ ≤ PDE.RicciFlow.compL2 (PDE.RicciFlow.ginvCompField e g basis y) := by
      apply Real.abs_le_sqrt
      exact Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ ![i, j])
    _ ≤ Real.sqrt (Fintype.card Idx) / (lam * c) := by
      exact hnorm

end DifferentialGeometry.Tensor.Coordinates
