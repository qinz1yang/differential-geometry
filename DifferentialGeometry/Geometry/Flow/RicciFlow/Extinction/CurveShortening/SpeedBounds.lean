import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CalculusGeometry
import Mathlib.Topology.Instances.Real.Lemmas
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Evolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ContinuationFrontier

section

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CurveMap

theorem speed_continuous (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (t : ℝ) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 (fun x => c.lift x t)) :
    Continuous (fun x => c.speed g x t) := by
  have hone : Continuous (fun x : ℝ =>
      (TotalSpace.mk' ℝ x (1 : ℝ) : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    ((contMDiff_vectorSpace_iff_contDiff (V := fun _ : ℝ => (1 : ℝ))).mpr
      (contDiff_const (n := 0))).continuous
  have hX : Continuous (fun x =>
      (TotalSpace.mk' E (c.lift x t) (c.X (I := I) x t) : TangentBundle I M)) :=
    (hc.continuous_tangentMap le_rfl).comp hone
  have hq : Continuous (fun x => (g t).inner (c.lift x t)
      (c.X (I := I) x t) (c.X (I := I) x t)) := by
    have hb : Continuous (fun x =>
        TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (c.lift x t)
          ((g t).inner (c.lift x t) (c.X (I := I) x t) (c.X (I := I) x t))) :=
      ((g t).contMDiff.continuous.comp hc.continuous).clm_bundle_apply₂
        (F₁ := E) (F₂ := E) hX hX
    apply continuous_iff_continuousAt.mpr
    intro x
    have hx := hb.continuousAt (x := x)
    rw [FiberBundle.continuousAt_totalSpace] at hx
    exact hx.2
  exact Real.continuous_sqrt.comp hq

theorem exists_speed_bounds (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (t : ℝ) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 (fun x => c.lift x t))
    (hi : ∀ x, c.X (I := I) x t ≠ 0) :
    ∃ m b : ℝ, 0 < m ∧ 0 < b ∧ ∀ x : ℝ, m ≤ c.speed g x t ∧ c.speed g x t ≤ b := by
  have hs := c.speed_continuous g t hc
  have hp : Function.Periodic (fun x => c.speed g x t) 1 := fun x =>
    c.speed_add_period g t x (hc.mdifferentiableAt (by simp))
  have hK := hp.compact_of_continuous one_ne_zero hs
  obtain ⟨m, hm, hmb⟩ := hK.exists_forall_le' continuousOn_id (by
    rintro _ ⟨x, rfl⟩
    exact Real.sqrt_pos.2 ((g t).pos _ _ (hi x)))
  obtain ⟨b, hb⟩ := hK.bddAbove
  have hbpos : 0 < b := (Real.sqrt_pos.2 ((g t).pos _ _ (hi 0))).trans_le (hb (mem_range_self 0))
  exact ⟨m, b, hm, hbpos, fun x => ⟨hmb _ (mem_range_self x), hb (mem_range_self x)⟩⟩

theorem exists_inv_speed_sq_bounds (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (t : ℝ) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 (fun x => c.lift x t))
    (hi : ∀ x, c.X (I := I) x t ≠ 0) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
      ∀ x : ℝ, a ≤ (c.speed g x t ^ 2)⁻¹ ∧ (c.speed g x t ^ 2)⁻¹ ≤ A := by
  obtain ⟨m, b, hm, hb, hbound⟩ := c.exists_speed_bounds g t hc hi
  refine ⟨(b ^ 2)⁻¹, (m ^ 2)⁻¹, by positivity, by positivity, ?_⟩
  intro x
  have hs := Real.sqrt_pos.2 ((g t).pos _ _ (hi x))
  constructor
  · exact (inv_le_inv₀ (sq_pos_of_pos hb) (sq_pos_of_pos hs)).2
      (pow_le_pow_left₀ hs.le (hbound x).2 2)
  · exact (inv_le_inv₀ (sq_pos_of_pos hs) (sq_pos_of_pos hm)).2
      (pow_le_pow_left₀ hm.le (hbound x).1 2)

end CurveMap

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end

section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval} {a b : ℝ}

namespace CurveMap

theorem speed_exponential_bounds_Ico
    (B : RicciBackground (I := I) (M := M) D a b) {T : ℝ} (hTb : T ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    {K : ℝ} (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K)
    (x t : ℝ) (ht : t ∈ Ico a T) :
    c.speed B.family.metric x a * Real.exp (-(K ^ 2 + B.B₀) * (t - a)) ≤
      c.speed B.family.metric x t ∧
    c.speed B.family.metric x t ≤
      c.speed B.family.metric x a * Real.exp (B.B₀ * (t - a)) := by
  rcases lt_or_eq_of_le ht.1 with hat | heq
  · have hsub : Icc a t ⊆ Ico a T := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hc' : c.IsSolutionOn B.family.metric (Icc a t) :=
      hc.mono hsub (fun s hs => ((uniqueDiffOn_Icc hat) s hs).uniqueMDiffWithinAt)
    exact speed_exponential_bounds B hat
      (Set.Icc_subset_Icc le_rfl (ht.2.le.trans hTb)) c hc' K
      (fun y s hs => hcurv y s (hsub hs)) x t ⟨ht.1, le_rfl⟩
  · simp [← heq]

theorem exists_speed_bounds_of_curvature_le_Ico
    (B : RicciBackground (I := I) (M := M) D a b) {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    {K : ℝ} (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K) :
    ∃ m C : ℝ, 0 < m ∧ 0 < C ∧
      ∀ x t, t ∈ Ico a T → m ≤ c.speed B.family.metric x t ∧
        c.speed B.family.metric x t ≤ C := by
  have ha : a ∈ Ico a T := ⟨le_rfl, haT⟩
  have hslice : ContMDiff 𝓘(ℝ, ℝ) I 1 (fun x => c.lift x a) :=
    (contMDiffOn_univ.mp (c.space_slice_contMDiffOn (Ico a T) hc.smooth a ha)).of_le
      (by simp)
  obtain ⟨m, C, hm, hC, hbase⟩ := c.exists_speed_bounds B.family.metric a hslice
    (fun x => hc.immersed x a ha)
  refine ⟨m * Real.exp (-(K ^ 2 + B.B₀) * (T - a)),
    C * Real.exp (B.B₀ * (T - a)), mul_pos hm (Real.exp_pos _),
    mul_pos hC (Real.exp_pos _), ?_⟩
  intro x t ht
  obtain ⟨hlower, hupper⟩ := c.speed_exponential_bounds_Ico B hTb hc hcurv x t ht
  have hlowexp : Real.exp (-(K ^ 2 + B.B₀) * (T - a)) ≤
      Real.exp (-(K ^ 2 + B.B₀) * (t - a)) := by
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonpos_left (sub_le_sub_right ht.2.le a)
      (neg_nonpos.mpr (add_nonneg (sq_nonneg K) B.B₀_nonneg))
  have hupexp : Real.exp (B.B₀ * (t - a)) ≤ Real.exp (B.B₀ * (T - a)) := by
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le a) B.B₀_nonneg
  constructor
  · exact (mul_le_mul (hbase x).1 hlowexp (Real.exp_nonneg _) (c.speed_nonneg _ _ _)).trans
      hlower
  · exact hupper.trans (mul_le_mul (hbase x).2 hupexp (Real.exp_nonneg _) hC.le)

end CurveMap

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
