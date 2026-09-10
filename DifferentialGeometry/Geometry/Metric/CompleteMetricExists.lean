import DifferentialGeometry.Geometry.Connection.LocalFrameRegularity
import DifferentialGeometry.Geometry.Metric.Construction.CompactPerturbationCompleteness
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false

noncomputable section

universe u uE uH

open Bundle Manifold MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



namespace Geometry


def addGradSqForm (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  g.inner x + (mvfderiv (I := I) f x).smulRight (mvfderiv (I := I) f x)

omit [FiniteDimensional ℝ E] in
lemma addGradSqForm_apply (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v w : TangentSpace I x) :
    addGradSqForm (I := I) g f x v w =
      g.inner x v w + mvfderiv (I := I) f x v * mvfderiv (I := I) f x w := by
  simp only [addGradSqForm, ContinuousLinearMap.smulRight_apply, add_apply, smul_apply,
    smul_eq_mul]

omit [FiniteDimensional ℝ E] in
lemma addGradSqForm_symm (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v w : TangentSpace I x) :
    addGradSqForm (I := I) g f x v w = addGradSqForm (I := I) g f x w v := by
  rw [addGradSqForm_apply, addGradSqForm_apply, g.symm x v w, mul_comm]

omit [FiniteDimensional ℝ E] in
lemma addGradSqForm_pos (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < addGradSqForm (I := I) g f x v v := by
  rw [addGradSqForm_apply]
  have h1 := g.pos x v hv
  have h2 : 0 ≤ mvfderiv (I := I) f x v * mvfderiv (I := I) f x v := mul_self_nonneg _
  linarith

lemma addGradSqForm_coeff_contMDiffOn (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => addGradSqForm (I := I) g f x
        (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hrw : (fun x : M => addGradSqForm (I := I) g f x
        (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x))
      = fun x : M => g.inner x (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x)
          + mvfderiv (I := I) f x (frameVec (I := I) x₀ i x)
            * mvfderiv (I := I) f x (frameVec (I := I) x₀ j x) := by
    funext x
    exact addGradSqForm_apply (I := I) g f x _ _
  rw [hrw]
  intro x hx
  have hfri := frameVec_cmdiffAt (I := I) x₀ i hx
  have hfrj := frameVec_cmdiffAt (I := I) x₀ j hx
  have hg : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => g.inner y (frameVec (I := I) x₀ i y) (frameVec (I := I) x₀ j y)) x :=
    CovariantDerivative.metric_inner_contMDiffAt (I := I) g hfri hfrj le_rfl
  have hdi : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => mvfderiv (I := I) f y (frameVec (I := I) x₀ i y)) x :=
    mvfderiv_apply_contMDiffAt_of_section (I := I) hf.contMDiffAt hfri
  have hdj : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => mvfderiv (I := I) f y (frameVec (I := I) x₀ j y)) x :=
    mvfderiv_apply_contMDiffAt_of_section (I := I) hf.contMDiffAt hfrj
  exact (hg.add (hdi.mul hdj)).contMDiffWithinAt

end Geometry

open Geometry

def SmoothRiemannianMetric.addGradSq (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) : SmoothRiemannianMetric I M :=
  (smoothMetric_of_localCoeff (I := I) (addGradSqForm (I := I) g f)
    (fun x v w => addGradSqForm_symm (I := I) g f x v w)
    (fun x v hv => addGradSqForm_pos (I := I) g f x v hv)
    (fun x₀ i j => addGradSqForm_coeff_contMDiffOn (I := I) g f hf x₀ i j)).choose

theorem SmoothRiemannianMetric.addGradSq_inner (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) (v w : TangentSpace I x) :
    (g.addGradSq f hf).inner x v w =
      g.inner x v w + mvfderiv (I := I) f x v * mvfderiv (I := I) f x w := by
  rw [show (g.addGradSq f hf).inner x v w = addGradSqForm (I := I) g f x v w from
      (smoothMetric_of_localCoeff (I := I) (addGradSqForm (I := I) g f)
        (fun x v w => addGradSqForm_symm (I := I) g f x v w)
        (fun x v hv => addGradSqForm_pos (I := I) g f x v hv)
        (fun x₀ i j =>
          addGradSqForm_coeff_contMDiffOn (I := I) g f hf x₀ i j)).choose_spec x v w]
  exact addGradSqForm_apply (I := I) g f x v w

theorem SmoothRiemannianMetric.le_addGradSq_inner (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) (v : TangentSpace I x) :
    g.inner x v v ≤ (g.addGradSq f hf).inner x v v := by
  rw [SmoothRiemannianMetric.addGradSq_inner]
  linarith [mul_self_nonneg (mvfderiv (I := I) f x v)]

theorem SmoothRiemannianMetric.sq_mvfderiv_le_addGradSq_inner
    (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) (v : TangentSpace I x) :
    mvfderiv (I := I) f x v * mvfderiv (I := I) f x v ≤ (g.addGradSq f hf).inner x v v := by
  rw [SmoothRiemannianMetric.addGradSq_inner]
  have : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (g.pos x v hv).le
  linarith

section SigmaCompact

variable [SigmaCompactSpace M] [T2Space M]



theorem exists_contMDiff_of_compact_family
    (A : ℕ → Set M) (hAc : ∀ n, IsCompact (A n))
    (hAsub : ∀ n, A n ⊆ interior (A (n + 1)))
    (hAnhds : ∀ x : M, ∃ n, A n ∈ 𝓝 x) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ (∀ x, 0 ≤ f x) ∧
      (∀ x ∈ A 0, f x = 0) ∧ ∀ (m : ℕ) (x : M), x ∉ A m → (m : ℝ) ≤ f x := by
  classical
  have hstep : ∀ n : ℕ, A n ⊆ A (n + 1) := fun n => (hAsub n).trans interior_subset
  have hmono : Monotone A := monotone_nat_of_le_succ hstep
  have hbump : ∀ n : ℕ, ∃ c : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ c ∧
      (∀ x ∈ A n, c x = 1) ∧ (∀ x, x ∉ interior (A (n + 1)) → c x = 0) ∧
      ∀ x, c x ∈ Icc (0 : ℝ) 1 := by
    intro n
    have hdisj : Disjoint ((interior (A (n + 1)))ᶜ) (A n) := by
      rw [Set.disjoint_compl_left_iff_subset]
      exact hAsub n
    obtain ⟨c, hc0, hc1, hcI⟩ :=
      exists_contMDiffMap_zero_one_of_isClosed I (n := (⊤ : ℕ∞))
        isOpen_interior.isClosed_compl (hAc n).isClosed hdisj
    exact ⟨fun x => c x, c.contMDiff, fun x hx => by simpa using hc1 hx,
      fun x hx => by simpa using hc0 hx, hcI⟩
  choose c hcsmooth hcone hczero hcIcc using hbump
  have hunonneg : ∀ (n : ℕ) (x : M), 0 ≤ 1 - c n x := by
    intro n x
    linarith [(hcIcc n x).2]
  have huzero : ∀ (n : ℕ) (x : M), x ∈ A n → 1 - c n x = 0 := by
    intro n x hx
    rw [hcone n x hx, sub_self]
  have hsupp : ∀ (m : ℕ) (x : M), x ∈ A m →
      Function.support (fun n : ℕ => 1 - c n x) ⊆ (Finset.range m : Finset ℕ) := by
    intro m x hx n hn
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hle
    exact hn (huzero n x (hmono (not_lt.mp hle) hx))
  have hfeq : ∀ (m : ℕ) (x : M), x ∈ A m →
      (∑ᶠ n : ℕ, (1 - c n x)) = ∑ n ∈ Finset.range m, (1 - c n x) :=
    fun m x hx => finsum_eq_sum_of_support_subset _ (hsupp m x hx)
  refine ⟨fun x => ∑ᶠ n : ℕ, (1 - c n x), ?_, ?_, ?_, ?_⟩
  · intro x₀
    obtain ⟨m, hm⟩ := hAnhds x₀
    have heq : (fun x : M => ∑ᶠ n : ℕ, (1 - c n x)) =ᶠ[𝓝 x₀]
        fun x : M => ∑ n ∈ Finset.range m, (1 - c n x) := by
      filter_upwards [hm] with x hx using hfeq m x hx
    refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
    exact ContMDiffAt.sum fun n _ => contMDiffAt_const.sub (hcsmooth n).contMDiffAt
  · intro x
    obtain ⟨m, hm⟩ := hAnhds x
    change (0 : ℝ) ≤ ∑ᶠ n : ℕ, (1 - c n x)
    rw [hfeq m x (mem_of_mem_nhds hm)]
    exact Finset.sum_nonneg fun n _ => hunonneg n x
  · intro x hx
    change (∑ᶠ n : ℕ, (1 - c n x)) = 0
    rw [hfeq 0 x hx, Finset.range_zero, Finset.sum_empty]
  · intro m x hx
    obtain ⟨p, hp⟩ := hAnhds x
    have hxN : x ∈ A (max p m) := hmono (le_max_left p m) (mem_of_mem_nhds hp)
    change (m : ℝ) ≤ ∑ᶠ n : ℕ, (1 - c n x)
    rw [hfeq (max p m) x hxN]
    have hone : ∀ n ∈ Finset.range m, 1 - c n x = (1 : ℝ) := by
      intro n hn
      have hnot : x ∉ interior (A (n + 1)) := by
        intro hmem
        exact hx (hmono (Nat.succ_le_of_lt (Finset.mem_range.mp hn)) (interior_subset hmem))
      rw [hczero n x hnot, sub_zero]
    calc (m : ℝ) = ∑ n ∈ Finset.range m, (1 - c n x) := by
          rw [Finset.sum_congr rfl hone]
          simp
      _ ≤ ∑ n ∈ Finset.range (max p m), (1 - c n x) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (le_max_right p m)) fun n _ _ => hunonneg n x

theorem exists_contMDiff_properFun_eqZero_of_isCompact
    (K : Set M) (hK : IsCompact K) :
    ∃ (f : M → ℝ) (W : Set M), ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ IsOpen W ∧ K ⊆ W ∧
      (∀ x ∈ W, f x = 0) ∧ (∀ x, 0 ≤ f x) ∧
      ∀ c : ℝ, IsCompact {x : M | f x ≤ c} := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  let Kex : CompactExhaustion M := CompactExhaustion.choice M
  obtain ⟨n₀, hn₀⟩ := Kex.exists_superset_of_isCompact hK
  have hAc : ∀ n : ℕ, IsCompact (Kex (n + n₀ + 1)) := fun n => Kex.isCompact _
  have hAsub : ∀ n : ℕ, Kex (n + n₀ + 1) ⊆ interior (Kex (n + 1 + n₀ + 1)) := by
    intro n
    have hidx : n + 1 + n₀ + 1 = n + n₀ + 1 + 1 := by omega
    rw [hidx]
    exact Kex.subset_interior_succ _
  have hAnhds : ∀ x : M, ∃ n : ℕ, Kex (n + n₀ + 1) ∈ 𝓝 x := by
    intro x
    obtain ⟨m, hm⟩ := Kex.exists_mem_nhds x
    exact ⟨m, Filter.mem_of_superset hm (Kex.subset (by omega))⟩
  obtain ⟨f, hfsmooth, hfnonneg, hfzero, hflow⟩ :=
    exists_contMDiff_of_compact_family (I := I) (fun n : ℕ => Kex (n + n₀ + 1)) hAc hAsub hAnhds
  refine ⟨f, interior (Kex (0 + n₀ + 1)), hfsmooth, isOpen_interior, ?_, ?_, hfnonneg, ?_⟩
  · have h0 : 0 + n₀ + 1 = n₀ + 1 := by omega
    rw [h0]
    exact hn₀.trans (Kex.subset_interior_succ n₀)
  · exact fun x hx => hfzero x (interior_subset hx)
  · intro c
    have hclosed : IsClosed {x : M | f x ≤ c} :=
      isClosed_le hfsmooth.continuous continuous_const
    refine (hAc (⌈c⌉₊ + 1)).of_isClosed_subset hclosed ?_
    intro x hx
    by_contra hmem
    have hlow := hflow (⌈c⌉₊ + 1) x hmem
    have hce : c ≤ (⌈c⌉₊ : ℝ) := Nat.le_ceil c
    simp only [Set.mem_ofPred_eq] at hx
    push_cast at hlow
    linarith



omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem ofReal_abs_sub_le_riemannianEDistOf
    (h : SmoothRiemannianMetric I M) (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hbound : ∀ (x : M) (v : TangentSpace I x),
      mvfderiv (I := I) f x v * mvfderiv (I := I) f x v ≤ h.inner x v v)
    (x y : M) :
    ENNReal.ofReal |f x - f y| ≤ riemannianEDistOf (I := I) h x y := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨h.toRiemannianMetric⟩
  have henorm : ∀ (z : M) (v : TangentSpace I z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (h.inner z v v)) := by
    intro z v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 2
  have hptwise : ∀ (z : M) (v : TangentSpace I z),
      ENNReal.ofReal |mvfderiv (I := I) f z v| ≤ ‖v‖ₑ := by
    intro z v
    rw [henorm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    have := hbound z v
    nlinarith [this]
  have key : ∀ γ : ℝ → M, CMDiff[Set.Icc (0 : ℝ) 1] 1 γ →
      ENNReal.ofReal |f (γ 0) - f (γ 1)| ≤ pathELength I γ 0 1 := by
    intro γ hγ
    rcases eq_or_ne (pathELength I γ 0 1) ⊤ with hLtop | hLtop
    · rw [hLtop]
      exact le_top
    have hLform : pathELength I γ 0 1
        = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ :=
      pathELength_eq_lintegral_mfderiv_Ioo
    have hucont : ContinuousOn (fun t : ℝ => f (γ t)) (Set.Icc 0 1) :=
      hf.continuous.comp_continuousOn hγ.continuousOn
    have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => f (γ s))
          (mvfderiv (I := I) f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)) t := by
      intro t ht
      have hmem : Set.Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
      have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
        ((hγ.mdifferentiableOn one_ne_zero) t
          (Set.Ioo_subset_Icc_self ht)).mdifferentiableAt hmem
      have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t) := hf.mdifferentiable (by simp) (γ t)
      have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => f (γ s)) t :=
        hfd.comp t hγd
      have hdiff : DifferentiableAt ℝ (fun s : ℝ => f (γ s)) t :=
        mdifferentiableAt_iff_differentiableAt.mp hcomp
      have hval : deriv (fun s : ℝ => f (γ s)) t
          = mvfderiv (I := I) f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
        rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv,
          show (fun s : ℝ => f (γ s)) = f ∘ γ from rfl, mfderiv_comp t hfd hγd]
        rfl
      have := hdiff.hasDerivAt
      rwa [hval] at this
    have hderivval : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        deriv (fun s : ℝ => f (γ s)) t
          = mvfderiv (I := I) f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) :=
      fun t ht => (hderiv t ht).deriv
    have hbdd : ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal |deriv (fun s : ℝ => f (γ s)) t| ≤ pathELength I γ 0 1 := by
      rw [hLform]
      refine MeasureTheory.setLIntegral_mono_ae' measurableSet_Ioo ?_
      filter_upwards with t ht
      rw [hderivval t ht]
      exact hptwise _ _
    have hint : MeasureTheory.IntegrableOn (deriv fun s : ℝ => f (γ s))
        (Set.Ioo (0 : ℝ) 1) := by
      refine ⟨(measurable_deriv (fun s : ℝ => f (γ s))).aestronglyMeasurable.restrict, ?_⟩
      rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
      calc ∫⁻ t in Set.Ioo (0 : ℝ) 1, ‖deriv (fun s : ℝ => f (γ s)) t‖ₑ
          = ∫⁻ t in Set.Ioo (0 : ℝ) 1,
              ENNReal.ofReal |deriv (fun s : ℝ => f (γ s)) t| := by
            refine MeasureTheory.lintegral_congr fun t => ?_
            rw [Real.enorm_eq_ofReal_abs]
        _ ≤ pathELength I γ 0 1 := hbdd
        _ < ⊤ := hLtop.lt_top
    have hIint : IntervalIntegrable (deriv fun s : ℝ => f (γ s)) MeasureTheory.volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
      exact hint
    have hderivWithin : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivWithinAt (fun s : ℝ => f (γ s))
          (deriv (fun s : ℝ => f (γ s)) t) (Set.Ioi t) t := by
      intro t ht
      have h1 := (hderiv t ht).hasDerivWithinAt (s := Set.Ioi t)
      rwa [← hderivval t ht] at h1
    have hftc : ∫ t in (0 : ℝ)..1, deriv (fun s : ℝ => f (γ s)) t = f (γ 1) - f (γ 0) :=
      intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hucont
        hderivWithin hIint
    have habs : |f (γ 1) - f (γ 0)|
        ≤ ∫ t in (0 : ℝ)..1, |deriv (fun s : ℝ => f (γ s)) t| := by
      rw [← hftc]
      exact intervalIntegral.abs_integral_le_integral_abs zero_le_one
    have hconv : ENNReal.ofReal (∫ t in (0 : ℝ)..1, |deriv (fun s : ℝ => f (γ s)) t|)
        = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv (fun s : ℝ => f (γ s)) t| := by
      rw [intervalIntegral.integral_of_le zero_le_one,
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint.abs
        (Filter.Eventually.of_forall fun t => abs_nonneg _)
    calc ENNReal.ofReal |f (γ 0) - f (γ 1)|
        = ENNReal.ofReal |f (γ 1) - f (γ 0)| := by rw [abs_sub_comm]
      _ ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..1, |deriv (fun s : ℝ => f (γ s)) t|) :=
          ENNReal.ofReal_le_ofReal habs
      _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1,
            ENNReal.ofReal |deriv (fun s : ℝ => f (γ s)) t| := hconv
      _ ≤ pathELength I γ 0 1 := hbdd
  by_contra hcon
  have hlt : Manifold.riemannianEDist I x y < ENNReal.ofReal |f x - f y| := not_le.mp hcon
  obtain ⟨γ, hγ0, hγ1, hγC, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hlt
  have hkey := key γ hγC
  rw [hγ0, hγ1] at hkey
  exact absurd (hkey.trans_lt hlen) (lt_irrefl _)



attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem RiemannianMetricComplete.of_properFun
    {h : SmoothRiemannianMetric I M} {f : M → ℝ}
    (hcpt : ∀ c : ℝ, IsCompact {x : M | f x ≤ c})
    (hlip : ∀ x y : M, ENNReal.ofReal |f x - f y| ≤ riemannianEDistOf (I := I) h x y) :
    RiemannianMetricComplete (I := I) h := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  refine ⟨?_⟩
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨h.inner, h.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  refine EMetric.complete_of_cauchySeq_tendsto (α := M) fun s hs => ?_
  have hed : ∀ a b : M, edist a b = riemannianEDistOf (I := I) h a b := fun _ _ => rfl
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hs 1 (by norm_num)
  have hmem : ∀ n : ℕ, s (n + N) ∈ {z : M | f z ≤ f (s N) + 1} := by
    intro n
    have h1 : edist (s N) (s (n + N)) < 1 := hN N le_rfl (n + N) (by omega)
    rw [hed] at h1
    have h3 : |f (s N) - f (s (n + N))| < 1 :=
      ENNReal.ofReal_lt_one.mp ((hlip (s N) (s (n + N))).trans_lt h1)
    have h4 := abs_lt.mp h3
    simp only [Set.mem_ofPred_eq]
    linarith [h4.1]
  obtain ⟨z, -, hz⟩ :=
    cauchySeq_tendsto_of_isComplete (hcpt (f (s N) + 1)).isComplete hmem
      (hs.comp_tendsto (Filter.tendsto_add_atTop_nat N))
  exact ⟨z, (Filter.tendsto_add_atTop_iff_nat N).mp hz⟩



theorem exists_riemannianMetricComplete_eqOn_of_isCompact
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K) :
    ∃ (g' : SmoothRiemannianMetric I M) (W : Set M),
      RiemannianMetricComplete (I := I) g' ∧ IsOpen W ∧ K ⊆ W ∧
      (∀ x ∈ W, g'.inner x = g.inner x) ∧
      (∀ x : M, ∀ v : TangentSpace I x, g.inner x v v ≤ g'.inner x v v) := by
  obtain ⟨f, W, hfsmooth, hWopen, hKW, hfW, -, hfcpt⟩ :=
    exists_contMDiff_properFun_eqZero_of_isCompact (I := I) K hK
  have hdW : ∀ x ∈ W, ∀ v : TangentSpace I x, mvfderiv (I := I) f x v = 0 := by
    intro x hx v
    have heq : f =ᶠ[𝓝 x] fun _ : M => (0 : ℝ) := by
      filter_upwards [hWopen.mem_nhds hx] with z hz using hfW z hz
    have hmf : mfderiv I 𝓘(ℝ, ℝ) f x = 0 := by
      rw [heq.mfderiv_eq]
      exact mfderiv_const
    rw [mvfderiv_real_eq_mfderiv I f x v, hmf]
    exact map_zero _
  refine ⟨g.addGradSq f hfsmooth, W, ?_, hWopen, hKW, ?_, ?_⟩
  · refine RiemannianMetricComplete.of_properFun (I := I) (f := f) hfcpt ?_
    refine ofReal_abs_sub_le_riemannianEDistOf (I := I) _ f hfsmooth ?_
    exact fun x v => g.sq_mvfderiv_le_addGradSq_inner f hfsmooth x v
  · intro x hx
    ext v w
    rw [SmoothRiemannianMetric.addGradSq_inner, hdW x hx v, hdW x hx w]
    ring
  · intro x v
    exact g.le_addGradSq_inner f hfsmooth x v

end SigmaCompact

end DifferentialGeometry

end
