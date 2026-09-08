import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.EndomorphismScalarization
import DifferentialGeometry.Analysis.InnerProductSpace.SpectralBounds
import DifferentialGeometry.Geometry.Connection.NormalSection

noncomputable section

open Bundle CovariantDerivative Filter Set
open DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


variable [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

private theorem exists_unit_minimum_eigenvector {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (A : W →L[ℝ] W) (hA : A.toLinearMap.IsSymmetric)
    (hneg : (⨅ v : {v : W // v ≠ 0}, A.rayleighQuotient v) < 0) :
    ∃ v : W, ‖v‖ = 1 ∧
      A v = (⨅ w : {w : W // w ≠ 0}, A.rayleighQuotient w) • v := by
  have : Nontrivial (W) := by
    rcases subsingleton_or_nontrivial (W) with h | h
    · let : IsEmpty {v : W // v ≠ 0} := ⟨fun v => v.property (Subsingleton.elim _ _)⟩
      simp only [iInf, Set.range_eq_empty, Real.sInf_empty] at hneg
      exact (lt_irrefl 0 hneg).elim
    · exact h
  have hdim := Module.finrank_pos (R := ℝ) (M := W)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdim)
  let v := hA.eigenvectorBasis hn (Fin.last n)
  refine ⟨v, (hA.eigenvectorBasis hn).orthonormal.norm_eq_one _, ?_⟩
  rw [hA.iInf_rayleighQuotient_eq_eigenvalues_last hn]
  exact hA.apply_eigenvectorBasis hn (Fin.last n)



theorem exists_cutoff_negative_minimum_eigenvalue_lower_support
    [NeZero (Module.finrank ℝ E)]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (x : M) (hx : I.IsInteriorPoint x)
    (X : ℝ → (y : M) → TangentSpace I y)
    (hGconn : G.connection t = LeviCivita (I := I) (G.metric t))
    (hAt : DifferentiableWithinAt ℝ (fun q => A q x) (Icc 0 T) t)
    (hA : (A t x).toLinearMap.IsSymmetric)
    (hneg : (⨅ v : {v : V x // v ≠ 0}, (A t x).rayleighQuotient v) < 0)
    (χ φ : ℝ → M → ℝ)
    (hφχ : ∀ᶠ p in 𝓝[Icc 0 T ×ˢ (Set.univ : Set M)] (t, x),
      0 ≤ φ p.1 p.2 ∧ φ p.1 p.2 ≤ χ p.1 p.2)
    (hφeq : φ t x = χ t x)
    (hφtime : DifferentiableWithinAt ℝ (fun q => φ q x) (Icc 0 T) t)
    (hφspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y)
    (hφgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (φ t) y) x) :
    ∃ v : Cₛ^∞⟮I; F, V⟯,
      let ν := ⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w
      let q : ℝ → M → ℝ := fun s y => inner ℝ (A s y (v y)) (v y)
      let ψ : ℝ → M → ℝ := fun s y => -(φ s y * q s y)
      cov v x = 0 ∧
      (∀ᶠ y in 𝓝 x, ‖v y‖ = 1) ∧
      A t x (v x) = ν • v x ∧
      ψ t x = χ t x * max (-ν) 0 ∧
      (∀ᶠ p in 𝓝[Icc 0 T ×ˢ (Set.univ : Set M)] (t, x),
        ψ p.1 p.2 ≤ χ p.1 p.2 * max (-(⨅ w : {w : V p.2 // w ≠ 0},
          (A p.1 p.2).rayleighQuotient w)) 0) ∧
      DifferentiableWithinAt ℝ (fun s => ψ s x) (Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (ψ t) y) ∧
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (ψ t) y) x ∧
      parabolicOperatorWithDrift (I := I) G T X ψ t x =
        -φ t x * inner ℝ
          ((derivWithin (fun s => A s x) (Icc 0 T) t -
            rawBundleEndomorphismConnLap (I := I) (G.metric t) cov (fun y => A t y) x -
            HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
              (fun y => A t y) x (X t x)) (v x)) (v x) -
        ν * parabolicOperatorWithDrift (I := I) G T X φ t x +
        2 * (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
          (gradientAt (I := I) G t (q t) x) := by
  let : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  obtain ⟨v₀, hv₀, heig⟩ := exists_unit_minimum_eigenvector (A t x) hA hneg
  have horth : Orthonormal ℝ (fun _ : Fin 1 => v₀) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    simp only [hij, ↓reduceIte, real_inner_self_eq_norm_sq, hv₀, one_pow]
  obtain ⟨U, hU, hxU, vs, hvs, hvsx, hvscov⟩ :=
    exists_orthonormal_normal_sections cov hcov x (fun _ : Fin 1 => v₀) horth
  let v := vs 0
  let ν := ⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w
  let q : ℝ → M → ℝ := fun s y => inner ℝ (A s y (v y)) (v y)
  let ψ : ℝ → M → ℝ := fun s y => -(φ s y * q s y)
  have hunit : ∀ᶠ y in 𝓝 x, ‖v y‖ = 1 := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact (hvs y hy).norm_eq_one 0
  have hvx : v x = v₀ := hvsx 0
  have hvnorm : ‖v x‖ = 1 := by rw [hvx]; exact hv₀
  have heigen : A t x (v x) = ν • v x := by rw [hvx]; exact heig
  have hqx : q t x = ν := by
    simp only [q, heigen, real_inner_smul_left, real_inner_self_eq_norm_sq, hvnorm,
      one_pow, mul_one]
  have hqtime : DifferentiableWithinAt ℝ (fun s => q s x) (Icc 0 T) t :=
    (hAt.clm_apply (differentiableWithinAt_const (c := v x))).inner ℝ
      (differentiableWithinAt_const (c := v x))
  have hqsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (q t) :=
    (ContMDiff.clm_bundle_apply (b := id) (A t).contMDiff v.contMDiff).inner_bundle
      v.contMDiff
  have hqspace (y : M) : MDifferentiableAt I 𝓘(ℝ, ℝ) (q t) y :=
    hqsmooth.mdifferentiableAt (by simp)
  have hqgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (q t) y) x :=
    (gradientFun_smooth (I := I) (G.metric t) hqsmooth).mdifferentiableAt (by simp)
  have hprodspace : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => φ t y * q t y) y := by
    filter_upwards [hφspace] with y hy
    exact hy.mul (hqspace y)
  have hprodgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (fun z => φ t z * q t z) y) x := by
    have heq : (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z => φ t z * q t z) y) =ᶠ[𝓝 x]
        (T% fun y : M => φ t y • gradientFun (I := I) (G.metric t) (q t) y +
          q t y • gradientFun (I := I) (G.metric t) (φ t) y) := by
      filter_upwards [hφspace] with y hy
      exact congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I : M → Type _)))
        (gradientFun_mul (I := I) (G.metric t) hy (hqspace y))
    exact (mdifferentiableAt_add_section
      (hφspace.self_of_nhds.smul_section hqgrad)
      ((hqspace x).smul_section hφgrad)).congr_of_eventuallyEq heq
  refine ⟨v, hvscov 0, hunit, heigen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change -(φ t x * q t x) = _
    rw [hqx, hφeq, max_eq_left (neg_nonneg.mpr hneg.le)]
    ring
  · have hunit' : ∀ᶠ p in 𝓝[Icc 0 T ×ˢ (Set.univ : Set M)] (t, x), ‖v p.2‖ = 1 :=
      ((continuous_snd.continuousAt : ContinuousAt (fun p : ℝ × M => p.2) (t, x)).eventually
        hunit).filter_mono inf_le_left
    filter_upwards [hunit', hφχ] with p hp hφp
    have hvne : v p.2 ≠ 0 := norm_ne_zero_iff.mp (hp.trans_ne one_ne_zero)
    have hray := (A p.1 p.2).iInf_rayleighQuotient_le hvne
    have hquot : (A p.1 p.2).rayleighQuotient (v p.2) = q p.1 p.2 := by
      simp only [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, hp, one_pow, div_one,
        RCLike.re_to_real, q]
    rw [hquot] at hray
    have hmax : -(q p.1 p.2) ≤ max (-(⨅ w : {w : V p.2 // w ≠ 0},
        (A p.1 p.2).rayleighQuotient w)) 0 :=
      (neg_le_neg hray).trans (le_max_left _ _)
    change -(φ p.1 p.2 * q p.1 p.2) ≤ _
    calc
      _ = φ p.1 p.2 * (-q p.1 p.2) := by ring
      _ ≤ φ p.1 p.2 * max (-(⨅ w : {w : V p.2 // w ≠ 0},
          (A p.1 p.2).rayleighQuotient w)) 0 := mul_le_mul_of_nonneg_left hmax hφp.1
      _ ≤ _ := mul_le_mul_of_nonneg_right hφp.2 (le_max_right _ _)
  · exact (hφtime.mul hqtime).neg
  · filter_upwards [hφspace] with y hy
    exact (hy.mul (hqspace y)).neg
  · have heq : (T% fun y : M => gradientFun (I := I) (G.metric t) (ψ t) y) =ᶠ[𝓝 x]
        (T% fun y : M => (-1 : ℝ) •
          gradientFun (I := I) (G.metric t) (fun z => φ t z * q t z) y) := by
      filter_upwards [hprodspace] with y hy
      apply congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      have hfun : ψ t = (-1 : ℝ) • (fun z => φ t z * q t z) := by
        funext z
        simp only [ψ, Pi.smul_apply, smul_eq_mul, neg_one_mul]
      rw [hfun]
      exact gradientFun_const_smul (I := I) (G.metric t) (-1 : ℝ) hy
    exact (hprodgrad.smul_const_section (a := (-1 : ℝ))).congr_of_eventuallyEq heq
  · have hmul := parabolic_mul_at (I := I) G T X φ q t x hφtime
      hqtime hφspace (Eventually.of_forall hqspace) hφgrad hqgrad
    have hnegop := parabolic_smul_at (I := I) G T X (-1)
      (fun s y => φ s y * q s y) t x (hφtime.mul hqtime)
      hprodspace hprodgrad
    have hunitInner : ∀ᶠ y in 𝓝 x, inner ℝ (v y) (v y) = 1 := by
      filter_upwards [hunit] with y hy
      simp only [real_inner_self_eq_norm_sq, hy, one_pow]
    have hscalar := parabolicOperatorWithDrift_inner_endomorphism_apply_of_normal_eigenvector
      (I := I) G cov hcov hT ht A v x hx X hGconn hAt hA heigen (hvscov 0) hunitInner
    change parabolicOperatorWithDrift (I := I) G T X q t x = _ at hscalar
    have hψ : (fun s y => (-1 : ℝ) * (φ s y * q s y)) = ψ := by
      funext s y
      simp only [ψ, neg_one_mul]
    change parabolicOperatorWithDrift (I := I) G T X
      (fun s y => (-1 : ℝ) * (φ s y * q s y)) t x =
        -1 * parabolicOperatorWithDrift (I := I) G T X (fun s y => φ s y * q s y) t x at hnegop
    rw [hψ, hmul, hscalar, hqx] at hnegop
    change parabolicOperatorWithDrift (I := I) G T X ψ t x = _
    rw [hnegop]
    ring

end DifferentialGeometry.Analysis.Parabolic
