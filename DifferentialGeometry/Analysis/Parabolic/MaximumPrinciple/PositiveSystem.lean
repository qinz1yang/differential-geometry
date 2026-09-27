import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.KernelRigidity
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.KernelTimeConstancy
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.RankSpreading

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative Set
open scoped Manifold ContDiff Topology InnerProductSpace

namespace PositiveSystem

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem kernel_rigidity_of_constant_range_rank
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ t, ContMDiffCovariantDerivative (cov t) ∞]
    (hcov : ∀ t, (cov t).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    {a b : ℝ}
    (hAspace : ContMDiffOnSpacetimeEndomorphism
      (I := I) (F := F) (V := V) (n := ∞)
      (fun t x ↦ A t x) (Ioo a b ×ˢ (Set.univ : Set M)))
    (q : ℕ) (hrange : ∀ t ∈ Ioo a b, ∀ x,
      Module.finrank ℝ (A t x).range = q)
    (hAsymm : ∀ t ∈ Ioo a b, ∀ x,
      ((A t x : V x →L[ℝ] V x) : V x →ₗ[ℝ] V x).IsSymmetric)
    (hApos : ∀ t ∈ Ioo a b, ∀ x, (A t x).IsPositive)
    (X : ℝ → (x : M) → TangentSpace I x)
    (reaction : ℝ → (x : M) →
      (V x →L[ℝ] V x) → V x →L[ℝ] V x)
    (hreactionNull : ∀ t x,
      satisfiesNullEigenvectorCondition (reaction t x))
    (hAt : ∀ t ∈ Ioo a b, ∀ x,
      DifferentiableAt ℝ (fun s ↦ A s x) t)
    (hevolution : ∀ t ∈ Ioo a b, ∀ x,
      deriv (fun s ↦ A s x) t =
        rawBundleEndomorphismConnLap (I := I) (g t) (cov t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y ↦ A t y) x (X t x) +
          reaction t x (A t x)) :
    let k := Module.finrank ℝ F - q
    (∀ p ∈ Ioo a b ×ˢ (Set.univ : Set M),
      ∃ (U : Set (ℝ × M)) (w : Fin k → (p : ℝ × M) → V p.2),
        IsOpen U ∧ p ∈ U ∧ U ⊆ Ioo a b ×ˢ (Set.univ : Set M) ∧
        (∀ z ∈ U, LinearIndependent ℝ (w · z)) ∧
        (∀ z ∈ U,
          Submodule.span ℝ (Set.range (w · z)) = (A z.1 z.2).ker) ∧
        ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I)
          ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
          (fun z ↦ TotalSpace.mk' F z (w i z) : ℝ × M →
            TotalSpace F ((ContMDiffMap.snd :
              C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯) *ᵖ V)) U) ∧
      (∀ t ∈ Ioo a b,
        IsCovariantlyInvariantSubmoduleFamily (cov t)
          (fun x ↦ (A t x).ker)) ∧
      (∀ t ∈ Ioo a b, ∀ x v, A t x v = 0 →
        inner ℝ (reaction t x (A t x) v) v = 0) ∧
      (∀ t ∈ Ioo a b, ∀ x v, A t x v = 0 →
        deriv (fun s ↦ A s x) t v = reaction t x (A t x) v) ∧
      ∀ t ∈ Ioo a b,
        ∀ (w : (p : ℝ × M) → V p.2) {U : Set (ℝ × M)},
          IsOpen U → ∀ {x}, (t, x) ∈ U →
          ContMDiffOn (𝓘(ℝ, ℝ).prod I)
            ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
            (fun p ↦ TotalSpace.mk' F p (w p) : ℝ × M →
              TotalSpace F ((ContMDiffMap.snd :
                C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯) *ᵖ V)) U →
          (∀ p ∈ U, A p.1 p.2 (w p) = 0) →
          A t x (deriv (fun s ↦ w (s, x)) t) =
              -reaction t x (A t x) (w (t, x)) ∧
            deriv (fun s ↦ A s x) t (w (t, x)) =
              reaction t x (A t x) (w (t, x)) := by
  let k := Module.finrank ℝ F - q
  let W := Ioo a b ×ˢ (Set.univ : Set M)
  have hW : IsOpen W := isOpen_Ioo.prod isOpen_univ
  let _ : ∀ x, FiniteDimensional ℝ (V x) := fun x ↦
    VectorBundle.finiteDimensional ℝ F V x
  have hker : ∀ p ∈ W, Module.finrank ℝ (A p.1 p.2).ker = k := by
    intro p hp
    let e := (trivializationAt F V p.2).linearEquivAt ℝ p.2
      (mem_baseSet_trivializationAt F V p.2)
    have hdim : Module.finrank ℝ (V p.2) = Module.finrank ℝ F :=
      e.finrank_eq
    have hsum := (A p.1 p.2).toLinearMap.finrank_range_add_finrank_ker
    have hrank := hrange p.1 hp.1 p.2
    dsimp only [k]
    omega
  let c : C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯ := ContMDiffMap.snd
  let _ : TopologicalSpace (TotalSpace F (fun p : ℝ × M ↦ V p.2)) := by
    change TopologicalSpace (TotalSpace F (c *ᵖ V)); infer_instance
  let _ : FiberBundle F (fun p : ℝ × M ↦ V p.2) := by
    change FiberBundle F (c *ᵖ V); infer_instance
  let _ : VectorBundle ℝ F (fun p : ℝ × M ↦ V p.2) := by
    change VectorBundle ℝ F (c *ᵖ V); infer_instance
  let _ : ContMDiffVectorBundle ∞ F (fun p : ℝ × M ↦ V p.2)
      (𝓘(ℝ, ℝ).prod I) := by
    change ContMDiffVectorBundle ∞ F (c *ᵖ V) (𝓘(ℝ, ℝ).prod I)
    infer_instance
  have hAspace' : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p ↦ TotalSpace.mk' (F →L[ℝ] F) p (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F)
          (fun p ↦ V p.2 →L[ℝ] V p.2)) W := by
    simpa only [W, ContMDiffOnSpacetimeEndomorphism] using hAspace
  have hsmooth : ∀ p ∈ W,
      ∃ (U : Set (ℝ × M)) (w : Fin k → (p : ℝ × M) → V p.2),
        IsOpen U ∧ p ∈ U ∧ U ⊆ W ∧
        (∀ z ∈ U, LinearIndependent ℝ (w · z)) ∧
        (∀ z ∈ U,
          Submodule.span ℝ (Set.range (w · z)) = (A z.1 z.2).ker) ∧
        ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I)
          ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
          (fun z ↦ TotalSpace.mk' F z (w i z) : ℝ × M →
            TotalSpace F (fun p : ℝ × M ↦ V p.2)) U := by
    intro p hp
    obtain ⟨U, w, hU, hpU, hUW, hw⟩ :=
      ContMDiffVectorSubbundle.exists_kernel_frameOn
        (I := 𝓘(ℝ, ℝ).prod I) (F₁ := F) (F₂ := F)
        (V₁ := fun p : ℝ × M ↦ V p.2)
        (V₂ := fun p : ℝ × M ↦ V p.2)
        (fun p : ℝ × M ↦ A p.1 p.2) W hW hAspace' k hker p hp
    exact ⟨U, w, hU, hpU, hUW,
      fun z hz ↦ hw.linearIndependent hz,
      fun z hz ↦ hw.spans hz, hw.contMDiffOn⟩
  have hinvariant : ∀ t ∈ Ioo a b,
      IsCovariantlyInvariantSubmoduleFamily (cov t)
        (fun x ↦ (A t x).ker) := by
    intro t ht
    apply kernel_isCovariantlyInvariant_of_constant_rank
      (g t) (cov t) (hcov t) A hW hAspace k hker
      (t := t) (fun x ↦ ⟨ht, Set.mem_univ x⟩)
      (hAsymm t ht) (hApos t ht) (X t)
      (fun x ↦ reaction t x (A t x)) (hAt t ht)
    · intro x v hv
      exact hreactionNull t x (A t x) (hApos t ht x) v hv
    · exact hevolution t ht
  have hreaction : ∀ t ∈ Ioo a b, ∀ x v, A t x v = 0 →
      inner ℝ (reaction t x (A t x) v) v = 0 := by
    intro t ht x
    apply kernel_reaction_inner_eq_zero_of_constant_rank
      (g t) (cov t) (hcov t) A hW hAspace k hker
      (t := t) (x := x) ⟨ht, Set.mem_univ x⟩
      (hAsymm t ht) (hApos t ht x) (X t x)
      (reaction t x (A t x)) (hAt t ht x)
    · intro v hv
      exact hreactionNull t x (A t x) (hApos t ht x) v hv
    · exact hevolution t ht x
  have hderiv : ∀ t ∈ Ioo a b, ∀ x v, A t x v = 0 →
      deriv (fun s ↦ A s x) t v = reaction t x (A t x) v := by
    intro t ht x v hv
    obtain ⟨U, w, hU, htxU, -, -, hwspan, hwsmooth⟩ :=
      hsmooth (t, x) ⟨ht, Set.mem_univ x⟩
    have hvspan : v ∈ Submodule.span ℝ (Set.range (w · (t, x))) := by
      rw [hwspan (t, x) htxU]
      exact LinearMap.mem_ker.mpr hv
    obtain ⟨coeff, hcoeff⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ℝ).mp hvspan
    let z : (p : ℝ × M) → V p.2 := fun p ↦ ∑ i, coeff i • w i p
    have hzsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
        (fun p ↦ TotalSpace.mk' F p (z p) : ℝ × M →
          TotalSpace F (fun p : ℝ × M ↦ V p.2)) U := by
      refine ContMDiffOn.sum_section (V := fun p : ℝ × M ↦ V p.2)
        (s := Finset.univ) ?_
      intro i hi
      exact (hwsmooth i).const_smul_section
    have hzker : ∀ p ∈ U, A p.1 p.2 (z p) = 0 := by
      intro p hp
      change A p.1 p.2 (∑ i, coeff i • w i p) = 0
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i hi
      rw [map_smul]
      have hiKer : w i p ∈ (A p.1 p.2).ker := by
        rw [← hwspan p hp]
        exact Submodule.subset_span (Set.mem_range_self i)
      have hiZero := LinearMap.mem_ker.mp hiKer
      change A p.1 p.2 (w i p) = 0 at hiZero
      rw [hiZero, smul_zero]
    have hzpoint : z (t, x) = v := hcoeff
    have hmotion := kernel_motion_of_isCovariantlyInvariant
      (g t) (cov t) A (fun y ↦ (A t y).ker) (t := t)
      (hinvariant t ht) (fun _ ↦ rfl)
      (fun y u hu ↦ LinearMap.mem_ker.mp hu) z hU htxU hzsmooth
      hzker (hAt t ht x) (X t x) (reaction t x (A t x))
      (hevolution t ht x)
    simpa only [hzpoint] using hmotion.2
  refine ⟨hsmooth, hinvariant, hreaction, hderiv, ?_⟩
  intro t ht w U hU x htxU hw hwker
  apply kernel_motion_of_isCovariantlyInvariant
    (g t) (cov t) A (fun y ↦ (A t y).ker) (t := t)
      (hinvariant t ht) (fun _ ↦ rfl)
      (fun y v hv ↦ LinearMap.mem_ker.mp hv) w hU htxU hw hwker
      (hAt t ht x) (X t x) (reaction t x (A t x))
      (hevolution t ht x)

theorem kernel_time_constant_of_constant_range_rank
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ t, ContMDiffCovariantDerivative (cov t) ∞]
    (hcov : ∀ t, (cov t).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    {a b : ℝ}
    (hAspace : ContMDiffOnSpacetimeEndomorphism
      (I := I) (F := F) (V := V) (n := ∞)
      (fun t x ↦ A t x) (Ioo a b ×ˢ (Set.univ : Set M)))
    (hA_time : ∀ x, ContDiffOn ℝ 1 (fun t ↦ A t x) (Ioo a b))
    (q : ℕ) (hrange : ∀ t ∈ Ioo a b, ∀ x,
      Module.finrank ℝ (A t x).range = q)
    (hAsymm : ∀ t ∈ Ioo a b, ∀ x,
      ((A t x : V x →L[ℝ] V x) : V x →ₗ[ℝ] V x).IsSymmetric)
    (hApos : ∀ t ∈ Ioo a b, ∀ x, (A t x).IsPositive)
    (X : ℝ → (x : M) → TangentSpace I x)
    (reaction : ℝ → (x : M) →
      (V x →L[ℝ] V x) → V x →L[ℝ] V x)
    (hreactionNull : ∀ t x,
      satisfiesNullEigenvectorCondition (reaction t x))
    (hreactionAnn : ∀ t ∈ Ioo a b, ∀ x v, A t x v = 0 →
      reaction t x (A t x) v = 0)
    (hAt : ∀ t ∈ Ioo a b, ∀ x,
      DifferentiableAt ℝ (fun s ↦ A s x) t)
    (hevolution : ∀ t ∈ Ioo a b, ∀ x,
      deriv (fun s ↦ A s x) t =
        rawBundleEndomorphismConnLap (I := I) (g t) (cov t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y ↦ A t y) x (X t x) +
          reaction t x (A t x))
    {x : M} {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    (A s x).ker = (A t x).ker ∧ (A s x).range = (A t x).range := by
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y ↦
    VectorBundle.finiteDimensional ℝ F V y
  let k := Module.finrank ℝ F - q
  have hker : ∀ u ∈ Ioo a b, ∀ y,
      Module.finrank ℝ (A u y).ker = k := by
    intro u hu y
    let e := (trivializationAt F V y).linearEquivAt ℝ y
      (mem_baseSet_trivializationAt F V y)
    have hdim : Module.finrank ℝ (V y) = Module.finrank ℝ F :=
      e.finrank_eq
    have hsum := (A u y).toLinearMap.finrank_range_add_finrank_ker
    have hrank := hrange u hu y
    dsimp only [k]
    omega
  have hrigidity := kernel_rigidity_of_constant_range_rank
    (I := I) g cov hcov A hAspace q hrange hAsymm hApos X reaction
      hreactionNull hAt hevolution
  obtain ⟨-, -, -, hderiv, -⟩ := hrigidity
  let c : C^1⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯ := ContMDiffMap.snd
  let _ : TopologicalSpace (TotalSpace F (fun p : ℝ × M ↦ V p.2)) := by
    change TopologicalSpace (TotalSpace F (c *ᵖ V)); infer_instance
  let _ : FiberBundle F (fun p : ℝ × M ↦ V p.2) := by
    change FiberBundle F (c *ᵖ V); infer_instance
  let _ : VectorBundle ℝ F (fun p : ℝ × M ↦ V p.2) := by
    change VectorBundle ℝ F (c *ᵖ V); infer_instance
  let _ : ContMDiffVectorBundle 1 F (fun p : ℝ × M ↦ V p.2)
      (𝓘(ℝ, ℝ).prod I) := by
    change ContMDiffVectorBundle 1 F (c *ᵖ V) (𝓘(ℝ, ℝ).prod I)
    infer_instance
  have hAspace1 : ContMDiffOnSpacetimeEndomorphism
      (I := I) (F := F) (V := V) (n := 1)
      (fun u y ↦ A u y) (Ioo a b ×ˢ (Set.univ : Set M)) :=
    hAspace.of_le (by norm_num)
  apply ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_contMDiffOn_constant_finrank_deriv_annihilation
    (I := I) (F := F) (V := V) (A := fun u y ↦ A u y)
      hAspace1 hA_time k hker
  · intro u hu y v hv
    have hvzero : A u y v = 0 := LinearMap.mem_ker.mp hv
    rw [hderiv u hu y v hvzero, hreactionAnn u hu y v hvzero]
  · exact hAsymm
  · exact hs
  · exact ht

end PositiveSystem
