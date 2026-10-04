import DifferentialGeometry.Topology.Manifold.SmoothCarrier.Metric

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Topology.Manifold

theorem SmoothCarrier.exists_pullback_metric_of_chartAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [MetricSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) 1 X]
    {ι : Type*} (A : SmoothCompatibleAtlas E X ι) (K s r : ℕ)
    (hrK : r ≤ K) (hrs : r + 1 ≤ s)
    (hA : A.IsCompatible (chartAt E : X → OpenPartialHomeomorph X E) s)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) (K : ℕ∞ω) E
      (TangentSpace 𝓘(ℝ, E) : X → Type _)) :
    ∃ G' : ContMDiffRiemannianMetric 𝓘(ℝ, E) (r : ℕ∞ω) E
        (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _),
      (∀ (x : SmoothCarrier A) (v w : E),
        G'.inner x v w = G.inner (SmoothCarrier.toBase A x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x w)) ∧
      (letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) := ⟨G.toRiemannianMetric⟩
       letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _) :=
         ⟨G'.toRiemannianMetric⟩
       (∀ (x : SmoothCarrier A) (v : TangentSpace 𝓘(ℝ, E) x),
          ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v‖ₑ = ‖v‖ₑ) ∧
       (∀ (y : X) (w : TangentSpace 𝓘(ℝ, E) y),
          ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y w‖ₑ = ‖w‖ₑ) ∧
       (∀ (γ : ℝ → SmoothCarrier A) (a b : ℝ),
          (∀ᵐ t ∂volume.restrict (Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) →
          pathELength 𝓘(ℝ, E) (SmoothCarrier.toBase A ∘ γ) a b =
            pathELength 𝓘(ℝ, E) γ a b) ∧
       (∀ (γ : ℝ → X) (a b : ℝ),
          (∀ᵐ t ∂volume.restrict (Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) →
          pathELength 𝓘(ℝ, E) (SmoothCarrier.ofBase A ∘ γ) a b =
            pathELength 𝓘(ℝ, E) γ a b) ∧
       (∀ x y : SmoothCarrier A, riemannianEDist 𝓘(ℝ, E) x y =
          riemannianEDist 𝓘(ℝ, E) (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y)) ∧
       (∀ x y : SmoothCarrier A,
          dist x y = dist (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y)) ∧
       (IsRiemannianManifold 𝓘(ℝ, E) X → IsRiemannianManifold 𝓘(ℝ, E) (SmoothCarrier A))) := by
  have hCs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) s (SmoothCarrier.toBase A) :=
    SmoothCarrier.contMDiff_toBase_of_chartAt A (chartAt E) (fun y => mem_range_self y) hA
  have hCs' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) s (SmoothCarrier.ofBase A) :=
    SmoothCarrier.contMDiff_ofBase_of_chartAt A (chartAt E) (fun y => mem_range_self y) hA
  let f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier A) X s :=
    ⟨SmoothCarrier.equivBase A,
      by simpa only [SmoothCarrier.coe_equivBase] using hCs,
      by simpa only [SmoothCarrier.coe_equivBase_symm] using hCs'⟩
  have hf : ⇑f = SmoothCarrier.toBase A := rfl
  obtain ⟨G', hG'⟩ :=
    DifferentialGeometry.Geometry.exists_finite_order_pullback_metric_of_diffeomorph
      K s r hrK hrs G f
  have hG'' : ∀ (x : SmoothCarrier A) (v w : E),
      G'.inner x v w = G.inner (SmoothCarrier.toBase A x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x w) := by
    intro x v w
    have h := hG' x v w
    rw [hf] at h
    exact h
  refine ⟨G', hG'', ?_⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) := ⟨G.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _) :=
    ⟨G'.toRiemannianMetric⟩
  have hs1 : (1 : ℕ∞ω) ≤ (s : ℕ∞ω) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le r)).trans hrs
  have hC1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (SmoothCarrier.toBase A) := hCs.of_le hs1
  have hC1' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (SmoothCarrier.ofBase A) := hCs'.of_le hs1
  have hd1 : ∀ x : SmoothCarrier A,
      MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x :=
    fun x => (hC1 x).mdifferentiableAt one_ne_zero
  have hd2 : ∀ y : X, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y :=
    fun y => (hC1' y).mdifferentiableAt one_ne_zero
  have hcomp : ∀ (y : X) (w : TangentSpace 𝓘(ℝ, E) y),
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) (SmoothCarrier.ofBase A y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y w) = w := by
    intro y w
    have heq :
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) (SmoothCarrier.ofBase A y)).comp
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y) =
            ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) y) := by
      rw [← mfderiv_comp y (hd1 (SmoothCarrier.ofBase A y)) (hd2 y),
        SmoothCarrier.toBase_comp_ofBase]
      exact mfderiv_id
    exact DFunLike.congr_fun heq w
  have hiso : ∀ (x : SmoothCarrier A) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v‖ₑ = ‖v‖ₑ :=
    enorm_mfderiv_eq_of_pullback G G' (SmoothCarrier.toBase A) hG''
  have hiso' : ∀ (y : X) (w : TangentSpace 𝓘(ℝ, E) y),
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y w‖ₑ = ‖w‖ₑ :=
    enorm_mfderiv_inverse_eq_of_pullback G G' (SmoothCarrier.toBase A) (SmoothCarrier.ofBase A)
      hG'' (SmoothCarrier.toBase_ofBase A) hcomp
  have hedist : ∀ x y : SmoothCarrier A, riemannianEDist 𝓘(ℝ, E) x y =
      riemannianEDist 𝓘(ℝ, E) (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y) := by
    intro x y
    have hle := riemannianEDist_comp_le (SmoothCarrier.ofBase A) hC1' hiso'
      (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y)
    rw [SmoothCarrier.ofBase_toBase, SmoothCarrier.ofBase_toBase] at hle
    exact le_antisymm hle (riemannianEDist_comp_le (SmoothCarrier.toBase A) hC1 hiso x y)
  refine ⟨hiso, hiso', fun γ a b hγ => pathELength_comp_eq_of_isometry _ hd1 hiso γ a b hγ,
    fun γ a b hγ => pathELength_comp_eq_of_isometry _ hd2 hiso' γ a b hγ, hedist,
    fun x y => (SmoothCarrier.dist_toBase A x y).symm, fun hX => ⟨fun x y => ?_⟩⟩
  exact (SmoothCarrier.edist_toBase A x y).symm.trans
    ((IsRiemannianManifold.out (I := 𝓘(ℝ, E)) (self := hX) (SmoothCarrier.toBase A x)
      (SmoothCarrier.toBase A y)).trans (hedist x y).symm)

end DifferentialGeometry.Topology.Manifold
