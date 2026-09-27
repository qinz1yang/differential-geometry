import DifferentialGeometry.Geometry.MinimalSurface.Width.SmoothRepresentatives
import DifferentialGeometry.Geometry.Measure.Area.LeastAreaComposition








noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [CompactSpace M] [T3Space M] [Nonempty M] [PreconnectedSpace M]
  [CompactSpace N] [T3Space N] [Nonempty N] [PreconnectedSpace N]
  {n m : ℕ}




theorem exists_regularized_composed_family
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (h : SmoothRiemannianMetric 𝓘(ℝ, F) N)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (a : N → EuclideanSpace ℝ (Fin m))
    (ha : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ a)
    (hamb : _root_.Topology.IsEmbedding a)
    (f : M → N) {L : ℝ≥0}
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (ξ : loopFamilyClass M)
    (Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top)))
    (hΓ : Γ ∈ regularFamilyRepresentatives e (he.of_le (by exact_mod_cast le_top)) hemb ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : regularSphereFamily a (ha.of_le (by exact_mod_cast le_top)))
      (hs : ∀ k, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ∞ (fun t : ℝ => (S k).val.val (t : loopCircle))),
      S ∈ regularFamilyRepresentatives a (ha.of_le (by exact_mod_cast le_top)) hamb
        (LoopFamily.postcompose ⟨f, continuous_of_riemannian_map_lipschitz g h hf⟩ ξ) ∧
      (∀ k, regularLeastArea h (S k) ≤ (L : ℝ) ^ 2 * regularLeastArea g (Γ k) + ε) ∧
      (∀ (d : ℕ) (b : N → EuclideanSpace ℝ (Fin d))
        (hb : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ b) (j : ℕ),
        Continuous[inferInstance, finiteRegularLoopTopology b hb j]
          (fun k => (⟨(S k).val.val, (hs k).of_le (by exact_mod_cast le_top)⟩ :
            finiteRegularLoop j F N))) := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  let ha₁ := ha.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he₁
  let : TopologicalSpace (regularContractibleLoop F N) := regularContractibleLoopTopology a ha₁
  let fc : C(M, N) := ⟨f, continuous_of_riemannian_map_lipschitz g h hf⟩
  obtain ⟨V, hV⟩ := exists_regular_family_lipschitz_bound g e he hemb hi
    (fun k => (Γ k).val) ((continuous_regularContractibleLoop_iff e he₁ Γ).mp Γ.continuous)
  let Γ₀ := (ContractibleLoop.postcompose fc).comp (regularSphereFamilyInclusion e he₁ hemb Γ)
  have hV₀ : ∀ k θ η, riemannianEDistOf h ((Γ₀ k).val θ) ((Γ₀ k).val η) ≤
      ((L * V : ℝ≥0) : ℝ≥0∞) * edist θ η :=
    fun k => riemannian_lipschitz_comp g h (hV k) hf
  obtain ⟨S, hs, H, hCr, harea, _⟩ := exists_smooth_family_leastArea_approximation h a ha hamb
    Γ₀ (L * V) hV₀ hε
  refine ⟨S, hs, ?_, ?_, hCr⟩
  · change LoopFamily.classOf (regularSphereFamilyInclusion a ha₁ hamb S) =
      LoopFamily.postcompose fc ξ
    have hc : LoopFamily.classOf Γ₀ = LoopFamily.postcompose fc ξ := by
      rw [← hΓ]
      rfl
    exact ((LoopFamily.classOf_eq_iff _ _).mpr ⟨H.symm⟩).trans hc
  · intro k
    have heq : (⟨Γ₀ k, L * V, hV₀ k⟩ : lipschitzContractibleLoop h) =
        postcomposeLipschitzContractibleLoop g h f hf (regularContractibleToLipschitz g (Γ k)) := by
      apply Subtype.ext
      rfl
    have ha := (abs_lt.mp (harea k)).2
    rw [heq] at ha
    have hb := leastSpanningArea_postcompose_le g h f hf (regularContractibleToLipschitz g (Γ k))
    change _ ≤ (L : ℝ) ^ 2 * regularLeastArea g (Γ k) at hb
    linarith



theorem classWidth_postcompose_le_familyMaximum
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (h : SmoothRiemannianMetric 𝓘(ℝ, F) N)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (a : N → EuclideanSpace ℝ (Fin m))
    (ha : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ a)
    (hamb : _root_.Topology.IsEmbedding a)
    (hai : ∀ p, Injective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) a p))
    (f : M → N) {L : ℝ≥0}
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (ξ : loopFamilyClass M)
    (Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top)))
    (hΓ : Γ ∈ regularFamilyRepresentatives e (he.of_le (by exact_mod_cast le_top)) hemb ξ) :
    classWidth h a (ha.of_le (by exact_mod_cast le_top)) hamb
      (LoopFamily.postcompose ⟨f, continuous_of_riemannian_map_lipschitz g h hf⟩ ξ) ≤
      (L : ℝ) ^ 2 * regularFamilyMaximum g e (he.of_le (by exact_mod_cast le_top)) Γ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨S, _, hS, harea, _⟩ := exists_regularized_composed_family
    g h e he hemb hi a ha hamb f hf ξ Γ hΓ hε
  obtain ⟨k, hk⟩ := regularFamilyMaximum_attained h a ha hamb hai S
  have hW := classWidth_le_familyMaximum h a ha hamb hai _ hS
  have hB := mul_le_mul_of_nonneg_left (regularLeastArea_le_familyMaximum g e he hemb hi Γ k)
    (sq_nonneg (L : ℝ))
  linarith [harea k]



theorem classWidth_postcompose_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (h : SmoothRiemannianMetric 𝓘(ℝ, F) N)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (a : N → EuclideanSpace ℝ (Fin m))
    (ha : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ a)
    (hamb : _root_.Topology.IsEmbedding a)
    (hai : ∀ p, Injective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) a p))
    (f : M → N) {L : ℝ≥0}
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (ξ : loopFamilyClass M) :
    classWidth h a (ha.of_le (by exact_mod_cast le_top)) hamb
      (LoopFamily.postcompose ⟨f, continuous_of_riemannian_map_lipschitz g h hf⟩ ξ) ≤
      (L : ℝ) ^ 2 * classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < (L : ℝ) ^ 2 + 1 := by positivity
  obtain ⟨Γ, hΓ, hmax⟩ := exists_regularFamily_maximum_lt g e he hemb ξ (div_pos hε hden)
  have hbound := classWidth_postcompose_le_familyMaximum g h e he hemb hi a ha hamb hai f hf ξ Γ hΓ
  have hb := mul_le_mul_of_nonneg_left hmax.le (sq_nonneg (L : ℝ))
  have hc : (L : ℝ) ^ 2 * (ε / ((L : ℝ) ^ 2 + 1)) ≤ ε := by
    calc
      _ ≤ ((L : ℝ) ^ 2 + 1) * (ε / ((L : ℝ) ^ 2 + 1)) := by gcongr; linarith
      _ = ε := mul_div_cancel₀ ε hden.ne'
  linarith

end DifferentialGeometry.Geometry
