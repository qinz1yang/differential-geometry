import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrNaturalitySource_O19
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThreeMetric_S76
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InverseLift_S76
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# CH12-S86 G2b (part 1): small lemmas for the S7 v3 assembly

* `isSmoothEmbedding_restrict_open_S86` : restricting a smooth embedding on `U` to an open `V ⊆ U`;
* `injective_mfderiv_of_embedding_S86` : injective differential from the embedding hypothesis;
* `restrictOpen_eq_pullback_val_S86` : `g|_W = (val)^* g`;
* `pullbackOfImmersion_eq_cross_S86` : `G = F ∘ e` ⇒ `G^* g = e^*(F^* g)`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness TopologicalSpace Set Manifold
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- Restriction of a smooth embedding on `U` to an open `V ⊆ U`. -/
theorem isSmoothEmbedding_restrict_open_S86 {M N : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (f : M → N) (U V : Opens M) (hVU : V ≤ U)
    (hf : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x)) :
    IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : V => f x) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  let i : V → U := fun x => ⟨x, hVU x.2⟩
  have hi : ContMDiff (𝓡 3) (𝓡 3) ∞ i := by
    have : i = Set.inclusion hVU := rfl
    rw [this]
    exact contMDiff_inclusion hVU
  have hval : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ (id : V → V)) :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen (𝓡 3) (𝓡 3) V id
      IsSmoothEmbedding.id
  have hiemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ i :=
    IsSmoothEmbedding.of_comp (g := (Subtype.val : U → M)) (f := i) hval hn hi
      contMDiff_subtype_val
  exact (IsSmoothEmbedding.comp (g := fun x : U => f x) (f := i) hf hiemb hn :)

/-- Injective differential of `f` on `U` from the embedding hypothesis. -/
theorem injective_mfderiv_of_embedding_S86 {M N : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (f : M → N) (U : Opens M) (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x)) :
    ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y) := by
  intro y hy v w hvw
  have h0 := hemb.isImmersion.mfderiv_injective (by simp) (⟨y, hy⟩ : U)
  apply h0
  exact (mfderiv_comp_val_C4 f U hF ⟨y, hy⟩ v).trans
    (hvw.trans (mfderiv_comp_val_C4 f U hF ⟨y, hy⟩ w).symm)

/-- `g|_W = (val)^* g`. -/
theorem restrictOpen_eq_pullback_val_S86 {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] (g : SmoothRiemannianMetric (𝓡 3) M) (W : Opens M) :
    g.restrictOpen W = g.pullbackOfImmersion (I := 𝓡 3) (Subtype.val : W → M)
      contMDiff_subtype_val
      (fun x v w hvw => by
        rwa [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply] at hvw) := by
  ext y v w
  change g.inner (y : M) v w = localPullInner (I := 𝓡 3) (J := 𝓡 3) g (Subtype.val : W → M) y v w
  rw [localPullInner_apply, mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]

/-- **Pullback naturality.** If `G = F ∘ e` for a diffeomorphism `e`, then `G^* g = e^*(F^* g)`. -/
theorem pullbackOfImmersion_eq_cross_S86 {P Q N : Type u}
    [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P] [IsManifold (𝓡 3) ∞ P]
    [T2Space P]
    [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] [IsManifold (𝓡 3) ∞ Q]
    [T2Space Q]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (gN : SmoothRiemannianMetric (𝓡 3) N) (e : Diffeomorph (𝓡 3) (𝓡 3) P Q ∞)
    (G : P → N) (F : Q → N) (hG : ContMDiff (𝓡 3) (𝓡 3) ∞ G)
    (hGinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 3) G x))
    (hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F)
    (hFinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 3) F x))
    (hGF : ∀ x, F (e x) = G x) :
    gN.pullbackOfImmersion (I := 𝓡 3) G hG hGinj =
      Diffeomorph.pullbackMetricCross (I := 𝓡 3) (J := 𝓡 3)
        (gN.pullbackOfImmersion (I := 𝓡 3) F hF hFinj) e := by
  have hinf : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hG' : G = F ∘ e := funext fun x => (hGF x).symm
  subst hG'
  ext x v w
  rw [SmoothRiemannianMetric.pullbackOfImmersion_inner,
    Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.pullbackOfImmersion_inner]
  rw [mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) x
      ((hF (e x)).mdifferentiableAt hinf) ((e.contMDiff x).mdifferentiableAt hinf) (v := v),
    mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) x
      ((hF (e x)).mdifferentiableAt hinf) ((e.contMDiff x).mdifferentiableAt hinf) (v := w)]
  rfl

end GC.LongTime.Ch12
