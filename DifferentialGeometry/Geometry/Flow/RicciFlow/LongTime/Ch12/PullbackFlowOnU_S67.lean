import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrBridge_S57
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Manifold.ImmersionRange

set_option autoImplicit false

/-!
# CH12-S67 / G1: the pulled-back Ricci flow on `↥U`

Given a Ricci flow `S` (`IsSolutionOn`) on a 3-manifold `N`, a smooth map `f : H.Carrier → N` which is
a smooth embedding on an open `U` (hypothesis shape of `hLTF04`), the family
`r ↦ (f|_U)^* (S r)` is a Ricci flow on the manifold `↥U` (`exists_solutionOn_pullbackRestrict_S67`).
Route: `f|_U : U → N` is a smooth embedding between 3-manifolds, so its range `V` is open
(`Manifold.isOpen_range_of_isSmoothEmbedding`) and `U ≃ₘ V`; then
`solutionOnRestrictOpen S V` + `solutionOnPullback` (tree API) + `isSolutionOn_pullback`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

section FlowOnU

variable (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]

omit [IsManifold (𝓡 3) ∞ N] in
/-- a smooth embedding of the open set `U` into a 3-manifold has open range. -/
theorem isOpen_range_restrict_S67 (f : H.Carrier → N) (U : Opens H.Carrier)
    (hemb : Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x)) :
    IsOpen (Set.range (fun x : U => f x)) :=
  Manifold.isOpen_range_of_isSmoothEmbedding (I := 𝓡 3) (J := 𝓡 3) rfl hemb

/-- `f|_U` is a diffeomorphism onto an open subset `V` of `N`. -/
theorem exists_diffeo_onto_open_S67 (f : H.Carrier → N) (U : Opens H.Carrier)
    (hemb : Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x)) :
    ∃ (V : Opens N) (Φ : Diffeomorph (𝓡 3) (𝓡 3) U V ∞), ∀ x : U, ((Φ x : V) : N) = f x := by
  let V : Opens N := ⟨Set.range (fun x : U => f x), isOpen_range_restrict_S67 H f U hemb⟩
  let f' : U → V := fun x => ⟨f x, x, rfl⟩
  have hf' : Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ f' :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen (𝓡 3) (𝓡 3) V f' hemb
  have hsurj : Function.Surjective f' := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  exact ⟨V, hf'.diffeomorphOfSurjective hsurj, fun x => rfl⟩

/-- injectivity of the differential of `f` on `U`, from the embedding hypothesis. -/
theorem injective_mfderiv_of_embedding_S67 (f : H.Carrier → N) (U : Opens H.Carrier)
    (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hemb : Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x)) :
    ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y) := by
  intro y hy v w hvw
  have h0 := hemb.isImmersion.mfderiv_injective (by simp) (⟨y, hy⟩ : U)
  apply h0
  exact (mfderiv_comp_val_C4 f U hF ⟨y, hy⟩ v).trans
    (hvw.trans (mfderiv_comp_val_C4 f U hF ⟨y, hy⟩ w).symm)

section Main

variable [T2Space N] [SigmaCompactSpace N]

/-- **G1 (flow on `↥U`).**  The pull-back family `r ↦ (f|_U)^* (S r)` of a Ricci flow `S` on `N`
along a smooth embedding `f|_U : ↥U → N` is a Ricci flow on `↥U`. -/
theorem exists_solutionOn_pullbackRestrict_S67 {D : RealTimeInterval}
    (S : SolutionOn (I := 𝓡 3) (M := N) D) (hS : IsSolutionOn (I := 𝓡 3) S)
    (f : H.Carrier → N) (U : Opens H.Carrier) (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hemb : Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x)) :
    ∃ S' : SolutionOn (I := 𝓡 3) (M := U) D, IsSolutionOn (I := 𝓡 3) S' ∧
      ∀ r : ℝ, S'.base.metric r = pullbackRestrict_S57 H (S.base.metric r) f U hF
        (injective_mfderiv_of_embedding_S67 H f U hF hemb) := by
  obtain ⟨V, Φ, hΦ⟩ := exists_diffeo_onto_open_S67 H f U hemb
  have : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) V.isOpen)
  have : SigmaCompactSpace U := Φ.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  let S1 := solutionOnRestrictOpen (I := 𝓡 3) S V
  refine ⟨solutionOnPullback (I := 𝓡 3) S1 Φ,
    isSolutionOn_pullback (I := 𝓡 3) S1 (isSolutionOn_restrictOpen (I := 𝓡 3) S hS V) Φ, ?_⟩
  intro r
  ext x v w
  have hinf : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hfun : (fun z : U => f z) = (Subtype.val : V → N) ∘ (Φ : U → V) :=
    funext fun z => (hΦ z).symm
  have hd : ∀ u : TangentSpace (𝓡 3) x,
      mfderiv (𝓡 3) (𝓡 3) (fun z : U => f z) x u =
        mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → N) (Φ x) (mfderiv (𝓡 3) (𝓡 3) (Φ : U → V) x u) := by
    intro u
    rw [hfun]
    exact mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) x
      ((contMDiff_subtype_val (I := 𝓡 3) (U := V)).mdifferentiableAt hinf)
      (Φ.contMDiff.mdifferentiableAt hinf) (v := u)
  change (Diffeomorph.pullbackMetric (I := 𝓡 3) ((S.base.metric r).restrictOpen V) Φ).inner x v w = _
  rw [Diffeomorph.pullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
    pullbackRestrict_S57, SmoothRiemannianMetric.pullbackOfImmersion_inner, hd v, hd w]
  have hx : ((Φ x : V) : N) = f x := hΦ x
  have key : ∀ y y' : N, y = y' → ∀ a b : EuclideanSpace ℝ (Fin 3),
      (S.base.metric r).inner y a b = (S.base.metric r).inner y' a b := by
    rintro y y' rfl a b
    rfl
  rw [DifferentialGeometry.mfderiv_subtype_val_apply (I := 𝓡 3) V (Φ x)
      (mfderiv (𝓡 3) (𝓡 3) (Φ : U → V) x v),
    DifferentialGeometry.mfderiv_subtype_val_apply (I := 𝓡 3) V (Φ x)
      (mfderiv (𝓡 3) (𝓡 3) (Φ : U → V) x w)]
  exact key _ _ hx _ _

end Main

end FlowOnU

end GC.LongTime.Ch12
