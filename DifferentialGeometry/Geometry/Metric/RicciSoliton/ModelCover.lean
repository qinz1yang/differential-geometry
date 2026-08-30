import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized
import DifferentialGeometry.Geometry.Metric.PullbackCross
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G} [J.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [SigmaCompactSpace N] [T2Space N]

def solitonModelCovering
    (h : SmoothRiemannianMetric J N) (Fpot : C^∞⟮J, N; Real⟯)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (cover : N → M) : Prop :=
  normalizedGradientRicciSoliton (I := J) h Fpot ∧
    normalizedGradientRicciSoliton (I := I) g f ∧
    ContMDiff J I ∞ cover ∧
    Function.Surjective cover ∧
    IsCoveringMap cover ∧
    (∀ x v w,
      h.inner x v w =
        g.inner (cover x) (mfderiv J I cover x v) (mfderiv J I cover x w)) ∧
    (∀ x, Fpot x = f (cover x))

theorem solitonModelCovering_source
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) :
    normalizedGradientRicciSoliton (I := J) h Fpot :=
  hπ.1

theorem solitonModelCovering_target
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) :
    normalizedGradientRicciSoliton (I := I) g f :=
  hπ.2.1

theorem solitonModelCovering_contMDiff
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) :
    ContMDiff J I ∞ cover :=
  hπ.2.2.1

theorem solitonModelCovering_surjective
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) :
    Function.Surjective cover :=
  hπ.2.2.2.1

theorem solitonModelCovering_isCoveringMap
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) :
    IsCoveringMap cover :=
  hπ.2.2.2.2.1

theorem solitonModelCovering_metric
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) (x : N)
    (v w : TangentSpace J x) :
    h.inner x v w =
      g.inner (cover x) (mfderiv J I cover x v) (mfderiv J I cover x w) :=
  hπ.2.2.2.2.2.1 x v w

theorem solitonModelCovering_potential
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) (x : N) :
    Fpot x = f (cover x) :=
  hπ.2.2.2.2.2.2 x

theorem solitonModelCovering_deck_preserves
    {h : SmoothRiemannianMetric I M} {Fpot : C^∞⟮I, M; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : M → M}
    (hπ : solitonModelCovering h Fpot g f cover)
    (γ : M ≃ₘ⟮I, I⟯ M)
    (hγ : ∀ x, cover (γ x) = cover x) :
    Diffeomorph.pullbackMetricCross h γ = h ∧
      Fpot.comp γ.toContMDiffMap = Fpot := by
  have hcomp : cover ∘ (γ : M → M) = cover := by
    funext x
    exact hγ x
  have hderiv (x : M) :
      mfderiv I I cover (γ x) ∘L mfderiv I I (γ : M → M) x =
        mfderiv I I cover x := by
    have h' := mfderiv_comp x
      ((solitonModelCovering_contMDiff hπ).mdifferentiableAt (by simp))
      (γ.contMDiff.mdifferentiableAt (by simp))
    rw [hcomp] at h'
    exact h'.symm
  constructor
  · apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    calc
      h.inner (γ x) (mfderiv I I (γ : M → M) x v)
          (mfderiv I I (γ : M → M) x w) =
          g.inner (cover (γ x))
            (mfderiv I I cover (γ x) (mfderiv I I (γ : M → M) x v))
            (mfderiv I I cover (γ x) (mfderiv I I (γ : M → M) x w)) :=
        solitonModelCovering_metric hπ (γ x) _ _
      _ = g.inner (cover x) (mfderiv I I cover x v)
            (mfderiv I I cover x w) := by
        have hv := congrArg (fun L => L v) (hderiv x)
        have hw := congrArg (fun L => L w) (hderiv x)
        simp only [ContinuousLinearMap.comp_apply] at hv hw
        rw [hv, hw, hγ x]
      _ = h.inner x v w := (solitonModelCovering_metric hπ x v w).symm
  · apply ContMDiffMap.ext
    intro x
    change Fpot (γ x) = Fpot x
    rw [solitonModelCovering_potential hπ (γ x), hγ x,
      solitonModelCovering_potential hπ x]

private noncomputable def identityTrivialization :
    Trivialization Unit (id : M → M) :=
  { toOpenPartialHomeomorph := (Homeomorph.prodUnique M Unit).symm.toOpenPartialHomeomorph
    baseSet := Set.univ
    open_baseSet := isOpen_univ
    source_eq := by simp
    target_eq := by simp
    proj_toFun := by intro p hp; rfl }

omit [SigmaCompactSpace M] [T2Space M] in
private theorem identity_isCoveringMap :
    IsCoveringMap (id : M → M) := by
  refine IsCoveringMap.mk (f := (id : M → M)) (fun _ : M => Unit)
    (fun _ => identityTrivialization (M := M)) ?_
  intro x
  exact Set.mem_univ x

theorem solitonModelCovering_refl
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) :
    solitonModelCovering (I := I) g f g f (id : M → M) := by
  refine ⟨h, h, contMDiff_id, Function.surjective_id, identity_isCoveringMap, ?_, ?_⟩
  · intro x v w
    rw [mfderiv_id]
    simp
  · intro x
    rfl

end DifferentialGeometry.Geometry
