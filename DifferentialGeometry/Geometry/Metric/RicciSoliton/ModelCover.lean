import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized
import DifferentialGeometry.Geometry.Metric.LocalPullback
import DifferentialGeometry.Geometry.Metric.PullbackCross
import DifferentialGeometry.Topology.Covering.DeckDiffeomorph
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
    IsLocalDiffeomorph J I ∞ cover ∧
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
  hπ.2.2.1.contMDiff

theorem solitonModelCovering_isLocalDiffeomorph
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) :
    IsLocalDiffeomorph J I ∞ cover :=
  hπ.2.2.1

theorem solitonModelCovering_surjective
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) :
    Function.Surjective cover :=
  hπ.2.2.2.1

theorem compactSpace_of_solitonModelCovering
    [CompactSpace N]
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) :
    CompactSpace M := by
  rw [← isCompact_univ_iff]
  rw [← Set.range_eq_univ.mpr (solitonModelCovering_surjective hπ)]
  exact isCompact_range (solitonModelCovering_contMDiff hπ).continuous

theorem solitonModelCovering_tangent_finrank_eq
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) (x : N) :
    Module.finrank Real (TangentSpace J x) =
      Module.finrank Real (TangentSpace I (cover x)) :=
  ((solitonModelCovering_isLocalDiffeomorph hπ).mfderivToContinuousLinearEquiv
    (by simp) x).toLinearEquiv.finrank_eq

theorem solitonModelCovering_target_tangent_finrank_eq
    {n : Nat}
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover)
    (hdim : Module.finrank Real F = n) (y : M) :
    Module.finrank Real (TangentSpace I y) = n := by
  obtain ⟨x, rfl⟩ := solitonModelCovering_surjective hπ y
  rw [← solitonModelCovering_tangent_finrank_eq hπ x]
  change Module.finrank Real F = n
  exact hdim

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

theorem solitonModelCovering_metric_eq_localPull
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) :
    h = localPullMetric g cover (solitonModelCovering_isLocalDiffeomorph hπ) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner]
  exact solitonModelCovering_metric hπ x v w

theorem solitonModelCovering_deck_preserves
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover)
    (γ : N ≃ₘ⟮J, J⟯ N)
    (hγ : ∀ x, cover (γ x) = cover x) :
    Diffeomorph.pullbackMetricCross h γ = h ∧
      Fpot.comp γ.toContMDiffMap = Fpot := by
  have hcomp : cover ∘ (γ : N → N) = cover := by
    funext x
    exact hγ x
  have hderiv (x : N) :
      mfderiv J I cover (γ x) ∘L mfderiv J J (γ : N → N) x =
        mfderiv J I cover x := by
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
      h.inner (γ x) (mfderiv J J (γ : N → N) x v)
          (mfderiv J J (γ : N → N) x w) =
          g.inner (cover (γ x))
            (mfderiv J I cover (γ x) (mfderiv J J (γ : N → N) x v))
            (mfderiv J I cover (γ x) (mfderiv J J (γ : N → N) x w)) :=
        solitonModelCovering_metric hπ (γ x) _ _
      _ = g.inner (cover x) (mfderiv J I cover x v)
            (mfderiv J I cover x w) := by
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

theorem solitonModelCovering_deckGroup_preserves
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover)
    (gamma : coveringDeckGroup cover) :
    Diffeomorph.pullbackMetricCross h
        (coveringDeckGroupDiffeomorph
          (solitonModelCovering_isLocalDiffeomorph hπ) gamma) = h ∧
      Fpot.comp
        (coveringDeckGroupDiffeomorph
          (solitonModelCovering_isLocalDiffeomorph hπ) gamma).toContMDiffMap = Fpot :=
  solitonModelCovering_deck_preserves hπ
    (coveringDeckGroupDiffeomorph
      (solitonModelCovering_isLocalDiffeomorph hπ) gamma)
    (coveringDeckGroup_map gamma)

theorem solitonModelCovering_deckGroup_potential
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover)
    (gamma : coveringDeckGroup cover) (x : N) :
    Fpot (gamma • x) = Fpot x := by
  rw [solitonModelCovering_potential hπ,
    coveringDeckGroup_map gamma,
    solitonModelCovering_potential hπ]

theorem solitonModelCovering_deckGroup_isQuotientCoveringMap
    [SimplyConnectedSpace N] [LocallyPathConnectedSpace N]
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) :
    IsQuotientCoveringMap cover (coveringDeckGroup cover) :=
  isQuotientCoveringMap_coveringDeckGroup
    (solitonModelCovering_isCoveringMap hπ)
    (solitonModelCovering_surjective hπ)

theorem solitonModelCovering_deckGroup_properlyDiscontinuousSMul
    [SimplyConnectedSpace N] [LocallyPathConnectedSpace N]
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) :
    ProperlyDiscontinuousSMul (coveringDeckGroup cover) N :=
  coveringDeckGroup_properlyDiscontinuousSMul
    (solitonModelCovering_isCoveringMap hπ)
    (solitonModelCovering_surjective hπ)

noncomputable def solitonModelCoveringDeckQuotientHomeomorph
    [SimplyConnectedSpace N] [LocallyPathConnectedSpace N]
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) :
    MulAction.orbitRel.Quotient (coveringDeckGroup cover) N ≃ₜ M :=
  coveringDeckGroupQuotientHomeomorph
    (solitonModelCovering_isCoveringMap hπ)
    (solitonModelCovering_surjective hπ)

theorem solitonModelCoveringDeckQuotientHomeomorph_apply
    [SimplyConnectedSpace N] [LocallyPathConnectedSpace N]
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) (x : N) :
    solitonModelCoveringDeckQuotientHomeomorph hπ (Quotient.mk'' x) = cover x :=
  coveringDeckGroupQuotientHomeomorph_apply
    (solitonModelCovering_isCoveringMap hπ)
    (solitonModelCovering_surjective hπ) x

noncomputable def solitonModelCoveringDeckQuotientPotential
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) :
    MulAction.orbitRel.Quotient (coveringDeckGroup cover) N → Real :=
  Quotient.lift Fpot (fun x y hxy => by
    rcases hxy with ⟨gamma, rfl⟩
    exact solitonModelCovering_deckGroup_potential hπ gamma y)

theorem solitonModelCoveringDeckQuotientPotential_apply
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) (x : N) :
    solitonModelCoveringDeckQuotientPotential hπ (Quotient.mk'' x) = Fpot x :=
  rfl

theorem solitonModelCoveringDeckQuotientPotential_continuous
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) :
    Continuous (solitonModelCoveringDeckQuotientPotential hπ) := by
  exact Fpot.contMDiff.continuous.quotient_lift (fun x y hxy => by
    rcases hxy with ⟨gamma, rfl⟩
    exact solitonModelCovering_deckGroup_potential hπ gamma y)

theorem solitonModelCoveringDeckQuotientPotential_eq_target
    [SimplyConnectedSpace N] [LocallyPathConnectedSpace N]
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover)
    (q : MulAction.orbitRel.Quotient (coveringDeckGroup cover) N) :
    solitonModelCoveringDeckQuotientPotential hπ q =
      f (solitonModelCoveringDeckQuotientHomeomorph hπ q) := by
  induction q using Quotient.inductionOn with
  | _ x =>
    rw [solitonModelCoveringDeckQuotientPotential_apply,
      solitonModelCoveringDeckQuotientHomeomorph_apply,
      solitonModelCovering_potential hπ]

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
  refine ⟨h, h, (Diffeomorph.refl I M ∞).isLocalDiffeomorph,
    Function.surjective_id, identity_isCoveringMap, ?_, ?_⟩
  · intro x v w
    rw [mfderiv_id]
    simp
  · intro x
    rfl

end DifferentialGeometry.Geometry
