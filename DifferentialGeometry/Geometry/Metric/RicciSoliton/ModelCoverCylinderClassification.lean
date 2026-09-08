import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverRoundThreeCylinder
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverCylinderQuotient
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph
import DifferentialGeometry.Topology.Covering.QuotientDiffeomorph

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners Real F H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [SigmaCompactSpace N] [T2Space N]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace Real G]
  [FiniteDimensional Real G] {H'' : Type*} [TopologicalSpace H'']
  {K : ModelWithCorners Real G H''} [K.Boundaryless]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H'' Q]
  [IsManifold K ∞ Q] [SigmaCompactSpace Q] [T2Space Q]

private theorem solitonModelCovering_factorization_preserves_metric_potential
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {k : SmoothRiemannianMetric K Q} {psi : C^∞⟮K, Q; Real⟯}
    {p : N → M} {q : N → Q}
    (hp : solitonModelCovering h Fpot g f p)
    (hq : solitonModelCovering h Fpot k psi q)
    (e : Q ≃ₘ⟮K, I⟯ M) (he : ∀ x, e (q x) = p x) :
    Diffeomorph.pullbackMetricCross g e = k ∧ ∀ y, f (e y) = psi y := by
  constructor
  · have hqld := solitonModelCovering_isLocalDiffeomorph hq
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    obtain ⟨x, rfl⟩ := solitonModelCovering_surjective hq y
    let D := hqld.mfderivToContinuousLinearEquiv (by simp) x
    have hD (u : TangentSpace K (q x)) : mfderiv J K q x (D.symm u) = u := by
      rw [← hqld.mfderivToContinuousLinearEquiv_coe (by simp)]
      exact D.apply_symm_apply u
    have hcomp : (e : Q → M) ∘ q = p := funext he
    have hderiv : mfderiv K I e (q x) ∘L mfderiv J K q x = mfderiv J I p x := by
      have hd := mfderiv_comp x
        (e.contMDiff.mdifferentiableAt (by simp))
        (hqld.contMDiff.mdifferentiableAt (by simp))
      rw [hcomp] at hd
      exact hd.symm
    have heD (u : TangentSpace K (q x)) :
        mfderiv K I e (q x) u = mfderiv J I p x (D.symm u) := by
      have hd := congrArg (fun L => L (D.symm u)) hderiv
      change mfderiv K I e (q x) (mfderiv J K q x (D.symm u)) =
        mfderiv J I p x (D.symm u) at hd
      erw [hD] at hd
      exact hd
    rw [Diffeomorph.pullbackMetricCross_inner, heD, heD, he x]
    rw [← solitonModelCovering_metric hp]
    rw [solitonModelCovering_metric hq, hD, hD]
  · intro y
    obtain ⟨x, rfl⟩ := solitonModelCovering_surjective hq y
    rw [he x, ← solitonModelCovering_potential hp, solitonModelCovering_potential hq]

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real E G} [J.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [SigmaCompactSpace N] [T2Space N]

theorem solitonModelCovering_roundThreeCylinder_target_diffeomorph_trichotomy
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯}
    {cover : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → N}
    (hπ : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential g f cover) :
    (coveringDeckGroup cover = ⊥ ∧
      ∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
          (𝓡 2).prod 𝓘(Real, Real), J⟯ N,
        ∀ x, e x = cover x) ∨
    (coveringDeckGroup cover = cylinderAntipodalGroup ∧
      ∃ e : (RealProjectivePlane × Real) ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), J⟯ N,
        ∀ x, e (realProjectivePlaneQuotientMap x.1, x.2) = cover x) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      ∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, J⟯ N,
        ∀ x, e (cylinderDiagonalQuotientDiffeomorph
          (cylinderDiagonalQuotientMap x)) = cover x) := by
  have hquotient := solitonModelCovering_roundThreeCylinder_isQuotientCoveringMap hπ
  have hlocal := solitonModelCovering_isLocalDiffeomorph hπ
  rcases solitonModelCovering_roundThreeCylinder_deckGroup_eq_trichotomy hπ with
    htrivial | hantipodal | hdiagonal
  · left
    have hinjective : Function.Injective cover := by
      intro x y hxy
      obtain ⟨gamma, hgamma⟩ := hquotient.apply_eq_iff_mem_orbit.mp hxy
      have hmem : gamma.1 ∈ (⊥ : Subgroup
          (Equiv.Perm
            (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real))) := by
        rw [← htrivial.1]
        exact gamma.property
      have hone : gamma.1 = 1 := by
        simpa only [Subgroup.mem_bot] using hmem
      change gamma.1 y = x at hgamma
      rw [hone] at hgamma
      exact hgamma.symm
    let e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
        (𝓡 2).prod 𝓘(Real, Real), J⟯ N :=
      hlocal.diffeomorphOfBijective
        ⟨hinjective, solitonModelCovering_surjective hπ⟩
    exact ⟨htrivial.1, e, fun _ => rfl⟩
  · right
    left
    have hquotient' : IsQuotientCoveringMap cover cylinderAntipodalGroup :=
      (IsQuotientCoveringMap.subgroup_congr
        cover (Equiv.Perm
          (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real))
        (coveringDeckGroup cover) cylinderAntipodalGroup
        hantipodal.1).mp hquotient
    let e : (RealProjectivePlane × Real) ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), J⟯ N :=
      cylinderAntipodalQuotientDiffeomorph.symm.trans
        (hquotient'.orbitRelQuotientDiffeomorph hlocal)
    refine ⟨hantipodal.1, e, fun x => ?_⟩
    change (hquotient'.orbitRelQuotientDiffeomorph hlocal)
      (cylinderAntipodalQuotientDiffeomorph.symm
        (realProjectivePlaneQuotientMap x.1, x.2)) = cover x
    rw [cylinderAntipodalQuotientDiffeomorph_symm_apply]
    exact hquotient'.orbitRelQuotientDiffeomorph_apply hlocal x
  · right
    right
    have hquotient' : IsQuotientCoveringMap cover cylinderDiagonalGroup :=
      (IsQuotientCoveringMap.subgroup_congr
        cover (Equiv.Perm
          (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real))
        (coveringDeckGroup cover) cylinderDiagonalGroup
        hdiagonal.1).mp hquotient
    let e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, J⟯ N :=
      cylinderDiagonalQuotientDiffeomorph.symm.trans
        (hquotient'.orbitRelQuotientDiffeomorph hlocal)
    refine ⟨hdiagonal.1, e, fun x => ?_⟩
    change (hquotient'.orbitRelQuotientDiffeomorph hlocal)
      (cylinderDiagonalQuotientDiffeomorph.symm
        (cylinderDiagonalQuotientDiffeomorph
          (cylinderDiagonalQuotientMap x))) = cover x
    rw [Diffeomorph.symm_apply_apply]
    exact hquotient'.orbitRelQuotientDiffeomorph_apply hlocal x

private instance euclideanThreeFinrankFact :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem solitonModelCovering_roundThreeCylinder_target_isometry_trichotomy
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯}
    {cover : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → N}
    (hπ : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential g f cover) :
    (coveringDeckGroup cover = ⊥ ∧
      ∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
          (𝓡 2).prod 𝓘(Real, Real), J⟯ N,
        (∀ x, e x = cover x) ∧
        Diffeomorph.pullbackMetricCross g e = roundThreeCylinderShrinkerMetric ∧
        ∀ x, f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderAntipodalGroup ∧
      ∃ e : (RealProjectivePlane × Real) ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), J⟯ N,
        (∀ x, e (realProjectivePlaneQuotientMap x.1, x.2) = cover x) ∧
        Diffeomorph.pullbackMetricCross g e =
          (scaleMetric 2 (by norm_num)
            (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
              (euclideanMetric (E := Real)) ∧
        ∀ x, f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      ∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, J⟯ N,
        (∀ x, e (cylinderDiagonalQuotientDiffeomorph
          (cylinderDiagonalQuotientMap x)) = cover x) ∧
        Diffeomorph.pullbackMetricCross g
          (cylinderDiagonalQuotientDiffeomorph.trans e) = cylinderDiagonalQuotientMetric ∧
        ∀ x, f (e (cylinderDiagonalQuotientDiffeomorph x)) =
          cylinderDiagonalQuotientPotential x) := by
  rcases solitonModelCovering_roundThreeCylinder_target_diffeomorph_trichotomy hπ with
    ⟨hgroup, e, he⟩ | ⟨hgroup, e, he⟩ | ⟨hgroup, e, he⟩
  · left
    have hpres := solitonModelCovering_factorization_preserves_metric_potential hπ
      (solitonModelCovering_refl normalizedGradientRicciSoliton_roundThreeCylinder) e he
    exact ⟨hgroup, e, he, hpres.1, fun x =>
      (hpres.2 x).trans (roundThreeCylinderShrinkerPotential_apply x)⟩
  · right
    left
    let d := cylinderAntipodalQuotientDiffeomorph.trans e
    have hd : ∀ x, d (cylinderAntipodalQuotientMap x) = cover x := he
    have hpres := solitonModelCovering_factorization_preserves_metric_potential hπ
      solitonModelCovering_cylinderAntipodalQuotient d hd
    refine ⟨hgroup, e, he, ?_, ?_⟩
    · have hleft : Diffeomorph.pullbackMetricCross
          (Diffeomorph.pullbackMetricCross g e) cylinderAntipodalQuotientDiffeomorph =
            cylinderAntipodalQuotientMetric := by
        rw [Diffeomorph.pullbackMetricCross_trans]
        exact hpres.1
      exact (Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hleft).symm.trans
        (Diffeomorph.pullbackMetricCross_symm_eq_iff.mp
          cylinderAntipodalQuotientDiffeomorph_pullbackMetric)
    · intro x
      have hf := hpres.2 (cylinderAntipodalQuotientDiffeomorph.symm x)
      change f (e (cylinderAntipodalQuotientDiffeomorph
        (cylinderAntipodalQuotientDiffeomorph.symm x))) = _ at hf
      rw [Diffeomorph.apply_symm_apply] at hf
      exact hf.trans (cylinderAntipodalQuotientDiffeomorph_potential x)
  · right
    right
    let d := cylinderDiagonalQuotientDiffeomorph.trans e
    have hd : ∀ x, d (cylinderDiagonalQuotientMap x) = cover x := he
    have hpres := solitonModelCovering_factorization_preserves_metric_potential hπ
      solitonModelCovering_cylinderDiagonalQuotient d hd
    exact ⟨hgroup, e, he, hpres⟩

end DifferentialGeometry.Geometry
