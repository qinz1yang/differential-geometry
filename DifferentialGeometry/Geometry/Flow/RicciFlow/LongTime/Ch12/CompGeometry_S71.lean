import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompNaturality_S71

set_option autoImplicit false

/-!
# CH12-S71 / G2: the pull-back identities (E1, E2) for a partial diffeomorphism `Φ`, `U ⊆ Φ.source`

Local versions of `pullbackRestrict_comp_eq_fixed_S60` / `pullbackRestrict_self_eq_fixed_S60`
(CompGeometry_S60), with `localPullbackMetric_S71` in place of `fixedDomainPullbackMetric`.
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

section Geom

variable (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]

theorem subset_partialImage_S71
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H.Carrier (∞ : WithTop ℕ∞))
    (U : Opens H.Carrier) (hU : (U : Set H.Carrier) ⊆ Φ.source) :
    (Φ : H.Carrier → H.Carrier) '' (U : Set H.Carrier) ⊆
      (partialImage_S71 Φ U hU : Set H.Carrier) := fun _ hy => hy

omit [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] in
theorem contMDiffOn_partial_S71
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H.Carrier (∞ : WithTop ℕ∞))
    (U : Opens H.Carrier) (hU : (U : Set H.Carrier) ⊆ Φ.source) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Φ : H.Carrier → H.Carrier) U :=
  Φ.contMDiffOn_toFun.mono hU

omit [IsManifold (𝓡 3) ∞ N] in
theorem contMDiffOn_comp_partial_S71
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H.Carrier (∞ : WithTop ℕ∞))
    (U : Opens H.Carrier) (hU : (U : Set H.Carrier) ⊆ Φ.source)
    (f : H.Carrier → N)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f ((Φ : H.Carrier → H.Carrier) '' (U : Set H.Carrier))) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f ∘ (Φ : H.Carrier → H.Carrier)) U :=
  hf.comp (contMDiffOn_partial_S71 H Φ U hU) (fun x hx => ⟨x, hx, rfl⟩)

omit [IsManifold (𝓡 3) ∞ N] in
theorem mfderiv_comp_partial_S71
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H.Carrier (∞ : WithTop ℕ∞))
    (U : Opens H.Carrier) (hU : (U : Set H.Carrier) ⊆ Φ.source)
    (f : H.Carrier → N)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f ((Φ : H.Carrier → H.Carrier) '' (U : Set H.Carrier)))
    (x : U) (v : TangentSpace (𝓡 3) (x : H.Carrier)) :
    mfderiv (𝓡 3) (𝓡 3) (f ∘ (Φ : H.Carrier → H.Carrier)) (x : H.Carrier) v =
      mfderiv (𝓡 3) (𝓡 3) f (Φ x)
        (mfderiv (𝓡 3) (𝓡 3) (Φ : H.Carrier → H.Carrier) x v) := by
  have hf' : MDifferentiableAt (𝓡 3) (𝓡 3) f (Φ x) :=
    (hf.contMDiffAt ((partialImage_S71 Φ U hU).isOpen.mem_nhds ⟨x, x.2, rfl⟩)).mdifferentiableAt
      infty_ne_zero_C4
  have he' : MDifferentiableAt (𝓡 3) (𝓡 3) (Φ : H.Carrier → H.Carrier) x :=
    ((contMDiffOn_partial_S71 H Φ U hU).contMDiffAt (U.isOpen.mem_nhds x.2)).mdifferentiableAt
      infty_ne_zero_C4
  exact mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) (x : H.Carrier) hf' he' (v := v)

omit [IsManifold (𝓡 3) ∞ N] in
theorem mfderiv_inj_comp_partial_S71
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H.Carrier (∞ : WithTop ℕ∞))
    (U : Opens H.Carrier) (hU : (U : Set H.Carrier) ⊆ Φ.source)
    (hΦ : ∀ y ∈ (U : Set H.Carrier),
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (Φ : H.Carrier → H.Carrier) y))
    (f : H.Carrier → N)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f ((Φ : H.Carrier → H.Carrier) '' (U : Set H.Carrier)))
    (hinj : ∀ y ∈ (Φ : H.Carrier → H.Carrier) '' (U : Set H.Carrier),
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)) :
    ∀ y ∈ (U : Set H.Carrier),
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (f ∘ (Φ : H.Carrier → H.Carrier)) y) := by
  intro y hy v w hvw
  have h1 := mfderiv_comp_partial_S71 H Φ U hU f hf ⟨y, hy⟩ v
  have h2 := mfderiv_comp_partial_S71 H Φ U hU f hf ⟨y, hy⟩ w
  exact hΦ y hy (hinj (Φ y) ⟨y, hy, rfl⟩ (h1.symm.trans (hvw.trans h2)))

/-- **(E2)** the pulled-back reference. -/
theorem pullbackRestrict_self_eq_local_S71
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H.Carrier (∞ : WithTop ℕ∞))
    (U : Opens H.Carrier) (hU : (U : Set H.Carrier) ⊆ Φ.source)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Φ : H.Carrier → H.Carrier) U)
    (hinj : ∀ y ∈ (U : Set H.Carrier),
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (Φ : H.Carrier → H.Carrier) y)) :
    pullbackRestrict_S57 H (scaleMetric (I := 𝓡 3) 1 one_pos H.metric)
        (Φ : H.Carrier → H.Carrier) U he hinj =
      localPullbackMetric_S71 Φ U hU (partialImage_S71 Φ U hU) (subset_partialImage_S71 H Φ U hU)
        (H.metric.restrictOpen (partialImage_S71 Φ U hU)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullbackMetric_inner_S71]
  simp only [pullbackRestrict_S57, SmoothRiemannianMetric.pullbackOfImmersion_inner,
    scaleMetric_inner, one_mul, mfderiv_comp_val_C4 (Φ : H.Carrier → H.Carrier) U he x]
  rfl

/-- **(E1)** the pulled-back target metric. -/
theorem pullbackRestrict_comp_eq_local_S71 (g : SmoothRiemannianMetric (𝓡 3) N)
    (f : H.Carrier → N)
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H.Carrier (∞ : WithTop ℕ∞))
    (U : Opens H.Carrier) (hU : (U : Set H.Carrier) ⊆ Φ.source)
    (hΦ : ∀ y ∈ (U : Set H.Carrier),
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (Φ : H.Carrier → H.Carrier) y))
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f ((Φ : H.Carrier → H.Carrier) '' (U : Set H.Carrier)))
    (hinj : ∀ y ∈ (Φ : H.Carrier → H.Carrier) '' (U : Set H.Carrier),
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)) :
    pullbackRestrict_S57 H g (f ∘ (Φ : H.Carrier → H.Carrier)) U
        (contMDiffOn_comp_partial_S71 H Φ U hU f hf)
        (mfderiv_inj_comp_partial_S71 H Φ U hU hΦ f hf hinj) =
      localPullbackMetric_S71 Φ U hU (partialImage_S71 Φ U hU) (subset_partialImage_S71 H Φ U hU)
        (pullbackRestrict_S57 H g f (partialImage_S71 Φ U hU) hf hinj) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullbackMetric_inner_S71]
  have hL := SmoothRiemannianMetric.pullbackOfImmersion_inner (I := 𝓡 3) g
    (fun z : U => (f ∘ (Φ : H.Carrier → H.Carrier)) z)
    (contMDiff_restrict_C4 (f ∘ (Φ : H.Carrier → H.Carrier)) U
      (contMDiffOn_comp_partial_S71 H Φ U hU f hf))
    (fun z => immersion_restrict_inj_S57 H (f ∘ (Φ : H.Carrier → H.Carrier)) U
      (contMDiffOn_comp_partial_S71 H Φ U hU f hf)
      (mfderiv_inj_comp_partial_S71 H Φ U hU hΦ f hf hinj) z) x v w
  have hR := SmoothRiemannianMetric.pullbackOfImmersion_inner (I := 𝓡 3) g
    (fun z : partialImage_S71 Φ U hU => f z) (contMDiff_restrict_C4 f _ hf)
    (fun z => immersion_restrict_inj_S57 H f (partialImage_S71 Φ U hU) hf hinj z)
    ⟨Φ x, x, x.2, rfl⟩ (mfderiv (𝓡 3) (𝓡 3) (Φ : H.Carrier → H.Carrier) x v)
    (mfderiv (𝓡 3) (𝓡 3) (Φ : H.Carrier → H.Carrier) x w)
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [mfderiv_comp_val_C4 (f ∘ (Φ : H.Carrier → H.Carrier)) U
      (contMDiffOn_comp_partial_S71 H Φ U hU f hf) x v,
    mfderiv_comp_val_C4 (f ∘ (Φ : H.Carrier → H.Carrier)) U
      (contMDiffOn_comp_partial_S71 H Φ U hU f hf) x w]
  have e1 := mfderiv_comp_val_C4 f (partialImage_S71 Φ U hU) hf ⟨Φ x, x, x.2, rfl⟩
    (mfderiv (𝓡 3) (𝓡 3) (Φ : H.Carrier → H.Carrier) x v)
  have e2 := mfderiv_comp_val_C4 f (partialImage_S71 Φ U hU) hf ⟨Φ x, x, x.2, rfl⟩
    (mfderiv (𝓡 3) (𝓡 3) (Φ : H.Carrier → H.Carrier) x w)
  exact congrArg₂ (fun a b => g.inner (f (Φ x)) a b)
    ((mfderiv_comp_partial_S71 H Φ U hU f hf x v).trans e1.symm)
    ((mfderiv_comp_partial_S71 H Φ U hU f hf x w).trans e2.symm)

end Geom

end GC.LongTime.Ch12
