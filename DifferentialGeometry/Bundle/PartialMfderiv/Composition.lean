import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open Set
open scoped Manifold

variable {k E E' F : Type*} [NontriviallyNormedField k]
  [NormedAddCommGroup E] [NormedSpace k E] [NormedAddCommGroup E'] [NormedSpace k E']
  [NormedAddCommGroup F] [NormedSpace k F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners k E H} {J : ModelWithCorners k E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → N} {g : N → F} {s : Set M} {t : Set N} {x : M}

namespace MDifferentiableAt

theorem mvfderiv_comp (hg : MDifferentiableAt J 𝓘(k, F) g (f x))
    (hf : MDifferentiableAt I J f x) :
    mvfderiv I (g ∘ f) x = (mvfderiv J g (f x)).comp (mfderiv I J f x) := by
  unfold _root_.mvfderiv
  rw [mfderiv_comp x hg hf]
  rfl

theorem mvfderiv_comp_apply (hg : MDifferentiableAt J 𝓘(k, F) g (f x))
    (hf : MDifferentiableAt I J f x) (X : TangentSpace I x) :
    mvfderiv I (g ∘ f) x X = mvfderiv J g (f x) (mfderiv I J f x X) :=
  congrArg (fun L => L X) (hg.mvfderiv_comp hf)

theorem mvfderiv_comp_mfderivWithin (hg : MDifferentiableAt J 𝓘(k, F) g (f x))
    (hf : MDifferentiableWithinAt I J f s x) (hs : UniqueMDiffWithinAt I s x) :
    mvfderivWithin I (g ∘ f) s x =
      (mvfderiv J g (f x)).comp (mfderivWithin I J f s x) := by
  unfold _root_.mvfderivWithin _root_.mvfderiv
  rw [mfderiv_comp_mfderivWithin x hg hf hs]
  rfl

theorem mvfderiv_comp_mfderivWithin_apply (hg : MDifferentiableAt J 𝓘(k, F) g (f x))
    (hf : MDifferentiableWithinAt I J f s x) (hs : UniqueMDiffWithinAt I s x)
    (X : TangentSpace I x) :
    mvfderivWithin I (g ∘ f) s x X = mvfderiv J g (f x) (mfderivWithin I J f s x X) :=
  congrArg (fun L => L X) (hg.mvfderiv_comp_mfderivWithin hf hs)

end MDifferentiableAt

namespace MDifferentiableWithinAt

theorem mvfderivWithin_comp (hg : MDifferentiableWithinAt J 𝓘(k, F) g t (f x))
    (hf : MDifferentiableWithinAt I J f s x) (hst : MapsTo f s t)
    (hs : UniqueMDiffWithinAt I s x) :
    mvfderivWithin I (g ∘ f) s x =
      (mvfderivWithin J g t (f x)).comp (mfderivWithin I J f s x) := by
  unfold _root_.mvfderivWithin
  rw [mfderivWithin_comp x hg hf hst hs]
  rfl

theorem mvfderivWithin_comp_apply (hg : MDifferentiableWithinAt J 𝓘(k, F) g t (f x))
    (hf : MDifferentiableWithinAt I J f s x) (hst : MapsTo f s t)
    (hs : UniqueMDiffWithinAt I s x) (X : TangentSpace I x) :
    mvfderivWithin I (g ∘ f) s x X =
      mvfderivWithin J g t (f x) (mfderivWithin I J f s x X) :=
  congrArg (fun L => L X) (hg.mvfderivWithin_comp hf hst hs)

end MDifferentiableWithinAt

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace k G]
  {A : M → F →L[k] G} {v : M → F}

theorem MDifferentiableWithinAt.mvfderivWithin_clm_apply
    (hA : MDifferentiableWithinAt I 𝓘(k, F →L[k] G) A s x)
    (hv : MDifferentiableWithinAt I 𝓘(k, F) v s x) (hs : UniqueMDiffWithinAt I s x) :
    mvfderivWithin I (fun y => A y (v y)) s x =
      (A x).comp (mvfderivWithin I v s x) +
        (ContinuousLinearMap.apply k G (v x)).comp (mvfderivWithin I A s x) := by
  refine HasMFDerivWithinAt.mfderivWithin ⟨hA.1.clm_apply hv.1, ?_⟩ hs
  convert! hA.hasMFDerivWithinAt.2.clm_apply hv.hasMFDerivWithinAt.2 using 1
  simp
  rfl

theorem MDifferentiableAt.mvfderiv_clm_apply
    (hA : MDifferentiableAt I 𝓘(k, F →L[k] G) A x)
    (hv : MDifferentiableAt I 𝓘(k, F) v x) :
    mvfderiv I (fun y => A y (v y)) x =
      (A x).comp (mvfderiv I v x) +
        (ContinuousLinearMap.apply k G (v x)).comp (mvfderiv I A x) := by
  simpa only [mvfderivWithin_univ] using
    hA.mdifferentiableWithinAt.mvfderivWithin_clm_apply
      hv.mdifferentiableWithinAt (uniqueMDiffWithinAt_univ I)
