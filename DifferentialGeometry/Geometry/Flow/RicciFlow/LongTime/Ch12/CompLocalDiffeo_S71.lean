import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompImmersion_S60
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false

/-!
# CH12-S71 / G1: order-0 smallness makes `E|_U` a diffeomorphism onto the open set `E '' U`

For `E : H.Carrier → H.Carrier` smooth and injective on an open `U`:

* `ckErr_S45 H H.metric 1 E 0 < 1` on `U` ⇒ `mfderiv E` injective, hence invertible (equal
  dimensions), on `U` (Cauchy-Schwarz, `ckErr0_immersion_S60`);
* ⇒ `E` is a local diffeomorphism on `U` (library inverse function theorem
  `isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv`) and, being injective on `U`, is the
  underlying map of a `PartialDiffeomorph` with source `U` (`exists_partialDiffeomorph_of_injOn`);
* `E '' U` is open (`image_opens_isOpen`).
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- an injective endomorphism of `ℝ³` is invertible (dimension count). -/
theorem isInvertible_of_injective_S71
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hA : Function.Injective A) : A.IsInvertible := by
  let L := (A.toLinearMap.linearEquivOfInjective hA rfl).toContinuousLinearEquiv
  exact ⟨L, rfl⟩

/-- order-0 error `< 1` against `H.metric` makes `mfderiv E q` invertible. -/
theorem mfderiv_isInvertible_of_ckErr0_S71 (H : FiniteVolumeHyperbolicModel.{u})
    (E : H.Carrier → H.Carrier) (q : H.Carrier) (hq : ckErr_S45 H H.metric 1 E 0 q < 1) :
    (mfderiv (𝓡 3) (𝓡 3) E q).IsInvertible :=
  isInvertible_of_injective_S71 _ (ckErr0_immersion_S60 H H.metric 1 E q hq).2

/-- `E` smooth, injective on the open `U` with invertible differential there: `E` is the underlying
map of a partial diffeomorphism with source `U`. -/
theorem exists_partialDiffeomorph_of_invertible_S71 (H : FiniteVolumeHyperbolicModel.{u})
    (E : H.Carrier → H.Carrier) (hE : ContMDiff (𝓡 3) (𝓡 3) ∞ E) (U : Opens H.Carrier)
    (hinj : Set.InjOn E (U : Set H.Carrier))
    (hinv : ∀ p ∈ (U : Set H.Carrier), (mfderiv (𝓡 3) (𝓡 3) E p).IsInvertible) :
    ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H.Carrier (∞ : WithTop ℕ∞),
      Φ.source = (U : Set H.Carrier) ∧ (Φ : H.Carrier → H.Carrier) = E := by
  have : Nonempty H.Carrier := ⟨H.basepoint⟩
  have hloc : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) (∞ : WithTop ℕ∞) E (U : Set H.Carrier) :=
    fun x => DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
      U.isOpen x.2 hE.contMDiffOn (hinv x x.2)
  obtain ⟨Φ, hs, _, hΦ⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn U.isOpen hloc hinj
  exact ⟨Φ, hs, hΦ⟩

/-- **G1 (steps (1)(2))**: smallness of the order-0 error on `U` and injectivity on `U` give a partial
diffeomorphism with source `U` and underlying map `E`, with `mfderiv E` injective on `U`. -/
theorem exists_partialDiffeomorph_of_ckErr0_S71 (H : FiniteVolumeHyperbolicModel.{u})
    (E : H.Carrier → H.Carrier) (hE : ContMDiff (𝓡 3) (𝓡 3) ∞ E) (U : Opens H.Carrier)
    (hinj : Set.InjOn E (U : Set H.Carrier))
    (h0 : ∀ p ∈ (U : Set H.Carrier), ckErr_S45 H H.metric 1 E 0 p < 1) :
    ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H.Carrier (∞ : WithTop ℕ∞),
      Φ.source = (U : Set H.Carrier) ∧ (Φ : H.Carrier → H.Carrier) = E ∧
        ∀ p ∈ (U : Set H.Carrier), Function.Injective (mfderiv (𝓡 3) (𝓡 3) E p) := by
  obtain ⟨Φ, hs, hΦ⟩ := exists_partialDiffeomorph_of_invertible_S71 H E hE U hinj
    (fun p hp => mfderiv_isInvertible_of_ckErr0_S71 H E p (h0 p hp))
  exact ⟨Φ, hs, hΦ, fun p hp => (ckErr0_immersion_S60 H H.metric 1 E p (h0 p hp)).2⟩

/-- `E '' U` is open. -/
theorem isOpen_image_of_ckErr0_S71 (H : FiniteVolumeHyperbolicModel.{u})
    (E : H.Carrier → H.Carrier) (hE : ContMDiff (𝓡 3) (𝓡 3) ∞ E) (U : Opens H.Carrier)
    (hinj : Set.InjOn E (U : Set H.Carrier))
    (h0 : ∀ p ∈ (U : Set H.Carrier), ckErr_S45 H H.metric 1 E 0 p < 1) :
    IsOpen (E '' (U : Set H.Carrier)) := by
  obtain ⟨Φ, hs, hΦ, -⟩ := exists_partialDiffeomorph_of_ckErr0_S71 H E hE U hinj h0
  subst hΦ
  exact image_opens_isOpen Φ (le_of_eq hs.symm)

end GC.LongTime.Ch12
