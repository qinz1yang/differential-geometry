import DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph.Defs
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section HomeomorphInto

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]

variable {f : M → N} {K : Set M}

theorem IsPLHomeomorphInto.isPLOn (hf : IsPLHomeomorphInto n f K) : IsPLOn n n f K :=
  hf.1

theorem IsPLHomeomorphInto.injOn (hf : IsPLHomeomorphInto n f K) : InjOn f K :=
  hf.2.1

theorem IsPLHomeomorphInto.continuousOn (hf : IsPLHomeomorphInto n f K) : ContinuousOn f K :=
  fun x hx => (hf.isPLOn x hx).continuousWithinAt

theorem IsPLHomeomorphInto.isPLOn_inverse (hf : IsPLHomeomorphInto n f K)
    {g : N → M} (hg : LeftInvOn g f K) : IsPLOn n n g (f '' K) := by
  intro y hy
  obtain ⟨g', hg', hleft⟩ := hf.2.2 y hy
  apply piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem hg' _ hy
  rintro z ⟨x, hx, rfl⟩
  exact (hg hx).trans (hleft hx).symm

theorem isPLHomeomorphInto_iff_exists_inverse [Nonempty M] :
    IsPLHomeomorphInto n f K ↔
      IsPLOn n n f K ∧ InjOn f K ∧
        ∃ g : N → M, IsPLOn n n g (f '' K) ∧ LeftInvOn g f K := by
  constructor
  · intro hf
    have hleft := hf.injOn.leftInvOn_invFunOn
    exact ⟨hf.isPLOn, hf.injOn, Function.invFunOn f K, hf.isPLOn_inverse hleft, hleft⟩
  · rintro ⟨hf, hinj, g, hg, hleft⟩
    exact ⟨hf, hinj, fun y hy => ⟨g, hg y hy, hleft⟩⟩

theorem isPLHomeomorphInto_empty (f : M → N) : IsPLHomeomorphInto n f ∅ := by
  refine ⟨fun _ hx => False.elim hx, fun _ hx => False.elim hx, ?_⟩
  simp

theorem IsPLHomeomorphInto.isOpen_image (hf : IsPLHomeomorphInto n f K) (hK : IsOpen K) :
    IsOpen (f '' K) :=
  isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin n))
    hK hf.continuousOn hf.injOn

theorem IsPLHomeomorphInto.isOpenMap_domRestrict (hf : IsPLHomeomorphInto n f K)
    (hK : IsOpen K) : IsOpenMap (K.domRestrict f) := by
  intro W hW
  have hWK : Subtype.val '' W ⊆ K := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hopen := isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin n))
    (hK.isOpenMap_subtype_val W hW) (hf.continuousOn.mono hWK) (hf.injOn.mono hWK)
  change IsOpen ((fun x : K => f x) '' W)
  simpa only [image_image] using hopen

end HomeomorphInto

end DifferentialGeometry.Topology.PiecewiseLinear
