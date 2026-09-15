import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceTowerExistence
import DifferentialGeometry.Topology.PiecewiseLinear.Manifold
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section HomeomorphInto

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]

def IsPLHomeomorphInto (n : ℕ) {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] (f : M → N) (K : Set M) : Prop :=
  IsPLOn n n f K ∧ InjOn f K ∧
    ∀ y ∈ f '' K, ∃ g : N → M, IsPLWithinAt n n g (f '' K) y ∧ LeftInvOn g f K

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

end HomeomorphInto

def Moise352 (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁}, IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n K →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
    ∀ (φ : M₁ → ℝ), ContinuousOn φ K → (∀ x ∈ K, 0 < φ x) →
    ∃ f : M₁ → M₂, IsPLHomeomorphInto n f K ∧ ∀ x ∈ K, dist (f x) (h x) < φ x

theorem Moise352.exists_approx_of_isOpen {m : ℕ} (h352 : Moise352.{u} (m + 1))
    {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M₂]
    [HasGroupoid M₁ (plGroupoid (m + 1))] [HasGroupoid M₂ (plGroupoid (m + 1))]
    {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂} (hh : Topology.IsEmbedding (U.domRestrict h))
    (φ : M₁ → ℝ) (hφ : ContinuousOn φ U) (hpos : ∀ x ∈ U, 0 < φ x) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto (m + 1) f U ∧
      ∀ x ∈ U, dist (f x) (h x) < φ x := by
  by_cases hne : U.Nonempty
  · let : Nonempty M₁ := ⟨hne.choose⟩
    exact h352 (isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen hU) hh φ hφ hpos
  · have hUempty : U = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst U
    exact ⟨h, isPLHomeomorphInto_empty h, fun _ hx => False.elim hx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
