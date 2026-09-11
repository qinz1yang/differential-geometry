import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.LinearAlgebra.Orientation
import DifferentialGeometry.Topology.Manifold.Paths
import DifferentialGeometry.Bundle.Orientation.Section

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

def tangentChartEquiv (p x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet) :
    TangentSpace I x ≃ₗ[ℝ] E :=
  (trivializationAt E (TangentSpace I) p).linearEquivAt ℝ x hx

structure ManifoldOrientation (n : ℕ) [FiniteDimensional ℝ E] where
  dimension_eq : Module.finrank ℝ E = n
  orientation : (x : M) → Orientation ℝ (TangentSpace I x) (Fin n)
  locally_constant : ∀ p x : M,
    ∀ hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet,
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ hU : U ⊆ (trivializationAt E (TangentSpace I) p).baseSet,
      ∀ y : M, ∀ hy : y ∈ U,
        Orientation.map (Fin n) (tangentChartEquiv I M p y (hU hy)) (orientation y) =
          Orientation.map (Fin n) (tangentChartEquiv I M p x hx) (orientation x)

namespace ManifoldOrientation

variable {I M} {n : ℕ} [FiniteDimensional ℝ E]

@[ext]
theorem ext {o₁ o₂ : ManifoldOrientation I M n}
    (h : ∀ x, o₁.orientation x = o₂.orientation x) : o₁ = o₂ := by
  cases o₁
  cases o₂
  congr
  exact funext h

def inChart (o : ManifoldOrientation I M n) (p x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet) :
    Orientation ℝ E (Fin n) :=
  Orientation.map (Fin n) (tangentChartEquiv I M p x hx) (o.orientation x)

def opposite (o : ManifoldOrientation I M n) : ManifoldOrientation I M n where
  dimension_eq := o.dimension_eq
  orientation x := -o.orientation x
  locally_constant p x hx := by
    obtain ⟨U, hUopen, hxU, hU, h⟩ := o.locally_constant p x hx
    refine ⟨U, hUopen, hxU, hU, fun y hy ↦ ?_⟩
    simpa only [Orientation.map_neg] using congrArg Neg.neg (h y hy)

@[simp]
theorem opposite_orientation (o : ManifoldOrientation I M n) (x : M) :
    o.opposite.orientation x = -o.orientation x := rfl

@[simp]
theorem opposite_opposite (o : ManifoldOrientation I M n) :
    o.opposite.opposite = o := by
  apply ManifoldOrientation.ext
  intro x
  exact neg_neg (o.orientation x)

end ManifoldOrientation

private theorem orientation_map_trans
    {A F G : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]
    {n : ℕ} (e : A ≃ₗ[ℝ] F) (f : F ≃ₗ[ℝ] G) (o : Orientation ℝ A (Fin n)) :
    Orientation.map (Fin n) (e.trans f) o =
      Orientation.map (Fin n) f (Orientation.map (Fin n) e o) := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

end DifferentialGeometry

namespace Diffeomorph

open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {N : Type*} [TopologicalSpace N]
  [ChartedSpace H' N] [IsManifold J ∞ N]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] {H'' : Type*} [TopologicalSpace H'']
  {K : ModelWithCorners ℝ G H''} {P : Type*} [TopologicalSpace P]
  [ChartedSpace H'' P] [IsManifold K ∞ P]
  {n : ℕ}

def preservesOrientation (f : M ≃ₘ⟮I, J⟯ N)
    (oM : ManifoldOrientation I M n) (oN : ManifoldOrientation J N n) : Prop :=
  ∀ x, Orientation.map (Fin n)
    (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
    (oM.orientation x) = oN.orientation (f x)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem mfderivLinearEquiv_refl (x : M) :
    ((Diffeomorph.refl I M ∞).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
      LinearEquiv.refl ℝ (TangentSpace I x) := by
  ext v
  change mfderiv I I id x v = v
  simp only [mfderiv_id, ContinuousLinearMap.id_apply]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [FiniteDimensional ℝ F] [IsManifold J ∞ N]
  [FiniteDimensional ℝ G] [IsManifold K ∞ P] in
private theorem mfderivLinearEquiv_trans (f : M ≃ₘ⟮I, J⟯ N)
    (g : N ≃ₘ⟮J, K⟯ P) (x : M) :
    ((f.trans g).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
      (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.trans
        (g.mfderivToContinuousLinearEquiv (by simp) (f x)).toLinearEquiv := by
  ext v
  exact mfderiv_comp_apply x (g.mdifferentiable (by simp) (f x))
    (f.mdifferentiable (by simp) x) v

theorem preservesOrientation_refl (o : ManifoldOrientation I M n) :
    (Diffeomorph.refl I M ∞).preservesOrientation o o := by
  intro x
  erw [mfderivLinearEquiv_refl, Orientation.map_refl]
  rfl

theorem preservesOrientation_trans {f : M ≃ₘ⟮I, J⟯ N} {g : N ≃ₘ⟮J, K⟯ P}
    {oM : ManifoldOrientation I M n} {oN : ManifoldOrientation J N n}
    {oP : ManifoldOrientation K P n}
    (hf : f.preservesOrientation oM oN) (hg : g.preservesOrientation oN oP) :
    (f.trans g).preservesOrientation oM oP := by
  intro x
  erw [mfderivLinearEquiv_trans, orientation_map_trans, hf x, hg (f x)]
  rfl

theorem preservesOrientation_symm {f : M ≃ₘ⟮I, J⟯ N}
    {oM : ManifoldOrientation I M n} {oN : ManifoldOrientation J N n}
    (hf : f.preservesOrientation oM oN) : f.symm.preservesOrientation oN oM := by
  intro y
  apply (Orientation.map (Fin n)
    (f.mfderivToContinuousLinearEquiv (by simp) (f.symm y)).toLinearEquiv).injective
  rw [hf (f.symm y)]
  have h := congrArg (fun e ↦ Orientation.map (Fin n) e (oN.orientation y))
    (mfderivLinearEquiv_trans f.symm f y)
  erw [f.symm_trans_self, mfderivLinearEquiv_refl, Orientation.map_refl,
    orientation_map_trans] at h
  convert! h.symm using 1
  congr 1
  exact f.apply_symm_apply y

theorem preservesOrientation_opposite {f : M ≃ₘ⟮I, J⟯ N}
    {oM : ManifoldOrientation I M n} {oN : ManifoldOrientation J N n}
    (hf : f.preservesOrientation oM oN) :
    f.preservesOrientation oM.opposite oN.opposite := by
  intro x
  simpa only [ManifoldOrientation.opposite_orientation, Orientation.map_neg] using
    congrArg Neg.neg (hf x)

end Diffeomorph

namespace DifferentialGeometry.Topology.Manifold

open Bundle Manifold
open scoped Manifold ContDiff

theorem exists_tangent_orientation_of_simply_connected
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [SimplyConnectedSpace M] (hdim : Module.finrank ℝ E = 3) :
    ∃ o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin 3),
      DifferentialGeometry.VectorBundle.IsCompatibleOrientation
        (F := E) (TangentSpace 𝓘(ℝ, E)) o := by
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  exact DifferentialGeometry.VectorBundle.exists_compatible_orientation_of_simply_connected
    (tangentBundleCore 𝓘(ℝ, E) M) hdim

end DifferentialGeometry.Topology.Manifold
