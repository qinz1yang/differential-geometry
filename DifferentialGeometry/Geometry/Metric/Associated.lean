import DifferentialGeometry.Bundle.Associated.Smooth
import DifferentialGeometry.Topology.GroupAction.Module
import DifferentialGeometry.Geometry.Metric.BundlePullback
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

noncomputable section

open Set Bundle
open scoped Manifold ContDiff

namespace Representation

variable {G W : Type*} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℝ W]

private theorem continuous_representation_of_inner_map (ρ : Representation ℝ G W)
    (hρ : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w) (g : G) :
    Continuous (ρ g) :=
  ((ρ g).isometryOfInner (hρ g)).continuous

def associatedRiemannianMetric (ρ : Representation ℝ G W)
    (hρ : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w)
    {B : Type*} (P : B → Type*) [∀ x, Torsor G (P x)] :
    Bundle.RiemannianMetric (fun x => P x →ₑ[ρ] W) :=
  (Bundle.RiemannianMetric.ofInnerProductSpace (fun _ : B => W)).pullback id
    (fun x => ρ.evalContinuousLinearEquiv (continuous_representation_of_inner_map ρ hρ)
      (Classical.arbitrary (P x)))

theorem associatedRiemannianMetric_inner (ρ : Representation ℝ G W)
    (hρ : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w)
    {B : Type*} (P : B → Type*) [∀ x, Torsor G (P x)] (x : B) (p : P x)
    (v w : P x →ₑ[ρ] W) :
    (ρ.associatedRiemannianMetric hρ P).inner x v w = inner ℝ (v p) (w p) := by
  let q := Classical.arbitrary (P x)
  change inner ℝ (v q) (w q) = inner ℝ (v p) (w p)
  have hv : v q = ρ (q /ₛ p) (v p) := by
    simpa only [sdiv_smul, Module.End.smul_def] using map_smulₛₗ v (q /ₛ p) p
  have hw : w q = ρ (q /ₛ p) (w p) := by
    simpa only [sdiv_smul, Module.End.smul_def] using map_smulₛₗ w (q /ₛ p) p
  rw [hv, hw, hρ]

def evalLinearIsometryEquiv (ρ : Representation ℝ G W)
    (hρ : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w)
    {B : Type*} (P : B → Type*) [∀ x, Torsor G (P x)] (x : B) (p : P x) :
    letI : NormedAddCommGroup (P x →ₑ[ρ] W) :=
      ((ρ.associatedRiemannianMetric hρ P).toCore x).toNormedAddCommGroupOfTopology
        ((ρ.associatedRiemannianMetric hρ P).continuousAt x)
        ((ρ.associatedRiemannianMetric hρ P).isVonNBounded x)
    (P x →ₑ[ρ] W) ≃ₗᵢ[ℝ] W := by
  letI : NormedAddCommGroup (P x →ₑ[ρ] W) :=
    ((ρ.associatedRiemannianMetric hρ P).toCore x).toNormedAddCommGroupOfTopology
      ((ρ.associatedRiemannianMetric hρ P).continuousAt x)
      ((ρ.associatedRiemannianMetric hρ P).isVonNBounded x)
  letI : InnerProductSpace ℝ (P x →ₑ[ρ] W) :=
    InnerProductSpace.ofCoreOfTopology ((ρ.associatedRiemannianMetric hρ P).toCore x)
      ((ρ.associatedRiemannianMetric hρ P).continuousAt x)
      ((ρ.associatedRiemannianMetric hρ P).isVonNBounded x)
  apply (ρ.evalLinearEquiv p).isometryOfInner
  intro v w
  change inner ℝ (v p) (w p) = (ρ.associatedRiemannianMetric hρ P).inner x v w
  exact (ρ.associatedRiemannianMetric_inner hρ P x p v w).symm

@[simp]
theorem evalLinearIsometryEquiv_apply (ρ : Representation ℝ G W)
    (hρ : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w)
    {B : Type*} (P : B → Type*) [∀ x, Torsor G (P x)] (x : B) (p : P x)
    (v : P x →ₑ[ρ] W) :
    ρ.evalLinearIsometryEquiv hρ P x p v = v p := rfl

@[simp]
theorem evalLinearIsometryEquiv_symm_apply (ρ : Representation ℝ G W)
    (hρ : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w)
    {B : Type*} (P : B → Type*) [∀ x, Torsor G (P x)] (x : B) (p q : P x) (w : W) :
    letI : NormedAddCommGroup (P x →ₑ[ρ] W) :=
      ((ρ.associatedRiemannianMetric hρ P).toCore x).toNormedAddCommGroupOfTopology
        ((ρ.associatedRiemannianMetric hρ P).continuousAt x)
        ((ρ.associatedRiemannianMetric hρ P).isVonNBounded x)
    (ρ.evalLinearIsometryEquiv hρ P x p).symm w q = ρ (q /ₛ p) w := rfl

end Representation

namespace ContRepresentation

variable {G B W : Type*} [Group G]
  [TopologicalSpace G] [TopologicalSpace B] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {P : B → Type*} [∀ x, Torsor G (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace G P)] [FiberBundle G P] [IsPrincipalBundle P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [ChartedSpace H B]
  (n : ℕ∞ω)

def associatedContMDiffRiemannianMetric
    (ρ : ContRepresentation ℝ G W)
    (hρ : Continuous (fun g => ρ g))
    (horth : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w)
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ A hA e₀ he₀ hx₀
    ContMDiffRiemannianMetric I n W (fun x => P x →ₑ[ρ.toRepresentation] W) := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ A hA e₀ he₀ hx₀
  let g := ρ.toRepresentation.associatedRiemannianMetric horth P
  refine { inner := g.inner
           symm := g.symm
           pos := g.pos
           isVonNBounded := g.isVonNBounded
           contMDiff := ?_ }
  intro x
  simp only [contMDiffAt_section]
  let L : W →L[ℝ] W →L[ℝ] ℝ := innerSL ℝ
  apply (contMDiffAt_const (c := L)).congr_of_eventuallyEq
  filter_upwards [(e₀ x).open_baseSet.mem_nhds (hx₀ x)] with y hy
  ext v w
  simp only [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ (by exact hy) (by exact hy) (by trivial)]
  rw [Trivialization.coe_linearMapAt_of_mem _ (by trivial)]
  change g.inner y
      ((trivializationAt W (fun x => P x →ₑ[ρ.toRepresentation] W) x).symm y v)
      ((trivializationAt W (fun x => P x →ₑ[ρ.toRepresentation] W) x).symm y w) = inner ℝ v w
  rw [ρ.toRepresentation.associatedRiemannianMetric_inner horth P y ((e₀ x).principalSection y)]
  have heval (u : W) :
      ((trivializationAt W (fun x => P x →ₑ[ρ.toRepresentation] W) x).symm y u)
        ((e₀ x).principalSection y) = u := by
    have h := congrArg Prod.snd
      ((trivializationAt W (fun x => P x →ₑ[ρ.toRepresentation] W) x).apply_mk_symm
        (by exact hy) u)
    exact h
  rw [heval v, heval w]

theorem associatedContMDiffRiemannianMetric_toRiemannianMetric
    (ρ : ContRepresentation ℝ G W)
    (hρ : Continuous (fun g => ρ g))
    (horth : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w)
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ A hA e₀ he₀ hx₀
    (ρ.associatedContMDiffRiemannianMetric I n hρ horth A hA e₀ he₀ hx₀).toRiemannianMetric =
      ρ.toRepresentation.associatedRiemannianMetric horth P := by
  apply Bundle.RiemannianMetric.ext
  intro x v w
  rfl

end ContRepresentation
