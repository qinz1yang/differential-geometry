import DifferentialGeometry.Bundle.Associated.Topology
import DifferentialGeometry.Topology.GroupAction.Module
import DifferentialGeometry.Geometry.Metric.BundlePullback
import Mathlib.Analysis.InnerProductSpace.LinearMap

noncomputable section

open Set Bundle

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
