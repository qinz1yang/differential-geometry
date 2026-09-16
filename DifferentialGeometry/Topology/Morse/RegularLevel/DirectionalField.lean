import DifferentialGeometry.Topology.VectorField.Transport
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Morse

theorem exists_unitSpeedVectorField_on_directional_chart
    {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ F H} [IsManifold I 1 M]
    (χ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {f : M → ℝ} {q : E → ℝ}
    (hq : ContDiffOn ℝ ∞ q χ.source)
    (hnormal : ∀ y ∈ χ.source, f (χ y) = q y) (v : E) :
    ∃ W : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I M))
        (χ '' {y | y ∈ χ.source ∧ fderiv ℝ q y v ≠ 0}) ∧
      (∀ x ∈ χ '' {y | y ∈ χ.source ∧ fderiv ℝ q y v ≠ 0},
        mfderiv I 𝓘(ℝ, E) χ.symm x (W x) = -(fderiv ℝ q (χ.symm x) v)⁻¹ • v) ∧
      ∀ x ∈ χ '' {y | y ∈ χ.source ∧ fderiv ℝ q y v ≠ 0},
        (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (W x)) = -1 := by
  let w : E → E := fun y => -(fderiv ℝ q y v)⁻¹ • v
  let W := _root_.VectorField.mpullback I 𝓘(ℝ, E) χ.symm w
  have hcoords {x : M} (hx : x ∈ χ.target) :
      mfderiv I 𝓘(ℝ, E) χ.symm x (W x) = w (χ.symm x) :=
    (DifferentialGeometry.VectorField.isInvertible_mfderiv_partialDiffeomorph χ.symm
      (by simp) hx).self_apply_inverse _
  have htarget {x : M} (hx : x ∈ χ '' {y | y ∈ χ.source ∧ fderiv ℝ q y v ≠ 0}) :
      x ∈ χ.target := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact χ.map_source hy.1
  have hne {x : M} (hx : x ∈ χ '' {y | y ∈ χ.source ∧ fderiv ℝ q y v ≠ 0}) :
      fderiv ℝ q (χ.symm x) v ≠ 0 := by
    obtain ⟨y, hy, rfl⟩ := hx
    have hi : χ.symm.toPartialEquiv (χ.toPartialEquiv y) = y := χ.left_inv hy.1
    rw [hi]
    exact hy.2
  have hqAt {x : M} (hx : x ∈ χ.target) : ContDiffAt ℝ ∞ q (χ.symm x) :=
    hq.contDiffAt (χ.open_source.mem_nhds (χ.map_target hx))
  refine ⟨W, ?_, fun x hx => hcoords (htarget hx), ?_⟩
  · intro x hx
    have hd : ContDiffAt ℝ ∞ (fun y => fderiv ℝ q y v) (χ.symm x) :=
      ((hqAt (htarget hx)).fderiv_right (by simp)).clm_apply contDiffAt_const
    have hw : ContDiffAt ℝ ∞ w (χ.symm x) := (hd.inv (hne hx)).neg.smul_const v
    exact (DifferentialGeometry.VectorField.contMDiffAt_mpullback_partialDiffeomorph χ.symm
      (m := ∞) (by simp) (htarget hx)
      (contMDiffAt_vectorSpace_iff_contDiffAt.mpr hw)).contMDiffWithinAt
  · intro x hx
    have heq : f =ᶠ[𝓝 x] q ∘ χ.symm := by
      filter_upwards [χ.open_target.mem_nhds (htarget hx)] with z hz
      exact (congrArg f (χ.right_inv hz)).symm.trans (hnormal (χ.symm z) (χ.map_target hz))
    have hdq := (hqAt (htarget hx)).differentiableAt (by simp)
    let A : F →L[ℝ] E := mfderiv I 𝓘(ℝ, E) χ.symm x
    let D : F →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f x
    have heqd : D = (mfderiv I 𝓘(ℝ, ℝ) (q ∘ χ.symm) x : F →L[ℝ] ℝ) := heq.mfderiv_eq
    have hmd : (mfderiv I 𝓘(ℝ, ℝ) (q ∘ χ.symm) x : F →L[ℝ] ℝ) =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) q (χ.symm x) : E →L[ℝ] ℝ).comp A :=
      mfderiv_comp x hdq.mdifferentiableAt (χ.symm.mdifferentiableAt (by simp) (htarget hx))
    have hqmf : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) q (χ.symm x) : E →L[ℝ] ℝ) =
        fderiv ℝ q (χ.symm x) := mfderiv_eq_fderiv
    have hd : D = (fderiv ℝ q (χ.symm x)).comp A :=
      heqd.trans (hmd.trans (congrArg (fun B : E →L[ℝ] ℝ => B.comp A) hqmf))
    change D (W x) = (-1 : ℝ)
    rw [hd]
    change fderiv ℝ q (χ.symm x) (A (W x)) = -1
    rw [show A (W x) = w (χ.symm x) from hcoords (htarget hx)]
    simp only [w, map_smul, smul_eq_mul, neg_mul, inv_mul_cancel₀ (hne hx)]

end DifferentialGeometry.Topology.Morse
