import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.ContinuousOn

noncomputable section

open Metric Module
open scoped Manifold

universe u

namespace Poincare.Topology

theorem sphere_outward_volumeForm_ne_zero
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (ω : Orientation ℝ E (Fin (n + 1))) (x : sphere (0 : E) 1) :
    ((ω.volumeForm.curryLeft (x : E)).compLinearMap
      (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x).toLinearMap) ≠ 0 := by
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n (ne_zero_of_mem_unit_sphere x)
  let L := mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x
  have hlift (i : Fin n) : ∃ v : TangentSpace (𝓡 n) x, L v = (b i : E) := by
    have hmem : (b i : E) ∈ L.range := by
      rw [show L.range = (ℝ ∙ (x : E))ᗮ from range_mvfderiv_subtypeVal x]
      exact (b i).property
    exact hmem
  choose v hv using hlift
  have hb : Orthonormal ℝ (fun i : Fin n => (b i : E)) := by
    exact b.orthonormal.comp_linearIsometry (ℝ ∙ (x : E))ᗮ.subtypeₗᵢ
  have hx : Orthonormal ℝ (Matrix.vecCons (x : E) (fun i : Fin n => (b i : E))) := by
    apply orthonormal_vecCons_iff.mpr
    refine ⟨norm_eq_of_mem_sphere x, ?_, hb⟩
    intro i
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b i).property
  have hvol : |ω.volumeForm (Matrix.vecCons (x : E) (fun i : Fin n => (b i : E)))| = 1 := by
    rw [ω.abs_volumeForm_apply_of_pairwise_orthogonal hx.2]
    simp only [hx.norm_eq_one, Finset.prod_const_one]
  intro hz
  have heval := congrArg (fun f => f v) hz
  change ω.volumeForm (Matrix.vecCons (x : E) (fun i => L (v i))) = 0 at heval
  simp only [hv] at heval
  rw [heval, abs_zero] at hvol
  norm_num at hvol

def sphereOutwardOrientation
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (ω : Orientation ℝ E (Fin (n + 1))) (x : sphere (0 : E) 1) :
    Orientation ℝ (TangentSpace (𝓡 n) x) (Fin n) :=
  rayOfNeZero ℝ ((ω.volumeForm.curryLeft (x : E)).compLinearMap
    (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x).toLinearMap)
      (sphere_outward_volumeForm_ne_zero n ω x)

theorem sphereOutwardOrientation_neg
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (ω : Orientation ℝ E (Fin (n + 1))) (x : sphere (0 : E) 1) :
    sphereOutwardOrientation n (-ω) x = -sphereOutwardOrientation n ω x := by
  unfold sphereOutwardOrientation
  rw [neg_rayOfNeZero]
  congr 1
  ext v
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.curryLeft_apply_apply,
    Orientation.volumeForm_neg_orientation, AlternatingMap.neg_apply]

end Poincare.Topology

end

noncomputable section

open Metric Module
open scoped Manifold

namespace Poincare.Topology

local instance : Fact (finrank ℝ ℝ = 0 + 1) := ⟨by simp⟩

private theorem real_sphere_outward_form_value
    (x : sphere (0 : ℝ) 1) (v : Fin 0 → TangentSpace (𝓡 0) x) :
    (((Basis.singleton (Fin 1) ℝ).orientation.volumeForm.curryLeft (x : ℝ)).compLinearMap
      (mvfderiv (𝓡 0) ((↑) : sphere (0 : ℝ) 1 → ℝ) x).toLinearMap) v = (x : ℝ) := by
  have horth : Orthonormal ℝ (Basis.singleton (Fin 1) ℝ : Fin 1 → ℝ) := by simp
  let b : OrthonormalBasis (Fin 1) ℝ ℝ :=
    (Basis.singleton (Fin 1) ℝ).toOrthonormalBasis horth
  have hb : b.toBasis = Basis.singleton (Fin 1) ℝ :=
    Basis.toBasis_toOrthonormalBasis _ horth
  have hvol : (Basis.singleton (Fin 1) ℝ).orientation.volumeForm =
      (Basis.singleton (Fin 1) ℝ).det :=
    ((Basis.singleton (Fin 1) ℝ).orientation.volumeForm_robust b
      (congrArg (fun e : Basis (Fin 1) ℝ ℝ => e.orientation) hb)).trans
        (congrArg (fun e : Basis (Fin 1) ℝ ℝ => e.det) hb)
  rw [AlternatingMap.compLinearMap_apply, AlternatingMap.curryLeft_apply_apply,
    hvol, Basis.det_apply, Matrix.det_fin_one]
  simp only [Basis.toMatrix_apply, Matrix.cons_val_zero, Basis.singleton_repr]

theorem sphereOutwardOrientation_real_positive :
    sphereOutwardOrientation 0 (Basis.singleton (Fin 1) ℝ).orientation
      (⟨1, by norm_num⟩ : sphere (0 : ℝ) 1) = positiveOrientation := by
  unfold sphereOutwardOrientation
  change rayOfNeZero ℝ _ _ =
    rayOfNeZero ℝ (AlternatingMap.constLinearEquivOfIsEmpty (1 : ℝ)) _
  congr 1
  ext v
  change (((Basis.singleton (Fin 1) ℝ).orientation.volumeForm.curryLeft (1 : ℝ)).compLinearMap
    (mvfderiv (𝓡 0) ((↑) : sphere (0 : ℝ) 1 → ℝ)
      (⟨1, by norm_num⟩ : sphere (0 : ℝ) 1)).toLinearMap) v = 1
  exact real_sphere_outward_form_value _ v

theorem sphereOutwardOrientation_real_negative :
    sphereOutwardOrientation 0 (Basis.singleton (Fin 1) ℝ).orientation
      (⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1) = -positiveOrientation := by
  unfold sphereOutwardOrientation
  change rayOfNeZero ℝ _ _ =
    rayOfNeZero ℝ (-(AlternatingMap.constLinearEquivOfIsEmpty (1 : ℝ))) _
  congr 1
  ext v
  change (((Basis.singleton (Fin 1) ℝ).orientation.volumeForm.curryLeft (-1 : ℝ)).compLinearMap
    (mvfderiv (𝓡 0) ((↑) : sphere (0 : ℝ) 1 → ℝ)
      (⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1)).toLinearMap) v = -1
  exact real_sphere_outward_form_value _ v

end Poincare.Topology

end

noncomputable section

open Bundle Metric Module Set
open scoped Manifold

universe u₁

namespace Poincare.Topology

private theorem sphere_chart_tangent_vector_continuousOn
    {E : Type u₁} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (p : sphere (0 : E) 1) (v : EuclideanSpace ℝ (Fin n)) :
    ContinuousOn (fun x : sphere (0 : E) 1 =>
      mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x
        ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).symmL ℝ x v))
      (chartAt (EuclideanSpace ℝ (Fin n)) p).source := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have hs : ContinuousOn (fun x : sphere (0 : E) 1 =>
      TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x (e.symmL ℝ x v)) e.baseSet := by
    have hc := e.continuousOn_symm.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun x hx => (show (x, v) ∈ e.baseSet ×ˢ univ from ⟨hx, mem_univ _⟩))
    apply hc.congr
    intro x hx
    change TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x (e.symmL ℝ x v) =
      TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x (e.symm x v)
    rw [e.symmL_apply hx]
  have ht : Continuous (tangentMap (𝓡 n) 𝓘(ℝ, E)
      ((↑) : sphere (0 : E) 1 → E)) :=
    (contMDiff_coe_sphere (m := 1)).continuous_tangentMap le_rfl
  have hp : Continuous (fun z : TangentBundle 𝓘(ℝ, E) E =>
      NormedSpace.fromTangentSpace z.proj z.2) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).continuous.snd
  have h := (hp.comp ht).comp_continuousOn hs
  change ContinuousOn (fun x : sphere (0 : E) 1 =>
      mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (e.symmL ℝ x v)) e.baseSet at h
  simpa only [e, TangentBundle.trivializationAt_baseSet] using h

private theorem sphere_outward_chart_volume_continuousOn
    {E : Type u₁} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (ω : Orientation ℝ E (Fin (n + 1))) (p : sphere (0 : E) 1)
    (b : Fin n → EuclideanSpace ℝ (Fin n)) :
    ContinuousOn (fun x : sphere (0 : E) 1 =>
      ω.volumeForm (Matrix.vecCons (x : E) (fun i =>
        mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x
          ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).symmL ℝ x
            (b i)))))
      (chartAt (EuclideanSpace ℝ (Fin n)) p).source := by
  have hω : Continuous ω.volumeForm := ω.volumeForm.continuous_of_bound 1 (by
    intro v
    simpa only [one_mul, Real.norm_eq_abs] using ω.abs_volumeForm_apply_le v)
  exact hω.comp_continuousOn (continuous_subtype_val.continuousOn.matrixVecCons
    (continuousOn_pi.mpr fun i => sphere_chart_tangent_vector_continuousOn n p (b i)))

private theorem sphere_outward_chart_volume_ne_zero
    {E : Type u₁} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (ω : Orientation ℝ E (Fin (n + 1))) (p x : sphere (0 : E) 1)
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ω.volumeForm (Matrix.vecCons (x : E) (fun i =>
      mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x
        ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).symmL ℝ x
          (b i)))) ≠ 0 := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have hxe : x ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using hx
  let A := e.continuousLinearEquivAt ℝ x hxe
  let f := (ω.volumeForm.curryLeft (x : E)).compLinearMap
    (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x).toLinearMap
  have hf : f ≠ 0 := sphere_outward_volumeForm_ne_zero n ω x
  have h := (AlternatingMap.map_basis_ne_zero_iff (b.map A.symm.toLinearEquiv) f).mpr hf
  change ω.volumeForm (Matrix.vecCons (x : E) (fun i =>
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (A.symm (b i)))) ≠ 0 at h
  simpa only [A, Trivialization.symm_continuousLinearEquivAt_eq] using h

end Poincare.Topology

end

noncomputable section

open Bundle Filter Metric Module Set
open scoped Manifold Topology

universe u₂ v₂ w₂

namespace Poincare.Topology

private theorem alternating_form_ray_isLocallyConstant
    {X : Type u₂} [TopologicalSpace X]
    {V : Type v₂} [AddCommGroup V] [Module ℝ V]
    {ι : Type w₂} [Finite ι]
    (b : Basis ι ℝ V) (f : X → V [⋀^ι]→ₗ[ℝ] ℝ)
    (hf : ∀ x, f x ≠ 0) (hc : Continuous (fun x => f x b)) :
    IsLocallyConstant (fun x => rayOfNeZero ℝ (f x) (hf x)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hx : f x b ≠ 0 := (AlternatingMap.map_basis_ne_zero_iff b (f x)).mpr (hf x)
  have hprod : ContinuousAt (fun y => f y b * f x b) x :=
    hc.continuousAt.mul continuousAt_const
  have hpos : 0 < f x b * f x b := mul_self_pos.mpr hx
  filter_upwards [hprod.eventually (Ioi_mem_nhds hpos)] with y hy
  apply (ray_eq_iff _ _).mpr
  rw [(f y).eq_smul_basis_det b, (f x).eq_smul_basis_det b]
  exact sameRay_smul_smul_of_mul_nonneg hy.le

theorem sphereOutwardOrientation_chart_isLocallyConstant
    {E : Type u₂} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (ω : Orientation ℝ E (Fin (n + 1))) (p : sphere (0 : E) 1) :
    IsLocallyConstant (fun x : (chartAt (EuclideanSpace ℝ (Fin n)) p).source =>
      Orientation.map (Fin n)
        ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).continuousLinearEquivAt
          ℝ (x : sphere (0 : E) 1)
            (by simpa only [TangentBundle.trivializationAt_baseSet] using x.property)).toLinearEquiv
        (sphereOutwardOrientation n ω x)) := by
  let U := (chartAt (EuclideanSpace ℝ (Fin n)) p).source
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  let A (x : U) := e.continuousLinearEquivAt ℝ (x : sphere (0 : E) 1)
    (by simpa only [e, U, TangentBundle.trivializationAt_baseSet] using x.property)
  let f (x : U) := (((ω.volumeForm.curryLeft ((x : sphere (0 : E) 1) : E)).compLinearMap
    (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x).toLinearMap).compLinearMap
      (A x).symm.toLinearEquiv.toLinearMap)
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have heval (x : U) : f x b =
      ω.volumeForm (Matrix.vecCons ((x : sphere (0 : E) 1) : E) (fun i =>
        mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (e.symmL ℝ x (b i)))) := by
    change ω.volumeForm (Matrix.vecCons ((x : sphere (0 : E) 1) : E) (fun i =>
      mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x ((A x).symm (b i)))) = _
    simp only [A, Trivialization.symm_continuousLinearEquivAt_eq]
  have hf (x : U) : f x ≠ 0 := by
    apply (AlternatingMap.map_basis_ne_zero_iff b (f x)).mp
    rw [heval]
    exact sphere_outward_chart_volume_ne_zero n ω p x x.property b
  have hc : Continuous (fun x : U => f x b) := by
    have h := (sphere_outward_chart_volume_continuousOn n ω p b).domRestrict
    exact h.congr (fun x => (heval x).symm)
  have hlocal := alternating_form_ray_isLocallyConstant b f hf hc
  have hmap (x : U) :
      Orientation.map (Fin n) (A x).toLinearEquiv (sphereOutwardOrientation n ω x) =
        rayOfNeZero ℝ (f x) (hf x) := rfl
  change IsLocallyConstant (fun x : U =>
    Orientation.map (Fin n) (A x).toLinearEquiv (sphereOutwardOrientation n ω x))
  simpa only [hmap] using hlocal

end Poincare.Topology

end
