import DifferentialGeometry.Topology.VectorField.Transport
import DifferentialGeometry.Topology.Morse.RegularLevel.RelativeVectorField
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set Filter Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace DifferentialGeometry.Topology.Morse

theorem exists_unitSpeedVectorField_on_quadratic_chart
    {E F H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] {I : ModelWithCorners ℝ F H} [IsManifold I 1 M]
    (χ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {f : M → ℝ} {c a : ℝ} (ha : a ≠ 0)
    (hnormal : ∀ y ∈ χ.source, f (χ y) = c + a / 2 * ‖y‖ ^ 2) :
    ∃ W : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I M))
        (χ '' (χ.source \ {0})) ∧
      (∀ x ∈ χ '' (χ.source \ {0}),
        mfderiv I 𝓘(ℝ, E) χ.symm x (W x) =
          -(a * ‖χ.symm x‖ ^ 2)⁻¹ • χ.symm x) ∧
      ∀ x ∈ χ '' (χ.source \ {0}),
        (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (W x)) = -1 := by
  let v : E → E := fun y => -(a * ‖y‖ ^ 2)⁻¹ • y
  let W := _root_.VectorField.mpullback I 𝓘(ℝ, E) χ.symm v
  have hcoords {x : M} (hx : x ∈ χ.target) :
      mfderiv I 𝓘(ℝ, E) χ.symm x (W x) = v (χ.symm x) :=
    (DifferentialGeometry.VectorField.isInvertible_mfderiv_partialDiffeomorph χ.symm
      (by simp) hx).self_apply_inverse _
  have hne {x : M} (hx : x ∈ χ '' (χ.source \ {0})) : χ.symm x ≠ 0 := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact fun h => hy.2 (mem_singleton_iff.mpr ((χ.left_inv hy.1).symm.trans h))
  have htarget {x : M} (hx : x ∈ χ '' (χ.source \ {0})) : x ∈ χ.target := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact χ.map_source hy.1
  refine ⟨W, ?_, fun _ hx => hcoords (htarget hx), ?_⟩
  · intro x hx
    have hv : ContDiffAt ℝ ∞ v (χ.symm x) := by
      exact ((contDiffAt_const.mul (contDiffAt_id.norm_sq ℝ)).inv
        (mul_ne_zero ha (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne hx))))).neg.smul contDiffAt_id
    exact (DifferentialGeometry.VectorField.contMDiffAt_mpullback_partialDiffeomorph χ.symm
      (m := ∞) (by simp) (htarget hx)
      (contMDiffAt_vectorSpace_iff_contDiffAt.mpr hv)).contMDiffWithinAt
  · intro x hx
    let q : E → ℝ := fun y => c + a / 2 * ‖y‖ ^ 2
    have hq (y : E) : HasFDerivAt q (a • innerSL ℝ y) y := by
      convert! ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (a / 2)).const_add c using 1
      ext z
      simp only [smul_apply, smul_eq_mul]
      ring
    have heq : f =ᶠ[𝓝 x] q ∘ χ.symm := by
      filter_upwards [χ.open_target.mem_nhds (htarget hx)] with z hz
      exact (congrArg f (χ.right_inv hz)).symm.trans (hnormal (χ.symm z) (χ.map_target hz))
    let A : F →L[ℝ] E := mfderiv I 𝓘(ℝ, E) χ.symm x
    let D : F →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f x
    have heqd : D = (mfderiv I 𝓘(ℝ, ℝ) (q ∘ χ.symm) x : F →L[ℝ] ℝ) := heq.mfderiv_eq
    have hmd : (mfderiv I 𝓘(ℝ, ℝ) (q ∘ χ.symm) x : F →L[ℝ] ℝ) =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) q (χ.symm x) : E →L[ℝ] ℝ).comp A :=
      mfderiv_comp x (hq (χ.symm x)).differentiableAt.mdifferentiableAt
        (χ.symm.mdifferentiableAt (by simp) (htarget hx))
    have hqmf : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) q (χ.symm x) : E →L[ℝ] ℝ) =
        fderiv ℝ q (χ.symm x) := mfderiv_eq_fderiv
    have hd : D = (fderiv ℝ q (χ.symm x)).comp A :=
      heqd.trans (hmd.trans (congrArg (fun B : E →L[ℝ] ℝ => B.comp A) hqmf))
    change D (W x) = (-1 : ℝ)
    rw [hd]
    change fderiv ℝ q (χ.symm x) (A (W x)) = -1
    rw [show A (W x) = v (χ.symm x) from hcoords (htarget hx), (hq (χ.symm x)).fderiv]
    change a * ⟪χ.symm x, -(a * ‖χ.symm x‖ ^ 2)⁻¹ • χ.symm x⟫ = -1
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    calc
      _ = -((a * ‖χ.symm x‖ ^ 2) * (a * ‖χ.symm x‖ ^ 2)⁻¹) := by ring
      _ = -1 := by
        rw [mul_inv_cancel₀ (mul_ne_zero ha (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne hx))))]

theorem exists_unitSpeedVectorField_radial_nhds_on_disjoint_charts
    {E F H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ F H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] {ι : Type*}
    (χ : ι → PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c α : ι → ℝ} (hα : ∀ i, α i ≠ 0)
    (hnormal : ∀ i, ∀ y ∈ (χ i).source, f (χ i y) = c i + α i / 2 * ‖y‖ ^ 2)
    {K : Set M} (hK : IsCompact K) (hregular : ∀ x ∈ K, ¬ IsCriticalPointAt I f x)
    {C : ι → Set M} (hC : IsCompact (⋃ i, C i))
    (hCχ : ∀ i, C i ⊆ χ i '' ((χ i).source \ {0}))
    (hdisjoint : Pairwise (fun i j => Disjoint
      (χ i '' ((χ i).source \ {0})) (χ j '' ((χ j).source \ {0})))) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport V) ∧
      (∀ x ∈ K, (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) = -1) ∧
      (∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) ∧
        (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) ≤ 0) ∧
      ∀ i, ∀ᶠ x in 𝓝ˢ (C i), x ∈ χ i '' ((χ i).source \ {0}) ∧
        mfderiv I 𝓘(ℝ, E) (χ i).symm x (V x) =
          -(α i * ‖(χ i).symm x‖ ^ 2)⁻¹ • (χ i).symm x := by
  classical
  choose W hW hcoords hWdf using fun i =>
    exists_unitSpeedVectorField_on_quadratic_chart (χ i) (hα i) (hnormal i)
  have hU (i : ι) : IsOpen (χ i '' ((χ i).source \ {0})) :=
    (χ i).toOpenPartialHomeomorph.isOpen_image_of_subset_source
      ((χ i).open_source.sdiff isClosed_singleton) sdiff_subset
  obtain ⟨V, hV, hsupp, hdf, hrate, heq⟩ :=
    exists_unitSpeedVectorField_eq_nhds_on_union hf hK hregular hC hU hCχ W hW hWdf
      (fun i j x hx => by
        by_cases hij : i = j
        · subst j
          rfl
        · exact False.elim ((Set.disjoint_left.mp (hdisjoint hij)) hx.1 hx.2))
  refine ⟨V, hV, hsupp, hdf, hrate, ?_⟩
  intro i
  filter_upwards [(hU i).mem_nhdsSet.mpr (hCχ i), heq i] with x hx hVW
  exact ⟨hx, hVW ▸ hcoords i x hx⟩

theorem exists_unitSpeedVectorField_radial_nhds_on_compact
    {E F H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ F H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (χ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c a : ℝ} (ha : a ≠ 0)
    (hnormal : ∀ y ∈ χ.source, f (χ y) = c + a / 2 * ‖y‖ ^ 2)
    {K C : Set M} (hK : IsCompact K) (hregular : ∀ x ∈ K, ¬ IsCriticalPointAt I f x)
    (hC : IsCompact C) (hCχ : C ⊆ χ '' (χ.source \ {0})) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport V) ∧
      (∀ x ∈ K, (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) = -1) ∧
      (∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) ∧
        (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) ≤ 0) ∧
      ∀ᶠ x in 𝓝ˢ C, x ∈ χ '' (χ.source \ {0}) ∧
        mfderiv I 𝓘(ℝ, E) χ.symm x (V x) = -(a * ‖χ.symm x‖ ^ 2)⁻¹ • χ.symm x := by
  have hdisjoint : Pairwise (fun _ _ : Unit =>
      Disjoint (χ '' (χ.source \ {0})) (χ '' (χ.source \ {0}))) := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))
  obtain ⟨V, hV, hsupp, hdf, hrate, hcoords⟩ :=
    exists_unitSpeedVectorField_radial_nhds_on_disjoint_charts
      (fun _ : Unit => χ) hf (fun _ => ha) (fun _ => hnormal) hK hregular
      (C := fun _ => C) (by simpa only [iUnion_const] using hC)
      (fun _ => hCχ) hdisjoint
  exact ⟨V, hV, hsupp, hdf, hrate, hcoords Unit.unit⟩


end DifferentialGeometry.Topology.Morse
