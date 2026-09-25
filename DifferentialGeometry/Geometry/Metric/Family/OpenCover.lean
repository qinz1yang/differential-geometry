import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Bundle.LocalFrameOpenRestriction
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenCover

set_option autoImplicit false
noncomputable section
open Set Bundle TopologicalSpace Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Coordinates
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tensor0SFamilyContinuousOnSet.of_open_cover
    {s : ℕ} {K : Set ℝ} {ι : Type*} (U : ι → Opens M)
    (A : (t : ℝ) → (x : M) → Tensor0SSpace s I x)
    (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hA : ∀ i, tensor0SFamilyContinuousOnSet (I := I) s K
      (fun t (x : U i) => A t (x : M))) :
    tensor0SFamilyContinuousOnSet (I := I) s K A := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  choose idx hidx using hcover
  let N (x : M) : Set M := (U (idx x) : Set M) ∩
    (trivializationAt E (TangentSpace I) x).baseSet
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp A N
    (fun x => inter_mem ((U (idx x)).isOpen.mem_nhds (hidx x))
      ((Trivialization.open_baseSet _).mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)))
  intro x j
  rw [continuousOn_iff_continuous_domRestrict]
  let P := {q : {t : ℝ // t ∈ K} × M // q.2 ∈ N x}
  let b : P → U (idx x) := fun p => ⟨p.1.2, p.2.1⟩
  have hb : Continuous b := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hslot (k : Fin s) : Continuous
      (fun p : P => TotalSpace.mk' E (E := fun y : U (idx x) => TangentSpace I y) (b p)
        (chartBasisVecFiber (I := I) x (j k) (p.1.2) : TangentSpace I (b p))) := by
    have hsm := (chartBasisVec_contMDiffOn (I := I) x (j k)).mpullback_vectorField_preimage
      (contMDiff_subtype_val (I := I) (U := U (idx x)) (n := ∞))
      (by intro y _; rw [mfderiv_subtype_val]; exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩)
      (by simp)
    have hc := hsm.continuousOn.comp_continuous hb (fun p => p.2.2)
    have heq (y : U (idx x)) : VectorField.mpullback I I
        (Subtype.val : U (idx x) → M) (chartBasisVecFiber (I := I) x (j k)) y =
        chartBasisVecFiber (I := I) x (j k) (y : M) := by
      simp only [VectorField.mpullback, mfderiv_subtype_val]
      change (ContinuousLinearMap.id ℝ E).inverse _ = _
      rw [ContinuousLinearMap.inverse_id]
      rfl
    simp only [heq] at hc
    exact hc
  exact (hA (idx x)).eval_continuous
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
    (fun p : P => p.1.1.2) hb hslot

end DifferentialGeometry.Geometry.Curvature

end

noncomputable section
open Set Bundle TopologicalSpace
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Coordinates
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem MetricFamilySmoothOn.of_open_cover
    {D : RealTimeInterval}
    {g : ℝ → SmoothRiemannianMetric I M}
    {ι : Type*} (U : ι → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hg : ∀ i, MetricFamilySmoothOn D (fun t => (g t).restrictOpen (U i))) :
    MetricFamilySmoothOn D g := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x v w
    obtain ⟨i, hxi⟩ := hcover x
    exact (hg i).coeff ⟨x, hxi⟩ v w
  · intro x v w
    obtain ⟨i, hxi⟩ := hcover x
    exact (hg i).coeff_cont ⟨x, hxi⟩ v w
  · apply tensor0SFamilyContinuousOnSet.of_open_cover U _ hcover
    intro i
    exact (hg i).metricTensor_cont
  · intro Idx _ frame u hframe i j
    apply contMDiffOn_of_open_cover_prod U hcover
    intro k
    exact (hg k).frameCompSmooth _ (hframe.restrict_open (U k)) i j

theorem chartGramMatrix_joint_contMDiffOn_of_restrict_open_cover
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ)
    {ι : Type*} (U : ι → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hg : ∀ k (x : U k) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × U k => chartGramMatrix ((g p.1).restrictOpen (U k)) x p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x).baseSet)) :
    ∀ (x : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (g p.1) x p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x).baseSet) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro x i j
  apply contMDiffOn_of_open_cover_prod U hcover
  intro k
  have hm := metricCLMSection_jointContMDiffOn_of_chartGram_on
    (fun t => (g t).restrictOpen (U k)) J (hg k)
  have hvec (a : Fin (Module.finrank ℝ E)) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : U k => (⟨y, chartBasisVecFiber (I := I) x a (y : M)⟩ :
        TotalSpace E (fun z : U k => TangentSpace I z)))
      (Subtype.val ⁻¹' (trivializationAt E (TangentSpace I) x).baseSet) := by
    have hs := (chartBasisVec_contMDiffOn (I := I) x a).mpullback_vectorField_preimage
      (contMDiff_subtype_val (I := I) (U := U k) (n := ∞))
      (by intro y _; rw [mfderiv_subtype_val]; exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩)
      (by simp)
    have heq (y : U k) : VectorField.mpullback I I (Subtype.val : U k → M)
        (chartBasisVecFiber (I := I) x a) y = chartBasisVecFiber (I := I) x a (y : M) := by
      simp only [VectorField.mpullback, mfderiv_subtype_val]
      change (ContinuousLinearMap.id ℝ E).inverse _ = _
      rw [ContinuousLinearMap.inverse_id]
      rfl
    simpa only [heq] using hs
  have hsnd : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (Prod.snd : ℝ × U k → U k)
      (J ×ˢ (Subtype.val ⁻¹' (trivializationAt E (TangentSpace I) x).baseSet)) :=
    contMDiffOn_snd
  have hv := (hvec i).comp hsnd (fun p hp => hp.2)
  have hw := (hvec j).comp hsnd (fun p hp => hp.2)
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := U k)) (E₂ := TangentSpace I (M := U k))
    (E₃ := Bundle.Trivial (U k) ℝ) (b := fun p : ℝ × U k => p.2)
    (hm.mono (prod_mono Subset.rfl (subset_univ _))) hv hw
  intro p hp
  have h := happ p hp
  rw [Bundle.contMDiffWithinAt_totalSpace] at h
  exact h.2

end DifferentialGeometry.Geometry.Curvature
end
