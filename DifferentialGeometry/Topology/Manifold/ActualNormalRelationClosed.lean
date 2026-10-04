import DifferentialGeometry.Topology.Manifold.NearestNormalDiscCoordinates
import DifferentialGeometry.Topology.Manifold.SmoothMapDifferentialCoordinates

/-! The normal relation of the actual embedding is closed in its native ambient product. -/

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {k : ℕ} {Z : Set H} [ChartedSpace (Fin k → ℝ) Z]
  [IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z]

private theorem actualTangentCoordinate_eq (p x : Z)
    (hx : x ∈ (chartAt (Fin k → ℝ) p).source) :
    inTangentCoordinates 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) id
      (Subtype.val : Z → H) (mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) Subtype.val) p x =
      (mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : Z → H) x).comp
        ((DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv
          𝓘(ℝ, Fin k → ℝ) p x hx).symm : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) := by
  have h := inTangentCoordinates_eq_mfderiv_comp (I := 𝓘(ℝ, Fin k → ℝ)) (I' := 𝓘(ℝ, H))
    (f := id) (g := (Subtype.val : Z → H))
    (ϕ := mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : Z → H)) hx (mem_univ _)
  have hc : (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (extChartAt 𝓘(ℝ, H) (p : H)) (x : H) :
      H →L[ℝ] H) = ContinuousLinearMap.id ℝ H := by
    rw [extChartAt_model_space_eq_id]
    change mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (id : H → H) (x : H) = _
    rw [mfderiv_id]
    rfl
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun A : (Fin k → ℝ) →L[ℝ] H => A v) h
  change inTangentCoordinates 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) id
    (Subtype.val : Z → H) (mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) Subtype.val) p x v =
    (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (extChartAt 𝓘(ℝ, H) (p : H)) (x : H))
      ((mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : Z → H) x)
        (mfderivWithin 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, Fin k → ℝ)
          (extChartAt 𝓘(ℝ, Fin k → ℝ) p).symm (range 𝓘(ℝ, Fin k → ℝ))
          (extChartAt 𝓘(ℝ, Fin k → ℝ) p x) v)) at hv
  rw [hc] at hv
  exact hv.trans (congrArg (mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : Z → H) x)
    (DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv_symm_apply
      𝓘(ℝ, Fin k → ℝ) p x hx v).symm)

theorem isClosed_actualNormalRelation
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H)) :
    IsClosed {yn : Z × H | yn.2 ∈ (actualZeroSetTangentSpace k Z yn.1)ᗮ} := by
  apply isClosed_of_closure_subset
  intro yn hyn
  let A : Z → (Fin k → ℝ) →L[ℝ] H := inTangentCoordinates
    𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) id (Subtype.val : Z → H)
      (mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) Subtype.val) yn.1
  have hA : ContinuousAt A yn.1 :=
    (hemb.contMDiff.contMDiffAt.mfderiv_const (m := 0) (by simp)).continuousAt
  let O : Set (Z × H) := {w | w.1 ∈ (chartAt (Fin k → ℝ) yn.1).source}
  have hO : IsOpen O := (chartAt (Fin k → ℝ) yn.1).open_source.preimage continuous_fst
  have hclosure : yn ∈ closure
      ({w : Z × H | w.2 ∈ (actualZeroSetTangentSpace k Z w.1)ᗮ} ∩ O) :=
    hO.closure_inter ⟨hyn, mem_chart_source (Fin k → ℝ) yn.1⟩
  have hzero (v : Fin k → ℝ) : inner ℝ yn.2 (A yn.1 v) = 0 := by
    have hcont : ContinuousAt (fun w : Z × H => inner ℝ w.2 (A w.1 v)) yn :=
      continuous_snd.continuousAt.inner ((hA.comp continuous_fst.continuousAt).clm_apply
        continuousAt_const)
    apply hcont.continuousWithinAt.eq_const_of_mem_closure hclosure
    rintro w ⟨hw, hwo⟩
    change w.2 ∈ (actualZeroSetTangentSpace k Z w.1)ᗮ at hw
    rw [Submodule.mem_orthogonal'] at hw
    apply hw
    change A w.1 v ∈ actualZeroSetTangentSpace k Z w.1
    dsimp only [A]
    rw [actualTangentCoordinate_eq yn.1 w.1 hwo]
    exact ⟨_, rfl⟩
  change yn.2 ∈ (actualZeroSetTangentSpace k Z yn.1)ᗮ
  rw [Submodule.mem_orthogonal']
  let D : (Fin k → ℝ) →L[ℝ] H :=
    mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : Z → H) yn.1
  change ∀ u ∈ LinearMap.range D.toLinearMap, inner ℝ yn.2 u = 0
  rintro u ⟨v, rfl⟩
  let e := DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv
    𝓘(ℝ, Fin k → ℝ) yn.1 yn.1 (mem_chart_source (Fin k → ℝ) yn.1)
  have hh := hzero (e v)
  dsimp only [A] at hh
  rw [actualTangentCoordinate_eq yn.1 yn.1 (mem_chart_source (Fin k → ℝ) yn.1)] at hh
  change inner ℝ yn.2
    ((mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : Z → H) yn.1)
      (e.symm (e v))) = 0 at hh
  rw [e.symm_apply_apply] at hh
  exact hh

end GC.MetricGeometry
