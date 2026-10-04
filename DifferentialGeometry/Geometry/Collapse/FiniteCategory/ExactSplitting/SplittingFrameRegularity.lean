import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFrameLinear
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteRegularityProof
import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.CoerciveInverseRegularity

/-!
# Finite regularity of the actual splitting frame

The original metric and coordinate differential determine the frame in each native tangent
trivialization. The local metric inverse retains that same frame at every base point.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] {r : ℕ∞}
  {F Y : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace Y]


local instance frameRegularityComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [I.Boundaryless] [IsRiemannianManifold I M] [CompleteSpace M] in
private def frameLocalMetric
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (a x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  let A : E →L[ℝ] E := (trivializationAt E (TangentSpace I) a).symmL ℝ x
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner x
  ((ContinuousLinearMap.compL ℝ E E ℝ).flip A).comp (G.comp A)

omit [I.Boundaryless] [IsRiemannianManifold I M] [CompleteSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem contMDiffAt_frameLocalMetric
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (a : M) : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ((r : ℕ∞ω) + 1)
      (frameLocalMetric g a) a := by
  apply contMDiffAt_clm_of_pointwise
  intro v
  apply contMDiffAt_clm_of_pointwise
  intro w
  have hv := DifferentialGeometry.Geometry.contMDiffAt_tangent_symmL_frame
    (I := I) (n := ((r : ℕ∞ω) + 1)) a v
  have hw := DifferentialGeometry.Geometry.contMDiffAt_tangent_symmL_frame
    (I := I) (n := ((r : ℕ∞ω) + 1)) a w
  have h := g.contMDiff.contMDiffAt.clm_bundle_apply₂ hv hw
  exact (contMDiffAt_totalSpace.mp h).2

private def frameLocalDifferential (e : M ≃ᵢ WithLp 2 (F × Y)) (a x : M) : E →L[ℝ] F :=
  (mvfderiv I (fun y => (e y).fst) x).comp
    ((trivializationAt E (TangentSpace I) a).symmL ℝ x)

private theorem contMDiffAt_frameLocalDifferential
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (a : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) ((r : ℕ∞ω) + 1) (frameLocalDifferential (I := I) e a) a := by
  have h := (contMDiff_splitting_fst (I := I) g hr hnorm e a).mfderiv_const
    (I := I) (I' := 𝓘(ℝ, F))
    (m := ((r : ℕ∞ω) + 1)) (by norm_num [add_assoc])
  apply h.congr_of_eventuallyEq
  filter_upwards [] with x
  ext v
  simp [frameLocalDifferential, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, mvfderiv]
  rfl

omit [I.Boundaryless] [IsRiemannianManifold I M] [CompleteSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem frameLocalMetric_coercive
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (a x : M) (hx : x ∈ (trivializationAt E (TangentSpace I) a).baseSet) :
    IsCoercive (frameLocalMetric g a x) := by
  let tau := trivializationAt E (TangentSpace I) a
  have hi : Function.Injective (tau.symmL ℝ x) := by
    rw [← tau.symm_continuousLinearEquivAt_eq' hx]
    exact (tau.continuousLinearEquivAt ℝ x hx).symm.injective
  apply ContinuousLinearMap.isCoercive_of_posDef
  intro v hv
  apply g.pos
  intro hz
  exact hv (hi (hz.trans (map_zero _).symm))

omit [I.Boundaryless] [IsRiemannianManifold I M] [CompleteSpace M]
  [FiniteDimensional ℝ F] in
private theorem frameLocalCoordinates_eq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (a x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) a).baseSet) (u : F) :
    (trivializationAt E (TangentSpace I) a).continuousLinearMapAt ℝ x
        (splittingFrame g e x u) =
      coerciveBilinearInverse (frameLocalMetric g a x)
        ((innerSL ℝ u).comp (frameLocalDifferential (I := I) e a x)) := by
  let tau := trivializationAt E (TangentSpace I) a
  have hc := frameLocalMetric_coercive g a x hx
  rw [← sharpCLM_eq_coerciveBilinearInverse hc]
  apply hc.bilin_injective
  rw [IsCoercive.sharpCLM_apply, hc.apply_sharp]
  ext v
  change g.inner x (tau.symmL ℝ x (tau.continuousLinearMapAt ℝ x
    (splittingFrame g e x u))) (tau.symmL ℝ x v) =
      inner ℝ u (mvfderiv I (fun y => (e y).fst) x (tau.symmL ℝ x v))
  erw [tau.symmL_continuousLinearMapAt hx]
  exact inner_splittingFrame_left g e x u (tau.symmL ℝ x v)

theorem contMDiff_splittingFrame_section
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ((r : ℕ∞ω) + 1)
      (fun x => (⟨x, splittingFrame g e x⟩ :
        TotalSpace (F →L[ℝ] E) (fun x => Bundle.Trivial M F x →L[ℝ] TangentSpace I x))) := by
  intro a
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_pointwise
  intro u
  have hb := contMDiffAt_frameLocalMetric g a
  have hc := frameLocalMetric_coercive g a a (mem_baseSet_trivializationAt E _ a)
  have hi := contMDiffAt_coerciveBilinearInverse hb hc
  have hd := contMDiffAt_frameLocalDifferential g hr hnorm e a
  let L : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] ℝ :=
    ContinuousLinearMap.compL ℝ E F ℝ (innerSL ℝ u)
  have hcov := L.contDiff.contMDiff.contMDiffAt.comp a hd
  have h := hi.clm_apply hcov
  apply h.congr_of_eventuallyEq
  let tau := trivializationAt E (TangentSpace I) a
  filter_upwards [tau.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ a)] with x hx
  change _ = coerciveBilinearInverse (frameLocalMetric g a x)
    ((innerSL ℝ u).comp (frameLocalDifferential (I := I) e a x))
  rw [← frameLocalCoordinates_eq g e a x hx u]
  simp [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_apply]

theorem contMDiff_splittingFrame_apply
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    ContMDiff ((𝓘(ℝ, F)).prod I) I.tangent ((r : ℕ∞ω) + 1)
      (fun p : F × M => (⟨p.2, splittingFrame g e p.2 p.1⟩ : TangentBundle I M)) := by
  have hf := (contMDiff_splittingFrame_section g hr hnorm e).comp
    (contMDiff_snd : ContMDiff ((𝓘(ℝ, F)).prod I) I ((r : ℕ∞ω) + 1) (fun p : F × M => p.2))
  have hu : ContMDiff ((𝓘(ℝ, F)).prod I) (I.prod 𝓘(ℝ, F)) ((r : ℕ∞ω) + 1)
      (fun p : F × M => (⟨p.2, p.1⟩ : TotalSpace F (Bundle.Trivial M F))) := by
    intro p
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_snd, ?_⟩
    convert contMDiffAt_fst using 1
    rfl
  exact hf.clm_bundle_apply hu

end DifferentialGeometry.Geometry.ExactSplitting
