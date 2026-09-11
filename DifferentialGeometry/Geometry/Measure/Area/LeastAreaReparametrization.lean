import DifferentialGeometry.Geometry.Measure.Area.LeastArea
import DifferentialGeometry.Geometry.Measure.Area.Reparametrization
import DifferentialGeometry.Topology.LoopSpace.RadialHomeomorphism



noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]



def precomposeLipschitzContractibleLoop (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) (ψ : C(loopCircle, loopCircle)) {K : ℝ≥0}
    (hψ : LipschitzWith K ψ) : lipschitzContractibleLoop g := by
  refine ⟨⟨γ.val.val.comp ψ, γ.val.property.comp_left ψ⟩, ?_⟩
  obtain ⟨L, hL⟩ := γ.property
  refine ⟨L * K, fun s t => ?_⟩
  apply (hL (ψ s) (ψ t)).trans
  calc
    (L : ℝ≥0∞) * edist (ψ s) (ψ t) ≤ (L : ℝ≥0∞) * ((K : ℝ≥0∞) * edist s t) :=
      mul_le_mul' le_rfl (hψ s t)
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_competitor_precompose_circle (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) (ψ : loopCircle ≃ₜ loopCircle) {K L : ℝ≥0}
    (hψ : LipschitzWith K ψ) (hψ' : LipschitzWith L ψ.symm)
    {u : C(closedDisk, M)} (hu : u ∈ spanningDiskCompetitors g γ.val.val) :
    ∃ v ∈ spanningDiskCompetitors g
      (precomposeLipschitzContractibleLoop g γ ⟨ψ, ψ.continuous⟩ hψ).val.val,
      riemannianDiskArea g v = riemannianDiskArea g u := by
  obtain ⟨φ, hφtrace, Kφ, Lφ, hφ, hφ'⟩ := exists_radial_disk_reparametrization ψ hψ hψ'
  obtain ⟨htrace, Cu, hCu⟩ := hu
  let v : C(closedDisk, M) := u.comp ⟨φ, φ.continuous⟩
  have hvtrace : diskTrace v = (precomposeLipschitzContractibleLoop g γ ⟨ψ, ψ.continuous⟩ hψ).val.val := by
    ext θ
    change u (φ (diskBoundary θ)) = γ.val.val (ψ θ)
    rw [hφtrace]
    exact congrArg (fun f : freeLoop M => f (ψ θ)) htrace
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hu' : LipschitzWith Cu u := hCu
  have hv : LipschitzWith (Cu * Kφ) v := hu'.comp hφ
  refine ⟨v, ⟨hvtrace, Cu * Kφ, hv⟩, ?_⟩
  exact riemannianDiskArea_reparametrize g hCu φ hφ hφ'



theorem leastSpanningArea_precompose_le [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g)
    (ψ : loopCircle ≃ₜ loopCircle) {K L : ℝ≥0}
    (hψ : LipschitzWith K ψ) (hψ' : LipschitzWith L ψ.symm) :
    leastSpanningArea g (precomposeLipschitzContractibleLoop g γ ⟨ψ, ψ.continuous⟩ hψ) ≤
      leastSpanningArea g γ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u, hu, harea⟩ := exists_spanningDisk_area_lt g γ hε
  obtain ⟨v, hv, hvarea⟩ := exists_competitor_precompose_circle g γ ψ hψ hψ' hu
  have hle := leastSpanningArea_le_competitor g _ hv
  linarith



theorem leastSpanningArea_precompose [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g)
    (ψ : loopCircle ≃ₜ loopCircle) {K L : ℝ≥0}
    (hψ : LipschitzWith K ψ) (hψ' : LipschitzWith L ψ.symm) :
    leastSpanningArea g (precomposeLipschitzContractibleLoop g γ ⟨ψ, ψ.continuous⟩ hψ) =
      leastSpanningArea g γ := by
  apply le_antisymm (leastSpanningArea_precompose_le g γ ψ hψ hψ')
  have h := leastSpanningArea_precompose_le g
    (precomposeLipschitzContractibleLoop g γ ⟨ψ, ψ.continuous⟩ hψ) ψ.symm hψ' hψ
  have heq : precomposeLipschitzContractibleLoop g
      (precomposeLipschitzContractibleLoop g γ ⟨ψ, ψ.continuous⟩ hψ) ⟨ψ.symm, ψ.symm.continuous⟩ hψ' = γ := by
    apply Subtype.ext
    apply Subtype.ext
    ext θ
    exact congrArg γ.val.val (ψ.apply_symm_apply θ)
  rw [heq] at h
  exact h

end DifferentialGeometry.Geometry
