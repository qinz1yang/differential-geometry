import DifferentialGeometry.Geometry.Exponential.GaussLemma.Framed
import DifferentialGeometry.Geometry.Exponential.RadialPath
import DifferentialGeometry.Topology.Manifold.Path.Segment
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Geometry.Metric.Distance.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)]

theorem riemannianEDistOf_pullback_zero
    (g : SmoothRiemannianMetric I M) (p : M) (U : Opens E)
    (hStar : StarConvex ℝ (0 : E) (U : Set E))
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞ (framedExpMap g p) U)
    (hdom : MapsTo (normalFrame g p) U (expDomain g p)) (z : U) :
    riemannianEDistOf
      (localPullMetric g (fun x : U => framedExpMap g p x)
        (isLocalDiffeomorph_restrict_open U hloc))
      ⟨0, hStar.mem ⟨z, z.property⟩⟩ z = ENNReal.ofReal ‖(z : E)‖ := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
    intro x v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  let f : U → M := fun x => framedExpMap g p x
  let hf := isLocalDiffeomorph_restrict_open U hloc
  let gPull := localPullMetric g f hf
  let origin : U := ⟨0, hStar.mem ⟨z, z.property⟩⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : U → Type _) :=
    ⟨gPull.toRiemannianMetric⟩
  change Manifold.riemannianEDist 𝓘(ℝ, E) origin z = ENNReal.ofReal ‖(z : E)‖
  apply le_antisymm
  · let modelPath := (Path.segment (0 : E) (z : E)).withSittingInstants
    have hModelMem : ∀ t : ℝ, modelPath.extend t ∈ (U : Set E) := by
      intro t
      apply hStar.segment_subset z.property
      have hm : modelPath.extend t ∈ range modelPath.extend := mem_range_self t
      rwa [Path.extend_range, Path.range_withSittingInstants, Path.range_segment] at hm
    let ρ : ℝ → U := fun t => ⟨modelPath.extend t, hModelMem t⟩
    have hModelSmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ modelPath.extend :=
      ((Path.segment (0 : E) (z : E)).isContMDiffWithSittingInstants_withSittingInstants
        (n := ⊤) (Path.contDiffOn_extend_segment 0 (z : E)).contMDiffOn).contMDiff
    have hρsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ρ := by
      intro t
      exact codRestr_contMDiffAt (V := U) hModelMem hModelSmooth.contMDiffAt
    have hρC1 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 ρ (Icc 0 1) :=
      (hρsmooth.of_le (by norm_num)).contMDiffOn
    have hρ0 : ρ 0 = origin := by
      apply Subtype.ext
      exact modelPath.extend_zero
    have hρ1 : ρ 1 = z := by
      apply Subtype.ext
      exact modelPath.extend_one
    let ray := radialPath g p (normalFrame g p (z : E)) (hdom z.property)
    have himage : f ∘ ρ = ray.withSittingInstants.extend := by
      rw [extend_radialPath_withSittingInstants]
      funext t
      change framedExpMap g p
        ((Path.segment (0 : E) (z : E)).withSittingInstants.extend t) = _
      rw [Path.extend_segment_withSittingInstants]
      simp only [AffineMap.lineMap_apply_module, smul_zero, zero_add]
      change expMap g p
          (normalFrame g p (Real.smoothTransition (3 * t - 1) • (z : E))) = _
      rw [map_smul]
    have hρlen : Manifold.pathELength 𝓘(ℝ, E) ρ 0 1 =
        ENNReal.ofReal ‖(z : E)‖ := by
      calc
        _ = Manifold.pathELength I (f ∘ ρ) 0 1 :=
          (localPull_pathLen g hEnorm f hf hρC1).symm
        _ = ray.withSittingInstants.riemannianELength (I := I) := by
          rw [himage]
          rfl
        _ = ray.riemannianELength (I := I) :=
          Path.riemannianELength_withSittingInstants ray
            ((contMDiffOn_extend_radialPath g p (normalFrame g p (z : E))
              (hdom z.property)).mdifferentiableOn (by decide))
        _ = ENNReal.ofReal ‖(z : E)‖ := by
          rw [riemannianELength_radialPath, normalFrame_sqrt]
          exact hEnorm
    exact (Manifold.riemannianEDist_le_pathELength
      hρC1 hρ0 hρ1 zero_le_one).trans_eq hρlen
  · by_contra hnot
    have hlt : Manifold.riemannianEDist 𝓘(ℝ, E) origin z <
        ENNReal.ofReal ‖(z : E)‖ := lt_of_not_ge hnot
    obtain ⟨γ, hγ0, hγ1, hγC1, hγlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hlt
    let η : ℝ → E := fun t => (γ t : E)
    have hη : ContDiffOn ℝ 1 η (Icc 0 1) := by
      apply contMDiffOn_iff_contDiffOn.mp
      exact (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U)
        (n := (1 : ℕ∞ω))).comp_contMDiffOn hγC1
    have hη0 : η 0 = 0 := by simp only [η, hγ0, origin]
    have hη1 : η 1 = (z : E) := by simp only [η, hγ1]
    have hlift := norm_le_pathELength_framedExpMap g hEnorm p zero_le_one hη0 hη
      (fun t _ => hdom (γ t).property)
    have hlen : Manifold.pathELength I (framedExpMap g p ∘ η) 0 1 =
        Manifold.pathELength 𝓘(ℝ, E) γ 0 1 :=
      localPull_pathLen g hEnorm f hf hγC1
    have hnorm_le : ENNReal.ofReal ‖(z : E)‖ ≤
        Manifold.pathELength 𝓘(ℝ, E) γ 0 1 := by
      rw [← hη1, ← hlen]
      exact hlift
    exact (not_lt_of_ge hnorm_le) hγlen

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
