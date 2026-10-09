import DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacher
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz
import DifferentialGeometry.Analysis.Calculus.Interpolation.FiniteClosedCover
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- A continuous lift of a metric-Lipschitz disk through a local diffeomorphism
is metric-Lipschitz for the literal pullback metric. The same lift selects each
inverse branch; no smooth extension of the lift is assumed. -/
theorem exists_lipschitz_disk_lift_of_localDiffeomorph
    (g : SmoothRiemannianMetric 𝓘(ℝ, F) N) (p : M → N)
    (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p x))
    (hps : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (u : C(closedDisk, N)) {L : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (uLift : C(closedDisk, M)) (hmap : ∀ z, p (uLift z) = u z) :
    ∃ K : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf (g.pullback p hp himm) (uLift z) (uLift w) ≤
        (K : ℝ≥0∞) * edist z w := by
  classical
  let gLift := g.pullback p hp himm
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨gLift.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨gLift.inner, gLift.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, F) : N → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (TangentSpace 𝓘(ℝ, F) : N → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  have : LocallyCompactSpace N := Manifold.locallyCompact_of_finiteDimensional (M := N) 𝓘(ℝ, F)
  have : RegularSpace N := inferInstance
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : PseudoEMetricSpace N := .ofRiemannianMetric 𝓘(ℝ, F) N
  have hmetric (x y : M) : edist x y = riemannianEDistOf gLift x y := rfl
  let U := diskExtension u
  let V := diskExtension uLift
  have hU : LipschitzWith L U := diskExtension_riemannian_lipschitz g hu
  have hV : Continuous V := uLift.continuous.comp diskRetraction_lipschitz.continuous
  have hproj (z : ℂ) : p (V z) = U z := hmap (diskRetraction z)
  have hlocal (x : closedDisk) : ∃ (C : ℝ≥0) (W : Set ℂ),
      IsOpen W ∧ (x : ℂ) ∈ W ∧ LipschitzOnWith C V W := by
    obtain ⟨φ, hx, hφ⟩ := hps (V x)
    have htarget : U x ∈ φ.target := by
      rw [← hproj x, hφ hx]
      exact φ.map_source hx
    have hinverse : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) 1 φ.symm (U x) :=
      (φ.contMDiffOn_invFun.contMDiffAt (φ.open_target.mem_nhds htarget)).of_le (by simp)
    obtain ⟨C, A, hA, hCA⟩ := hinverse.exists_lipschitzOnWith
    have hpre : U ⁻¹' A ∩ V ⁻¹' φ.source ∈ 𝓝 (x : ℂ) :=
      inter_mem (hU.continuous.continuousAt hA)
        (hV.continuousAt.preimage_mem_nhds (φ.open_source.mem_nhds hx))
    obtain ⟨W, hWA, hW, hxW⟩ := mem_nhds_iff.mp hpre
    have hinv (z : ℂ) (hz : z ∈ W) : φ.symm (U z) = V z := by
      rw [← hproj z, hφ (hWA hz).2]
      exact φ.left_inv (hWA hz).2
    refine ⟨C * L, W, hW, hxW, ?_⟩
    intro z hz w hw
    rw [← hinv z hz, ← hinv w hw]
    exact (hCA (hWA hz).1 (hWA hw).1).trans
      ((mul_le_mul_right (hU z w) (C : ℝ≥0∞)).trans_eq (by
        rw [ENNReal.coe_mul, mul_assoc]))
  choose C W hW hxW hCW using hlocal
  obtain ⟨s, hs⟩ := (isCompact_closedBall (0 : ℂ) 1).elim_finite_subcover W hW
    (fun z hz => mem_iUnion_of_mem (⟨z, hz⟩ : closedDisk) (hxW ⟨z, hz⟩))
  have hcomp : LipschitzOnWith (s.sup C) V (Metric.closedBall (0 : ℂ) 1) := by
    apply Analysis.lipschitzOnWith_of_eventually_edist_le (convex_closedBall (0 : ℂ) 1)
    intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hs hz)
    filter_upwards [mem_nhdsWithin_of_mem_nhds ((hW i).mem_nhds hzi)] with w hwi
    exact (hCW i hwi hzi).trans (mul_le_mul_left
      (ENNReal.coe_le_coe.mpr (Finset.le_sup hi)) _)
  refine ⟨s.sup C, fun z w => ?_⟩
  simpa only [V, diskExtension_coe, hmetric, gLift, Subtype.edist_eq] using
    hcomp z.property w.property

end DifferentialGeometry.Geometry
