import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceLineScalarFlat
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

local instance intrinsicLineNullPlaneOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

section Pointwise

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem exists_null_plane_of_nonnegative_sectional_ricci_null
    (g : SmoothRiemannianMetric I M) (hdim : 2 ≤ Module.finrank ℝ E) (p : M)
    (hsec : metricRm04At (I := I) g p ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (v : TangentSpace I p) (hv : v ≠ 0)
    (hRic : ricciTensor (I := I) g p v v = 0) :
    ∃ a b : TangentSpace I p,
      0 < g.inner p a a * g.inner p b b - (g.inner p a b) ^ 2 ∧
        metricRm04StandardAt (I := I) g p a b b a = 0 := by
  classical
  by_contra hnone
  have hpositive (a b : TangentSpace I p) (ha : a ≠ 0) (hb : b ≠ 0)
      (hab : g.inner p a b = 0) :
      0 < metricRm04StandardAt (I := I) g p a b b a := by
    have hnonneg :=
      (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
        (I := I) g p).mp hsec a b
    have hne : metricRm04StandardAt (I := I) g p a b b a ≠ 0 := by
      intro hz
      apply hnone
      refine ⟨a, b, ?_, hz⟩
      rw [hab, zero_pow (by decide : 2 ≠ 0), sub_zero]
      exact mul_pos (g.pos p a ha) (g.pos p b hb)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hpos := ricci_pos_of_sec g p (by omega) hpositive hv
  exact (ne_of_gt hpos) hRic

end Pointwise

section Intrinsic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem exists_null_plane_of_nonnegative_sectional_intrinsic_line
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hsec : ∀ p : M, metricRm04At (I := I) g p ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {gamma : ℝ → M}
    (hline : ∀ s t : ℝ, riemannianEDistOf (I := I) g (gamma s) (gamma t) =
      ENNReal.ofReal |s - t|) (p : M) :
    ∃ a b : TangentSpace I p,
      0 < g.inner p a a * g.inner p b b - (g.inner p a b) ^ 2 ∧
        metricRm04StandardAt (I := I) g p a b b a = 0 := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun q : M => TangentSpace I q) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun q : M => TangentSpace I q) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro q v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : CompleteSpace M := hg.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := fun q v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g q v
  let _ : MetricSpace M := riemMetricSpace (I := I) (M := M)
  let _ : ProperSpace M := properSpace_riemMetric (I := I) hg.complete g hEnorm
  have hgamma : Isometry gamma := by
    apply Isometry.of_dist_eq
    intro s t
    rw [riemMetric_dist_eq (I := I),
      ← riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm, hline,
      ENNReal.toReal_ofReal (abs_nonneg _), Real.dist_eq]
  have hRic (q : M) (v : TangentSpace I q) :
      0 ≤ ricciTensor (I := I) g q v v := ricci_nonneg_of_sec g q (hsec q) v
  let b : M → ℝ := busemann (fun t : ℝ≥0 => gamma t)
  have hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b := busemann_contMDiff g hEnorm hRic hgamma
  have hunit (q : M) : g.inner q (gradientFun (I := I) g b q)
      (gradientFun (I := I) g b q) = 1 :=
    (opposite_busemann_gradient_unit g hEnorm hRic hgamma q).1
  have hH (q : M) : hessFun (I := I) g b q = 0 :=
    busemann_hessian_eq_zero g hEnorm hRic hgamma q
  have hzero := ricci_gradient_eq_zero_of_unit_hessian_zero g hb hunit hH p
  have hv : gradientFun (I := I) g b p ≠ 0 := by
    intro hz
    have hu := hunit p
    rw [hz] at hu
    simp at hu
  exact exists_null_plane_of_nonnegative_sectional_ricci_null g hdim p (hsec p)
    (gradientFun (I := I) g b p) hv hzero

end Intrinsic

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
