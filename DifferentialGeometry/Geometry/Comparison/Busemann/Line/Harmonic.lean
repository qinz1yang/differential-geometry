import DifferentialGeometry.Analysis.Elliptic.WeakLaplacian
import DifferentialGeometry.Geometry.Comparison.Busemann.Line.Regularity

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set Topology
open scoped ENNReal Manifold NNReal

namespace DifferentialGeometry.Geometry.Riemannian

open Analysis.Sobolev.IntrinsicLp
open Geometry.Operator
open BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem IsMinimizingLine.busemann_laplacian_eq_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (x : M) :
    ΔG (I := I) g
      ⟨busemann (I := I) γ,
        hγ.busemann_contMDiff (I := I) hEnorm hd hRic⟩ x = 0 := by
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let bp : M → ℝ := busemann (I := I) γ
  let bn : M → ℝ := busemann (I := I) (fun t : ℝ ↦ γ (-t))
  have hbp_smooth : ContMDiff I 𝓘(ℝ, ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) bp := by
    simpa only [bp] using hγ.busemann_contMDiff (I := I) hEnorm hd hRic
  have hpair (y : M) : bp y + bn y = 0 := by
    simpa only [bp, bn] using
      hγ.busemann_add_reverse_eq_zero (I := I) hEnorm hd hRic y
  have hbn_eq : bn = fun y ↦ -bp y := by
    funext y
    linarith [hpair y]
  have hbn_smooth : ContMDiff I 𝓘(ℝ, ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) bn := by
    rw [hbn_eq]
    exact hbp_smooth.neg
  have hd_lap : 0 < Module.finrank ℝ E - 1 := by omega
  have hbp_distrib : IsLaplacianLEDistributionalOn (I := I) g bp
      (fun _ : M ↦ 0) univ := by
    simpa only [bp] using
      busemann_isLaplacianLEDistributionalOn
        (I := I) g hEnorm hγ.positive_ray hd_lap hRic
  have hbn_distrib : IsLaplacianLEDistributionalOn (I := I) g bn
      (fun _ : M ↦ 0) univ := by
    simpa only [bn] using
      busemann_isLaplacianLEDistributionalOn
        (I := I) g hEnorm hγ.negative_ray hd_lap hRic
  have hbp_le : ΔG (I := I) g ⟨bp, hbp_smooth⟩ x ≤ 0 := by
    exact hbp_distrib.laplacian_le (I := I) hbp_smooth continuousOn_const
      x (Set.mem_univ x)
  have hbn_le : ΔG (I := I) g ⟨bn, hbn_smooth⟩ x ≤ 0 := by
    exact hbn_distrib.laplacian_le (I := I) hbn_smooth continuousOn_const
      x (Set.mem_univ x)
  have hbn_as_neg :
      ΔG (I := I) g ⟨bn, hbn_smooth⟩ x =
        ΔG (I := I) g ⟨fun y ↦ -bp y, hbp_smooth.neg⟩ x := by
    exact Δ_g_congr_of_eventuallyEq (I := I) g hbn_smooth hbp_smooth.neg
      (Filter.Eventually.of_forall fun y ↦ congrFun hbn_eq y)
  have hbn_lap :
      ΔG (I := I) g ⟨bn, hbn_smooth⟩ x =
        -ΔG (I := I) g ⟨bp, hbp_smooth⟩ x := by
    calc
      ΔG (I := I) g ⟨bn, hbn_smooth⟩ x =
          ΔG (I := I) g ⟨fun y ↦ -bp y, hbp_smooth.neg⟩ x := hbn_as_neg
      _ = -ΔG (I := I) g ⟨bp, hbp_smooth⟩ x :=
        Δ_g_neg (I := I) g hbp_smooth
  have hbp_nonneg : 0 ≤ ΔG (I := I) g ⟨bp, hbp_smooth⟩ x := by
    linarith [hbn_le, hbn_lap]
  have hzero : ΔG (I := I) g ⟨bp, hbp_smooth⟩ x = 0 :=
    le_antisymm hbp_le hbp_nonneg
  simpa only [bp] using hzero

end DifferentialGeometry.Geometry.Riemannian
