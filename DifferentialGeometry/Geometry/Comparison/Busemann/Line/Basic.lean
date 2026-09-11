import DifferentialGeometry.Geometry.Comparison.Busemann.Basic
import DifferentialGeometry.Geometry.Geodesic.Minimizing.Line.Basic

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped ENNReal Manifold

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [SigmaCompactSpace M]

section BusemannLine

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [ConnectedSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] in
private theorem edist_real_tri (x y z : M) :
    (riemannianEDist I x z).toReal ≤
      (riemannianEDist I x y).toReal +
        (riemannianEDist I y z).toReal := by
  have hxy : riemannianEDist I x y ≠ ⊤ :=
    Exponential.riemannianEDist_ne_top (I := I) x y
  have hyz : riemannianEDist I y z ≠ ⊤ :=
    Exponential.riemannianEDist_ne_top (I := I) y z
  have htri : riemannianEDist I x z ≤
      riemannianEDist I x y + riemannianEDist I y z :=
    Manifold.riemannianEDist_triangle
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hxy, hyz⟩) htri
  rwa [ENNReal.toReal_add hxy hyz] at hreal

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private theorem line_dist_real
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ)
    ⦃s t : ℝ⦄ (hst : s ≤ t) :
    (riemannianEDist I (γ s) (γ t)).toReal = t - s := by
  rw [hγ.edist_eq hst, ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]

namespace IsMinimizingLine

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem busemann_add_reverse_nonneg
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ) (x : M) :
    0 ≤ busemann (I := I) γ x +
      busemann (I := I) (fun t : ℝ ↦ γ (-t)) x := by
  have hlim : Tendsto
      (fun n : ℕ ↦ busemannApprox (I := I) γ n x +
        busemannApprox (I := I) (fun t : ℝ ↦ γ (-t)) n x)
      atTop
      (nhds (busemann (I := I) γ x +
        busemann (I := I) (fun t : ℝ ↦ γ (-t)) x)) :=
    (tendsto_busemannApprox (I := I) hγ.positive_ray x).add
      (tendsto_busemannApprox (I := I) hγ.negative_ray x)
  apply ge_of_tendsto' hlim
  intro n
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hline :
      (riemannianEDist I (γ (-(n : ℝ))) (γ (n : ℝ))).toReal =
        (n : ℝ) - (-(n : ℝ)) :=
    line_dist_real (I := I) hγ (neg_le_self hn)
  have htri := edist_real_tri (I := I) (γ (-(n : ℝ))) x (γ (n : ℝ))
  have hcomm :
      (riemannianEDist I x (γ (n : ℝ))).toReal =
        (riemannianEDist I (γ (n : ℝ)) x).toReal :=
    congrArg ENNReal.toReal
      (Manifold.riemannianEDist_comm (I := I)
        (x := x) (y := γ (n : ℝ)))
  rw [hline, hcomm] at htri
  unfold busemannApprox
  linarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem busemann_add_reverse_at_zero
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ) :
    busemann (I := I) γ (γ 0) +
      busemann (I := I) (fun t : ℝ ↦ γ (-t)) (γ 0) = 0 := by
  have hpos : busemann (I := I) γ (γ 0) = 0 := by
    simpa using busemann_apply_ray (I := I) hγ.positive_ray (s := 0) (le_refl 0)
  have hneg : busemann (I := I) (fun t : ℝ ↦ γ (-t)) (γ 0) = 0 := by
    simpa using busemann_apply_ray (I := I) hγ.negative_ray (s := 0) (le_refl 0)
  rw [hpos, hneg, add_zero]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem busemann_add_reverse_on_line
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ) (t : ℝ) :
    busemann (I := I) γ (γ t) +
      busemann (I := I) (fun s : ℝ ↦ γ (-s)) (γ t) = 0 := by
  by_cases ht : 0 ≤ t
  · have hpos : busemann (I := I) γ (γ t) = -t :=
      busemann_apply_ray (I := I) hγ.positive_ray ht
    have hneg_zero :
        busemann (I := I) (fun s : ℝ ↦ γ (-s)) (γ 0) = 0 := by
      simpa using busemann_apply_ray (I := I) hγ.negative_ray (s := 0) (le_refl 0)
    have hdist : (riemannianEDist I (γ t) (γ 0)).toReal = t := by
      rw [Manifold.riemannianEDist_comm]
      simpa only [sub_zero] using line_dist_real (I := I) hγ ht
    have hupper := busemann_sub_le (I := I) hγ.negative_ray (γ t) (γ 0)
    have hnonneg := busemann_add_reverse_nonneg (I := I) hγ (γ t)
    rw [hpos] at hnonneg
    rw [hneg_zero, hdist, sub_zero] at hupper
    linarith
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have hneg :
        busemann (I := I) (fun s : ℝ ↦ γ (-s)) (γ t) = t := by
      simpa using
        busemann_apply_ray (I := I) hγ.negative_ray (s := -t) (neg_nonneg.mpr ht')
    have hpos_zero : busemann (I := I) γ (γ 0) = 0 := by
      simpa using busemann_apply_ray (I := I) hγ.positive_ray (s := 0) (le_refl 0)
    have hdist : (riemannianEDist I (γ t) (γ 0)).toReal = -t := by
      simpa only [zero_sub] using line_dist_real (I := I) hγ ht'
    have hupper := busemann_sub_le (I := I) hγ.positive_ray (γ t) (γ 0)
    have hnonneg := busemann_add_reverse_nonneg (I := I) hγ (γ t)
    rw [hneg] at hnonneg
    rw [hpos_zero, hdist, sub_zero] at hupper
    linarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
theorem busemann_apply_line
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ) (t : ℝ) :
    busemann (I := I) γ (γ t) = -t := by
  have hvalue (n : ℕ) (hn : t ≤ (n : ℝ)) : busemannApprox (I := I) γ n (γ t) = -t := by
    rw [busemannApprox, riemannianEDist_comm, hγ.edist_eq hn,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hn)]
    ring
  apply IsLeast.csInf_eq
  constructor
  · obtain ⟨n, hn⟩ := exists_nat_ge t
    exact ⟨n, hvalue n hn⟩
  · rintro _ ⟨n, rfl⟩
    rcases le_total t (n : ℝ) with hn | hn
    · exact (hvalue n hn).symm.le
    · change -t ≤ (riemannianEDist I (γ (n : ℝ)) (γ t)).toReal - (n : ℝ)
      rw [hγ.edist_eq hn, ENNReal.toReal_ofReal (sub_nonneg.mpr hn)]
      linarith

end IsMinimizingLine

end BusemannLine

end Riemannian
end Geometry
end DifferentialGeometry
