import DifferentialGeometry.Geometry.Geodesic.Minimizing.Ray
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped ENNReal Manifold

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [SigmaCompactSpace M]

section BusemannMetricCore

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
def busemannApprox (γ : Real → M) (n : ℕ) (x : M) : Real :=
  (riemannianEDist I (γ (n : Real)) x).toReal - (n : Real)
def busemann (γ : Real → M) (x : M) : Real :=
  sInf (Set.range (fun n : ℕ => busemannApprox (I := I) γ n x))

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] in
private theorem edist_real_triangle (x y z : M) :
    (riemannianEDist I x z).toReal ≤
      (riemannianEDist I x y).toReal +
        (riemannianEDist I y z).toReal := by
  have hxy : riemannianEDist I x y ≠ ⊤ :=
    riemannianEDist_ne_top (I := I) x y
  have hyz : riemannianEDist I y z ≠ ⊤ :=
    riemannianEDist_ne_top (I := I) y z
  have htri : riemannianEDist I x z ≤
      riemannianEDist I x y + riemannianEDist I y z :=
    Manifold.riemannianEDist_triangle
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hxy, hyz⟩) htri
  rwa [ENNReal.toReal_add hxy hyz] at hreal

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] in
private theorem edist_real_comm (x y : M) :
    (riemannianEDist I x y).toReal =
      (riemannianEDist I y x).toReal := by
  exact congrArg ENNReal.toReal
    (Manifold.riemannianEDist_comm (I := I) (x := x) (y := y))

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem ray_dist_real
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ)
    {s t : Real} (hs : 0 ≤ s) (hst : s ≤ t) :
    (riemannianEDist I (γ s) (γ t)).toReal = t - s := by
  calc
    (riemannianEDist I (γ s) (γ t)).toReal =
        (ENNReal.ofReal (t - s)).toReal :=
      congrArg ENNReal.toReal (hray.edist_eq hs hst)
    _ = t - s := ENNReal.toReal_ofReal (sub_nonneg.mpr hst)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem busemannApprox_antitone
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x : M) :
    Antitone (fun n : ℕ => busemannApprox (I := I) γ n x) := by
  intro n m hnm
  have hnm_real : (n : Real) ≤ (m : Real) := by exact_mod_cast hnm
  have htri := edist_real_triangle (I := I) (γ (m : Real)) (γ (n : Real)) x
  have hdist :
      (riemannianEDist I (γ (m : Real)) (γ (n : Real))).toReal =
        (m : Real) - (n : Real) := by
    rw [edist_real_comm (I := I) (γ (m : Real)) (γ (n : Real))]
    exact ray_dist_real (I := I) hray (Nat.cast_nonneg n) hnm_real
  unfold busemannApprox
  rw [hdist] at htri
  linarith

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem busemannApprox_lower_bound
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x : M) (n : ℕ) :
    -(riemannianEDist I (γ 0) x).toReal ≤
      busemannApprox (I := I) γ n x := by
  have hdist :
      (riemannianEDist I (γ 0) (γ (n : Real))).toReal = (n : Real) := by
    simpa only [sub_zero] using
      ray_dist_real (I := I) hray (le_refl 0) (Nat.cast_nonneg n)
  have htri : (n : Real) ≤
      (riemannianEDist I (γ 0) x).toReal +
        (riemannianEDist I (γ (n : Real)) x).toReal := by
    calc
      (n : Real) =
          (riemannianEDist I (γ 0) (γ (n : Real))).toReal := hdist.symm
      _ ≤ (riemannianEDist I (γ 0) x).toReal +
          (riemannianEDist I x (γ (n : Real))).toReal :=
        edist_real_triangle (I := I) (γ 0) x (γ (n : Real))
      _ = (riemannianEDist I (γ 0) x).toReal +
          (riemannianEDist I (γ (n : Real)) x).toReal := by
        rw [edist_real_comm (I := I) x (γ (n : Real))]
  change -(riemannianEDist I (γ 0) x).toReal ≤
    (riemannianEDist I (γ (n : Real)) x).toReal - (n : Real)
  linarith

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem busemannApprox_bddBelow
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x : M) :
    BddBelow (Set.range (fun n : ℕ => busemannApprox (I := I) γ n x)) := by
  refine ⟨-(riemannianEDist I (γ 0) x).toReal, ?_⟩
  rintro y ⟨n, rfl⟩
  exact busemannApprox_lower_bound (I := I) hray x n

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem busemann_le_approx
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x : M) (n : ℕ) :
    busemann (I := I) γ x ≤ busemannApprox (I := I) γ n x := by
  unfold busemann
  exact csInf_le (busemannApprox_bddBelow (I := I) hray x) ⟨n, rfl⟩

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem tendsto_busemannApprox
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x : M) :
    Tendsto (fun n : ℕ => busemannApprox (I := I) γ n x) atTop
      (nhds (busemann (I := I) γ x)) := by
  unfold busemann
  rw [sInf_range]
  exact tendsto_atTop_ciInf
    (busemannApprox_antitone (I := I) hray x) (busemannApprox_bddBelow (I := I) hray x)

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] in
theorem busemannApprox_dist_le (γ : Real → M) (n : ℕ) (x y : M) :
    |busemannApprox (I := I) γ n x - busemannApprox (I := I) γ n y| ≤
      (riemannianEDist I x y).toReal := by
  have hxy := edist_real_triangle (I := I) (γ (n : Real)) y x
  have hyx := edist_real_triangle (I := I) (γ (n : Real)) x y
  have hcomm := edist_real_comm (I := I) y x
  unfold busemannApprox
  rw [hcomm] at hxy
  rw [abs_le]
  constructor <;> linarith

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem busemann_sub_le
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x y : M) :
    busemann (I := I) γ x - busemann (I := I) γ y ≤
      (riemannianEDist I x y).toReal := by
  have hlim :
      Tendsto
        (fun n : ℕ => busemannApprox (I := I) γ n x -
          busemannApprox (I := I) γ n y) atTop
        (nhds (busemann (I := I) γ x - busemann (I := I) γ y)) :=
    (tendsto_busemannApprox (I := I) hray x).sub
      (tendsto_busemannApprox (I := I) hray y)
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun n =>
    (abs_le.mp (busemannApprox_dist_le (I := I) γ n x y)).2

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem busemann_dist_le
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x y : M) :
    |busemann (I := I) γ x - busemann (I := I) γ y| ≤
      (riemannianEDist I x y).toReal := by
  rw [abs_le]
  constructor
  · have h := busemann_sub_le (I := I) hray y x
    rw [edist_real_comm (I := I) y x] at h
    linarith
  · exact busemann_sub_le (I := I) hray x y

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem edist_busemann_le_riemannianEDist
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x y : M) :
    edist (busemann (I := I) γ x) (busemann (I := I) γ y) ≤
      riemannianEDist I x y := by
  rw [edist_dist, Real.dist_eq,
    ← ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I) x y)]
  exact ENNReal.ofReal_le_ofReal (busemann_dist_le (I := I) hray x y)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem continuous_busemann
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) :
    Continuous (busemann (I := I) γ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt, EMetric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_riemannianEDist_lt I x hε] with y hy
  exact (edist_busemann_le_riemannianEDist (I := I) hray y x).trans_lt
    (by rwa [riemannianEDist_comm])

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem busemann_apply_ray
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) {s : Real} (hs : 0 ≤ s) :
    busemann (I := I) γ (γ s) = -s := by
  obtain ⟨N, hN⟩ := exists_nat_ge s
  have hconst :
      Tendsto (fun n : ℕ => busemannApprox (I := I) γ n (γ s)) atTop
        (nhds (-s)) := by
    apply tendsto_atTop_of_eventually_const (i₀ := N)
    intro n hn
    have hNn : (N : Real) ≤ (n : Real) := by exact_mod_cast hn
    have hsn : s ≤ (n : Real) := hN.trans hNn
    have hdist :
        (riemannianEDist I (γ (n : Real)) (γ s)).toReal =
          (n : Real) - s := by
      rw [edist_real_comm (I := I) (γ (n : Real)) (γ s)]
      exact ray_dist_real (I := I) hray hs hsn
    unfold busemannApprox
    rw [hdist]
    ring
  exact tendsto_nhds_unique (tendsto_busemannApprox (I := I) hray (γ s)) hconst

end BusemannMetricCore

end Riemannian
end Geometry
end DifferentialGeometry
