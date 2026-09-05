import DifferentialGeometry.Geometry.Geodesic.Maximal.Rescaling
import DifferentialGeometry.Geometry.Geodesic.Flow.CrossVectorFieldReduction

open Filter Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem smul_mem_expDomain_iff
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p} {c : ℝ} :
    c • v ∈ expDomain g p ↔ c ∈ maximalGeodesicInterval g p v := by
  change (1 : ℝ) ∈ maximalGeodesicInterval g p (c • v) ↔
    c ∈ maximalGeodesicInterval g p v
  simpa only [mul_one] using mem_maximalGeodesicInterval_smul_iff (g := g) (p := p)
    (v := v) (c := c) (t := 1)

theorem expMap_smul [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (c : ℝ) :
    expMap g p (c • v) = maximalGeodesic g p v c := by
  change maximalGeodesic g p (c • v) 1 = maximalGeodesic g p v c
  simpa only [mul_one] using maximalGeodesic_smul g p v c 1

theorem smul_mem_expDomain
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p} {c : ℝ}
    (hv : v ∈ expDomain g p) (hc : c ∈ Icc (0 : ℝ) 1) :
    c • v ∈ expDomain g p := by
  obtain ⟨γ, J, hJ, hconn, h0, h1, hγ⟩ := hv
  exact smul_mem_expDomain_iff.mpr
    ⟨γ, J, hJ, hconn, h0, hconn.ordConnected.out h0 h1 hc, hγ⟩

theorem starConvex_expDomain (g : SmoothRiemannianMetric I M) (p : M) :
    StarConvex ℝ (0 : TangentSpace I p) (expDomain g p) := by
  rw [starConvex_zero_iff]
  exact fun _ hv _ hc0 hc1 => smul_mem_expDomain hv ⟨hc0, hc1⟩

theorem exists_isGeodesicOnWithInitial_eqOn_expMap [T2Space (TangentBundle I M)]
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p} {r : ℝ}
    (hr : r • v ∈ expDomain g p) :
    ∃ (γ : ℝ → M) (J : Set ℝ), IsOpen J ∧ IsPreconnected J ∧ uIcc 0 r ⊆ J ∧
      IsGeodesicOnWithInitial g γ J p v ∧ EqOn γ (fun t => expMap g p (t • v)) J := by
  obtain ⟨γ, J, hJ, hconn, h0, hrJ, hγ⟩ := smul_mem_expDomain_iff.mp hr
  have hsub : uIcc 0 r ⊆ J := hconn.ordConnected.uIcc_subset h0 hrJ
  refine ⟨γ, J, hJ, hconn, hsub, hγ, ?_⟩
  intro t ht
  exact (maximalGeodesic_eqOn g hJ hconn h0 hγ ht).symm.trans
    (expMap_smul g p v t).symm

theorem hasGeodesicEquationAt_expMap_smul [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) {t : ℝ}
    (ht : t • v ∈ expDomain g p) :
    HasGeodesicEquationAt g (fun s : ℝ => expMap g p (s • v)) t := by
  obtain ⟨γ, J, hJ, _, hsub, hγ, heq⟩ := exists_isGeodesicOnWithInitial_eqOn_expMap ht
  have hJt : J ∈ 𝓝 t := hJ.mem_nhds (hsub right_mem_uIcc)
  have hEq : (fun s => expMap g p (s • v)) =ᶠ[𝓝 t] γ :=
    eventuallyEq_of_mem hJt (fun s hs => (heq hs).symm)
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at hEq.eq_of_nhds hEq
    ((hγ.isGeodesicAt hJt).hasGeodesicEquationAt g)

end DifferentialGeometry.Geometry.Riemannian.Exponential
