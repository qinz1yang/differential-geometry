import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TruncationLevelCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HoroballFlat

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.LongTime.CuspP1
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12
variable {H : FiniteVolumeHyperbolicModel.{u}}

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- A flat cusp cross-section has a finite path-diameter constant `D_q`: any two points are
joined by a smooth curve of `q`-speed `≤ D_q`. -/
theorem exists_connecting_path_bound_C1 (C : HyperbolicCusp) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y : Torus, ∃ c : ℝ → Torus,
      ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ c ∧ c 0 = x ∧ c 1 = y ∧
      ∀ s, C.torusMetric.inner (c s) (mfderiv 𝓘(ℝ, ℝ) torusModel c s 1)
        (mfderiv 𝓘(ℝ, ℝ) torusModel c s 1) ≤ D ^ 2 := by
  obtain ⟨cov, hloc, -, hsurj, hiso⟩ := exists_flat_cover_torus_CPF3 C
  have hcov : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) torusModel ∞ cov := hloc.contMDiff
  have hopen : ∀ n : ℕ, IsOpen (cov '' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) n) :=
    fun n => hloc.isOpenMap _ Metric.isOpen_ball
  have hcover : (univ : Set Torus) ⊆ ⋃ n : ℕ, cov '' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) n := by
    intro x _
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨n, hn⟩ := exists_nat_gt ‖a‖
    exact mem_iUnion.mpr ⟨n, a, by simpa using hn, rfl⟩
  have hmono : Monotone fun n : ℕ => cov '' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) n :=
    fun m n hmn => image_mono (Metric.ball_subset_ball (by exact_mod_cast hmn))
  obtain ⟨N, hN⟩ := (isCompact_univ (X := Torus)).elim_directed_cover _ hopen hcover
    (Monotone.directed_le hmono)
  refine ⟨2 * N, by positivity, fun x y => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hN (mem_univ x)
  obtain ⟨b, hb, rfl⟩ := hN (mem_univ y)
  let p : ℝ → EuclideanSpace ℝ (Fin 2) := fun s => a + s • (b - a)
  have hp : ContDiff ℝ ∞ p := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hpd : ∀ s, HasDerivAt p (b - a) s := by
    intro s
    have h := ((hasDerivAt_id s).smul_const (b - a)).const_add a
    exact h.congr_deriv (by simp)
  have hpm : ∀ s, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p s :=
    fun s => hp.contMDiff.mdifferentiableAt (by simp)
  have hv : ∀ s, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p s 1 = b - a := by
    intro s
    rw [mfderiv_eq_fderiv]
    exact (hpd s).deriv
  refine ⟨fun s => cov (p s), hcov.comp hp.contMDiff, by simp [p], by simp [p], fun s => ?_⟩
  have hcd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) torusModel cov (p s) :=
    (hcov (p s)).mdifferentiableAt (by simp)
  have hcomp : mfderiv 𝓘(ℝ, ℝ) torusModel (fun s => cov (p s)) s =
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) torusModel cov (p s)).comp
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p s) :=
    mfderiv_comp s hcd (hpm s)
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hv s, hiso, real_inner_self_eq_norm_sq]
  have hb' : ‖b‖ < N := by simpa using hb
  have ha' : ‖a‖ < N := by simpa using ha
  have h1 : ‖b - a‖ ≤ 2 * N := by
    have := norm_sub_le b a; linarith
  have h0 := norm_nonneg (b - a)
  nlinarith

/-- **(3) Intrinsic diameter of the level-`S` slices, explicit.** With `D_q` from
`exists_connecting_path_bound_C1` (depends only on the original cross-section metric `q`), any two
points of the slice at depth `z ≥ 0` are joined in `H` by a smooth curve of speed
`≤ e^{-(S+z)/2} D_q ≤ e^{-S/2} D_q`. -/
theorem truncationAtLevel_slice_diam_C1 (T : HyperbolicTruncation H) {S : ℝ} (hS : 2 ≤ S)
    (i : Fin T.count) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (x y : Torus) {z : ℝ}, 0 ≤ z →
    ∃ f : ℝ → H.Carrier, ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ f ∧
      f 0 = (truncationAtLevel_C1 T hS).cuspMap i (x, halfSpaceOneLift z) ∧
      f 1 = (truncationAtLevel_C1 T hS).cuspMap i (y, halfSpaceOneLift z) ∧
      ∀ s, H.metric.inner (f s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) f s 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) f s 1) ≤
        (Real.exp (-(S + z) / 2) * D) ^ 2 ∧ Real.exp (-(S + z) / 2) ≤ Real.exp (-S / 2) := by
  obtain ⟨D, hD0, hD⟩ := exists_connecting_path_bound_C1 (T.cusp i)
  refine ⟨D, hD0, fun x y z hz => ?_⟩
  obtain ⟨c, hc, h0, h1, hs⟩ := hD x y
  exact truncationAtLevel_slice_connect_C1 T hS i x y c hc h0 h1 hs hz

end GC.LongTime.Ch12
