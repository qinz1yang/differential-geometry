import DifferentialGeometry.Topology.Manifold.Orientation
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# LFR14, orientation preservation from positive chart Jacobians

Blueprint LFR14 (master207A.tex:25869), step 5 (orientation). If a chart parametrization `σ` of
`N` and a chart `d` of `Y` are oriented against one fixed orientation `oE` of the model (in the
pointwise form of interface I-LIM-OR), and the chart representation `d⁻¹ ∘ f ∘ σ` of a partial
diffeomorphism `f : N → Y` has positive Jacobian at `u`, then the differential of `f` at `σ u`
carries the orientation of `N` to that of `Y`.

* `orientation_map_mfderiv_eq_of_det_pos`: the pointwise statement (chain rule
  `Df ∘ Dσ = Dd ∘ D(d⁻¹ ∘ f ∘ σ)` near `u`, and `Orientation.map_eq_iff_det_pos`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

/-- **Orientation preservation from a positive chart Jacobian.** -/
theorem orientation_map_mfderiv_eq_of_det_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace E Y] [IsManifold 𝓘(ℝ, E) ∞ Y]
    {K : ℕ} (hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0) (oE : Orientation ℝ E (Fin n))
    (oN : ManifoldOrientation 𝓘(ℝ, E) N n) (oY : ManifoldOrientation 𝓘(ℝ, E) Y n)
    (σ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E N K)
    (d : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E Y ∞)
    (hσ : ∀ u (hu : u ∈ σ.source), Orientation.map (Fin n)
      ((σ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) (K : ℕ∞ω) hu).mfderivToContinuousLinearEquiv
        hK0).toLinearEquiv oE = oN.orientation (σ u))
    (hd : ∀ u (hu : u ∈ d.source), Orientation.map (Fin n)
      ((d.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ hu).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv oE = oY.orientation (d u))
    (f : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N Y K) {x : N} (hx : x ∈ f.source)
    {u : E} (hu : u ∈ σ.source) (hσu : σ u = x) (ht : f x ∈ d.target)
    (hdet : 0 < (fderiv ℝ (fun y => d.symm (f (σ y))) u).det) :
    Orientation.map (Fin n)
      ((f.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
        hK0).toLinearEquiv (oN.orientation x) = oY.orientation (f x) := by
  subst hσu
  set c : E → E := fun y => d.symm (f (σ y)) with hc
  have hcu : c u ∈ d.source := d.toPartialEquiv.map_target ht
  have hdc : d (c u) = f (σ u) := d.toPartialEquiv.right_inv ht
  have hinf : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hσd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) σ u := σ.mdifferentiableAt hK0 hu
  have hfd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) f (σ u) := f.mdifferentiableAt hK0 hx
  have hdd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) d (c u) := d.mdifferentiableAt hinf hcu
  have hdsd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) d.symm (f (σ u)) :=
    d.symm.mdifferentiableAt hinf ht
  have hcd : DifferentiableAt ℝ c u :=
    mdifferentiableAt_iff_differentiableAt.mp (hdsd.comp u (hfd.comp u hσd))
  -- `f ∘ σ = d ∘ c` near `u`
  have hgerm : (f ∘ σ : E → Y) =ᶠ[𝓝 u] (d ∘ c : E → Y) := by
    have hcont : ContinuousAt (f ∘ σ : E → Y) u := hfd.continuousAt.comp hσd.continuousAt
    filter_upwards [hcont.preimage_mem_nhds (d.open_target.mem_nhds ht)] with y hy
    exact (d.toPartialEquiv.right_inv hy).symm
  -- the chain rule
  have hchain : ∀ v : E, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (σ u)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ u v) : E) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) d (c u) (fderiv ℝ c u v) : E) := by
    intro v
    have h1 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (f ∘ σ) u =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (σ u)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ u) :=
      mfderiv_comp u hfd hσd
    have h2 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (d ∘ c) u =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) d (c u)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c u) :=
      mfderiv_comp u hdd hcd.mdifferentiableAt
    have h3 := hgerm.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    have h4 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c u = fderiv ℝ c u := mfderiv_eq_fderiv
    have e1 := DFunLike.congr_fun h1 v
    have e2 := DFunLike.congr_fun h2 v
    have e3 := DFunLike.congr_fun h3 v
    have e4 := DFunLike.congr_fun h4 v
    exact e1.symm.trans (e3.trans (e2.trans (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) d (c u)) e4)))
  have hdim : Fintype.card (Fin n) = Module.finrank ℝ E := by
    rw [Fintype.card_fin, oN.dimension_eq]
  set A := ((σ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) (K : ℕ∞ω) hu).mfderivToContinuousLinearEquiv
    hK0).toLinearEquiv with hA
  set B := ((f.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
    hK0).toLinearEquiv with hB
  set C := ((d.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ hcu).mfderivToContinuousLinearEquiv
    hinf).toLinearEquiv with hC
  let M : E ≃ₗ[ℝ] E := (A.trans B).trans C.symm
  have hMv : ∀ v : E, M v = fderiv ℝ c u v := by
    intro v
    change C.symm (B (A v)) = fderiv ℝ c u v
    have hBA : B (A v) = C (fderiv ℝ c u v) := hchain v
    rw [hBA]
    exact C.symm_apply_apply _
  have hMpos : Orientation.map (Fin n) M oE = oE := by
    refine (oE.map_eq_iff_det_pos M hdim).mpr ?_
    have hlin : (M : E →ₗ[ℝ] E) = ((fderiv ℝ c u : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
      LinearMap.ext hMv
    rw [hlin]
    exact hdet
  have hAB : A.trans B = M.trans C := by
    ext v
    change B (A v) = C (C.symm (B (A v)))
    exact (C.apply_symm_apply _).symm
  have key : ∀ y y' : Y, y = y' →
      (oY.orientation y : Orientation ℝ E (Fin n)) = oY.orientation y' := by
    rintro y _ rfl
    rfl
  have s1 : Orientation.map (Fin n) B (oN.orientation (σ u)) =
      Orientation.map (Fin n) B (Orientation.map (Fin n) A oE) := by rw [hσ u hu]
  have s2 := DifferentialGeometry.VectorBundle.map_orientation_trans_between A B oE
  have s3 : Orientation.map (Fin n) (A.trans B) oE = Orientation.map (Fin n) (M.trans C) oE :=
    congrArg (fun e => Orientation.map (Fin n) e oE) hAB
  have s4 := (DifferentialGeometry.VectorBundle.map_orientation_trans_between M C oE).symm
  have s5 : Orientation.map (Fin n) C (Orientation.map (Fin n) M oE) =
      Orientation.map (Fin n) C oE := by rw [hMpos]
  exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans ((hd (c u) hcu).trans (key _ _ hdc))))))

end DifferentialGeometry.CheegerGromovCompactness
