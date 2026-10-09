import DifferentialGeometry.Geometry.Comparison.Variation.EndpointAccelerationGerm
import DifferentialGeometry.Geometry.Exponential.Radial
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Comparison.Variation.EndpointGerms
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PullbackLocalIso
import Mathlib.Algebra.BigOperators.Fin
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PullbackLocalIsoDifferentiable
set_option autoImplicit false

noncomputable section

open Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped BigOperators

universe uM uE uH

theorem sum_variation_acceleration_boundary_eq_endpoints
    {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    (g : (i : Fin (n + 1)) → ℝ → SmoothRiemannianMetric I (M i))
    (a b : Fin (n + 1) → ℝ)
    (f : (i : Fin (n + 1)) → ℝ → ℝ → M i)
    (hf : ∀ i : Fin n, ContMDiffAt 𝓘(ℝ, ℝ) I 2
      (fun e => f i.castSucc e (b i.castSucc)) 0)
    (F : (i : Fin n) → PartialDiffeomorph I I (M i.castSucc) (M i.succ) ∞)
    (hmetric : ∀ (i : Fin n) (x : M i.castSucc), x ∈ (F i).source →
      ∀ V W : TangentSpace I x,
      (g i.castSucc (b i.castSucc)).inner x V W =
        (g i.succ (a i.succ)).inner (F i x)
          (mfderiv I I (F i : M i.castSucc → M i.succ) x V)
          (mfderiv I I (F i : M i.castSucc → M i.succ) x W))
    (hjoin : ∀ᶠ e in 𝓝 (0 : ℝ), ∀ i : Fin n,
      f i.castSucc e (b i.castSucc) ∈ (F i).source ∧
      F i (f i.castSucc e (b i.castSucc)) = f i.succ e (a i.succ))
    (hvelocity : ∀ i : Fin n,
      (mfderiv I I (F i : M i.castSucc → M i.succ) (f i.castSucc 0 (b i.castSucc))
        (mfderiv 𝓘(ℝ, ℝ) I (f i.castSucc 0) (b i.castSucc) 1) : E) =
          mfderiv 𝓘(ℝ, ℝ) I (f i.succ 0) (a i.succ) 1)
    :
    (∑ i : Fin (n + 1),
      ((g i (b i)).inner (f i 0 (b i))
        (covDerivAlong (I := I) (g i (b i)) (fun e => f i e (b i))
          (fun e => mfderiv 𝓘(ℝ, ℝ) I (fun z => f i z (b i)) e 1) 0)
        (mfderiv 𝓘(ℝ, ℝ) I (f i 0) (b i) 1) -
      (g i (a i)).inner (f i 0 (a i))
        (covDerivAlong (I := I) (g i (a i)) (fun e => f i e (a i))
          (fun e => mfderiv 𝓘(ℝ, ℝ) I (fun z => f i z (a i)) e 1) 0)
        (mfderiv 𝓘(ℝ, ℝ) I (f i 0) (a i) 1))) =
      (g (Fin.last n) (b (Fin.last n))).inner
        (f (Fin.last n) 0 (b (Fin.last n)))
        (centralVariationAcceleration (g (Fin.last n) (b (Fin.last n)))
          (f (Fin.last n)) (b (Fin.last n)))
        (mfderiv 𝓘(ℝ, ℝ) I (f (Fin.last n) 0) (b (Fin.last n)) 1) -
      (g 0 (a 0)).inner (f 0 0 (a 0))
        (centralVariationAcceleration (g 0 (a 0)) (f 0) (a 0))
        (mfderiv 𝓘(ℝ, ℝ) I (f 0 0) (a 0) 1) := by
  let A (i : Fin (n + 1)) (r : ℝ) := (g i r).inner (f i 0 r)
    (centralVariationAcceleration (g i r) (f i) r)
    (mfderiv 𝓘(ℝ, ℝ) I (f i 0) r 1)
  have hpair (i : Fin n) : A i.castSucc (b i.castSucc) = A i.succ (a i.succ) := by
    let gamma := fun e => f i.castSucc e (b i.castSucc)
    let delta := fun e => f i.succ e (a i.succ)
    let gl := g i.castSucc (b i.castSucc)
    let gr := g i.succ (a i.succ)
    have hmet (x : M i.castSucc) (hx : x ∈ (F i).source) (V W : TangentSpace I x) :
        gl.inner x V W = gr.inner (F i x)
          (mfderiv I I (F i : M i.castSucc → M i.succ) x V)
          (mfderiv I I (F i : M i.castSucc → M i.succ) x W) := by
      exact hmetric i x hx V W
    have hj : ∀ᶠ e in 𝓝 (0 : ℝ), gamma e ∈ (F i).source ∧ F i (gamma e) = delta e :=
      hjoin.mono (fun e he => he i)
    have hpoint : F i (gamma 0) = delta 0 := hj.self_of_nhds.2
    have hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I 2 gamma 0 := hf i
    have hnat := covDerivAlong_map_of_local_isometry_on_of_mdifferentiableAt gl gr
      (F i).open_source (fun x => ⟨F i, x.property, fun _ _ => rfl⟩) hmet
      gamma (fun e => mfderiv 𝓘(ℝ, ℝ) I gamma e 1) hj.self_of_nhds.1
      (hgamma.mdifferentiableAt (by decide)) (differentiableAt_chartRepAt_curveVelocity hgamma)
    have hdiff : ∀ᶠ e in 𝓝 (0 : ℝ), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma e := by
      filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hgamma] with e he
      exact he.mdifferentiableAt (by decide)
    have hmapVelocity : ∀ᶠ e in 𝓝 (0 : ℝ),
        (mfderiv I I (F i : M i.castSucc → M i.succ) (gamma e)
          (mfderiv 𝓘(ℝ, ℝ) I gamma e 1) : E) =
            mfderiv 𝓘(ℝ, ℝ) I (fun z => F i (gamma z)) e 1 := by
      filter_upwards [hj, hdiff] with e he hde
      exact (mfderiv_comp_apply e ((F i).mdifferentiableAt (by simp) he.1) hde (1 : ℝ)).symm
    have hnatVelocity := hnat.trans (covDerivAlong_congr_curve gr
      (fun e => mfderiv I I (F i : M i.castSucc → M i.succ) (gamma e)
        (mfderiv 𝓘(ℝ, ℝ) I gamma e 1))
      (fun e => mfderiv 𝓘(ℝ, ℝ) I (fun z => F i (gamma z)) e 1)
      (EventuallyEq.refl _ _) hmapVelocity)
    have hendpoint :
        (centralVariationAcceleration gr (f i.succ) (a i.succ) : E) =
          covDerivAlong (I := I) gr (fun e => F i (gamma e))
            (fun e => mfderiv 𝓘(ℝ, ℝ) I (fun z => F i (gamma z)) e 1) 0 :=
      centralVariationAcceleration_eq_of_endpoint_germ gr (f i.succ) (a i.succ)
        (hj.mono (fun _ he => he.2.symm))
    have hacc : (mfderiv I I (F i : M i.castSucc → M i.succ) (gamma 0)
        (centralVariationAcceleration gl (f i.castSucc) (b i.castSucc)) : E) =
          centralVariationAcceleration gr (f i.succ) (a i.succ) :=
      hnatVelocity.trans hendpoint.symm
    change gl.inner (gamma 0)
      (centralVariationAcceleration gl (f i.castSucc) (b i.castSucc))
      (mfderiv 𝓘(ℝ, ℝ) I (f i.castSucc 0) (b i.castSucc) 1) =
      gr.inner (delta 0) (centralVariationAcceleration gr (f i.succ) (a i.succ))
        (mfderiv 𝓘(ℝ, ℝ) I (f i.succ 0) (a i.succ) 1)
    rw [hmet (gamma 0) hj.self_of_nhds.1, hacc, hvelocity i, hpoint]
  change (∑ i, (A i (b i) - A i (a i))) =
    A (Fin.last n) (b (Fin.last n)) - A 0 (a 0)
  rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp_rw [hpair]
  ring

/-- A genuine terminal exponential germ has zero variation acceleration. This
places no restriction on the velocity of the original central action curve. -/
theorem centralVariationAcceleration_eq_zero_of_exp_germ
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (b : ℝ)
    (q : M) (Z : TangentSpace I q)
    (hf : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun e => f e b) 0)
    (hexp : (fun e => f e b) =ᶠ[𝓝 (0 : ℝ)]
      (fun e => DifferentialGeometry.Geometry.Riemannian.Exponential.expMap g q (e • Z))) :
    centralVariationAcceleration g f b = 0 := by
  have hgeo := DifferentialGeometry.Geometry.Riemannian.Exponential.hasGeodesicEquationAt_expMap_smul
    g q Z (t := 0) (by
      rw [zero_smul]
      exact DifferentialGeometry.Geometry.Riemannian.Exponential.zero_mem_expDomain g q)
  exact centralVariationAcceleration_eq_zero_of_geodesic_germ g f b hf hgeo hexp

/-- Exact seam cancellation with a fixed first endpoint and a genuine terminal
exponential germ. The central curve's final velocity is retained. -/
theorem sum_variation_acceleration_boundary_eq_zero_of_terminal_exp
    {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    (g : (i : Fin (n + 1)) → ℝ → SmoothRiemannianMetric I (M i))
    (a b : Fin (n + 1) → ℝ)
    (f : (i : Fin (n + 1)) → ℝ → ℝ → M i)
    (hf : ∀ i : Fin n, ContMDiffAt 𝓘(ℝ, ℝ) I 2
      (fun e => f i.castSucc e (b i.castSucc)) 0)
    (F : (i : Fin n) → PartialDiffeomorph I I (M i.castSucc) (M i.succ) ∞)
    (hmetric : ∀ (i : Fin n) (x : M i.castSucc), x ∈ (F i).source →
      ∀ V W : TangentSpace I x,
      (g i.castSucc (b i.castSucc)).inner x V W =
        (g i.succ (a i.succ)).inner (F i x)
          (mfderiv I I (F i : M i.castSucc → M i.succ) x V)
          (mfderiv I I (F i : M i.castSucc → M i.succ) x W))
    (hjoin : ∀ᶠ e in 𝓝 (0 : ℝ), ∀ i : Fin n,
      f i.castSucc e (b i.castSucc) ∈ (F i).source ∧
      F i (f i.castSucc e (b i.castSucc)) = f i.succ e (a i.succ))
    (hvelocity : ∀ i : Fin n,
      (mfderiv I I (F i : M i.castSucc → M i.succ) (f i.castSucc 0 (b i.castSucc))
        (mfderiv 𝓘(ℝ, ℝ) I (f i.castSucc 0) (b i.castSucc) 1) : E) =
          mfderiv 𝓘(ℝ, ℝ) I (f i.succ 0) (a i.succ) 1)
    (p : M 0) (hfirst : (fun e => f 0 e (a 0)) =ᶠ[𝓝 (0 : ℝ)] fun _ => p)
    (q : M (Fin.last n)) (Z : TangentSpace I q)
    (hterminal : ContMDiffAt 𝓘(ℝ, ℝ) I 2
      (fun e => f (Fin.last n) e (b (Fin.last n))) 0)
    (hexp : (fun e => f (Fin.last n) e (b (Fin.last n))) =ᶠ[𝓝 (0 : ℝ)]
      (fun e => DifferentialGeometry.Geometry.Riemannian.Exponential.expMap
        (g (Fin.last n) (b (Fin.last n))) q (e • Z))) :
    (∑ i : Fin (n + 1),
      ((g i (b i)).inner (f i 0 (b i))
        (covDerivAlong (I := I) (g i (b i)) (fun e => f i e (b i))
          (fun e => mfderiv 𝓘(ℝ, ℝ) I (fun z => f i z (b i)) e 1) 0)
        (mfderiv 𝓘(ℝ, ℝ) I (f i 0) (b i) 1) -
      (g i (a i)).inner (f i 0 (a i))
        (covDerivAlong (I := I) (g i (a i)) (fun e => f i e (a i))
          (fun e => mfderiv 𝓘(ℝ, ℝ) I (fun z => f i z (a i)) e 1) 0)
        (mfderiv 𝓘(ℝ, ℝ) I (f i 0) (a i) 1))) = 0 := by
  have hfirstA := centralVariationAcceleration_eq_zero_of_eventually_constant
    (g 0 (a 0)) (f 0) (a 0) p hfirst
  have hlastA := centralVariationAcceleration_eq_zero_of_exp_germ
    (g (Fin.last n) (b (Fin.last n))) (f (Fin.last n)) (b (Fin.last n))
    q Z hterminal hexp
  have hsum := sum_variation_acceleration_boundary_eq_endpoints
    g a b f hf F hmetric hjoin hvelocity
  simpa only [hfirstA, hlastA, map_zero, zero_apply, sub_self] using hsum

end DifferentialGeometry.Geometry.Riemannian.Variation
