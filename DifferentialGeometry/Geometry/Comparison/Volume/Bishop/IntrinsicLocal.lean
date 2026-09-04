import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Intrinsic
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.JacobiLocal

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open CovariantDerivativeAlong
open Exponential
open Geodesic
open Variation
open BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
private theorem linIndep_ortho
    {ι : Type*} [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : ι → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    LinearIndependent Real v := by
  classical
  rw [linearIndependent_iff']
  intro s c hc j hj
  have hpair := congrArg (fun z : E => g.inner p z (v j)) hc
  change g.inner p (∑ i ∈ s, c i • v i) (v j) =
    g.inner p 0 (v j) at hpair
  rw [map_sum, sum_apply, map_zero,
    zero_apply] at hpair
  have hsummand : ∀ i ∈ s,
      g.inner p (c i • v i) (v j) =
        c i * (if i = j then 1 else 0) := by
    intro i _
    rw [ContinuousLinearMap.map_smul, smul_apply,
      smul_eq_mul, hON i j]
  rw [Finset.sum_congr rfl hsummand] at hpair
  rw [Finset.sum_eq_single_of_mem j hj] at hpair
  · simpa only [if_pos, mul_one] using hpair
  · intro i _ hij
    rw [if_neg (by simpa using hij), mul_zero]

omit [T2Space (TangentBundle I M)] in
private theorem intrJacobi_li_on
    {ι : Type*}
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (v : ι → TangentSpace I p)
    (hv : LinearIndependent Real v) {t : Real} (ht : t ≠ 0)
    (hno : ¬ IsConjVec (I := I) g hEnorm p (t • (u : E))) :
    LinearIndependent Real fun i =>
      intrinsicJacobi (I := I) g hEnorm p u (v i) t := by
  let L : E →L[Real] E :=
    mfderiv 𝓘(Real, E) I
      (fun z : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from z))
      (t • (u : E))
  have hLinj : Function.Injective L := by
    unfold IsConjVec at hno
    exact Classical.not_not.mp hno
  let a : Realˣ := Units.mk0 t ht
  let as : ι → Realˣ := fun _ => a
  have hscaled : LinearIndependent Real fun i => t • v i := by
    have has : as • v = fun i => t • v i := by
      funext i
      rfl
    rw [← has]
    exact hv.units_smul as
  have hmapped : LinearIndependent Real fun i => L (t • (v i : E)) :=
    hscaled.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr hLinj)
  have hfield :
      (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i) t) =
        fun i => L (t • (v i : E)) := by
    funext i
    unfold intrinsicJacobi
    dsimp only [L]
    apply eq_of_heq
    exact heq_of_eq
      (intrinsic_jacobi_at (I := I) g hEnorm p (u : E) (v i : E) t)
  rw [hfield]
  exact hmapped

theorem exists_intrMean_on
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (q b : Real)
    (hq : 0 ≤ q) (hb : 1 < b)
    (hu : 0 < g.inner p u u)
    (hno : ∀ t ∈ Set.Ioo (0 : Real) b,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E))
    (hRic : 0 < Module.finrank Real E - 1 →
      let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
      ∀ t ∈ Set.Ioo (0 : Real) b,
        -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) *
            g.inner (γ t) (curveVelocity (I := I) γ t)
              (curveVelocity (I := I) γ t) ≤
          ricciTensor (I := I) g (γ t)
            (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t)) :
    ∃ v : Fin (Module.finrank Real E - 1) → TangentSpace I p,
      LinearIndependent Real v ∧
      (∀ i, g.inner p u (v i) = 0) ∧
      let γ := intrinsicGeodesic (I := I) g hEnorm p u
      let V := fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)
      let ell := Real.sqrt (g.inner p u u)
      curveMean (I := I) g γ V 1 / ell ≤
        ((Module.finrank Real E - 1 : Nat) : Real) / ell +
          ((Module.finrank Real E - 1 : Nat) : Real) * q := by
  classical
  let d : Nat := Module.finrank Real E - 1
  by_cases hd0 : d = 0
  · let v : Fin d → TangentSpace I p := fun i => Fin.elim0 (hd0 ▸ i)
    have hv : LinearIndependent Real v := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      exact Fin.elim0 (hd0 ▸ i)
    have hperp : ∀ i, g.inner p u (v i) = 0 := by
      intro i
      exact Fin.elim0 (hd0 ▸ i)
    refine ⟨v, hv, hperp, ?_⟩
    have hmean0 :
        curveMean (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) 1 = 0 := by
      simp only [curveMean, Matrix.trace]
      apply Finset.sum_eq_zero
      intro i hi
      exact Fin.elim0 (hd0 ▸ i)
    simp only [d, hd0, Nat.cast_zero, zero_div, zero_mul, add_zero,
      hmean0]
    exact le_rfl
  · have hd : 0 < d := Nat.pos_of_ne_zero hd0
    obtain ⟨v, hON, hperp'⟩ := exists_perp_pos (I := I) g p u hu
    have hperp : ∀ i, g.inner p u (v i) = 0 := by
      intro i
      rw [g.symm p u (v i)]
      exact hperp' i
    have hv : LinearIndependent Real v :=
      linIndep_ortho (I := I) g p v hON
    refine ⟨v, hv, hperp, ?_⟩
    let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
    let V : Fin d → ∀ t, TangentSpace I (γ t) := fun i =>
      intrinsicJacobi (I := I) g hEnorm p u (v i)
    let ell : Real := Real.sqrt (g.inner p u u)
    have hell : 0 < ell := by
      simpa only [ell] using Real.sqrt_pos.2 hu
    have hγInf : ContMDiff 𝓘(Real, Real) I ∞ γ :=
      intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
    have hγ : ∀ t ∈ Set.Ioo (0 : Real) b,
        ContMDiffAt 𝓘(Real, Real) I (2 : WithTop ℕ∞) γ t := by
      intro t ht
      exact hγInf.contMDiffAt.of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hspeed : ∀ t ∈ Set.Ioo (0 : Real) b,
        g.inner (γ t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t) = ell ^ 2 := by
      intro t ht
      calc
        g.inner (γ t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t) =
            g.inner p u u := by
          change g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
            (mfderiv 𝓘(Real, Real) I
              (intrinsicGeodesic (I := I) g hEnorm p u) t 1)
            (mfderiv 𝓘(Real, Real) I
              (intrinsicGeodesic (I := I) g hEnorm p u) t 1) =
              g.inner p u u
          exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u t
        _ = ell ^ 2 := (Real.sq_sqrt hu.le).symm
    have hVdiff : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
        DifferentiableAt Real (chartRepAt (I := I) γ (V i) t) t := by
      intro t ht i
      simpa only [γ, V] using
        (intrJacobi_diff (I := I) g hEnorm p u (v i) t).1
    have hDVdiff : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
        DifferentiableAt Real
          (chartRepAt (I := I) γ
            (fun s => covDerivAlong (I := I) g γ (V i) s) t) t := by
      intro t ht i
      simpa only [γ, V] using
        (intrJacobi_diff (I := I) g hEnorm p u (v i) t).2
    have hVperp : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
        g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0 := by
      intro t ht i
      simpa only [γ, V] using
        intrJacobi_perp_ne (I := I) g hEnorm p u (v i) ht.1.ne' (hperp i)
    have hDVperp : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
        g.inner (γ t) (curveVelocity (I := I) γ t)
          (covDerivAlong (I := I) g γ (V i) t) = 0 := by
      intro t ht i
      simpa only [γ, V] using
        intrJacobi_dperp (I := I) g hEnorm p u (v i) ht.1.ne'
          (hperp i)
    have hLI : ∀ t ∈ Set.Ioo (0 : Real) b,
        LinearIndependent Real fun i => V i t := by
      intro t ht
      simpa only [γ, V] using
        intrJacobi_li_on (I := I) g hEnorm p u v hv ht.1.ne' (hno t ht)
    have hW : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i j,
        jacobiWronskian (I := I) g γ (V i) (V j) t = 0 := by
      intro t ht i j
      exact wronskian_eq_zero (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
        g γ (V i) (V j) (hγInf.of_le
          (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
        (fun s _ => by simpa only [γ, V] using
          (intrJacobi_diff (I := I) g hEnorm p u (v i) s).1)
        (fun s _ => by simpa only [γ, V] using
          (intrJacobi_diff (I := I) g hEnorm p u (v j) s).1)
        (fun s _ => by simpa only [γ, V] using
          (intrJacobi_diff (I := I) g hEnorm p u (v i) s).2)
        (fun s _ => by simpa only [γ, V] using
          (intrJacobi_diff (I := I) g hEnorm p u (v j) s).2)
        (fun s _ => by
          change IsJacobiAt (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm p u)
            (intrinsicJacobi (I := I) g hEnorm p u (v i)) s
          exact intrinsic_jacobi (I := I) g hEnorm p (u : E) (v i : E) s)
        (fun s _ => by
          change IsJacobiAt (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm p u)
            (intrinsicJacobi (I := I) g hEnorm p u (v j)) s
          exact intrinsic_jacobi (I := I) g hEnorm p (u : E) (v j : E) s)
        (by simp [V]) (by simp [V]) t ⟨ht.1.le, ht.2.le⟩
    have hJ : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
        IsJacobiAt (I := I) g γ (V i) t := by
      intro t ht i
      change IsJacobiAt (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p u)
        (intrinsicJacobi (I := I) g hEnorm p u (v i)) t
      exact intrinsic_jacobi (I := I) g hEnorm p (u : E) (v i : E) t
    have hRicγ : ∀ t ∈ Set.Ioo (0 : Real) b,
        -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) *
            g.inner (γ t) (curveVelocity (I := I) γ t)
              (curveVelocity (I := I) γ t) ≤
          ricciTensor (I := I) g (γ t)
            (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t) := by
      intro t ht
      simpa only [γ] using hRic hd t ht
    have hRatio : ∃ C : Real, 0 < C ∧
        ∀ᶠ t in 𝓝[>] (0 : Real),
          C ≤ curveDensity (I := I) g γ V t /
            hypDensity (q * ell) d t := by
      obtain ⟨C, hC, hraw⟩ :=
        radialRatio_auto (I := I) g p (u : E) (fun i => (v i : E))
          (q * ell) (mul_nonneg hq hell.le) hv
      have hcurve :
          ∀ᶠ t in 𝓝[>] (0 : Real),
            γ t = radialCurve (I := I) g p (u : E) t := by
        filter_upwards [intrinsic_geodesic_and_jacobi_eventually_eq_radial (I := I) g hEnorm p (u : E) (0 : E)]
          with t ht
        simpa only [γ] using ht.1
      have hfield_i : ∀ i,
          ∀ᶠ t in 𝓝[>] (0 : Real),
            (V i t : E) =
              (radialJacobiField (I := I) g p (u : E) (v i : E) t : E) := by
        intro i
        filter_upwards [
          intrinsic_geodesic_and_jacobi_eventually_eq_radial (I := I) g hEnorm p (u : E) (v i : E)] with t ht
        simpa only [V] using ht.2
      have hfields :
          ∀ᶠ t in 𝓝[>] (0 : Real), ∀ i,
            (V i t : E) =
              (radialJacobiField (I := I) g p (u : E) (v i : E) t : E) :=
        Filter.eventually_all.2 hfield_i
      refine ⟨C, hC, ?_⟩
      filter_upwards [hraw, hcurve, hfields] with t hrt hct hft
      have hgram :
          curveGram (I := I) g γ V t =
            curveGram (I := I) g
              (radialCurve (I := I) g p (u : E))
              (fun i => radialJacobiField (I := I) g p
                (u : E) (v i : E)) t := by
        ext i j
        simp only [curveGram, Matrix.of_apply]
        rw [hct, hft i, hft j]
      calc
        C ≤ curveDensity (I := I) g
              (radialCurve (I := I) g p (u : E))
              (fun i => radialJacobiField (I := I) g p
                (u : E) (v i : E)) t /
              hypDensity (q * ell) (Fintype.card (Fin d)) t := hrt
        _ = curveDensity (I := I) g γ V t /
              hypDensity (q * ell) d t := by
          rw [Fintype.card_fin]
          simp only [curveDensity, hgram]
    have hmean := curveMean_le_on
      (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
      g γ V q ell b hq hell (Fintype.card_fin d) hd hγ hspeed
      hVperp hDVperp hVdiff hDVdiff hLI hW hJ hRicγ hRatio
    have hone : (1 : Real) ∈ Set.Ioo (0 : Real) b :=
      ⟨zero_lt_one, hb⟩
    have hmean1 := hmean 1 hone
    have hhyp :=
      hypMeanCurv_le d (mul_nonneg hq hell.le) (by norm_num : (0 : Real) < 1)
    have hrawBound :
        curveMean (I := I) g γ V 1 ≤
          (d : Real) + (d : Real) * q * ell := by
      calc
        curveMean (I := I) g γ V 1 ≤
            hypMeanCurv (q * ell) d 1 := hmean1
        _ ≤ (d : Real) / 1 + (d : Real) * (q * ell) := hhyp
        _ = (d : Real) + (d : Real) * q * ell := by ring
    apply (div_le_iff₀ hell).2
    calc
      curveMean (I := I) g γ V 1 ≤
          (d : Real) + (d : Real) * q * ell := hrawBound
      _ = ((d : Real) / ell + (d : Real) * q) * ell := by
        rw [add_mul, div_mul_cancel₀ _ hell.ne']

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
