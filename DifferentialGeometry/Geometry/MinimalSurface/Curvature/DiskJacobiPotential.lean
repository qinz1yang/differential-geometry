import DifferentialGeometry.Geometry.MinimalSurface.Curvature.ScalarGaussTrace
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.ContractedBianchi
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold _root_.Topology BigOperators

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem normal_jacobi_coefficient_eq_scalar_gauss_of_zero_mean_curvature_complex
    (N : TopologicalSpace.Opens ℂ) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hdim : Module.finrank ℝ E = 3) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (z : N) (ν : TangentSpace 𝓘(ℝ, E) (U z))
    (hunit : g.inner (U z) ν ν = 1)
    (hnormal : ∀ v : TangentSpace 𝓘(ℝ, ℂ) z, g.inner (U z) ν
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) z v) = 0)
    (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z))
    (hb : ∀ i j, (g.pullback (fun q : N => U q) hU hi).inner z (b i) (b j) =
      if i = j then 1 else 0)
    (hmean : ∑ i : Fin 2,
      secondFundamentalFormAmbientAt (g.pullback (fun q : N => U q) hU hi)
        g (fun q : N => U q) z (b i) (b i) = 0) :
    let gN := g.pullback (fun q : N => U q) hU hi
    let P : Fin 2 → TangentSpace 𝓘(ℝ, E) (U z) := fun i =>
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (b i)
    let II := secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
    ((∑ i : Fin 2, g.inner (U z)
        ((riemannOp (LeviCivita g) (U z)) ν (P i) (P i)) ν) +
      ∑ i : Fin 2, ∑ j : Fin 2,
        g.inner (U z) (II (b i) (b j)) (II (b i) (b j))) =
      (metricScalarAt g (U z) +
        ∑ i : Fin 2, ∑ j : Fin 2,
          g.inner (U z) (II (b i) (b j)) (II (b i) (b j))) / 2 -
        metricScalarAt gN z / 2 := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let gN := g.pullback (fun q : N => U q) hU hi
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U z)
  let n : E := ν
  let d : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => U q) z
  let P : Fin 2 → E := fun i => d (b i)
  let Q : ℂ →L[ℝ] ℂ →L[ℝ] E :=
    secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
  let S : ℝ := ∑ i : Fin 2, ∑ j : Fin 2, B (Q (b i) (b j)) (Q (b i) (b j))
  let R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E := riemannOp (LeviCivita g) (U z)
  let Ric : E →L[ℝ] E →L[ℝ] ℝ := ricciTensor g (U z)
  have hbN : ∀ i j, gN.inner z (b i) (b j) = if i = j then 1 else 0 := hb
  have hP (i j : Fin 2) : B (P i) (P j) = if i = j then 1 else 0 := hb i j
  let F : Fin 3 → E := Fin.cons n P
  have hF : ∀ i j : Fin 3, B (F i) (F j) = if i = j then 1 else 0 := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · change B n n = if (0 : Fin 3) = 0 then 1 else 0
        rw [ite_eq_left rfl]
        change g.inner (U z) ν ν = 1
        exact hunit
      · change B n (P j) = if (0 : Fin 3) = j.succ then 1 else 0
        rw [ite_eq_right (Fin.succ_ne_zero j).symm]
        exact hnormal (b j)
    · refine Fin.cases ?_ (fun j => ?_) j
      · change B (P i) n = if i.succ = (0 : Fin 3) then 1 else 0
        rw [ite_eq_right (Fin.succ_ne_zero i)]
        exact (g.symm (U z) (P i) ν).trans (hnormal (b i))
      · change B (P i) (P j) = if i.succ = j.succ then 1 else 0
        simpa only [Fin.succ_inj] using hP i j
  let F' : Fin (Module.finrank ℝ E) → E := fun i => F (Fin.cast hdim i)
  have hF' : ∀ i j : Fin (Module.finrank ℝ E),
      B (F' i) (F' j) = if i = j then 1 else 0 := by
    intro i j
    rw [hF]
    simp only [Fin.cast_inj]
  have hRic : Ric n n = ∑ i : Fin 3, B (R (F i) n n) (F i) := by
    calc
      Ric n n = ∑ i : Fin (Module.finrank ℝ E), B (R (F' i) n n) (F' i) :=
        ricciTensor_eq_orthonormal_trace g (U z) ν ν F' hF'
      _ = ∑ i : Fin 3, B (R (F i) n n) (F i) :=
        Fintype.sum_equiv (finCongr hdim)
          (fun i => B (R (F' i) n n) (F' i))
          (fun i => B (R (F i) n n) (F i)) (fun _ => rfl)
  have hzero : B (R n n n) n = 0 := by
    have hs := riemannOp_swap (LeviCivita g) (U z) ν ν ν
    have h := congrArg (fun v : E => B v n) hs
    change B (R n n n) n = B (-(R n n n)) n at h
    simp only [map_neg, _root_.neg_apply] at h
    linarith
  have hpair (i : Fin 2) : B (R (P i) n n) (P i) = B (R n (P i) (P i)) n :=
    (riemannOp_inner_pair_symm g (U z) ν (P i) (P i) ν).symm
  have hnormalRic : Ric n n = ∑ i : Fin 2, B (R n (P i) (P i)) n := by
    rw [hRic, Fin.sum_univ_succ]
    change B (R n n n) n + (∑ i : Fin 2, B (R (P i) n n) (P i)) = _
    rw [hzero, zero_add]
    exact Finset.sum_congr rfl (fun i _ => hpair i)
  have hscalar : metricScalarAt g (U z) =
      Ric n n + ∑ i : Fin 2, Ric (P i) (P i) := by
    calc
      metricScalarAt g (U z) =
          ∑ i : Fin (Module.finrank ℝ E), Ric (F' i) (F' i) :=
        (metricScalar_eq_scal g (U z)).trans
          (scalarCurv_eq_orthonormal_trace g (U z) F' hF')
      _ = ∑ i : Fin 3, Ric (F i) (F i) :=
        Fintype.sum_equiv (finCongr hdim)
          (fun i => Ric (F' i) (F' i)) (fun i => Ric (F i) (F i)) (fun _ => rfl)
      _ = Ric n n + ∑ i : Fin 2, Ric (P i) (P i) := by
        rw [Fin.sum_univ_succ]
        rfl
  have hgauss : (∑ i : Fin 2, Ric (P i) (P i)) =
      metricScalarAt g (U z) / 2 +
        metricRm04StandardAt gN z (b 0) (b 1) (b 1) (b 0) + S / 2 := by
    have h := ricci_tangent_trace_eq_scalar_gauss_of_zero_mean_curvature
      (gN := gN) (gM := g) (f := fun q : N => U q)
      hU (fun _ _ _ => rfl) z hdim b hbN hmean
    simp only [DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor] at h
    exact h
  have hK : metricRm04StandardAt gN z (b 0) (b 1) (b 1) (b 0) =
      metricScalarAt gN z / 2 := by
    have h := metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two
      gN Complex.finrank_real_complex z (b 0) (b 1) (b 1) (b 0)
    simpa [hbN] using h
  rw [hK] at hgauss
  rw [hnormalRic] at hscalar
  dsimp only
  rw [← DifferentialGeometry.mfderiv_restrict_open
    (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U N z]
  change (∑ i : Fin 2, B (R n (P i) (P i)) n) + S =
    (metricScalarAt g (U z) + S) / 2 - metricScalarAt gN z / 2
  linarith

end DifferentialGeometry.Geometry
