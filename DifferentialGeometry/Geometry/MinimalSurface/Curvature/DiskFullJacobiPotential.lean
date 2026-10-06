import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskJacobiPotential
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology BigOperators

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_smooth_full_jacobi_potential_of_zero_mean_curvature_complex
    (N : TopologicalSpace.Opens ℂ) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hdim : Module.finrank ℝ E = 3) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) ((𝓘(ℝ, E)).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hunit : ∀ q : N, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : N) (v : TangentSpace 𝓘(ℝ, ℂ) q),
      g.inner (U q) (ν q)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0)
    (hmean : ∀ (q : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, (g.pullback (fun p : N => U p) hU hi).inner q (b i) (b j) =
        if i = j then 1 else 0) →
      ∑ i : Fin 2, secondFundamentalFormAmbientAt
        (g.pullback (fun p : N => U p) hU hi) g (fun p : N => U p)
        q (b i) (b i) = 0) :
    let gN := g.pullback (fun q : N => U q) hU hi
    ∃ VJ : C^∞⟮𝓘(ℝ, ℂ), N; ℝ⟯,
      (∀ q : N, VJ q = scalarCurv gN q - scalarCurv g (U q) +
        ricciTensor g (U q) (ν q) (ν q)) ∧
      (∀ (q : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
        (∀ i j, gN.inner q (b i) (b j) = if i = j then 1 else 0) →
        let II := secondFundamentalFormAmbientAt gN g (fun p : N => U p) q
        VJ q = metricScalarAt gN q / 2 -
          (metricScalarAt g (U q) +
            ∑ i : Fin 2, ∑ j : Fin 2,
              g.inner (U q) (II (b i) (b j)) (II (b i) (b j))) / 2) ∧
      ∀ q : N, VJ q ≤ scalarCurv gN q / 2 - scalarCurv g (U q) / 2 := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let gN := g.pullback (fun q : N => U q) hU hi
  have hRicSection := (ricciTensor_contMDiff g).comp hU
  have happ : ContMDiff 𝓘(ℝ, ℂ) ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : N => (⟨U q, ricciTensor g (U q) (ν q) (ν q)⟩ :
        TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
    ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := fun q : N => U q) hRicSection hν hν
  have hRicSmooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
      (fun q : N => ricciTensor g (U q) (ν q) (ν q)) := by
    intro q
    have hq := happ q
    rw [Bundle.contMDiffAt_totalSpace] at hq
    exact hq.2
  let VJ : C^∞⟮𝓘(ℝ, ℂ), N; ℝ⟯ :=
    ⟨fun q => scalarCurv gN q - scalarCurv g (U q) +
        ricciTensor g (U q) (ν q) (ν q),
      ((scalarCurv_contMDiff gN).sub ((scalarCurv_contMDiff g).comp hU)).add
        hRicSmooth⟩
  have hcoeff (q : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q))
      (hb : ∀ i j, gN.inner q (b i) (b j) = if i = j then 1 else 0) :
      let II := secondFundamentalFormAmbientAt gN g (fun p : N => U p) q
      VJ q = metricScalarAt gN q / 2 -
        (metricScalarAt g (U q) +
          ∑ i : Fin 2, ∑ j : Fin 2,
            g.inner (U q) (II (b i) (b j)) (II (b i) (b j))) / 2 := by
    let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U q)
    let n : E := ν q
    let d : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q
    let P : Fin 2 → E := fun i => d (b i)
    let Q : ℂ →L[ℝ] ℂ →L[ℝ] E :=
      secondFundamentalFormAmbientAt gN g (fun p : N => U p) q
    let S : ℝ := ∑ i : Fin 2, ∑ j : Fin 2,
      B (Q (b i) (b j)) (Q (b i) (b j))
    let R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E := riemannOp (LeviCivita g) (U q)
    let Ric : E →L[ℝ] E →L[ℝ] ℝ := ricciTensor g (U q)
    have hP (i j : Fin 2) : B (P i) (P j) = if i = j then 1 else 0 := hb i j
    let F : Fin 3 → E := Fin.cons n P
    have hF : ∀ i j : Fin 3, B (F i) (F j) = if i = j then 1 else 0 := by
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · change B n n = if (0 : Fin 3) = 0 then 1 else 0
          rw [ite_eq_left rfl]
          change g.inner (U q) (ν q) (ν q) = 1
          exact hunit q
        · change B n (P j) = if (0 : Fin 3) = j.succ then 1 else 0
          rw [ite_eq_right (Fin.succ_ne_zero j).symm]
          exact hnormal q (b j)
      · refine Fin.cases ?_ (fun j => ?_) j
        · change B (P i) n = if i.succ = (0 : Fin 3) then 1 else 0
          rw [ite_eq_right (Fin.succ_ne_zero i)]
          exact (g.symm (U q) (P i) (ν q)).trans (hnormal q (b i))
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
          ricciTensor_eq_orthonormal_trace g (U q) (ν q) (ν q) F' hF'
        _ = ∑ i : Fin 3, B (R (F i) n n) (F i) :=
          Fintype.sum_equiv (finCongr hdim)
            (fun i => B (R (F' i) n n) (F' i))
            (fun i => B (R (F i) n n) (F i)) (fun _ => rfl)
    have hzero : B (R n n n) n = 0 := by
      have hs := riemannOp_swap (LeviCivita g) (U q) (ν q) (ν q) (ν q)
      have h := congrArg (fun v : E => B v n) hs
      change B (R n n n) n = B (-(R n n n)) n at h
      simp only [map_neg, _root_.neg_apply] at h
      linarith
    have hpair (i : Fin 2) : B (R (P i) n n) (P i) = B (R n (P i) (P i)) n :=
      (riemannOp_inner_pair_symm g (U q) (ν q) (P i) (P i) (ν q)).symm
    have hnormalRic : Ric n n = ∑ i : Fin 2, B (R n (P i) (P i)) n := by
      rw [hRic, Fin.sum_univ_succ]
      change B (R n n n) n + (∑ i : Fin 2, B (R (P i) n n) (P i)) = _
      rw [hzero, zero_add]
      exact Finset.sum_congr rfl (fun i _ => hpair i)
    have hgauss :=
      normal_jacobi_coefficient_eq_scalar_gauss_of_zero_mean_curvature_complex
        N g hdim U hU hi q (ν q) (hunit q) (hnormal q) b hb (hmean q b hb)
    dsimp only at hgauss
    rw [← DifferentialGeometry.mfderiv_restrict_open
      (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U N q] at hgauss
    change (∑ i : Fin 2, B (R n (P i) (P i)) n) + S =
      (metricScalarAt g (U q) + S) / 2 - metricScalarAt gN q / 2 at hgauss
    rw [← hnormalRic] at hgauss
    change scalarCurv gN q - scalarCurv g (U q) + Ric n n =
      metricScalarAt gN q / 2 - (metricScalarAt g (U q) + S) / 2
    simp only [metricScalar_eq_scal] at hgauss ⊢
    linarith
  refine ⟨VJ, fun _ => rfl, hcoeff, ?_⟩
  intro q
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis gN q
  have hdimTwo : Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℂ) q) = 2 := by
    change Module.finrank ℝ ℂ = 2
    rw [Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin]
  let e := finCongr hdimTwo
  let b₂ := b.reindex e
  have hb₂ (i j : Fin 2) : gN.inner q (b₂ i) (b₂ j) = if i = j then 1 else 0 := by
    change gN.inner q ((b.reindex e) i) ((b.reindex e) j) = _
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb]
    simp only [Equiv.apply_eq_iff_eq]
  let II := secondFundamentalFormAmbientAt gN g (fun p : N => U p) q
  have hS : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2,
      g.inner (U q) (II (b₂ i) (b₂ j)) (II (b₂ i) (b₂ j)) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact DifferentialGeometry.metric_inner_self_nonneg g (U q) (II (b₂ i) (b₂ j))
  have hc := hcoeff q b₂ hb₂
  dsimp only at hc
  simp only [metricScalar_eq_scal] at hc
  linarith

end DifferentialGeometry.Geometry
