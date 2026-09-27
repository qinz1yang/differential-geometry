import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange

set_option autoImplicit false

noncomputable section
open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.CheegerGromovCompactness

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

theorem exists_manifold_uniform_iterated_covariant_derivative_norm_comparison
    (q₂ p : ℕ) {C B : ℝ} (hC : 1 ≤ C) (hB : 0 ≤ B) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [T2Space M] (u : Set M), IsOpen u →
      ∀ (g gRef : SmoothRiemannianMetric I M),
      (∀ x ∈ u, ∀ v : TangentSpace I x,
        C⁻¹ * gRef.inner x v v ≤ g.inner x v v ∧
          g.inner x v v ≤ C * gRef.inner x v v) →
      (∀ x ∈ u, ∀ j : ℕ, 1 ≤ j → j ≤ p →
        Real.sqrt (normSq0S g x (2 + j)
          (iterCov gRef 2 (metricTensorField g) j x)) ≤ B) →
      ∀ T : Tensor0SField (I := I) (M := M) ∞ q₂,
      ∀ x ∈ u, ∀ r : ℕ, 0 < r → r ≤ p →
        Real.sqrt (normSq0S g x (q₂ + r) (iterCov g q₂ T r x)) ≤
          Real.sqrt (C ^ (q₂ + r)) *
            (Real.sqrt (normSq0S gRef x (q₂ + r) (iterCov gRef q₂ T r x)) +
              Cc * ∑ k ∈ Finset.range r,
                Real.sqrt (normSq0S gRef x (q₂ + k) (iterCov gRef q₂ T k x))) := by
  classical
  let C0 : ℝ := Real.sqrt (Module.finrank ℝ E) * 2
  let L : ℝ := 2 ^ (2 + p) * B
  have hL0 : 0 ≤ L := mul_nonneg (by positivity) hB
  let Cc := iteratedRecurrenceConstant
    (fun c => inverseContractionRecurrenceConstant C0
      (|(1 / 2 : ℝ)| + |(1 / 2 : ℝ)| + |-(1 / 2 : ℝ)|) L c) p q₂
  have hCc : 0 ≤ Cc := iterated_recurrence_constant_nonneg
    (fun c => inverse_contraction_recurrence_constant_nonneg hL0 c) p q₂
  refine ⟨Cc, hCc, ?_⟩
  intro M _ _ _ _ u hu g gRef hequiv hgK T x hx r hr0 hrp
  let e₀ := trivializationAt E (TangentSpace I : M → Type _) x
  obtain ⟨basisE, u', η, hu', hxu', hsub, hη0, hsmall, hnear, hON, hcomp, _⟩ :=
    exists_goodFrame_compBound (I := I) g x
  let frame : Fin (Module.finrank Real E) → (y : M) → TangentSpace I y :=
    fun a y => e₀.localFrame basisE a y
  let w : Set M := u' ∩ u
  have hwopen : IsOpen w := hu'.inter hu
  have hxw : x ∈ w := ⟨hxu', hx⟩
  have hwsub : w ⊆ e₀.baseSet := fun _ hz => hsub hz.1
  let hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame w :=
    (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub
  have hframeS : ∀ d : Fin (Module.finrank Real E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) w :=
    fun d => (frame_e_mdiffOn e₀ basisE d).mono hwsub
  have hchrG : ∀ d i j : Fin (Module.finrank Real E), ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        frame hframe y d i j) w :=
    fun d i j => ((lcChrist_e_mdiffOn e₀ g basisE d i j).mono hwsub).congr
      (fun z hz => chrInFrame_mono (I := I) (leviCivitaConnectionOfMetric (I := I) g)
        frame (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) hwsub hz d i j)
  have hchrH : ∀ d i j : Fin (Module.finrank Real E), ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
        frame hframe y d i j) w :=
    fun d i j => ((lcChrist_e_mdiffOn e₀ gRef basisE d i j).mono hwsub).congr
      (fun z hz => chrInFrame_mono (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
        frame (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) hwsub hz d i j)
  have hgsm := fun k => (gCompField_mdiffOn e₀ g basisE k).mono hwsub
  have hTsm := fun k => (tensorComp_mdiffOn e₀ T basisE k).mono hwsub
  have hGinv : ∀ z ∈ w, compL2 (ginvCompField (I := I) e₀ g basisE z) ≤ C0 := by
    intro z hz
    have h := movingGinv_le (I := I) e₀ g g basisE 1 zero_lt_one
      (fun v => by simp) η hη0 hsmall (fun i j => hnear z hz.1 i j)
    simpa only [C0, Fintype.card_fin, mul_one] using h
  have hinv : ∀ z ∈ w, ∀ c e : Fin (Module.finrank Real E),
      (∑ l, frameComp0S (I := I) (metricTensorField (I := I) g) frame z
          (Fin.snoc (fun _ : Fin 1 => l) c) *
        ginvCompField (I := I) e₀ g basisE z (Fin.snoc (fun _ : Fin 1 => e) l)) =
          if c = e then 1 else 0 :=
    fun z hz c e => ginv_hinv (I := I) e₀ g basisE (hwsub hz) c e
  have hgKcomp : ∀ z ∈ w, ∀ j, 1 ≤ j → j ≤ p →
      compL2 (iterCovComp (I := I) frame
        (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe y)
        (frameComp0S (I := I) (metricTensorField (I := I) g) frame) j z) ≤ L * 1 := by
    intro z hz j hj1 hjp
    have htow := compL2_tower_le (I := I) (gM := gRef) (gRef := g) (r := 2)
      (T := metricTensorField (I := I) g) frame hframe hwopen hz
      (fun s A => hcomp z (hwsub hz) hz.1 s A) j
    have hbound := hgK z hz.2 j hj1 hjp
    calc
      _ ≤ 2 ^ (2 + j) * Real.sqrt (normSq0S g z (2 + j)
          (iterCov gRef 2 (metricTensorField g) j z)) := htow
      _ ≤ 2 ^ (2 + j) * B :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ ≤ L * 1 := by
        simpa only [L, mul_one] using
          mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 2 + j ≤ 2 + p)) hB
  have hcompF3 := iterated_covariant_derivative_comparison_bound
    hwopen g gRef frame hframe hframeS hchrG hchrH
    hgsm (frameComp0S (I := I) T frame) hTsm
    (ginvCompField (I := I) e₀ g basisE) hinv C0 L 1 hL0 zero_le_one le_rfl hGinv p hgKcomp
  have hON' : ∀ i j : Fin (Module.finrank Real E),
      g.inner x (hframe.toBasisAt hxw i) (hframe.toBasisAt hxw j) =
        if i = j then 1 else 0 := by
    intro i j
    simpa only [IsLocalFrameOn.toBasisAt_coe] using hON i j
  have hinvON := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g
    (hframe.toBasisAt hxw) hON'
  have hF3 : ∀ s : ℕ, 0 < s → s ≤ p →
      Real.sqrt (normSq0S (I := I) g x (q₂ + s) (iterCov (I := I) g q₂ T s x)) ≤
        Real.sqrt (normSq0S (I := I) g x (q₂ + s) (iterCov (I := I) gRef q₂ T s x)) +
        1 * Cc * ∑ k ∈ Finset.range s,
          Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) := by
    intro s hs0 hsp
    apply sqrt_norm_sq_iter_cov_le_of_component_bound
      hwopen g gRef T frame hframe hxw hinvON 1 Cc s
    simpa only [Cc] using hcompF3 x hxw s hs0 hsp
  simpa only [one_mul] using
    covariant_derivative_norm_comparison_of_intrinsic_metric_equivalence g gRef T p
      (x := x) hC (hequiv x hx) 1 Cc zero_le_one hCc hF3 r hr0 hrp

private theorem metricDerivNorm_eq_sqrt_normSq_iterCov {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (A B R : SmoothRiemannianMetric I M) (q : ℕ) (x : M) :
    metricDerivNorm q A B R x =
      Real.sqrt (normSq0S R x (2 + q)
        (iterCov R 2 (metricTensorField A - metricTensorField B) q x)) := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis R x
  exact metricDerivNorm_eq_iterCov A B R q b
    (metricInverseInBasis_identity_of_orthonormal R b hb)

theorem exists_manifold_uniform_metric_deriv_norm_reference_bound
    (p : ℕ) {C B : ℝ} (hC : 1 ≤ C) (hB : 0 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [T2Space M] (u : Set M), IsOpen u →
      ∀ (gRef g : SmoothRiemannianMetric I M),
      (∀ x ∈ u, ∀ v : TangentSpace I x,
        C⁻¹ * gRef.inner x v v ≤ g.inner x v v ∧
          g.inner x v v ≤ C * gRef.inner x v v) →
      (∀ x ∈ u, ∀ j : ℕ, 1 ≤ j → j ≤ p →
        Real.sqrt (normSq0S g x (2 + j)
          (iterCov gRef 2 (metricTensorField g) j x)) ≤ B) →
      ∀ (A B : SmoothRiemannianMetric I M), ∀ r : ℕ, r ≤ p → ∀ x ∈ u,
        metricDerivNorm r A B g x ≤
          D * ∑ k ∈ Finset.range (p + 1), metricDerivNorm k A B gRef x := by
  classical
  obtain ⟨Cc, hCc, hcomp⟩ :=
    exists_manifold_uniform_iterated_covariant_derivative_norm_comparison.{u} (I := I)
      2 p hC hB
  let F := Real.sqrt (C ^ (2 + p))
  have hF : 0 ≤ F := Real.sqrt_nonneg _
  refine ⟨F * (1 + Cc), mul_nonneg hF (by positivity), ?_⟩
  intro M _ _ _ _ u hu gRef g heq hb A B r hr x hx
  let S := ∑ k ∈ Finset.range (p + 1), metricDerivNorm k A B gRef x
  have hn (k : ℕ) : 0 ≤ metricDerivNorm k A B gRef x := Real.sqrt_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => hn k
  have hsingle : metricDerivNorm r A B gRef x ≤ S :=
    Finset.single_le_sum (fun k _ => hn k) (Finset.mem_range.mpr (by omega))
  have hsum : (∑ k ∈ Finset.range r, metricDerivNorm k A B gRef x) ≤ S := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (by omega)
    · intro k _ _
      exact hn k
  have hfac : Real.sqrt (C ^ (2 + r)) ≤ F :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ hC (by omega))
  by_cases hr0 : r = 0
  · subst r
    have hzero := diffNorm_zero_change A B g gRef x hC (heq x hx)
    calc
      metricDerivNorm 0 A B g x ≤
          Real.sqrt (C ^ 2) * metricDerivNorm 0 A B gRef x := hzero
      _ ≤ F * S := mul_le_mul hfac hsingle (hn 0) hF
      _ ≤ (F * (1 + Cc)) * S := by nlinarith [mul_nonneg hF (mul_nonneg hCc hS)]
  · have hc := hcomp u hu g gRef heq hb (metricTensorField A - metricTensorField B)
      x hx r (Nat.pos_of_ne_zero hr0) hr
    simp_rw [← metricDerivNorm_eq_sqrt_normSq_iterCov] at hc
    calc
      metricDerivNorm r A B g x ≤ Real.sqrt (C ^ (2 + r)) *
          (metricDerivNorm r A B gRef x + Cc *
            ∑ k ∈ Finset.range r, metricDerivNorm k A B gRef x) := hc
      _ ≤ F * (S + Cc * S) := by
        exact mul_le_mul hfac
          (add_le_add hsingle (mul_le_mul_of_nonneg_left hsum hCc))
          (add_nonneg (hn r) (mul_nonneg hCc
            (Finset.sum_nonneg fun k _ => hn k))) hF
      _ = (F * (1 + Cc)) * S := by ring

end DifferentialGeometry.CheegerGromovCompactness
