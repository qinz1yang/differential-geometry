import DifferentialGeometry.Analysis.Convex.MovingSetDistance
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIveyRegionReaction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Bundle Filter Set
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Topology RealInnerProductSpace BigOperators
open scoped Matrix.Norms.Frobenius

abbrev HI3 := EuclideanSpace ℝ (Fin 3 × Fin 3)

theorem hamiltonIveyRegion_seqClosedGraph
    {K T : ℝ} (hK : 0 < K) :
    ∀ τ₀ : ℝ, τ₀ ∈ Set.Icc 0 T → ∀ q : HI3,
      ∀ (τn : ℕ → ℝ) (qn : ℕ → HI3),
        Tendsto τn atTop (𝓝 τ₀) →
        Tendsto qn atTop (𝓝 q) →
          (∀ᶠ n in atTop, τn n ∈ Set.Icc 0 T ∧
            qn n ∈ hamiltonIveyConvexMatrixRegionEuclid K (τn n)) → q ∈
            hamiltonIveyConvexMatrixRegionEuclid K τ₀ := by
  classical
  intro τ₀ hτ₀ q τn qn hτn hqn hmem
  refine (hamiltonIveyConvexMatrixRegionEuclid_mem_iff_forall_support_le hK hτ₀.1 q).mpr ?_
  intro ν hν
  rcases (mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ₀.1 ν).mp hν with hneg | hzero
  · have hsupp : ContinuousOn
        (fun τ : ℝ => hamiltonIveyConvexMatrixRegionSupportEuclid K τ ν) (Set.Icc 0 T) :=
      hamiltonIveyConvexMatrixRegionSupportEuclid_continuousOn (K := K) (T := T) hK ν hneg
    have hτwithin : Tendsto τn atTop (𝓝[Set.Icc 0 T] τ₀) :=
      (tendsto_nhdsWithin_iff.mpr ⟨hτn, hmem.mono (fun n hn => hn.1)⟩)
    have hsuppT : Tendsto (fun n : ℕ =>
        hamiltonIveyConvexMatrixRegionSupportEuclid K (τn n) ν)
        atTop (𝓝 (hamiltonIveyConvexMatrixRegionSupportEuclid K τ₀ ν)) :=
      (hsupp.continuousWithinAt hτ₀).tendsto.comp hτwithin
    have hinnerT : Tendsto (fun n : ℕ => inner ℝ ν (qn n)) atTop (𝓝 (inner ℝ ν q)) := by
      have hc : ContinuousAt (fun x : HI3 => inner ℝ ν x) q :=
        (continuous_const.inner continuous_id).continuousAt
      simpa using hc.tendsto.comp hqn
    have hle : ∀ᶠ n in atTop,
        inner ℝ ν (qn n) ≤ hamiltonIveyConvexMatrixRegionSupportEuclid K (τn n) ν := by
      filter_upwards [hmem] with n hn
      have hfs : ν ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K (τn n)) := by
        rw [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hn.1.1]
        exact Or.inl hneg
      exact (hamiltonIveyConvexMatrixRegionEuclid_mem_iff_forall_support_le
        hK hn.1.1 (qn n)).mp hn.2 ν hfs
    have hlim : Tendsto (fun n : ℕ =>
        hamiltonIveyConvexMatrixRegionSupportEuclid K (τn n) ν - inner ℝ ν (qn n))
        atTop (𝓝 (hamiltonIveyConvexMatrixRegionSupportEuclid K τ₀ ν - inner ℝ ν q)) :=
      hsuppT.sub hinnerT
    have hnonneg : ∀ᶠ n in atTop,
        (0 : ℝ) ≤ hamiltonIveyConvexMatrixRegionSupportEuclid K (τn n) ν - inner ℝ ν (qn n) := by
      filter_upwards [hle] with n hn
      linarith
    have hge : (0 : ℝ) ≤ hamiltonIveyConvexMatrixRegionSupportEuclid K τ₀ ν - inner ℝ ν q :=
      ge_of_tendsto hlim hnonneg
    linarith
  · have hsupp0 : ∀ τ : ℝ, hamiltonIveyConvexMatrixRegionSupportEuclid K τ ν = 0 := by
      intro τ
      unfold hamiltonIveyConvexMatrixRegionSupportEuclid
      have hν₁ : (symmEuclid_isHermitian ν).eigenvalues₀ 0 = 0 := by
        have hze : (symmEuclid_isHermitian ν).eigenvalues = 0 := by
          exact (Matrix.IsHermitian.eigenvalues_eq_zero_iff
            (hA := symmEuclid_isHermitian ν)).mpr hzero
        let e : Fin 3 ≃ Fin 3 := Fintype.equivOfCardEq (Fintype.card_fin 3)
        have h0 : (symmEuclid_isHermitian ν).eigenvalues (e 0) = 0 := congrFun hze (e 0)
        have hrel : (symmEuclid_isHermitian ν).eigenvalues (e 0) =
            (symmEuclid_isHermitian ν).eigenvalues₀ 0 := by
          change (symmEuclid_isHermitian ν).eigenvalues₀
              ((Fintype.equivOfCardEq (Fintype.card_fin 3)).symm (e 0)) =
              (symmEuclid_isHermitian ν).eigenvalues₀ 0
          congr
          exact Equiv.symm_apply_apply e 0
        rwa [hrel] at h0
      rw [hν₁]
      simp
    have hinnerT : Tendsto (fun n : ℕ => inner ℝ ν (qn n)) atTop (𝓝 (inner ℝ ν q)) := by
      have hc : ContinuousAt (fun x : HI3 => inner ℝ ν x) q :=
        (continuous_const.inner continuous_id).continuousAt
      simpa using hc.tendsto.comp hqn
    have hle : ∀ᶠ n in atTop, inner ℝ ν (qn n) ≤ 0 := by
      filter_upwards [hmem] with n hn
      have hfs : ν ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K (τn n)) := by
        rw [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hn.1.1]
        exact Or.inr hzero
      have hqnle := (hamiltonIveyConvexMatrixRegionEuclid_mem_iff_forall_support_le
        hK hn.1.1 (qn n)).mp hn.2 ν hfs
      rwa [hsupp0 (τn n)] at hqnle
    have hlim : Tendsto (fun n : ℕ => -inner ℝ ν (qn n)) atTop (𝓝 (-inner ℝ ν q)) :=
      hinnerT.neg
    have hnonneg : ∀ᶠ n in atTop, (0 : ℝ) ≤ -inner ℝ ν (qn n) := by
      filter_upwards [hle] with n hn
      linarith
    have hge : (0 : ℝ) ≤ -inner ℝ ν q := ge_of_tendsto hlim hnonneg
    have hle0 : inner ℝ ν q ≤ 0 := by linarith
    rw [hsupp0 τ₀]
    exact hle0

theorem hamiltonIveyRegion_approx
    {K T : ℝ} (hK : 0 < K) :
    ∀ τ₀ : ℝ, τ₀ ∈ Set.Icc 0 T → ∀ q : HI3,
      q ∈ hamiltonIveyConvexMatrixRegionEuclid K τ₀ → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℝ, τ ∈ Set.Icc 0 T → |τ - τ₀| < δ →
          ∃ q' : HI3, q' ∈ hamiltonIveyConvexMatrixRegionEuclid K τ ∧ dist q' q < ε := by
  classical
  intro τ₀ hτ₀ q hqC ε hε
  let A : Matrix (Fin 3) (Fin 3) ℝ := euclidToMatrix q
  have hA : A.IsHermitian := by
    have hmem : A ∈ hamiltonIveyConvexMatrixRegion K τ₀ := by
      rwa [mem_hamiltonIveyConvexMatrixRegionEuclid_iff] at hqC
    rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hmem
    exact hmem.1
  let X : ℝ := max (-(hA.eigenvalues₀ 2)) 0
  let s : ℝ := A.trace
  have hXge : 0 ≤ X := by
    dsimp [X]
    exact le_max_right _ _
  have hbar : hamiltonIveyConvexBarrier K τ₀ X ≤ s := by
    have hmem : A ∈ hamiltonIveyConvexMatrixRegion K τ₀ := by
      rwa [mem_hamiltonIveyConvexMatrixRegionEuclid_iff] at hqC
    rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hmem
    have hX' : max (-sectionalRayleighMin3 A) 0 = X := by
      rw [sectionalRayleighMin3_eq_eigenvalue_min hA]
    have hb := hmem.2.2
    rw [hX'] at hb
    simpa [s] using hb
  have hBslice : ContinuousOn (fun τ : ℝ => hamiltonIveyConvexBarrier K τ X) (Set.Icc 0 T) := by
    have hfull := continuousOn_hamiltonIveyConvexBarrier_time_nonneg (K := K) (T := T) hK
    have hmap : ContinuousOn (fun τ : ℝ => (τ, X)) (Set.Icc 0 T) := by fun_prop
    have hsub : Set.MapsTo (fun τ : ℝ => (τ, X)) (Set.Icc 0 T)
        (Set.Icc 0 T ×ˢ Set.Ici 0) := by
      intro τ hτ
      exact ⟨hτ, hXge⟩
    exact hfull.comp hmap hsub
  let C₀ : ℝ := 9
  have hεC : 0 < ε / C₀ := by positivity
  have hc0 := hBslice.continuousWithinAt hτ₀
  rw [Metric.continuousWithinAt_iff] at hc0
  rcases hc0 (ε / C₀) hεC with ⟨δ₀, hδ₀pos, hδ₀⟩
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro τ hτ hτδ
  rcases hermitian_orthogonal_diagonalization hA with ⟨O, hO₁, hO₂⟩
  have hOtO : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hO₁
  let lam : Fin 3 → ℝ := hA.eigenvalues₀
  have hlamanti : Antitone lam := by
    dsimp [lam]
    exact hA.eigenvalues₀_antitone
  let c : ℝ := max (hamiltonIveyConvexBarrier K τ X - s) 0
  let d : Fin 3 → ℝ := ![lam 0 + c, lam 1 + c, lam 2]
  let A' : Matrix (Fin 3) (Fin 3) ℝ := O * Matrix.diagonal d * O.transpose
  let q' : HI3 := matrixToEuclid A'
  have hcge : 0 ≤ c := by
    dsimp [c]
    exact le_max_right _ _
  have hdanti : Antitone d := by
    intro i j hij
    dsimp [d]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · have h₁ := hlamanti (by decide : (0 : Fin 3) ≤ 1)
      linarith
    · have h₁ := hlamanti (by decide : (0 : Fin 3) ≤ 2)
      linarith
    · have h₁ := hlamanti (by decide : (1 : Fin 3) ≤ 2)
      linarith
  have hBle : hamiltonIveyConvexBarrier K τ X ≤ s + 2 * c := by
    have h1 : hamiltonIveyConvexBarrier K τ X - s ≤ c := by
      dsimp [c]
      exact le_max_left _ _
    have h1' : hamiltonIveyConvexBarrier K τ X ≤ s + c := by
      have h := sub_le_iff_le_add.mp h1
      simpa [add_comm] using h
    calc
      hamiltonIveyConvexBarrier K τ X ≤ s + c := h1'
      _ ≤ s + 2 * c := by
            have hc2 : c ≤ 2 * c := by
              calc c = 1 * c := (one_mul c).symm
              _ ≤ 2 * c := mul_le_mul_of_nonneg_right (by norm_num) hcge
            exact add_le_add le_rfl hc2
  have hD : Matrix.diagonal d ∈ hamiltonIveyConvexMatrixRegion K τ := by
    rw [hamiltonIveyConvexMatrixRegion_eq_violation]
    refine ⟨Matrix.isHermitian_diagonal d, ?_, ?_⟩
    · exact le_max_right _ _
    · have hd_eig : (Matrix.isHermitian_diagonal d).eigenvalues₀ = d :=
        diagonal_eigenvalues₀_eq_of_antitone d hdanti
      have hd_min : sectionalRayleighMin3 (Matrix.diagonal d) = d 2 := by
        rw [sectionalRayleighMin3_eq_eigenvalue_min (Matrix.isHermitian_diagonal d), hd_eig]
        rfl
      have hX' : max (-(d 2)) 0 = X := by
        have hd2 : d 2 = lam 2 := by
          dsimp [d]
        rw [hd2]
        rfl
      rw [hd_min, hX']
      have ht : (Matrix.diagonal d).trace = s + 2 * c := by
        have htr : A.trace = lam 0 + lam 1 + lam 2 := by
          have htrace : A.trace = ∑ i : Fin 3, hA.eigenvalues i :=
            Matrix.IsHermitian.trace_eq_sum_eigenvalues hA
          have hperm : (∑ i : Fin 3, hA.eigenvalues i) = ∑ j : Fin 3, hA.eigenvalues₀ j := by
            let e : Fin 3 ≃ Fin 3 := Fintype.equivOfCardEq (Fintype.card_fin 3)
            have hstep : (∑ i : Fin 3, hA.eigenvalues i) =
                ∑ i : Fin 3, hA.eigenvalues₀ (e.symm i) := by
              simp [Matrix.IsHermitian.eigenvalues, e]
              rfl
            rw [hstep]
            refine Finset.sum_bij (fun i _hi => e.symm i) (fun a ha => by simp) ?inj ?surj ?h
            · intro a₁ ha₁ a₂ ha₂ h
              exact e.symm.injective h
            · intro b hb
              refine ⟨e b, by simp, ?_⟩
              simp
            · intro a ha
              rfl
          rw [htrace, hperm]
          dsimp [lam]
          rw [Fin.sum_univ_three]
        rw [Matrix.trace_diagonal]
        dsimp [d, s, lam]
        have htr' : A.trace = lam 0 + lam 1 + lam 2 := htr
        have hsum : (∑ i : Fin 3, (![lam 0 + c, lam 1 + c, lam 2] : Fin 3 → ℝ) i) =
            (lam 0 + lam 1 + lam 2) + 2 * c := by
          simp only [Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val]
          ring
        rw [htr']
        simpa using hsum
      rw [ht]
      exact hBle
  have hQtA'Q : O.transpose * A' * O = Matrix.diagonal d := by
    dsimp [A']
    rw [show O.transpose * (O * Matrix.diagonal d * O.transpose) * O =
        (O.transpose * O) * Matrix.diagonal d * (O.transpose * O) by
      repeat rw [Matrix.mul_assoc]]
    rw [hOtO]
    simp
  have hA' : A' ∈ hamiltonIveyConvexMatrixRegion K τ := by
    exact (hamiltonIveyConvexMatrixRegion_orthogonal_conj (Q := O) hOtO hO₁).2 (by
      rwa [hQtA'Q])
  have hq'C : q' ∈ hamiltonIveyConvexMatrixRegionEuclid K τ := by
    rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
    simpa [q', A'] using hA'
  have hAeq : A = O * Matrix.diagonal lam * O.transpose := by
    calc
      A = O * (O.transpose * A * O) * O.transpose := by
            rw [show O * (O.transpose * A * O) * O.transpose =
                (O * O.transpose) * A * (O * O.transpose) by
              repeat rw [Matrix.mul_assoc]]
            rw [hO₁]
            simp
      _ = O * Matrix.diagonal lam * O.transpose := by
            rw [hO₂]
            rfl
  have hsub : A' - A = O * (Matrix.diagonal d - Matrix.diagonal lam) * O.transpose := by
    rw [hAeq]
    dsimp [A']
    rw [← Matrix.sub_mul (O * Matrix.diagonal d) (O * Matrix.diagonal lam) O.transpose]
    rw [← Matrix.mul_sub O (Matrix.diagonal d) (Matrix.diagonal lam)]
  have hO₂sq : ‖O‖ ^ 2 = (3 : ℝ) := by
    rw [Matrix.frobenius_norm_def, sq]
    rw [← Real.sqrt_eq_rpow]
    have hS : 0 ≤ (∑ i : Fin 3, ∑ j : Fin 3, ‖O i j‖ ^ (2 : ℝ)) := by
      exact Finset.sum_nonneg (fun i hi => by positivity)
    rw [← sq]
    rw [Real.sq_sqrt hS]
    have hsum : (∑ i : Fin 3, ∑ j : Fin 3, ‖O i j‖ ^ (2 : ℝ)) =
        (∑ i : Fin 3, (O * O.transpose) i i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      calc
        (∑ j : Fin 3, ‖O i j‖ ^ (2 : ℝ)) = ∑ j : Fin 3, O i j * O i j := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simp [Real.norm_eq_abs, pow_two]
        _ = ∑ j : Fin 3, O i j * (O.transpose j i) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rfl
        _ = (O * O.transpose) i i := (Matrix.mul_apply (M := O) (N := O.transpose)
              (k := i) (i := i)).symm
    have ht : (∑ i : Fin 3, (O * O.transpose) i i) = (3 : ℝ) := by
      rw [hO₁]
      simp
    rw [hsum, ht]
  have hOle : ‖O‖ ≤ 2 := by
    nlinarith [hO₂sq, norm_nonneg O]
  have hOtle : ‖O.transpose‖ ≤ 2 := by
    rw [Matrix.frobenius_norm_transpose]
    exact hOle
  have hd_norm : ‖Matrix.diagonal d - Matrix.diagonal lam‖ ≤ 2 * c := by
    rw [Matrix.diagonal_sub]
    have hD : d - lam = ![c, c, 0] := by
      funext i
      fin_cases i <;> dsimp [d, lam] <;> simp
    change ‖Matrix.diagonal (d - lam)‖ ≤ 2 * c
    rw [hD]
    have hf := Matrix.frobenius_norm_diagonal (v := (![c, c, 0] : Fin 3 → ℝ))
    rw [hf]
    have hsum : (∑ i : Fin 3, ‖(![c, c, 0] : Fin 3 → ℝ) i‖ ^ 2) = 2 * c ^ 2 := by
      rw [Fin.sum_univ_three]
      simp [sq_abs, Real.norm_eq_abs]
      ring
    have hnorm : ‖WithLp.toLp 2 (![c, c, 0] : Fin 3 → ℝ)‖ =
        Real.sqrt (2 * c ^ 2) := by
      rw [PiLp.norm_eq_of_L2]
      rw [show (∑ i : Fin 3, ‖(WithLp.toLp 2 (![c, c, 0] : Fin 3 → ℝ)).ofLp i‖ ^ 2) =
          (∑ i : Fin 3, ‖(![c, c, 0] : Fin 3 → ℝ) i‖ ^ 2) by
        simp]
      rw [hsum, Real.sqrt_eq_rpow]
    rw [hnorm]
    have h₁ : Real.sqrt (2 * c ^ 2) ≤ Real.sqrt ((2 * c) ^ 2) :=
      (Real.sqrt_le_sqrt_iff (by positivity : 0 ≤ (2 * c) ^ 2)).2 (by nlinarith)
    rwa [Real.sqrt_sq (by positivity : 0 ≤ 2 * c)] at h₁
  have hnorm : ‖A' - A‖ ≤ 9 * c := by
    rw [hsub]
    calc
      ‖O * (Matrix.diagonal d - Matrix.diagonal lam) * O.transpose‖
          ≤ ‖O * (Matrix.diagonal d - Matrix.diagonal lam)‖ * ‖O.transpose‖ :=
            Matrix.frobenius_norm_mul (O * (Matrix.diagonal d - Matrix.diagonal lam)) O.transpose
      _ ≤ (‖O‖ * ‖Matrix.diagonal d - Matrix.diagonal lam‖) * ‖O.transpose‖ := by
            exact mul_le_mul_of_nonneg_right
              (Matrix.frobenius_norm_mul O (Matrix.diagonal d - Matrix.diagonal lam)) (norm_nonneg _)
      _ ≤ (2 * (2 * c)) * 2 := by
            exact mul_le_mul (mul_le_mul hOle hd_norm (norm_nonneg _) (by positivity))
              hOtle (by positivity) (by positivity)
      _ ≤ 9 * c := by nlinarith
  have hdist : dist q' q ≤ 9 * c := by
    rw [dist_eq_norm]
    have hqA : q = matrixToEuclid A := by
      dsimp [A]
      exact (matrixToEuclid_euclidToMatrix q).symm
    have hq' : q' - q = matrixToEuclid (A' - A) := by
      rw [hqA]
      dsimp [q']
      rw [matrixToEuclid_sub]
    rw [hq']
    rw [matrixToEuclid_norm]
    exact hnorm
  have hc_le : c ≤ |hamiltonIveyConvexBarrier K τ X - hamiltonIveyConvexBarrier K τ₀ X| := by
    dsimp [c]
    by_cases h : hamiltonIveyConvexBarrier K τ X ≤ s
    · have h' : hamiltonIveyConvexBarrier K τ X - s ≤ 0 := by linarith
      rw [max_eq_right h']
      exact abs_nonneg _
    · have h' : s < hamiltonIveyConvexBarrier K τ X := lt_of_not_ge h
      have h'' : 0 ≤ hamiltonIveyConvexBarrier K τ X - s := by linarith
      have hmax : max (hamiltonIveyConvexBarrier K τ X - s) 0 =
          hamiltonIveyConvexBarrier K τ X - s := max_eq_left h''
      rw [hmax]
      have h₁ : hamiltonIveyConvexBarrier K τ X - s ≤
          hamiltonIveyConvexBarrier K τ X - hamiltonIveyConvexBarrier K τ₀ X := by linarith
      exact le_trans h₁ (le_abs_self _)
  have hδ : |hamiltonIveyConvexBarrier K τ X - hamiltonIveyConvexBarrier K τ₀ X| < ε / C₀ := by
    have hd := hδ₀ (x := τ) hτ (by simpa [Real.dist_eq, abs_sub_comm] using hτδ)
    simpa [Real.dist_eq, abs_sub_comm] using hd
  have hclt : c < ε / C₀ := lt_of_le_of_lt hc_le hδ
  have hdlt : dist q' q < ε := by
    have h₁ : dist q' q ≤ 9 * c := hdist
    have h₂ : 9 * c < ε := by
      have hc' : c < ε / 9 := by simpa [C₀] using hclt
      nlinarith
    exact lt_of_le_of_lt h₁ h₂
  exact ⟨q', hq'C, hdlt⟩

theorem continuousOn_infDist_hamiltonIveyRegion
    {K T : ℝ} (hK : 0 < K) :
    ContinuousOn (fun q : ℝ × HI3 =>
      Metric.infDist q.2 (hamiltonIveyConvexMatrixRegionEuclid K q.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set HI3)) :=
  continuousOn_infDist_of_seqClosedGraph_of_approx (a := 0) (b := T)
    (C := fun τ => hamiltonIveyConvexMatrixRegionEuclid K τ)
    (hCne := fun _ hτ => nonempty_hamiltonIveyConvexMatrixRegionEuclid hK hτ.1)
    (hgraph := hamiltonIveyRegion_seqClosedGraph hK)
    (happrox := hamiltonIveyRegion_approx hK)

theorem continuousOn_infDist_hamiltonIveyRegion_comp_shift
    {M : Type*} [TopologicalSpace M]
    {t0 T K : ℝ} (hK : 0 < K)
    (A : ℝ → M → HI3)
    (hjoint : ContinuousOn
      (fun q : Real × M => A q.1 q.2)
      (Set.Icc t0 (t0 + T) ×ˢ (Set.univ : Set M))) :
    ContinuousOn
      (fun q : Real × M => Metric.infDist (A q.1 q.2)
        (hamiltonIveyConvexMatrixRegionEuclid K (q.1 - t0)))
      (Set.Icc t0 (t0 + T) ×ˢ (Set.univ : Set M)) := by
  have hg : ContinuousOn (fun q : ℝ × HI3 =>
      Metric.infDist q.2 (hamiltonIveyConvexMatrixRegionEuclid K q.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set HI3)) :=
    continuousOn_infDist_hamiltonIveyRegion hK
  have hh : ContinuousOn
      (fun q : ℝ × M => (q.1 - t0, A q.1 q.2))
      (Set.Icc t0 (t0 + T) ×ˢ (Set.univ : Set M)) := by
    have hfst : ContinuousOn (fun q : ℝ × M => q.1 - t0)
        (Set.Icc t0 (t0 + T) ×ˢ (Set.univ : Set M)) := by fun_prop
    exact hfst.prodMk hjoint
  have hmaps : Set.MapsTo
      (fun q : ℝ × M => (q.1 - t0, A q.1 q.2))
      (Set.Icc t0 (t0 + T) ×ˢ (Set.univ : Set M))
      (Set.Icc 0 T ×ˢ (Set.univ : Set HI3)) := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, trivial⟩
  refine (hg.comp hh hmaps).congr ?_
  intro q hq
  rfl

end DifferentialGeometry.Geometry.Curvature.DimensionThree

end
