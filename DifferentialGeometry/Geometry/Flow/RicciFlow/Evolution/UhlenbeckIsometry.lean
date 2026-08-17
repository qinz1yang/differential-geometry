import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Uhlenbeck
import DifferentialGeometry.Analysis.ODE.GlobalLipschitzAffineExistence
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set Filter
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Curvature
open scoped BigOperators Topology NNReal Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [FiniteDimensional Real E] [CompleteSpace E] in
theorem eq_of_hasDerivAt_zero_on_Ioo {f : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hf_cont : ContinuousOn f (Set.Icc 0 t))
    (hf' : ∀ s : ℝ, s ∈ Set.Ioo 0 t → HasDerivAt f 0 s) :
    f t = f 0 := by
  by_cases ht0 : t = 0
  · subst t
    rfl
  · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hmono : MonotoneOn f (Set.Icc 0 t) :=
      monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hf_cont
        (fun x hx => (hf' x (by simpa [interior_Icc] using hx)).differentiableAt.differentiableWithinAt)
        (fun x hx => by
          rw [(hf' x (by simpa [interior_Icc] using hx)).deriv])
    have hant : AntitoneOn f (Set.Icc 0 t) :=
      antitoneOn_of_deriv_nonpos (convex_Icc 0 t) hf_cont
        (fun x hx => (hf' x (by simpa [interior_Icc] using hx)).differentiableAt.differentiableWithinAt)
        (fun x hx => by
          rw [(hf' x (by simpa [interior_Icc] using hx)).deriv])
    have h01 : f 0 ≤ f t := hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    have h10 : f t ≤ f 0 := hant ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    exact le_antisymm h10 h01

omit [CompleteSpace E] in
theorem uhlenbeckFrameODE_solution
    {T : ℝ} (hT : 0 < T)
    {Idx : Type*} [Fintype Idx] [Nonempty Idx]
    (Rup : ℝ → Idx → Idx → ℝ)
    (hR_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ l k : Idx, |Rup t l k| ≤ C)
    (hR_cont : ∀ l k : Idx, ContinuousOn (fun t : ℝ => Rup t l k) (Set.Icc 0 T))
    (A₀ : Idx → Idx → ℝ) :
    ∃ iota : ℝ → Idx → Idx → ℝ,
      (∀ a k : Idx, iota 0 a k = A₀ a k) ∧
      ContinuousOn (fun t : ℝ => iota t) (Set.Icc 0 T) ∧
      ∀ t : ℝ, t ∈ Set.Ico 0 T → ∀ a k : Idx,
        HasDerivWithinAt (fun s : ℝ => iota s a k)
          (∑ l : Idx, Rup t l k * iota t a l) (Set.Ici 0) t := by
  classical
  let E₀ := Idx → Idx → ℝ
  rcases hR_bdd with ⟨C, hC, hRbd⟩
  let K : ℝ≥0 := ⟨C * Fintype.card Idx, mul_nonneg hC (Nat.cast_nonneg _)⟩
  let f : ℝ → E₀ → E₀ := fun t A a k => ∑ l : Idx, Rup t l k * A a l
  have hcard : (1 : ℝ) ≤ Fintype.card Idx := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty Idx›)
  have hf_lip : ∀ t : ℝ, t ∈ Set.Icc 0 T → LipschitzWith K (f t) := by
    intro t ht
    refine LipschitzWith.of_dist_le_mul fun A B => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hlin : f t A - f t B = f t (A - B) := by
      funext a k
      dsimp [f]
      rw [Pi.sub_apply, Pi.sub_apply]
      calc
        (∑ l : Idx, Rup t l k * A a l) - (∑ l : Idx, Rup t l k * B a l) =
            ∑ l : Idx, (Rup t l k * A a l - Rup t l k * B a l) :=
              (Finset.sum_sub_distrib (fun l : Idx => Rup t l k * A a l)
                (fun l : Idx => Rup t l k * B a l)).symm
        _ = ∑ l : Idx, Rup t l k * (A a l - B a l) := by
              refine Finset.sum_congr rfl ?_
              intro l hl
              ring
    rw [hlin]
    have hmain : ∀ a k : Idx, |∑ l : Idx, Rup t l k * (A - B) a l| ≤
        (K : ℝ≥0) * ‖A - B‖₊ := by
      intro a k
      have hsum : |∑ l : Idx, Rup t l k * (A - B) a l| ≤
          ∑ l : Idx, |Rup t l k| * |(A - B) a l| := by
        simpa using Finset.abs_sum_le_sum_abs
          (fun l : Idx => Rup t l k * (A - B) a l) Finset.univ
      have hterm : ∀ l : Idx, |Rup t l k| * |(A - B) a l| ≤ C * |(A - B) a l| := by
        intro l
        exact mul_le_mul_of_nonneg_right (hRbd t ht l k) (abs_nonneg _)
      have hsumC : ∑ l : Idx, |Rup t l k| * |(A - B) a l| ≤
          C * (∑ l : Idx, |(A - B) a l|) := by
        have h1 := Finset.sum_le_sum (s := Finset.univ) (fun l hl => hterm l)
        simpa [Finset.mul_sum] using h1
      have hentry : ∀ l : Idx, |(A - B) a l| ≤ (‖A - B‖₊ : ℝ) := by
        intro l
        have h2' : ‖(A - B) a l‖₊ ≤ ‖(A - B) a‖₊ := by
          rw [Pi.nnnorm_def ((A - B) a)]
          exact Finset.le_sup (s := (Finset.univ : Finset Idx))
            (f := fun b : Idx => ‖(A - B) a b‖₊) (Finset.mem_univ l)
        have h1' : ‖(A - B) a‖₊ ≤ ‖A - B‖₊ := by
          rw [Pi.nnnorm_def (A - B)]
          exact Finset.le_sup (s := (Finset.univ : Finset Idx))
            (f := fun b : Idx => ‖(A - B) b‖₊) (Finset.mem_univ a)
        exact_mod_cast (le_trans h2' h1')
      have hsumAbs : ∑ l : Idx, |(A - B) a l| ≤
          (Fintype.card Idx : ℝ) * (‖A - B‖₊ : ℝ) := by
        have h1 := Finset.sum_le_sum (s := Finset.univ) (fun l hl => hentry l)
        simpa [Finset.sum_const, nsmul_eq_mul] using h1
      exact le_trans hsum (by
        calc
          (∑ l : Idx, |Rup t l k| * |(A - B) a l|) ≤
              C * (∑ l : Idx, |(A - B) a l|) := hsumC
          _ ≤ C * ((Fintype.card Idx : ℝ) * (‖A - B‖₊ : ℝ)) :=
                mul_le_mul_of_nonneg_left hsumAbs hC
          _ = ((K : ℝ≥0) : ℝ) * (‖A - B‖₊ : ℝ) := by
                dsimp [K]
                ring)
    have hbound : ‖f t (A - B)‖ ≤ (K : ℝ) * ‖A - B‖ := by
      rw [Pi.norm_def]
      have hsup : (Finset.univ : Finset Idx).sup
          (fun a : Idx => ‖(f t (A - B)) a‖₊) ≤ (K : ℝ≥0) * ‖A - B‖₊ := by
        refine Finset.sup_le_iff.mpr ?_
        intro a ha
        rw [Pi.nnnorm_def]
        refine Finset.sup_le_iff.mpr ?_
        intro k hk
        dsimp [f]
        exact hmain a k
      exact_mod_cast hsup
    simpa [K] using hbound
  have hf_cont : ∀ A : E₀, ContinuousOn (fun t : ℝ => f t A) (Set.Icc 0 T) := by
    intro A
    rw [continuousOn_iff_continuous_restrict]
    have hRr : ∀ l k : Idx, Continuous (fun t : Set.Icc 0 T => Rup t.1 l k) :=
      fun l k => (hR_cont l k).restrict
    have hcontA : Continuous (fun t : Set.Icc 0 T => f t.1 A) := by
      rw [continuous_iff_continuousAt]
      intro t
      rw [continuousAt_pi]
      intro a
      rw [continuousAt_pi]
      intro k
      have hsum : ContinuousAt (fun t : Set.Icc 0 T =>
          ∑ l : Idx, Rup t.1 l k * A a l) t := by
        have hterm : ∀ l : Idx, Continuous (fun t : Set.Icc 0 T =>
            Rup t.1 l k * A a l) := by
          intro l
          exact (hRr l k).mul continuous_const
        exact (continuous_finset_sum (Finset.univ) (fun l hl => hterm l)).continuousAt
      simpa [f] using hsum
    simpa [Function.comp_def] using hcontA
  have hf_aff : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ A : E₀,
      ‖f t A‖ ≤ 0 + (K : ℝ) * ‖A‖ := by
    intro t ht A
    have hf0 : f t 0 = 0 := by
      funext a k
      change (∑ l : Idx, Rup t l k * (0 : Idx → Idx → ℝ) a l) =
        (0 : Idx → Idx → ℝ) a k
      simp
    have h := (hf_lip t ht).dist_le_mul A 0
    rw [dist_eq_norm, dist_eq_norm, hf0, sub_zero, sub_zero] at h
    linarith
  obtain ⟨γ, hγ0, hγcont, hγderiv⟩ :=
    forward_solution_of_lipschitzWith_affineBound (E := E₀) (f := f) hT
      (by norm_num : 0 ≤ (0 : ℝ)) hf_lip hf_cont hf_aff A₀
  let iota : ℝ → Idx → Idx → ℝ := fun t a k => γ t a k
  refine ⟨iota, ?_, ?_, ?_⟩
  · intro a k
    change γ 0 a k = A₀ a k
    rw [hγ0]
  · have hraw : ContinuousOn (fun t : ℝ => iota t) (Set.Icc 0 T) := hγcont
    exact hraw
  · intro t ht a k
    let L : E₀ →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (ι := Idx)
        (φ := fun _ : Idx => ℝ) (i := k)).comp
        (ContinuousLinearMap.proj (R := ℝ) (ι := Idx)
          (φ := fun _ : Idx => Idx → ℝ) (i := a))
    have hd := hγderiv t ht
    have hcomp : HasDerivWithinAt (fun s : ℝ => L (γ s))
        (L (f t (γ t))) (Set.Ici 0) t :=
      L.hasFDerivAt.comp_hasDerivWithinAt t hd
    have hLγ : ∀ s : ℝ, L (γ s) = γ s a k := by
      intro s
      dsimp [L]
      rfl
    have hLf : L (f t (γ t)) = ∑ l : Idx, Rup t l k * γ t a l := by
      dsimp [L, f]
      rfl
    simpa [iota, hLγ, hLf] using hcomp

omit [CompleteSpace E] [TopologicalSpace M] in
theorem movingFrameGram_valueConstant_of_ricciFlow
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {T : ℝ}
    {Idx : Type*} [Fintype Idx]
    (metricComp Ric frameComp Rup : MatrixComp M Idx)
    (hmetric : MetricCompRicciFlowInFrameOn (D := D) metricComp Ric)
    (hframe : FrameRicciODEInFrameOn (D := D) frameComp Rup)
    (hcompat : RicciEndomorphismCompatibleInFrame metricComp Ric Rup)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hgram_cont : ∀ x : M, ∀ a b : Idx,
      ContinuousOn (fun s : ℝ => movingFrameGramInFrame metricComp frameComp s x a b)
        (Set.Icc 0 T))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) (a b : Idx) :
    movingFrameGramInFrame metricComp frameComp t x a b =
      movingFrameGramInFrame metricComp frameComp 0 x a b := by
  let f : ℝ → ℝ := fun s => movingFrameGramInFrame metricComp frameComp s x a b
  have hzero : ∀ s : ℝ, s ∈ Set.Ioo 0 t → HasDerivAt f 0 s := by
    intro s hs
    have hsreg : s ∈ D.regular := hTreg ⟨hs.1, hs.2.le.trans ht.2⟩
    have hderiv := evolvingFrameGram_constant_of_ricciFlow (D := D)
      metricComp Ric frameComp Rup hmetric hframe hcompat
      ⟨s, hsreg⟩ x a b
    have hD : D.carrier ∈ 𝓝 s := D.regular_mem_nhds hsreg
    exact (hderiv.hasDerivAt hD).congr_deriv (by simp)
  have hcont : ContinuousOn f (Set.Icc 0 t) := by
    refine (hgram_cont x a b).mono ?_
    intro s hs
    exact ⟨hs.1, le_trans hs.2 ht.2⟩
  have hmain := eq_of_hasDerivAt_zero_on_Ioo ht.1 hcont hzero
  simpa [f] using hmain

section FlowFrame

variable {Idx : Type*} [Fintype Idx]

noncomputable def uhlenbeckRupOfSolution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real → DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx → (x : M) → TangentSpace I x) : MatrixComp M Idx :=
  fun t x i k => ricciOneUpCompInFrame (I := I) S gInv frame t x i k

omit [SigmaCompactSpace M] [T2Space M] in
theorem uhlenbeckRup_entry_continuousOn
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (gInv : Real → DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (hginv_cont : ∀ i j : Idx, ContinuousOn
      (fun q : ℝ × M => gInv q.1 q.2 i j) (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
    (hricci_cont : ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun t : ℝ => S.ricciAt t x (vec2 v w)) (Set.Icc 0 T))
    (frame : Idx → (x : M) → TangentSpace I x)
    {x : M} (i k : Idx) :
    ContinuousOn (fun t : ℝ => uhlenbeckRupOfSolution (I := I) S gInv frame t x i k)
      (Set.Icc 0 T) := by
  classical
  refine continuousOn_finset_sum Finset.univ ?_
  intro a ha
  have hginv : ContinuousOn (fun t : ℝ => gInv t x k a) (Set.Icc 0 T) := by
    have hmap : ContinuousOn (fun t : ℝ => (t, x)) (Set.Icc 0 T) := by
      fun_prop
    have hsub : Set.MapsTo (fun t : ℝ => (t, x)) (Set.Icc 0 T)
        (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
      intro t ht
      exact ⟨ht, trivial⟩
    have hc := (hginv_cont k a).comp hmap hsub
    simpa using hc
  have hricci : ContinuousOn (fun t : ℝ => ricciCompInFrame (I := I) S frame t x i a)
      (Set.Icc 0 T) := by
    simpa [ricciCompInFrame] using hricci_cont x (frame i x) (frame a x)
  simpa [uhlenbeckRupOfSolution, ricciOneUpCompInFrame, Finset.mul_sum] using hginv.mul hricci

omit [SigmaCompactSpace M] [T2Space M] in
theorem uhlenbeckIotaOfSolution
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    {Idx : Type*} [Fintype Idx] [Nonempty Idx]
    (gInv : Real → DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (hginv_cont : ∀ i j : Idx, ContinuousOn
      (fun q : ℝ × M => gInv q.1 q.2 i j) (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
    (hricci_cont : ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun t : ℝ => S.ricciAt t x (vec2 v w)) (Set.Icc 0 T))
    (frame : Idx → (x : M) → TangentSpace I x)
    (A₀ : Idx → Idx → ℝ) :
    ∃ iota : MatrixComp M Idx,
      (∀ x : M, ∀ a k : Idx, iota 0 x a k = A₀ a k) ∧
      (∀ x : M, ContinuousOn (fun t : ℝ => iota t x) (Set.Icc 0 T)) ∧
      ∀ t : ℝ, t ∈ Set.Ico 0 T → ∀ x : M, ∀ a k : Idx,
        HasDerivWithinAt (fun s : ℝ => iota s x a k)
          (∑ l : Idx, uhlenbeckRupOfSolution (I := I) S gInv frame t x l k * iota t x a l)
          (Set.Ici 0) t := by
  classical
  have hRup_cont : ∀ x : M, ∀ i k : Idx,
      ContinuousOn (fun t : ℝ => uhlenbeckRupOfSolution (I := I) S gInv frame t x i k)
        (Set.Icc 0 T) := by
    intro x i k
    exact uhlenbeckRup_entry_continuousOn (I := I) (M := M) hT S
      gInv hginv_cont hricci_cont frame i k
  have hEx : ∀ x : M, ∃ iota : ℝ → Idx → Idx → ℝ,
      (∀ a k : Idx, iota 0 a k = A₀ a k) ∧
      ContinuousOn iota (Set.Icc 0 T) ∧
      ∀ t : ℝ, t ∈ Set.Ico 0 T → ∀ a k : Idx,
        HasDerivWithinAt (fun s : ℝ => iota s a k)
          (∑ l : Idx, uhlenbeckRupOfSolution (I := I) S gInv frame t x l k * iota t a l)
          (Set.Ici 0) t := by
    intro x
    have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ l k : Idx,
        |uhlenbeckRupOfSolution (I := I) S gInv frame t x l k| ≤ C := by
      have hmax : ∀ (i k : Idx), ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Icc 0 T →
          |uhlenbeckRupOfSolution (I := I) S gInv frame t x i k| ≤ M := by
        intro i k
        have hc : ContinuousOn (fun t : ℝ =>
            |uhlenbeckRupOfSolution (I := I) S gInv frame t x i k|) (Set.Icc 0 T) :=
          (hRup_cont x i k).norm
        have hne : (Set.Icc (0 : ℝ) T).Nonempty := ⟨0, ⟨le_rfl, le_of_lt hT⟩⟩
        obtain ⟨q, hq, hmaxq⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMaxOn hne hc
        exact ⟨|uhlenbeckRupOfSolution (I := I) S gInv frame q x i k|,
          fun t ht => hmaxq ⟨ht.1, ht.2⟩⟩
      have hpos_choose : ∀ (i k : Idx), 0 ≤ (hmax i k).choose := by
        intro i k
        exact le_trans (abs_nonneg _) ((hmax i k).choose_spec 0 ⟨le_rfl, le_of_lt hT⟩)
      let C : ℝ := ∑ i : Idx, ∑ k : Idx, (hmax i k).choose
      refine ⟨C, ?_, ?_⟩
      · exact Finset.sum_nonneg (fun i hi =>
          Finset.sum_nonneg (fun k hk => hpos_choose i k))
      · intro t ht l k
        have hle : |uhlenbeckRupOfSolution (I := I) S gInv frame t x l k| ≤
            (hmax l k).choose := (hmax l k).choose_spec t ht
        calc
          |uhlenbeckRupOfSolution (I := I) S gInv frame t x l k| ≤
              (hmax l k).choose := hle
          _ ≤ C := by
                dsimp [C]
                have h1 : (hmax l k).choose ≤ ∑ k' : Idx, (hmax l k').choose := by
                  refine Finset.single_le_sum (fun i' hi' => hpos_choose l i')
                    (Finset.mem_univ k)
                have h2 : ∑ k' : Idx, (hmax l k').choose ≤ C := by
                  refine Finset.single_le_sum (fun i' hi' =>
                    Finset.sum_nonneg (fun k' hk' => hpos_choose i' k'))
                    (Finset.mem_univ l)
                exact le_trans h1 h2
    rcases uhlenbeckFrameODE_solution hT (uhlenbeckRupOfSolution (I := I) S gInv frame · x)
      hbdd (fun l k => hRup_cont x l k) A₀ with ⟨γ, hγ0, hγcont, hγderiv⟩
    exact ⟨γ, hγ0, hγcont, hγderiv⟩
  let iota : MatrixComp M Idx := fun t x a k => (Classical.choose (hEx x)) t a k
  refine ⟨iota, ?_, ?_, ?_⟩
  · intro x a k
    exact (Classical.choose_spec (hEx x)).1 a k
  · intro x
    exact (Classical.choose_spec (hEx x)).2.1
  · intro t ht x a k
    exact (Classical.choose_spec (hEx x)).2.2 t ht a k

end FlowFrame

end DifferentialGeometry.PDE.RicciFlow
