import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.Frame
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureEvolution
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Curvature.Algebraic.Tensor
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorLeastEigenvalue
import DifferentialGeometry.Analysis.ODE.Existence.GlobalLipschitzAffine
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set Filter
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped BigOperators Topology NNReal Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [FiniteDimensional Real E] [CompleteSpace E] in
private theorem eq_of_hasDerivAt_zero_on_Ioo {f : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
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
private theorem uhlenbeckFrameODE_solution
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
                rw [show (K : ℝ) = C * (Fintype.card Idx : ℝ) from rfl]
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
    exact hbound
  have hf_cont : ∀ A : E₀, ContinuousOn (fun t : ℝ => f t A) (Set.Icc 0 T) := by
    intro A
    rw [continuousOn_iff_continuous_domRestrict]
    have hRr : ∀ l k : Idx, Continuous (fun t : Set.Icc 0 T => Rup t.1 l k) :=
      fun l k => (hR_cont l k).domRestrict
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
        exact (continuous_finsetSum (Finset.univ) (fun l hl => hterm l)).continuousAt
      simpa [f] using hsum
    change Continuous (fun t : Set.Icc 0 T => f t.1 A)
    exact hcontA
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
theorem movingFrameGramInFrame_eq_initial_of_ricci_flow
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {T : ℝ}
    {Idx : Type*} [Fintype Idx]
    (metricComp Ric frameComp Rup : MatrixComp M Idx)
    (hmetric : MetricCompRicciFlowInFrameOn (D := D) metricComp Ric)
    (hframe : FrameRicciODEInFrameOn (D := D) frameComp Rup)
    (hcompat : RicciEndomorphismCompatibleInFrame metricComp Ric Rup)
    (hTreg : Set.Ioo 0 T ⊆ D.regular)
    (hgram_cont : ∀ x : M, ∀ a b : Idx,
      ContinuousOn (fun s : ℝ => movingFrameGramInFrame metricComp frameComp s x a b)
        (Set.Icc 0 T))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) (a b : Idx) :
    movingFrameGramInFrame metricComp frameComp t x a b =
      movingFrameGramInFrame metricComp frameComp 0 x a b := by
  let f : ℝ → ℝ := fun s => movingFrameGramInFrame metricComp frameComp s x a b
  have hzero : ∀ s : ℝ, s ∈ Set.Ioo 0 t → HasDerivAt f 0 s := by
    intro s hs
    have hsreg : s ∈ D.regular := hTreg ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
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
    (hginv_cont : ∀ x : M, ∀ i j : Idx, ContinuousOn
      (fun t : ℝ => gInv t x i j) (Set.Icc 0 T))
    (hricci_cont : ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun t : ℝ => S.ricciAt t x (vec2 v w)) (Set.Icc 0 T))
    (frame : Idx → (x : M) → TangentSpace I x)
    {x : M} (i k : Idx) :
    ContinuousOn (fun t : ℝ => uhlenbeckRupOfSolution (I := I) S gInv frame t x i k)
      (Set.Icc 0 T) := by
  classical
  refine continuousOn_finsetSum Finset.univ ?_
  intro a ha
  have hginv : ContinuousOn (fun t : ℝ => gInv t x k a) (Set.Icc 0 T) :=
    hginv_cont x k a
  have hricci : ContinuousOn (fun t : ℝ => ricciCompInFrame (I := I) S frame t x i a)
      (Set.Icc 0 T) := by
    simpa [ricciCompInFrame] using hricci_cont x (frame i x) (frame a x)
  change ContinuousOn
    (fun t : ℝ => gInv t x k a * ricciCompInFrame (I := I) S frame t x i a)
    (Set.Icc 0 T)
  exact hginv.mul hricci

omit [SigmaCompactSpace M] [T2Space M] in
theorem uhlenbeckIotaOfSolution
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    {Idx : Type*} [Fintype Idx] [Nonempty Idx]
    (gInv : Real → DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (hginv_cont : ∀ x : M, ∀ i j : Idx, ContinuousOn
      (fun t : ℝ => gInv t x i j) (Set.Icc 0 T))
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

omit [SigmaCompactSpace M] [T2Space M] in
theorem metricCompInFrame_symm
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {Idx : Type*}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    metricCompInFrame (I := I) S frame t x i j =
      metricCompInFrame (I := I) S frame t x j i := by
  simpa [metricCompInFrame] using (S.family.metric t).symm x (frame i x) (frame j x)

omit [SigmaCompactSpace M] in
theorem ricciCompInFrame_symm
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {Idx : Type*}
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    ricciCompInFrame (I := I) S frame t x i j =
      ricciCompInFrame (I := I) S frame t x j i := by
  unfold ricciCompInFrame
  change metricRicciAt (I := I) (S.family.metric t) x (vec2 (frame i x) (frame j x)) =
    metricRicciAt (I := I) (S.family.metric t) x (vec2 (frame j x) (frame i x))
  simpa [metricRicciAt_apply_eq_ricciTensor] using
    (metricRicciAt_apply_eq_ricciTensor (I := I) (M := M) (S.family.metric t) x
      (frame i x) (frame j x)).trans
      (ricciTensor_symm (I := I) (S.family.metric t) x (frame i x) (frame j x))

omit [SigmaCompactSpace M] [T2Space M] in
theorem uhlenbeckRup_mul_metricComp_eq_ricci
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real → DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hgInv : ∀ t x i j,
      ∑ k : Idx, gInv t x i k * metricCompInFrame (I := I) S frame t x k j =
        if i = j then 1 else 0)
    (hginv_symm : ∀ t x i j, gInv t x i j = gInv t x j i)
    (t : Real) (x : M) (l j : Idx) :
    (∑ k : Idx, uhlenbeckRupOfSolution (I := I) S gInv frame t x l k *
        metricCompInFrame (I := I) S frame t x k j) =
      ricciCompInFrame (I := I) S frame t x l j := by
  classical
  calc
    (∑ k : Idx, uhlenbeckRupOfSolution (I := I) S gInv frame t x l k *
        metricCompInFrame (I := I) S frame t x k j)
        = (∑ k : Idx, (∑ a : Idx, gInv t x k a * ricciCompInFrame (I := I) S frame t x l a) *
            metricCompInFrame (I := I) S frame t x k j) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          dsimp [uhlenbeckRupOfSolution, ricciOneUpCompInFrame]
    _ = (∑ k : Idx, ∑ a : Idx,
          gInv t x k a * ricciCompInFrame (I := I) S frame t x l a *
            metricCompInFrame (I := I) S frame t x k j) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
    _ = (∑ a : Idx, ∑ k : Idx,
          gInv t x k a * ricciCompInFrame (I := I) S frame t x l a *
            metricCompInFrame (I := I) S frame t x k j) := by
          rw [Finset.sum_comm]
    _ = (∑ a : Idx, ricciCompInFrame (I := I) S frame t x l a *
          (∑ k : Idx, gInv t x k a * metricCompInFrame (I := I) S frame t x k j)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
    _ = (∑ a : Idx, ricciCompInFrame (I := I) S frame t x l a * (if a = j then 1 else 0)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          have hinner : (∑ k : Idx, gInv t x k a * metricCompInFrame (I := I) S frame t x k j) =
              if a = j then 1 else 0 := by
            calc
              (∑ k : Idx, gInv t x k a * metricCompInFrame (I := I) S frame t x k j)
                  = (∑ k : Idx, gInv t x a k * metricCompInFrame (I := I) S frame t x k j) := by
                    refine Finset.sum_congr rfl fun k _ => ?_
                    rw [hginv_symm t x a k]
              _ = if a = j then 1 else 0 := hgInv t x a j
          rw [hinner]
    _ = ricciCompInFrame (I := I) S frame t x l j := by
          simp

omit [SigmaCompactSpace M] in
theorem ricciOneUpCompatible_of_inverseMetric
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [I.Boundaryless]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real → DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hgInv : ∀ t x i j,
      ∑ k : Idx, gInv t x i k * metricCompInFrame (I := I) S frame t x k j =
        if i = j then 1 else 0)
    (hginv_symm : ∀ t x i j, gInv t x i j = gInv t x j i) :
    RicciEndomorphismCompatibleInFrame
      (metricCompInFrame (I := I) S frame)
      (ricciCompInFrame (I := I) S frame)
      (uhlenbeckRupOfSolution (I := I) S gInv frame) := by
  classical
  intro t x v w
  constructor
  · calc
      (∑ l : Idx, ∑ k : Idx, ∑ j : Idx,
          v l * uhlenbeckRupOfSolution (I := I) S gInv frame t x l k * w j *
            metricCompInFrame (I := I) S frame t x k j)
          = (∑ l : Idx, ∑ j : Idx, ∑ k : Idx,
              v l * uhlenbeckRupOfSolution (I := I) S gInv frame t x l k * w j *
                metricCompInFrame (I := I) S frame t x k j) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.sum_comm]
      _ = (∑ l : Idx, ∑ j : Idx,
          v l * w j * ricciCompInFrame (I := I) S frame t x l j) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            calc
              (∑ k : Idx,
                  v l * uhlenbeckRupOfSolution (I := I) S gInv frame t x l k * w j *
                    metricCompInFrame (I := I) S frame t x k j)
                  = v l * w j *
                      (∑ k : Idx,
                        uhlenbeckRupOfSolution (I := I) S gInv frame t x l k *
                          metricCompInFrame (I := I) S frame t x k j) := by
                    calc
                      (∑ k : Idx,
                          v l * uhlenbeckRupOfSolution (I := I) S gInv frame t x l k * w j *
                            metricCompInFrame (I := I) S frame t x k j)
                          = (∑ k : Idx,
                              v l * w j *
                                (uhlenbeckRupOfSolution (I := I) S gInv frame t x l k *
                                  metricCompInFrame (I := I) S frame t x k j)) := by
                            refine Finset.sum_congr rfl fun k _ => ?_
                            ring
                      _ = v l * w j *
                          (∑ k : Idx,
                            uhlenbeckRupOfSolution (I := I) S gInv frame t x l k *
                              metricCompInFrame (I := I) S frame t x k j) := by
                            rw [← Finset.mul_sum]
              _ = v l * w j * ricciCompInFrame (I := I) S frame t x l j := by
                    rw [uhlenbeckRup_mul_metricComp_eq_ricci (I := I) (M := M) S gInv frame
                      hgInv hginv_symm t x l j]
      _ = (∑ i : Idx, ∑ j : Idx, v i * w j * ricciCompInFrame (I := I) S frame t x i j) := by
            rfl
  · calc
      (∑ i : Idx, ∑ l : Idx, ∑ k : Idx,
          v i * w l * uhlenbeckRupOfSolution (I := I) S gInv frame t x l k *
            metricCompInFrame (I := I) S frame t x i k)
          = (∑ i : Idx, ∑ l : Idx, ∑ k : Idx,
              v i * w l * uhlenbeckRupOfSolution (I := I) S gInv frame t x l k *
                metricCompInFrame (I := I) S frame t x k i) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro l hl
            apply Finset.sum_congr rfl
            intro k hk
            rw [metricCompInFrame_symm (I := I) (M := M) S frame t x i k]
      _ = (∑ i : Idx, ∑ l : Idx,
          v i * w l * ricciCompInFrame (I := I) S frame t x l i) := by
            have hinner : ∀ i l : Idx,
                (∑ k : Idx, uhlenbeckRupOfSolution (I := I) S gInv frame t x l k *
                    metricCompInFrame (I := I) S frame t x k i) =
                  ricciCompInFrame (I := I) S frame t x l i := by
              intro i l
              exact uhlenbeckRup_mul_metricComp_eq_ricci (I := I) (M := M) S gInv frame
                hgInv hginv_symm t x l i
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro l hl
            calc
              (∑ k : Idx,
                  v i * w l * uhlenbeckRupOfSolution (I := I) S gInv frame t x l k *
                    metricCompInFrame (I := I) S frame t x k i)
                  = v i * w l *
                      (∑ k : Idx,
                        uhlenbeckRupOfSolution (I := I) S gInv frame t x l k *
                          metricCompInFrame (I := I) S frame t x k i) := by
                    calc
                      (∑ k : Idx,
                          v i * w l * uhlenbeckRupOfSolution (I := I) S gInv frame t x l k *
                            metricCompInFrame (I := I) S frame t x k i)
                          = (∑ k : Idx,
                              v i * w l *
                                (uhlenbeckRupOfSolution (I := I) S gInv frame t x l k *
                                  metricCompInFrame (I := I) S frame t x k i)) := by
                            apply Finset.sum_congr rfl
                            intro k hk
                            ring
                      _ = v i * w l *
                          (∑ k : Idx,
                            uhlenbeckRupOfSolution (I := I) S gInv frame t x l k *
                              metricCompInFrame (I := I) S frame t x k i) := by
                            rw [← Finset.mul_sum]
              _ = v i * w l * ricciCompInFrame (I := I) S frame t x l i := by
                    rw [hinner i l]
      _ = (∑ i : Idx, ∑ j : Idx, v i * w j * ricciCompInFrame (I := I) S frame t x i j) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro l hl
            rw [ricciCompInFrame_symm (I := I) (M := M) S frame t x l i]

omit [SigmaCompactSpace M] in
theorem movingFrameGram_continuousOn_of_metricFamily
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    {Idx : Type*} [Fintype Idx]
    (frameComp : MatrixComp M Idx)
    (hframe_cont : ∀ x : M, ContinuousOn (fun t : ℝ => frameComp t x) (Set.Icc 0 T))
    (frame : Idx → (x : M) → TangentSpace I x)
    {x : M} (a b : Idx) :
    ContinuousOn (fun s : ℝ =>
      movingFrameGramInFrame (metricCompInFrame (I := I) S frame) frameComp s x a b)
      (Set.Icc 0 T) := by
  classical
  refine continuousOn_finsetSum Finset.univ ?_
  intro i hi
  refine continuousOn_finsetSum Finset.univ ?_
  intro j hj
  have hproj : ∀ p q : Idx, Continuous (fun F : Idx → Idx → ℝ => F p q) := by
    intro p q
    change Continuous (fun F : (j : Idx) → Idx → ℝ => (F p) q)
    have h1 : Continuous (fun F : (j : Idx) → Idx → ℝ => F p) :=
      continuous_apply (i := p)
    have h2 : Continuous (fun G : (j : Idx) → ℝ => G q) :=
      continuous_apply (i := q)
    exact h2.comp h1
  have hi_cont : ContinuousOn (fun s : ℝ => frameComp s x a i) (Set.Icc 0 T) :=
    (hproj a i).comp_continuousOn (hframe_cont x)
  have hj_cont : ContinuousOn (fun s : ℝ => frameComp s x b j) (Set.Icc 0 T) :=
    (hproj b j).comp_continuousOn (hframe_cont x)
  have hmetric_cont : ContinuousOn (fun s : ℝ =>
      metricCompInFrame (I := I) S frame s x i j) (Set.Icc 0 T) := by
    have hc := hS.smoothMetric.coeff_cont x (frame i x) (frame j x)
    have hsub : Set.Icc 0 T ⊆ (RealTimeInterval.closed 0 T hT.le).carrier := by
      intro s hs
      exact hs
    simpa [metricCompInFrame] using hc.mono hsub
  exact ((hi_cont.mul hj_cont).mul hmetric_cont).congr (fun s hs => by
    simp)

omit [SigmaCompactSpace M] in
theorem uhlenbeckIota_isometry
    {T : ℝ} (hT : 0 < T)
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
    (gInv : Real → DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (hginv_cont : ∀ x : M, ∀ i j : Idx, ContinuousOn
      (fun t : ℝ => gInv t x i j) (Set.Icc 0 T))
    (hricci_cont : ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun t : ℝ => S.ricciAt t x (vec2 v w)) (Set.Icc 0 T))
    (frame : Idx → (x : M) → TangentSpace I x)
    (hgInv : ∀ t x i j,
      ∑ k : Idx, gInv t x i k * metricCompInFrame (I := I) S frame t x k j =
        if i = j then 1 else 0)
    (hginv_symm : ∀ t x i j, gInv t x i j = gInv t x j i)
    (A₀ : Idx → Idx → ℝ) :
    ∃ iota : MatrixComp M Idx,
      (∀ x : M, ∀ a k : Idx, iota 0 x a k = A₀ a k) ∧
      FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le) iota
        (uhlenbeckRupOfSolution (I := I) S gInv frame) ∧
      ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Idx,
        movingFrameGramInFrame (metricCompInFrame (I := I) S frame) iota t x a b =
          movingFrameGramInFrame (metricCompInFrame (I := I) S frame) iota 0 x a b := by
  classical
  obtain ⟨iota, hiota0, hiota_cont, hiota_deriv⟩ :=
    uhlenbeckIotaOfSolution (I := I) (M := M) hT S gInv hginv_cont hricci_cont frame A₀
  have hframeODE : FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le) iota
      (uhlenbeckRupOfSolution (I := I) S gInv frame) := by
    intro t x a k
    exact (hiota_deriv (t : ℝ) ⟨le_of_lt t.2.1, t.2.2⟩ x a k).mono (by
      intro s hs
      exact hs.1)
  refine ⟨iota, hiota0, hframeODE, ?_⟩
  intro t ht x a b
  have hcompat := ricciOneUpCompatible_of_inverseMetric (I := I) (M := M) S gInv frame
    hgInv hginv_symm
  have hmetric : MetricCompRicciFlowInFrameOn (D := RealTimeInterval.closed 0 T hT.le)
      (metricCompInFrame (I := I) S frame) (ricciCompInFrame (I := I) S frame) := by
    intro τ x i j
    exact metricCompInFrame_timeDeriv (I := I) S hS frame τ x i j
  have hgram_cont : ∀ x : M, ∀ a b : Idx,
      ContinuousOn (fun s : ℝ =>
        movingFrameGramInFrame (metricCompInFrame (I := I) S frame) iota s x a b)
        (Set.Icc 0 T) := by
    intro x a b
    exact movingFrameGram_continuousOn_of_metricFamily (I := I) (M := M) hT S hS
      iota hiota_cont frame a b
  exact movingFrameGramInFrame_eq_initial_of_ricci_flow
    (D := RealTimeInterval.closed 0 T hT.le) (T := T)
    (metricCompInFrame (I := I) S frame) (ricciCompInFrame (I := I) S frame)
    iota (uhlenbeckRupOfSolution (I := I) S gInv frame)
    hmetric hframeODE hcompat (by
      intro s hs
      change s ∈ Set.Ioo 0 T
      exact hs)
    hgram_cont ht x a b

noncomputable def uhlenbeckEndomorphismAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx) (t : Real) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  basis.constrL (fun a : Idx => ∑ k : Idx, iota t x a k • basis k)

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma uhlenbeckEndomorphism_apply_basis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx) (t : Real) (a : Idx) :
    uhlenbeckEndomorphismAt basis iota t (basis a) =
      ∑ k : Idx, iota t x a k • basis k := by
  unfold uhlenbeckEndomorphismAt
  exact basis.constrL_basis (fun a : Idx => ∑ k : Idx, iota t x a k • basis k) a

omit [SigmaCompactSpace M] [T2Space M] in
lemma uhlenbeckEndomorphism_gram_pair
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {Idx : Type*} [Fintype Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx) (t : Real) (x : M) (a b : Idx) :
    (S.family.metric t).inner x
      (uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x a))
      (uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x b)) =
    movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b := by
  classical
  rw [uhlenbeckEndomorphism_apply_basis, uhlenbeckEndomorphism_apply_basis]
  unfold movingFrameGramInFrame
  calc
    (S.family.metric t).inner x
        (∑ k : Idx, iota t x a k • basisAt x k)
        (∑ l : Idx, iota t x b l • basisAt x l) =
      ∑ l : Idx, ∑ k : Idx,
        iota t x a k * (iota t x b l *
          (S.family.metric t).inner x (basisAt x k) (basisAt x l)) := by
        simp only [map_sum, map_smul, FunLike.coe_sum,
          FunLike.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Finset.mul_sum, mul_left_comm]
    _ = ∑ i : Idx, ∑ j : Idx,
        iota t x a i * (iota t x b j *
          (S.family.metric t).inner x (basisAt x i) (basisAt x j)) := by
        exact Finset.sum_comm (s := (Finset.univ : Finset Idx)) (t := (Finset.univ : Finset Idx))
          (f := fun l k : Idx => iota t x a k * (iota t x b l *
            (S.family.metric t).inner x (basisAt x k) (basisAt x l)))
    _ = ∑ i : Idx, ∑ j : Idx,
        iota t x a i * iota t x b j *
          metricCompInFrame (I := I) S (fun a x => basisAt x a) t x i j := by
        simp only [mul_assoc, metricCompInFrame_apply]

omit [SigmaCompactSpace M] [T2Space M] in
theorem uhlenbeckEndomorphism_isometry
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx)
    (hiota0 : ∀ x : M, ∀ a k : Idx, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Idx,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) (v w : TangentSpace I x) :
    (S.family.metric t).inner x
      (uhlenbeckEndomorphismAt (basisAt x) iota t v)
      (uhlenbeckEndomorphismAt (basisAt x) iota t w) =
    (S.family.metric 0).inner x v w := by
  classical
  have hU0 : ∀ a : Idx,
      uhlenbeckEndomorphismAt (basisAt x) iota 0 (basisAt x a) = basisAt x a := by
    intro a
    rw [uhlenbeckEndomorphism_apply_basis]
    simp [hiota0 x]
  let Bt : TangentSpace I x →ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ) :=
    { toFun := fun v =>
        { toFun := fun z => (S.family.metric t).inner x
            (uhlenbeckEndomorphismAt (basisAt x) iota t v)
            (uhlenbeckEndomorphismAt (basisAt x) iota t z)
          map_add' := by intro z w; simp
          map_smul' := by intro c z; simp }
      map_add' := by intro v w; ext z; simp
      map_smul' := by intro c v; ext z; simp }
  let B0 : TangentSpace I x →ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ) :=
    { toFun := fun v =>
        { toFun := fun z => (S.family.metric 0).inner x
            (uhlenbeckEndomorphismAt (basisAt x) iota 0 v)
            (uhlenbeckEndomorphismAt (basisAt x) iota 0 z)
          map_add' := by intro z w; simp
          map_smul' := by intro c z; simp }
      map_add' := by intro v w; ext z; simp
      map_smul' := by intro c v; ext z; simp }
  let J0 : TangentSpace I x →ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ) :=
    { toFun := fun v =>
        { toFun := fun z => (S.family.metric 0).inner x v z
          map_add' := by intro z w; simp
          map_smul' := by intro c z; simp }
      map_add' := by intro v w; ext z; simp
      map_smul' := by intro c v; ext z; simp }
  have hB : Bt = B0 := by
    apply (basisAt x).ext
    intro a
    apply (basisAt x).ext
    intro b
    change (S.family.metric t).inner x
        (uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x a))
        (uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x b)) =
      (S.family.metric 0).inner x
        (uhlenbeckEndomorphismAt (basisAt x) iota 0 (basisAt x a))
        (uhlenbeckEndomorphismAt (basisAt x) iota 0 (basisAt x b))
    rw [uhlenbeckEndomorphism_gram_pair]
    rw [hgram t ht x a b]
    rw [← uhlenbeckEndomorphism_gram_pair (S := S) (basisAt := basisAt) (iota := iota)
      (t := 0) (x := x) (a := a) (b := b)]
  have hB0 : B0 = J0 := by
    apply (basisAt x).ext
    intro a
    apply (basisAt x).ext
    intro b
    change (S.family.metric 0).inner x
        (uhlenbeckEndomorphismAt (basisAt x) iota 0 (basisAt x a))
        (uhlenbeckEndomorphismAt (basisAt x) iota 0 (basisAt x b)) =
      (S.family.metric 0).inner x (basisAt x a) (basisAt x b)
    rw [hU0 a, hU0 b]
  change Bt v w = (S.family.metric 0).inner x v w
  rw [hB, hB0]
  rfl

private lemma continuousMultilinearMap_update_sum
    {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => V) ℝ)
    (m : Fin 4 → V) (i : Fin 4) (c : ι → ℝ) (v : ι → V) :
    f (Function.update m i (∑ p : ι, c p • v p)) =
      ∑ p : ι, c p • f (Function.update m i (v p)) := by
  classical
  let L : V →ₗ[ℝ] ℝ :=
    { toFun := fun x => f (Function.update m i x)
      map_add' := by intro x y; simp
      map_smul' := by intro r x; simp }
  calc
    f (Function.update m i (∑ p : ι, c p • v p)) = L (∑ p : ι, c p • v p) := rfl
    _ = ∑ p : ι, L (c p • v p) := by rw [map_sum]
    _ = ∑ p : ι, c p • f (Function.update m i (v p)) := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      simp [L]

noncomputable def uhlenbeckPulledRm04At
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {Idx : Type*} [Fintype Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx) (t : ℝ) (x : M) :
    Tensor04At (I := I) (M := M) x :=
  (S.base.rm04 t x).compContinuousLinearMap
    (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t)

omit [SigmaCompactSpace M] in
theorem uhlenbeckPulledRm04At_apply
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {Idx : Type*} [Fintype Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx) (t : ℝ) (x : M) (X Y Z W : TangentSpace I x) :
    tensor04StdAt (uhlenbeckPulledRm04At S basisAt iota t x) X Y Z W =
      tensor04StdAt (S.base.rm04 t x)
        (uhlenbeckEndomorphismAt (basisAt x) iota t X)
        (uhlenbeckEndomorphismAt (basisAt x) iota t Y)
        (uhlenbeckEndomorphismAt (basisAt x) iota t Z)
        (uhlenbeckEndomorphismAt (basisAt x) iota t W) := by
  change (S.base.rm04 t x :
      ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
      (fun i : Fin 4 =>
        uhlenbeckEndomorphismAt (basisAt x) iota t (vec4 X Y Z W i)) =
    (S.base.rm04 t x) (vec4 (uhlenbeckEndomorphismAt (basisAt x) iota t X)
      (uhlenbeckEndomorphismAt (basisAt x) iota t Y)
      (uhlenbeckEndomorphismAt (basisAt x) iota t Z)
      (uhlenbeckEndomorphismAt (basisAt x) iota t W))
  congr 1
  funext i
  fin_cases i <;> simp [vec4]

omit [SigmaCompactSpace M] in
theorem uhlenbeckPulledRm04At_mem_algebraicCurvatureTensorSubmodule
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {Idx : Type*} [Fintype Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx) (t : ℝ) (x : M) :
    uhlenbeckPulledRm04At S basisAt iota t x ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  rw [mem_algebraicCurvatureTensorSubmodule]
  let Rm : Tensor04At (I := I) (M := M) x := S.base.rm04 t x
  have hform : IsAlgCurvForm (tensor04StdAt (I := I) (M := M) Rm) :=
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) x)
  change IsAlgCurvForm (fun X Y Z W =>
    tensor04StdAt (uhlenbeckPulledRm04At S basisAt iota t x) X Y Z W)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x₁ x₂ y z w
    rw [uhlenbeckPulledRm04At_apply, uhlenbeckPulledRm04At_apply,
      uhlenbeckPulledRm04At_apply]
    rw [show uhlenbeckEndomorphismAt (basisAt x) iota t (x₁ + x₂) =
        uhlenbeckEndomorphismAt (basisAt x) iota t x₁ +
          uhlenbeckEndomorphismAt (basisAt x) iota t x₂ from by simp]
    exact hform.add_left _ _ _ _ _
  · intro a u y z w
    rw [uhlenbeckPulledRm04At_apply, uhlenbeckPulledRm04At_apply]
    rw [show uhlenbeckEndomorphismAt (basisAt x) iota t (a • u) =
        a • uhlenbeckEndomorphismAt (basisAt x) iota t u from by simp]
    exact hform.smul_left _ _ _ _ _
  · intro u v y z
    rw [uhlenbeckPulledRm04At_apply, uhlenbeckPulledRm04At_apply]
    exact hform.anti_first _ _ _ _
  · intro u v y z
    rw [uhlenbeckPulledRm04At_apply, uhlenbeckPulledRm04At_apply]
    exact hform.anti_last _ _ _ _
  · intro u v y z
    rw [uhlenbeckPulledRm04At_apply, uhlenbeckPulledRm04At_apply,
      uhlenbeckPulledRm04At_apply]
    exact hform.bianchi _ _ _ _

omit [SigmaCompactSpace M] in
theorem uhlenbeckPulledRm04At_apply_basis
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {Idx : Type*} [Fintype Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx) (t : ℝ) (x : M) (a b c d : Idx) :
    tensor04StdAt (uhlenbeckPulledRm04At S basisAt iota t x) (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) =
      uhlenbeckPullbackRmInFrame iota
        (fun s x a b c d => tensor04StdAt (S.base.rm04 s x) (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d))
        t x a b c d := by
  classical
  change (S.base.rm04 t x :
      ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
      (fun i : Fin 4 =>
        uhlenbeckEndomorphismAt (basisAt x) iota t
          (vec4 (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) i)) =
    uhlenbeckPullbackRmInFrame iota
      (fun s x a b c d => tensor04StdAt (S.base.rm04 s x) (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d))
      t x a b c d
  simp only [uhlenbeckPullbackRmInFrame, tensor04StdAt_apply]
  let g : Fin 4 → TangentSpace I x := fun _ => 0
  have harg : (fun i : Fin 4 =>
      uhlenbeckEndomorphismAt (basisAt x) iota t
        (vec4 (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) i)) =
      Function.update (Function.update (Function.update (Function.update g 3
        (∑ l : Idx, iota t x d l • basisAt x l)) 2 (∑ k : Idx, iota t x c k • basisAt x k))
        1 (∑ j : Idx, iota t x b j • basisAt x j)) 0 (∑ i : Idx, iota t x a i • basisAt x i) := by
    funext i
    fin_cases i <;> simp [g, vec4, uhlenbeckEndomorphism_apply_basis]
  rw [harg]
  let m0 : Fin 4 → TangentSpace I x :=
    Function.update (Function.update (Function.update g 3
      (∑ l : Idx, iota t x d l • basisAt x l)) 2 (∑ k : Idx, iota t x c k • basisAt x k))
      1 (∑ j : Idx, iota t x b j • basisAt x j)
  have h0 : (S.base.rm04 t x) (Function.update m0 0 (∑ p : Idx, iota t x a p • basisAt x p)) =
      ∑ p : Idx, iota t x a p • (S.base.rm04 t x) (Function.update m0 0 (basisAt x p)) := by
    exact continuousMultilinearMap_update_sum (f := (S.base.rm04 t x)) (m := m0)
      (i := (0 : Fin 4)) (c := fun p : Idx => iota t x a p) (v := fun p : Idx => basisAt x p)
  rw [h0]
  have h1 : ∀ p : Idx,
      (S.base.rm04 t x) (Function.update m0 0 (basisAt x p)) =
      ∑ j : Idx, iota t x b j • (S.base.rm04 t x)
        (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x j)) := by
    intro p
    calc
      (S.base.rm04 t x) (Function.update m0 0 (basisAt x p))
          = (S.base.rm04 t x) (Function.update (Function.update m0 0 (basisAt x p)) 1
              ((Function.update m0 0 (basisAt x p)) (1 : Fin 4))) := by
            rw [Function.update_eq_self (a := (1 : Fin 4))
              (f := Function.update m0 0 (basisAt x p))]
      _ = ∑ j : Idx, iota t x b j • (S.base.rm04 t x)
            (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x j)) := by
            rw [show (Function.update m0 0 (basisAt x p)) (1 : Fin 4) =
                ∑ j : Idx, iota t x b j • basisAt x j from rfl]
            exact continuousMultilinearMap_update_sum (f := (S.base.rm04 t x))
              (m := Function.update m0 0 (basisAt x p)) (i := (1 : Fin 4))
              (c := fun j : Idx => iota t x b j) (v := fun j : Idx => basisAt x j)
  have h2 : ∀ p q : Idx,
      (S.base.rm04 t x) (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) =
      ∑ k : Idx, iota t x c k • (S.base.rm04 t x)
        (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) 2
          (basisAt x k)) := by
    intro p q
    calc
      (S.base.rm04 t x) (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q))
          = (S.base.rm04 t x) (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
              (basisAt x q)) 2 ((Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q))
                (2 : Fin 4))) := by
            rw [Function.update_eq_self (a := (2 : Fin 4))
              (f := Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q))]
      _ = ∑ k : Idx, iota t x c k • (S.base.rm04 t x)
            (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) 2
              (basisAt x k)) := by
            rw [show (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) (2 : Fin 4) =
                ∑ k : Idx, iota t x c k • basisAt x k from rfl]
            exact continuousMultilinearMap_update_sum (f := (S.base.rm04 t x))
              (m := Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q))
              (i := (2 : Fin 4)) (c := fun k : Idx => iota t x c k) (v := fun k : Idx => basisAt x k)
  have h3 : ∀ p q r : Idx,
      (S.base.rm04 t x) (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
        (basisAt x q)) 2 (basisAt x r)) =
      ∑ l : Idx, iota t x d l • (S.base.rm04 t x)
        (Function.update (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
          (basisAt x q)) 2 (basisAt x r)) 3 (basisAt x l)) := by
    intro p q r
    calc
      (S.base.rm04 t x) (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
          (basisAt x q)) 2 (basisAt x r))
          = (S.base.rm04 t x) (Function.update (Function.update (Function.update (Function.update m0 0
              (basisAt x p)) 1 (basisAt x q)) 2 (basisAt x r)) 3
              ((Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) 2
                (basisAt x r)) (3 : Fin 4))) := by
            rw [Function.update_eq_self (a := (3 : Fin 4))
              (f := Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
                (basisAt x q)) 2 (basisAt x r))]
      _ = ∑ l : Idx, iota t x d l • (S.base.rm04 t x)
            (Function.update (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
              (basisAt x q)) 2 (basisAt x r)) 3 (basisAt x l)) := by
            rw [show (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
                (basisAt x q)) 2 (basisAt x r)) (3 : Fin 4) =
                ∑ l : Idx, iota t x d l • basisAt x l from rfl]
            exact continuousMultilinearMap_update_sum (f := (S.base.rm04 t x))
              (m := Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
                (basisAt x q)) 2 (basisAt x r)) (i := (3 : Fin 4))
              (c := fun l : Idx => iota t x d l) (v := fun l : Idx => basisAt x l)
  have hbase : ∀ p q r l : Idx,
      (S.base.rm04 t x) (Function.update (Function.update (Function.update (Function.update m0 0
        (basisAt x p)) 1 (basisAt x q)) 2 (basisAt x r)) 3 (basisAt x l)) =
      (S.base.rm04 t x) (vec4 (basisAt x p) (basisAt x q) (basisAt x r) (basisAt x l)) := by
    intro p q r l
    congr 1
    funext n
    fin_cases n <;> simp [m0, vec4]
  calc
    ∑ p : Idx, iota t x a p • (S.base.rm04 t x) (Function.update m0 0 (basisAt x p))
        = ∑ p : Idx, iota t x a p • (∑ j : Idx, iota t x b j •
            (S.base.rm04 t x) (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x j))) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [h1 p]
    _ = ∑ p : Idx, iota t x a p • (∑ j : Idx, iota t x b j • (∑ k : Idx, iota t x c k •
            (S.base.rm04 t x) (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
              (basisAt x j)) 2 (basisAt x k)))) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [h2 p j]
    _ = ∑ p : Idx, iota t x a p • (∑ j : Idx, iota t x b j • (∑ k : Idx, iota t x c k • (∑ l : Idx,
            iota t x d l • (S.base.rm04 t x) (Function.update (Function.update (Function.update
              (Function.update m0 0 (basisAt x p)) 1 (basisAt x j)) 2 (basisAt x k)) 3 (basisAt x l))))) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro j hj
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [h3 p j k]
    _ = ∑ p : Idx, iota t x a p • (∑ j : Idx, iota t x b j • (∑ k : Idx, iota t x c k • (∑ l : Idx,
            iota t x d l • (S.base.rm04 t x) (vec4 (basisAt x p) (basisAt x j) (basisAt x k) (basisAt x l))))) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro j hj
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro k hk
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro l hl
          rw [hbase p j k l]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        iota t x a i * iota t x b j * iota t x c k * iota t x d l *
          (S.base.rm04 t x) (vec4 (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l)) := by
          simp [smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

omit [SigmaCompactSpace M] [T2Space M] in
theorem uhlenbeckEndomorphism_invertible
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx)
    (hiota0 : ∀ x : M, ∀ a k : Idx, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Idx,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) :
    Function.Bijective (uhlenbeckEndomorphismAt (basisAt x) iota t) := by
  have hinj : Function.Injective (uhlenbeckEndomorphismAt (basisAt x) iota t) := by
    intro v w hvw
    by_contra hne
    have hpos : 0 < (S.family.metric 0).inner x (v - w) (v - w) :=
      (S.family.metric 0).pos x (v - w) (sub_ne_zero.mpr hne)
    have hiso := uhlenbeckEndomorphism_isometry (I := I) (M := M) hT S basisAt iota hiota0 hgram ht x (v - w) (v - w)
    have hU : uhlenbeckEndomorphismAt (basisAt x) iota t (v - w) = 0 := by
      simp [hvw]
    have hz : (S.family.metric t).inner x 0 0 = 0 := by simp
    have hvv : (S.family.metric 0).inner x (v - w) (v - w) = 0 := by
      rw [← hiso]
      simp [hU]
    linarith
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := ℝ) (V := TangentSpace I x) (V₂ := TangentSpace I x) rfl
      (f := (uhlenbeckEndomorphismAt (basisAt x) iota t).toLinearMap)).mp hinj⟩

noncomputable def uhlenbeckMovingBasis
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx)
    (hiota0 : ∀ x : M, ∀ a k : Idx, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Idx,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) (x : M) :
    Module.Basis Idx Real (TangentSpace I x) :=
  (basisAt x).map (LinearMap.linearEquivOfInjective
    (uhlenbeckEndomorphismAt (basisAt x) iota t).toLinearMap
    (uhlenbeckEndomorphism_invertible hT S basisAt iota hiota0 hgram ht x).1 rfl)

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma uhlenbeckMovingBasis_apply
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx)
    (hiota0 : ∀ x : M, ∀ a k : Idx, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Idx,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) (x : M) (a : Idx) :
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x a =
      uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x a) := by
  unfold uhlenbeckMovingBasis
  simp

omit [SigmaCompactSpace M] [T2Space M] in
theorem uhlenbeckMovingBasis_orthonormalBasisAt
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (x : M) (horth0 : OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    OrthonormalBasisAt (I := I) (S.base.metric t) x
      (uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x) := by
  intro i j
  rw [uhlenbeckMovingBasis_apply, uhlenbeckMovingBasis_apply]
  exact (uhlenbeckEndomorphism_isometry (I := I) (M := M) hT S basisAt iota hiota0 hgram ht x
    (basisAt x i) (basisAt x j)).trans (horth0 i j)

omit [SigmaCompactSpace M] in
theorem curvatureOperatorMatrixAt_pulledTensor_eq_original_moving
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) :
    curvatureOperatorMatrixAt x (basisAt x)
        ⟨uhlenbeckPulledRm04At S basisAt iota t x,
          uhlenbeckPulledRm04At_mem_algebraicCurvatureTensorSubmodule S basisAt iota t x⟩ =
      curvatureOperatorMatrixAt x (uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x)
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) x⟩ := by
  ext i j
  unfold curvatureOperatorMatrixAt
  rw [uhlenbeckPulledRm04At_apply]
  simp [uhlenbeckMovingBasis_apply]

end FlowFrame

end DifferentialGeometry.PDE.RicciFlow
