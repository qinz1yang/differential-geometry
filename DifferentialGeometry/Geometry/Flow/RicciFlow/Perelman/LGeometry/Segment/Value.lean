import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.ScalarLowerBound
import Mathlib.Order.Bounds.Lattice

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M] {D : RealTimeInterval}

private def lSegmentCosts
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ)
    (Ω : Set (M × ℝ)) (a b : ℝ) (x y : M) : Set ℝ :=
  {r | ∃ gamma : ℝ → M,
    isFiniteActionLCurve S T Ω a b gamma ∧
      gamma a = x ∧ gamma b = y ∧ lLength S T gamma a b = r}

private theorem lSegmentCosts_split
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ)
    (Ω : Set (M × ℝ)) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (x z : M) :
    lSegmentCosts S T Ω a c x z =
      ⋃ y : M,
        Set.image2 (fun u v : ℝ ↦ u + v)
          (lSegmentCosts S T Ω a b x y)
          (lSegmentCosts S T Ω b c y z) := by
  classical
  ext r
  constructor
  · rintro ⟨gamma, hgamma, hga, hgc, hr⟩
    have hleft : isFiniteActionLCurve S T Ω a b gamma :=
      hgamma.mono hab
        (fun _ hs ↦ ⟨hs.1, hs.2.trans hbc⟩)
    have hright : isFiniteActionLCurve S T Ω b c gamma :=
      hgamma.mono hbc
        (fun _ hs ↦ ⟨hab.trans hs.1, hs.2⟩)
    apply Set.mem_iUnion_of_mem (gamma b)
    refine ⟨lLength S T gamma a b, ?_,
      lLength S T gamma b c, ?_, ?_⟩
    · exact ⟨gamma, hleft, hga, rfl, rfl⟩
    · exact ⟨gamma, hright, rfl, hgc, rfl⟩
    · exact
        (lLength_add_adj S T gamma a b c
          hleft.2.2.1 hright.2.2.1).trans hr
  · intro hr
    rcases Set.mem_iUnion.mp hr with ⟨y, hy⟩
    rcases hy with ⟨u, hu, v, hv, huv⟩
    rcases hu with ⟨gamma, hgamma, hga, hgb, hu⟩
    rcases hv with ⟨eta, heta, heb, hec, hv⟩
    refine ⟨Set.piecewise (Set.Iic b) gamma eta,
      hgamma.piecewise_Iic heta hab hbc
        (hgb.trans heb.symm), ?_, ?_, ?_⟩
    · rw [Set.piecewise_eq_of_mem (Set.Iic b) gamma eta hab]
      exact hga
    · by_cases hcb : c ≤ b
      · have hcb' : c = b := le_antisymm hcb hbc
        subst c
        rw [Set.piecewise_eq_of_mem
          (Set.Iic b) gamma eta (Set.mem_Iic.mpr le_rfl)]
        exact (hgb.trans heb.symm).trans hec
      · rw [Set.piecewise_eq_of_notMem
          (Set.Iic b) gamma eta hcb]
        exact hec
    · calc
        lLength S T
            (Set.piecewise (Set.Iic b) gamma eta) a c =
            lLength S T gamma a b +
              lLength S T eta b c :=
          lLength_piecewise_Iic S T a b c gamma eta hab hbc
            hgamma.2.2.1 heta.2.2.1
        _ = u + v := congrArg₂ (· + ·) hu hv
        _ = r := huv

def lSegmentValue
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ)
    (Ω : Set (M × ℝ)) (a b : ℝ) (x y : M) : WithTop ℝ :=
  sInf ((fun r : ℝ ↦ (r : WithTop ℝ)) '' lSegmentCosts S T Ω a b x y)

theorem le_lSegmentValue
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ)
    (Ω : Set (M × ℝ)) (a b : ℝ) (x y : M)
    (A : WithTop ℝ)
    (hA : ∀ gamma : ℝ → M,
      isFiniteActionLCurve S T Ω a b gamma →
      gamma a = x → gamma b = y →
      A ≤ (lLength S T gamma a b : WithTop ℝ)) :
    A ≤ lSegmentValue S T Ω a b x y := by
  unfold lSegmentValue
  by_cases hne : (lSegmentCosts S T Ω a b x y).Nonempty
  · apply le_csInf (hne.image fun r : ℝ ↦ (r : WithTop ℝ))
    intro q hq
    rcases hq with ⟨r, hr, rfl⟩
    rcases hr with ⟨gamma, hgamma, hxa, hyb, rfl⟩
    exact hA gamma hgamma hxa hyb
  · have hempty : lSegmentCosts S T Ω a b x y = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, Set.image_empty, WithTop.sInf_empty]
    exact le_top

def isLSegmentMinimizer
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ)
    (Ω : Set (M × ℝ)) (a b : ℝ) (x y : M)
    (gamma : ℝ → M) : Prop :=
  isFiniteActionLCurve S T Ω a b gamma ∧
    gamma a = x ∧ gamma b = y ∧
      lSegmentValue S T Ω a b x y = (lLength S T gamma a b : WithTop ℝ)

private theorem bddBelow_lSegmentCosts
    (S : SolutionOn (I := I) (M := M) D) (T K : ℝ)
    (Ω : Set (M × ℝ)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1) (x y : M) :
    BddBelow (lSegmentCosts S T Ω a b x y) := by
  refine ⟨-(2 * K / 3) *
    (b * Real.sqrt b - a * Real.sqrt a), ?_⟩
  intro r hr
  rcases hr with ⟨gamma, hgamma, _, _, rfl⟩
  rcases hgamma with ⟨_, _, hInt, hΩ⟩
  exact lLength_ge_of_scalar_lower_bound S T a b K ha hab gamma
    (fun s hs ↦ hR (gamma s, T - s) (hΩ s hs)) hInt

private theorem lSegmentValue_add
    (S : SolutionOn (I := I) (M := M) D)
    (T K : ℝ) (Ω : Set (M × ℝ))
    {a b c : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1)
    (x y z : M) :
    lSegmentValue S T Ω a b x y +
        lSegmentValue S T Ω b c y z =
      sInf ((fun r : ℝ ↦ (r : WithTop ℝ)) ''
        Set.image2 (fun u v : ℝ ↦ u + v)
          (lSegmentCosts S T Ω a b x y)
          (lSegmentCosts S T Ω b c y z)) := by
  classical
  let A := lSegmentCosts S T Ω a b x y
  let B := lSegmentCosts S T Ω b c y z
  change
    sInf ((fun r : ℝ ↦ (r : WithTop ℝ)) '' A) +
        sInf ((fun r : ℝ ↦ (r : WithTop ℝ)) '' B) =
      sInf ((fun r : ℝ ↦ (r : WithTop ℝ)) ''
        Set.image2 (fun u v : ℝ ↦ u + v) A B)
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · have hb : 0 ≤ b := ha.trans hab
      have hAbdd : BddBelow A :=
        bddBelow_lSegmentCosts S T K Ω ha hab hR x y
      have hBbdd : BddBelow B :=
        bddBelow_lSegmentCosts S T K Ω hb hbc hR y z
      have hAB :
          (Set.image2 (fun u v : ℝ ↦ u + v) A B).Nonempty :=
        hA.image2 hB
      have hABbdd :
          BddBelow (Set.image2 (fun u v : ℝ ↦ u + v) A B) := by
        rcases hAbdd with ⟨p, hp⟩
        rcases hBbdd with ⟨q, hq⟩
        refine ⟨p + q, ?_⟩
        rintro w ⟨u, hu, v, hv, rfl⟩
        exact add_le_add (hp hu) (hq hv)
      have hInf :
          sInf (Set.image2 (fun u v : ℝ ↦ u + v) A B) =
            sInf A + sInf B :=
        csInf_image2_eq_csInf_csInf
          (u := fun p q : ℝ ↦ p + q)
          (l₁ := fun q p : ℝ ↦ p - q)
          (l₂ := fun p q : ℝ ↦ q - p)
          (fun _ _ _ ↦ sub_le_iff_le_add)
          (fun _ _ _ ↦ sub_le_iff_le_add')
          hA hAbdd hB hBbdd
      calc
        sInf ((fun r : ℝ ↦ (r : WithTop ℝ)) '' A) +
            sInf ((fun r : ℝ ↦ (r : WithTop ℝ)) '' B) =
            ((sInf A + sInf B : ℝ) : WithTop ℝ) := by
          simpa only [WithTop.coe_add] using
            congrArg₂ (· + ·)
              (WithTop.coe_sInf' hA hAbdd).symm
              (WithTop.coe_sInf' hB hBbdd).symm
        _ = ((sInf
            (Set.image2 (fun u v : ℝ ↦ u + v) A B) : ℝ) :
              WithTop ℝ) :=
          congrArg (fun q : ℝ ↦ (q : WithTop ℝ)) hInf.symm
        _ = sInf ((fun r : ℝ ↦ (r : WithTop ℝ)) ''
            Set.image2 (fun u v : ℝ ↦ u + v) A B) :=
          WithTop.coe_sInf' hAB hABbdd
    · have hBe : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
      rw [hBe, Set.image_empty, WithTop.sInf_empty,
        Set.image2_empty_right, Set.image_empty,
        WithTop.sInf_empty, WithTop.add_top]
  · have hAe : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    rw [hAe, Set.image_empty, WithTop.sInf_empty,
      Set.image2_empty_left, Set.image_empty,
      WithTop.sInf_empty, WithTop.top_add]

private theorem lSegmentValue_eq_coe_sInf
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ)
    (Ω : Set (M × ℝ)) (a b : ℝ) (x y : M)
    (hne : (lSegmentCosts S T Ω a b x y).Nonempty)
    (hbdd : BddBelow (lSegmentCosts S T Ω a b x y)) :
    lSegmentValue S T Ω a b x y =
      ((sInf (lSegmentCosts S T Ω a b x y) : ℝ) : WithTop ℝ) := by
  unfold lSegmentValue
  exact (WithTop.coe_sInf' hne hbdd).symm

theorem lSegmentValue_le_lLength
    (S : SolutionOn (I := I) (M := M) D) (T K : ℝ)
    (Ω : Set (M × ℝ)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1)
    (x y : M)
    (gamma : ℝ → M) (hgamma : isFiniteActionLCurve S T Ω a b gamma)
    (hxa : gamma a = x) (hyb : gamma b = y) :
    lSegmentValue S T Ω a b x y ≤
      (lLength S T gamma a b : WithTop ℝ) := by
  have hmem : lLength S T gamma a b ∈ lSegmentCosts S T Ω a b x y :=
    ⟨gamma, hgamma, hxa, hyb, rfl⟩
  have hbdd := bddBelow_lSegmentCosts S T K Ω ha hab hR x y
  rw [lSegmentValue_eq_coe_sInf S T Ω a b x y ⟨_, hmem⟩ hbdd]
  exact WithTop.coe_le_coe.2 (csInf_le hbdd hmem)

theorem lSegmentValue_le_lLength_of_scalar_lower_bound_on_time_interval
    (S : SolutionOn (I := I) (M := M) D) (T K : ℝ)
    (Ω : Set (M × ℝ)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ s ∈ Icc a b, ∀ z : M, -K ≤ S.scalar (T - s) z)
    (x y : M)
    (gamma : ℝ → M) (hgamma : isFiniteActionLCurve S T Ω a b gamma)
    (hxa : gamma a = x) (hyb : gamma b = y) :
    lSegmentValue S T Ω a b x y ≤
      (lLength S T gamma a b : WithTop ℝ) := by
  have hmem : lLength S T gamma a b ∈ lSegmentCosts S T Ω a b x y :=
    ⟨gamma, hgamma, hxa, hyb, rfl⟩
  have hbdd : BddBelow (lSegmentCosts S T Ω a b x y) := by
    refine ⟨-(2 * K / 3) *
      (b * Real.sqrt b - a * Real.sqrt a), ?_⟩
    intro r hr
    rcases hr with ⟨eta, heta, _, _, rfl⟩
    exact lLength_ge_of_scalar_lower_bound S T a b K ha hab eta
      (fun s hs ↦ hR s hs (eta s)) heta.2.2.1
  rw [lSegmentValue_eq_coe_sInf S T Ω a b x y ⟨_, hmem⟩ hbdd]
  exact WithTop.coe_le_coe.2 (csInf_le hbdd hmem)

theorem le_lSegmentValue_of_scalar_lower_bound
    (S : SolutionOn (I := I) (M := M) D) (T K : ℝ)
    (Ω : Set (M × ℝ)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1) (x y : M) :
    ((-(2 * K / 3) *
        (b * Real.sqrt b - a * Real.sqrt a) : ℝ) : WithTop ℝ) ≤
      lSegmentValue S T Ω a b x y := by
  apply le_lSegmentValue
  intro gamma hgamma _ _
  exact WithTop.coe_le_coe.2 (lLength_ge_of_scalar_lower_bound S T a b K ha hab gamma
    (fun s hs ↦ hR (gamma s, T - s) (hgamma.2.2.2 s hs)) hgamma.2.2.1)

theorem lSegmentValue_ne_top
    (S : SolutionOn (I := I) (M := M) D) (T K : ℝ)
    (Ω : Set (M × ℝ)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1)
    (x y : M)
    (gamma : ℝ → M) (hgamma : isFiniteActionLCurve S T Ω a b gamma)
    (hxa : gamma a = x) (hyb : gamma b = y) :
    lSegmentValue S T Ω a b x y ≠ ⊤ := by
  exact ne_top_of_le_ne_top WithTop.coe_ne_top
    (lSegmentValue_le_lLength S T K Ω ha hab hR x y gamma hgamma hxa hyb)

theorem lSegmentValue_le_of_subset
    (S : SolutionOn (I := I) (M := M) D)
    (T K : ℝ) {Ω Ω' : Set (M × ℝ)} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hΩ : Ω ⊆ Ω')
    (hR : ∀ q ∈ Ω', -K ≤ S.scalar q.2 q.1) (x y : M) :
    lSegmentValue S T Ω' a b x y ≤ lSegmentValue S T Ω a b x y := by
  apply le_lSegmentValue
  intro gamma hgamma hxa hyb
  exact lSegmentValue_le_lLength S T K Ω' ha hab hR x y gamma
    ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      fun s hs ↦ hΩ (hgamma.2.2.2 s hs)⟩ hxa hyb

theorem lSegmentValue_eq_sInf_of_covers_curves
    {ι : Sort*} (S : SolutionOn (I := I) (M := M) D)
    (T K : ℝ) (Ω : Set (M × ℝ))
    (Ωj : ι → Set (M × ℝ)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hsub : ∀ j, Ωj j ⊆ Ω)
    (hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1)
    (x y : M)
    (hgraph : ∀ gamma : ℝ → M,
      isFiniteActionLCurve S T Ω a b gamma →
      gamma a = x → gamma b = y →
      ∃ j, ∀ s ∈ Icc a b, (gamma s, T - s) ∈ Ωj j) :
    lSegmentValue S T Ω a b x y =
      sInf (Set.range fun j : ι ↦
        lSegmentValue S T (Ωj j) a b x y) := by
  let V : ι → WithTop ℝ := fun j ↦ lSegmentValue S T (Ωj j) a b x y
  have hle (j : ι) : lSegmentValue S T Ω a b x y ≤ V j :=
    lSegmentValue_le_of_subset S T K ha hab (hsub j) hR x y
  have hRangeBdd : BddBelow (Set.range V) := by
    refine ⟨lSegmentValue S T Ω a b x y, ?_⟩
    rintro q ⟨j, rfl⟩
    exact hle j
  have hglb := WithTop.isGLB_sInf' hRangeBdd
  change lSegmentValue S T Ω a b x y = sInf (Set.range V)
  apply le_antisymm
  · apply hglb.2
    rintro q ⟨j, rfl⟩
    exact hle j
  · apply le_lSegmentValue
    intro gamma hgamma hxa hyb
    obtain ⟨j, hgraphj⟩ := hgraph gamma hgamma hxa hyb
    exact (hglb.1 ⟨j, rfl⟩).trans
      (lSegmentValue_le_lLength S T K (Ωj j) ha hab
        (fun q hqj ↦ hR q (hsub j hqj)) x y gamma
        ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1, hgraphj⟩ hxa hyb)

theorem lSegmentValue_dynamic_programming
    (S : SolutionOn (I := I) (M := M) D)
    (T K : ℝ) (Ω : Set (M × ℝ))
    {a b c : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1)
    (x z : M) :
    lSegmentValue S T Ω a c x z =
      sInf (Set.range fun y : M ↦
        lSegmentValue S T Ω a b x y +
          lSegmentValue S T Ω b c y z) := by
  classical
  have hac : a ≤ c := hab.trans hbc
  let F : M → Set (WithTop ℝ) := fun y ↦
    (fun r : ℝ ↦ (r : WithTop ℝ)) ''
      Set.image2 (fun u v : ℝ ↦ u + v)
        (lSegmentCosts S T Ω a b x y)
        (lSegmentCosts S T Ω b c y z)
  let U : Set (WithTop ℝ) := ⋃ y : M, F y
  let V : M → WithTop ℝ := fun y ↦
    lSegmentValue S T Ω a b x y + lSegmentValue S T Ω b c y z
  have hUeq : U = (fun r : ℝ ↦ (r : WithTop ℝ)) ''
      lSegmentCosts S T Ω a c x z := by
    dsimp only [U, F]
    rw [← Set.image_iUnion, ← lSegmentCosts_split S T Ω hab hbc x z]
  have hUbdd : BddBelow U := by
    rw [hUeq]
    exact Monotone.map_bddBelow
      (fun _ _ h ↦ WithTop.coe_mono h)
      (bddBelow_lSegmentCosts S T K Ω ha hac hR x z)
  have hFbdd (y : M) : BddBelow (F y) :=
    hUbdd.mono (by
      intro q hq
      change q ∈ ⋃ y : M, F y
      exact Set.mem_iUnion_of_mem y hq)
  have hFglb (y : M) : IsGLB (F y) (sInf (F y)) :=
    WithTop.isGLB_sInf' (hFbdd y)
  have hRangeBdd : BddBelow (Set.range fun y : M ↦ sInf (F y)) := by
    rcases hUbdd with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    rintro q ⟨y, rfl⟩
    apply (hFglb y).2
    intro w hw
    exact hp (Set.mem_iUnion_of_mem y hw)
  have hOuter : sInf U = sInf (Set.range fun y : M ↦ sInf (F y)) :=
    (WithTop.isGLB_sInf' hUbdd).unique
      ((isGLB_iUnion_iff_of_isGLB hFglb _).mp (WithTop.isGLB_sInf' hRangeBdd))
  have hadd (y : M) : V y = sInf (F y) := by
    dsimp only [V, F]
    exact lSegmentValue_add S T K Ω ha hab hbc hR x y z
  have hfun : V = fun y : M ↦ sInf (F y) := funext hadd
  have hRange : Set.range V = Set.range (fun y : M ↦ sInf (F y)) :=
    congrArg Set.range hfun
  change sInf ((fun r : ℝ ↦ (r : WithTop ℝ)) ''
      lSegmentCosts S T Ω a c x z) = sInf (Set.range V)
  calc
    sInf ((fun r : ℝ ↦ (r : WithTop ℝ)) ''
        lSegmentCosts S T Ω a c x z) = sInf U := congrArg sInf hUeq.symm
    _ = sInf (Set.range fun y : M ↦ sInf (F y)) := hOuter
    _ = sInf (Set.range V) := congrArg sInf hRange.symm

theorem lSegmentValue_eq_and_confinement_of_action_gap
    (S : SolutionOn (I := I) (M := M) D)
    (T K : ℝ) (Ω₁ Ω₂ : Set (M × ℝ))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hΩ : Ω₁ ⊆ Ω₂)
    (hR : ∀ q ∈ Ω₂, -K ≤ S.scalar q.2 q.1)
    (x y : M) (η : ℝ) (hη : 0 ≤ η)
    (hgap : ∀ gamma : ℝ → M,
      isFiniteActionLCurve S T Ω₂ a b gamma →
      gamma a = x → gamma b = y →
      ¬ isFiniteActionLCurve S T Ω₁ a b gamma →
      lSegmentValue S T Ω₁ a b x y + (η : WithTop ℝ) ≤
        (lLength S T gamma a b : WithTop ℝ)) :
    lSegmentValue S T Ω₂ a b x y = lSegmentValue S T Ω₁ a b x y ∧
      ∀ (ε : ℝ), ε < η →
        ∀ gamma : ℝ → M,
          isFiniteActionLCurve S T Ω₂ a b gamma →
          gamma a = x → gamma b = y →
          (lLength S T gamma a b : WithTop ℝ) <
            lSegmentValue S T Ω₂ a b x y + (ε : WithTop ℝ) →
          isFiniteActionLCurve S T Ω₁ a b gamma := by
  classical
  have hR₁ : ∀ q ∈ Ω₁, -K ≤ S.scalar q.2 q.1 :=
    fun q hq ↦ hR q (hΩ hq)
  have hRestricted_le :
      lSegmentValue S T Ω₁ a b x y ≤ lSegmentValue S T Ω₂ a b x y := by
    apply le_lSegmentValue
    intro gamma hgamma hga hgb
    by_cases hin : isFiniteActionLCurve S T Ω₁ a b gamma
    · exact lSegmentValue_le_lLength S T K Ω₁ ha hab hR₁ x y gamma hin hga hgb
    · have hη0 : (0 : WithTop ℝ) ≤ (η : WithTop ℝ) := by
        exact_mod_cast hη
      calc
        lSegmentValue S T Ω₁ a b x y =
            lSegmentValue S T Ω₁ a b x y + 0 := (add_zero _).symm
        _ ≤ lSegmentValue S T Ω₁ a b x y + (η : WithTop ℝ) :=
          add_le_add_right hη0 _
        _ ≤ (lLength S T gamma a b : WithTop ℝ) :=
          hgap gamma hgamma hga hgb hin
  have hAmbient_le :
      lSegmentValue S T Ω₂ a b x y ≤ lSegmentValue S T Ω₁ a b x y :=
    lSegmentValue_le_of_subset S T K ha hab hΩ hR x y
  have hEq :
      lSegmentValue S T Ω₂ a b x y = lSegmentValue S T Ω₁ a b x y :=
    le_antisymm hAmbient_le hRestricted_le
  refine ⟨hEq, ?_⟩
  intro ε hε gamma hgamma hga hgb hmin
  by_contra hout
  have hfin : lSegmentValue S T Ω₁ a b x y ≠ ⊤ := by
    rw [← hEq]
    exact lSegmentValue_ne_top S T K Ω₂ ha hab hR x y gamma hgamma hga hgb
  obtain ⟨L, hL⟩ := WithTop.ne_top_iff_exists.mp hfin
  have houtGap := hgap gamma hgamma hga hgb hout
  rw [← hL] at houtGap
  have houtGap' :
      ((L + η : ℝ) : WithTop ℝ) ≤
        (lLength S T gamma a b : WithTop ℝ) := by
    simpa only [WithTop.coe_add] using houtGap
  have houtGapReal : L + η ≤ lLength S T gamma a b :=
    WithTop.coe_le_coe.mp houtGap'
  rw [hEq, ← hL] at hmin
  have hmin' :
      (lLength S T gamma a b : WithTop ℝ) <
        ((L + ε : ℝ) : WithTop ℝ) := by
    simpa only [WithTop.coe_add] using hmin
  have hminReal : lLength S T gamma a b < L + ε :=
    WithTop.coe_lt_coe.mp hmin'
  exact (not_lt_of_ge houtGapReal)
    (hminReal.trans (add_lt_add_right hε L))

end DifferentialGeometry.PDE.RicciFlow.Perelman
