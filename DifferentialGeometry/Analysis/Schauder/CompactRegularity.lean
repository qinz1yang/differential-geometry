import DifferentialGeometry.Analysis.Schauder.C2Composition
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section

open Set Metric
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

omit [NormedSpace Real V] [NormedSpace Real F] in
theorem exists_norm_bound_of_continuousOn_isCompact
    {s : Set V} (hs : IsCompact s) {f : V → F}
    (hf : ContinuousOn f s) :
    ∃ C : NNReal, ∀ x ∈ s, ‖f x‖ ≤ C := by
  rcases hs.exists_bound_of_continuousOn hf with ⟨C, hC⟩
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro x hx
  exact (hC x hx).trans (le_max_left _ _)

theorem exists_holderWith_restrict_of_contDiffOn_isCompact
    {s : Set V} (hs : IsCompact s) (hsconv : Convex Real s)
    {f : V → F} (hf : ContDiffOn Real 1 f s)
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ C : NNReal, HolderWith C alpha (s.restrict f) := by
  rcases hf.exists_lipschitzOnWith one_ne_zero hsconv hs with ⟨L, hL⟩
  let D : NNReal := (ediam s).toNNReal
  refine ⟨L * D ^ ((1 : Real) - (alpha : Real)), ?_⟩
  apply HolderOnWith.holderWith
  apply hL.holderOnWith.of_le (D := D) _ halpha
  intro x hx y hy
  rw [ENNReal.coe_toNNReal hs.isBounded.ediam_ne_top]
  exact edist_le_ediam_of_mem hx hy

theorem exists_norm_bound_and_holderWith_restrict_of_contDiffOn_isCompact
    {s : Set V} (hs : IsCompact s) (hsconv : Convex Real s)
    {f : V → F} (hf : ContDiffOn Real 1 f s)
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ C₀ Cα : NNReal,
      (∀ x ∈ s, ‖f x‖ ≤ C₀) ∧ HolderWith Cα alpha (s.restrict f) := by
  rcases exists_norm_bound_of_continuousOn_isCompact hs hf.continuousOn with ⟨C₀, hC₀⟩
  rcases exists_holderWith_restrict_of_contDiffOn_isCompact hs hsconv hf halpha with ⟨Cα, hCα⟩
  exact ⟨C₀, Cα, hC₀, hCα⟩

theorem isCompact_parabolicCylinder_Icc
    {X : Type*} [TopologicalSpace X]
    (a b : Real) {K : Set X} (hK : IsCompact K) :
    IsCompact (parabolicCylinder (Set.Icc a b) K) := by
  rw [show parabolicCylinder (Set.Icc a b) K =
      (Metric.Snowflaking.toSnowflaking '' Set.Icc a b) ×ˢ K by
    ext p
    rw [Metric.Snowflaking.image_toSnowflaking_eq_preimage]
    rfl]
  exact (isCompact_Icc.image Metric.Snowflaking.continuous_toSnowflaking).prod hK

theorem exists_holderWith_restrict_parabolicCylinder_Icc_of_contDiffOn
    (a b : Real) {K : Set V} (hK : IsCompact K) (hKconv : Convex Real K)
    {f : Real × V → F} (hf : ContDiffOn Real 1 f (Set.Icc a b ×ˢ K))
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ C : NNReal, HolderWith C alpha
      ((parabolicCylinder (Set.Icc a b) K).restrict
        (f ∘ parabolicToProduct)) := by
  rcases hf.exists_lipschitzOnWith one_ne_zero
      (convex_Icc a b |>.prod hKconv) (isCompact_Icc.prod hK) with ⟨L, hL⟩
  let Q := parabolicCylinder (Set.Icc a b) K
  have hmaps : MapsTo parabolicToProduct Q (Set.Icc a b ×ˢ K) := by
    intro p hp
    exact hp
  have hcomp : LipschitzOnWith
      (L * parabolicTimeSlabLipschitzConst a b)
      (f ∘ parabolicToProduct) Q :=
    hL.comp (lipschitzOnWith_parabolicToProduct_Icc a b K) hmaps
  have hQ : IsCompact Q := isCompact_parabolicCylinder_Icc a b hK
  let D : NNReal := (ediam Q).toNNReal
  refine ⟨(L * parabolicTimeSlabLipschitzConst a b) *
      D ^ ((1 : Real) - (alpha : Real)), ?_⟩
  apply HolderOnWith.holderWith
  apply hcomp.holderOnWith.of_le (D := D) _ halpha
  intro p hp q hq
  rw [ENNReal.coe_toNNReal hQ.isBounded.ediam_ne_top]
  exact edist_le_ediam_of_mem hp hq

theorem exists_norm_bound_and_holderWith_restrict_parabolicCylinder_Icc_of_contDiffOn
    (a b : Real) {K : Set V} (hK : IsCompact K) (hKconv : Convex Real K)
    {f : Real × V → F} (hf : ContDiffOn Real 1 f (Set.Icc a b ×ˢ K))
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ C₀ Cα : NNReal,
      (∀ p ∈ parabolicCylinder (Set.Icc a b) K,
        ‖f (parabolicToProduct p)‖ ≤ C₀) ∧
      HolderWith Cα alpha
        ((parabolicCylinder (Set.Icc a b) K).restrict
          (f ∘ parabolicToProduct)) := by
  rcases exists_norm_bound_of_continuousOn_isCompact
      (isCompact_Icc.prod hK) hf.continuousOn with ⟨C₀, hC₀⟩
  rcases exists_holderWith_restrict_parabolicCylinder_Icc_of_contDiffOn
      a b hK hKconv hf halpha with ⟨Cα, hCα⟩
  refine ⟨C₀, Cα, ?_, hCα⟩
  intro p hp
  exact hC₀ (parabolicToProduct p) hp

theorem exists_c2Pullback_schauder_bounds_on_compact_convex_of_contDiffOn
    {W : Type*} [NormedAddCommGroup W] [NormedSpace Real W]
    {s U : Set V} (hs : IsCompact s) (hsconv : Convex Real s)
    (hU : IsOpen U) (hsU : s ⊆ U)
    {phi : V → W} (hphi : ContDiffOn Real 3 phi U)
    {alpha : NNReal} (halpha : alpha ≤ 1) (J : Set Real) :
    ∃ L K1 K2 M1 M2 : NNReal,
      1 ≤ L ∧
      LipschitzOnWith L phi s ∧
      HolderWith K1 alpha
        ((parabolicCylinder J s).restrict
          (fun p => fderiv Real phi p.space)) ∧
      HolderWith K2 alpha
        ((parabolicCylinder J s).restrict
          (fun p => hessianCurryEquiv V W
            (iteratedFDeriv Real 2 phi p.space))) ∧
      (∀ p ∈ parabolicCylinder J s, ‖fderiv Real phi p.space‖ ≤ M1) ∧
      ∀ p ∈ parabolicCylinder J s,
        ‖hessianCurryEquiv V W
          (iteratedFDeriv Real 2 phi p.space)‖ ≤ M2 := by
  obtain ⟨L0, hL0⟩ :=
    (hphi.mono hsU).exists_lipschitzOnWith (by norm_num) hsconv hs
  let L : NNReal := max 1 L0
  have hL : 1 ≤ L := le_max_left _ _
  have hLip : LipschitzOnWith L phi s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact (hL0.dist_le_mul x hx y hy).trans
      (mul_le_mul_of_nonneg_right (by
        exact_mod_cast (le_max_right (1 : NNReal) L0)) dist_nonneg)
  have hD1 : ContDiffOn Real 1 (fderiv Real phi) U :=
    hphi.fderiv_of_isOpen hU (by norm_num)
  obtain ⟨M1, K1, hM1, hK1⟩ :=
    exists_norm_bound_and_holderWith_restrict_of_contDiffOn_isCompact
      hs hsconv (hD1.mono hsU) halpha
  have hD2 : ContDiffOn Real 1 (iteratedFDeriv Real 2 phi) U := by
    intro x hx
    exact ((hphi x hx).contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right
      (m := 1) (i := 2) (by norm_num) |>.contDiffWithinAt
  obtain ⟨M2, K2, hM2, hK2raw⟩ :=
    exists_norm_bound_and_holderWith_restrict_of_contDiffOn_isCompact
      hs hsconv (hD2.mono hsU) halpha
  have hK2 : HolderWith K2 alpha
      (s.restrict (fun x => hessianCurryEquiv V W
        (iteratedFDeriv Real 2 phi x))) := by
    have hcomp := (hessianCurryEquiv V W).lipschitz.holderWith.comp hK2raw
    simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul,
      Function.comp_apply, Set.restrict_apply] using hcomp
  refine ⟨L, K1, K2, M1, M2, hL, hLip, ?_, ?_, ?_, ?_⟩
  · exact holderWith_restrict_parabolic_const_time _ hK1 J
  · exact holderWith_restrict_parabolic_const_time _ hK2 J
  · intro p hp
    exact hM1 p.space hp.2
  · intro p hp
    rw [(hessianCurryEquiv V W).norm_map]
    exact hM2 p.space hp.2

theorem exists_c2Pullback_schauder_bounds_on_compact_convex
    {W : Type*} [NormedAddCommGroup W] [NormedSpace Real W]
    {s : Set V} (hs : IsCompact s) (hsconv : Convex Real s)
    {phi : V → W} (hphi : ContDiff Real 3 phi)
    {alpha : NNReal} (halpha : alpha ≤ 1) (J : Set Real) :
    ∃ L K1 K2 M1 M2 : NNReal,
      1 ≤ L ∧
      LipschitzOnWith L phi s ∧
      HolderWith K1 alpha
        ((parabolicCylinder J s).restrict
          (fun p => fderiv Real phi p.space)) ∧
      HolderWith K2 alpha
        ((parabolicCylinder J s).restrict
          (fun p => hessianCurryEquiv V W
            (iteratedFDeriv Real 2 phi p.space))) ∧
      (∀ p ∈ parabolicCylinder J s, ‖fderiv Real phi p.space‖ ≤ M1) ∧
      ∀ p ∈ parabolicCylinder J s,
        ‖hessianCurryEquiv V W
          (iteratedFDeriv Real 2 phi p.space)‖ ≤ M2 := by
  exact exists_c2Pullback_schauder_bounds_on_compact_convex_of_contDiffOn
    hs hsconv isOpen_univ (subset_univ s) hphi.contDiffOn halpha J

end DifferentialGeometry.Analysis.Schauder

end
