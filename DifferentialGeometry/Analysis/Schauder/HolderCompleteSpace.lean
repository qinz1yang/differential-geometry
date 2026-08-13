import DifferentialGeometry.Analysis.Schauder.HolderNormedSpace
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Topology.Instances.NNReal.Lemmas

noncomputable section

open Set
open scoped BigOperators NNReal Topology

namespace DifferentialGeometry.Analysis.Schauder

section Holder

variable {X G : Type*} [MetricSpace X]
  [NormedAddCommGroup G]

theorem holderWith_tsum {alpha : NNReal} {C : Nat → NNReal}
    {f : Nat → X → G} (hC : Summable C)
    (hf : ∀ n, HolderWith (C n) alpha (f n))
    (hpoint : ∀ x, Summable fun n ↦ f n x) :
    HolderWith (∑' n, C n) alpha (fun x ↦ ∑' n, f n x) := by
  have hfinset : ∀ s : Finset Nat,
      HolderWith (∑ n ∈ s, C n) alpha
        (fun x ↦ ∑ n ∈ s, f n x) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (HolderWith.zero : HolderWith 0 alpha (0 : X → G))
    | @insert n s hn ih =>
        simpa only [Finset.sum_insert hn, Pi.add_apply] using
          (hf n).add ih
  have hpartial : ∀ N,
      HolderWith (∑' n, C n) alpha
        (fun x ↦ ∑ n ∈ Finset.range N, f n x) := by
    intro N
    exact (hfinset (Finset.range N)).mono
      (hC.sum_le_tsum (Finset.range N) fun _ _ ↦ zero_le _)
  intro x y
  exact le_of_tendsto
    ((hpoint x).hasSum.tendsto_sum_nat.edist
      (hpoint y).hasSum.tendsto_sum_nat)
    (Filter.Eventually.of_forall fun N ↦ hpartial N x y)

end Holder

section BoundedHolder

variable {X F : Type*} [MetricSpace X]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

private theorem exists_boundedHolderSpace_pointwise_tsum
    {alpha : NNReal}
    (f : Nat → BoundedHolderSpace (X := X) (F := F) alpha)
    (hf : Summable fun n ↦ ‖f n‖) :
    ∃ g : BoundedHolderSpace (X := X) (F := F) alpha,
      (∀ x, g x = ∑' n, f n x) ∧
      ‖g‖ ≤ (((2 : NNReal) * ∑' n, ‖f n‖₊ : NNReal) : Real) := by
  let g : X → F := fun x ↦ ∑' n, f n x
  have hfNN : Summable fun n ↦ ‖f n‖₊ := by
    rw [← NNReal.summable_coe]
    simpa only [coe_nnnorm] using hf
  let S : NNReal := ∑' n, ‖f n‖₊
  have hpointNorm : ∀ x, Summable fun n ↦ ‖f n x‖ := by
    intro x
    exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ norm_boundedHolderSpace_apply_le (f n) x) hf
  have hpoint : ∀ x, Summable fun n ↦ f n x := by
    intro x
    exact Summable.of_norm (hpointNorm x)
  have hholder : HolderWith S alpha g := by
    exact holderWith_tsum hfNN
      (fun n ↦ boundedHolderSpace_holderWith (f n)) hpoint
  have hsup : eSupNormOn Set.univ g ≤ S := by
    rw [eSupNormOn_le]
    intro x _hx
    have hx : ‖g x‖ ≤ (S : Real) := by
      calc
        ‖g x‖ ≤ ∑' n, ‖f n x‖ :=
          norm_tsum_le_tsum_norm (hpointNorm x)
        _ ≤ ∑' n, ‖f n‖ :=
          (hpointNorm x).tsum_le_tsum
            (fun n ↦ norm_boundedHolderSpace_apply_le (f n) x) hf
        _ = S := by
          dsimp only [S]
          rw [NNReal.coe_tsum]
          simp only [coe_nnnorm]
    simpa only [ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal hx
  have hgauge : eHolderGauge alpha g ≤ ((2 : NNReal) * S : NNReal) := by
    unfold eHolderGauge
    calc
      eSupNormOn Set.univ g + eHolderNorm alpha g ≤
          (S : ENNReal) + S := add_le_add hsup hholder.eHolderNorm_le
      _ = ((2 : NNReal) * S : NNReal) := by
        push_cast
        ring
  have hfinite : IsBoundedHolder alpha g :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hgauge
  let G : BoundedHolderSpace (X := X) (F := F) alpha := ⟨g, hfinite⟩
  refine ⟨G, fun x ↦ rfl, ?_⟩
  rw [norm_boundedHolderSpace_eq]
  have hreal := ENNReal.toReal_mono
    (show ((((2 : NNReal) * S : NNReal) : ENNReal) ≠ ⊤) from
      ENNReal.coe_ne_top) hgauge
  simpa only [ENNReal.toReal_ofNat, ENNReal.toReal_mul,
    G, g, S] using hreal

instance (alpha : NNReal) :
    CompleteSpace (BoundedHolderSpace (X := X) (F := F) alpha) := by
  apply NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
  intro f hf
  obtain ⟨g, hg, _hgnorm⟩ :=
    exists_boundedHolderSpace_pointwise_tsum f hf
  refine ⟨g, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hfPoint : ∀ x, Summable fun n ↦ f n x := by
    intro x
    exact Summable.of_norm_bounded hf fun n ↦
      norm_boundedHolderSpace_apply_le (f n) x
  have htailBound : ∀ N,
      ‖(∑ n ∈ Finset.range N, f n) - g‖ ≤
        (((2 : NNReal) * ∑' m, ‖f (m + N)‖₊ : NNReal) : Real) := by
    intro N
    have htailSummable : Summable fun m ↦ ‖f (m + N)‖ :=
      (summable_nat_add_iff N).mpr hf
    obtain ⟨tail, htail, htailNorm⟩ :=
      exists_boundedHolderSpace_pointwise_tsum
        (fun m ↦ f (m + N)) htailSummable
    have hdiff : (∑ n ∈ Finset.range N, f n) - g = -tail := by
      apply boundedHolderSpace_ext
      intro x
      rw [boundedHolderSpace_sub_apply, boundedHolderSpace_neg_apply,
        boundedHolderSpace_sum_apply]
      rw [hg x, htail x]
      have hsum := (hfPoint x).sum_add_tsum_nat_add N
      rw [← hsum]
      abel
    rw [hdiff, norm_neg]
    exact htailNorm
  have htailZero : Filter.Tendsto
      (fun N ↦ (((2 : NNReal) *
        ∑' m, ‖f (m + N)‖₊ : NNReal) : Real))
      Filter.atTop (nhds 0) := by
    have hNN :=
      (NNReal.tendsto_sum_nat_add (fun n ↦ ‖f n‖₊)).const_mul
        (2 : NNReal)
    have hNN' : Filter.Tendsto
        (fun N ↦ (2 : NNReal) * ∑' m, ‖f (m + N)‖₊)
        Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using hNN
    have hR : Filter.Tendsto
        (fun N ↦ (((2 : NNReal) *
          ∑' m, ‖f (m + N)‖₊ : NNReal) : Real))
        Filter.atTop (nhds (((0 : NNReal) : Real))) :=
      NNReal.tendsto_coe.mpr hNN'
    simpa only [NNReal.coe_zero] using hR
  exact squeeze_zero (fun _ ↦ norm_nonneg _) htailBound htailZero

end BoundedHolder

section Elliptic

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

private theorem exists_contDiffHolderSpace_pointwise_tsum
    {k : Nat} {alpha : NNReal}
    (f : Nat → ContDiffHolderSpace (V := V) (F := F) k alpha)
    (hf : Summable fun n ↦ ‖f n‖) :
    ∃ g : ContDiffHolderSpace (V := V) (F := F) k alpha,
      (∀ x, g x = ∑' n, f n x) ∧
      ‖g‖ ≤ ((((k + 2 : Nat) : NNReal) * ∑' n, ‖f n‖₊ : NNReal) : Real) := by
  let g : V → F := fun x ↦ ∑' n, f n x
  have hfNN : Summable fun n ↦ ‖f n‖₊ := by
    rw [← NNReal.summable_coe]
    simpa only [coe_nnnorm] using hf
  let S : NNReal := ∑' n, ‖f n‖₊
  have hcont : ∀ n, ContDiff Real k (contDiffHolderSpaceFun (f n)) := by
    intro n
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (f n).2.1.1 x (Set.mem_univ x)
  have hjetBound : ∀ (j n : Nat) (x : V), (j : ℕ∞) ≤ k →
      ‖iteratedFDeriv Real j (contDiffHolderSpaceFun (f n)) x‖ ≤ ‖f n‖ := by
    intro j n x hj
    exact contDiffHolderSpace_iteratedFDeriv_norm_le (f n)
      (by exact_mod_cast hj) x
  have hgCont : ContDiff Real k g := by
    exact contDiff_tsum (v := fun _ n ↦ ‖f n‖) hcont
      (fun _ _ ↦ hf) hjetBound
  have hjetEq : ∀ (j : Nat), (j : ℕ∞) ≤ k → ∀ x,
      iteratedFDeriv Real j g x =
        ∑' n, iteratedFDeriv Real j (contDiffHolderSpaceFun (f n)) x := by
    intro j hj x
    exact iteratedFDeriv_tsum_apply (v := fun _ n ↦ ‖f n‖) hcont
      (fun _ _ ↦ hf) hjetBound hj x
  have hjetNormSummable : ∀ (j : Nat), (j : ℕ∞) ≤ k → ∀ x,
      Summable fun n ↦
        ‖iteratedFDeriv Real j (contDiffHolderSpaceFun (f n)) x‖ := by
    intro j hj x
    exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ hjetBound j n x hj) hf
  have hjetSummable : ∀ (j : Nat), (j : ℕ∞) ≤ k → ∀ x,
      Summable fun n ↦
        iteratedFDeriv Real j (contDiffHolderSpaceFun (f n)) x := by
    intro j hj x
    exact Summable.of_norm_bounded hf fun n ↦ hjetBound j n x hj
  have htermHolder : ∀ n, HolderWith ‖f n‖₊ alpha
      (Set.univ.restrict
        (iteratedFDeriv Real k (contDiffHolderSpaceFun (f n)))) := by
    intro n
    apply topSpatialJet_holderWith_restrict
    rw [eContDiffHolderGaugeOn_eq_ofReal_norm]
    simp only [ofReal_norm_eq_enorm, enorm_eq_nnnorm, le_refl]
  have htopHolderTsum : HolderWith S alpha
      (fun x : (Set.univ : Set V) ↦
        ∑' n, Set.univ.restrict
          (iteratedFDeriv Real k
            (contDiffHolderSpaceFun (f n))) x) := by
    exact holderWith_tsum hfNN htermHolder fun x ↦
      hjetSummable k (by exact_mod_cast (le_refl k)) x
  have htopHolder : HolderWith S alpha
      (Set.univ.restrict (iteratedFDeriv Real k g)) := by
    intro x y
    change edist (iteratedFDeriv Real k g x)
      (iteratedFDeriv Real k g y) ≤ _
    rw [hjetEq k (by exact_mod_cast (le_refl k)) x,
      hjetEq k (by exact_mod_cast (le_refl k)) y]
    exact htopHolderTsum x y
  have hspatial : ∀ j ≤ k, ∀ x ∈ (Set.univ : Set V),
      ‖iteratedFDeriv Real j g x‖ ≤ S := by
    intro j hj x _hx
    rw [hjetEq j (by exact_mod_cast hj) x]
    calc
      ‖∑' n, iteratedFDeriv Real j
          (contDiffHolderSpaceFun (f n)) x‖ ≤
          ∑' n, ‖iteratedFDeriv Real j
            (contDiffHolderSpaceFun (f n)) x‖ :=
        norm_tsum_le_tsum_norm (hjetNormSummable j (by exact_mod_cast hj) x)
      _ ≤ ∑' n, ‖f n‖ :=
        (hjetNormSummable j (by exact_mod_cast hj) x).tsum_le_tsum
          (fun n ↦ hjetBound j n x (by exact_mod_cast hj)) hf
      _ = S := by
        dsimp only [S]
        rw [NNReal.coe_tsum]
        simp only [coe_nnnorm]
  have hgauge : eContDiffHolderGaugeOn k alpha Set.univ g ≤
      (∑ _j ∈ Finset.range (k + 1), (S : ENNReal)) + S :=
    eContDiffHolderGaugeOn_le (fun _ ↦ S) S hspatial htopHolder
  have hfinite : eContDiffHolderGaugeOn k alpha Set.univ g ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.coe_ne_top,
        ENNReal.coe_ne_top⟩) hgauge
  let G : ContDiffHolderSpace (V := V) (F := F) k alpha :=
    ⟨g, ⟨⟨fun x _ ↦ hgCont.contDiffAt, htopHolder.memHolder⟩, hfinite⟩⟩
  have hgauge' : eContDiffHolderGaugeOn k alpha Set.univ g ≤
      (((k + 2 : Nat) : NNReal) * S : NNReal) := by
    calc
      eContDiffHolderGaugeOn k alpha Set.univ g ≤
          (∑ _j ∈ Finset.range (k + 1), (S : ENNReal)) + S := hgauge
      _ = (((k + 2 : Nat) : NNReal) * S : NNReal) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
  refine ⟨G, fun x ↦ rfl, ?_⟩
  rw [norm_contDiffHolderSpace_eq]
  have hreal := ENNReal.toReal_mono
    (show ((((k + 2 : Nat) : NNReal) * S : NNReal) : ENNReal) ≠ ⊤ from
      ENNReal.coe_ne_top) hgauge'
  simpa only [ENNReal.toReal_ofNat, ENNReal.toReal_mul,
    Nat.cast_ofNat, G, g, S] using hreal

instance (k : Nat) (alpha : NNReal) :
    CompleteSpace (ContDiffHolderSpace (V := V) (F := F) k alpha) := by
  apply NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
  intro f hf
  obtain ⟨g, hg, _hgnorm⟩ :=
    exists_contDiffHolderSpace_pointwise_tsum f hf
  refine ⟨g, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hfPoint : ∀ x, Summable fun n ↦ f n x := by
    intro x
    exact Summable.of_norm_bounded hf fun n ↦
      norm_contDiffHolderSpace_apply_le (f n) x
  have htailBound : ∀ N,
      ‖(∑ n ∈ Finset.range N, f n) - g‖ ≤
        ((((k + 2 : Nat) : NNReal) *
          ∑' m, ‖f (m + N)‖₊ : NNReal) : Real) := by
    intro N
    have htailSummable : Summable fun m ↦ ‖f (m + N)‖ :=
      (summable_nat_add_iff N).mpr hf
    obtain ⟨tail, htail, htailNorm⟩ :=
      exists_contDiffHolderSpace_pointwise_tsum
        (fun m ↦ f (m + N)) htailSummable
    have hdiff : (∑ n ∈ Finset.range N, f n) - g = -tail := by
      apply contDiffHolderSpace_ext
      intro x
      rw [contDiffHolderSpace_sub_apply, contDiffHolderSpace_neg_apply,
        contDiffHolderSpace_sum_apply]
      rw [hg x, htail x]
      have hsum := (hfPoint x).sum_add_tsum_nat_add N
      rw [← hsum]
      abel
    rw [hdiff, norm_neg]
    exact htailNorm
  have htailZero : Filter.Tendsto
      (fun N ↦ ((((k + 2 : Nat) : NNReal) *
        ∑' m, ‖f (m + N)‖₊ : NNReal) : Real))
      Filter.atTop (nhds 0) := by
    have hNN :=
      (NNReal.tendsto_sum_nat_add (fun n ↦ ‖f n‖₊)).const_mul
        ((k + 2 : Nat) : NNReal)
    have hNN' : Filter.Tendsto
        (fun N ↦ ((k + 2 : Nat) : NNReal) *
          ∑' m, ‖f (m + N)‖₊)
        Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using hNN
    have hR : Filter.Tendsto
        (fun N ↦ ((((k + 2 : Nat) : NNReal) *
          ∑' m, ‖f (m + N)‖₊ : NNReal) : Real))
        Filter.atTop (nhds (((0 : NNReal) : Real))) :=
      NNReal.tendsto_coe.mpr hNN'
    simpa only [NNReal.coe_zero] using hR
  exact squeeze_zero (fun _ ↦ norm_nonneg _) htailBound htailZero

end Elliptic

section Parabolic

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

private theorem exists_parabolicC2HolderSpace_pointwise_tsum
    {alpha : NNReal}
    (u : Nat → ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (hu : Summable fun n ↦ ‖u n‖) :
    ∃ v : ParabolicC2HolderSpace (V := V) (F := F) alpha,
      (∀ t x, v t x = ∑' n, u n t x) ∧
      ‖v‖ ≤ (((6 : NNReal) * ∑' n, ‖u n‖₊ : NNReal) : Real) := by
  let v : Real → V → F := fun t x ↦ ∑' n, u n t x
  have huNN : Summable fun n ↦ ‖u n‖₊ := by
    rw [← NNReal.summable_coe]
    simpa only [coe_nnnorm] using hu
  let S : NNReal := ∑' n, ‖u n‖₊
  have hvalueSummable : ∀ t x, Summable fun n ↦ u n t x := by
    intro t x
    exact Summable.of_norm_bounded hu fun n ↦
      norm_parabolicC2HolderSpace_apply_le (u n) t x
  have hspaceCont : ∀ n t,
      ContDiff Real 2 (parabolicC2HolderSpaceFun (u n) t) := by
    intro n t
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (u n).2.1.1.1 (parabolicPoint t x) (Set.mem_univ _)
  have hspaceJetBound : ∀ (j n : Nat) (t : Real) (x : V),
      (j : ℕ∞) ≤ 2 →
      ‖iteratedFDeriv Real j
        (parabolicC2HolderSpaceFun (u n) t) x‖ ≤ ‖u n‖ := by
    intro j n t x hj
    simpa only [parabolicSpatialJet, parabolicPoint_time,
      parabolicPoint_space] using
        parabolicC2HolderSpace_spatialJet_norm_le (u n)
          (by exact_mod_cast hj) (parabolicPoint t x)
  have hvSpaceCont : ∀ t, ContDiff Real 2 (v t) := by
    intro t
    exact contDiff_tsum (v := fun _ n ↦ ‖u n‖) (fun n ↦ hspaceCont n t)
      (fun _ _ ↦ hu) (fun j n x hj ↦ hspaceJetBound j n t x hj)
  have hspaceJetEq : ∀ (j : Nat), (j : ℕ∞) ≤ 2 → ∀ p,
      parabolicSpatialJet j v p =
        ∑' n, parabolicSpatialJet j
          (parabolicC2HolderSpaceFun (u n)) p := by
    intro j hj p
    unfold parabolicSpatialJet
    exact iteratedFDeriv_tsum_apply (v := fun _ n ↦ ‖u n‖)
      (fun n ↦ hspaceCont n p.time) (fun _ _ ↦ hu)
      (fun q n x hq ↦ hspaceJetBound q n p.time x hq) hj p.space
  have hspaceJetNormSummable : ∀ (j : Nat), (j : ℕ∞) ≤ 2 → ∀ p,
      Summable fun n ↦ ‖parabolicSpatialJet j
        (parabolicC2HolderSpaceFun (u n)) p‖ := by
    intro j hj p
    exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ by
        simpa only [parabolicSpatialJet] using
          hspaceJetBound j n p.time p.space hj) hu
  have hspaceJetSummable : ∀ (j : Nat), (j : ℕ∞) ≤ 2 → ∀ p,
      Summable fun n ↦ parabolicSpatialJet j
        (parabolicC2HolderSpaceFun (u n)) p := by
    intro j hj p
    exact Summable.of_norm_bounded hu fun n ↦ by
      simpa only [parabolicSpatialJet] using
        hspaceJetBound j n p.time p.space hj
  have htimeHasDerivAt : ∀ n x t,
      HasDerivAt (fun s ↦ u n s x)
        (parabolicTimeDerivative (parabolicC2HolderSpaceFun (u n))
          (parabolicPoint t x)) t := by
    intro n x t
    have hdiff := (u n).2.1.1.2 (parabolicPoint t x) (Set.mem_univ _)
    simpa only [parabolicTimeDerivative, parabolicPoint_time,
      parabolicPoint_space, fderiv_apply_one_eq_deriv] using
        hdiff.hasDerivAt
  have htimeBound : ∀ n x t,
      ‖parabolicTimeDerivative (parabolicC2HolderSpaceFun (u n))
        (parabolicPoint t x)‖ ≤ ‖u n‖ := by
    intro n x t
    exact parabolicC2HolderSpace_timeDerivative_norm_le (u n)
      (parabolicPoint t x)
  have hvTimeHasDerivAt : ∀ x t,
      HasDerivAt (fun s ↦ v s x)
        (∑' n, parabolicTimeDerivative
          (parabolicC2HolderSpaceFun (u n)) (parabolicPoint t x)) t := by
    intro x t
    exact hasDerivAt_tsum hu (fun n s ↦ htimeHasDerivAt n x s)
      (fun n s ↦ htimeBound n x s) (hvalueSummable 0 x) t
  have htimeEq : ∀ p, parabolicTimeDerivative v p =
      ∑' n, parabolicTimeDerivative
        (parabolicC2HolderSpaceFun (u n)) p := by
    intro p
    unfold parabolicTimeDerivative
    rw [fderiv_apply_one_eq_deriv]
    exact (hvTimeHasDerivAt p.space p.time).deriv
  have htimeNormSummable : ∀ p, Summable fun n ↦
      ‖parabolicTimeDerivative
        (parabolicC2HolderSpaceFun (u n)) p‖ := by
    intro p
    exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ parabolicC2HolderSpace_timeDerivative_norm_le (u n) p) hu
  have htimeSummable : ∀ p, Summable fun n ↦
      parabolicTimeDerivative
        (parabolicC2HolderSpaceFun (u n)) p := by
    intro p
    exact Summable.of_norm_bounded hu fun n ↦
      parabolicC2HolderSpace_timeDerivative_norm_le (u n) p
  have htermSpaceHolder : ∀ n, HolderWith ‖u n‖₊ alpha
      (Set.univ.restrict (parabolicSpatialJet 2
        (parabolicC2HolderSpaceFun (u n)))) := by
    intro n
    apply parabolicSpatialJet_holderWith_restrict
    rw [eParabolicC2HolderGaugeOn_eq_ofReal_norm]
    simp only [ofReal_norm_eq_enorm, enorm_eq_nnnorm, le_refl]
  have htermTimeHolder : ∀ n, HolderWith ‖u n‖₊ alpha
      (Set.univ.restrict (parabolicTimeDerivative
        (parabolicC2HolderSpaceFun (u n)))) := by
    intro n
    apply parabolicTimeDerivative_holderWith_restrict
    rw [eParabolicC2HolderGaugeOn_eq_ofReal_norm]
    simp only [ofReal_norm_eq_enorm, enorm_eq_nnnorm, le_refl]
  have hspaceHolderTsum : HolderWith S alpha
      (fun p : (Set.univ : Set (ParabolicPoint V)) ↦
        ∑' n, Set.univ.restrict (parabolicSpatialJet 2
          (parabolicC2HolderSpaceFun (u n))) p) := by
    exact holderWith_tsum huNN htermSpaceHolder fun p ↦
      hspaceJetSummable 2 (by norm_num) p
  have htimeHolderTsum : HolderWith S alpha
      (fun p : (Set.univ : Set (ParabolicPoint V)) ↦
        ∑' n, Set.univ.restrict (parabolicTimeDerivative
          (parabolicC2HolderSpaceFun (u n))) p) := by
    exact holderWith_tsum huNN htermTimeHolder fun p ↦ htimeSummable p
  have hspaceHolder : HolderWith S alpha
      (Set.univ.restrict (parabolicSpatialJet 2 v)) := by
    intro p q
    change edist (parabolicSpatialJet 2 v p)
      (parabolicSpatialJet 2 v q) ≤ _
    rw [hspaceJetEq 2 (by norm_num) p, hspaceJetEq 2 (by norm_num) q]
    exact hspaceHolderTsum p q
  have htimeHolder : HolderWith S alpha
      (Set.univ.restrict (parabolicTimeDerivative v)) := by
    intro p q
    change edist (parabolicTimeDerivative v p)
      (parabolicTimeDerivative v q) ≤ _
    rw [htimeEq p, htimeEq q]
    exact htimeHolderTsum p q
  have hspatial : ∀ j < 3, ∀ p ∈ (Set.univ : Set (ParabolicPoint V)),
      ‖parabolicSpatialJet j v p‖ ≤ S := by
    intro j hj p _hp
    have hj' : (j : ℕ∞) ≤ 2 := by exact_mod_cast (by omega : j ≤ 2)
    rw [hspaceJetEq j hj' p]
    calc
      ‖∑' n, parabolicSpatialJet j
          (parabolicC2HolderSpaceFun (u n)) p‖ ≤
          ∑' n, ‖parabolicSpatialJet j
            (parabolicC2HolderSpaceFun (u n)) p‖ :=
        norm_tsum_le_tsum_norm (hspaceJetNormSummable j hj' p)
      _ ≤ ∑' n, ‖u n‖ :=
        (hspaceJetNormSummable j hj' p).tsum_le_tsum
          (fun n ↦ parabolicC2HolderSpace_spatialJet_norm_le (u n)
            (by omega) p) hu
      _ = S := by
        dsimp only [S]
        rw [NNReal.coe_tsum]
        simp only [coe_nnnorm]
  have htime : ∀ p ∈ (Set.univ : Set (ParabolicPoint V)),
      ‖parabolicTimeDerivative v p‖ ≤ S := by
    intro p _hp
    rw [htimeEq p]
    calc
      ‖∑' n, parabolicTimeDerivative
          (parabolicC2HolderSpaceFun (u n)) p‖ ≤
          ∑' n, ‖parabolicTimeDerivative
            (parabolicC2HolderSpaceFun (u n)) p‖ :=
        norm_tsum_le_tsum_norm (htimeNormSummable p)
      _ ≤ ∑' n, ‖u n‖ :=
        (htimeNormSummable p).tsum_le_tsum
          (fun n ↦ parabolicC2HolderSpace_timeDerivative_norm_le (u n) p) hu
      _ = S := by
        dsimp only [S]
        rw [NNReal.coe_tsum]
        simp only [coe_nnnorm]
  have hgauge : eParabolicC2HolderGaugeOn alpha Set.univ v ≤
      (∑ _j ∈ Finset.range 3, (S : ENNReal)) + S + S + S :=
    eParabolicC2HolderGaugeOn_le (fun _ ↦ S) S S S
      hspatial htime hspaceHolder htimeHolder
  have hgauge' : eParabolicC2HolderGaugeOn alpha Set.univ v ≤
      ((6 : NNReal) * S : NNReal) := by
    calc
      eParabolicC2HolderGaugeOn alpha Set.univ v ≤
          (∑ _j ∈ Finset.range 3, (S : ENNReal)) + S + S + S := hgauge
      _ = ((6 : NNReal) * S : NNReal) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        norm_num
        ring
  have hfinite : eParabolicC2HolderGaugeOn alpha Set.univ v ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hgauge'
  let Vsum : ParabolicC2HolderSpace (V := V) (F := F) alpha :=
    ⟨v, ⟨⟨⟨fun p _ ↦ (hvSpaceCont p.time).contDiffAt,
      fun p _ ↦ (hvTimeHasDerivAt p.space p.time).differentiableAt⟩,
      hspaceHolder.memHolder, htimeHolder.memHolder⟩, hfinite⟩⟩
  refine ⟨Vsum, fun _ _ ↦ rfl, ?_⟩
  rw [norm_parabolicC2HolderSpace_eq]
  have hreal := ENNReal.toReal_mono
    (show (((6 : NNReal) * S : NNReal) : ENNReal) ≠ ⊤ from
      ENNReal.coe_ne_top) hgauge'
  simpa only [ENNReal.toReal_ofNat, ENNReal.toReal_mul,
    Nat.cast_ofNat, Vsum, v, S] using hreal

instance (alpha : NNReal) :
    CompleteSpace (ParabolicC2HolderSpace (V := V) (F := F) alpha) := by
  apply NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
  intro u hu
  obtain ⟨v, hv, _hvnorm⟩ :=
    exists_parabolicC2HolderSpace_pointwise_tsum u hu
  refine ⟨v, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have huPoint : ∀ t x, Summable fun n ↦ u n t x := by
    intro t x
    exact Summable.of_norm_bounded hu fun n ↦
      norm_parabolicC2HolderSpace_apply_le (u n) t x
  have htailBound : ∀ N,
      ‖(∑ n ∈ Finset.range N, u n) - v‖ ≤
        (((6 : NNReal) * ∑' m, ‖u (m + N)‖₊ : NNReal) : Real) := by
    intro N
    have htailSummable : Summable fun m ↦ ‖u (m + N)‖ :=
      (summable_nat_add_iff N).mpr hu
    obtain ⟨tail, htail, htailNorm⟩ :=
      exists_parabolicC2HolderSpace_pointwise_tsum
        (fun m ↦ u (m + N)) htailSummable
    have hdiff : (∑ n ∈ Finset.range N, u n) - v = -tail := by
      apply parabolicC2HolderSpace_ext
      intro t x
      rw [parabolicC2HolderSpace_sub_apply,
        parabolicC2HolderSpace_neg_apply,
        parabolicC2HolderSpace_sum_apply]
      rw [hv t x, htail t x]
      have hsum := (huPoint t x).sum_add_tsum_nat_add N
      rw [← hsum]
      abel
    rw [hdiff, norm_neg]
    exact htailNorm
  have htailZero : Filter.Tendsto
      (fun N ↦ (((6 : NNReal) *
        ∑' m, ‖u (m + N)‖₊ : NNReal) : Real))
      Filter.atTop (nhds 0) := by
    have hNN :=
      (NNReal.tendsto_sum_nat_add (fun n ↦ ‖u n‖₊)).const_mul
        (6 : NNReal)
    have hNN' : Filter.Tendsto
        (fun N ↦ (6 : NNReal) * ∑' m, ‖u (m + N)‖₊)
        Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using hNN
    have hR : Filter.Tendsto
        (fun N ↦ (((6 : NNReal) *
          ∑' m, ‖u (m + N)‖₊ : NNReal) : Real))
        Filter.atTop (nhds (((0 : NNReal) : Real))) :=
      NNReal.tendsto_coe.mpr hNN'
    simpa only [NNReal.coe_zero] using hR
  exact squeeze_zero (fun _ ↦ norm_nonneg _) htailBound htailZero

end Parabolic

end DifferentialGeometry.Analysis.Schauder
