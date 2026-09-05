import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Interval Topology

namespace AbsolutelyContinuousOnInterval

variable {X : Type*} [PseudoMetricSpace X]

theorem piecewise_Iic {f g : ℝ → X} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g b c)
    (hfg : f b = g b) :
    AbsolutelyContinuousOnInterval (Set.piecewise (Set.Iic b) f g) a c := by
  classical
  rw [absolutelyContinuousOnInterval_iff] at hf hg ⊢
  intro ε hε
  obtain ⟨δf, hδf, hf⟩ := hf (ε / 2) (half_pos hε)
  obtain ⟨δg, hδg, hg⟩ := hg (ε / 2) (half_pos hε)
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  rintro ⟨n, p⟩ hp hpLen
  change
    (∀ i ∈ Finset.range n, (p i).1 ∈ uIcc a c ∧ (p i).2 ∈ uIcc a c) ∧
      Set.PairwiseDisjoint (Finset.range n) (fun i ↦ uIoc (p i).1 (p i).2) at hp
  rcases hp with ⟨hpEnds, hpDisj⟩
  have hleft_subset (x y : ℝ) :
      uIoc (min x b) (min y b) ⊆ uIoc x y := by
    simp only [uIoc]
    grind
  have hright_subset (x y : ℝ) :
      uIoc (max x b) (max y b) ⊆ uIoc x y := by
    simp only [uIoc]
    grind
  have hpLeft :
      (n, fun i ↦ (min (p i).1 b, min (p i).2 b)) ∈ disjWithin a b := by
    refine ⟨?_, hpDisj.mono (fun i ↦ hleft_subset (p i).1 (p i).2)⟩
    intro i hi
    have hiEnds := hpEnds i hi
    rw [uIcc_of_le (hab.trans hbc)] at hiEnds
    rw [uIcc_of_le hab]
    exact ⟨⟨le_min hiEnds.1.1 hab, min_le_right _ _⟩,
      ⟨le_min hiEnds.2.1 hab, min_le_right _ _⟩⟩
  have hpRight :
      (n, fun i ↦ (max (p i).1 b, max (p i).2 b)) ∈ disjWithin b c := by
    refine ⟨?_, hpDisj.mono (fun i ↦ hright_subset (p i).1 (p i).2)⟩
    intro i hi
    have hiEnds := hpEnds i hi
    rw [uIcc_of_le (hab.trans hbc)] at hiEnds
    rw [uIcc_of_le hbc]
    exact ⟨⟨le_max_right _ _, max_le hiEnds.1.2 hbc⟩,
      ⟨le_max_right _ _, max_le hiEnds.2.2 hbc⟩⟩
  have hleftLen :
      ∑ i ∈ Finset.range n, dist (min (p i).1 b) (min (p i).2 b) < δf := by
    refine lt_of_le_of_lt (Finset.sum_le_sum fun i _ ↦ ?_) (hpLen.trans_le (min_le_left _ _))
    simpa using (LipschitzWith.id.min_const b).dist_le_mul (p i).1 (p i).2
  have hrightLen :
      ∑ i ∈ Finset.range n, dist (max (p i).1 b) (max (p i).2 b) < δg := by
    refine lt_of_le_of_lt (Finset.sum_le_sum fun i _ ↦ ?_) (hpLen.trans_le (min_le_right _ _))
    simpa using (LipschitzWith.id.max_const b).dist_le_mul (p i).1 (p i).2
  have hfSum := hf (n, fun i ↦ (min (p i).1 b, min (p i).2 b)) hpLeft hleftLen
  have hgSum := hg (n, fun i ↦ (max (p i).1 b, max (p i).2 b)) hpRight hrightLen
  have hdist (x y : ℝ) :
      dist (Set.piecewise (Set.Iic b) f g x)
          (Set.piecewise (Set.Iic b) f g y) ≤
        dist (f (min x b)) (f (min y b)) +
          dist (g (max x b)) (g (max y b)) := by
    by_cases hx : x ≤ b <;> by_cases hy : y ≤ b
    · simp [Set.piecewise, hx, hy]
    · have hby : b ≤ y := le_of_not_ge hy
      simpa [Set.piecewise, hx, hy, min_eq_left, min_eq_right hby,
        max_eq_right, max_eq_left hby, hfg] using dist_triangle (f x) (f b) (g y)
    · have hbx : b ≤ x := le_of_not_ge hx
      simpa [Set.piecewise, hx, hy, min_eq_right hbx, min_eq_left,
        max_eq_left hbx, max_eq_right, hfg, add_comm] using
        dist_triangle (g x) (g b) (f y)
    · have hbx : b ≤ x := le_of_not_ge hx
      have hby : b ≤ y := le_of_not_ge hy
      simp [Set.piecewise, hx, hy, min_eq_right hbx, min_eq_right hby,
        max_eq_left hbx, max_eq_left hby]
  calc
    ∑ i ∈ Finset.range n,
        dist (Set.piecewise (Set.Iic b) f g (p i).1)
          (Set.piecewise (Set.Iic b) f g (p i).2) ≤
        ∑ i ∈ Finset.range n,
          (dist (f (min (p i).1 b)) (f (min (p i).2 b)) +
            dist (g (max (p i).1 b)) (g (max (p i).2 b))) :=
      Finset.sum_le_sum fun i _ ↦ hdist (p i).1 (p i).2
    _ =
        (∑ i ∈ Finset.range n,
          dist (f (min (p i).1 b)) (f (min (p i).2 b))) +
        ∑ i ∈ Finset.range n,
          dist (g (max (p i).1 b)) (g (max (p i).2 b)) := by
      rw [Finset.sum_add_distrib]
    _ < ε / 2 + ε / 2 := add_lt_add hfSum hgSum
    _ = ε := by ring

theorem congr {f g : ℝ → X} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hfg : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hf⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro p hp hpLen
  have hpEnds := hp.1
  convert hf p hp hpLen using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hfg (hpEnds i hi).1, ← hfg (hpEnds i hi).2]

theorem _root_.LipschitzOnWith.comp_absolutelyContinuousOnInterval
    {Y : Type*} [PseudoMetricSpace Y]
    {f : X → Y} {g : ℝ → X} {s : Set X} {K : NNReal} {a b : ℝ}
    (hf : LipschitzOnWith K f s)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hgs : MapsTo g (uIcc a b) s) :
    AbsolutelyContinuousOnInterval (f ∘ g) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hg⟩ := hg (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro p hp hpLen
  have hgSum := hg p hp hpLen
  have hpEnds := hp.1
  calc
    ∑ i ∈ Finset.range p.1,
        dist ((f ∘ g) (p.2 i).1) ((f ∘ g) (p.2 i).2) ≤
        ∑ i ∈ Finset.range p.1,
          K * dist (g (p.2 i).1) (g (p.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hle := hf
        (hgs (hpEnds i hi).1) (hgs (hpEnds i hi).2)
      apply ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) at hle
      simpa only [Function.comp_apply, ENNReal.toReal_mul, ENNReal.coe_toReal,
        ← dist_edist] using hle
    _ = K * ∑ i ∈ Finset.range p.1,
        dist (g (p.2 i).1) (g (p.2 i).2) := by
      rw [Finset.mul_sum]
    _ ≤ K * (ε / (K + 1)) := by
      gcongr
    _ < (K + 1) * (ε / (K + 1)) := by
      gcongr
      linarith
    _ = ε := by field

theorem comp_monotone_lipschitzOn
    {f : ℝ → X} {g : ℝ → ℝ} {a b c d : ℝ} {K : NNReal}
    (hf : AbsolutelyContinuousOnInterval f c d)
    (hg : LipschitzOnWith K g (uIcc a b))
    (hmono : MonotoneOn g (uIcc a b))
    (hmap : MapsTo g (uIcc a b) (uIcc c d)) :
    AbsolutelyContinuousOnInterval (f ∘ g) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hf⟩ := hf ε hε
  refine ⟨δ / (K + 1), by positivity, ?_⟩
  rintro ⟨n, p⟩ hp hpLen
  let q : ℕ → ℝ × ℝ := fun i ↦ (g (p i).1, g (p i).2)
  have hmin_mem {x y : ℝ} (hx : x ∈ uIcc a b) (hy : y ∈ uIcc a b) :
      min x y ∈ uIcc a b := by
    rw [uIcc] at hx hy ⊢
    exact ⟨le_min hx.1 hy.1, (min_le_left x y).trans hx.2⟩
  have hmax_mem {x y : ℝ} (hx : x ∈ uIcc a b) (hy : y ∈ uIcc a b) :
      max x y ∈ uIcc a b := by
    rw [uIcc] at hx hy ⊢
    exact ⟨hx.1.trans (le_max_left x y), max_le hx.2 hy.2⟩
  have hmin_map {x y : ℝ} (hx : x ∈ uIcc a b) (hy : y ∈ uIcc a b) :
      g (min x y) = min (g x) (g y) := by
    rcases le_total x y with hxy | hyx
    · rw [min_eq_left hxy, min_eq_left (hmono hx hy hxy)]
    · rw [min_eq_right hyx, min_eq_right (hmono hy hx hyx)]
  have hmax_map {x y : ℝ} (hx : x ∈ uIcc a b) (hy : y ∈ uIcc a b) :
      g (max x y) = max (g x) (g y) := by
    rcases le_total x y with hxy | hyx
    · rw [max_eq_right hxy, max_eq_right (hmono hx hy hxy)]
    · rw [max_eq_left hyx, max_eq_left (hmono hy hx hyx)]
  have hq : (n, q) ∈ disjWithin c d := by
    refine ⟨?_, ?_⟩
    · intro i hi
      exact ⟨hmap (hp.1 i hi).1, hmap (hp.1 i hi).2⟩
    · intro i hi j hj hij
      have hdisj := hp.2 hi hj hij
      simp only [uIoc, Set.Ioc_disjoint_Ioc] at hdisj ⊢
      have hiMin := hmin_mem (hp.1 i hi).1 (hp.1 i hi).2
      have hiMax := hmax_mem (hp.1 i hi).1 (hp.1 i hi).2
      have hjMin := hmin_mem (hp.1 j hj).1 (hp.1 j hj).2
      have hjMax := hmax_mem (hp.1 j hj).1 (hp.1 j hj).2
      have hleft := hmin_mem hiMax hjMax
      have hright := hmax_mem hiMin hjMin
      have horder := hmono hleft hright hdisj
      rw [hmin_map hiMax hjMax, hmax_map hiMin hjMin,
        hmax_map (hp.1 i hi).1 (hp.1 i hi).2,
        hmax_map (hp.1 j hj).1 (hp.1 j hj).2,
        hmin_map (hp.1 i hi).1 (hp.1 i hi).2,
        hmin_map (hp.1 j hj).1 (hp.1 j hj).2] at horder
      exact horder
  apply hf (n, q) hq
  calc
    ∑ i ∈ Finset.range n, dist (q i).1 (q i).2 ≤
        ∑ i ∈ Finset.range n, K * dist (p i).1 (p i).2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hle := hg (hp.1 i hi).1 (hp.1 i hi).2
      apply ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) at hle
      simpa only [q, ENNReal.toReal_mul, ENNReal.coe_toReal, ← dist_edist] using hle
    _ = K * ∑ i ∈ Finset.range n, dist (p i).1 (p i).2 := by
      rw [Finset.mul_sum]
    _ ≤ K * (δ / (K + 1)) := by
      gcongr
    _ < (K + 1) * (δ / (K + 1)) := by
      gcongr
      linarith
    _ = δ := by field

theorem comp_sq
    {f : ℝ → X} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f (a ^ 2) (b ^ 2)) :
    AbsolutelyContinuousOnInterval (f ∘ fun s : ℝ ↦ s ^ 2) a b := by
  obtain ⟨K, hK⟩ :=
    (contDiff_id.pow 2).contDiffOn.exists_lipschitzOnWith
      one_ne_zero (convex_Icc a b) isCompact_Icc
  apply comp_monotone_lipschitzOn hf (by simpa only [uIcc_of_le hab, id_eq] using hK)
  · intro x hx y hy hxy
    rw [uIcc_of_le hab] at hx hy
    exact (sq_le_sq₀ (ha.trans hx.1) (ha.trans hy.1)).2 hxy
  · intro s hs
    rw [uIcc_of_le hab] at hs
    have hs0 : 0 ≤ s := ha.trans hs.1
    rw [uIcc_of_le ((sq_le_sq₀ ha (ha.trans hab)).2 hab)]
    exact ⟨(sq_le_sq₀ ha hs0).2 hs.1,
      (sq_le_sq₀ hs0 (ha.trans hab)).2 hs.2⟩

end AbsolutelyContinuousOnInterval

namespace Real

theorem absolutelyContinuousOnInterval_sqrt (a b : ℝ) :
    AbsolutelyContinuousOnInterval sqrt a b := by
  let q : ℝ := -(1 / 2 : ℝ)
  let v : ℝ → ℝ := fun t ↦ (1 / 2 : ℝ) * t ^ q
  have hvInt : IntervalIntegrable v volume a b := by
    exact (intervalIntegral.intervalIntegrable_rpow'
      (a := a) (b := b) (by norm_num [q])).const_mul (1 / 2 : ℝ)
  have hprim : AbsolutelyContinuousOnInterval
      (fun x ↦ ∫ t in a..x, v t) a b :=
    hvInt.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hconst : AbsolutelyContinuousOnInterval
      (fun _ : ℝ ↦ sqrt a) a b :=
    (LipschitzWith.const (sqrt a)).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hconst.add hprim).congr
  intro x _
  simp only [Pi.add_apply, v, q]
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]
  simp only [← sqrt_eq_rpow]
  ring

end Real

namespace AbsolutelyContinuousOnInterval

variable {f g : ℝ → ℝ} {a b : ℝ}

theorem sub_le_integral_of_dini_le (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntervalIntegrable g volume a b)
    (hD : ∀ t ∈ Ioo a b, ∀ ε, 0 < ε →
      ∀ᶠ s in 𝓝[>] t, slope f t s ≤ g t + ε) :
    f b - f a ≤ ∫ t in a..b, g t := by
  have hdiff : ∀ᵐ t ∂volume.restrict (Icc a b),
      DifferentiableAt ℝ f t := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    simpa only [uIcc_of_le hab] using hf.ae_differentiableAt
  have hmem : ∀ᵐ t ∂volume.restrict (Icc a b), t ∈ Ioo a b := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [Ioo_ae_eq_Icc (μ := volume)] with t ht htab
    exact ht.mpr htab
  have hle : ∀ᵐ t ∂volume.restrict (Icc a b), deriv f t ≤ g t := by
    filter_upwards [hdiff, hmem] with t ht htab
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    exact le_of_tendsto
      (ht.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t))
      (hD t htab ε hε)
  rw [← hf.integral_deriv_eq_sub]
  exact intervalIntegral.integral_mono_ae_restrict hab
    hf.intervalIntegrable_deriv hg hle

theorem _root_.ContinuousOn.sub_le_integral_of_dini_le (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hfac : ∀ c ∈ Ioc a b, AbsolutelyContinuousOnInterval f c b)
    (hg : IntervalIntegrable g volume a b)
    (hD : ∀ t ∈ Ioo a b, ∀ ε, 0 < ε →
      ∀ᶠ s in 𝓝[>] t, slope f t s ≤ g t + ε) :
    f b - f a ≤ ∫ t in a..b, g t := by
  obtain rfl | hab' := hab.eq_or_lt
  · simp
  let s := {c | f b - f c ≤ ∫ t in c..b, g t} ∩ Icc a b
  have hs : IsClosed s := by
    have hgIcc : IntegrableOn g (Icc a b) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hg
    have hgU : IntegrableOn g (uIcc a b) := by
      simpa only [uIcc_of_le hab] using hgIcc
    have hprim : ContinuousOn (fun c ↦ ∫ t in c..b, g t) (Icc a b) := by
      simpa only [uIcc_of_le hab] using
        (intervalIntegral.continuousOn_primitive_interval_left
          (f := g) (μ := volume) (a := a) (b := b) hgU)
    simpa only [s, inter_comm, Pi.sub_apply, Set.inter_def, Set.mem_ofPred_eq] using
      isClosed_Icc.isClosed_le (continuousOn_const.sub hf) hprim
  have hclosure : closure (Ioc a b) ⊆ s := by
    apply hs.closure_subset_iff.2
    intro c hc
    have hcb : c ≤ b := hc.2
    have hgcb : IntervalIntegrable g volume c b := by
      apply hg.mono_set
      rw [uIcc_of_le hcb, uIcc_of_le hab]
      exact Icc_subset_Icc hc.1.le le_rfl
    refine ⟨AbsolutelyContinuousOnInterval.sub_le_integral_of_dini_le (f := f) (g := g) hcb
      (hfac c hc) hgcb ?_, ⟨hc.1.le, hc.2⟩⟩
    intro t ht
    exact hD t ⟨hc.1.trans ht.1, ht.2⟩
  rw [closure_Ioc hab'.ne] at hclosure
  exact (hclosure (left_mem_Icc.2 hab)).1

end AbsolutelyContinuousOnInterval
