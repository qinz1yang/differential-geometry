import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.ChartTimeH1
import Mathlib.Geometry.Manifold.ContMDiff.Basic

set_option autoImplicit false

noncomputable section

open Filter Function Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

def flatExtend {X : Type*} (f : ℝ → X) (a b : ℝ) : ℝ → X :=
  Set.piecewise (Iic a) (fun _ ↦ f a)
    (Set.piecewise (Iic b) f (fun _ ↦ f b))

theorem flatExtend_of_mem {X : Type*} (f : ℝ → X) {a b s : ℝ}
    (hs : s ∈ Icc a b) : flatExtend f a b s = f s := by
  by_cases hsa : s ≤ a
  · have hsa' : s = a := le_antisymm hsa hs.1
    subst s
    simp only [flatExtend, Set.piecewise_eq_of_mem, mem_Iic, le_rfl]
  · rw [flatExtend, (Iic a).piecewise_eq_of_notMem _ _ hsa,
      (Iic b).piecewise_eq_of_mem _ _ hs.2]

theorem flatExtend_self {X : Type*} (f : ℝ → X) (a : ℝ) :
    flatExtend f a a = fun _ ↦ f a := by
  funext s
  by_cases hs : s ≤ a
  · exact (Iic a).piecewise_eq_of_mem (fun _ ↦ f a)
      (Set.piecewise (Iic a) f (fun _ ↦ f a)) hs
  · rw [flatExtend, (Iic a).piecewise_eq_of_notMem _ _ hs,
      (Iic a).piecewise_eq_of_notMem _ _ hs]

theorem flatExtend_mapsTo {X : Type*} (f : ℝ → X) {a b : ℝ}
    (hab : a ≤ b) {U : Set X} (hf : MapsTo f (Icc a b) U) :
    MapsTo (flatExtend f a b) univ U := by
  intro s _hs
  by_cases hsa : s ≤ a
  · rw [flatExtend, (Iic a).piecewise_eq_of_mem _ _ hsa]
    exact hf ⟨le_rfl, hab⟩
  · rw [flatExtend, (Iic a).piecewise_eq_of_notMem _ _ hsa]
    by_cases hsb : s ≤ b
    · rw [(Iic b).piecewise_eq_of_mem _ _ hsb]
      exact hf ⟨le_of_not_ge hsa, hsb⟩
    · rw [(Iic b).piecewise_eq_of_notMem _ _ hsb]
      exact hf ⟨hab, le_rfl⟩

theorem flatExtend_cont {X : Type*} [TopologicalSpace X]
    (f : ℝ → X) {a b : ℝ} (hab : a ≤ b) (hf : Continuous f) :
    Continuous (flatExtend f a b) := by
  let tail : ℝ → X := Set.piecewise (Iic b) f (fun _ ↦ f b)
  have htail : Continuous tail := by
    apply hf.piecewise (s := Iic b) ?_ continuous_const
    intro s hs
    have hs' : s = b := by
      simpa only [frontier_Iic, Set.mem_singleton_iff] using hs
    subst s
    rfl
  have htaila : tail a = f a := by
    exact ((Iic b).piecewise_eq_of_mem f (fun _ ↦ f b) hab)
  change Continuous (Set.piecewise (Iic a) (fun _ ↦ f a) tail)
  apply continuous_const.piecewise (s := Iic a) ?_ htail
  intro s hs
  have hs' : s = a := by
    simpa only [frontier_Iic, Set.mem_singleton_iff] using hs
  subst s
  exact htaila.symm

theorem flatExtend_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ℝ → X) {a b : ℝ} (hab : a ≤ b) (hf : ContDiff ℝ 1 f)
    (ha : f =ᶠ[𝓝 a] fun _ ↦ f a) (hb : f =ᶠ[𝓝 b] fun _ ↦ f b) :
    ContDiff ℝ 1 (flatExtend f a b) := by
  rcases hab.eq_or_lt with rfl | hab
  · rw [flatExtend_self]
    exact contDiff_const
  let tail : ℝ → X := Set.piecewise (Iic b) f (fun _ ↦ f b)
  have htail : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, X) 1 tail := by
    exact ContMDiff.piecewise_Iic hf.contMDiff contMDiff_const hb
  have htail_f : tail =ᶠ[𝓝 a] f := by
    filter_upwards [eventually_lt_nhds hab] with s hs
    exact (Iic b).piecewise_eq_of_mem f (fun _ ↦ f b) hs.le
  have hjoin : (fun _ : ℝ ↦ f a) =ᶠ[𝓝 a] tail :=
    ha.symm.trans htail_f.symm
  change ContDiff ℝ 1 (Set.piecewise (Iic a) (fun _ ↦ f a) tail)
  exact (ContMDiff.piecewise_Iic contMDiff_const htail hjoin).contDiff

theorem flatExtend_left {X : Type*} (f : ℝ → X) {a b : ℝ}
    (hab : a ≤ b) (ha : f =ᶠ[𝓝 a] fun _ ↦ f a) :
    flatExtend f a b =ᶠ[𝓝 a] fun _ ↦ f a := by
  rcases hab.eq_or_lt with rfl | hab
  · rw [flatExtend_self]
  filter_upwards [ha, eventually_lt_nhds hab] with s hsa hsb
  by_cases hle : s ≤ a
  · exact (Iic a).piecewise_eq_of_mem (fun _ ↦ f a)
      (Set.piecewise (Iic b) f (fun _ ↦ f b)) hle
  · rw [flatExtend, (Iic a).piecewise_eq_of_notMem _ _ hle,
      (Iic b).piecewise_eq_of_mem _ _ hsb.le, hsa]

theorem flatExtend_right {X : Type*} (f : ℝ → X) {a b : ℝ}
    (hab : a ≤ b) (hb : f =ᶠ[𝓝 b] fun _ ↦ f b) :
    flatExtend f a b =ᶠ[𝓝 b] fun _ ↦ f b := by
  rcases hab.eq_or_lt with rfl | hab
  · rw [flatExtend_self]
  filter_upwards [hb, eventually_gt_nhds hab] with s hsb hsa
  have hnot : ¬ s ≤ a := not_le.mpr hsa
  rw [flatExtend, (Iic a).piecewise_eq_of_notMem _ _ hnot]
  by_cases hle : s ≤ b
  · rw [(Iic b).piecewise_eq_of_mem _ _ hle, hsb]
  · exact (Iic b).piecewise_eq_of_notMem f (fun _ ↦ f b) hle

def flatJoin {X : Type*} (x : X) (t : ℕ → ℝ) (f : ℕ → ℝ → X) : ℕ → ℝ → X
  | 0 => fun _ ↦ x
  | n + 1 => Set.piecewise (Iic (t n)) (flatJoin x t f n) (f n)

theorem flatJoin_eq {X : Type*} (x : X) (t : ℕ → ℝ) (f : ℕ → ℝ → X)
    (ht : Monotone t) {n i : ℕ} (hi : i < n) {s : ℝ}
    (hleft : t i < s) (hright : s ≤ t (i + 1)) :
    flatJoin x t f n s = f i s := by
  induction n generalizing i s with
  | zero => exact (Nat.not_lt_zero i hi).elim
  | succ n hn =>
      by_cases hin : i = n
      · subst i
        exact (Iic (t n)).piecewise_eq_of_notMem
          (flatJoin x t f n) (f n) (not_le.mpr hleft)
      · have hinle : i ≤ n := Nat.lt_succ_iff.mp hi
        have hi' : i < n := lt_of_le_of_ne hinle hin
        have hs : s ≤ t n := hright.trans (ht (Nat.succ_le_iff.mpr hi'))
        rw [flatJoin, (Iic (t n)).piecewise_eq_of_mem _ _ hs]
        exact hn hi' hleft hright

theorem flatJoin_contMDiff
    {E₁ H₁ M₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H₁] (I₁ : ModelWithCorners ℝ E₁ H₁)
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    (x : M₁) (t : ℕ → ℝ) (f : ℕ → ℝ → M₁) (ht : Monotone t)
    (hf : ∀ n, ContMDiff 𝓘(ℝ, ℝ) I₁ 1 (f n))
    (hzero : (fun _ : ℝ ↦ x) =ᶠ[𝓝 (t 0)] f 0)
    (hjoin : ∀ n, f n =ᶠ[𝓝 (t (n + 1))] f (n + 1)) :
    ∀ n, ContMDiff 𝓘(ℝ, ℝ) I₁ 1 (flatJoin x t f n) := by
  have hmain : ∀ n, ContMDiff 𝓘(ℝ, ℝ) I₁ 1 (flatJoin x t f n) ∧
      flatJoin x t f n =ᶠ[𝓝 (t n)] f n := by
    intro n
    induction n with
    | zero => exact ⟨contMDiff_const, hzero⟩
    | succ n hn =>
        have hsmooth : ContMDiff 𝓘(ℝ, ℝ) I₁ 1 (flatJoin x t f (n + 1)) := by
          exact ContMDiff.piecewise_Iic hn.1 (hf n) hn.2
        refine ⟨hsmooth, ?_⟩
        rcases (ht (Nat.le_succ n)).eq_or_lt with heq | hlt
        · have hpiece : flatJoin x t f (n + 1) =ᶠ[𝓝 (t n)] f n := by
            filter_upwards [hn.2] with s hs
            by_cases hle : s ≤ t n
            · exact ((Iic (t n)).piecewise_eq_of_mem
                (flatJoin x t f n) (f n) hle).trans hs
            · exact (Iic (t n)).piecewise_eq_of_notMem
                (flatJoin x t f n) (f n) hle
          have hj : f n =ᶠ[𝓝 (t n)] f (n + 1) := by
            simpa only [heq] using hjoin n
          simpa only [heq] using hpiece.trans hj
        · have hselect : flatJoin x t f (n + 1) =ᶠ[𝓝 (t (n + 1))] f n := by
            filter_upwards [eventually_gt_nhds hlt] with s hs
            exact (Iic (t n)).piecewise_eq_of_notMem
              (flatJoin x t f n) (f n) (not_le.mpr hs)
          exact hselect.trans (hjoin n)
  exact fun n ↦ (hmain n).1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M]

noncomputable def chartFlatLift
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
    (p : M) (f : ℝ → E) (a b : ℝ) : ℝ → M :=
  (extChartAt I p).symm ∘ flatExtend f a b

theorem chartLift_continuous
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
    (p : M) (f : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous f)
    (htar : MapsTo f (Icc a b) (extChartAt I p).target) :
    Continuous (chartFlatLift I p f a b) := by
  rw [← continuousOn_univ]
  exact (continuousOn_extChartAt_symm p).comp
    (flatExtend_cont f hab hf).continuousOn
    (flatExtend_mapsTo f hab htar)

theorem chartLift_contMDiff
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    (p : M) (f : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hf : ContDiff ℝ 1 f)
    (ha : f =ᶠ[𝓝 a] fun _ ↦ f a) (hb : f =ᶠ[𝓝 b] fun _ ↦ f b)
    (htar : MapsTo f (Icc a b) (extChartAt I p).target) :
    ContMDiff 𝓘(ℝ, ℝ) I 1 (chartFlatLift I p f a b) := by
  rw [← contMDiffOn_univ]
  exact (contMDiffOn_extChartAt_symm (I := I) (n := 1) p).comp
    (flatExtend_contDiff f hab hf ha hb).contMDiff.contMDiffOn
    (flatExtend_mapsTo f hab htar)

theorem chartLift_coord
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
    (p : M) (f : ℝ → E) {a b : ℝ}
    (htar : MapsTo f (Icc a b) (extChartAt I p).target) :
    EqOn ((extChartAt I p) ∘ chartFlatLift I p f a b) f (Icc a b) := by
  intro s hs
  rw [Function.comp_apply, chartFlatLift, Function.comp_apply,
    flatExtend_of_mem f hs]
  exact (extChartAt I p).right_inv (htar hs)

theorem chartLift_left
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
    (p : M) (f : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (ha : f =ᶠ[𝓝 a] fun _ ↦ f a) :
    chartFlatLift I p f a b =ᶠ[𝓝 a]
      fun _ ↦ (extChartAt I p).symm (f a) := by
  exact (flatExtend_left f hab ha).fun_comp (extChartAt I p).symm

theorem chartLift_right
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
    (p : M) (f : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hb : f =ᶠ[𝓝 b] fun _ ↦ f b) :
    chartFlatLift I p f a b =ᶠ[𝓝 b]
      fun _ ↦ (extChartAt I p).symm (f b) := by
  exact (flatExtend_right f hab hb).fun_comp (extChartAt I p).symm

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry

end
