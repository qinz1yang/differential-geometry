import DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.MeasureTheory.Integral.Bochner.Set
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Locality
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ContDiff

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem HasWeakPartialDeriv.indicator_of_cutoff
    {j : Fin d} {f g χ : E → ℝ} {Ω : Set E}
    (hf : HasWeakPartialDeriv j g f Ω) (hΩ : MeasurableSet Ω)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχone : ∀ᵐ x ∂volume.restrict Ω,
      (f x ≠ 0 ∨ g x ≠ 0) → χ =ᶠ[𝓝 x] (fun _ => 1)) :
    HasWeakPartialDeriv j (Ω.indicator g) (Ω.indicator f) univ := by
  classical
  intro φ hφ hφc _
  let ψ : E → ℝ := fun x => χ x * φ x
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hχ.mul hφ
  have hψc : HasCompactSupport ψ := hφc.mul_left
  have hψΩ : tsupport ψ ⊆ Ω := tsupport_mul_subset_left.trans hχΩ
  have hlocal := hf ψ hψ hψc hψΩ
  have hleft :
      (fun x => f x * fderiv ℝ ψ x (EuclideanSpace.single j 1)) =ᵐ[volume.restrict Ω]
        (fun x => f x * fderiv ℝ φ x (EuclideanSpace.single j 1)) := by
    filter_upwards [hχone] with x hx
    by_cases hfx : f x = 0
    · simp only [hfx, zero_mul]
    · have hnear : ψ =ᶠ[𝓝 x] φ := by
        filter_upwards [hx (Or.inl hfx)] with y hy
        simp only [ψ, hy, one_mul]
      rw [hnear.fderiv_eq]
  have hright : (fun x => g x * ψ x) =ᵐ[volume.restrict Ω]
      (fun x => g x * φ x) := by
    filter_upwards [hχone] with x hx
    by_cases hgx : g x = 0
    · simp only [hgx, zero_mul]
    · have hχx : χ x = 1 := (hx (Or.inr hgx)).eq_of_nhds
      simp only [ψ, hχx, one_mul]
  rw [integral_congr_ae hleft, integral_congr_ae hright] at hlocal
  simp only [Measure.restrict_univ]
  calc
    (∫ x, Ω.indicator f x * fderiv ℝ φ x (EuclideanSpace.single j 1)) =
        ∫ x, Ω.indicator (fun y => f y * fderiv ℝ φ y (EuclideanSpace.single j 1)) x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        (Set.indicator_mul_left Ω f (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1))).symm
    _ = ∫ x in Ω, f x * fderiv ℝ φ x (EuclideanSpace.single j 1) := integral_indicator hΩ
    _ = -∫ x in Ω, g x * φ x := hlocal
    _ = -∫ x, Ω.indicator (fun y => g y * φ y) x := by rw [integral_indicator hΩ]
    _ = -∫ x, Ω.indicator g x * φ x := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => Set.indicator_mul_left Ω g φ

theorem HasWeakPartialDeriv.indicator_of_cutoff_of_ae_zero_off
    {j : Fin d} {f g χ : E → ℝ} {Ω K : Set E}
    (hf : HasWeakPartialDeriv j g f Ω) (hΩ : MeasurableSet Ω)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχΩ : tsupport χ ⊆ Ω)
    (hzero : ∀ᵐ x ∂volume.restrict Ω, x ∉ K → f x = 0 ∧ g x = 0)
    (hχone : ∀ x ∈ K, χ =ᶠ[𝓝 x] (fun _ => 1)) :
    HasWeakPartialDeriv j (Ω.indicator g) (Ω.indicator f) univ := by
  apply hf.indicator_of_cutoff hΩ hχ hχΩ
  filter_upwards [hzero] with x hx
  intro hfg
  have hxK : x ∈ K := by
    by_contra hxK
    obtain ⟨hfx, hgx⟩ := hx hxK
    exact hfg.elim (fun h => h hfx) (fun h => h hgx)
  exact hχone x hxK

end DeGiorgi

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace DeGiorgi

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

private def MemW1pWitness.indicatorOfCutoff
    {p : ℝ≥0∞} {Ω : Set V} (hΩ : IsOpen Ω)
    {f χ : V → ℝ} (hf : MemW1pWitness p f Ω)
    (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Ω)
    (hcut : ∀ᵐ x ∂volume.restrict Ω,
      (f x ≠ 0 ∨ hf.weakGrad x ≠ 0) → χ =ᶠ[𝓝 x] 1) :
    MemW1pWitness p (Ω.indicator f) univ where
  memLp := by
    simpa only [Measure.restrict_univ] using
      (memLp_indicator_iff_restrict hΩ.measurableSet).mpr hf.memLp
  weakGrad := Ω.indicator hf.weakGrad
  weakGrad_component_memLp := by
    intro j
    have h := (memLp_indicator_iff_restrict hΩ.measurableSet).mpr
      (hf.weakGrad_component_memLp j)
    have heq : (fun x => (Ω.indicator hf.weakGrad x) j) =
        Ω.indicator (fun x => hf.weakGrad x j) := by
      funext x
      by_cases hx : x ∈ Ω <;> simp [hx]
    simpa only [Measure.restrict_univ, heq] using h
  isWeakGrad := by
    intro j
    have hcutj : ∀ᵐ x ∂volume.restrict Ω,
        (f x ≠ 0 ∨ hf.weakGrad x j ≠ 0) → χ =ᶠ[𝓝 x] 1 := by
      filter_upwards [hcut] with x hx
      intro hn
      apply hx
      rcases hn with hf | hg
      · exact Or.inl hf
      · right
        intro hz
        exact hg (by rw [hz]; rfl)
    have heq : (fun x => (Ω.indicator hf.weakGrad x) j) =
        Ω.indicator (fun x => hf.weakGrad x j) := by
      funext x
      by_cases hx : x ∈ Ω <;> simp [hx]
    rw [heq]
    exact HasWeakPartialDeriv.indicator_of_cutoff (hf.isWeakGrad j) hΩ.measurableSet hχ hsupp hcutj

end DeGiorgi

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*}
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_weak_extension_of_eq_on_collar
    {Ω : Set V} (hΩ : IsOpen Ω) {b : V} {a c : ℝ}
    (ha : 0 ≤ a) (hac : a < c) (hball : Metric.ball b c ⊆ Ω)
    {w q : V → F}
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) Ω)
    (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (Metric.ball b c))
    (hqw : q =ᵐ[volume.restrict (Metric.ball b c \ Metric.closedBall b a)] w) :
    ∃ (v : V → F), Nonempty (∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω) ∧
      (v =ᵐ[volume.restrict (Metric.ball b c)] q) ∧
      (v =ᵐ[volume.restrict (Ω \ Metric.closedBall b a)] w) := by
  classical
  let B := Metric.ball b c
  let hwB (i : ι) := DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hball (hw i)
  let hd (i : ι) := (hq i).add ((hwB i).smul (-1))
  have hgrad (i : ι) := DeGiorgi.MemW1pWitness.weakGrad_ae_eq_of_ae_eq
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (Metric.isOpen_ball.sdiff Metric.isClosed_closedBall) sdiff_subset (hq i) (hwB i)
    (hqw.mono fun x hx => congrArg (fun z : F => z i) hx)
  have hrestr : (volume.restrict B).restrict (Metric.closedBall b a)ᶜ =
      volume.restrict (B \ Metric.closedBall b a) := by
    rw [Measure.restrict_restrict Metric.isClosed_closedBall.measurableSet.compl]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff, and_comm]
  let a' := (2 * a + c) / 3
  let c' := (a + 2 * c) / 3
  have haa' : a < a' := by dsimp only [a']; linarith
  have ha'c' : a' < c' := by dsimp only [a', c']; linarith
  have hc'c : c' < c := by dsimp only [c']; linarith
  let χ : ContDiffBump b := ⟨a', c', ha.trans_lt haa', ha'c'⟩
  have hχsupp : tsupport (χ : V → ℝ) ⊆ B := by
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball hc'c
  have hcut (i : ι) : ∀ᵐ x ∂volume.restrict B,
      ((fun x => q x i + -1 * w x i) x ≠ 0 ∨ (hd i).weakGrad x ≠ 0) →
      (χ : V → ℝ) =ᶠ[𝓝 x] 1 := by
    have heq : ∀ᵐ x ∂volume.restrict B, x ∉ Metric.closedBall b a → q x = w x := by
      exact (ae_restrict_iff' Metric.isClosed_closedBall.measurableSet.compl).mp
        (by rw [hrestr]; exact hqw)
    have hgeq : ∀ᵐ x ∂volume.restrict B, x ∉ Metric.closedBall b a →
        (hq i).weakGrad x = (hwB i).weakGrad x := by
      exact (ae_restrict_iff' Metric.isClosed_closedBall.measurableSet.compl).mp
        (by rw [hrestr]; exact hgrad i)
    filter_upwards [heq, hgeq] with x hx hg
    intro hn
    by_cases hxa : x ∈ Metric.closedBall b a
    · exact χ.eventuallyEq_one_of_mem_ball (Metric.closedBall_subset_ball haa' hxa)
    · exfalso
      have hz : (hd i).weakGrad x = 0 := by
        change (hq i).weakGrad x + -1 • (hwB i).weakGrad x = 0
        rw [hg hxa]
        simp
      exact hn.elim (fun h => h (by rw [hx hxa]; ring)) (fun h => h hz)
  let hz (i : ι) := DeGiorgi.MemW1pWitness.indicatorOfCutoff Metric.isOpen_ball
    (hd i) χ.contDiff hχsupp (hcut i)
  let v : V → F := fun x => WithLp.toLp 2 fun i =>
    w x i + B.indicator (fun y => q y i + -1 * w y i) x
  let hv (i : ι) : DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω :=
    (hw i).add (DeGiorgi.MemW1pWitness.restrict hΩ (subset_univ _) (hz i))
  refine ⟨v, ⟨hv⟩, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    ext i
    change w x i + B.indicator (fun y => q y i + -1 * w y i) x = q x i
    rw [indicator_of_mem (show x ∈ B from hx)]
    ring
  · have heq : ∀ᵐ x ∂volume, x ∈ B \ Metric.closedBall b a → q x = w x :=
      (ae_restrict_iff' (Metric.isOpen_ball.measurableSet.diff
        Metric.isClosed_closedBall.measurableSet)).mp hqw
    filter_upwards [ae_restrict_of_ae heq,
      ae_restrict_mem (hΩ.measurableSet.diff Metric.isClosed_closedBall.measurableSet)]
      with x hx hxΩ
    ext i
    by_cases hxB : x ∈ B
    · have hxq := hx ⟨hxB, hxΩ.2⟩
      simp only [v, indicator_of_mem hxB, hxq]
      ring
    · simp only [v, indicator_of_notMem hxB, add_zero]

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
