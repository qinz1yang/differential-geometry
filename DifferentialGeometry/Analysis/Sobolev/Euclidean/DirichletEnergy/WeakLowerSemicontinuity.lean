import DifferentialGeometry.Analysis.Integration.Lp.QuadraticLowerSemicontinuity
import DifferentialGeometry.Topology.Order.LiminfSum
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.SmoothTests
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Y" => Lp E 2 (volume.restrict Ω)

theorem gradLpOfWitness_eq_add_of_sub (hΩ : IsOpen Ω)
    {u b : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hb : DeGiorgi.MemW1pWitness 2 b Ω)
    (hd : DeGiorgi.MemW1pWitness 2 (fun x => u x - b x) Ω) :
    DeGiorgi.gradLpOfWitness hu = DeGiorgi.gradLpOfWitness hd +
      DeGiorgi.gradLpOfWitness hb := by
  have hcoord (i : Fin d) :
      (fun x => hu.weakGrad x i) =ᵐ[volume.restrict Ω]
        (fun x => hd.weakGrad x i + hb.weakGrad x i) := by
    apply DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ (hu.isWeakGrad i)
      (by simpa only [DeGiorgi.MemW1pWitness.add, PiLp.add_apply, sub_add_cancel] using
        (hd.add hb).isWeakGrad i)
      ((hu.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    exact (((hd.add hb).weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  apply Lp.ext
  filter_upwards [hu.weakGrad_memLp.coeFn_toLp,
    hd.weakGrad_memLp.coeFn_toLp, hb.weakGrad_memLp.coeFn_toLp,
    Lp.coeFn_add (DeGiorgi.gradLpOfWitness hd) (DeGiorgi.gradLpOfWitness hb),
    ae_all_iff.mpr hcoord] with x hux hdx hbx hadd hx
  rw [hadd]
  change hu.weakGrad_memLp.toLp hu.weakGrad x =
    hd.weakGrad_memLp.toLp hd.weakGrad x + hb.weakGrad_memLp.toLp hb.weakGrad x
  rw [hux, hdx, hbx]
  exact PiLp.ext hx

theorem norm_gradLpOfWitness_sq_le_liminf_of_weak_sub (hΩ : IsOpen Ω)
    {u : ℕ → E → ℝ} {v b : E → ℝ}
    (hu : ∀ n, DeGiorgi.MemW1pWitness 2 (u n) Ω)
    (hv : DeGiorgi.MemW1pWitness 2 v Ω)
    (hb : DeGiorgi.MemW1pWitness 2 b Ω)
    (hdu : ∀ n, DeGiorgi.MemW1pWitness 2 (fun x => u n x - b x) Ω)
    (hdv : DeGiorgi.MemW1pWitness 2 (fun x => v x - b x) Ω)
    (hweak : ∀ z : Y, Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hdu n)) z)
      atTop (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness hdv) z))) :
    ‖DeGiorgi.gradLpOfWitness hv‖ ^ 2 ≤
      liminf (fun n => ‖DeGiorgi.gradLpOfWitness (hu n)‖ ^ 2) atTop := by
  have hfull (z : Y) : Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hu n)) z)
      atTop (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness hv) z)) := by
    simp only [gradLpOfWitness_eq_add_of_sub hΩ (hu _) hb (hdu _),
      gradLpOfWitness_eq_add_of_sub hΩ hv hb hdv, inner_add_left]
    exact (hweak z).add_const _
  have hdual (F : Y →L[ℝ] ℝ) : Tendsto (fun n => F (DeGiorgi.gradLpOfWitness (hu n)))
      atTop (𝓝 (F (DeGiorgi.gradLpOfWitness hv))) := by
    have hF (w : Y) : F w = inner ℝ w ((_root_.InnerProductSpace.toDual ℝ Y).symm F) := by
      rw [real_inner_comm, _root_.InnerProductSpace.toDual_symm_apply]
    simpa only [hF] using hfull ((_root_.InnerProductSpace.toDual ℝ Y).symm F)
  let B : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have h := integral_quadratic_le_liminf_of_weak (μ := volume.restrict Ω)
    (fun _ _ => B) (fun _ => B)
    (fun _ _ _ => aestronglyMeasurable_const) (fun _ _ => aestronglyMeasurable_const)
    (fun _ => ‖B‖) ‖B‖ (fun _ => Eventually.of_forall fun _ => le_rfl)
    (Eventually.of_forall fun _ => le_rfl)
    (fun δ hδ => Eventually.of_forall fun _ => Eventually.of_forall fun _ => by
      change ‖B - B‖ ≤ δ
      have he : B - B = 0 := by
        ext x y
        change B x y - B x y = 0
        exact sub_self _
      rw [he]
      have hz : ‖(0 : E →L[ℝ] E →L[ℝ] ℝ)‖ = 0 := ContinuousLinearMap.opNorm_zero
      exact hz.le.trans hδ.le)
    (fun _ => Eventually.of_forall fun _ x => by
      change 0 ≤ inner ℝ x x
      exact real_inner_self_nonneg)
    (fun n => DeGiorgi.gradLpOfWitness (hu n)) (DeGiorgi.gradLpOfWitness hv) hdual
  have heq (w : Y) : (∫ x, B (w x) (w x) ∂volume.restrict Ω) = ‖w‖ ^ 2 := by
    change inner ℝ w w = ‖w‖ ^ 2
    exact real_inner_self_eq_norm_sq w
  simpa only [heq] using h

theorem norm_gradLpOfWitness_sq_eq_integral
    {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω) :
    ‖DeGiorgi.gradLpOfWitness hu‖ ^ 2 = ∫ x in Ω, ‖hu.weakGrad x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (DeGiorgi.gradLpOfWitness hu)]
  change (∫ x in Ω, inner ℝ (DeGiorgi.gradLpOfWitness hu x)
    (DeGiorgi.gradLpOfWitness hu x)) = _
  apply integral_congr_ae
  filter_upwards [hu.weakGrad_memLp.coeFn_toLp] with x hx
  change inner ℝ (hu.weakGrad_memLp.toLp hu.weakGrad x)
    (hu.weakGrad_memLp.toLp hu.weakGrad x) = _
  rw [hx, real_inner_self_eq_norm_sq]

theorem sum_norm_gradLpOfWitness_sq_le_liminf_of_weak_sub
    {ι : Type*} [Fintype ι] (hΩ : IsOpen Ω)
    {u : ℕ → E → EuclideanSpace ℝ ι} {v b : E → EuclideanSpace ℝ ι}
    (hu : ∀ i n, DeGiorgi.MemW1pWitness 2 (fun x => u n x i) Ω)
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω)
    (hb : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => b x i) Ω)
    (hdu : ∀ i n, DeGiorgi.MemW1pWitness 2 (fun x => u n x i - b x i) Ω)
    (hdv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i - b x i) Ω)
    {C : ℝ} (hbound : ∀ n, ∑ i, ‖DeGiorgi.gradLpOfWitness (hu i n)‖ ^ 2 ≤ C)
    (hweak : ∀ i (z : Y), Tendsto
      (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hdu i n)) z)
      atTop (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hdv i)) z))) :
    (∑ i, ‖DeGiorgi.gradLpOfWitness (hv i)‖ ^ 2) ≤
      liminf (fun n => ∑ i, ‖DeGiorgi.gradLpOfWitness (hu i n)‖ ^ 2) atTop := by
  classical
  let q (i : ι) (n : ℕ) := ‖DeGiorgi.gradLpOfWitness (hu i n)‖ ^ 2
  have hlo (i : ι) : IsBoundedUnder (· ≥ ·) atTop (q i) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ q i n
    exact Eventually.of_forall fun n => sq_nonneg _
  have hhi (i : ι) : IsBoundedUnder (· ≤ ·) atTop (q i) := by
    refine ⟨C, ?_⟩
    change ∀ᶠ n in atTop, q i n ≤ C
    exact Eventually.of_forall fun n =>
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖DeGiorgi.gradLpOfWitness (hu j n)‖)
        (Finset.mem_univ i)).trans (hbound n)
  have hlsc (i : ι) : ‖DeGiorgi.gradLpOfWitness (hv i)‖ ^ 2 ≤ liminf (q i) atTop :=
    norm_gradLpOfWitness_sq_le_liminf_of_weak_sub hΩ (hu i) (hv i) (hb i)
      (hdu i) (hdv i) (hweak i)
  have hsum := sum_liminf_le Finset.univ q (fun i _ => hlo i) (fun i _ => hhi i)
  have heq : (∑ i, q i) = (fun n => ∑ i, q i n) := by
    funext n
    exact Finset.sum_apply n Finset.univ q
  rw [heq] at hsum
  exact (Finset.sum_le_sum fun i _ => hlsc i).trans hsum

end DifferentialGeometry.Analysis.Sobolev.Euclidean
