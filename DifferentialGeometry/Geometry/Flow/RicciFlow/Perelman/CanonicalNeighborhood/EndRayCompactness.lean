import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EndRayFromSegment
import DifferentialGeometry.Analysis.Calculus.Compactness.Interval
import Mathlib.Topology.Order.IsLocallyClosed
import Mathlib.Topology.Algebra.Order.Field

open Filter Set
open scoped Topology

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private theorem tendsto_atTop_of_one_le_mul_sub_sq {ell : ℝ} (hell : 0 < ell)
    {f : ℝ → ℝ} (hf : ∀ s ∈ Ico 0 ell, 1 ≤ f s * (ell - s) ^ 2) :
    Tendsto f (𝓝[<] ell) atTop := by
  have hgap : Tendsto (fun s : ℝ => (ell - s) ^ 2) (𝓝[<] ell) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
        ((tendsto_const_nhds (x := ell)).sub
          (show Tendsto (fun s : ℝ => s) (𝓝[<] ell) (𝓝 ell) from nhdsWithin_le_nhds)).pow 2
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change 0 < (ell - s) ^ 2
      exact sq_pos_of_pos (sub_pos.mpr hs)
  apply tendsto_atTop_mono' _ _ hgap.inv_tendsto_nhdsGT_zero
  filter_upwards [Ico_mem_nhdsLT hell] with s hs
  change ((ell - s) ^ 2)⁻¹ ≤ f s
  rw [← one_div]
  exact (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hs.2))).mpr (hf s hs)

variable {W : Type*} [MetricSpace W]

private theorem exists_endRay_of_convergent_curves {ell : ℝ} (hell : 0 < ell)
    (beta : ℕ → ℝ → W)
    (hpoints : ∀ s ∈ Ico 0 ell, ∃ w : W, Tendsto (fun i => beta i s) atTop (𝓝 w))
    (hpair : ∀ s ∈ Ico 0 ell, ∀ t ∈ Ico 0 ell,
      Tendsto (fun i => dist (beta i s) (beta i t)) atTop (𝓝 |s - t|))
    (f : W → ℝ) (hf : Continuous f)
    (hlower : ∀ s ∈ Ico 0 ell, ∀ w : W,
      Tendsto (fun i => beta i s) atTop (𝓝 w) → 1 ≤ f w * (ell - s) ^ 2) :
    ∃ (E : UniformSpace.Completion W) (a : EndRay E),
      a.length = ell ∧
      (∀ s ∈ Ioc 0 ell, Tendsto (fun i => beta i (ell - s)) atTop (𝓝 (a.point s))) ∧
      (∀ s ∈ Ioc 0 ell, 1 ≤ f (a.point s) * s ^ 2) ∧
      (∀ x : W, (x : UniformSpace.Completion W) ≠ E) := by
  classical
  have hzero : (0 : ℝ) ∈ Ico 0 ell := ⟨le_rfl, hell⟩
  let gamma (s : ℝ) : W := if hs : s ∈ Ico 0 ell then
    (hpoints s hs).choose else (hpoints 0 hzero).choose
  have hgamma (s : ℝ) (hs : s ∈ Ico 0 ell) :
      Tendsto (fun i => beta i s) atTop (𝓝 (gamma s)) := by
    simpa only [gamma, dif_pos hs] using (hpoints s hs).choose_spec
  have hisom : Isometry (fun s : Ico 0 ell => gamma s) := by
    apply Isometry.of_dist_eq
    intro s t
    exact tendsto_nhds_unique ((hgamma s s.property).dist (hgamma t t.property))
      (hpair s s.property t t.property)
  have hblow : Tendsto (f ∘ gamma) (𝓝[<] ell) atTop :=
    tendsto_atTop_of_one_le_mul_sub_sq hell (fun s hs => hlower s hs (gamma s) (hgamma s hs))
  obtain ⟨E, a, ha, hagamma, hmissing⟩ := exists_endRay_of_isometry_Ico hell hisom hf hblow
  refine ⟨E, a, ha, ?_, ?_, hmissing⟩
  · intro s hs
    rw [hagamma]
    exact hgamma (ell - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  · intro s hs
    rw [hagamma]
    simpa only [sub_sub_cancel] using
      hlower (ell - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
        (gamma (ell - s)) (hgamma (ell - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩)


private theorem exists_endRay_subseq_of_equicontinuous {ell : ℝ} (hell : 0 < ell)
    (beta : ℕ → C(Ico 0 ell, W))
    (hequi : Equicontinuous (fun i => (beta i : Ico 0 ell → W)))
    (hcompact : ∀ s : Ico 0 ell, ∃ K : Set W, IsCompact K ∧ ∀ i, beta i s ∈ K)
    (hpair : ∀ s t : Ico 0 ell,
      Tendsto (fun i => dist (beta i s) (beta i t)) atTop (𝓝 |(s : ℝ) - t|))
    (f : W → ℝ) (hf : Continuous f)
    (hlower : ∀ (phi : ℕ → ℕ), StrictMono phi → ∀ (s : Ico 0 ell) (w : W),
      Tendsto (fun i => beta (phi i) s) atTop (𝓝 w) →
        1 ≤ f w * (ell - s) ^ 2) :
    ∃ (phi : ℕ → ℕ) (E : UniformSpace.Completion W) (a : EndRay E),
      StrictMono phi ∧ a.length = ell ∧
      (∀ s : Ico 0 ell,
        Tendsto (fun i => beta (phi i) s) atTop (𝓝 (a.point (ell - s)))) ∧
      (∀ s ∈ Ioc 0 ell, 1 ≤ f (a.point s) * s ^ 2) ∧
      (∀ x : W, (x : UniformSpace.Completion W) ≠ E) := by
  classical
  let : LocallyCompactSpace (Ico (0 : ℝ) ell) := isLocallyClosed_Ico.locallyCompactSpace
  obtain ⟨phi, gamma, hphi, hconv⟩ :=
    DifferentialGeometry.Analysis.arzela_ascoli_subseq_tendsto_locally_uniformly_of_pointwise_compact
      beta hequi hcompact
  have heval (s : Ico 0 ell) : Tendsto (fun i => beta (phi i) s) atTop (𝓝 (gamma s)) :=
    (hconv {s} isCompact_singleton).tendsto_at (mem_singleton s)
  let b (i : ℕ) (s : ℝ) : W := if hs : s ∈ Ico 0 ell then
    beta (phi i) ⟨s, hs⟩ else beta (phi i) ⟨0, le_rfl, hell⟩
  obtain ⟨E, a, ha, haconv, halower, hmissing⟩ := exists_endRay_of_convergent_curves hell b
    (fun s hs => ⟨gamma ⟨s, hs⟩, by simpa only [b, dif_pos hs] using heval ⟨s, hs⟩⟩)
    (fun s hs t ht => by
      simpa only [b, dif_pos hs, dif_pos ht, Function.comp_def] using
        (hpair ⟨s, hs⟩ ⟨t, ht⟩).comp hphi.tendsto_atTop)
    f hf (fun s hs w hw => hlower phi hphi ⟨s, hs⟩ w (by simpa only [b, dif_pos hs] using hw))
  refine ⟨phi, E, a, hphi, ha, ?_, halower, hmissing⟩
  intro s
  have hs : ell - (s : ℝ) ∈ Ioc 0 ell :=
    ⟨sub_pos.mpr s.property.2, sub_le_self _ s.property.1⟩
  simpa only [sub_sub_cancel, b, dif_pos s.property] using haconv (ell - (s : ℝ)) hs


theorem exists_endRay_subseq_of_scalar_distance_lower_bound {ell : ℝ} (hell : 0 < ell)
    (beta : ℕ → C(Ico 0 ell, W))
    (hequi : Equicontinuous (fun i => (beta i : Ico 0 ell → W)))
    (hcompact : ∀ s : Ico 0 ell, ∃ K : Set W, IsCompact K ∧ ∀ i, beta i s ∈ K)
    (hpair : ∀ s t : Ico 0 ell,
      Tendsto (fun i => dist (beta i s) (beta i t)) atTop (𝓝 |(s : ℝ) - t|))
    (f : W → ℝ) (hf : Continuous f) (q r : ℕ → Ico 0 ell → ℝ)
    (hq : ∀ s : Ico 0 ell,
      Tendsto (fun i => q i s - f (beta i s)) atTop (𝓝 0))
    (hr : ∀ s : Ico 0 ell, Tendsto (fun i => r i s) atTop (𝓝 (ell - s)))
    (hlower : ∀ s : Ico 0 ell, ∀ᶠ i in atTop, 1 ≤ q i s * r i s ^ 2) :
    ∃ (phi : ℕ → ℕ) (E : UniformSpace.Completion W) (a : EndRay E),
      StrictMono phi ∧ a.length = ell ∧
      (∀ s : Ico 0 ell,
        Tendsto (fun i => beta (phi i) s) atTop (𝓝 (a.point (ell - s)))) ∧
      (∀ s ∈ Ioc 0 ell, 1 ≤ f (a.point s) * s ^ 2) ∧
      (∀ x : W, (x : UniformSpace.Completion W) ≠ E) := by
  apply exists_endRay_subseq_of_equicontinuous hell beta hequi hcompact hpair f hf
  intro phi hphi s w hw
  have hscalar : Tendsto (fun i => q (phi i) s) atTop (𝓝 (f w)) := by
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using
      ((hq s).comp hphi.tendsto_atTop).add (hf.continuousAt.tendsto.comp hw)
  have hradius := (hr s).comp hphi.tendsto_atTop
  exact ge_of_tendsto (hscalar.mul (hradius.pow 2))
    (hphi.tendsto_atTop.eventually (hlower s))


open scoped NNReal in
theorem exists_endRay_subseq_of_eventually_lipschitzOnWith {ell : ℝ} (hell : 0 < ell)
    (beta : ℕ → ℝ → W)
    (hcompact : ∀ s ∈ Ico 0 ell, ∃ K : Set W, IsCompact K ∧
      ∀ᶠ i in atTop, beta i s ∈ K)
    (hLip : ∀ r ∈ Ioo 0 ell, ∃ L : ℝ≥0,
      ∀ᶠ i in atTop, LipschitzOnWith L (beta i) (Icc 0 r))
    (hpair : ∀ s ∈ Ico 0 ell, ∀ t ∈ Ico 0 ell,
      Tendsto (fun i => dist (beta i s) (beta i t)) atTop (𝓝 |s - t|))
    (f : W → ℝ) (hf : Continuous f)
    (hlower : ∀ (phi : ℕ → ℕ), StrictMono phi → ∀ s ∈ Ico 0 ell, ∀ w : W,
      Tendsto (fun i => beta (phi i) s) atTop (𝓝 w) →
        1 ≤ f w * (ell - s) ^ 2) :
    ∃ (phi : ℕ → ℕ) (E : UniformSpace.Completion W) (a : EndRay E),
      StrictMono phi ∧ a.length = ell ∧
      (∀ r : ℝ, r < ell → TendstoUniformlyOn
        (fun i (s : Ico 0 ell) => beta (phi i) s)
        (fun s : Ico 0 ell => a.point (ell - s)) atTop {s | (s : ℝ) ≤ r}) ∧
      (∀ s ∈ Ioc 0 ell, 1 ≤ f (a.point s) * s ^ 2) ∧
      (∀ x : W, (x : UniformSpace.Completion W) ≠ E) := by
  obtain ⟨phi, gamma, hphi, hconv⟩ :=
    DifferentialGeometry.Analysis.exists_subseq_tendsto_uniformlyOn_Ico_of_eventually_lipschitzOnWith
      hell beta hcompact hLip
  have heval (s : Ico 0 ell) :
      Tendsto (fun i => beta (phi i) s) atTop (𝓝 (gamma s)) :=
    (hconv s s.property.2).tendsto_at (show (s : ℝ) ≤ s from le_rfl)
  obtain ⟨E, a, ha, haconv, halower, hmissing⟩ :=
    exists_endRay_of_convergent_curves hell (fun i => beta (phi i))
      (fun s hs => ⟨gamma ⟨s, hs⟩, heval ⟨s, hs⟩⟩)
      (fun s hs t ht => (hpair s hs t ht).comp hphi.tendsto_atTop)
      f hf (hlower phi hphi)
  have hgamma : (gamma : Ico 0 ell → W) =
      fun s : Ico 0 ell => a.point (ell - s) := by
    funext s
    have hs : ell - (s : ℝ) ∈ Ioc 0 ell :=
      ⟨sub_pos.mpr s.property.2, sub_le_self _ s.property.1⟩
    apply tendsto_nhds_unique (heval s)
    simpa only [sub_sub_cancel] using haconv (ell - s) hs
  refine ⟨phi, E, a, hphi, ha, ?_, halower, hmissing⟩
  intro r hr
  rw [← hgamma]
  exact hconv r hr


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
