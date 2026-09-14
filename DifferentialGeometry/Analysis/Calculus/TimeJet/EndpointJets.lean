import DifferentialGeometry.Analysis.Calculus.TimeJet.Commutation
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace DifferentialGeometry.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem spatial_iteratedFDeriv_contDiffOn {G : ℝ → E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ V)) (k : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => iteratedFDeriv ℝ k (G p.1) p.2) (J ×ˢ V) := by
  induction k with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp_contDiffOn hG
  | succ k ih =>
    have hd := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun t x => iteratedFDeriv ℝ k (G t) x) hJ hV ih
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm.contDiff.comp_contDiffOn hd

private theorem time_derivWithin_contDiffOn {G : ℝ → E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ V)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => derivWithin (fun t => G t p.2) J p.1) (J ×ˢ V) := by
  have hfd : ContDiffOn ℝ ∞ (fderivWithin ℝ (Function.uncurry G) (J ×ˢ V)) (J ×ˢ V) :=
    hG.fderivWithin (hJ.prod hV.uniqueDiffOn) (by simp)
  have hd := hfd.clm_apply (contDiffOn_const (c := ((1, 0) : ℝ × E)))
  apply hd.congr
  intro p hp
  have hh : HasDerivWithinAt (fun t : ℝ => (t, p.2)) ((1, 0) : ℝ × E) J p.1 :=
    (hasDerivWithinAt_id p.1 J).prodMk (hasDerivWithinAt_const p.1 J p.2)
  have hm : MapsTo (fun t : ℝ => (t, p.2)) J (J ×ˢ V) := fun t ht => ⟨ht, hp.2⟩
  exact ((hG.differentiableOn (by simp) p hp).hasFDerivWithinAt.comp_hasDerivWithinAt
    p.1 hh hm).derivWithin (hJ p.1 hp.1)

theorem time_iteratedDerivWithin_contDiffOn {G : ℝ → E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ V)) (b : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => iteratedDerivWithin b (fun t => G t p.2) J p.1) (J ×ˢ V) := by
  induction b generalizing G with
  | zero => exact hG
  | succ b ih =>
    have hh := ih (G := fun t x => derivWithin (fun s => G s x) J t)
      (time_derivWithin_contDiffOn hJ hV hG)
    simpa only [iteratedDerivWithin_succ'] using hh

theorem mixed_endpoint_jets_contDiffOn {G : ℝ → E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ V)) (a b : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => iteratedDerivWithin b
        (fun t => iteratedFDeriv ℝ a (G t) p.2) J p.1) (J ×ˢ V) :=
  time_iteratedDerivWithin_contDiffOn (G := fun t x => iteratedFDeriv ℝ a (G t) x) hJ hV
    (spatial_iteratedFDeriv_contDiffOn hJ hV hG a) b

theorem exists_bound_spatial_iteratedFDeriv_on_compact
    {ι : Type*} [Finite ι] {G : ι → ℝ → E → F} {J : Set ℝ} {V K : ι → Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : ∀ i, IsOpen (V i)) (hJc : IsCompact J)
    (hK : ∀ i, IsCompact (K i))
    (hKV : ∀ i, K i ⊆ V i)
    (hG : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (G i)) (J ×ˢ V i)) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i t, t ∈ J → ∀ x ∈ K i, ‖iteratedFDeriv ℝ k (G i t) x‖ ≤ C := by
  let f := fun i (p : ℝ × E) => iteratedFDeriv ℝ k (G i p.1) p.2
  have hc (i : ι) : ContinuousOn (f i) (J ×ˢ K i) :=
    (spatial_iteratedFDeriv_contDiffOn hJ (hV i) (hG i) k).continuousOn.mono (prod_mono_right (hKV i))
  have hcompact : IsCompact (⋃ i, f i '' (J ×ˢ K i)) :=
    isCompact_iUnion (fun i => (hJc.prod (hK i)).image_of_continuousOn (hc i))
  obtain ⟨C, hC, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun i t ht x hx => hbound _ (mem_iUnion.mpr ⟨i, ⟨(t, x), ⟨ht, hx⟩, rfl⟩⟩)⟩

end DifferentialGeometry.Analysis
