import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakLaplacian.HolderRegularity
import DifferentialGeometry.Analysis.Schauder.Holder.IteratedDerivative

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff NNReal ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Schauder

variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem contDiffOn_of_semilinear_weak_laplacian
    {u : V → F} {c : V} {R : ℝ}
    (hu : ContDiffOn ℝ 2 u (ball c R)) {K α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hH : HolderOnWith K α (iteratedFDeriv ℝ 2 u) (ball c R))
    {U : Set (V × F × (V →L[ℝ] F))} (hU : IsOpen U)
    (huU : MapsTo (fun x => (x, u x, fderiv ℝ u x)) (ball c R) U)
    {A : (V × F × (V →L[ℝ] F)) → F} (hA : ContDiffOn ℝ ∞ A U)
    (hdiv : ∀ i, DeGiorgi.HasWeakDiv (fun x => A (x, u x, fderiv ℝ u x) i)
      (DeGiorgi.smoothGradField (fun x => u x i)) (ball c R)) :
    ContDiffOn ℝ ∞ u (ball c R) := by
  let f (x : V) := A (x, u x, fderiv ℝ u x)
  have hreg (n : ℕ) : ∀ r : ℝ, 0 < r → r < R →
      ContDiffOn ℝ (n + 2 : ℕ) u (ball c r) ∧
        ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDeriv ℝ (n + 2) u) (ball c r) := by
    intro r hr hrR
    induction n generalizing r with
    | zero =>
        exact ⟨hu.mono (ball_subset_ball hrR.le), K, hH.mono (ball_subset_ball hrR.le)⟩
    | succ n ih =>
        let s := (r + R) / 2
        have hrs : r < s := by dsimp only [s]; linarith
        have hsR : s < R := by dsimp only [s]; linarith
        have hs : 0 < s := hr.trans hrs
        obtain ⟨huS, Cu, hCu⟩ := ih s hs hsR
        let t := (r + s) / 2
        have hrt : r < t := by dsimp only [t]; linarith
        have hts : t < s := by dsimp only [t]; linarith
        have ht : 0 < t := hr.trans hrt
        have hclosed : closedBall c t ⊆ ball c s := closedBall_subset_ball hts
        have hsmall : ball c s ⊆ ball c R := ball_subset_ball hsR.le
        have huN : ContDiffOn ℝ ((n + 1 : ℕ) + 1) u (ball c s) := by
          convert huS using 1
          congr 1
        have hAfinite : ContDiffOn ℝ ((n + 1 : ℕ) + 1) A U :=
          hA.of_le (by exact_mod_cast (le_top : ((n + 1 + 1 : ℕ) : ℕ∞) ≤ ⊤))
        have hfN : ContDiffOn ℝ (n + 1 : ℕ) f (ball c s) := by
          apply (hAfinite.of_le (by simp)).comp _ (fun x hx => huU (hsmall hx))
          exact contDiffOn_id.prodMk ((huN.of_le (by simp)).prodMk
            (huN.fderiv_of_isOpen (m := (n + 1 : ℕ)) isOpen_ball le_rfl))
        have hCu' : HolderOnWith Cu α (iteratedFDeriv ℝ ((n + 1) + 1) u) (closedBall c t) := by
          exact hCu.mono hclosed
        obtain ⟨Cf, hCf⟩ := exists_holderOnWith_iteratedFDeriv_firstJet_comp_on_closedBall
          isOpen_ball huN ht hclosed hα hα1.le hCu' hU
          (fun x hx => huU (hsmall (hclosed hx))) hAfinite
        have hcomponent (i : ι) : ∃ C : ℝ≥0,
            ContDiffOn ℝ (n + 1 + 2 : ℕ) (fun x => u x i) (ball c r) ∧
            HolderOnWith C α (iteratedFDeriv ℝ (n + 1 + 2) (fun x => u x i)) (ball c r) := by
          let L : F →L[ℝ] ℝ := PiLp.proj 2 (fun _ : ι => ℝ) i
          have hui : ContDiffOn ℝ ((n + 1) + 1 : ℕ) (fun x => u x i) (ball c s) :=
            L.contDiff.comp_contDiffOn huN
          have hfi : ContDiffOn ℝ (n + 1 : ℕ) (fun x => f x i) (ball c s) :=
            L.contDiff.comp_contDiffOn hfN
          obtain ⟨Kui, hKui⟩ := exists_holderOnWith_iteratedFDeriv_clm_comp isOpen_ball
            hclosed huN hCu' L
          obtain ⟨Kfi, hKfi⟩ := exists_holderOnWith_iteratedFDeriv_clm_comp isOpen_ball
            hclosed hfN hCf L
          exact exists_holder_iteratedFDeriv_add_two_of_weak_laplacian isOpen_ball hui hfi
            ((hdiv i).restrict hsmall) hr hrt hclosed hα hα1 hKui hKfi
        choose C hC hHC using hcomponent
        have huNew : ContDiffOn ℝ (n + 1 + 2 : ℕ) u (ball c r) := contDiffOn_piLp' 2 hC
        exact ⟨huNew, exists_holderOnWith_iteratedFDeriv_of_components isOpen_ball huNew
          (fun i => ⟨C i, hHC i⟩)⟩
  rw [contDiffOn_infty]
  intro n x hx
  have hxR : dist x c < R := mem_ball.mp hx
  let r := (dist x c + R) / 2
  have hr : 0 < r := by dsimp only [r]; linarith [dist_nonneg (x := x) (y := c)]
  have hrR : r < R := by dsimp only [r]; linarith
  have hxr : x ∈ ball c r := mem_ball.mpr (by dsimp only [r]; linarith)
  exact (((hreg n r hr hrR).1.of_le (by exact_mod_cast (by omega : n ≤ n + 2))).contDiffAt
    (isOpen_ball.mem_nhds hxr)).contDiffWithinAt

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
