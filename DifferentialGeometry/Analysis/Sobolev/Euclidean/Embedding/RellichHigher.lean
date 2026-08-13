import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.External.DeGiorgi.SobolevSpace
import DifferentialGeometry.Analysis.Sobolev.Tools.Translation
import DifferentialGeometry.Analysis.Sobolev.Tools.FrechetKolmogorov
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Analytic.IteratedFDeriv

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

lemma chosenWeakPartial'_ae_eq_fderiv_of_smooth
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu_smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) u)
    (hu_supp : HasCompactSupport u) (hu_sub : tsupport u ⊆ Ω) (i : Fin d) :
    chosenWeakPartial' 2 i u Ω =ᵐ[volume.restrict Ω]
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))) := by
  classical
  have hu_inner : ContDiff ℝ (⊤ : ℕ∞) u :=
    hu_smooth.of_le (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  have hu_mem : DeGiorgi.MemW1p 2 u Ω :=
    (DeGiorgi.memW01p_of_contDiff_hasCompactSupport_subset hΩ hu_inner hu_supp hu_sub).memW1p
  have hw : DeGiorgi.HasWeakPartialDeriv i (chosenWeakPartial' 2 i u Ω) u Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_mem i
  have hf : DeGiorgi.HasWeakPartialDeriv i
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))) u Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff hΩ (hu_smooth.of_le (by norm_num))
  have hg₁ : LocallyIntegrable (chosenWeakPartial' 2 i u Ω) (volume.restrict Ω) :=
    (chosenWeakPartial'_memLp_of_mem hu_mem i).locallyIntegrable
      (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
  have hg₂ : LocallyIntegrable (fun x => (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ)))
      (volume.restrict Ω) := by
    have hs : ContDiff ℝ (⊤ : ℕ∞)
        (fun x => (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))) :=
      (hu_inner.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
    have hsupp : HasCompactSupport
        (fun x => (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))) :=
      hu_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))
    exact ((hs.continuous.memLp_of_hasCompactSupport hsupp).restrict Ω).locallyIntegrable
      (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ hw hf hg₁ hg₂

omit [NeZero d] in
lemma fderiv_iteratedFDeriv_apply_const
    {u : E → ℝ} (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (j : ℕ) (v : Fin j → E) (w : E) (x : E) :
    fderiv ℝ (fun y => (iteratedFDeriv ℝ j u y) v) x w =
      (fderiv ℝ (iteratedFDeriv ℝ j u) x) w v := by
  let A : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ →L[ℝ] ℝ :=
    { toFun := fun L => L v
      map_add' := by intro L M; rfl
      map_smul' := by intro c L; rfl }
  have hg : DifferentiableAt ℝ (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ => A L)
      (iteratedFDeriv ℝ j u x) :=
    A.hasFDerivAt.differentiableAt
  have hf : DifferentiableAt ℝ (iteratedFDeriv ℝ j u) x :=
    (hu_smooth.iteratedFDeriv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (i := j)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (by exact_mod_cast (le_top : (⊤ : ℕ∞) + (j : ℕ∞) ≤ (⊤ : ℕ∞)))).contDiffAt.differentiableAt
      (by decide : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have h : fderiv ℝ (fun y => A (iteratedFDeriv ℝ j u y)) x =
      A.comp (fderiv ℝ (iteratedFDeriv ℝ j u) x) := by
    change fderiv ℝ ((fun L : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ => A L) ∘
        iteratedFDeriv ℝ j u) x = A.comp (fderiv ℝ (iteratedFDeriv ℝ j u) x)
    rw [fderiv_comp x hg hf]
    congr 1
    exact A.hasFDerivAt.fderiv
  calc
    fderiv ℝ (fun y => (iteratedFDeriv ℝ j u y) v) x w
        = fderiv ℝ (fun y => A (iteratedFDeriv ℝ j u y)) x w := rfl
    _ = (A.comp (fderiv ℝ (iteratedFDeriv ℝ j u) x)) w := by rw [h]
    _ = A ((fderiv ℝ (iteratedFDeriv ℝ j u) x) w) := rfl
    _ = (fderiv ℝ (iteratedFDeriv ℝ j u) x) w v := rfl

omit [NeZero d] in
lemma iteratedFDeriv_succ_cons_apply
    {u : E → ℝ} (hu_smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) u)
    (j : ℕ) (α : Fin j → Fin d) (i : Fin d) :
    (fun x => (fderiv ℝ
        (fun y => (iteratedFDeriv ℝ j u y) (fun i' : Fin j => EuclideanSpace.single (α i')
          (1 : ℝ))) x)
          (EuclideanSpace.single i (1 : ℝ))) =
      fun x => (iteratedFDeriv ℝ (j + 1) u x)
        (Fin.cons (EuclideanSpace.single i (1 : ℝ))
          (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ))) := by
  funext x
  have hu_inner : ContDiff ℝ (⊤ : ℕ∞) u :=
    hu_smooth.of_le (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  calc
    (fderiv ℝ (fun y => (iteratedFDeriv ℝ j u y)
          (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ))) x)
          (EuclideanSpace.single i (1 : ℝ))
        = (fderiv ℝ (iteratedFDeriv ℝ j u) x) (EuclideanSpace.single i (1 : ℝ))
            (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ)) :=
          fderiv_iteratedFDeriv_apply_const hu_inner j
            (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ)) (EuclideanSpace.single i
              (1 : ℝ)) x
    _ = (iteratedFDeriv ℝ (j + 1) u x)
          (Fin.cons (EuclideanSpace.single i (1 : ℝ))
            (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ))) := by
      rw [iteratedFDeriv_succ_apply_left]
      rfl

omit [NeZero d] in
lemma iteratedFDeriv_fderiv_cons_eq
    {u : E → ℝ} (hu_smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) u)
    (j : ℕ) (α : Fin j → Fin d) (i : Fin d) :
    (fun x => (iteratedFDeriv ℝ j
        (fun y => (fderiv ℝ u y) (EuclideanSpace.single i (1 : ℝ))) x)
          (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ))) =
      fun x => (iteratedFDeriv ℝ (j + 1) u x)
        (Fin.cons (EuclideanSpace.single i (1 : ℝ))
          (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ))) := by
  induction j with
  | zero =>
      funext x
      simp [iteratedFDeriv_zero_apply]
  | succ j ih =>
      funext x
      have hu_inner : ContDiff ℝ (⊤ : ℕ∞) u :=
        hu_smooth.of_le (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
      have hIH := ih (fun i' : Fin j => α i'.succ)
      have hIH_fderiv :
          (fderiv ℝ (fun y => (iteratedFDeriv ℝ j
              (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ))) y)
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))) x)
              (EuclideanSpace.single (α 0) (1 : ℝ)) =
            (fderiv ℝ (fun y => (iteratedFDeriv ℝ (j + 1) u y)
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)))) x)
              (EuclideanSpace.single (α 0) (1 : ℝ)) := by
        congr 1
        exact congrArg (fun f : E → ℝ => fderiv ℝ f x) hIH
      have hLHS :
          (iteratedFDeriv ℝ (j + 1)
              (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ))) x)
                (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ)) =
            (fderiv ℝ (iteratedFDeriv ℝ j
              (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ)))) x
                (EuclideanSpace.single (α 0) (1 : ℝ)))
              (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)) := rfl
      have hw_smooth' : ContDiff ℝ (⊤ : ℕ∞)
          (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ))) :=
        (hu_inner.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
      have hclm_L :
          fderiv ℝ (fun y => (iteratedFDeriv ℝ j
              (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ))) y)
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))) x
              (EuclideanSpace.single (α 0) (1 : ℝ)) =
            (fderiv ℝ (iteratedFDeriv ℝ j
              (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ)))) x
                (EuclideanSpace.single (α 0) (1 : ℝ)))
              (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)) :=
          fderiv_iteratedFDeriv_apply_const hw_smooth'
            j (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))
            (EuclideanSpace.single (α 0) (1 : ℝ)) x
      have hclm_R :
          fderiv ℝ (fun y => (iteratedFDeriv ℝ (j + 1) u y)
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)))) x
              (EuclideanSpace.single (α 0) (1 : ℝ)) =
            (fderiv ℝ (iteratedFDeriv ℝ (j + 1) u) x
                (EuclideanSpace.single (α 0) (1 : ℝ)))
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))) :=
          fderiv_iteratedFDeriv_apply_const hu_inner (j + 1)
            (Fin.cons (EuclideanSpace.single i (1 : ℝ))
              (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)))
            (EuclideanSpace.single (α 0) (1 : ℝ)) x
      have hswap :
          (fderiv ℝ (iteratedFDeriv ℝ (j + 1) u) x
                (EuclideanSpace.single (α 0) (1 : ℝ)))
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))) =
            (fderiv ℝ (iteratedFDeriv ℝ (j + 1) u) x
                (EuclideanSpace.single i (1 : ℝ)))
              (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ)) := by
        let σ : Equiv.Perm (Fin (j + 2)) := Equiv.swap (0 : Fin (j + 2)) (1 : Fin (j + 2))
        have hperm := ContDiffAt.iteratedFDeriv_comp_perm (𝕜 := ℝ) (f := u)
          (show ContDiffAt ℝ (⊤ : WithTop ℕ∞) u x from hu_smooth.contDiffAt)
          (n := j + 2)
          (v := Fin.cons (EuclideanSpace.single (α 0) (1 : ℝ))
            (Fin.cons (EuclideanSpace.single i (1 : ℝ))
              (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)))) σ
        have hperm' :
            iteratedFDeriv ℝ (j + 2) u x
                (Fin.cons (EuclideanSpace.single (α 0) (1 : ℝ))
                  (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                    (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)))) =
              iteratedFDeriv ℝ (j + 2) u x
                (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                  (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ))) := by
          rw [← hperm]
          congr 1
          funext k
          cases k with
          | mk n hn =>
              cases n with
              | zero => simp [σ]
              | succ n =>
                  cases n with
                  | zero => simp [σ]
                  | succ n =>
                      have hk0 : (⟨n + 1 + 1, hn⟩ : Fin (j + 2)) ≠ 0 := by
                        intro h
                        have : n + 1 + 1 = 0 := congrArg Fin.val h
                        omega
                      have hk1 : (⟨n + 1 + 1, hn⟩ : Fin (j + 2)) ≠ 1 := by
                        intro h
                        have : n + 1 + 1 = 1 := congrArg Fin.val h
                        omega
                      simp [σ, Fin.cons, Equiv.swap_apply_of_ne_of_ne hk0 hk1]
        have hL : iteratedFDeriv ℝ (j + 2) u x
              (Fin.cons (EuclideanSpace.single (α 0) (1 : ℝ))
                (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                  (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)))) =
            (fderiv ℝ (iteratedFDeriv ℝ (j + 1) u) x
                (EuclideanSpace.single (α 0) (1 : ℝ)))
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))) := rfl
        have hR : iteratedFDeriv ℝ (j + 2) u x
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ))) =
            (fderiv ℝ (iteratedFDeriv ℝ (j + 1) u) x
                (EuclideanSpace.single i (1 : ℝ)))
              (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ)) := rfl
        exact (hL.symm.trans hperm').trans hR
      calc
        (iteratedFDeriv ℝ (j + 1)
            (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ))) x)
              (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ))
            = (fderiv ℝ (iteratedFDeriv ℝ j
                (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ)))) x
                  (EuclideanSpace.single (α 0) (1 : ℝ)))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)) := hLHS
        _ = fderiv ℝ (fun y => (iteratedFDeriv ℝ j
              (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ))) y)
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))) x
              (EuclideanSpace.single (α 0) (1 : ℝ)) := hclm_L.symm
        _ = fderiv ℝ (fun y => (iteratedFDeriv ℝ (j + 1) u y)
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)))) x
              (EuclideanSpace.single (α 0) (1 : ℝ)) := hIH_fderiv
        _ = (fderiv ℝ (iteratedFDeriv ℝ (j + 1) u) x
                (EuclideanSpace.single (α 0) (1 : ℝ)))
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))) := hclm_R
        _ = (fderiv ℝ (iteratedFDeriv ℝ (j + 1) u) x
                (EuclideanSpace.single i (1 : ℝ)))
              (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ)) := hswap
        _ = (iteratedFDeriv ℝ (j + 2) u x)
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ))) := rfl

lemma iterWeakPartial_ae_eq_iteratedFDeriv_of_smooth
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu_smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) u)
    (hu_supp : HasCompactSupport u) (hu_sub : tsupport u ⊆ Ω) :
    ∀ (j : ℕ) (α : Fin j → Fin d),
      iterWeakPartial (d := d) 2 j α u Ω =ᵐ[volume.restrict Ω]
        (fun x => (iteratedFDeriv ℝ j u x) (fun i : Fin j => EuclideanSpace.single (α i)
          (1 : ℝ))) := by
  intro j
  induction j generalizing u with
  | zero =>
      intro α
      simp [iterWeakPartial_zero, iteratedFDeriv_zero_apply]
  | succ j ih =>
      intro α
      rw [iterWeakPartial_succ]
      have hpart := chosenWeakPartial'_ae_eq_fderiv_of_smooth hΩ hu_smooth hu_supp hu_sub (α 0)
      have hw_smooth : ContDiff ℝ (⊤ : WithTop ℕ∞)
          (fun x => (fderiv ℝ u x) (EuclideanSpace.single (α 0) (1 : ℝ))) :=
        (hu_smooth.fderiv_right (m := (⊤ : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
      have hw_supp : HasCompactSupport
          (fun x => (fderiv ℝ u x) (EuclideanSpace.single (α 0) (1 : ℝ))) :=
        hu_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single (α 0) (1 : ℝ))
      have hw_sub : tsupport (fun x => (fderiv ℝ u x) (EuclideanSpace.single (α 0) (1 : ℝ))) ⊆ Ω :=
        (tsupport_fderiv_apply_subset (𝕜 := ℝ) (EuclideanSpace.single (α 0) (1 : ℝ))).trans hu_sub
      have hIH := ih (u := fun x => (fderiv ℝ u x) (EuclideanSpace.single (α 0) (1 : ℝ)))
        hw_smooth hw_supp hw_sub (fun i : Fin j => α i.succ)
      have htransport : iterWeakPartial (d := d) 2 j (fun i : Fin j => α i.succ)
            (chosenWeakPartial' 2 (α 0) u Ω) Ω =ᵐ[volume.restrict Ω]
          iterWeakPartial (d := d) 2 j (fun i : Fin j => α i.succ)
            (fun x => (fderiv ℝ u x) (EuclideanSpace.single (α 0) (1 : ℝ))) Ω :=
        iterWeakPartial_ae_congr (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ j
          (fun i : Fin j => α i.succ) hpart
      refine ae_eq_trans htransport ?_
      calc
        iterWeakPartial (d := d) 2 j (fun i : Fin j => α i.succ)
            (fun x => (fderiv ℝ u x) (EuclideanSpace.single (α 0) (1 : ℝ))) Ω
            =ᵐ[volume.restrict Ω]
          (fun x => (iteratedFDeriv ℝ j
            (fun y => (fderiv ℝ u y) (EuclideanSpace.single (α 0) (1 : ℝ))) x)
              (fun i : Fin j => EuclideanSpace.single (α i.succ) (1 : ℝ))) := hIH
        _ =ᵐ[volume.restrict Ω]
          (fun x => (iteratedFDeriv ℝ (j + 1) u x)
            (fun i : Fin (j + 1) => EuclideanSpace.single (α i) (1 : ℝ))) := by
          filter_upwards with x
          simpa [Fin.cons] using
            congrFun (iteratedFDeriv_fderiv_cons_eq hu_smooth j
              (fun i : Fin j => α i.succ) (α 0)) x

omit [NeZero d] in
lemma eLpNorm_iterWeakPartial_le_of_norm_le
    {Ω : Set E} {u : E → ℝ} {R : ℝ≥0∞} {k : ℕ}
    (hu : iteratedWeakSobolevNorm (d := d) (k + 1) 2 u Ω ≤ R)
    {j : ℕ} (hj : j ≤ k + 1) (α : Fin j → Fin d) :
    eLpNorm (iterWeakPartial (d := d) 2 j α u Ω) 2 (volume.restrict Ω) ≤ R := by
  classical
  have hmem_j : j ∈ Finset.range (k + 2) := by
    simp [Finset.mem_range]
    omega
  have h1 : eLpNorm (iterWeakPartial (d := d) 2 j α u Ω) 2 (volume.restrict Ω) ≤
      (∑ α' : Fin j → Fin d,
        eLpNorm (iterWeakPartial (d := d) 2 j α' u Ω) 2 (volume.restrict Ω) : ℝ≥0∞) :=
    Finset.single_le_sum
      (show ∀ x ∈ (Finset.univ : Finset (Fin j → Fin d)),
        (0 : ℝ≥0∞) ≤ eLpNorm (iterWeakPartial (d := d) 2 j x u Ω) 2 (volume.restrict Ω)
        from fun x _ => bot_le) (Finset.mem_univ α)
  have h2 : (∑ α' : Fin j → Fin d,
        eLpNorm (iterWeakPartial (d := d) 2 j α' u Ω) 2 (volume.restrict Ω) : ℝ≥0∞) ≤
      iteratedWeakSobolevNorm (d := d) (k + 1) 2 u Ω := by
    unfold iteratedWeakSobolevNorm
    exact Finset.single_le_sum
      (show ∀ x ∈ Finset.range (k + 2),
        (0 : ℝ≥0∞) ≤ (∑ α' : Fin x → Fin d,
          eLpNorm (iterWeakPartial (d := d) 2 x α' u Ω) 2 (volume.restrict Ω))
        from fun x _ => Finset.sum_nonneg (fun _ _ => bot_le)) hmem_j
  exact le_trans h1 (le_trans h2 hu)

omit [NeZero d] in
lemma exists_diagonal_extraction_lp
    {ι : Type*} [Finite ι] {Ω : Set E}
    {s : ι → ℕ → E → ℝ}
    (h : ∀ t : ι, ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ a : E → ℝ, MemLp a 2 (volume.restrict Ω) ∧
        Tendsto (fun n => eLpNorm (fun x => s t (ψ (σ n)) x - a x) 2
          (volume.restrict Ω)) atTop (𝓝 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ t : ι, ∃ a : E → ℝ, MemLp a 2 (volume.restrict Ω) ∧
        Tendsto (fun n => eLpNorm (fun x => s t (ψ n) x - a x) 2
          (volume.restrict Ω)) atTop (𝓝 0) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hmain : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ t ∈ (Finset.univ : Finset ι), ∃ a : E → ℝ, MemLp a 2 (volume.restrict Ω) ∧
        Tendsto (fun n => eLpNorm (fun x => s t (ψ n) x - a x) 2
          (volume.restrict Ω)) atTop (𝓝 0) := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty =>
        refine ⟨id, strictMono_id, ?_⟩
        intro t ht
        exact absurd ht (Finset.notMem_empty t)
    | insert t T' ht_notin ih =>
        rcases ih with ⟨ψ₀, hψ₀_mono, hP₀⟩
        rcases h t ψ₀ hψ₀_mono with ⟨σ, hσ_mono, a, ha_mem, ha⟩
        refine ⟨ψ₀ ∘ σ, hψ₀_mono.comp hσ_mono, ?_⟩
        intro t' ht'
        rcases Finset.mem_insert.mp ht' with rfl | ht'_T'
        · exact ⟨a, ha_mem, ha⟩
        · rcases hP₀ t' ht'_T' with ⟨a_t', ha_t'_mem, ha_t'⟩
          exact ⟨a_t', ha_t'_mem, ha_t'.comp (tendsto_atTop_atTop_of_monotone hσ_mono.monotone
            (fun n => ⟨n, hσ_mono.id_le n⟩))⟩
  rcases hmain with ⟨ψ, hψ_mono, hP⟩
  exact ⟨ψ, hψ_mono, fun t => hP t (Finset.mem_univ t)⟩

lemma eLpNorm_grad_eq_restrict
    {Ω : Set E} (hΩ_meas : MeasurableSet Ω)
    {φ : E → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_sub : tsupport φ ⊆ Ω)
    {p : ℝ≥0∞} (i : Fin d) :
    eLpNorm (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ))) p volume =
      eLpNorm (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ))) p
        (volume.restrict Ω) := by
  have hgrad_eq_indicator :
      (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ))) =
        Ω.indicator (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ))) := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · have hzero :=
        DeGiorgi.fderiv_apply_zero_outside_of_tsupport_subset
          (Ω := Ω) (hf := hφ_smooth) (hsub := hφ_sub) hx i
      simp [hx, hzero]
  conv_lhs => rw [hgrad_eq_indicator]
  exact MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
    (μ := volume) (s := Ω) (p := p)
    (f := fun x => (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ))) hΩ_meas

omit [NeZero d] in
lemma eLpNorm_phi_sub_indicator_eq
    {Ω : Set E} (hΩ_meas : MeasurableSet Ω)
    {φ u : E → ℝ}
    (hφ_sub : tsupport φ ⊆ Ω)
    {p : ℝ≥0∞} :
    eLpNorm (fun x => φ x - Ω.indicator u x) p volume =
      eLpNorm (fun x => φ x - u x) p (volume.restrict Ω) := by
  have hEq :
      (fun x => φ x - Ω.indicator u x) =
        Ω.indicator (fun x => φ x - u x) := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · have hφx : φ x = 0 :=
        DeGiorgi.zero_outside_of_tsupport_subset (Ω := Ω) hφ_sub hx
      simp [hx, hφx]
  conv_lhs => rw [hEq]
  exact MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
    (μ := volume) (s := Ω) (p := p) (f := fun x => φ x - u x) hΩ_meas

theorem rellich_kondrachov_W01p_seq_smooth
    {Ω : Set E} (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    {u : ℕ → E → ℝ}
    (hu_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u n))
    (hu_supp : ∀ n, HasCompactSupport (u n))
    (hu_supp_sub : ∀ n, tsupport (u n) ⊆ Ω)
    {R : ℝ}
    (hu_bdd_fun : ∀ n, eLpNorm (u n) 2 (volume.restrict Ω) ≤ ENNReal.ofReal R)
    (hu_bdd_grad : ∀ n,
      ∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ (u n) x) (EuclideanSpace.single i (1 : ℝ))) 2
          (volume.restrict Ω) ≤ ENNReal.ofReal R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ u_lim : E → ℝ, MemLp u_lim 2 (volume.restrict Ω) ∧
        Tendsto (fun k => eLpNorm (fun x => u (φ k) x - u_lim x) 2
          (volume.restrict Ω)) atTop (𝓝 0) := by
  classical
  set K : Set E := closure Ω with hK_def
  have hK_compact : IsCompact K := hΩ_bdd.isCompact_closure
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  set u_ext : ℕ → E → ℝ := fun n => Ω.indicator (u n) with hu_ext_def
  have hu_ext_supp : ∀ n, ∀ x, x ∉ K → u_ext n x = 0 := by
    intro n x hx
    rw [hu_ext_def]
    have hx0 : x ∉ Ω := by
      intro hxΩ
      exact hx (subset_closure hxΩ)
    simp [Set.indicator_of_notMem hx0]
  have hu_ext_memLp : ∀ n, MemLp (u_ext n) 2 volume := by
    intro n
    have hm : MemLp (u n) 2 (volume.restrict Ω) := by
      have hinner : ContDiff ℝ (⊤ : ℕ∞) (u n) := hu_smooth n
      exact (hinner.continuous.memLp_of_hasCompactSupport (hu_supp n)).restrict Ω
    exact (memLp_indicator_iff_restrict (μ := volume) (s := Ω) (f := u n) (p := 2) hΩ_meas).mpr hm
  have hu_ext_eLp : ∀ n,
      eLpNorm (u_ext n) 2 volume = eLpNorm (u n) 2 (volume.restrict Ω) := by
    intro n
    rw [hu_ext_def]
    exact MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict (μ := volume) (s := Ω)
      (f := u n) (p := 2) hΩ_meas
  have hu_ext_bdd : ∀ n, eLpNorm (u_ext n) 2 volume ≤ ENNReal.ofReal R := by
    intro n
    rw [hu_ext_eLp n]
    exact hu_bdd_fun n
  have hu_ext_translation :
      ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ h : E, ‖h‖ < δ →
        eLpNorm (fun x => u_ext n (x - h) - u_ext n x) 2 volume ≤
          ENNReal.ofReal ε := by
    intro ε hε
    refine ⟨ε / (max R 0 + 1), ?_, ?_⟩
    · exact div_pos hε (by have h := le_max_right R 0; linarith)
    intro n h hh
    have hpoint : (fun x => u_ext n (x - h) - u_ext n x) =
        (fun x => u n (x - h) - u n x) := by
      funext x
      rw [hu_ext_def]
      by_cases hx1 : x - h ∈ Ω
      · by_cases hx2 : x ∈ Ω
        · simp [hx1, hx2]
        · have hu0 : u n x = 0 :=
            DeGiorgi.zero_outside_of_tsupport_subset (hu_supp_sub n) hx2
          simp [hx1, hx2, hu0]
      · by_cases hx2 : x ∈ Ω
        · have hu0 : u n (x - h) = 0 :=
            DeGiorgi.zero_outside_of_tsupport_subset (hu_supp_sub n) hx1
          simp [hx1, hx2, hu0]
        · have hu0 : u n (x - h) = 0 :=
            DeGiorgi.zero_outside_of_tsupport_subset (hu_supp_sub n) hx1
          have hu1 : u n x = 0 :=
            DeGiorgi.zero_outside_of_tsupport_subset (hu_supp_sub n) hx2
          simp [hx1, hx2, hu0, hu1]
    have htrans := eLpNorm_translate_sub_le_sum_components (d := d) (p := 2)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hu_smooth n) h
    have hgrad : (∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ (u n) x) (EuclideanSpace.single i (1 : ℝ))) 2 volume) ≤
        ENNReal.ofReal R := by
      have hper : ∀ i : Fin d,
          eLpNorm (fun x => (fderiv ℝ (u n) x) (EuclideanSpace.single i (1 : ℝ))) 2 volume =
            eLpNorm (fun x => (fderiv ℝ (u n) x) (EuclideanSpace.single i (1 : ℝ))) 2
              (volume.restrict Ω) := fun i =>
        eLpNorm_grad_eq_restrict hΩ_meas (hu_smooth n) (hu_supp_sub n) i
      calc
        (∑ i : Fin d,
          eLpNorm (fun x => (fderiv ℝ (u n) x) (EuclideanSpace.single i (1 : ℝ))) 2 volume)
            = (∑ i : Fin d,
              eLpNorm (fun x => (fderiv ℝ (u n) x) (EuclideanSpace.single i (1 : ℝ))) 2
                (volume.restrict Ω)) := by
              exact Finset.sum_congr rfl (fun i _ => hper i)
        _ ≤ ENNReal.ofReal R := hu_bdd_grad n
    have hPhB' : eLpNorm (fun x => u_ext n (x - h) - u_ext n x) 2 volume ≤
        ENNReal.ofReal ‖h‖ * ENNReal.ofReal R := by
      rw [hpoint]
      exact htrans.trans (mul_le_mul_of_nonneg_left hgrad (zero_le _))
    have hR_le_max : (R : ℝ) ≤ max R 0 := le_max_left R 0
    have h2 : ENNReal.ofReal ‖h‖ * ENNReal.ofReal R ≤
        ENNReal.ofReal ‖h‖ * ENNReal.ofReal (max R 0) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hR_le_max)
    have hmaxR_nn : 0 ≤ max R 0 := le_max_right R 0
    have hdelta_pos : 0 < (max R 0 + 1) := by linarith
    have hh_le : ‖h‖ ≤ ε / (max R 0 + 1) := hh.le
    have hh_nn : 0 ≤ ‖h‖ := norm_nonneg _
    have h3 : ‖h‖ * max R 0 ≤ ε := by
      have h3a : ‖h‖ * max R 0 ≤ ‖h‖ * (max R 0 + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hh_nn
      have h3b : ‖h‖ * (max R 0 + 1) ≤ ε := by
        rw [show (ε : ℝ) = ε / (max R 0 + 1) * (max R 0 + 1) from
          (div_mul_cancel₀ ε hdelta_pos.ne').symm]
        exact mul_le_mul_of_nonneg_right hh_le (by linarith)
      linarith
    have h4 : ENNReal.ofReal ‖h‖ * ENNReal.ofReal (max R 0) ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_mul hh_nn]
      exact ENNReal.ofReal_le_ofReal h3
    exact hPhB'.trans (h2.trans h4)
  rcases tendsto_subseq_of_uniform_translation_in_Lp (d := d)
    (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    hK_compact hu_ext_memLp hu_ext_supp hu_ext_bdd hu_ext_translation with
    ⟨φ, hφ_mono, u_lim_v, hu_lim_v_memLp, h_tendsto_v⟩
  refine ⟨φ, hφ_mono, u_lim_v, hu_lim_v_memLp.restrict Ω, ?_⟩
  have hSqueeze : ∀ k,
      eLpNorm (fun x => u (φ k) x - u_lim_v x) 2 (volume.restrict Ω) ≤
        eLpNorm (fun x => u_ext (φ k) x - u_lim_v x) 2 volume := by
    intro k
    have h_cong : ∀ᵐ x ∂(volume.restrict Ω),
        u (φ k) x - u_lim_v x = u_ext (φ k) x - u_lim_v x := by
      filter_upwards [self_mem_ae_restrict hΩ_meas] with x hx
      simp [hu_ext_def, Set.indicator_of_mem hx]
    have h_eq : eLpNorm (fun x => u (φ k) x - u_lim_v x) 2 (volume.restrict Ω) =
        eLpNorm (fun x => u_ext (φ k) x - u_lim_v x) 2 (volume.restrict Ω) :=
      eLpNorm_congr_ae h_cong
    rw [h_eq]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  refine ENNReal.tendsto_atTop_zero.mpr ?_
  intro ε hε
  rcases (ENNReal.tendsto_atTop_zero.mp h_tendsto_v) ε hε with ⟨N, hN⟩
  refine ⟨N, fun k hk => ?_⟩
  exact (hSqueeze k).trans (hN k hk)


lemma smooth_extract_of_sequence
    {Ω : Set E} (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (v : ℕ → E → ℝ)
    (hv_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n))
    (hv_supp : ∀ n, HasCompactSupport (v n))
    (hv_sub : ∀ n, tsupport (v n) ⊆ Ω)
    {R : ℝ}
    (hv_fun : ∀ n, eLpNorm (v n) 2 (volume.restrict Ω) ≤ ENNReal.ofReal R)
    (hv_grad : ∀ n,
      (∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ (v n) x) (EuclideanSpace.single i (1 : ℝ))) 2
          (volume.restrict Ω)) ≤ ENNReal.ofReal R) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ w_lim : E → ℝ, MemLp w_lim 2 (volume.restrict Ω) ∧
        Tendsto (fun n => eLpNorm (fun x => v (σ n) x - w_lim x) 2
          (volume.restrict Ω)) atTop (𝓝 0) :=
  rellich_kondrachov_W01p_seq_smooth hΩ_open hΩ_bdd hv_smooth hv_supp hv_sub hv_fun hv_grad

theorem rellich_kondrachov_Wkp_seq_smooth
    {Ω : Set E} (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    {k : ℕ} {u : ℕ → E → ℝ}
    (hu_smooth : ∀ n, ContDiff ℝ (⊤ : WithTop ℕ∞) (u n))
    (hu_supp : ∀ n, HasCompactSupport (u n))
    (hu_supp_sub : ∀ n, tsupport (u n) ⊆ Ω)
    {R : ℝ} (hR : 0 ≤ R)
    (hu_bdd : ∀ n, iteratedWeakSobolevNorm (d := d) (k + 1) 2 (u n) Ω ≤ ENNReal.ofReal R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ (j : ℕ), j ≤ k → ∀ α : Fin j → Fin d,
        ∃ w_lim : E → ℝ, MemLp w_lim 2 (volume.restrict Ω) ∧
          Tendsto (fun n => eLpNorm
            (fun x => iterWeakPartial (d := d) 2 j α (u (φ n)) Ω x - w_lim x)
            2 (volume.restrict Ω)) atTop (𝓝 0) := by
  classical
  let s : (Σ j : Fin (k + 1), Fin j.1 → Fin d) → ℕ → E → ℝ := fun t n x =>
    (iteratedFDeriv ℝ t.1.1 (u n) x) (fun i : Fin t.1.1 => EuclideanSpace.single (t.2 i) (1 : ℝ))
  have hs_smooth : ∀ t n, ContDiff ℝ (⊤ : WithTop ℕ∞) (s t n) := by
    intro t n
    have hf : ContDiff ℝ (⊤ : WithTop ℕ∞) (iteratedFDeriv ℝ t.1.1 (u n)) :=
      (hu_smooth n).iteratedFDeriv_right (m := (⊤ : WithTop ℕ∞)) (i := t.1.1)
        (n := (⊤ : WithTop ℕ∞)) (by simp)
    let A : ContinuousMultilinearMap ℝ (fun _ : Fin t.1.1 => E) ℝ →L[ℝ] ℝ :=
      { toFun := fun L => L (fun i : Fin t.1.1 => EuclideanSpace.single (t.2 i) (1 : ℝ))
        map_add' := by intro L M; rfl
        map_smul' := by intro c L; rfl }
    exact A.contDiff.comp hf
  have hs_supp : ∀ t n, HasCompactSupport (s t n) := by
    intro t n
    have hf : HasCompactSupport (iteratedFDeriv ℝ t.1.1 (u n)) :=
      (hu_supp n).iteratedFDeriv t.1.1
    refine hf.of_isClosed_subset (isClosed_tsupport _) (closure_mono ?_)
    intro x hx
    by_contra hx0
    have hfx : (iteratedFDeriv ℝ t.1.1 (u n) x) = 0 := by
      by_contra hfx
      exact hx0 (by simp [Function.support, hfx])
    simp [s, hfx] at hx
  have hs_supp_sub : ∀ t n, tsupport (s t n) ⊆ Ω := by
    intro t n
    have hs : Function.support (s t n) ⊆ Function.support (iteratedFDeriv ℝ t.1.1 (u n)) := by
      intro x hx
      by_contra hx0
      have hfx : (iteratedFDeriv ℝ t.1.1 (u n) x) = 0 := by
        by_contra hfx
        exact hx0 (by simp [Function.support, hfx])
      simp [s, hfx] at hx
    exact (closure_mono hs).trans ((tsupport_iteratedFDeriv_subset (n := t.1.1)).trans
      (hu_supp_sub n))
  have hs_ae : ∀ t n,
      (iterWeakPartial (d := d) 2 t.1.1 t.2 (u n) Ω =ᵐ[volume.restrict Ω] s t n) := by
    intro t n
    exact iterWeakPartial_ae_eq_iteratedFDeriv_of_smooth hΩ_open (hu_smooth n)
      (hu_supp n) (hu_supp_sub n) t.1.1 t.2
  have hs_fun_bdd : ∀ t n,
      eLpNorm (s t n) 2 (volume.restrict Ω) ≤ ENNReal.ofReal R := by
    intro t n
    rw [show eLpNorm (s t n) 2 (volume.restrict Ω) =
        eLpNorm (iterWeakPartial (d := d) 2 t.1.1 t.2 (u n) Ω) 2 (volume.restrict Ω) from
      (eLpNorm_congr_ae (p := 2) (hs_ae t n)).symm]
    exact eLpNorm_iterWeakPartial_le_of_norm_le (hu_bdd n)
      (show (t.1.1 : ℕ) ≤ k + 1 from by omega) t.2
  have hs_grad_bdd : ∀ t n,
      (∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ (s t n) x) (EuclideanSpace.single i (1 : ℝ))) 2
          (volume.restrict Ω)) ≤ ENNReal.ofReal (R * (d : ℝ)) := by
    intro t n
    have hterm : ∀ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ (s t n) x) (EuclideanSpace.single i (1 : ℝ))) 2
            (volume.restrict Ω) ≤ ENNReal.ofReal R := by
      intro i
      have hid : (fun x => (fderiv ℝ (s t n) x) (EuclideanSpace.single i (1 : ℝ))) =
          fun x => (iteratedFDeriv ℝ (t.1.1 + 1) (u n) x)
            (Fin.cons (EuclideanSpace.single i (1 : ℝ))
              (fun i' : Fin t.1.1 => EuclideanSpace.single (t.2 i') (1 : ℝ))) := by
        change (fun x => (fderiv ℝ (fun y => (iteratedFDeriv ℝ t.1.1 (u n) y)
          (fun i' : Fin t.1.1 => EuclideanSpace.single (t.2 i') (1 : ℝ))) x)
            (EuclideanSpace.single i (1 : ℝ))) = _
        exact iteratedFDeriv_succ_cons_apply (hu_smooth n) t.1.1 t.2 i
      have hae' : iterWeakPartial (d := d) 2 (t.1.1 + 1) (Fin.cons i t.2)
        (u n) Ω =ᵐ[volume.restrict Ω]
          (fun x => (iteratedFDeriv ℝ (t.1.1 + 1) (u n) x)
            (Fin.cons (EuclideanSpace.single i (1 : ℝ))
              (fun i' : Fin t.1.1 => EuclideanSpace.single (t.2 i') (1 : ℝ)))) :=
        iterWeakPartial_ae_eq_iteratedFDeriv_of_smooth hΩ_open (hu_smooth n)
          (hu_supp n) (hu_supp_sub n) (t.1.1 + 1) (Fin.cons i t.2)
      calc
        eLpNorm (fun x => (fderiv ℝ (s t n) x) (EuclideanSpace.single i (1 : ℝ))) 2
            (volume.restrict Ω)
            = eLpNorm (iterWeakPartial (d := d) 2 (t.1.1 + 1) (Fin.cons i t.2) (u n) Ω) 2
                (volume.restrict Ω) := by
              refine (eLpNorm_congr_ae (p := 2) ?_).symm
              calc
                iterWeakPartial (d := d) 2 (t.1.1 + 1) (Fin.cons i t.2) (u n) Ω
                    =ᵐ[volume.restrict Ω] (fun x => (iteratedFDeriv ℝ (t.1.1 + 1) (u n) x)
                        (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                          (fun i' : Fin t.1.1 => EuclideanSpace.single (t.2 i') (1 : ℝ)))) := hae'
                _ =ᵐ[volume.restrict Ω] (fun x => (fderiv ℝ (s t n) x) (EuclideanSpace.single i
                  (1 : ℝ))) := by
                  rw [hid]
        _ ≤ ENNReal.ofReal R :=
          eLpNorm_iterWeakPartial_le_of_norm_le (hu_bdd n)
            (show (t.1.1 : ℕ) + 1 ≤ k + 1 from by omega) (Fin.cons i t.2)
    calc
      (∑ i : Fin d,
          eLpNorm (fun x => (fderiv ℝ (s t n) x) (EuclideanSpace.single i (1 : ℝ))) 2
            (volume.restrict Ω))
          ≤ ∑ i : Fin d, ENNReal.ofReal R := Finset.sum_le_sum (fun i _ => hterm i)
      _ = ENNReal.ofReal (R * (d : ℝ)) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        simp [ENNReal.ofReal_mul hR, mul_comm]
  let R1 : ℝ := R * (d : ℝ) + R
  have hRd_nonneg : 0 ≤ R * (d : ℝ) := mul_nonneg hR (Nat.cast_nonneg d)
  have hR1_nonneg : 0 ≤ R1 := by
    dsimp [R1]
    linarith
  have h_fun_le_R1 : ∀ t n, eLpNorm (s t n) 2 (volume.restrict Ω) ≤ ENNReal.ofReal R1 := by
    intro t n
    exact le_trans (hs_fun_bdd t n) (ENNReal.ofReal_le_ofReal (by
      dsimp [R1]
      linarith))
  have h_grad_le_R1 : ∀ t n,
      (∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ (s t n) x) (EuclideanSpace.single i (1 : ℝ))) 2
          (volume.restrict Ω)) ≤ ENNReal.ofReal R1 := by
    intro t n
    exact le_trans (hs_grad_bdd t n) (ENNReal.ofReal_le_ofReal (by
      dsimp [R1]
      linarith))
  have h_extract : ∀ t : (Σ j : Fin (k + 1), Fin j.1 → Fin d),
      ∀ ψ : ℕ → ℕ, StrictMono ψ →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          ∃ w_lim : E → ℝ, MemLp w_lim 2 (volume.restrict Ω) ∧
            Tendsto (fun n => eLpNorm (fun x => s t (ψ (σ n)) x - w_lim x) 2
              (volume.restrict Ω)) atTop (𝓝 0) := by
    intro t ψ hψ
    let v : ℕ → E → ℝ := fun m => s t (ψ m)
    have hv_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) := fun n => by
      change ContDiff ℝ (⊤ : ℕ∞) (s t (ψ n))
      exact (hs_smooth t (ψ n)).of_le (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
    have hv_supp : ∀ n, HasCompactSupport (v n) := fun n => by
      change HasCompactSupport (s t (ψ n))
      exact hs_supp t (ψ n)
    have hv_sub : ∀ n, tsupport (v n) ⊆ Ω := fun n => by
      change tsupport (s t (ψ n)) ⊆ Ω
      exact hs_supp_sub t (ψ n)
    have hv_fun : ∀ n, eLpNorm (v n) 2 (volume.restrict Ω) ≤ ENNReal.ofReal R1 := fun n => by
      change eLpNorm (s t (ψ n)) 2 (volume.restrict Ω) ≤ ENNReal.ofReal R1
      exact h_fun_le_R1 t (ψ n)
    have hv_grad : ∀ n,
        (∑ i : Fin d,
          eLpNorm (fun x => (fderiv ℝ (v n) x) (EuclideanSpace.single i (1 : ℝ))) 2
            (volume.restrict Ω)) ≤ ENNReal.ofReal R1 := fun n => by
      change (∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ (s t (ψ n)) x) (EuclideanSpace.single i (1 : ℝ))) 2
          (volume.restrict Ω)) ≤ ENNReal.ofReal R1
      exact h_grad_le_R1 t (ψ n)
    exact smooth_extract_of_sequence hΩ_open hΩ_bdd v hv_smooth hv_supp hv_sub hv_fun hv_grad
  obtain ⟨ψ, hψ_mono, hψ_conv⟩ := exists_diagonal_extraction_lp (Ω := Ω) (s := s) h_extract
  refine ⟨ψ, hψ_mono, ?_⟩
  intro j hj α
  let t : Σ j : Fin (k + 1), Fin j.1 → Fin d := ⟨⟨j, by omega⟩, α⟩
  rcases hψ_conv t with ⟨a, ha_mem, ha⟩
  refine ⟨a, ha_mem, ?_⟩
  refine (Filter.tendsto_congr (fun n => ?_)).mpr ha
  exact eLpNorm_congr_ae (by
    filter_upwards [hs_ae t (ψ n)] with x hx
    simp [s, t, hx])

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
