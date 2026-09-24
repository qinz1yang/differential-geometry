import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Regularity
import DifferentialGeometry.Analysis.Schauder.Holder.Multilinear
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import DifferentialGeometry.Analysis.Schauder.Holder.Localization
import DifferentialGeometry.Analysis.Schauder.Holder.HigherOrderComposition
import Mathlib.Analysis.Calculus.TangentCone.Real

noncomputable section
open Set
open scoped ContDiff NNReal

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_holderOnWith_clm_comp
    {X A B : Type*} [PseudoEMetricSpace X]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {s : Set X} {f : X → A}
    {K α : ℝ≥0} (hf : HolderOnWith K α f s) (L : A →L[ℝ] B) :
    ∃ C : ℝ≥0, HolderOnWith C α (fun x => L (f x)) s := by
  have hh := L.lipschitz.holderWith.comp_holderOnWith hf
  refine ⟨‖L‖₊ * K, ?_⟩
  simpa only [Function.comp_def, NNReal.coe_one, NNReal.rpow_one, one_mul] using hh

theorem exists_holderOnWith_iteratedFDeriv_add_two_of_basis
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ E)
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 2) f Ω) {α : ℝ≥0}
    (hH : ∀ v : Fin n → ι, ∃ K : ℝ≥0,
      HolderOnWith K α (iteratedFDeriv ℝ 2 (fun x =>
        iteratedFDeriv ℝ n f x (fun i => b (v i)))) Ω) :
    ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDeriv ℝ (n + 2) f) Ω := by
  apply Schauder.exists_holderOnWith_continuousMultilinearMap_of_basis b
  intro v
  let w : Fin n → ι := Fin.tail (Fin.tail v)
  obtain ⟨K, hK⟩ := hH w
  obtain ⟨C, hC⟩ := exists_holderOnWith_clm_comp hK
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) F ![b (v 0), b (v 1)])
  refine ⟨C, ?_⟩
  have heq (x : E) (hx : x ∈ Ω) :
      iteratedFDeriv ℝ 2 (fun x => iteratedFDeriv ℝ n f x (fun i => b (w i))) x
        ![b (v 0), b (v 1)] = iteratedFDeriv ℝ (n + 2) f x (fun i => b (v i)) := by
    rw [iteratedFDeriv_two_apply_const (hf.contDiffAt (hΩ.mem_nhds hx))]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
  intro x hx y hy
  have hh := hC x hx y hy
  change edist (iteratedFDeriv ℝ 2 _ x _) (iteratedFDeriv ℝ 2 _ y _) ≤ _ at hh
  rwa [heq x hx, heq y hy] at hh

end DifferentialGeometry.Analysis

end

noncomputable section
open Set
open scoped NNReal ENNReal ContDiff

namespace DifferentialGeometry.Analysis.Schauder

variable {X V ι : Type*} [PseudoEMetricSpace X] [Fintype ι]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
local notation "F" => EuclideanSpace ℝ ι

theorem exists_holderOnWith_piLp_of_components
    {s : Set X} {f : X → F} {α : ℝ≥0}
    (hf : ∀ i, ∃ K : ℝ≥0, HolderOnWith K α (fun x => f x i) s) :
    ∃ K : ℝ≥0, HolderOnWith K α f s := by
  classical
  choose K hK using hf
  have hp : HolderOnWith (∑ i, K i) α (fun x i => f x i) s := by
    intro x hx y hy
    apply edist_pi_le_iff.mpr
    intro i
    apply (hK i x hx y hy).trans
    gcongr
    exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  have hh := e.lipschitz.holderWith.comp_holderOnWith hp
  refine ⟨‖e.toContinuousLinearMap‖₊ * ∑ i, K i, ?_⟩
  intro x hx y hy
  have he (x : X) : e (fun i => f x i) = f x := rfl
  simpa only [Function.comp_def, he, NNReal.coe_one, NNReal.rpow_one, one_mul] using hh x hx y hy

theorem exists_holderOnWith_iteratedFDeriv_of_components
    {Ω : Set V} (hΩ : IsOpen Ω) {f : V → F} {n : ℕ}
    (hf : ContDiffOn ℝ n f Ω) {α : ℝ≥0}
    (hH : ∀ i, ∃ K : ℝ≥0,
      HolderOnWith K α (iteratedFDeriv ℝ n (fun x => f x i)) Ω) :
    ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDeriv ℝ n f) Ω := by
  classical
  let L (i : ι) : F →L[ℝ] ℝ := PiLp.proj 2 (fun _ : ι => ℝ) i
  let S (i : ι) : ℝ →L[ℝ] F :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (EuclideanSpace.single i 1))
  have hcomp (i : ι) (x : V) (hx : x ∈ Ω) :
      iteratedFDeriv ℝ n (fun x => f x i) x =
        (L i).compContinuousMultilinearMap (iteratedFDeriv ℝ n f x) :=
    (L i).iteratedFDeriv_comp_left (hf.contDiffAt (hΩ.mem_nhds hx)) le_rfl
  have heq (x : V) : (∑ i, (S i).compContinuousMultilinearMap
      ((L i).compContinuousMultilinearMap (iteratedFDeriv ℝ n f x))) = iteratedFDeriv ℝ n f x := by
    ext v k
    simp only [sum_apply, ContinuousLinearMap.compContinuousMultilinearMap_coe,
      Function.comp_apply, S, L, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      PiLp.proj_apply]
    simp [Pi.single_apply]
  have hterm (i : ι) : ∃ K : ℝ≥0,
      HolderOnWith K α (fun x => (S i).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fun x => f x i) x)) Ω := by
    obtain ⟨K, hK⟩ := hH i
    exact DifferentialGeometry.Analysis.exists_holderOnWith_clm_comp hK
      (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => V) ℝ F (S i))
  choose K hK using hterm
  refine ⟨∑ i, K i, ?_⟩
  have hh := holderWith_finset_sum Finset.univ (fun i _ => (hK i).holderWith)
  have hh' : HolderOnWith (∑ i, K i) α (fun x => ∑ i, (S i).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (fun x => f x i) x)) Ω :=
    HolderWith.restrict_iff.mp hh
  intro x hx y hy
  have he (x : V) (hx : x ∈ Ω) : (∑ i, (S i).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (fun x => f x i) x)) = iteratedFDeriv ℝ n f x := by
    simp only [hcomp _ x hx, heq]
  have ht := hh' x hx y hy
  change edist (∑ i, (S i).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (fun x => f x i) x))
    (∑ i, (S i).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (fun x => f x i) y)) ≤ _ at ht
  rwa [he x hx, he y hy] at ht

theorem exists_holderOnWith_iteratedFDeriv_clm_comp
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {Ω s : Set V} (hΩ : IsOpen Ω) (hs : s ⊆ Ω) {f : V → A} {n : ℕ}
    (hf : ContDiffOn ℝ n f Ω) {K α : ℝ≥0}
    (hH : HolderOnWith K α (iteratedFDeriv ℝ n f) s) (L : A →L[ℝ] B) :
    ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDeriv ℝ n (L ∘ f)) s := by
  obtain ⟨C, hC⟩ := DifferentialGeometry.Analysis.exists_holderOnWith_clm_comp hH
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => V) A B L)
  refine ⟨C, ?_⟩
  intro x hx y hy
  have he (x : V) (hx : x ∈ s) : iteratedFDeriv ℝ n (L ∘ f) x =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f x) :=
    L.iteratedFDeriv_comp_left (hf.contDiffAt (hΩ.mem_nhds (hs hx))) le_rfl
  rw [he x hx, he y hy]
  exact hC x hx y hy

end DifferentialGeometry.Analysis.Schauder

end

noncomputable section
open Set Filter Metric
open scoped Topology NNReal ContDiff

namespace DifferentialGeometry.Analysis.Schauder

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_holderOnWith_iteratedFDeriv_firstJet_comp_on_closedBall
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → F} {n : ℕ}
    (hu : ContDiffOn ℝ (n + 1) u Ω) {c : E} {R : ℝ} (hR : 0 < R)
    (hball : closedBall c R ⊆ Ω) {K α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1)
    (hjet : HolderOnWith K α (iteratedFDeriv ℝ (n + 1) u) (closedBall c R))
    {U : Set (E × F × (E →L[ℝ] F))} (hU : IsOpen U)
    (huU : MapsTo (fun x => (x, u x, fderiv ℝ u x)) (closedBall c R) U)
    {A : (E × F × (E →L[ℝ] F)) → G} (hA : ContDiffOn ℝ (n + 1) A U) :
    ∃ C : ℝ≥0, HolderOnWith C α
      (iteratedFDeriv ℝ n (fun x => A (x, u x, fderiv ℝ u x))) (closedBall c R) := by
  have hs : UniqueDiffOn ℝ (closedBall c R) :=
    uniqueDiffOn_convex (convex_closedBall c R)
      ⟨c, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds c hR)⟩
  have heD (x : E) (hx : x ∈ closedBall c R) :
      fderivWithin ℝ u (closedBall c R) x = fderiv ℝ u x :=
    (hu.contDiffAt (hΩ.mem_nhds (hball hx))).differentiableAt (by simp) |>.fderivWithin (hs x hx)
  have hJ : HolderOnWith K α (iteratedFDerivWithin ℝ (n + 1) u (closedBall c R))
      (closedBall c R) := by
    intro x hx y hy
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hs (hu.contDiffAt (hΩ.mem_nhds (hball hx))) hx,
      iteratedFDerivWithin_eq_iteratedFDeriv hs (hu.contDiffAt (hΩ.mem_nhds (hball hy))) hy]
    exact hjet x hx y hy
  have hf (x : E) (hx : x ∈ closedBall c R) :
      ContDiffAt ℝ n (fun x => A (x, u x, fderiv ℝ u x)) x := by
    have huc := hu.contDiffAt (hΩ.mem_nhds (hball hx))
    apply ((hA.of_le (by simp)).contDiffAt (hU.mem_nhds (huU hx))).comp x
    exact contDiffAt_id.prodMk ((huc.of_le (by simp)).prodMk
      (huc.fderiv_right (m := n) le_rfl))
  have heq : EqOn (fun x => A (x, u x, fderivWithin ℝ u (closedBall c R) x))
      (fun x => A (x, u x, fderiv ℝ u x)) (closedBall c R) := by
    intro x hx
    dsimp only
    rw [heD x hx]
  obtain ⟨C, hC⟩ := exists_holderOnWith_iteratedFDerivWithin_firstJet_comp
    (isCompact_closedBall c R) (convex_closedBall c R) hs (hu.mono hball) hα hα1 hJ hU
    (fun x hx => by dsimp only; rw [heD x hx]; exact huU hx) hA
  refine ⟨C, ?_⟩
  intro x hx y hy
  have ht := hC x hx y hy
  rw [iteratedFDerivWithin_congr heq hx, iteratedFDerivWithin_congr heq hy,
    iteratedFDerivWithin_eq_iteratedFDeriv hs (hf x hx) hx,
    iteratedFDerivWithin_eq_iteratedFDeriv hs (hf y hy) hy] at ht
  exact ht

end DifferentialGeometry.Analysis.Schauder

end
