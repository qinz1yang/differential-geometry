import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
import DifferentialGeometry.Analysis.Calculus.Inverse.ImplicitDerivativeBounds

set_option autoImplicit false

/-!
# CH12-CX3: quantitative stability of finite jets under composition

The constants below are independent of the maps whose jets are being compared.
The difference estimate retains the small parameter, including in order zero.
-/

noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology BigOperators

namespace GC.LongTime.Ch12

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A finite combinatorial bound for the difference of composed jets. -/
def jetCompConstant_CX3 (n : ℕ) (B : ℝ) : ℝ :=
  ∑ c : OrderedFinpartition n,
    (B * c.length * B ^ (c.length - 1) + B * B ^ c.length)

theorem jetCompConstant_nonneg_CX3 (n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ jetCompConstant_CX3 n B := by
  unfold jetCompConstant_CX3
  positivity

/-- Quantitative Faà di Bruno, for two finite jets.  No higher derivatives of the
inner maps occur in the hypotheses. -/
theorem norm_taylorComp_sub_le_CX3
    (p₁ p₂ : FormalMultilinearSeries ℝ F G)
    (q₁ q₂ : FormalMultilinearSeries ℝ E F)
    (n : ℕ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hp : ∀ j ≤ n, ‖p₁ j‖ ≤ B)
    (hpδ : ∀ j ≤ n, ‖p₁ j - p₂ j‖ ≤ B * ε)
    (hq₁ : ∀ j, 1 ≤ j → j ≤ n → ‖q₁ j‖ ≤ B)
    (hq₂ : ∀ j, 1 ≤ j → j ≤ n → ‖q₂ j‖ ≤ B)
    (hqδ : ∀ j, 1 ≤ j → j ≤ n → ‖q₁ j - q₂ j‖ ≤ ε) :
    ‖p₁.taylorComp q₁ n - p₂.taylorComp q₂ n‖ ≤ jetCompConstant_CX3 n B * ε := by
  classical
  simp only [FormalMultilinearSeries.taylorComp, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [jetCompConstant_CX3, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c _
  let a₁ : ∀ i : Fin c.length, E [×c.partSize i]→L[ℝ] F := fun i => q₁ (c.partSize i)
  let a₂ : ∀ i : Fin c.length, E [×c.partSize i]→L[ℝ] F := fun i => q₂ (c.partSize i)
  have ha₁ : ‖a₁‖ ≤ B := (pi_norm_le_iff_of_nonneg hB).mpr
    (fun i => hq₁ _ (c.partSize_pos i) (c.partSize_le i))
  have ha₂ : ‖a₂‖ ≤ B := (pi_norm_le_iff_of_nonneg hB).mpr
    (fun i => hq₂ _ (c.partSize_pos i) (c.partSize_le i))
  have haδ : ‖a₁ - a₂‖ ≤ ε := (pi_norm_le_iff_of_nonneg hε).mpr
    (fun i => hqδ _ (c.partSize_pos i) (c.partSize_le i))
  have hprod : (∏ i, ‖a₂ i‖) ≤ B ^ c.length := by
    calc
      _ ≤ ∏ _i : Fin c.length, B := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => hq₂ _ (c.partSize_pos i) (c.partSize_le i))
      _ = _ := by simp
  change ‖c.compAlongOrderedFinpartition (p₁ c.length) a₁ -
      c.compAlongOrderedFinpartition (p₂ c.length) a₂‖ ≤ _
  refine (c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le _ _ _ _).trans ?_
  calc
    _ ≤ B * c.length * B ^ (c.length - 1) * ε + (B * ε) * B ^ c.length := by
      gcongr
      · exact hp _ c.length_le
      · exact max_le ha₁ ha₂
      · exact hpδ _ c.length_le
    _ = _ := by ring

/-- The same estimate for actual derivatives at a point. -/
theorem norm_iteratedFDeriv_comp_sub_le_CX3
    {f : F → G} {u v : E → F} {x : E} (n : ℕ)
    (hf₁ : ContDiffAt ℝ n f (u x)) (hf₂ : ContDiffAt ℝ n f (v x))
    (hu : ContDiffAt ℝ n u x) (hv : ContDiffAt ℝ n v x)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hp : ∀ j ≤ n, ‖iteratedFDeriv ℝ j f (u x)‖ ≤ B)
    (hpδ : ∀ j ≤ n,
      ‖iteratedFDeriv ℝ j f (u x) - iteratedFDeriv ℝ j f (v x)‖ ≤ B * ε)
    (huB : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j u x‖ ≤ B)
    (hvB : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j v x‖ ≤ B)
    (hδ : ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j u x - iteratedFDeriv ℝ j v x‖ ≤ ε) :
    ‖iteratedFDeriv ℝ n (f ∘ u) x - iteratedFDeriv ℝ n (f ∘ v) x‖ ≤
      jetCompConstant_CX3 n B * ε := by
  rw [iteratedFDeriv_comp hf₁ hu le_rfl, iteratedFDeriv_comp hf₂ hv le_rfl]
  exact norm_taylorComp_sub_le_CX3 _ _ _ _ n hB hε hp hpδ huB hvB hδ

/-- Uniform bounds for finitely many derivatives on a compact subset of an open domain. -/
theorem exists_compact_jet_bound_CX3 {f : E → F} {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j ≤ k, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
  classical
  have hbound : ∀ j : ℕ, ∃ B : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
    intro j
    obtain ⟨B, hB⟩ := hK.bddAbove_image
      ((ContinuousOn.continuousOn_iteratedFDeriv hf hU (by exact_mod_cast le_top)).norm.mono hKU)
    exact ⟨B, fun x hx => hB ⟨x, hx, rfl⟩⟩
  choose B hB using hbound
  refine ⟨max 1 ((Finset.range (k + 1)).sup' ⟨0, by simp⟩ B), le_max_left _ _, ?_⟩
  intro j hj x hx
  exact (hB j x hx).trans ((Finset.le_sup' B (by simpa using hj)).trans (le_max_right _ _))

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A compact part of the zero section admits a uniform vertical tube. -/
theorem exists_graph_tube_CX3 {K : Set E} {N : Set (E × F)}
    (hK : IsCompact K) (hN : IsOpen N) (h0 : ∀ x ∈ K, (x, (0 : F)) ∈ N) :
    ∃ r : ℝ, 0 < r ∧ K ×ˢ closedBall (0 : F) r ⊆ N := by
  obtain ⟨u, v, _, hv, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hK isCompact_singleton hN (by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      have hy0 : y = 0 := hy
      subst y
      exact h0 x hx)
  obtain ⟨r, hr, hrv⟩ := Metric.isOpen_iff.mp hv 0 (h0v rfl)
  refine ⟨r / 2, by positivity, ?_⟩
  intro z hz
  apply huv
  refine ⟨hKu hz.1, hrv ?_⟩
  have hz' := hz.2
  rw [mem_closedBall, dist_zero_right] at hz'
  rw [mem_ball, dist_zero_right]
  linarith

theorem norm_iteratedFDeriv_graph_CX3 {c : E → F} {x : E} {k j : ℕ}
    (hc : ContDiffAt ℝ k c x) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ‖iteratedFDeriv ℝ j (fun y => (y, c y)) x‖ ≤
      max 1 ‖iteratedFDeriv ℝ j c x‖ := by
  rw [iteratedFDeriv_prodMk (f := fun y : E => y) contDiffAt_id hc (by exact_mod_cast hjk)]
  exact (DifferentialGeometry.Analysis.ContinuousMultilinearMap.norm_prod_le_max _ _).trans
    (max_le_max (DifferentialGeometry.Analysis.norm_iteratedFDeriv_id_le_one j hj x) le_rfl)

theorem norm_iteratedFDeriv_graph_sub_CX3 {c : E → F} {x : E} {k j : ℕ}
    (hc : ContDiffAt ℝ k c x) (hjk : j ≤ k) :
    ‖iteratedFDeriv ℝ j (fun y => (y, c y)) x -
      iteratedFDeriv ℝ j (fun y : E => (y, (0 : F))) x‖ ≤
      ‖iteratedFDeriv ℝ j c x‖ := by
  have hpair : ContDiffAt ℝ j (fun y => (y, c y)) x :=
    (contDiffAt_id.prodMk hc).of_le (by exact_mod_cast hjk)
  have hzero : ContDiffAt ℝ j (fun y : E => (y, (0 : F))) x :=
    contDiffAt_id.prodMk contDiffAt_const
  rw [← iteratedFDeriv_sub_apply hpair hzero]
  change ‖iteratedFDeriv ℝ j (fun y : E => (y, c y) - (y, (0 : F))) x‖ ≤ _
  have heq : (fun y : E => (y, c y) - (y, (0 : F))) = fun y => ((0 : E), c y) := by
    funext y
    simp
  rw [heq, iteratedFDeriv_prodMk contDiffAt_const hc (by exact_mod_cast hjk)]
  have hz : iteratedFDeriv ℝ j (fun _ : E => (0 : E)) x = 0 := by
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply]
  rw [hz]
  simpa only [norm_zero, max_eq_right (norm_nonneg _)] using
    DifferentialGeometry.Analysis.ContinuousMultilinearMap.norm_prod_le_max
      (0 : E [×j]→L[ℝ] E) (iteratedFDeriv ℝ j c x)

/-- A smooth map on a fixed tube is locally Lipschitz on bounded finite jets of
graphs over the zero section.  The constants precede the varying graph. -/
theorem exists_graph_jet_bound_CX3 [FiniteDimensional ℝ F]
    {ψ : E × F → G} {K : Set E} {N : Set (E × F)}
    (hK : IsCompact K) (hN : IsOpen N) (hψ : ContDiffOn ℝ ∞ ψ N)
    (h0 : ∀ x ∈ K, (x, (0 : F)) ∈ N) (k : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (c : E → F) (x : E), x ∈ K → ContDiffAt ℝ k c x →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ →
          (∀ j ≤ k, ‖iteratedFDeriv ℝ j c x‖ ≤ ε) →
          (x, c x) ∈ N ∧ ∀ j ≤ k,
            ‖iteratedFDeriv ℝ j (fun y => ψ (y, c y)) x -
              iteratedFDeriv ℝ j (fun y => ψ (y, (0 : F))) x‖ ≤ C * ε := by
  classical
  obtain ⟨r, hr, htube⟩ := exists_graph_tube_CX3 hK hN h0
  obtain ⟨B, hB, hbound⟩ := exists_compact_jet_bound_CX3
    (hK.prod (isCompact_closedBall (0 : F) r)) hN htube hψ (k + 1)
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  let C : ℝ := 1 + ∑ j ∈ Finset.range (k + 1), jetCompConstant_CX3 j B
  have hC : 0 < C := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (k + 1)) =>
      jetCompConstant_nonneg_CX3 j hB0)
    dsimp [C]
    linarith
  refine ⟨min r 1, C, lt_min hr zero_lt_one, hC, ?_⟩
  intro c x hx hc ε hε hεδ hjets
  have hεr : ε ≤ r := hεδ.trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := hεδ.trans (min_le_right _ _)
  have hc0 : ‖c x‖ ≤ ε := by simpa only [norm_iteratedFDeriv_zero] using hjets 0 (Nat.zero_le k)
  have hcx : (x, c x) ∈ K ×ˢ closedBall (0 : F) r :=
    ⟨hx, by simpa only [mem_closedBall, dist_zero_right] using hc0.trans hεr⟩
  have hx0 : (x, (0 : F)) ∈ K ×ˢ closedBall (0 : F) r :=
    ⟨hx, mem_closedBall_self hr.le⟩
  refine ⟨htube hcx, ?_⟩
  intro j hj
  have hj' : (j : ℕ∞ω) ≤ k := by exact_mod_cast hj
  have houter : ∀ i ≤ j,
      ‖iteratedFDeriv ℝ i ψ (x, c x) - iteratedFDeriv ℝ i ψ (x, (0 : F))‖ ≤ B * ε := by
    intro i hi
    let S : Set (E × F) := {x} ×ˢ closedBall (0 : F) r
    have hSN : S ⊆ N := fun z hz => htube ⟨by
      rw [mem_singleton_iff.mp hz.1]; exact hx, hz.2⟩
    have hder : ∀ z ∈ S, DifferentiableAt ℝ (iteratedFDeriv ℝ i ψ) z := by
      intro z hz
      exact ((hψ.contDiffAt (hN.mem_nhds (hSN hz))).iteratedFDeriv_right
        (m := 1) (by simp)).differentiableAt one_ne_zero
    have hdB : ∀ z ∈ S, ‖fderiv ℝ (iteratedFDeriv ℝ i ψ) z‖ ≤ B := by
      intro z hz
      rw [norm_fderiv_iteratedFDeriv]
      exact hbound (i + 1) (by omega) z ⟨by
        rw [mem_singleton_iff.mp hz.1]; exact hx, hz.2⟩
    have hmv := ((convex_singleton x).prod (convex_closedBall (0 : F) r)).norm_image_sub_le_of_norm_fderiv_le
      hder hdB (show (x, (0 : F)) ∈ S from ⟨rfl, hx0.2⟩)
      (show (x, c x) ∈ S from ⟨rfl, hcx.2⟩)
    have hnorm : ‖(x, c x) - (x, (0 : F))‖ = ‖c x‖ := by simp
    rw [hnorm] at hmv
    exact hmv.trans (mul_le_mul_of_nonneg_left hc0 hB0)
  have hcomp := norm_iteratedFDeriv_comp_sub_le_CX3 (f := ψ)
    (u := fun y => (y, c y)) (v := fun y : E => (y, (0 : F))) j
    ((hψ.contDiffAt (hN.mem_nhds (htube hcx))).of_le (by exact_mod_cast le_top))
    ((hψ.contDiffAt (hN.mem_nhds (htube hx0))).of_le (by exact_mod_cast le_top))
    ((contDiffAt_id.prodMk hc).of_le hj') (contDiffAt_id.prodMk contDiffAt_const)
    hB0 hε (fun i hi => hbound i (by omega) _ hcx) houter
    (fun i hi hij => (norm_iteratedFDeriv_graph_CX3 hc hi (hij.trans hj)).trans
      (max_le hB ((hjets i (hij.trans hj)).trans (hε1.trans hB))))
    (fun i hi hij => (norm_iteratedFDeriv_graph_CX3
      (contDiffAt_const : ContDiffAt ℝ k (fun _ : E => (0 : F)) x) hi (hij.trans hj)).trans
      (by simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, max_eq_left zero_le_one] using hB))
    (fun i _ hij => (norm_iteratedFDeriv_graph_sub_CX3 hc (hij.trans hj)).trans
      (hjets i (hij.trans hj)))
  refine hcomp.trans (mul_le_mul_of_nonneg_right ?_ hε)
  have hle := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (k + 1)) =>
    jetCompConstant_nonneg_CX3 i hB0) (show j ∈ Finset.range (k + 1) by simpa using hj)
  dsimp [C]
  linarith

end GC.LongTime.Ch12
