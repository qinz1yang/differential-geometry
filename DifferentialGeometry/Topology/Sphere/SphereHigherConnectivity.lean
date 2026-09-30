import DifferentialGeometry.Topology.Sphere.SphereSimplyConnected
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace DifferentialGeometry.Topology

open Set Metric Module _root_.Topology unitInterval
open scoped ContinuousMap

def diffRestrictionSubalgebra {m : ℕ} (s : Set (EuclideanSpace ℝ (Fin m))) :
    Subalgebra ℝ C(s, ℝ) where
  carrier := {g | ∃ G : EuclideanSpace ℝ (Fin m) → ℝ, Differentiable ℝ G ∧
    ∀ z : s, g z = G z.1}
  mul_mem' := by
    rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
    exact ⟨F * G, hF.mul hG, fun z => by simp [hf z, hg z]⟩
  add_mem' := by
    rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
    exact ⟨F + G, hF.add hG, fun z => by simp [hf z, hg z]⟩
  algebraMap_mem' r := ⟨fun _ => r, differentiable_const r, fun _ => rfl⟩

theorem diffRestrictionSubalgebra_separatesPoints {m : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin m))) : (diffRestrictionSubalgebra s).SeparatesPoints := by
  intro z w hzw
  have hcoord : ∃ i : Fin m, z.1 i ≠ w.1 i := by
    by_contra! h
    apply hzw
    apply Subtype.ext
    ext i
    exact h i
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨fun x : s => x.1 i, ⟨⟨fun x : s => x.1 i, by fun_prop⟩,
    ⟨fun x => x i, differentiable_euclidean.mp differentiable_id i, fun _ => rfl⟩, rfl⟩, hi⟩

theorem exists_differentiable_near_on_compact {m n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin m))} [CompactSpace s]
    {f : s → EuclideanSpace ℝ (Fin n)} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n), Differentiable ℝ G ∧
      ∀ z : s, ‖G z.1 - f z‖ < ε := by
  have hε' : 0 < ε / (n + 1) := by positivity
  have hcomp : ∀ i : Fin n, ∃ G : EuclideanSpace ℝ (Fin m) → ℝ, Differentiable ℝ G ∧
      ∀ z : s, |G z.1 - f z i| < ε / (n + 1) := by
    intro i
    obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
      (diffRestrictionSubalgebra s) (diffRestrictionSubalgebra_separatesPoints s)
      (fun z => f z i) (by fun_prop) _ hε'
    obtain ⟨G, hG, hgG⟩ := g.2
    refine ⟨G, hG, fun z => ?_⟩
    have h := hg z
    rw [Real.norm_eq_abs, hgG z] at h
    exact h
  choose G hG hGf using hcomp
  refine ⟨fun x => WithLp.toLp 2 (fun i => G i x),
    differentiable_euclidean.mpr hG, fun z => ?_⟩
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖(WithLp.toLp 2 (fun i => G i z.1) - f z) i‖ ^ 2 ≤
      ∑ _i : Fin n, (ε / (n + 1)) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    simp only [PiLp.sub_apply, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hGf i z).le 2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  refine (Real.sqrt_le_sqrt hsum).trans_lt ?_
  rw [Real.sqrt_lt' hε, div_pow, mul_div_assoc', div_lt_iff₀ (by positivity)]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hε2 : 0 < ε ^ 2 := by positivity
  nlinarith [mul_nonneg hε2.le (sq_nonneg (n : ℝ)), mul_nonneg hε2.le hn, hε2]

section Normalization

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_homotopic_normalization (f : C(X, sphere (0 : E) 1))
    (G : X → E) (hG : Continuous G) (hnear : ∀ x, ‖G x - (f x : E)‖ < 1) :
    ∃ δ : C(X, sphere (0 : E) 1), f.Homotopic δ ∧
      ∀ x, (δ x : E) = radialProj (G x) := by
  let w : I × X → E := fun p => (f p.2 : E) + (p.1 : ℝ) • (G p.2 - (f p.2 : E))
  have hw : Continuous w := by
    exact (continuous_subtype_val.comp (f.continuous.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((hG.comp continuous_snd).sub
          (continuous_subtype_val.comp (f.continuous.comp continuous_snd))))
  have hne (p : I × X) : w p ≠ 0 := by
    have hclose : ‖w p - (f p.2 : E)‖ < 1 := by
      have heq : w p - (f p.2 : E) = (p.1 : ℝ) • (G p.2 - (f p.2 : E)) := by
        dsimp [w]
        abel
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg p.1.2.1]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) p.1.2.2) (hnear p.2)
    intro hz
    rw [hz, zero_sub, norm_neg, norm_eq_of_mem_sphere (f p.2)] at hclose
    exact lt_irrefl _ hclose
  have hw0 (x : X) : w (0, x) = (f x : E) := by simp [w]
  have hw1 (x : X) : w (1, x) = G x := by simp [w]
  let H : C(I × X, sphere (0 : E) 1) :=
    ⟨fun p => ⟨radialProj (w p), radialProj_mem_sphere (hne p)⟩,
      (continuous_radialProj_comp hw hne).subtype_mk _⟩
  let δ : C(X, sphere (0 : E) 1) := H.comp ⟨fun x => (1, x), by fun_prop⟩
  refine ⟨δ, ⟨{ toContinuousMap := H, map_zero_left := ?_, map_one_left := fun _ => rfl }⟩, ?_⟩
  · intro x
    apply Subtype.ext
    change radialProj (w (0, x)) = (f x : E)
    rw [hw0, radialProj_of_norm_eq_one (norm_eq_of_mem_sphere (f x))]
  · intro x
    change radialProj (w (1, x)) = radialProj (G x)
    rw [hw1]

end Normalization

theorem nullhomotopic_of_compact_euclidean_source {m n : ℕ} (hmn : m + 1 ≤ n)
    {s : Set (EuclideanSpace ℝ (Fin m))} [CompactSpace s]
    (f : C(s, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) : f.Nullhomotopic := by
  obtain ⟨G, hG, hnear⟩ := exists_differentiable_near_on_compact
    (continuous_subtype_val.comp f.continuous) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨δ, hfδ, hδ⟩ := exists_homotopic_normalization f (fun x => G x.1)
    (hG.continuous.comp continuous_subtype_val) hnear
  let cone : EuclideanSpace ℝ (Fin m) × ℝ → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun p => p.2 • G p.1
  have hcone : Differentiable ℝ cone := by
    change Differentiable ℝ (fun p : EuclideanSpace ℝ (Fin m) × ℝ => p.2 • G p.1)
    have hfst : Differentiable ℝ (Prod.fst : EuclideanSpace ℝ (Fin m) × ℝ →
        EuclideanSpace ℝ (Fin m)) := differentiable_fst
    have hsnd : Differentiable ℝ (Prod.snd : EuclideanSpace ℝ (Fin m) × ℝ → ℝ) :=
      differentiable_snd
    exact hsnd.smul (hG.comp hfst)
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin m) × ℝ) <
      finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self,
      finrank_euclideanSpace_fin]
    omega
  obtain ⟨q, hq⟩ := (hcone.dense_compl_range_of_finrank_lt_finrank hdim).nonempty
  have hq0 : q ≠ 0 := by
    intro hzero
    apply hq
    refine ⟨(0, 0), ?_⟩
    simp [cone, hzero]
  let qS : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    ⟨radialProj q, radialProj_mem_sphere hq0⟩
  have hmiss (x : s) : δ x ≠ qS := by
    intro heq
    have hrad := congrArg Subtype.val heq
    rw [hδ x] at hrad
    change radialProj (G x.1) = radialProj q at hrad
    apply hq
    refine ⟨(x.1, ‖q‖ * ‖G x.1‖⁻¹), ?_⟩
    change (‖q‖ * ‖G x.1‖⁻¹) • G x.1 = q
    rw [← smul_smul]
    change ‖q‖ • radialProj (G x.1) = q
    rw [hrad]
    simp [radialProj, smul_smul, norm_ne_zero_iff.mpr hq0]
  let δ' : C(s, ({qS}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) :=
    ⟨fun x => ⟨δ x, hmiss x⟩, δ.continuous.subtype_mk _⟩
  have : ContractibleSpace ({qS}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
    contractibleSpace_sphere_compl_singleton qS
  have hδnull : δ.Nullhomotopic :=
    ((id_nullhomotopic _).comp_left δ').comp_right ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨c, hc⟩ := hδnull
  exact ⟨c, hfδ.trans hc⟩

theorem nullhomotopic_map_sphere_of_add_two_le {k n : ℕ} (hkn : k + 2 ≤ n)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1,
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) : f.Nullhomotopic :=
  nullhomotopic_of_compact_euclidean_source (by omega) f

end DifferentialGeometry.Topology
