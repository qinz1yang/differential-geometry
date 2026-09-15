import DifferentialGeometry.Topology.Attachment.TransitionGluing
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Analysis.Calculus.MapConvergence.MovingCoordinates

section

noncomputable section
open Set Filter Topology
namespace TopCat.GlueData
open TopologicalSpace
universe u v
variable {ι E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
    (U : Opens E) (near : ι → ι → Bool)
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hJ : ∀ a, ContinuousOn (J a) U)
    (hrefl : ∀ i, near i i = true)
    (hsymm : ∀ i j, near i j = true → near j i = true)
    (hself : ∀ i x, x ∈ U → J ⟨(i, i), hrefl i⟩ x = x)
    (hinv : ∀ i j (h : near i j = true) x, x ∈ U → J ⟨(i, j), h⟩ x ∈ U →
      J ⟨(j, i), hsymm i j h⟩ (J ⟨(i, j), h⟩ x) = x)
    (htrans : ∀ i j k (hij : near i j = true) (hjk : near j k = true) x,
      x ∈ U → J ⟨(i, j), hij⟩ x ∈ U → J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x) ∈ U →
      ∃ hik : near i k = true,
        J ⟨(i, k), hik⟩ x = J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x))

local notation "D" => ofTransitionMaps (U : Set E) U.isOpen near J hJ hrefl hsymm hself hinv htrans


theorem ofTransitionMaps_eq_of_source_chart_collision_limit
    {M : ℕ → Type v} [∀ n, TopologicalSpace (M n)]
    (c : ι → ∀ n, OpenPartialHomeomorph E (M n))
    (hsource : ∀ i n, (U : Set E) ⊆ (c i n).source)
    (hfar : ∀ i j, near i j = false →
      ∀ᶠ n in atTop, Disjoint ((c i n) '' (U : Set E)) ((c j n) '' (U : Set E)))
    {V : Set E} (hV : IsOpen V) (hUV : (U : Set E) ⊆ V)
    (hconv : ∀ a, DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts V
      (fun n z => (c a.1.2 n).symm (c a.1.1 n z)) (J a))
    (hcont : ∀ a, ContinuousOn (J a) V)
    {i j : ι} (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (x y : ℕ → E) (z w : U)
    (hx : Tendsto x atTop (nhds (z : E)))
    (hy : Tendsto y atTop (nhds (w : E)))
    (heq : ∀ᶠ n in atTop, c i (φ n) (x n) = c j (φ n) (y n)) :
    (D).toGlueData.ι i z = (D).toGlueData.ι j w := by
  have hxU := hx.eventually (U.isOpen.mem_nhds z.property)
  have hyU := hy.eventually (U.isOpen.mem_nhds w.property)
  have hij : near i j = true := by
    cases hn : near i j
    · have hdisj := hφ.tendsto_atTop.eventually (hfar i j hn)
      obtain ⟨n, hxn, hyn, hen, hdn⟩ := (hxU.and (hyU.and (heq.and hdisj))).exists
      exact False.elim (Set.disjoint_left.mp hdn ⟨x n, hxn, rfl⟩ ⟨y n, hyn, hen.symm⟩)
    · rfl
  have hseq := (hconv ⟨(i,j),hij⟩).comp_subseq hφ
  obtain ⟨K, hK, hzK, hKV⟩ := exists_compact_subset hV (hUV z.property)
  have hxK : Tendsto x atTop (nhdsWithin (z : E) K) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hx
      (hx.eventually (mem_interior_iff_mem_nhds.mp hzK))
  have hlim := (DifferentialGeometry.CheegerGromovCompactness.tendstoUniformlyOn_of_cPConvergence
    (hseq K hK hKV 0)).tendsto_comp ((hcont ⟨(i,j),hij⟩ z (hUV z.property)).mono hKV) hxK
  have hevent : (fun n => (c j (φ n)).symm (c i (φ n) (x n))) =ᶠ[atTop] y := by
    filter_upwards [heq, hyU] with n hn hyn
    rw [hn]
    exact (c j (φ n)).left_inv (hsource j (φ n) hyn)
  have hJzw : J ⟨(i,j),hij⟩ z = w :=
    tendsto_nhds_unique hlim (hy.congr' hevent.symm)
  let a : transitionOverlap (U : Set E) U.isOpen near J hJ i j :=
    ⟨z, hij, hJzw.symm ▸ w.property⟩
  have hglue := (D).glue_condition_apply i j a
  change (D).toGlueData.ι j ⟨J ⟨(i,j),hij⟩ z, _⟩ = (D).toGlueData.ι i z at hglue
  rw [hglue.symm]
  congr 1
  exact Subtype.ext hJzw

end TopCat.GlueData

end

end

section

noncomputable section
open Set Filter Topology
namespace TopCat.GlueData
open TopologicalSpace
universe u v
variable {ι E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
    (U : Opens E) (near : ι → ι → Bool)
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hJ : ∀ a, ContinuousOn (J a) U)
    (hrefl : ∀ i, near i i = true)
    (hsymm : ∀ i j, near i j = true → near j i = true)
    (hself : ∀ i x, x ∈ U → J ⟨(i, i), hrefl i⟩ x = x)
    (hinv : ∀ i j (h : near i j = true) x, x ∈ U → J ⟨(i, j), h⟩ x ∈ U →
      J ⟨(j, i), hsymm i j h⟩ (J ⟨(i, j), h⟩ x) = x)
    (htrans : ∀ i j k (hij : near i j = true) (hjk : near j k = true) x,
      x ∈ U → J ⟨(i, j), hij⟩ x ∈ U → J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x) ∈ U →
      ∃ hik : near i k = true,
        J ⟨(i, k), hik⟩ x = J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x))

local notation "D" => ofTransitionMaps (U : Set E) U.isOpen near J hJ hrefl hsymm hself hinv htrans


theorem ofTransitionMaps_collision_limits_of_chart_convergence
    {M : ℕ → Type v} [∀ n, TopologicalSpace (M n)]
    (c : ι → ∀ n, OpenPartialHomeomorph E (M n))
    (hsource : ∀ i n, (U : Set E) ⊆ (c i n).source)
    (hfar : ∀ i j, near i j = false →
      ∀ᶠ n in atTop, Disjoint ((c i n) '' (U : Set E)) ((c j n) '' (U : Set E)))
    {V : Set E} (hV : IsOpen V) (hUV : (U : Set E) ⊆ V)
    (hconv : ∀ a, DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts V
      (fun n z => (c a.1.2 n).symm (c a.1.1 n z)) (J a))
    (hcont : ∀ a, ContinuousOn (J a) V)
    [Nonempty U]
    (VQ : Opens (D).toGlueData.glued)
    (F : ∀ n, (D).toGlueData.glued → M n)
    (A : ι → ℕ → E → E)
    (hA : ∀ i, DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Subtype.val '' ((fun z : U => (D).toGlueData.ι i z) ⁻¹' (VQ : Set (D).toGlueData.glued)))
      (A i) id)
    (hcoords : ∀ i n (z : U), A i n z = (c i n).symm (F n ((D).toGlueData.ι i z)))
    (himage : ∀ i (L : Set E), IsCompact L →
      L ⊆ Subtype.val '' ((fun z : U => (D).toGlueData.ι i z) ⁻¹' (VQ : Set (D).toGlueData.glued)) →
      ∀ᶠ n in atTop, ∀ z : U, (z : E) ∈ L → F n ((D).toGlueData.ι i z) ∈ (c i n).target)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (q r : ℕ → (D).toGlueData.glued) (a b : (D).toGlueData.glued)
    (ha : a ∈ VQ) (hb : b ∈ VQ)
    (hq : Tendsto q atTop (nhds a)) (hr : Tendsto r atTop (nhds b))
    (heq : ∀ n, F (φ n) (q n) = F (φ n) (r n)) : a = b := by
  obtain ⟨i, z, rfl⟩ := (D).ι_jointly_surjective a
  obtain ⟨j, w, rfl⟩ := (D).ι_jointly_surjective b
  let : Nonempty ((D).U i) := ⟨Classical.choice (show Nonempty U from inferInstance)⟩
  let : Nonempty ((D).U j) := ⟨Classical.choice (show Nonempty U from inferInstance)⟩
  let ei : OpenPartialHomeomorph U (D).toGlueData.glued :=
    ((D).ι_isOpenEmbedding i).toOpenPartialHomeomorph ((D).toGlueData.ι i)
  let ej : OpenPartialHomeomorph U (D).toGlueData.glued :=
    ((D).ι_isOpenEmbedding j).toOpenPartialHomeomorph ((D).toGlueData.ι j)
  have hi := DifferentialGeometry.CheegerGromovCompactness.tendsto_source_chart_inverse_of_chart_convergence
    U ei rfl VQ (c i) F (A i) (hA i) (hcoords i) (himage i) ha hq φ hφ
  have hj := DifferentialGeometry.CheegerGromovCompactness.tendsto_source_chart_inverse_of_chart_convergence
    U ej rfl VQ (c j) F (A j) (hA j) (hcoords j) (himage j) hb hr φ hφ
  apply ofTransitionMaps_eq_of_source_chart_collision_limit U near J hJ hrefl hsymm hself hinv htrans
    c hsource hfar hV hUV hconv hcont φ hφ
    (fun n => (c i (φ n)).symm (F (φ n) (q n)))
    (fun n => (c j (φ n)).symm (F (φ n) (r n))) z w hi.1 hj.1
  filter_upwards [hi.2, hj.2] with n hin hjn
  rw [(c i (φ n)).right_inv hin, (c j (φ n)).right_inv hjn, heq n]

end TopCat.GlueData

end

end
