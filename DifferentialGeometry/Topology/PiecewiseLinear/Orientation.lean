import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.StellarSphere
import DifferentialGeometry.Topology.SimplicialComplex.Incidence

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*}

noncomputable def faceCofaces
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (s : Finset E) (n : ℕ) : Finset (Finset E) := by
  classical
  exact SimplicialComplex.cofaces K.toPreAbstractSimplicialComplex s n

@[simp]
theorem mem_faceCofaces
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {s t : Finset E} {n : ℕ} :
    t ∈ faceCofaces K s n ↔ t ∈ K.faces ∧ t.card = n ∧ s ⊆ t := by
  classical
  exact SimplicialComplex.mem_cofaces K.toPreAbstractSimplicialComplex

def incidenceIndex (r : LinearOrder E) (s : Finset E) (v : E) : ℕ :=
  let _ := r
  (s.filter fun w => w < v).card

def incidenceSign (r : LinearOrder E) (s : Finset E) (v : E) : ℤ :=
  (-1 : ℤ) ^ incidenceIndex r s v

theorem incidenceIndex_erase_of_lt (r : LinearOrder E) {s : Finset E} {v w : E}
    (hv : v ∈ s) (hvw : v < w) :
    incidenceIndex r (s.erase v) w + 1 = incidenceIndex r s w := by
  let _ := r
  classical
  simp only [incidenceIndex, Finset.filter_erase]
  exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hv, hvw⟩)

theorem incidenceIndex_erase_of_not_lt (r : LinearOrder E) {s : Finset E} {v w : E}
    (hvw : ¬ v < w) : incidenceIndex r (s.erase v) w = incidenceIndex r s w := by
  let _ := r
  classical
  simp [incidenceIndex, Finset.filter_erase, hvw]

theorem incidenceSign_pair (r : LinearOrder E) {s : Finset E} {v w : E}
    (hv : v ∈ s) (hw : w ∈ s) (hvw : v ≠ w) :
    incidenceSign r s v * incidenceSign r (s.erase v) w =
      -(incidenceSign r s w * incidenceSign r (s.erase w) v) := by
  let _ := r
  rcases lt_or_gt_of_ne hvw with h | h
  · have hiw := incidenceIndex_erase_of_lt r hv h
    have hiv := incidenceIndex_erase_of_not_lt r (s := s) (v := w) (w := v) (not_lt_of_ge h.le)
    simp only [incidenceSign, ← pow_add]
    rw [hiv]
    have hp : incidenceIndex r s w = incidenceIndex r (s.erase v) w + 1 := hiw.symm
    rw [hp]
    have he : incidenceIndex r (s.erase v) w + 1 + incidenceIndex r s v =
        (incidenceIndex r s v + incidenceIndex r (s.erase v) w) + 1 := by omega
    rw [he, pow_succ]
    ring
  · have hiv := incidenceIndex_erase_of_lt r hw h
    have hiw := incidenceIndex_erase_of_not_lt r (s := s) (v := v) (w := w) (not_lt_of_ge h.le)
    simp only [incidenceSign, ← pow_add]
    rw [hiw]
    have hp : incidenceIndex r s v = incidenceIndex r (s.erase w) v + 1 := hiv.symm
    rw [hp]
    have he : incidenceIndex r (s.erase w) v + 1 + incidenceIndex r s w =
        (incidenceIndex r s w + incidenceIndex r (s.erase w) v) + 1 := by omega
    rw [he, pow_succ]
    ring

def doubleFaceTerm (r : LinearOrder E) (s u : Finset E) (p : E × E) : ℤ :=
  if (s.erase p.1).erase p.2 = u then
    incidenceSign r s p.1 * incidenceSign r (s.erase p.1) p.2
  else 0

theorem doubleFaceTerm_swap (r : LinearOrder E) {s u : Finset E} {p : E × E}
    (hp : p ∈ s.offDiag) : doubleFaceTerm r s u p + doubleFaceTerm r s u (p.2, p.1) = 0 := by
  obtain ⟨hp₁, hp₂, hne⟩ := Finset.mem_offDiag.mp hp
  rw [doubleFaceTerm, doubleFaceTerm]
  have herase : (s.erase p.2).erase p.1 = (s.erase p.1).erase p.2 :=
    Finset.erase_right_comm
  by_cases h : (s.erase p.1).erase p.2 = u
  · have h' : (s.erase p.2).erase p.1 = u := herase.trans h
    rw [if_pos h, if_pos h', incidenceSign_pair r hp₁ hp₂ hne]
    ring
  · have h' : (s.erase p.2).erase p.1 ≠ u := fun he => h (herase.symm.trans he)
    rw [if_neg h, if_neg h', zero_add]

theorem sum_doubleFaceTerm_eq_zero (r : LinearOrder E) (s u : Finset E) :
    ∑ p ∈ s.offDiag, doubleFaceTerm r s u p = 0 := by
  classical
  exact Finset.sum_involution
    (fun p _ => (p.2, p.1))
    (fun p hp => doubleFaceTerm_swap r hp)
    (fun p hp _ => by
      intro heq
      exact (Finset.mem_offDiag.mp hp).2.2 (congrArg Prod.fst heq).symm)
    (fun p hp => by
      exact Finset.mem_offDiag.mpr
        ⟨(Finset.mem_offDiag.mp hp).2.1, (Finset.mem_offDiag.mp hp).1,
          (Finset.mem_offDiag.mp hp).2.2.symm⟩)
    (fun _ _ => rfl)

def simplexBoundaryCoefficient (r : LinearOrder E) (s t : Finset E) : ℤ :=
  ∑ v ∈ s, if s.erase v = t then incidenceSign r s v else 0

theorem simplexBoundaryCoefficient_erase (r : LinearOrder E) {s : Finset E} {v : E}
    (hv : v ∈ s) : simplexBoundaryCoefficient r s (s.erase v) = incidenceSign r s v := by
  classical
  rw [simplexBoundaryCoefficient, Finset.sum_eq_single v]
  · rw [if_pos rfl]
  · intro w hw hwv
    rw [if_neg]
    exact fun he => hwv ((Finset.erase_inj s hw).mp he)
  · exact fun h => False.elim (h hv)

theorem sum_simplexBoundaryCoefficient_comp_eq_zero
    [AddCommGroup E] [Module ℝ E] (r : LinearOrder E)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} {s u : Finset E} (hs : s ∈ K.faces) (hscard : s.card = n + 2) :
    ∑ t ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex (n + 1),
        simplexBoundaryCoefficient r s t * simplexBoundaryCoefficient r t u = 0 := by
  classical
  simp_rw [simplexBoundaryCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  have herase (v : E) (hv : v ∈ s) :
      s.erase v ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex (n + 1) := by
    rw [SimplicialComplex.mem_facesOfCard]
    refine ⟨K.down_closed hs (Finset.erase_subset v s) ?_, ?_⟩
    · have hc := Finset.card_erase_of_mem hv
      exact Finset.card_pos.mp (by omega)
    · rw [Finset.card_erase_of_mem hv, hscard]
      omega
  calc
    _ = ∑ v ∈ s, incidenceSign r s v * simplexBoundaryCoefficient r (s.erase v) u := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [herase v hv, simplexBoundaryCoefficient]
    _ = ∑ v ∈ s, ∑ w ∈ s.erase v, doubleFaceTerm r s u (v, w) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [simplexBoundaryCoefficient, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      simp only [mul_ite, mul_zero, doubleFaceTerm]
    _ = ∑ p ∈ s.offDiag, doubleFaceTerm r s u p := by
      symm
      apply Finset.sum_finset_product
      intro p
      simp only [Finset.mem_offDiag, Finset.mem_erase]
      tauto
    _ = 0 := sum_doubleFaceTerm_eq_zero r s u

noncomputable def orientedBoundary
    [AddCommGroup E] [Module ℝ E] (r : LinearOrder E)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (n : ℕ) (c : Finset E → ℤ) (t : Finset E) : ℤ :=
  ∑ s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex (n + 1),
    c s * simplexBoundaryCoefficient r s t

theorem orientedBoundary_boundary
    [AddCommGroup E] [Module ℝ E] (r : LinearOrder E)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (n : ℕ) (c : Finset E → ℤ) (u : Finset E) :
    orientedBoundary r K n (orientedBoundary r K (n + 1) c) u = 0 := by
  classical
  rw [orientedBoundary]
  simp_rw [orientedBoundary, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro s hs
  obtain ⟨hsK, hscard⟩ :=
    (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, sum_simplexBoundaryCoefficient_comp_eq_zero r K hsK hscard, mul_zero]

open Classical in
theorem cofaces_eq_singleton_of_cofaceVertices_eq_singleton
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {s : Finset E} {a : E}
    (hvertices : {w | w ∉ s ∧ insert w s ∈ K.faces} = {a}) :
    faceCofaces K s (s.card + 1) = {insert a s} := by
  ext t
  rw [mem_faceCofaces, Finset.mem_singleton]
  constructor
  · rintro ⟨ht, htcard, hst⟩
    obtain ⟨w, hws, hwt⟩ := Finset.exists_eq_insert_iff.mpr ⟨hst, htcard.symm⟩
    have hw : w ∈ {x | x ∉ s ∧ insert x s ∈ K.faces} := ⟨hws, hwt ▸ ht⟩
    rw [hvertices] at hw
    exact hwt.symm.trans (congrArg (fun x => insert x s) (Set.mem_singleton_iff.mp hw))
  · rintro rfl
    have ha : a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces} := by
      rw [hvertices]
      exact Set.mem_singleton a
    exact ⟨ha.2, Finset.card_insert_of_notMem ha.1, Finset.subset_insert a s⟩

open Classical in
theorem cofaces_eq_pair_of_cofaceVertices_eq_pair
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {s : Finset E} {a b : E}
    (hvertices : {w | w ∉ s ∧ insert w s ∈ K.faces} = {a, b}) :
    faceCofaces K s (s.card + 1) = {insert a s, insert b s} := by
  ext t
  rw [mem_faceCofaces]
  constructor
  · rintro ⟨ht, htcard, hst⟩
    obtain ⟨w, hws, hwt⟩ := Finset.exists_eq_insert_iff.mpr ⟨hst, htcard.symm⟩
    have hw : w ∈ {x | x ∉ s ∧ insert x s ∈ K.faces} := ⟨hws, hwt ▸ ht⟩
    rw [hvertices] at hw
    have hw' : w = a ∨ w = b := by simpa using hw
    rcases hw' with hwa | hwb
    · rw [Finset.mem_insert]
      exact Or.inl (hwt.symm.trans (congrArg (fun x => insert x s) hwa))
    · rw [Finset.mem_insert]
      exact Or.inr (Finset.mem_singleton.mpr
        (hwt.symm.trans (congrArg (fun x => insert x s) hwb)))
  · intro ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · have ha : a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces} := by
        rw [hvertices]
        simp
      exact ⟨ha.2, Finset.card_insert_of_notMem ha.1, Finset.subset_insert a s⟩
    · rw [Finset.mem_singleton] at ht
      subst t
      have hb : b ∈ {w | w ∉ s ∧ insert w s ∈ K.faces} := by
        rw [hvertices]
        simp
      exact ⟨hb.2, Finset.card_insert_of_notMem hb.1, Finset.subset_insert b s⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_iff_card_cofaces_eq_one
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {s : Finset E} (hs : s ∈ K.faces) (hscard : s.card = n + 1) :
    s ∈ (boundaryComplex (n + 1) K).faces ↔
      (faceCofaces K s (n + 2)).card = 1 := by
  have hbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1 := by
    intro u hu _
    rw [hscard]
    exact hK.card_le K hu
  constructor
  · intro hsB
    have hball := ((hK.mem_boundaryComplex_faces_iff K).mp hsB).2.2
    have hball₀ : IsPLBall 0 (SimplicialComplex.geometricLink K s).space := by
      simpa only [hscard, Nat.sub_self] using hball
    rw [geometricLink_space_eq_coface_vertices_of_card_le K s hbound] at hball₀
    obtain ⟨a, ha⟩ := isPLBall_zero_iff.mp hball₀
    have hcofaces := cofaces_eq_singleton_of_cofaceVertices_eq_singleton K ha
    rw [show n + 2 = s.card + 1 by omega, hcofaces, Finset.card_singleton]
  · intro hcard
    rcases hK.codimension_one_cofaces K hs hscard with ⟨a, ha⟩ | ⟨a, b, hab, habset⟩
    · apply (hK.mem_boundaryComplex_faces_iff K).mpr
      refine ⟨hs, hscard.le, ?_⟩
      have hball₀ : IsPLBall 0 (SimplicialComplex.geometricLink K s).space := by
        rw [geometricLink_space_eq_coface_vertices_of_card_le K s hbound]
        exact isPLBall_zero_iff.mpr ⟨a, ha⟩
      simpa only [hscard, Nat.sub_self] using hball₀
    · have haV : a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces} := by
        rw [habset]
        simp
      have hbV : b ∈ {w | w ∉ s ∧ insert w s ∈ K.faces} := by
        rw [habset]
        simp
      have hinsert : insert a s ≠ insert b s := by
        intro heq
        apply hab
        have hamem : a ∈ insert b s := heq ▸ Finset.mem_insert_self a s
        exact (Finset.mem_insert.mp hamem).resolve_right haV.1
      have hcofaces := cofaces_eq_pair_of_cofaceVertices_eq_pair K habset
      rw [show n + 2 = s.card + 1 by omega, hcofaces] at hcard
      simp [hinsert] at hcard

open Classical in
theorem IsCombinatorialManifoldWithBoundary.card_faceCofaces_eq_one_or_two
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {s : Finset E} (hs : s ∈ K.faces) (hscard : s.card = n + 1) :
    (faceCofaces K s (n + 2)).card = 1 ∨ (faceCofaces K s (n + 2)).card = 2 := by
  rcases hK.codimension_one_cofaces K hs hscard with ⟨a, ha⟩ | ⟨a, b, hab, habset⟩
  · left
    have hcofaces := cofaces_eq_singleton_of_cofaceVertices_eq_singleton K ha
    rw [show n + 2 = s.card + 1 by omega, hcofaces, Finset.card_singleton]
  · right
    have haV : a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces} := by
      rw [habset]
      simp
    have hinsert : insert a s ≠ insert b s := by
      intro heq
      apply hab
      have hamem : a ∈ insert b s := heq ▸ Finset.mem_insert_self a s
      exact (Finset.mem_insert.mp hamem).resolve_right haV.1
    have hcofaces := cofaces_eq_pair_of_cofaceVertices_eq_pair K habset
    rw [show n + 2 = s.card + 1 by omega, hcofaces]
    simp [hinsert]

structure CoherentOrientation
    [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] where
  vertexOrder : LinearOrder E
  sign : Finset E → ℤ
  sign_top : ∀ s ∈ K.faces, s.card = n + 1 → sign s = 1 ∨ sign s = -1
  coherent : ∀ t ∈ K.faces, t.card = n →
    (faceCofaces K t (n + 1)).card ≠ 1 →
      orientedBoundary vertexOrder K n sign t = 0

def IsOrientable
    [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] : Prop :=
  Nonempty (CoherentOrientation n K)

open Classical in
noncomputable instance finite_boundaryComplex_faces
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Finite (boundaryComplex n K).faces := by
  classical
  exact Set.Finite.to_subtype (boundaryComplex_faces_finite n K)

theorem orientedBoundary_eq_of_cofaces_eq_singleton
    [AddCommGroup E] [Module ℝ E]
    (r : LinearOrder E) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (c : Finset E → ℤ) {t q : Finset E}
    (hcofaces : faceCofaces K t (n + 1) = {q}) :
    orientedBoundary r K n c t = c q * simplexBoundaryCoefficient r q t := by
  classical
  rw [orientedBoundary, Finset.sum_eq_single q]
  · intro s hs hsq
    have hscard :=
      ((SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs).2
    suffices simplexBoundaryCoefficient r s t = 0 by rw [this, mul_zero]
    rw [simplexBoundaryCoefficient]
    apply Finset.sum_eq_zero
    intro v hv
    rw [if_neg]
    intro herase
    have hts : t ⊆ s := by
      rw [← herase]
      exact Finset.erase_subset v s
    have hsco : s ∈ faceCofaces K t (n + 1) :=
      (mem_faceCofaces K).mpr
        ⟨((SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs).1,
          hscard, hts⟩
    rw [hcofaces, Finset.mem_singleton] at hsco
    exact hsq hsco
  · intro hq
    have hqco : q ∈ faceCofaces K t (n + 1) := by
      rw [hcofaces]
      exact Finset.mem_singleton_self q
    exact False.elim (hq ((SimplicialComplex.mem_facesOfCard
      K.toPreAbstractSimplicialComplex).mpr
        ⟨((mem_faceCofaces K).mp hqco).1,
          ((mem_faceCofaces K).mp hqco).2.1⟩))

theorem orientedBoundary_eq_sum_faceCofaces
    [AddCommGroup E] [Module ℝ E]
    (r : LinearOrder E) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (c : Finset E → ℤ) (t : Finset E) :
    orientedBoundary r K n c t =
      ∑ s ∈ faceCofaces K t (n + 1), c s * simplexBoundaryCoefficient r s t := by
  classical
  rw [orientedBoundary]
  symm
  apply Finset.sum_subset
  · intro s hs
    exact (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mpr
      ⟨((mem_faceCofaces K).mp hs).1, ((mem_faceCofaces K).mp hs).2.1⟩
  · intro s hs hst
    suffices simplexBoundaryCoefficient r s t = 0 by rw [this, mul_zero]
    rw [simplexBoundaryCoefficient]
    apply Finset.sum_eq_zero
    intro v hv
    rw [if_neg]
    intro herase
    apply hst
    apply (mem_faceCofaces K).mpr
    refine ⟨((SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs).1,
      ((SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs).2, ?_⟩
    rw [← herase]
    exact Finset.erase_subset v s

theorem orientedBoundary_eq_of_faceCofaces_eq
    [AddCommGroup E] [Module ℝ E]
    (r : LinearOrder E)
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    {n : ℕ} (c : Finset E → ℤ) (t : Finset E)
    (hcofaces : faceCofaces K t (n + 1) = faceCofaces L t (n + 1)) :
    orientedBoundary r K n c t = orientedBoundary r L n c t := by
  rw [orientedBoundary_eq_sum_faceCofaces, orientedBoundary_eq_sum_faceCofaces, hcofaces]

theorem orientedBoundary_eq_one_or_neg_one_of_card_cofaces_eq_one
    [AddCommGroup E] [Module ℝ E]
    (r : LinearOrder E) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} {c : Finset E → ℤ}
    (hc : ∀ s ∈ K.faces, s.card = n + 1 → c s = 1 ∨ c s = -1)
    {t : Finset E} (htcard : t.card = n)
    (hcofaces : (faceCofaces K t (n + 1)).card = 1) :
    orientedBoundary r K n c t = 1 ∨ orientedBoundary r K n c t = -1 := by
  classical
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcofaces
  have hqco : q ∈ faceCofaces K t (n + 1) := by
    rw [hq]
    exact Finset.mem_singleton_self q
  obtain ⟨hqK, hqcard, htq⟩ :=
    (mem_faceCofaces K).mp hqco
  obtain ⟨v, hvt, hvq⟩ := Finset.exists_eq_insert_iff.mpr ⟨htq, by omega⟩
  have hvqmem : v ∈ q := hvq ▸ Finset.mem_insert_self v t
  have hqerase : q.erase v = t := by rw [← hvq, Finset.erase_insert hvt]
  rw [orientedBoundary_eq_of_cofaces_eq_singleton r K c hq]
  rw [← hqerase, simplexBoundaryCoefficient_erase r hvqmem]
  rcases hc q hqK hqcard with hcq | hcq <;>
    rcases neg_one_pow_eq_or ℤ (incidenceIndex r q v) with hi | hi <;>
      simp only [incidenceSign, hcq, hi] <;> norm_num

open Classical in
theorem CoherentOrientation.orientedBoundary_boundaryComplex_eq
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (o : CoherentOrientation (n + 1) K) (u : Finset E) :
    orientedBoundary o.vertexOrder (boundaryComplex (n + 1) K) n
        (orientedBoundary o.vertexOrder K (n + 1) o.sign) u =
      orientedBoundary o.vertexOrder K n
        (orientedBoundary o.vertexOrder K (n + 1) o.sign) u := by
  rw [orientedBoundary, orientedBoundary]
  apply Finset.sum_subset
  · intro t ht
    rw [SimplicialComplex.mem_facesOfCard] at ht ⊢
    exact ⟨boundaryComplex_faces_subset (n + 1) K ht.1, ht.2⟩
  · intro t htK htB
    obtain ⟨htKface, htcard⟩ :=
      (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp htK
    have htNotBoundary : t ∉ (boundaryComplex (n + 1) K).faces := by
      intro ht
      apply htB
      exact (SimplicialComplex.mem_facesOfCard
        (boundaryComplex (n + 1) K).toPreAbstractSimplicialComplex).mpr ⟨ht, htcard⟩
    have hne :
        (faceCofaces K t (n + 2)).card ≠ 1 :=
      fun h => htNotBoundary
        ((hK.mem_boundaryComplex_iff_card_cofaces_eq_one K htKface htcard).mpr h)
    rw [o.coherent t htKface htcard hne, zero_mul]

open Classical in
noncomputable def CoherentOrientation.boundary
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (o : CoherentOrientation (n + 1) K) :
    CoherentOrientation n (boundaryComplex (n + 1) K) where
  vertexOrder := o.vertexOrder
  sign := orientedBoundary o.vertexOrder K (n + 1) o.sign
  sign_top := by
    intro t htB htcard
    have htK : t ∈ K.faces := boundaryComplex_faces_subset (n + 1) K htB
    have hcofaces :=
      (hK.mem_boundaryComplex_iff_card_cofaces_eq_one K htK htcard).mp htB
    exact orientedBoundary_eq_one_or_neg_one_of_card_cofaces_eq_one
      o.vertexOrder K o.sign_top htcard hcofaces
  coherent := by
    intro u hu hucard _
    rw [o.orientedBoundary_boundaryComplex_eq K hK]
    exact orientedBoundary_boundary o.vertexOrder K n o.sign u

open Classical in
theorem IsOrientable.boundary
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (h : IsOrientable (n + 1) K) :
    IsOrientable n (boundaryComplex (n + 1) K) := by
  obtain ⟨o⟩ := h
  exact ⟨o.boundary K hK⟩

open Classical in
theorem IsOrientable.of_le
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    {n : ℕ} (hLK : L ≤ K)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L)
    (h : IsOrientable (n + 1) K) : IsOrientable (n + 1) L := by
  obtain ⟨o⟩ := h
  refine ⟨{
    vertexOrder := o.vertexOrder
    sign := o.sign
    sign_top := fun s hs hscard => o.sign_top s (hLK hs) hscard
    coherent := ?_ }⟩
  intro t htL htcard hLne
  have htK : t ∈ K.faces := hLK htL
  have hsub : faceCofaces L t (n + 2) ⊆ faceCofaces K t (n + 2) := by
    intro s hs
    exact (mem_faceCofaces K).mpr
      ⟨hLK ((mem_faceCofaces L).mp hs).1, ((mem_faceCofaces L).mp hs).2.1,
        ((mem_faceCofaces L).mp hs).2.2⟩
  have hLtwo : (faceCofaces L t (n + 2)).card = 2 :=
    (hL.card_faceCofaces_eq_one_or_two L htL htcard).resolve_left hLne
  have hKnotone : (faceCofaces K t (n + 2)).card ≠ 1 := by
    intro hKone
    have hcardle := Finset.card_le_card hsub
    rw [hLtwo, hKone] at hcardle
    omega
  have hKtwo : (faceCofaces K t (n + 2)).card = 2 :=
    (hK.card_faceCofaces_eq_one_or_two K htK htcard).resolve_left hKnotone
  have hcofaces : faceCofaces L t (n + 2) = faceCofaces K t (n + 2) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hLtwo, hKtwo])
  rw [← orientedBoundary_eq_of_faceCofaces_eq o.vertexOrder K L o.sign t hcofaces.symm]
  exact o.coherent t htK htcard hKnotone

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

open Classical in
theorem isPLHomeomorphOn_gluedMap_of_full
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    (K₁ : Geometry.SimplicialComplex ℝ E) (K₂ : Geometry.SimplicialComplex ℝ F)
    [Finite K₁.faces] [Finite K₂.faces]
    (A₁ : Geometry.SimplicialComplex ℝ E) (A₂ : Geometry.SimplicialComplex ℝ F)
    (ψ : E → F) (ψ' : F → E) (h : IsGlueIso A₁ A₂ ψ ψ')
    (hA₁ : A₁.faces ⊆ K₁.faces) (hA₂ : A₂.faces ⊆ K₂.faces)
    (hfull₁ : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A₁.faces) → s ∈ A₁.faces)
    (g₁ : E → G) (g₂ : F → G) (Y₁ Y₂ : Set G)
    (hg₁ : IsPLHomeomorphOn g₁ K₁.space Y₁)
    (hg₂ : IsPLHomeomorphOn g₂ K₂.space Y₂)
    (hcompat : ∀ x ∈ A₁.space, g₂ (simplicialMap A₁ ψ x) = g₁ x)
    (hoverlap : Y₁ ∩ Y₂ = g₁ '' A₁.space) :
    IsPLHomeomorphOn (gluedMap K₁ A₁ ψ g₁ g₂)
      (gluedComplex K₁ K₂ h hA₂ hfull₁).space (Y₁ ∪ Y₂) := by
  classical
  let ι₁ := simplicialMap K₁ (glueEmbed₁ A₁ ψ)
  let ι₂ := simplicialMap K₂ (glueEmbed₂ A₂ ψ')
  have hemb₁ := isPLHomeomorphOn_embedComplex K₁ (glueEmbed₁ A₁ ψ)
    (glueFst E F) (fun _ _ _ _ => rfl)
  have hemb₂ := isPLHomeomorphOn_embedComplex K₂ (glueEmbed₂ A₂ ψ')
    (glueSnd E F) (fun _ _ _ _ => rfl)
  have hπ₁ : EqOn (glueFst E F) (Function.invFunOn ι₁ K₁.space)
      (glued₁ K₁ A₁ ψ).space := by
    intro z hz
    apply hemb₁.bijOn.injOn
      (glueFst_mem_of_mem_glued₁ K₁ A₁ ψ hz)
      (hemb₁.bijOn.surjOn.mapsTo_invFunOn hz)
    calc
      simplicialMap K₁ (glueEmbed₁ A₁ ψ) (glueFst E F z) = z :=
        simplicialMap_glueFst K₁ A₁ ψ hz
      _ = simplicialMap K₁ (glueEmbed₁ A₁ ψ)
          (Function.invFunOn ι₁ K₁.space z) :=
        (hemb₁.bijOn.invOn_invFunOn.2 hz).symm
  have hπ₂ : EqOn (glueSnd E F) (Function.invFunOn ι₂ K₂.space)
      (glued₂ K₂ A₂ ψ').space := by
    intro z hz
    apply hemb₂.bijOn.injOn
      (glueSnd_mem_of_mem_glued₂ K₂ A₂ ψ' hz)
      (hemb₂.bijOn.surjOn.mapsTo_invFunOn hz)
    calc
      simplicialMap K₂ (glueEmbed₂ A₂ ψ') (glueSnd E F z) = z :=
        simplicialMap_glueSnd K₂ A₂ ψ' hz
      _ = simplicialMap K₂ (glueEmbed₂ A₂ ψ')
          (Function.invFunOn ι₂ K₂.space z) :=
        (hemb₂.bijOn.invOn_invFunOn.2 hz).symm
  have hside₁ : IsPLHomeomorphOn (g₁ ∘ glueFst E F)
      (glued₁ K₁ A₁ ψ).space Y₁ := by
    refine (hemb₁.symm.trans hg₁).congr ?_
    intro z hz
    simp only [Function.comp_apply]
    rw [hπ₁ hz]
  have hside₂ : IsPLHomeomorphOn (g₂ ∘ glueSnd E F)
      (glued₂ K₂ A₂ ψ').space Y₂ := by
    refine (hemb₂.symm.trans hg₂).congr ?_
    intro z hz
    simp only [Function.comp_apply]
    rw [hπ₂ hz]
  have hinter := glued₁_space_inter_glued₂_space K₁ K₂ h hA₁ hA₂ hfull₁
  have hglue₁ : EqOn (gluedMap K₁ A₁ ψ g₁ g₂) (g₁ ∘ glueFst E F)
      (glued₁ K₁ A₁ ψ).space := by
    intro z hz
    rw [gluedMap_of_mem K₁ A₁ ψ g₁ g₂ hz]
    rfl
  have hglue₂ : EqOn (gluedMap K₁ A₁ ψ g₁ g₂) (g₂ ∘ glueSnd E F)
      (glued₂ K₂ A₂ ψ').space := by
    intro z hz
    by_cases hz₁ : z ∈ (glued₁ K₁ A₁ ψ).space
    · rw [gluedMap_of_mem K₁ A₁ ψ g₁ g₂ hz₁]
      have hz' : z ∈ (glued₁ K₁ A₁ ψ).space ∩ (glued₂ K₂ A₂ ψ').space :=
        ⟨hz₁, hz⟩
      rw [hinter] at hz'
      obtain ⟨x, hx, rfl⟩ := hz'
      simp only [Function.comp_apply]
      rw [glueFst_simplicialMap K₁ A₁ ψ (space_mono_of_faces_subset hA₁ hx),
        glueSnd_simplicialMap_of_mem K₁ hA₁ hx, hcompat x hx]
    · rw [gluedMap_of_notMem K₁ A₁ ψ g₁ g₂ hz₁]
      rfl
  have hmeet : (gluedMap K₁ A₁ ψ g₁ g₂) ''
      ((glued₁ K₁ A₁ ψ).space ∩ (glued₂ K₂ A₂ ψ').space) = Y₁ ∩ Y₂ := by
    rw [hinter, hoverlap]
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      rw [gluedMap_of_mem K₁ A₁ ψ g₁ g₂
        (simplicialMap_mem_glued₁ K₁ A₁ ψ (space_mono_of_faces_subset hA₁ hx)),
        glueFst_simplicialMap K₁ A₁ ψ (space_mono_of_faces_subset hA₁ hx)]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨ι₁ x, ⟨x, hx, rfl⟩, ?_⟩
      rw [gluedMap_of_mem K₁ A₁ ψ g₁ g₂
        (simplicialMap_mem_glued₁ K₁ A₁ ψ (space_mono_of_faces_subset hA₁ hx)),
        glueFst_simplicialMap K₁ A₁ ψ (space_mono_of_faces_subset hA₁ hx)]
  let hfin₁ : Finite (glued₁ K₁ A₁ ψ).faces := (glued₁_faces_finite K₁ A₁ ψ).to_subtype
  let hfin₂ : Finite (glued₂ K₂ A₂ ψ').faces := (glued₂_faces_finite K₂ A₂ ψ').to_subtype
  have hpoly₁ : IsPolyhedron (glued₁ K₁ A₁ ψ).space := isPolyhedron_space _
  have hpoly₂ : IsPolyhedron (glued₂ K₂ A₂ ψ').space := isPolyhedron_space _
  have hunion := (hside₁.congr hglue₁).union (hside₂.congr hglue₂) hpoly₁ hpoly₂ hmeet
  rw [gluedComplex_space K₁ K₂ h hA₂ hfull₁]
  exact hunion

open Classical in
noncomputable def boundaryRelSubdivision
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) :
    Geometry.SimplicialComplex ℝ E :=
  relDerived (boundaryComplex_faces_subset n K)
    (IsSubdivision.refl (boundaryComplex n K))
    (centroid_mem_openSimplex_of_mem_faces K)

open Classical in
theorem boundaryComplex_faces_subset_boundaryRelSubdivision
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) :
    (boundaryComplex n K).faces ⊆ (boundaryRelSubdivision n K).faces :=
  faces_subset_relDerived (boundaryComplex_faces_subset n K)
    (IsSubdivision.refl (boundaryComplex n K))
    (centroid_mem_openSimplex_of_mem_faces K)

open Classical in
theorem boundaryComplex_full_boundaryRelSubdivision
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) (s : Finset E)
    (hs : s ∈ (boundaryRelSubdivision n K).faces)
    (hv : ∀ v ∈ s, {v} ∈ (boundaryComplex n K).faces) :
    s ∈ (boundaryComplex n K).faces :=
  mem_faces_of_mem_relDerived_of_forall_singleton_mem
    (boundaryComplex_faces_subset n K)
    (IsSubdivision.refl (boundaryComplex n K))
    (centroid_mem_openSimplex_of_mem_faces K) hs hv

open Classical in
noncomputable def double (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) :
    Geometry.SimplicialComplex ℝ (E × E × ℝ) :=
  gluedComplex (boundaryRelSubdivision n K) K
    (isGlueIso_id (boundaryComplex n K))
    (boundaryComplex_faces_subset n K)
    (boundaryComplex_full_boundaryRelSubdivision n K)

open Classical in
theorem boundaryComplex_simplexComplex_std (n : ℕ)
    [DecidableEq (Fin (n + 2) → ℝ)] :
    boundaryComplex (n + 1)
        (simplexComplex (stdVertices n) (stdVertices_affineIndependent n)) =
      simplexBoundary (stdVertices n) (stdVertices_affineIndependent n) := by
  let K := simplexComplex (stdVertices n) (stdVertices_affineIndependent n)
  let B := simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)
  let hKfinite : Finite K.faces :=
    (simplexComplex_faces_finite (stdVertices n) (stdVertices_affineIndependent n)).to_subtype
  have hTne : (stdVertices n).Nonempty := Finset.card_pos.mp (by rw [card_stdVertices]; omega)
  have hKspace : K.space = stdSimplex ℝ (Fin (n + 2)) := by
    rw [show K = simplexComplex (stdVertices n) (stdVertices_affineIndependent n) from rfl,
      simplexComplex_space _ _ hTne, convexHull_stdVertices]
  have hKid : IsPLHomeomorphOn id (stdSimplex ℝ (Fin (n + 2))) K.space := by
    rw [hKspace]
    exact isPLHomeomorphOn_id_of_isHPolytope (isHPolytope_stdSimplex _)
  have hspace : (boundaryComplex (n + 1) K).space = B.space := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hKid]
    exact image_id B.space
  apply Geometry.SimplicialComplex.ext
  ext s
  constructor
  · intro hs
    have hsK : s ∈ K.faces := boundaryComplex_faces_subset (n + 1) K hs
    have hx := centroid_mem_openSimplex_of_mem_faces K s hsK
    by_contra hnot
    exact notMem_space_of_notMem_faces
      (simplexBoundary_faces_subset_simplexComplex (stdVertices n)
        (stdVertices_affineIndependent n)) hsK hnot hx
      (hspace ▸ (boundaryComplex (n + 1) K).convexHull_subset_space hs
        (openSimplex_subset_convexHull s hx))
  · intro hs
    have hsK : s ∈ K.faces :=
      simplexBoundary_faces_subset_simplexComplex (stdVertices n)
        (stdVertices_affineIndependent n) hs
    have hx := centroid_mem_openSimplex_of_mem_faces K s hsK
    by_contra hnot
    exact notMem_space_of_notMem_faces
      (boundaryComplex_faces_subset (n + 1) K) hsK hnot hx
      (hspace.symm ▸ B.convexHull_subset_space hs
        (openSimplex_subset_convexHull s hx))

private noncomputable def classicalConeComplex {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E}
    {L : Geometry.SimplicialComplex ℝ E} (h : IsConeBase p L) :
    Geometry.SimplicialComplex ℝ E :=
  @coneComplex E _ _ (Classical.decEq E) p L h

open Classical in
theorem simplexBoundary_full_coneComplex
    {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : 2 ≤ T.card) {p : E} (hp : p ∈ openSimplex T)
    (s : Finset E) (hs : s ∈ (coneComplex
      (isConeBase_simplexBoundary hT hcard hp)).faces)
    (hv : ∀ v ∈ s, {v} ∈ (simplexBoundary T hT).faces) :
    s ∈ (simplexBoundary T hT).faces := by
  rw [mem_coneComplex_faces_iff] at hs
  rcases hs with hs | rfl | ⟨σ, hσ, rfl⟩
  · exact hs
  · exact False.elim ((isConeBase_simplexBoundary hT hcard hp).notMem_face
      (hv p (Finset.mem_singleton_self p)) (Finset.mem_singleton_self p))
  · exact False.elim ((isConeBase_simplexBoundary hT hcard hp).notMem_face
      (hv p (Finset.mem_insert_self p σ)) (Finset.mem_singleton_self p))

open Classical in
theorem isPLSphere_gluedCone_simplex
    [FiniteDimensional ℝ E] {n : ℕ} {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = n + 2)
    {p : E} (hp : p ∈ openSimplex T) :
    IsPLSphere (n + 1) (gluedComplex
      (coneComplex (isConeBase_simplexBoundary hT (by omega) hp))
      (simplexComplex T hT) (isGlueIso_id (simplexBoundary T hT))
      (simplexBoundary_faces_subset_simplexComplex T hT)
      (simplexBoundary_full_coneComplex hT (by omega) hp)).space := by
  classical
  let B := simplexBoundary T hT
  let K := simplexComplex T hT
  let hcone : IsConeBase p B := isConeBase_simplexBoundary hT (by omega) hp
  let C := coneComplex hcone
  let e₁ : E → E × E × ℝ := glueEmbed₁ B id
  let e₂ : E → E × E × ℝ := glueEmbed₂ B id
  let q := e₁ p
  let V := T.image e₂
  let U := insert q V
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hvB (v : E) (hv : v ∈ T) : {v} ∈ B.faces := by
    apply (mem_simplexBoundary_faces_iff).mpr
    refine ⟨Finset.singleton_subset_iff.mpr hv, Finset.singleton_nonempty v, ?_⟩
    intro heq
    have := congrArg Finset.card heq
    simp only [Finset.card_singleton, hcard] at this
    omega
  have hpB : {p} ∉ B.faces := by
    intro hpface
    exact hcone.notMem_face hpface (Finset.mem_singleton_self p)
  have hqheight : glueHeight E E q = 1 := by
    simp [q, e₁, glueEmbed₁, glueHeight, hpB]
  have hVheight (z : E × E × ℝ) (hz : z ∈ V) : glueHeight E E z = 0 := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    simp [e₂, glueEmbed₂, glueHeight, hvB v hv]
  have hqV : q ∉ V := by
    intro hq
    have hz := hVheight q hq
    rw [hqheight] at hz
    norm_num at hz
  have hKtop : T ∈ K.faces := (mem_simplexComplex_faces_iff T hT).mpr ⟨hTne, subset_rfl⟩
  have hVface : V ∈ (glued₂ K B id).faces := by
    exact (mem_glued₂_faces_iff K B id).mpr ⟨T, hKtop, rfl⟩
  have hVind : AffineIndependent ℝ ((↑) : V → E × E × ℝ) :=
    (glued₂ K B id).indep hVface
  have hUind : AffineIndependent ℝ ((↑) : U → E × E × ℝ) := by
    apply (affineIndependent_insert_iff hqV hVind).mpr
    rintro ⟨c, -, hcq⟩
    have hmap := congrArg (glueHeight E E) hcq
    have hzero : glueHeight E E (∑ v ∈ V, c v • v) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro v hv
      rw [map_smul, hVheight v hv, smul_zero]
    rw [hzero, hqheight] at hmap
    norm_num at hmap
  have hVcard : V.card = T.card := by
    exact Finset.card_image_of_injective T (glueEmbed₂_injective B id)
  have hUcard : U.card = n + 3 := by
    change (insert q V).card = n + 3
    rw [Finset.card_insert_of_notMem hqV, hVcard, hcard]
  have hinv (z : E × E × ℝ) (hz : z ∈ V) : e₂ (glueSnd E E z) = z := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    rfl
  have hpreimage (t : Finset (E × E × ℝ)) (ht : t ⊆ V) :
      ∃ s : Finset E, s ⊆ T ∧ t = s.image e₂ := by
    let s := t.image (glueSnd E E)
    refine ⟨s, ?_, ?_⟩
    · intro v hv
      obtain ⟨z, hzt, hzv⟩ := Finset.mem_image.mp hv
      obtain ⟨w, hwT, hzw⟩ := Finset.mem_image.mp (ht hzt)
      have hvw : v = w := by
        rw [← hzv, ← hzw]
        rfl
      exact hvw.symm ▸ hwT
    · apply Finset.Subset.antisymm
      · intro z hzt
        apply Finset.mem_image.mpr
        exact ⟨glueSnd E E z, Finset.mem_image.mpr ⟨z, hzt, rfl⟩,
          hinv z (ht hzt)⟩
      · intro z hz
        obtain ⟨v, hvs, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨w, hwt, hwv⟩ := Finset.mem_image.mp hvs
        rw [← hwv, hinv w (ht hwt)]
        exact hwt
  have hbaseImage (s : Finset E) (hs : s ∈ B.faces) : s.image e₁ = s.image e₂ := by
    simpa [e₁, e₂] using image_glueEmbed₁_eq (isGlueIso_id B) hs
  have hcomplex : gluedComplex C K (isGlueIso_id B)
      (simplexBoundary_faces_subset_simplexComplex T hT)
      (simplexBoundary_full_coneComplex hT (by omega) hp) = simplexBoundary U hUind := by
    apply Geometry.SimplicialComplex.ext
    ext t
    rw [mem_gluedComplex_faces_iff, mem_simplexBoundary_faces_iff]
    constructor
    · intro ht
      rcases ht with ht | ht
      · obtain ⟨s, hsC, rfl⟩ := (mem_glued₁_faces_iff C B id).mp ht
        have hsne := C.nonempty_of_mem_faces hsC
        have himgne : (s.image e₁).Nonempty := hsne.image e₁
        have hsub : s.image e₁ ⊆ U := by
          rw [mem_coneComplex_faces_iff] at hsC
          rcases hsC with hsB | rfl | ⟨σ, hσB, rfl⟩
          · rw [hbaseImage s hsB]
            exact Finset.Subset.trans (Finset.image_subset_image
              ((mem_simplexBoundary_faces_iff.mp hsB).1))
              (Finset.subset_insert q V)
          · rw [Finset.image_singleton]
            exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self q V)
          · rw [Finset.image_insert, hbaseImage σ hσB]
            exact Finset.insert_subset (Finset.mem_insert_self q V)
              ((Finset.image_subset_image (mem_simplexBoundary_faces_iff.mp hσB).1).trans
                (Finset.subset_insert q V))
        refine ⟨hsub, himgne, ?_⟩
        intro heq
        have hcardle : (s.image e₁).card ≤ T.card := by
          rw [Finset.card_image_of_injective s (glueEmbed₁_injective B id)]
          rw [mem_coneComplex_faces_iff] at hsC
          rcases hsC with hsB | rfl | ⟨σ, hσB, rfl⟩
          · exact Finset.card_le_card (mem_simplexBoundary_faces_iff.mp hsB).1
          · simp only [Finset.card_singleton]
            omega
          · rw [Finset.card_insert_of_notMem (hcone.notMem_face hσB)]
            have hproper := (mem_simplexBoundary_faces_iff.mp hσB).2.2
            exact Nat.succ_le_of_lt (Finset.card_lt_card
              (Finset.ssubset_iff_subset_ne.mpr
                ⟨(mem_simplexBoundary_faces_iff.mp hσB).1, hproper⟩))
        have hcards : (s.image e₁).card = U.card :=
          congrArg Finset.card (by simpa [e₁] using heq)
        rw [hUcard] at hcards
        omega
      · obtain ⟨s, hsK, rfl⟩ := (mem_glued₂_faces_iff K B id).mp ht
        refine ⟨?_, (K.nonempty_of_mem_faces hsK).image e₂, ?_⟩
        · exact (Finset.image_subset_image hsK.2).trans (Finset.subset_insert q V)
        · intro heq
          have hcardle : (s.image e₂).card ≤ T.card := by
            rw [Finset.card_image_of_injective s (glueEmbed₂_injective B id)]
            exact Finset.card_le_card hsK.2
          have hcards : (s.image e₂).card = U.card :=
            congrArg Finset.card (by simpa [e₂] using heq)
          rw [hUcard] at hcards
          omega
    · rintro ⟨htU, htne, htUneq⟩
      by_cases hqt : q ∈ t
      · have ht0V : t.erase q ⊆ V := by
          intro z hz
          rcases Finset.mem_insert.mp (htU (Finset.mem_of_mem_erase hz)) with hzq | hzV
          · exact absurd hzq (Finset.ne_of_mem_erase hz)
          · exact hzV
        obtain ⟨σ, hσT, ht0⟩ := hpreimage (t.erase q) ht0V
        by_cases hσne : σ.Nonempty
        · have hσneq : σ ≠ T := by
            intro hσT'
            apply htUneq
            calc
              t = insert q (t.erase q) := (Finset.insert_erase hqt).symm
              _ = insert q (σ.image e₂) := by rw [ht0]
              _ = insert q V := by rw [hσT']
              _ = U := rfl
          have hσB : σ ∈ B.faces :=
            (mem_simplexBoundary_faces_iff).mpr ⟨hσT, hσne, hσneq⟩
          apply Or.inl
          apply (mem_glued₁_faces_iff C B id).mpr
          refine ⟨insert p σ, Or.inr (Or.inr ⟨σ, hσB, rfl⟩), ?_⟩
          calc
            t = insert q (t.erase q) := (Finset.insert_erase hqt).symm
            _ = insert q (σ.image e₂) := by rw [ht0]
            _ = insert (e₁ p) (σ.image e₁) := by rw [hbaseImage σ hσB]
            _ = (insert p σ).image e₁ := by rw [Finset.image_insert]
            _ = (insert p σ).image (glueEmbed₁ B id) := by rfl
        · rw [Finset.not_nonempty_iff_eq_empty] at hσne
          apply Or.inl
          apply (mem_glued₁_faces_iff C B id).mpr
          refine ⟨{p}, Or.inr (Or.inl rfl), ?_⟩
          rw [Finset.image_singleton]
          rw [← Finset.insert_erase hqt, ht0, hσne, Finset.image_empty, Finset.insert_empty]
      · have htV : t ⊆ V := by
          intro z hz
          rcases Finset.mem_insert.mp (htU hz) with hzq | hzV
          · subst z
            exact False.elim (hqt hz)
          · exact hzV
        obtain ⟨s, hsT, hts⟩ := hpreimage t htV
        have hsne : s.Nonempty := by
          rw [hts] at htne
          exact Finset.Nonempty.of_image htne
        apply Or.inr
        exact (mem_glued₂_faces_iff K B id).mpr
          ⟨s, (mem_simplexComplex_faces_iff T hT).mpr ⟨hsne, hsT⟩, hts⟩
  rw [show gluedComplex
      (coneComplex (isConeBase_simplexBoundary hT (by omega) hp))
      (simplexComplex T hT) (isGlueIso_id (simplexBoundary T hT))
      (simplexBoundary_faces_subset_simplexComplex T hT)
      (simplexBoundary_full_coneComplex hT (by omega) hp) = simplexBoundary U hUind by
        exact hcomplex]
  rw [simplexBoundary_space U hUind (by omega)]
  exact isPLSphere_biUnion_erase U hUind hUcard

open Classical in
theorem boundaryRelSubdivision_isSubdivision
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) :
    IsSubdivision (boundaryRelSubdivision n K) K :=
  relDerived_isSubdivision (boundaryComplex_faces_subset n K)
    (IsSubdivision.refl (boundaryComplex n K))
    (centroid_mem_openSimplex_of_mem_faces K)

open Classical in
theorem boundaryRelSubdivision_faces_finite
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    (boundaryRelSubdivision n K).faces.Finite :=
  relDerived_faces_finite (boundaryComplex_faces_subset n K)
    (IsSubdivision.refl (boundaryComplex n K))
    (centroid_mem_openSimplex_of_mem_faces K)

theorem simplicialMap_id_eq_of_mem
    (K : Geometry.SimplicialComplex ℝ E) {x : E} (hx : x ∈ K.space) :
    simplicialMap K id x = x := by
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  rw [simplicialMap_eq_of_mem K id hs hxs]
  exact sum_weights_smul hxs

open Classical in
theorem simplicialMap_glueEmbed_id_eq
    (K₁ K₂ A : Geometry.SimplicialComplex ℝ E)
    (hA₁ : A.faces ⊆ K₁.faces) (hA₂ : A.faces ⊆ K₂.faces)
    {x : E} (hx : x ∈ A.space) :
    simplicialMap K₁ (glueEmbed₁ A id) x =
      simplicialMap K₂ (glueEmbed₂ A id) x := by
  obtain ⟨s, hs, hxs⟩ := A.mem_space_iff.mp hx
  rw [simplicialMap_eq_of_mem K₁ _ (hA₁ hs) hxs,
    simplicialMap_eq_of_mem K₂ _ (hA₂ hs) hxs]
  apply Finset.sum_congr rfl
  intro v hv
  have hvA : {v} ∈ A.faces := A.down_closed hs
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  rw [glueEmbed₁, glueEmbed₂, if_pos hvA, if_pos hvA]
  rfl

open Classical in
theorem boundaryRelSubdivision_simplexComplex_std (n : ℕ) :
    boundaryRelSubdivision (n + 1)
        (simplexComplex (stdVertices n) (stdVertices_affineIndependent n)) =
      classicalConeComplex (isConeBase_simplexBoundary (stdVertices_affineIndependent n)
        (two_le_card_stdVertices n) (centroid_mem_openSimplex (by
          exact Finset.card_pos.mp (by rw [card_stdVertices]; omega)))) := by
  classical
  let _ : DecidableEq (Fin (n + 2) → ℝ) := Classical.decEq _
  unfold boundaryRelSubdivision classicalConeComplex
  have hTne : (stdVertices n).Nonempty :=
    Finset.card_pos.mp (by rw [card_stdVertices]; omega)
  have hmem (u : Finset (Fin (n + 2) → ℝ)) :
      u ∈ (boundaryComplex (n + 1)
          (simplexComplex (stdVertices n) (stdVertices_affineIndependent n))).faces ↔
        u ∈ (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).faces := by
    rw [boundaryComplex_simplexComplex_std n]
  ext s
  constructor
  · rintro ⟨τ, d, hrel, rfl⟩
    have hdsub : d ⊆ {stdVertices n} := by
      intro u hu
      rw [Finset.mem_singleton]
      have huK := hrel.flag.mem_faces hu
      by_contra hut
      exact hrel.notMem u hu ((hmem u).mpr
        ((mem_simplexBoundary_faces_iff).mpr ⟨huK.2, huK.1, hut⟩))
    rcases Finset.subset_singleton_iff.mp hdsub with rfl | rfl
    · rw [Finset.image_empty, Finset.union_empty]
      rcases hrel.base with hτ | hτ
      · rcases hrel.nonempty with hne | hne
        · exact absurd hne (hτ ▸ Finset.not_nonempty_empty)
        · exact absurd hne Finset.not_nonempty_empty
      · exact Or.inl ((hmem τ).mp hτ)
    · rw [Finset.image_singleton]
      rcases hrel.base with hτ | hτ
      · rw [hτ, Finset.empty_union]
        exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨τ, (hmem τ).mp hτ,
          by rw [Finset.union_singleton]⟩)
  · intro hs
    rcases hs with hs | rfl | ⟨σ, hσ, rfl⟩
    · refine ⟨s, ∅, ?_, by rw [Finset.image_empty, Finset.union_empty]⟩
      exact ⟨Or.inr ((hmem s).mpr hs),
        ⟨fun u hu => absurd hu (Finset.notMem_empty u),
          fun u hu => absurd hu (Finset.notMem_empty u)⟩,
        fun u hu => absurd hu (Finset.notMem_empty u),
        fun u hu => absurd hu (Finset.notMem_empty u),
        Or.inl ((simplexBoundary (stdVertices n)
          (stdVertices_affineIndependent n)).nonempty_of_mem_faces hs)⟩
    · refine ⟨∅, {stdVertices n}, ?_, by rw [Finset.image_singleton, Finset.empty_union]⟩
      refine ⟨Or.inl rfl, ?_, ?_, ?_,
        Or.inr (Finset.singleton_nonempty (stdVertices n))⟩
      · exact ⟨fun u hu => by
          rw [Finset.mem_singleton] at hu
          subst u
          exact ⟨hTne, Finset.Subset.refl (stdVertices n)⟩,
          fun u hu v hv => by
            rw [Finset.mem_singleton] at hu hv
            subst u
            subst v
            exact Or.inl (Finset.Subset.refl (stdVertices n))⟩
      · intro u hu
        rw [Finset.mem_singleton] at hu
        subst u
        exact fun h =>
          (mem_simplexBoundary_faces_iff.mp ((hmem (stdVertices n)).mp h)).2.2 rfl
      · intro u hu v hv
        exact absurd hv (Finset.notMem_empty v)
    · refine ⟨σ, {stdVertices n}, ?_, by rw [Finset.image_singleton, Finset.union_singleton]⟩
      refine ⟨Or.inr ((hmem σ).mpr hσ), ?_, ?_, ?_, Or.inl
        ((simplexBoundary (stdVertices n)
          (stdVertices_affineIndependent n)).nonempty_of_mem_faces hσ)⟩
      · exact ⟨fun u hu => by
          rw [Finset.mem_singleton] at hu
          subst u
          exact ⟨hTne, Finset.Subset.refl (stdVertices n)⟩,
          fun u hu v hv => by
            rw [Finset.mem_singleton] at hu hv
            subst u
            subst v
            exact Or.inl (Finset.Subset.refl (stdVertices n))⟩
      · intro u hu
        rw [Finset.mem_singleton] at hu
        subst u
        exact fun h =>
          (mem_simplexBoundary_faces_iff.mp ((hmem (stdVertices n)).mp h)).2.2 rfl
      · intro u hu v hv
        rw [Finset.mem_singleton] at hu
        subst u
        exact subset_convexHull ℝ
          (((stdVertices n : Finset (Fin (n + 2) → ℝ))) : Set (Fin (n + 2) → ℝ))
          (Finset.mem_coe.mpr
            ((mem_simplexBoundary_faces_iff.mp hσ).1 (Finset.mem_coe.mp hv)))

open Classical in
theorem isPLSphere_double_simplexComplex_std (n : ℕ) :
    IsPLSphere (n + 1) (double (n + 1)
      (simplexComplex (stdVertices n) (stdVertices_affineIndependent n))).space := by
  classical
  let _ : DecidableEq (Fin (n + 2) → ℝ) := Classical.decEq _
  have hsphere := isPLSphere_gluedCone_simplex (stdVertices_affineIndependent n)
    (card_stdVertices n) (centroid_mem_openSimplex
      (Finset.card_pos.mp (by rw [card_stdVertices]; omega)))
  simpa only [double, boundaryRelSubdivision_simplexComplex_std,
    boundaryComplex_simplexComplex_std, classicalConeComplex] using hsphere

open Classical in
theorem exists_isPLHomeomorphOn_double
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {f : E → F} (hf : IsPLHomeomorphOn f K.space L.space) :
    ∃ g : E × E × ℝ → F × F × ℝ,
      IsPLHomeomorphOn g (double (n + 1) K).space (double (n + 1) L).space := by
  classical
  let A₀ := boundaryComplex (n + 1) K
  let R₀ := boundaryRelSubdivision (n + 1) K
  let B := boundaryComplex (n + 1) L
  let R := boundaryRelSubdivision (n + 1) L
  let hA₀finite : Finite A₀.faces := (boundaryComplex_faces_finite (n + 1) K).to_subtype
  let hR₀finite : Finite R₀.faces :=
    (boundaryRelSubdivision_faces_finite (n + 1) K).to_subtype
  let hBfinite : Finite B.faces := (boundaryComplex_faces_finite (n + 1) L).to_subtype
  let hRfinite : Finite R.faces :=
    (boundaryRelSubdivision_faces_finite (n + 1) L).to_subtype
  have hR₀sub : IsSubdivision R₀ K := boundaryRelSubdivision_isSubdivision (n + 1) K
  have hRsub : IsSubdivision R L := boundaryRelSubdivision_isSubdivision (n + 1) L
  have hA₀R₀ : A₀.faces ⊆ R₀.faces :=
    boundaryComplex_faces_subset_boundaryRelSubdivision (n + 1) K
  have hA₀K : A₀.faces ⊆ K.faces := boundaryComplex_faces_subset (n + 1) K
  have hBR : B.faces ⊆ R.faces :=
    boundaryComplex_faces_subset_boundaryRelSubdivision (n + 1) L
  have hBL : B.faces ⊆ L.faces := boundaryComplex_faces_subset (n + 1) L
  let ι₁ := simplicialMap R (glueEmbed₁ B id)
  let ι₂ := simplicialMap L (glueEmbed₂ B id)
  let g₁ := ι₁ ∘ f
  let g₂ := ι₂ ∘ f
  let Y₁ := (glued₁ R B id).space
  let Y₂ := (glued₂ L B id).space
  have hemb₁ := isPLHomeomorphOn_embedComplex R (glueEmbed₁ B id)
    (glueFst F F) (fun _ _ _ _ => rfl)
  have hemb₂ := isPLHomeomorphOn_embedComplex L (glueEmbed₂ B id)
    (glueSnd F F) (fun _ _ _ _ => rfl)
  have hfR : IsPLHomeomorphOn f K.space R.space := by
    rw [hRsub.space_eq]
    exact hf
  have hg₁ : IsPLHomeomorphOn g₁ R₀.space Y₁ := by
    rw [hR₀sub.space_eq]
    exact hfR.trans hemb₁
  have hg₂ : IsPLHomeomorphOn g₂ K.space Y₂ := hf.trans hemb₂
  have hBimage : B.space = f '' A₀.space := by
    exact boundaryComplex_space_of_isPLHomeomorphOn K L hK hf
  have hcompat : ∀ x ∈ A₀.space, g₂ (simplicialMap A₀ id x) = g₁ x := by
    intro x hx
    rw [simplicialMap_id_eq_of_mem A₀ hx]
    have hfx : f x ∈ B.space := by
      rw [hBimage]
      exact ⟨x, hx, rfl⟩
    exact (simplicialMap_glueEmbed_id_eq R L B hBR hBL hfx).symm
  have hoverlap : Y₁ ∩ Y₂ = g₁ '' A₀.space := by
    calc
      Y₁ ∩ Y₂ = ι₁ '' B.space :=
        glued₁_space_inter_glued₂_space R L (isGlueIso_id B) hBR hBL
          (boundaryComplex_full_boundaryRelSubdivision (n + 1) L)
      _ = ι₁ '' (f '' A₀.space) := by rw [← hBimage]
      _ = g₁ '' A₀.space := by rw [Set.image_image]; rfl
  have hmap := isPLHomeomorphOn_gluedMap_of_full R₀ K A₀ A₀ id id
    (isGlueIso_id A₀) hA₀R₀ hA₀K
    (boundaryComplex_full_boundaryRelSubdivision (n + 1) K)
    g₁ g₂ Y₁ Y₂ hg₁ hg₂ hcompat hoverlap
  rw [← gluedComplex_space R L (isGlueIso_id B) hBL
    (boundaryComplex_full_boundaryRelSubdivision (n + 1) L)] at hmap
  have hdouble : IsPLHomeomorphOn
      (gluedMap R₀ A₀ id g₁ g₂) (double (n + 1) K).space
        (double (n + 1) L).space := by
    simpa only [double, A₀, R₀, B, R] using hmap
  exact ⟨_, hdouble⟩

open Classical in
theorem isPLSphere_double_of_isPLBall
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsPLBall (n + 1) K.space) :
    IsPLSphere (n + 1) (double (n + 1) K).space := by
  classical
  obtain ⟨f, hf⟩ := hK
  let S := simplexComplex (stdVertices n) (stdVertices_affineIndependent n)
  let hSfinite : Finite S.faces :=
    (simplexComplex_faces_finite (stdVertices n) (stdVertices_affineIndependent n)).to_subtype
  have hTne : (stdVertices n).Nonempty := Finset.card_pos.mp (by rw [card_stdVertices]; omega)
  have hSspace : S.space = stdSimplex ℝ (Fin (n + 2)) := by
    rw [simplexComplex_space _ _ hTne, convexHull_stdVertices]
  have hSball : IsPLBall (n + 1) S.space := by
    rw [hSspace]
    exact ⟨id, isPLHomeomorphOn_id_of_isHPolytope (isHPolytope_stdSimplex _)⟩
  have hfS : IsPLHomeomorphOn f S.space K.space := by
    rw [hSspace]
    exact hf
  obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_double S K
    hSball.isCombinatorialManifoldWithBoundary hfS
  exact (isPLSphere_double_simplexComplex_std n).of_isPLHomeomorphOn hg

end DifferentialGeometry.Topology.PiecewiseLinear
