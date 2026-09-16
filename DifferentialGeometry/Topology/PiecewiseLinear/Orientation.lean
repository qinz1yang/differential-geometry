import DifferentialGeometry.Topology.PiecewiseLinear.AffineOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.StellarSphere
import DifferentialGeometry.Topology.SimplicialComplex.Incidence
import DifferentialGeometry.Topology.SphereSeparation.PermutationDeletion
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order

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

open Classical in
theorem simplexBoundaryCoefficient_insert (r : LinearOrder E) {t : Finset E} {v : E}
    (hv : v ∉ t) :
    simplexBoundaryCoefficient r (insert v t) t = incidenceSign r (insert v t) v := by
  have hmem : v ∈ insert v t := Finset.mem_insert_self v t
  have herase : @Finset.erase E r.toDecidableEq (insert v t) v = t := by
    ext w
    simp [hv]
  calc
    simplexBoundaryCoefficient r (insert v t) t =
        simplexBoundaryCoefficient r (insert v t)
          (@Finset.erase E r.toDecidableEq (insert v t) v) := by rw [herase]
    _ = incidenceSign r (insert v t) v := simplexBoundaryCoefficient_erase r hmem

open Classical in
theorem simplexBoundaryCoefficient_pair_cancel
    (r : LinearOrder E) {a m p b : Finset E}
    (ham : a ⊆ m) (hamcard : a.card + 1 = m.card)
    (hmb : m ⊆ b) (hmbcard : m.card + 1 = b.card)
    (hap : a ⊆ p) (hapcard : a.card + 1 = p.card)
    (hpb : p ⊆ b) (hmp : m ≠ p) :
    simplexBoundaryCoefficient r b m * simplexBoundaryCoefficient r m a +
      simplexBoundaryCoefficient r b p * simplexBoundaryCoefficient r p a = 0 := by
  obtain ⟨x, hxa, hma⟩ := Finset.exists_eq_insert_iff.mpr ⟨ham, hamcard⟩
  obtain ⟨y, hym, hbm⟩ := Finset.exists_eq_insert_iff.mpr ⟨hmb, hmbcard⟩
  obtain ⟨z, hza, hpz⟩ := Finset.exists_eq_insert_iff.mpr ⟨hap, hapcard⟩
  have hxy : x ≠ y := by
    intro hxy
    apply hym
    rw [← hxy, ← hma]
    exact Finset.mem_insert_self x a
  have hzy : z = y := by
    have hzb : z ∈ b := hpb (hpz ▸ Finset.mem_insert_self z a)
    rw [← hbm, ← hma, Finset.mem_insert, Finset.mem_insert] at hzb
    rcases hzb with hzy | hzx | hza'
    · exact hzy
    · exact False.elim (hmp (by rw [← hma, ← hpz, hzx]))
    · exact False.elim (hza hza')
  have hpa : p = insert y a := by rw [← hpz, hzy]
  have hxb : x ∈ b := by
    rw [← hbm, ← hma]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self x a)
  have hyb : y ∈ b := hbm ▸ Finset.mem_insert_self y m
  have hby : @Finset.erase E r.toDecidableEq b y = m := by
    rw [← hbm]
    have hdec : r.toDecidableEq = Classical.decEq E := Subsingleton.elim _ _
    rw [hdec]
    ext w
    simp [hym]
  have hbx : @Finset.erase E r.toDecidableEq b x = p := by
    have hbp : b = insert x p := by
      rw [← hbm, ← hma, hpa, Finset.insert_comm y x]
    rw [hbp]
    have hxp : x ∉ p := by
      rw [hpa]
      simp [hxy, hxa]
    have hdec : r.toDecidableEq = Classical.decEq E := Subsingleton.elim _ _
    rw [hdec]
    ext w
    simp [hxp]
  have hbmCoefficient : simplexBoundaryCoefficient r b m = incidenceSign r b y := by
    rw [← hby]
    exact simplexBoundaryCoefficient_erase r hyb
  have hbpCoefficient : simplexBoundaryCoefficient r b p = incidenceSign r b x := by
    rw [← hbx]
    exact simplexBoundaryCoefficient_erase r hxb
  have hmaCoefficient : simplexBoundaryCoefficient r m a = incidenceSign r m x := by
    have hxm : x ∈ m := hma ▸ Finset.mem_insert_self x a
    have hmx : @Finset.erase E r.toDecidableEq m x = a := by
      rw [← hma]
      have hdec : r.toDecidableEq = Classical.decEq E := Subsingleton.elim _ _
      rw [hdec]
      ext w
      simp [hxa]
    rw [← hmx]
    exact simplexBoundaryCoefficient_erase r hxm
  have hpaCoefficient : simplexBoundaryCoefficient r p a = incidenceSign r p y := by
    have hyp : y ∈ p := hpa ▸ Finset.mem_insert_self y a
    have hpy : @Finset.erase E r.toDecidableEq p y = a := by
      rw [hpa]
      have hdec : r.toDecidableEq = Classical.decEq E := Subsingleton.elim _ _
      rw [hdec]
      ext w
      simp [hzy ▸ hza]
    rw [← hpy]
    exact simplexBoundaryCoefficient_erase r hyp
  have hsign := incidenceSign_pair r hyb hxb hxy.symm
  rw [hby, hbx] at hsign
  rw [hbmCoefficient, hmaCoefficient, hbpCoefficient, hpaCoefficient, hsign]
  ring

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

open Classical in
theorem IsCombinatorialManifold.card_faceCofaces_eq_two
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifold (n + 1) K)
    {s : Finset E} (hs : s ∈ K.faces) (hscard : s.card = n + 1) :
    (faceCofaces K s (n + 2)).card = 2 := by
  obtain ⟨a, b, hab, habset⟩ := hK.codimension_one_cofaces K hs hscard
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
theorem isOrientable_zero
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] : IsOrientable 0 K := by
  refine ⟨{
    vertexOrder := linearOrderOfSTO WellOrderingRel
    sign := fun _ => 1
    sign_top := fun _ _ _ => Or.inl rfl
    coherent := ?_
  }⟩
  intro t ht hcard _
  exact ((K.nonempty_of_mem_faces ht).ne_empty (Finset.card_eq_zero.mp hcard)).elim

open Classical in
noncomputable def complexVertexFinset
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] : Finset E :=
  ((Set.toFinite K.faces).preimage Finset.singleton_injective.injOn).toFinset

open Classical in
theorem mem_complexVertexFinset
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (x : E) :
    x ∈ complexVertexFinset K ↔ {x} ∈ K.faces := by
  exact ((Set.toFinite K.faces).preimage Finset.singleton_injective.injOn).mem_toFinset

def finiteOrderRank {X : Type*} (r : LinearOrder X) (V : Finset X) (x : X) : ℕ :=
  let _ := r
  (V.filter fun y => y < x).card

theorem finiteOrderRank_mono {X : Type*} (r : LinearOrder X) (V : Finset X)
    {x y : X} (hxy : @LT.lt X r.toLT x y) :
    finiteOrderRank r V x ≤ finiteOrderRank r V y := by
  let _ := r
  unfold finiteOrderRank
  apply Finset.card_le_card
  intro z hz
  rw [Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, lt_trans hz.2 hxy⟩

theorem finiteOrderRank_lt_of_mem {X : Type*} (r : LinearOrder X) (V : Finset X)
    {x y : X} (hx : x ∈ V) (hxy : @LT.lt X r.toLT x y) :
    finiteOrderRank r V x < finiteOrderRank r V y := by
  let _ := r
  unfold finiteOrderRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, lt_trans hz.2 hxy⟩
  · intro heq
    have hxRight : x ∈ V.filter (fun z => z < y) := Finset.mem_filter.mpr ⟨hx, hxy⟩
    rw [← heq, Finset.mem_filter] at hxRight
    exact (lt_irrefl x hxRight.2).elim

theorem finiteOrderRank_eq_of_lt_iff {X : Type*}
    (r₁ r₂ : LinearOrder X) (V : Finset X) (x : X)
    (h : ∀ y ∈ V, @LT.lt X r₁.toLT y x ↔ @LT.lt X r₂.toLT y x) :
    finiteOrderRank r₁ V x = finiteOrderRank r₂ V x := by
  unfold finiteOrderRank
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_filter]
  exact and_congr_right fun hy => h y hy

open Classical in
noncomputable def orderAmalgamCode {X : Type*}
    (r₁ r₂ : LinearOrder X) (V₁ V₂ A : Finset X) (x : X) :
    ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  if x ∈ A then
      toLex (finiteOrderRank r₁ A x, toLex (2, 0))
    else if x ∈ V₁ then
      toLex (finiteOrderRank r₁ A x, toLex (0, finiteOrderRank r₁ V₁ x))
    else if x ∈ V₂ then
      toLex (finiteOrderRank r₂ A x, toLex (1, finiteOrderRank r₂ V₂ x))
    else
      toLex (0, toLex (3, 0))

open Classical in
structure OrderAmalgamTie (X : Type*) where
  val : X

open Classical in
noncomputable instance {X : Type*} : LinearOrder (OrderAmalgamTie X) :=
  linearOrderOfSTO WellOrderingRel

open Classical in
noncomputable def orderAmalgamKey {X : Type*}
    (r₁ r₂ : LinearOrder X) (V₁ V₂ A : Finset X) (x : X) :
    (ℕ ×ₗ (ℕ ×ₗ ℕ)) ×ₗ OrderAmalgamTie X :=
  toLex (orderAmalgamCode r₁ r₂ V₁ V₂ A x, ⟨x⟩)

open Classical in
theorem orderAmalgamKey_injective {X : Type*}
    (r₁ r₂ : LinearOrder X) (V₁ V₂ A : Finset X) :
    Function.Injective (orderAmalgamKey r₁ r₂ V₁ V₂ A) := by
  intro x y hxy
  have hlast := congrArg
    (fun z : (ℕ ×ₗ (ℕ ×ₗ ℕ)) ×ₗ OrderAmalgamTie X => z.2.val) hxy
  exact hlast

open Classical in
@[instance_reducible]
noncomputable def orderAmalgam {X : Type*}
    (r₁ r₂ : LinearOrder X) (V₁ V₂ A : Finset X) : LinearOrder X :=
  LinearOrder.lift' (orderAmalgamKey r₁ r₂ V₁ V₂ A)
    (orderAmalgamKey_injective r₁ r₂ V₁ V₂ A)

open Classical in
theorem orderAmalgamCode_lt_of_mem_left {X : Type*}
    (r₁ r₂ : LinearOrder X) {V₁ V₂ A : Finset X} {x y : X}
    (hxV : x ∈ V₁) (hyV : y ∈ V₁) (hxy : @LT.lt X r₁.toLT x y) :
    orderAmalgamCode r₁ r₂ V₁ V₂ A x < orderAmalgamCode r₁ r₂ V₁ V₂ A y := by
  by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
  · rw [orderAmalgamCode, if_pos hxA, orderAmalgamCode, if_pos hyA,
      Prod.Lex.toLex_lt_toLex]
    exact Or.inl (finiteOrderRank_lt_of_mem r₁ A hxA hxy)
  · rw [orderAmalgamCode, if_pos hxA, orderAmalgamCode, if_neg hyA, if_pos hyV,
      Prod.Lex.toLex_lt_toLex]
    exact Or.inl (finiteOrderRank_lt_of_mem r₁ A hxA hxy)
  · have hmono := finiteOrderRank_mono r₁ A hxy
    rw [orderAmalgamCode, if_neg hxA, if_pos hxV, orderAmalgamCode, if_pos hyA,
      Prod.Lex.toLex_lt_toLex]
    rcases hmono.lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl (by omega)
  · have hmono := finiteOrderRank_mono r₁ A hxy
    rw [orderAmalgamCode, if_neg hxA, if_pos hxV, orderAmalgamCode, if_neg hyA,
      if_pos hyV, Prod.Lex.toLex_lt_toLex]
    rcases hmono.lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      rw [Prod.Lex.toLex_lt_toLex]
      refine Or.inr ⟨rfl, ?_⟩
      exact finiteOrderRank_lt_of_mem r₁ V₁ hxV hxy

open Classical in
theorem orderAmalgamCode_lt_of_mem_right {X : Type*}
    (r₁ r₂ : LinearOrder X) {V₁ V₂ A : Finset X} {x y : X}
    (hinter : V₁ ∩ V₂ ⊆ A)
    (hagree : ∀ a ∈ A, ∀ b ∈ A,
      (@LT.lt X r₁.toLT a b ↔ @LT.lt X r₂.toLT a b))
    (hxV : x ∈ V₂) (hyV : y ∈ V₂) (hxy : @LT.lt X r₂.toLT x y) :
    orderAmalgamCode r₁ r₂ V₁ V₂ A x < orderAmalgamCode r₁ r₂ V₁ V₂ A y := by
  have hArank (z : X) (hz : z ∈ A) :
      finiteOrderRank r₁ A z = finiteOrderRank r₂ A z :=
    finiteOrderRank_eq_of_lt_iff r₁ r₂ A z (fun a ha => hagree a ha z hz)
  by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
  · have hxy₁ : @LT.lt X r₁.toLT x y := (hagree x hxA y hyA).mpr hxy
    rw [orderAmalgamCode, if_pos hxA, orderAmalgamCode, if_pos hyA,
      Prod.Lex.toLex_lt_toLex]
    exact Or.inl (finiteOrderRank_lt_of_mem r₁ A hxA hxy₁)
  · have hyNotV₁ : y ∉ V₁ := by
      intro hyV₁
      exact hyA (hinter (Finset.mem_inter.mpr ⟨hyV₁, hyV⟩))
    have hlt := finiteOrderRank_lt_of_mem r₂ A hxA hxy
    rw [orderAmalgamCode, if_pos hxA, orderAmalgamCode, if_neg hyA,
      if_neg hyNotV₁, if_pos hyV, Prod.Lex.toLex_lt_toLex, hArank x hxA]
    exact Or.inl hlt
  · have hxNotV₁ : x ∉ V₁ := by
      intro hxV₁
      exact hxA (hinter (Finset.mem_inter.mpr ⟨hxV₁, hxV⟩))
    have hmono := finiteOrderRank_mono r₂ A hxy
    rw [orderAmalgamCode, if_neg hxA, if_neg hxNotV₁, if_pos hxV,
      orderAmalgamCode, if_pos hyA, Prod.Lex.toLex_lt_toLex, hArank y hyA]
    rcases hmono.lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl (by omega)
  · have hxNotV₁ : x ∉ V₁ := by
      intro hxV₁
      exact hxA (hinter (Finset.mem_inter.mpr ⟨hxV₁, hxV⟩))
    have hyNotV₁ : y ∉ V₁ := by
      intro hyV₁
      exact hyA (hinter (Finset.mem_inter.mpr ⟨hyV₁, hyV⟩))
    have hmono := finiteOrderRank_mono r₂ A hxy
    rw [orderAmalgamCode, if_neg hxA, if_neg hxNotV₁, if_pos hxV,
      orderAmalgamCode, if_neg hyA, if_neg hyNotV₁, if_pos hyV,
      Prod.Lex.toLex_lt_toLex]
    rcases hmono.lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      rw [Prod.Lex.toLex_lt_toLex]
      refine Or.inr ⟨rfl, ?_⟩
      exact finiteOrderRank_lt_of_mem r₂ V₂ hxV hxy

open Classical in
theorem orderAmalgamKey_lt_of_code_lt {X : Type*}
    (r₁ r₂ : LinearOrder X) (V₁ V₂ A : Finset X) {x y : X}
    (h : orderAmalgamCode r₁ r₂ V₁ V₂ A x <
      orderAmalgamCode r₁ r₂ V₁ V₂ A y) :
    orderAmalgamKey r₁ r₂ V₁ V₂ A x < orderAmalgamKey r₁ r₂ V₁ V₂ A y := by
  change toLex (orderAmalgamCode r₁ r₂ V₁ V₂ A x, (⟨x⟩ : OrderAmalgamTie X)) <
    toLex (orderAmalgamCode r₁ r₂ V₁ V₂ A y, (⟨y⟩ : OrderAmalgamTie X))
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

open Classical in
theorem orderAmalgam_lt_iff_left {X : Type*}
    (r₁ r₂ : LinearOrder X) {V₁ V₂ A : Finset X} {x y : X}
    (hxV : x ∈ V₁) (hyV : y ∈ V₁) :
    let _ := orderAmalgam r₁ r₂ V₁ V₂ A
    x < y ↔ @LT.lt X r₁.toLT x y := by
  change orderAmalgamKey r₁ r₂ V₁ V₂ A x < orderAmalgamKey r₁ r₂ V₁ V₂ A y ↔ _
  constructor
  · intro hkey
    let _ := r₁
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · exact hxy
    · subst y
      exact False.elim (lt_irrefl _ hkey)
    · have hreverse := orderAmalgamKey_lt_of_code_lt r₁ r₂ V₁ V₂ A
        (orderAmalgamCode_lt_of_mem_left r₁ r₂ hyV hxV hyx)
      exact False.elim (asymm hkey hreverse)
  · intro hxy
    exact orderAmalgamKey_lt_of_code_lt r₁ r₂ V₁ V₂ A
      (orderAmalgamCode_lt_of_mem_left r₁ r₂ hxV hyV hxy)

open Classical in
theorem orderAmalgam_lt_iff_right {X : Type*}
    (r₁ r₂ : LinearOrder X) {V₁ V₂ A : Finset X}
    (hinter : V₁ ∩ V₂ ⊆ A)
    (hagree : ∀ a ∈ A, ∀ b ∈ A,
      (@LT.lt X r₁.toLT a b ↔ @LT.lt X r₂.toLT a b))
    {x y : X} (hxV : x ∈ V₂) (hyV : y ∈ V₂) :
    let _ := orderAmalgam r₁ r₂ V₁ V₂ A
    x < y ↔ @LT.lt X r₂.toLT x y := by
  change orderAmalgamKey r₁ r₂ V₁ V₂ A x < orderAmalgamKey r₁ r₂ V₁ V₂ A y ↔ _
  constructor
  · intro hkey
    let _ := r₂
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · exact hxy
    · subst y
      exact False.elim (lt_irrefl _ hkey)
    · have hreverse := orderAmalgamKey_lt_of_code_lt r₁ r₂ V₁ V₂ A
        (orderAmalgamCode_lt_of_mem_right r₁ r₂ hinter hagree hyV hxV hyx)
      exact False.elim (asymm hkey hreverse)
  · intro hxy
    exact orderAmalgamKey_lt_of_code_lt r₁ r₂ V₁ V₂ A
      (orderAmalgamCode_lt_of_mem_right r₁ r₂ hinter hagree hxV hyV hxy)

open Classical in
noncomputable def orientationVertexKey
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Geometry.SimplicialComplex ℝ F) (ψ : F → E) (y : F) : E ⊕ₗ F :=
  if {y} ∈ L.faces then toLex (Sum.inl (ψ y)) else toLex (Sum.inr y)

open Classical in
theorem orientationVertexKey_injective
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Geometry.SimplicialComplex ℝ E} {L : Geometry.SimplicialComplex ℝ F}
    {φ : E → F} {ψ : F → E} (h : IsGlueIso K L φ ψ) :
    Function.Injective (orientationVertexKey L ψ) := by
  intro y z hyz
  by_cases hy : {y} ∈ L.faces <;> by_cases hz : {z} ∈ L.faces
  · have hψ : ψ y = ψ z := by
      simpa [orientationVertexKey, hy, hz] using hyz
    calc
      y = φ (ψ y) := (h.right {y} hy y (Finset.mem_singleton_self y)).symm
      _ = φ (ψ z) := by rw [hψ]
      _ = z := h.right {z} hz z (Finset.mem_singleton_self z)
  · simp [orientationVertexKey, hy, hz] at hyz
  · simp [orientationVertexKey, hy, hz] at hyz
  · simpa [orientationVertexKey, hy, hz] using hyz

open Classical in
@[instance_reducible]
noncomputable def CoherentOrientation.mapVertexOrder
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} {φ : E → F} {ψ : F → E}
    (o : CoherentOrientation n K) (h : IsGlueIso K L φ ψ) : LinearOrder F := by
  let _ : LinearOrder E := o.vertexOrder
  let _ : LinearOrder F := linearOrderOfSTO WellOrderingRel
  exact LinearOrder.lift' (orientationVertexKey L ψ) (orientationVertexKey_injective h)

open Classical in
theorem CoherentOrientation.mapVertexOrder_lt_iff
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} {φ : E → F} {ψ : F → E}
    (o : CoherentOrientation n K) (h : IsGlueIso K L φ ψ)
    {y z : F} (hy : {y} ∈ L.faces) (hz : {z} ∈ L.faces) :
    let _ := o.mapVertexOrder h
    y < z ↔ let _ := o.vertexOrder; ψ y < ψ z := by
  let _ : LinearOrder E := o.vertexOrder
  let _ : LinearOrder F := linearOrderOfSTO WellOrderingRel
  change orientationVertexKey L ψ y < orientationVertexKey L ψ z ↔ ψ y < ψ z
  simp [orientationVertexKey, hy, hz]

open Classical in
theorem CoherentOrientation.incidenceIndex_mapVertexOrder
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} {φ : E → F} {ψ : F → E}
    (o : CoherentOrientation n K) (h : IsGlueIso K L φ ψ)
    {s : Finset F} (hs : s ∈ L.faces) {y : F} (hy : y ∈ s) :
    incidenceIndex (o.mapVertexOrder h) s y =
      incidenceIndex o.vertexOrder (s.image ψ) (ψ y) := by
  have hvertex (w : F) (hw : w ∈ s) : {w} ∈ L.faces :=
    L.down_closed hs (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)
  have hinj : Set.InjOn ψ (s : Set F) := by
    intro u hu v hv huv
    calc
      u = φ (ψ u) := (h.right s hs u (Finset.mem_coe.mp hu)).symm
      _ = φ (ψ v) := by rw [huv]
      _ = v := h.right s hs v (Finset.mem_coe.mp hv)
  have hfilter :
      (s.filter fun w => @LT.lt F (o.mapVertexOrder h).toLT w y).image ψ =
        (s.image ψ).filter fun z => @LT.lt E o.vertexOrder.toLT z (ψ y) := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      have hw' := Finset.mem_filter.mp hw
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image_of_mem ψ hw'.1, ?_⟩
      exact (o.mapVertexOrder_lt_iff h (hvertex w hw'.1) (hvertex y hy)).mp hw'.2
    · intro hz
      have hz' := Finset.mem_filter.mp hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz'.1
      apply Finset.mem_image.mpr
      refine ⟨w, Finset.mem_filter.mpr ⟨hw, ?_⟩, rfl⟩
      exact (o.mapVertexOrder_lt_iff h (hvertex w hw) (hvertex y hy)).mpr hz'.2
  change (s.filter fun w => @LT.lt F (o.mapVertexOrder h).toLT w y).card =
    ((s.image ψ).filter fun z => @LT.lt E o.vertexOrder.toLT z (ψ y)).card
  calc
    _ = ((s.filter fun w => @LT.lt F (o.mapVertexOrder h).toLT w y).image ψ).card :=
      (Finset.card_image_of_injOn (hinj.mono fun w hw =>
        Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).1)).symm
    _ = _ := congrArg Finset.card hfilter

open Classical in
theorem CoherentOrientation.incidenceSign_mapVertexOrder
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} {φ : E → F} {ψ : F → E}
    (o : CoherentOrientation n K) (h : IsGlueIso K L φ ψ)
    {s : Finset F} (hs : s ∈ L.faces) {y : F} (hy : y ∈ s) :
    incidenceSign (o.mapVertexOrder h) s y =
      incidenceSign o.vertexOrder (s.image ψ) (ψ y) := by
  rw [incidenceSign, incidenceSign, o.incidenceIndex_mapVertexOrder h hs hy]

open Classical in
theorem IsGlueIso.injOn_right_face
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Geometry.SimplicialComplex ℝ E} {L : Geometry.SimplicialComplex ℝ F}
    {φ : E → F} {ψ : F → E} (h : IsGlueIso K L φ ψ)
    {s : Finset F} (hs : s ∈ L.faces) : Set.InjOn ψ (s : Set F) := by
  intro u hu v hv huv
  calc
    u = φ (ψ u) := (h.right s hs u (Finset.mem_coe.mp hu)).symm
    _ = φ (ψ v) := by rw [huv]
    _ = v := h.right s hs v (Finset.mem_coe.mp hv)

open Classical in
theorem IsGlueIso.image_faceCofaces_right
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} [Finite L.faces]
    {φ : E → F} {ψ : F → E} (h : IsGlueIso K L φ ψ)
    {t : Finset F} (ht : t ∈ L.faces) (k : ℕ) :
    (faceCofaces L t k).image (fun s => s.image ψ) =
      faceCofaces K (t.image ψ) k := by
  ext q
  constructor
  · intro hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hsL, hscard, hts⟩ := (mem_faceCofaces L).mp hs
    apply (mem_faceCofaces K).mpr
    refine ⟨h.image₂ s hsL, ?_, Finset.image_mono ψ hts⟩
    rw [Finset.card_image_of_injOn (h.injOn_right_face hsL), hscard]
  · intro hq
    obtain ⟨hqK, hqcard, htq⟩ := (mem_faceCofaces K).mp hq
    let s := q.image φ
    have hsL : s ∈ L.faces := h.image₁ q hqK
    have hst : t ⊆ s := by
      intro y hy
      apply Finset.mem_image.mpr
      refine ⟨ψ y, htq (Finset.mem_image_of_mem ψ hy), ?_⟩
      exact h.right t ht y hy
    have hscard : s.card = k := by
      rw [Finset.card_image_of_injOn (h.symm.injOn_right_face hqK), hqcard]
    apply Finset.mem_image.mpr
    refine ⟨s, (mem_faceCofaces L).mpr ⟨hsL, hscard, hst⟩, ?_⟩
    exact h.image_image_left hqK

open Classical in
theorem IsGlueIso.card_faceCofaces_right
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} [Finite L.faces]
    {φ : E → F} {ψ : F → E} (h : IsGlueIso K L φ ψ)
    {t : Finset F} (ht : t ∈ L.faces) (k : ℕ) :
    (faceCofaces L t k).card = (faceCofaces K (t.image ψ) k).card := by
  have hinj : Set.InjOn (fun s : Finset F => s.image ψ) (faceCofaces L t k : Set (Finset F)) := by
    intro s hs u hu hsu
    have hsL := ((mem_faceCofaces L).mp (Finset.mem_coe.mp hs)).1
    have huL := ((mem_faceCofaces L).mp (Finset.mem_coe.mp hu)).1
    calc
      s = (s.image ψ).image φ := (h.image_image_right hsL).symm
      _ = (u.image ψ).image φ := congrArg (fun q => q.image φ) hsu
      _ = u := h.image_image_right huL
  calc
    (faceCofaces L t k).card =
        ((faceCofaces L t k).image fun s => s.image ψ).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = (faceCofaces K (t.image ψ) k).card := by
      rw [h.image_faceCofaces_right ht k]

open Classical in
theorem image_erase_of_injOn
    {A B : Type*} {f : A → B} {s : Finset A} {a : A}
    (hf : Set.InjOn f (s : Set A)) (ha : a ∈ s) :
    (s.erase a).image f = (s.image f).erase (f a) := by
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hw' := Finset.mem_erase.mp hw
    exact Finset.mem_erase.mpr
      ⟨fun heq => hw'.1 (hf (Finset.mem_coe.mpr hw'.2) (Finset.mem_coe.mpr ha) heq),
        Finset.mem_image_of_mem f hw'.2⟩
  · exact Finset.erase_image_subset_image_erase f s a

open Classical in
theorem CoherentOrientation.simplexBoundaryCoefficient_mapVertexOrder
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} {φ : E → F} {ψ : F → E}
    (o : CoherentOrientation n K) (h : IsGlueIso K L φ ψ)
    {s t : Finset F} (hs : s ∈ L.faces) (hts : t ⊆ s)
    (hcard : t.card + 1 = s.card) :
    simplexBoundaryCoefficient (o.mapVertexOrder h) s t =
      simplexBoundaryCoefficient o.vertexOrder (s.image ψ) (t.image ψ) := by
  obtain ⟨y, hyt, hys⟩ := Finset.exists_eq_insert_iff.mpr ⟨hts, hcard⟩
  have hysmem : y ∈ s := hys ▸ Finset.mem_insert_self y t
  have herase : s.erase y = t := by
    rw [← hys, Finset.erase_insert hyt]
  let tF := @Finset.erase F (o.mapVertexOrder h).toDecidableEq s y
  let tE := @Finset.erase E o.vertexOrder.toDecidableEq (s.image ψ) (ψ y)
  have htF : tF = t := by
    calc
      tF = s.erase y := by ext z; simp [tF]
      _ = t := herase
  have htE : tE = t.image ψ := by
    calc
      tE = (s.image ψ).erase (ψ y) := by ext z; simp [tE]
      _ = (s.erase y).image ψ :=
        (image_erase_of_injOn (h.injOn_right_face hs) hysmem).symm
      _ = t.image ψ := by rw [herase]
  calc
    simplexBoundaryCoefficient (o.mapVertexOrder h) s t =
        simplexBoundaryCoefficient (o.mapVertexOrder h) s tF := by rw [htF]
    _ =
        incidenceSign (o.mapVertexOrder h) s y :=
      simplexBoundaryCoefficient_erase (o.mapVertexOrder h) hysmem
    _ = incidenceSign o.vertexOrder (s.image ψ) (ψ y) :=
      o.incidenceSign_mapVertexOrder h hs hysmem
    _ = simplexBoundaryCoefficient o.vertexOrder (s.image ψ)
        tE :=
      (simplexBoundaryCoefficient_erase o.vertexOrder
        (Finset.mem_image_of_mem ψ hysmem)).symm
    _ = simplexBoundaryCoefficient o.vertexOrder (s.image ψ) (t.image ψ) := by rw [htE]

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

theorem incidenceIndex_eq_of_lt_iff
    (r₁ r₂ : LinearOrder E) (s : Finset E) (v : E)
    (h : ∀ w ∈ s, @LT.lt E r₁.toLT w v ↔ @LT.lt E r₂.toLT w v) :
    incidenceIndex r₁ s v = incidenceIndex r₂ s v := by
  unfold incidenceIndex
  apply congrArg Finset.card
  ext w
  simp only [Finset.mem_filter]
  exact and_congr_right fun hw => h w hw

open Classical in
theorem simplexBoundaryCoefficient_eq_of_lt_iff
    (r₁ r₂ : LinearOrder E) {s t : Finset E}
    (hts : t ⊆ s) (hcard : t.card + 1 = s.card)
    (h : ∀ v ∈ s, ∀ w ∈ s,
      (@LT.lt E r₁.toLT v w ↔ @LT.lt E r₂.toLT v w)) :
    simplexBoundaryCoefficient r₁ s t = simplexBoundaryCoefficient r₂ s t := by
  obtain ⟨v, hvt, hsv⟩ := Finset.exists_eq_insert_iff.mpr ⟨hts, hcard⟩
  have hv : v ∈ s := hsv ▸ Finset.mem_insert_self v t
  have erase_eq (d : DecidableEq E) : @Finset.erase E d s v = t := by
    rw [← hsv]
    ext w
    simp only [Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hwv, hwv' | hwt⟩
      · exact False.elim (hwv hwv')
      · exact hwt
    · intro hwt
      exact ⟨fun hwv => hvt (hwv ▸ hwt), Or.inr hwt⟩
  have herase₁ : @Finset.erase E r₁.toDecidableEq s v = t := erase_eq _
  have herase₂ : @Finset.erase E r₂.toDecidableEq s v = t := erase_eq _
  have hindex : incidenceIndex r₁ s v = incidenceIndex r₂ s v :=
    incidenceIndex_eq_of_lt_iff r₁ r₂ s v (fun w hw => h w hw v hv)
  calc
    simplexBoundaryCoefficient r₁ s t =
        simplexBoundaryCoefficient r₁ s (@Finset.erase E r₁.toDecidableEq s v) := by
      rw [herase₁]
    _ = incidenceSign r₁ s v := simplexBoundaryCoefficient_erase r₁ hv
    _ = incidenceSign r₂ s v := by rw [incidenceSign, incidenceSign, hindex]
    _ = simplexBoundaryCoefficient r₂ s (@Finset.erase E r₂.toDecidableEq s v) :=
      (simplexBoundaryCoefficient_erase r₂ hv).symm
    _ = simplexBoundaryCoefficient r₂ s t := by rw [herase₂]

open Classical in
noncomputable def CoherentOrientation.withVertexOrder
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation n K) (r : LinearOrder E)
    (h : ∀ v w, {v} ∈ K.faces → {w} ∈ K.faces →
      (@LT.lt E r.toLT v w ↔ @LT.lt E o.vertexOrder.toLT v w)) :
    CoherentOrientation n K where
  vertexOrder := r
  sign := o.sign
  sign_top := o.sign_top
  coherent := by
    intro t ht htcard hnotone
    rw [orientedBoundary_eq_sum_faceCofaces]
    have hold := o.coherent t ht htcard hnotone
    rw [orientedBoundary_eq_sum_faceCofaces] at hold
    calc
      (∑ s ∈ faceCofaces K t (n + 1),
          o.sign s * simplexBoundaryCoefficient r s t) =
          ∑ s ∈ faceCofaces K t (n + 1),
            o.sign s * simplexBoundaryCoefficient o.vertexOrder s t := by
        apply Finset.sum_congr rfl
        intro s hs
        obtain ⟨hsK, hscard, hts⟩ := (mem_faceCofaces K).mp hs
        congr 1
        apply simplexBoundaryCoefficient_eq_of_lt_iff r o.vertexOrder hts
          (by omega)
        intro v hv w hw
        apply h v w
        · exact K.down_closed hsK (Finset.singleton_subset_iff.mpr hv)
            (Finset.singleton_nonempty v)
        · exact K.down_closed hsK (Finset.singleton_subset_iff.mpr hw)
            (Finset.singleton_nonempty w)
      _ = 0 := hold

open Classical in
noncomputable def CoherentOrientation.neg
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation n K) : CoherentOrientation n K where
  vertexOrder := o.vertexOrder
  sign := fun s => -o.sign s
  sign_top := by
    intro s hs hscard
    rcases o.sign_top s hs hscard with hsone | hsneg
    · right
      rw [hsone]
    · left
      rw [hsneg]
      norm_num
  coherent := by
    intro t ht htcard hnotone
    rw [orientedBoundary_eq_sum_faceCofaces]
    calc
      (∑ s ∈ faceCofaces K t (n + 1),
          -o.sign s * simplexBoundaryCoefficient o.vertexOrder s t) =
          -(∑ s ∈ faceCofaces K t (n + 1),
            o.sign s * simplexBoundaryCoefficient o.vertexOrder s t) := by
        simp_rw [neg_mul]
        rw [Finset.sum_neg_distrib]
      _ = 0 := by
        rw [← orientedBoundary_eq_sum_faceCofaces,
          o.coherent t ht htcard hnotone, neg_zero]

open Classical in
theorem CoherentOrientation.orientedBoundary_mapVertexOrder
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} [Finite L.faces]
    {φ : E → F} {ψ : F → E}
    (o : CoherentOrientation n K) (h : IsGlueIso K L φ ψ)
    {t : Finset F} (ht : t ∈ L.faces) (htcard : t.card = n) :
    orientedBoundary (o.mapVertexOrder h) L n (fun s => o.sign (s.image ψ)) t =
      orientedBoundary o.vertexOrder K n o.sign (t.image ψ) := by
  rw [orientedBoundary_eq_sum_faceCofaces, orientedBoundary_eq_sum_faceCofaces,
    ← h.image_faceCofaces_right ht (n + 1)]
  have hinj : Set.InjOn (fun s : Finset F => s.image ψ)
      (faceCofaces L t (n + 1) : Set (Finset F)) := by
    intro s hs u hu hsu
    have hsL := ((mem_faceCofaces L).mp (Finset.mem_coe.mp hs)).1
    have huL := ((mem_faceCofaces L).mp (Finset.mem_coe.mp hu)).1
    calc
      s = (s.image ψ).image φ := (h.image_image_right hsL).symm
      _ = (u.image ψ).image φ := congrArg (fun q => q.image φ) hsu
      _ = u := h.image_image_right huL
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro s hs
  obtain ⟨hsL, hscard, hts⟩ := (mem_faceCofaces L).mp hs
  rw [o.simplexBoundaryCoefficient_mapVertexOrder h hsL hts (by omega)]

open Classical in
noncomputable def CoherentOrientation.map
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} [Finite L.faces]
    {φ : E → F} {ψ : F → E}
    (o : CoherentOrientation n K) (h : IsGlueIso K L φ ψ) :
    CoherentOrientation n L where
  vertexOrder := o.mapVertexOrder h
  sign := fun s => o.sign (s.image ψ)
  sign_top := by
    intro s hs hscard
    apply o.sign_top (s.image ψ) (h.image₂ s hs)
    rw [Finset.card_image_of_injOn (h.injOn_right_face hs), hscard]
  coherent := by
    intro t ht htcard hne
    rw [o.orientedBoundary_mapVertexOrder h ht htcard]
    apply o.coherent (t.image ψ) (h.image₂ t ht)
    · rw [Finset.card_image_of_injOn (h.injOn_right_face ht), htcard]
    · intro hone
      apply hne
      rw [h.card_faceCofaces_right ht (n + 1), hone]

open Classical in
theorem IsOrientable.of_isGlueIso
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} [Finite L.faces]
    {φ : E → F} {ψ : F → E} (h : IsGlueIso K L φ ψ)
    (ho : IsOrientable n K) : IsOrientable n L := by
  obtain ⟨o⟩ := ho
  exact ⟨o.map h⟩

open Classical in
theorem isOrientable_iff_of_isGlueIso
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} [Finite L.faces]
    {φ : E → F} {ψ : F → E} (h : IsGlueIso K L φ ψ) :
    IsOrientable n K ↔ IsOrientable n L :=
  ⟨IsOrientable.of_isGlueIso h, IsOrientable.of_isGlueIso h.symm⟩

open Classical in
noncomputable def relativeVertexRank
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (x : E) : Option ℕ :=
  if h : ∃ s ∈ K.faces, s ∉ L.faces ∧ s.centroid ℝ id = x then
    some h.choose.card
  else none

open Classical in
theorem relativeVertexRank_centroid
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) {s : Finset E}
    (hsK : s ∈ K.faces) (hsL : s ∉ L.faces) :
    relativeVertexRank K L (s.centroid ℝ id) = some s.card := by
  rw [relativeVertexRank, dif_pos ⟨s, hsK, hsL, rfl⟩]
  congr 2
  apply injOn_faces_of_mem_openSimplex K (centroid_mem_openSimplex_of_mem_faces K)
    (show Classical.choose (show ∃ t ∈ K.faces,
      t ∉ L.faces ∧ t.centroid ℝ id = s.centroid ℝ id from ⟨s, hsK, hsL, rfl⟩) ∈ K.faces from
      (Classical.choose_spec (show ∃ t ∈ K.faces,
        t ∉ L.faces ∧ t.centroid ℝ id = s.centroid ℝ id from ⟨s, hsK, hsL, rfl⟩)).1)
    hsK
  exact (Classical.choose_spec (show ∃ t ∈ K.faces,
    t ∉ L.faces ∧ t.centroid ℝ id = s.centroid ℝ id from ⟨s, hsK, hsL, rfl⟩)).2.2

open Classical in
theorem relativeVertexRank_eq_none_of_mem_space
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {x : E} (hx : x ∈ L.space) : relativeVertexRank K L x = none := by
  rw [relativeVertexRank, dif_neg]
  rintro ⟨s, hsK, hsL, hsx⟩
  exact c_notMem_space hLK (centroid_mem_openSimplex_of_mem_faces K) hsK hsL (hsx ▸ hx)

open Classical in
noncomputable def relativeOrientationVertexKey
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (x : E) :
    ((OrderDual ℕ ×ₗ E) ⊕ₗ E) :=
  match relativeVertexRank K L x with
  | some k => toLex (Sum.inl (toLex (OrderDual.toDual k, x)))
  | none => toLex (Sum.inr x)

open Classical in
theorem relativeOrientationVertexKey_injective
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) :
    Function.Injective (relativeOrientationVertexKey K L) := by
  intro x y hxy
  unfold relativeOrientationVertexKey at hxy
  split at hxy <;> split at hxy <;> simp_all

open Classical in
@[instance_reducible]
noncomputable def CoherentOrientation.relativeVertexOrder
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation n K) (L : Geometry.SimplicialComplex ℝ E) : LinearOrder E := by
  let _ : LinearOrder E := o.vertexOrder
  exact LinearOrder.lift' (relativeOrientationVertexKey K L)
    (relativeOrientationVertexKey_injective K L)

open Classical in
theorem CoherentOrientation.relativeVertexOrder_centroid_lt_centroid
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation n K) (L : Geometry.SimplicialComplex ℝ E)
    {s t : Finset E} (hsK : s ∈ K.faces) (hsL : s ∉ L.faces)
    (htK : t ∈ K.faces) (htL : t ∉ L.faces) (hst : t.card < s.card) :
    let _ := o.relativeVertexOrder L
    s.centroid ℝ id < t.centroid ℝ id := by
  let _ : LinearOrder E := o.vertexOrder
  change relativeOrientationVertexKey K L (s.centroid ℝ id) <
    relativeOrientationVertexKey K L (t.centroid ℝ id)
  rw [relativeOrientationVertexKey, relativeOrientationVertexKey,
    relativeVertexRank_centroid K L hsK hsL, relativeVertexRank_centroid K L htK htL]
  change toLex (Sum.inl (toLex (OrderDual.toDual s.card, s.centroid ℝ id))) <
    toLex (Sum.inl (toLex (OrderDual.toDual t.card, t.centroid ℝ id)))
  rw [Sum.Lex.inl_lt_inl_iff, Prod.Lex.toLex_lt_toLex]
  exact Or.inl hst

open Classical in
theorem CoherentOrientation.relativeVertexOrder_centroid_lt_boundary
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation n K) {L : Geometry.SimplicialComplex ℝ E}
    (hLK : L.faces ⊆ K.faces) {s : Finset E} (hsK : s ∈ K.faces)
    (hsL : s ∉ L.faces) {v : E} (hv : {v} ∈ L.faces) :
    let _ := o.relativeVertexOrder L
    s.centroid ℝ id < v := by
  let _ : LinearOrder E := o.vertexOrder
  have hvspace : v ∈ L.space := L.convexHull_subset_space hv
    (subset_convexHull ℝ _ (by simp))
  change relativeOrientationVertexKey K L (s.centroid ℝ id) <
    relativeOrientationVertexKey K L v
  rw [relativeOrientationVertexKey, relativeOrientationVertexKey,
    relativeVertexRank_centroid K L hsK hsL,
    relativeVertexRank_eq_none_of_mem_space hLK hvspace]
  simp

open Classical in
theorem CoherentOrientation.relativeVertexOrder_boundary_lt_iff
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation n K) {L : Geometry.SimplicialComplex ℝ E}
    (hLK : L.faces ⊆ K.faces) {v w : E} (hv : {v} ∈ L.faces)
    (hw : {w} ∈ L.faces) :
    let _ := o.relativeVertexOrder L
    v < w ↔ let _ := o.vertexOrder; v < w := by
  let _ : LinearOrder E := o.vertexOrder
  have hvspace : v ∈ L.space := L.convexHull_subset_space hv
    (subset_convexHull ℝ _ (by simp))
  have hwspace : w ∈ L.space := L.convexHull_subset_space hw
    (subset_convexHull ℝ _ (by simp))
  change relativeOrientationVertexKey K L v < relativeOrientationVertexKey K L w ↔ v < w
  rw [relativeOrientationVertexKey, relativeOrientationVertexKey,
    relativeVertexRank_eq_none_of_mem_space hLK hvspace,
    relativeVertexRank_eq_none_of_mem_space hLK hwspace]
  simp

open Classical in
theorem CoherentOrientation.relativeIncidenceIndex_centroid
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation n K) {L : Geometry.SimplicialComplex ℝ E}
    (hLK : L.faces ⊆ K.faces) {τ m : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L τ (insert m d)) (hm : m ∉ d) :
    incidenceIndex (o.relativeVertexOrder L)
      (τ ∪ (insert m d).image (fun s => s.centroid ℝ id)) (m.centroid ℝ id) =
      (d.filter fun s => m.card < s.card).card := by
  let _ : LinearOrder E := o.relativeVertexOrder L
  let _ : DecidableEq E := Classical.decEq E
  have hmFlag : m ∈ insert m d := Finset.mem_insert_self m d
  have hmK : m ∈ K.faces := h.subset_faces m hmFlag
  have hmL : m ∉ L.faces := h.notMem m hmFlag
  have hfilter :
      (τ ∪ (insert m d).image (fun s => s.centroid ℝ id)).filter
          (fun x => x < m.centroid ℝ id) =
        (d.filter fun s => m.card < s.card).image (fun s => s.centroid ℝ id) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxmem, hxlt⟩ := Finset.mem_filter.mp hx
      rcases Finset.mem_union.mp hxmem with hxτ | hxc
      · have hτL : τ ∈ L.faces := by
          rcases h.base with hzero | hmem
          · exact False.elim (Finset.notMem_empty x (hzero ▸ hxτ))
          · exact hmem
        have hxL : {x} ∈ L.faces :=
          L.down_closed hτL (Finset.singleton_subset_iff.mpr hxτ) (Finset.singleton_nonempty x)
        exact False.elim (not_lt_of_ge
          (o.relativeVertexOrder_centroid_lt_boundary hLK hmK hmL hxL).le hxlt)
      · obtain ⟨s, hs, hsx⟩ := Finset.mem_image.mp hxc
        subst x
        rcases Finset.mem_insert.mp hs with hsm | hsd
        · subst s
          exact False.elim (lt_irrefl _ hxlt)
        · have hsK : s ∈ K.faces := h.subset_faces s (Finset.mem_insert_of_mem hsd)
          have hsL : s ∉ L.faces := h.notMem s (Finset.mem_insert_of_mem hsd)
          have hcard : m.card < s.card := by
            by_contra hnot
            have hle : s.card ≤ m.card := Nat.le_of_not_gt hnot
            have hne : s.card ≠ m.card := by
              intro heq
              rcases h.flag.subset_or_subset (Finset.mem_insert_of_mem hsd) hmFlag with hsm | hms
              · exact hm ((Finset.eq_of_subset_of_card_le hsm heq.ge).symm ▸ hsd)
              · exact hm (Finset.eq_of_subset_of_card_le hms heq.le ▸ hsd)
            have hslt : s.card < m.card := lt_of_le_of_ne hle hne
            exact (not_lt_of_ge hxlt.le)
              (o.relativeVertexOrder_centroid_lt_centroid L hmK hmL hsK hsL hslt)
          exact Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨hsd, hcard⟩, rfl⟩
    · intro hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hsd, hcard⟩ := Finset.mem_filter.mp hs
      have hsK : s ∈ K.faces := h.subset_faces s (Finset.mem_insert_of_mem hsd)
      have hsL : s ∉ L.faces := h.notMem s (Finset.mem_insert_of_mem hsd)
      exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem hsd)),
        o.relativeVertexOrder_centroid_lt_centroid L hsK hsL hmK hmL hcard⟩
  unfold incidenceIndex
  dsimp only
  calc
    _ = ((d.filter fun s => m.card < s.card).image
        (fun s => s.centroid ℝ id)).card := congrArg Finset.card hfilter
    _ = (d.filter fun s => m.card < s.card).card :=
      Finset.card_image_of_injOn
        ((injOn_faces_of_mem_openSimplex K
          (centroid_mem_openSimplex_of_mem_faces K)).mono
            (fun s hs => h.subset_faces s
              (Finset.mem_insert_of_mem
                (Finset.mem_filter.mp (Finset.mem_coe.mp hs)).1)))

open Classical in
theorem CoherentOrientation.relativeIncidenceIndex_boundary
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation n K) {L : Geometry.SimplicialComplex ℝ E}
    (hLK : L.faces ⊆ K.faces) {τ : Finset E} {d : Finset (Finset E)} {v : E}
    (h : IsRelFace K L L (insert v τ) d) :
    incidenceIndex (o.relativeVertexOrder L)
      (insert v τ ∪ d.image (fun s => s.centroid ℝ id)) v =
      d.card + incidenceIndex o.vertexOrder (insert v τ) v := by
  let _ : LinearOrder E := o.relativeVertexOrder L
  let _ : DecidableEq E := Classical.decEq E
  have hbaseL : insert v τ ∈ L.faces := by
    rcases h.base with hzero | hmem
    · have hvEmpty : v ∈ (∅ : Finset E) := hzero ▸ Finset.mem_insert_self v τ
      exact False.elim (Finset.notMem_empty v hvEmpty)
    · exact hmem
  have hvL : {v} ∈ L.faces :=
    L.down_closed hbaseL (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self v τ))
      (Finset.singleton_nonempty v)
  have hfilter :
      (insert v τ ∪ d.image (fun s => s.centroid ℝ id)).filter (fun x => x < v) =
        (insert v τ).filter (fun x => let _ := o.vertexOrder; x < v) ∪
          d.image (fun s => s.centroid ℝ id) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxmem, hxlt⟩ := Finset.mem_filter.mp hx
      rcases Finset.mem_union.mp hxmem with hxbase | hxc
      · have hxL : {x} ∈ L.faces :=
          L.down_closed hbaseL (Finset.singleton_subset_iff.mpr hxbase)
            (Finset.singleton_nonempty x)
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxbase,
          (o.relativeVertexOrder_boundary_lt_iff hLK hxL hvL).mp hxlt⟩)
      · exact Finset.mem_union_right _ hxc
    · intro hx
      rcases Finset.mem_union.mp hx with hxbase | hxc
      · obtain ⟨hxmem, hxlt⟩ := Finset.mem_filter.mp hxbase
        have hxL : {x} ∈ L.faces :=
          L.down_closed hbaseL (Finset.singleton_subset_iff.mpr hxmem)
            (Finset.singleton_nonempty x)
        exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hxmem,
          (o.relativeVertexOrder_boundary_lt_iff hLK hxL hvL).mpr hxlt⟩
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hxc
        have hsK : s ∈ K.faces := h.subset_faces s hs
        have hsL : s ∉ L.faces := h.notMem s hs
        exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _
          (Finset.mem_image_of_mem _ hs),
          o.relativeVertexOrder_centroid_lt_boundary hLK hsK hsL hvL⟩
  change ((insert v τ ∪ d.image (fun s => s.centroid ℝ id)).filter
      (fun x => @LT.lt E (o.relativeVertexOrder L).toLT x v)).card =
    d.card + incidenceIndex o.vertexOrder (insert v τ) v
  have hinj := (injOn_faces_of_mem_openSimplex K
    (centroid_mem_openSimplex_of_mem_faces K)).mono h.flag.coe_subset_faces
  have hdisjoint := (h.disjoint (c := fun s => s.centroid ℝ id) hLK
    (IsSubdivision.refl L) (centroid_mem_openSimplex_of_mem_faces K)).mono_left
      (Finset.filter_subset (fun x : E => let _ := o.vertexOrder; x < v) (insert v τ))
  calc
    _ = ((insert v τ).filter (fun x => let _ := o.vertexOrder; x < v) ∪
        d.image (fun s => s.centroid ℝ id)).card := congrArg Finset.card hfilter
    _ = ((insert v τ).filter (fun x => let _ := o.vertexOrder; x < v)).card +
        (d.image (fun s => s.centroid ℝ id)).card :=
      Finset.card_union_of_disjoint hdisjoint
    _ = d.card + ((insert v τ).filter
        (fun x => let _ := o.vertexOrder; x < v)).card := by
      rw [Finset.card_image_of_injOn hinj, add_comm]
    _ = d.card + incidenceIndex o.vertexOrder (insert v τ) v := by
      unfold incidenceIndex
      dsimp only
      apply congrArg (fun k : ℕ => d.card + k)
      apply congrArg Finset.card
      ext x
      simp only [Finset.mem_filter]

open Classical in
theorem CoherentOrientation.simplexBoundaryCoefficient_relative_centroid
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation n K) {L : Geometry.SimplicialComplex ℝ E}
    (hLK : L.faces ⊆ K.faces) {τ m : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L τ (insert m d)) (hm : m ∉ d) :
    simplexBoundaryCoefficient (o.relativeVertexOrder L)
        (τ ∪ (insert m d).image (fun s => s.centroid ℝ id))
        (τ ∪ d.image (fun s => s.centroid ℝ id)) =
      (-1 : ℤ) ^ (d.filter fun s => m.card < s.card).card := by
  let r := o.relativeVertexOrder L
  let _ : DecidableEq E := Classical.decEq E
  have hmFlag : m ∈ insert m d := Finset.mem_insert_self m d
  have hmK : m ∈ K.faces := h.subset_faces m hmFlag
  have hdisjoint := h.disjoint (c := fun s => s.centroid ℝ id) hLK
    (IsSubdivision.refl L) (centroid_mem_openSimplex_of_mem_faces K)
  have hcentroidNotMem : m.centroid ℝ id ∉
      τ ∪ d.image (fun s => s.centroid ℝ id) := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hbase | himage
    · exact (Finset.disjoint_left.mp hdisjoint hbase
        (Finset.mem_image_of_mem _ hmFlag))
    · obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp himage
      have hsK : s ∈ K.faces := h.subset_faces s (Finset.mem_insert_of_mem hs)
      have hsm : s = m := (injOn_faces_of_mem_openSimplex K
        (centroid_mem_openSimplex_of_mem_faces K)) hsK hmK heq
      exact hm (hsm ▸ hs)
  have htop : τ ∪ (insert m d).image (fun s => s.centroid ℝ id) =
      insert (m.centroid ℝ id) (τ ∪ d.image (fun s => s.centroid ℝ id)) := by
    ext x
    simp [Finset.image_insert]
  have hcentroidMem : m.centroid ℝ id ∈
      τ ∪ (insert m d).image (fun s => s.centroid ℝ id) :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hmFlag)
  have herase : @Finset.erase E r.toDecidableEq
      (τ ∪ (insert m d).image (fun s => s.centroid ℝ id)) (m.centroid ℝ id) =
        τ ∪ d.image (fun s => s.centroid ℝ id) := by
    rw [htop]
    have hdec : r.toDecidableEq = (inferInstance : DecidableEq E) := Subsingleton.elim _ _
    rw [hdec]
    exact Finset.erase_insert hcentroidNotMem
  calc
    simplexBoundaryCoefficient r
        (τ ∪ (insert m d).image (fun s => s.centroid ℝ id))
        (τ ∪ d.image (fun s => s.centroid ℝ id)) =
      simplexBoundaryCoefficient r
        (τ ∪ (insert m d).image (fun s => s.centroid ℝ id))
        (@Finset.erase E r.toDecidableEq
          (τ ∪ (insert m d).image (fun s => s.centroid ℝ id))
          (m.centroid ℝ id)) := by rw [herase]
    _ = incidenceSign r
        (τ ∪ (insert m d).image (fun s => s.centroid ℝ id))
        (m.centroid ℝ id) := simplexBoundaryCoefficient_erase r hcentroidMem
    _ = (-1 : ℤ) ^ (d.filter fun s => m.card < s.card).card := by
      rw [incidenceSign, o.relativeIncidenceIndex_centroid hLK h hm]

open Classical in
theorem CoherentOrientation.simplexBoundaryCoefficient_relative_boundary
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation n K) {L : Geometry.SimplicialComplex ℝ E}
    (hLK : L.faces ⊆ K.faces) {τ : Finset E} {d : Finset (Finset E)} {v : E}
    (h : IsRelFace K L L (insert v τ) d) (hv : v ∉ τ) :
    simplexBoundaryCoefficient (o.relativeVertexOrder L)
        (insert v τ ∪ d.image (fun s => s.centroid ℝ id))
        (τ ∪ d.image (fun s => s.centroid ℝ id)) =
      (-1 : ℤ) ^ d.card * simplexBoundaryCoefficient o.vertexOrder (insert v τ) τ := by
  let r := o.relativeVertexOrder L
  let _ : DecidableEq E := Classical.decEq E
  have hdisjoint := h.disjoint (c := fun s => s.centroid ℝ id) hLK
    (IsSubdivision.refl L) (centroid_mem_openSimplex_of_mem_faces K)
  have hvNotMem : v ∉ τ ∪ d.image (fun s => s.centroid ℝ id) := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hτ | himage
    · exact hv hτ
    · exact Finset.disjoint_left.mp hdisjoint (Finset.mem_insert_self v τ) himage
  have htop : insert v τ ∪ d.image (fun s => s.centroid ℝ id) =
      insert v (τ ∪ d.image (fun s => s.centroid ℝ id)) := by
    ext x
    simp
  have hvMem : v ∈ insert v τ ∪ d.image (fun s => s.centroid ℝ id) :=
    Finset.mem_union_left _ (Finset.mem_insert_self v τ)
  have herase : @Finset.erase E r.toDecidableEq
      (insert v τ ∪ d.image (fun s => s.centroid ℝ id)) v =
        τ ∪ d.image (fun s => s.centroid ℝ id) := by
    rw [htop]
    have hdec : r.toDecidableEq = (inferInstance : DecidableEq E) := Subsingleton.elim _ _
    rw [hdec]
    exact Finset.erase_insert hvNotMem
  calc
    simplexBoundaryCoefficient r
        (insert v τ ∪ d.image (fun s => s.centroid ℝ id))
        (τ ∪ d.image (fun s => s.centroid ℝ id)) =
      simplexBoundaryCoefficient r
        (insert v τ ∪ d.image (fun s => s.centroid ℝ id))
        (@Finset.erase E r.toDecidableEq
          (insert v τ ∪ d.image (fun s => s.centroid ℝ id)) v) := by rw [herase]
    _ = incidenceSign r (insert v τ ∪ d.image (fun s => s.centroid ℝ id)) v :=
      simplexBoundaryCoefficient_erase r hvMem
    _ = (-1 : ℤ) ^ (d.card + incidenceIndex o.vertexOrder (insert v τ) v) := by
      rw [incidenceSign, o.relativeIncidenceIndex_boundary hLK h]
    _ = (-1 : ℤ) ^ d.card * incidenceSign o.vertexOrder (insert v τ) v := by
      rw [pow_add]
      rfl
    _ = (-1 : ℤ) ^ d.card * simplexBoundaryCoefficient o.vertexOrder (insert v τ) τ := by
      have hdec : o.vertexOrder.toDecidableEq = (inferInstance : DecidableEq E) :=
        Subsingleton.elim _ _
      have hcoefficient := simplexBoundaryCoefficient_insert o.vertexOrder hv
      rw [hdec] at hcoefficient
      exact congrArg (fun z : ℤ => (-1 : ℤ) ^ d.card * z) hcoefficient.symm

open Classical in
theorem IsRelFace.base_subset_of_mem
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L τ d) {s : Finset E} (hs : s ∈ d) : τ ⊆ s := by
  rcases τ.eq_empty_or_nonempty with hτ | hτ
  · rw [hτ]
    exact Finset.empty_subset s
  · have hτL : τ ∈ L.faces := h.base.resolve_left (fun he => by
      subst τ
      exact Finset.not_nonempty_empty hτ)
    exact face_subset_of_mem_openSimplex_of_mem_convexHull K (hLK hτL)
      (h.subset_faces s hs) (centroid_mem_openSimplex hτ)
      (h.convexHull_subset_of_mem hs
        (openSimplex_subset_convexHull τ (centroid_mem_openSimplex hτ)))

open Classical in
theorem IsRelFace.base_not_mem_flag
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E}
    {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L τ d) : τ ∉ d := by
  intro hτd
  rcases h.base with hτ | hτ
  · have hne := K.nonempty_of_mem_faces (h.subset_faces τ hτd)
    exact hne.ne_empty hτ
  · exact h.notMem τ hτd hτ

open Classical in
theorem IsRelFace.card_union_image
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L L' : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    (hL' : IsSubdivision L' L) (c : Finset E → E)
    (hc : ∀ s ∈ K.faces, c s ∈ openSimplex s)
    {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L' τ d) :
    (τ ∪ d.image c).card = τ.card + d.card := by
  rw [Finset.card_union_of_disjoint (h.disjoint hLK hL' hc),
    Finset.card_image_of_injOn (h.flag.injOn K hc)]

open Classical in
theorem IsRelFace.card_flag_le_sub_card_base
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L τ d) {u : Finset E} (hu : u ∈ d)
    (htop : ∀ s ∈ d, s ⊆ u) : d.card ≤ u.card - τ.card := by
  have hτu := h.base_subset_of_mem hLK hu
  have hmaps : Set.MapsTo Finset.card (d : Set (Finset E))
      ((Finset.Icc (τ.card + 1) u.card : Finset ℕ) : Set ℕ) := by
    intro s hs
    rw [Finset.coe_Icc, mem_Icc]
    have hτs := h.base_subset_of_mem hLK (Finset.mem_coe.mp hs)
    have hne : τ ≠ s := fun he => h.base_not_mem_flag (he ▸ Finset.mem_coe.mp hs)
    exact ⟨by
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hτs, hne⟩)
      omega,
      Finset.card_le_card (htop s (Finset.mem_coe.mp hs))⟩
  have hinj : Set.InjOn Finset.card (d : Set (Finset E)) := by
    intro s hs t ht hcard
    rcases h.flag.subset_or_subset (Finset.mem_coe.mp hs) (Finset.mem_coe.mp ht) with hst | hts
    · exact Finset.eq_of_subset_of_card_le hst hcard.ge
    · exact (Finset.eq_of_subset_of_card_le hts hcard.le).symm
  have hcard := Finset.card_le_card_of_injOn Finset.card hmaps hinj
  simpa using hcard

open Classical in
theorem IsRelFace.flag_nonempty_of_top_card
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E}
    {N : ℕ} (hLcard : ∀ s ∈ L.faces, s.card ≤ N)
    {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L τ d)
    (hcard : (τ ∪ d.image fun s => s.centroid ℝ id).card = N + 1) :
    d.Nonempty := by
  by_contra hdne
  rw [Finset.not_nonempty_iff_eq_empty] at hdne
  have hτcard : τ.card = N + 1 := by
    simpa [hdne] using hcard
  rcases h.base with hτ | hτ
  · rw [hτ, Finset.card_empty] at hτcard
    omega
  · have := hLcard τ hτ
    omega

open Classical in
theorem IsRelFace.top_card_eq_of_top_face
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {N : ℕ} (hKcard : ∀ s ∈ K.faces, s.card ≤ N + 1)
    {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L τ d)
    (hcard : (τ ∪ d.image fun s => s.centroid ℝ id).card = N + 1)
    {u : Finset E} (hu : u ∈ d) (htop : ∀ s ∈ d, s ⊆ u) :
    u.card = N + 1 := by
  have hsum := h.card_union_image hLK (IsSubdivision.refl L)
    (fun s => s.centroid ℝ id) (centroid_mem_openSimplex_of_mem_faces K)
  rw [hcard] at hsum
  have hτu := h.base_subset_of_mem hLK hu
  have hτcard : τ.card ≤ u.card := Finset.card_le_card hτu
  have hdcard := h.card_flag_le_sub_card_base hLK hu htop
  have hucard := hKcard u (h.subset_faces u hu)
  omega

open Classical in
theorem IsRelFace.existsUnique_card_of_top_face
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {N : ℕ} (hKcard : ∀ s ∈ K.faces, s.card ≤ N + 1)
    (hLcard : ∀ s ∈ L.faces, s.card ≤ N)
    {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L τ d)
    (hcard : (τ ∪ d.image fun s => s.centroid ℝ id).card = N + 1)
    {k : ℕ} (hτk : τ.card < k) (hkN : k ≤ N + 1) :
    ∃! s, s ∈ d ∧ s.card = k := by
  have hdne := h.flag_nonempty_of_top_card hLcard hcard
  obtain ⟨u, hu, htop⟩ := h.flag.exists_top hdne
  have hucard := h.top_card_eq_of_top_face hLK hKcard hcard hu htop
  have hsum := h.card_union_image hLK (IsSubdivision.refl L)
    (fun s => s.centroid ℝ id) (centroid_mem_openSimplex_of_mem_faces K)
  rw [hcard] at hsum
  have hτu := h.base_subset_of_mem hLK hu
  have hmaps : Set.MapsTo Finset.card (d : Set (Finset E))
      ((Finset.Icc (τ.card + 1) (N + 1) : Finset ℕ) : Set ℕ) := by
    intro s hs
    rw [Finset.coe_Icc, mem_Icc]
    have hτs := h.base_subset_of_mem hLK (Finset.mem_coe.mp hs)
    have hne : τ ≠ s := fun he => h.base_not_mem_flag (he ▸ Finset.mem_coe.mp hs)
    exact ⟨by
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hτs, hne⟩)
      omega,
      by simpa [hucard] using Finset.card_le_card (htop s (Finset.mem_coe.mp hs))⟩
  have hinj : Set.InjOn Finset.card (d : Set (Finset E)) := by
    intro s hs t ht heq
    rcases h.flag.subset_or_subset (Finset.mem_coe.mp hs) (Finset.mem_coe.mp ht) with hst | hts
    · exact Finset.eq_of_subset_of_card_le hst heq.ge
    · exact (Finset.eq_of_subset_of_card_le hts heq.le).symm
  have himage : d.image Finset.card = Finset.Icc (τ.card + 1) (N + 1) := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_coe.mp (hmaps (Finset.mem_coe.mpr hs))
    · rw [Finset.card_image_of_injOn hinj]
      have hτN : τ.card ≤ N + 1 := hsum ▸ Nat.le_add_right τ.card d.card
      simp only [Nat.card_Icc]
      omega
  have hk : k ∈ d.image Finset.card := by
    rw [himage, Finset.mem_Icc]
    omega
  obtain ⟨s, hs, hsk⟩ := Finset.mem_image.mp hk
  refine ⟨s, ⟨hs, hsk⟩, ?_⟩
  intro t ht
  apply hinj (Finset.mem_coe.mpr ht.1) (Finset.mem_coe.mpr hs)
  exact ht.2.trans hsk.symm

noncomputable def relativeFlagBoundaryProduct
    (r : LinearOrder E) (τ : Finset E) (d : Finset (Finset E)) : ℤ :=
  ∏ s ∈ d, ∏ t ∈ (insert τ d).filter (fun t => t.card + 1 = s.card),
    simplexBoundaryCoefficient r s t

noncomputable def relativeLowerBoundaryProduct
    (r : LinearOrder E) (τ : Finset E) (d : Finset (Finset E)) (m : Finset E) : ℤ :=
  ∏ t ∈ insert τ d,
    if t.card + 1 = m.card then simplexBoundaryCoefficient r m t else 1

noncomputable def relativeUpperBoundaryProduct
    (r : LinearOrder E) (d : Finset (Finset E)) (m : Finset E) : ℤ :=
  ∏ s ∈ d,
    if m.card + 1 = s.card then simplexBoundaryCoefficient r s m else 1

open Classical in
theorem relativeFlagBoundaryProduct_insert
    (r : LinearOrder E) (τ : Finset E) (d : Finset (Finset E)) (m : Finset E)
    (hm : m ∉ d) (hmτ : m ≠ τ) :
    relativeFlagBoundaryProduct r τ (insert m d) =
      relativeFlagBoundaryProduct r τ d * relativeLowerBoundaryProduct r τ d m *
        relativeUpperBoundaryProduct r d m := by
  unfold relativeFlagBoundaryProduct relativeLowerBoundaryProduct relativeUpperBoundaryProduct
  simp_rw [Finset.prod_filter]
  rw [Finset.prod_insert hm]
  rw [Finset.insert_comm τ m d]
  have hmold : m ∉ insert τ d := by simp [hm, hmτ]
  have hnew :
      (∏ t ∈ insert m (insert τ d),
        if t.card + 1 = m.card then simplexBoundaryCoefficient r m t else 1) =
        ∏ t ∈ insert τ d,
          if t.card + 1 = m.card then simplexBoundaryCoefficient r m t else 1 := by
    rw [Finset.prod_insert hmold]
    simp
  rw [hnew]
  have hinner (s : Finset E) :
      (∏ t ∈ insert m (insert τ d),
        if t.card + 1 = s.card then simplexBoundaryCoefficient r s t else 1) =
        (if m.card + 1 = s.card then simplexBoundaryCoefficient r s m else 1) *
          ∏ t ∈ insert τ d,
            if t.card + 1 = s.card then simplexBoundaryCoefficient r s t else 1 := by
    rw [Finset.prod_insert hmold]
  simp_rw [hinner]
  rw [Finset.prod_mul_distrib]
  ring

open Classical in
theorem relativeLowerBoundaryProduct_eq_of_unique
    (r : LinearOrder E) (τ : Finset E) (d : Finset (Finset E))
    {m a : Finset E} (ha : a ∈ insert τ d) (hacard : a.card + 1 = m.card)
    (hunique : ∀ t ∈ insert τ d, t.card + 1 = m.card → t = a) :
    relativeLowerBoundaryProduct r τ d m = simplexBoundaryCoefficient r m a := by
  unfold relativeLowerBoundaryProduct
  rw [Finset.prod_eq_single a]
  · rw [if_pos hacard]
  · intro t ht hta
    by_cases htcard : t.card + 1 = m.card
    · exact False.elim (hta (hunique t ht htcard))
    · rw [if_neg htcard]
  · exact fun hnot => False.elim (hnot ha)

open Classical in
theorem relativeUpperBoundaryProduct_eq_of_unique
    (r : LinearOrder E) (d : Finset (Finset E))
    {m b : Finset E} (hb : b ∈ d) (hbcard : m.card + 1 = b.card)
    (hunique : ∀ s ∈ d, m.card + 1 = s.card → s = b) :
    relativeUpperBoundaryProduct r d m = simplexBoundaryCoefficient r b m := by
  unfold relativeUpperBoundaryProduct
  rw [Finset.prod_eq_single b]
  · rw [if_pos hbcard]
  · intro s hs hsb
    by_cases hscard : m.card + 1 = s.card
    · exact False.elim (hsb (hunique s hs hscard))
    · rw [if_neg hscard]
  · exact fun hnot => False.elim (hnot hb)

open Classical in
theorem relativeUpperBoundaryProduct_eq_one
    (r : LinearOrder E) (d : Finset (Finset E)) (m : Finset E)
    (hcard : ∀ s ∈ d, s.card ≤ m.card) :
    relativeUpperBoundaryProduct r d m = 1 := by
  unfold relativeUpperBoundaryProduct
  apply Finset.prod_eq_one
  intro s hs
  rw [if_neg]
  have := hcard s hs
  omega

open Classical in
theorem IsRelFace.relativeFlagBoundaryProduct_insert_base
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {m τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L m d) (r : LinearOrder E)
    (hcard : τ.card + 1 = m.card) :
    relativeFlagBoundaryProduct r τ (insert m d) =
      relativeFlagBoundaryProduct r m d * simplexBoundaryCoefficient r m τ := by
  have hm : m ∉ d := h.base_not_mem_flag
  have hpred : (insert τ (insert m d)).filter (fun s => s.card + 1 = m.card) = {τ} := by
    ext s
    constructor
    · intro hs
      obtain ⟨hs, hscard⟩ := Finset.mem_filter.mp hs
      rcases Finset.mem_insert.mp hs with hsτ | hs
      · exact Finset.mem_singleton.mpr hsτ
      · rcases Finset.mem_insert.mp hs with hsm | hsd
        · subst s
          omega
        · have hle := Finset.card_le_card (h.base_subset_of_mem hLK hsd)
          omega
    · intro hs
      rw [Finset.mem_singleton] at hs
      subst s
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self τ _, hcard⟩
  have hfilters (s : Finset E) (hs : s ∈ d) :
      (insert τ (insert m d)).filter (fun t => t.card + 1 = s.card) =
        (insert m d).filter (fun t => t.card + 1 = s.card) := by
    have hms := h.base_subset_of_mem hLK hs
    have hne : m ≠ s := fun heq => hm (heq ▸ hs)
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hms, hne⟩)
    ext t
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨ht | ht, htcard⟩
      · subst t
        omega
      · exact ⟨ht, htcard⟩
    · exact fun ht => ⟨Or.inr ht.1, ht.2⟩
  have hprod :
      (∏ s ∈ d, ∏ t ∈ (insert τ (insert m d)).filter
          (fun t => t.card + 1 = s.card), simplexBoundaryCoefficient r s t) =
        ∏ s ∈ d, ∏ t ∈ (insert m d).filter
          (fun t => t.card + 1 = s.card), simplexBoundaryCoefficient r s t := by
    apply Finset.prod_congr rfl
    intro s hs
    rw [hfilters s hs]
  unfold relativeFlagBoundaryProduct
  rw [Finset.prod_insert hm, hpred, Finset.prod_singleton]
  rw [hprod]
  ring

noncomputable def relativeTopCoefficient
    (r : LinearOrder E) (N : ℕ) (c : Finset E → ℤ)
    (τ : Finset E) (d : Finset (Finset E)) : ℤ :=
  (∏ s ∈ d.filter (fun s => s.card = N + 1), c s) *
    relativeFlagBoundaryProduct r τ d

open Classical in
theorem IsRelFace.relativeTopCoefficient_insert_base
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {N : ℕ} {m τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L m d) (r : LinearOrder E) (c : Finset E → ℤ)
    (hcard : τ.card + 1 = m.card) (hmN : m.card ≤ N) :
    relativeTopCoefficient r N c τ (insert m d) =
      relativeTopCoefficient r N c m d * simplexBoundaryCoefficient r m τ := by
  have hm : m ∉ d := h.base_not_mem_flag
  have hfilter : (insert m d).filter (fun s => s.card = N + 1) =
      d.filter (fun s => s.card = N + 1) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hsm | hsd, hscard⟩
      · subst s
        omega
      · exact ⟨hsd, hscard⟩
    · exact fun hs => ⟨Or.inr hs.1, hs.2⟩
  unfold relativeTopCoefficient
  rw [hfilter, h.relativeFlagBoundaryProduct_insert_base hLK r hcard]
  ring

open Classical in
theorem relativeTopCoefficient_insert_middle
    (r : LinearOrder E) (N : ℕ) (c : Finset E → ℤ)
    (τ : Finset E) (d : Finset (Finset E)) {m a b : Finset E}
    (hm : m ∉ d) (hmτ : m ≠ τ) (hmN : m.card ≤ N)
    (ha : a ∈ insert τ d) (hacard : a.card + 1 = m.card)
    (haunique : ∀ t ∈ insert τ d, t.card + 1 = m.card → t = a)
    (hb : b ∈ d) (hbcard : m.card + 1 = b.card)
    (hbunique : ∀ s ∈ d, m.card + 1 = s.card → s = b) :
    relativeTopCoefficient r N c τ (insert m d) =
      relativeTopCoefficient r N c τ d *
        simplexBoundaryCoefficient r b m * simplexBoundaryCoefficient r m a := by
  have hfilter : (insert m d).filter (fun s => s.card = N + 1) =
      d.filter (fun s => s.card = N + 1) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hsm | hsd, hscard⟩
      · subst s
        omega
      · exact ⟨hsd, hscard⟩
    · exact fun hs => ⟨Or.inr hs.1, hs.2⟩
  unfold relativeTopCoefficient
  rw [hfilter, relativeFlagBoundaryProduct_insert r τ d m hm hmτ,
    relativeLowerBoundaryProduct_eq_of_unique r τ d ha hacard haunique,
    relativeUpperBoundaryProduct_eq_of_unique r d hb hbcard hbunique]
  ring

open Classical in
theorem relativeTopCoefficient_insert_top
    (r : LinearOrder E) (N : ℕ) (c : Finset E → ℤ)
    (τ : Finset E) (d : Finset (Finset E)) {m u : Finset E}
    (hm : m ∉ d) (hmτ : m ≠ τ) (hmcard : m.card = N + 1)
    (hdcard : ∀ s ∈ d, s.card ≤ N)
    (hu : u ∈ insert τ d) (hucard : u.card = N)
    (huunique : ∀ t ∈ insert τ d, t.card = N → t = u) :
    relativeTopCoefficient r N c τ (insert m d) =
      relativeTopCoefficient r N c τ d * c m * simplexBoundaryCoefficient r m u := by
  have hfilterD : d.filter (fun s => s.card = N + 1) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro s hs
    have := hdcard s hs
    omega
  have hfilterInsert : (insert m d).filter (fun s => s.card = N + 1) = {m} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsm | hsd, hscard⟩
      · exact hsm
      · have := hdcard s hsd
        omega
    · intro hsm
      subst s
      exact ⟨Or.inl rfl, hmcard⟩
  have hlower := relativeLowerBoundaryProduct_eq_of_unique r τ d (m := m) (a := u) hu
    (by omega) (fun t ht htcard => huunique t ht (by omega))
  have hupper := relativeUpperBoundaryProduct_eq_one r d m (fun s hs => by
    have := hdcard s hs
    omega)
  unfold relativeTopCoefficient
  rw [hfilterInsert, hfilterD, Finset.prod_singleton, Finset.prod_empty,
    relativeFlagBoundaryProduct_insert r τ d m hm hmτ, hlower, hupper]
  ring

theorem simplexBoundaryCoefficient_eq_one_or_neg_one
    (r : LinearOrder E) {s t : Finset E} (hts : t ⊆ s)
    (hcard : t.card + 1 = s.card) :
    simplexBoundaryCoefficient r s t = 1 ∨ simplexBoundaryCoefficient r s t = -1 := by
  obtain ⟨v, hvt, hvs⟩ := Finset.exists_eq_insert_iff.mpr ⟨hts, hcard⟩
  have hv : v ∈ s := hvs ▸ Finset.mem_insert_self v t
  have herase : @Finset.erase E r.toDecidableEq s v = t := by
    rw [← hvs, Finset.erase_insert hvt]
  rw [← herase, simplexBoundaryCoefficient_erase r hv, incidenceSign]
  exact neg_one_pow_eq_or ℤ (incidenceIndex r s v)

open Classical in
theorem finset_prod_eq_one_or_neg_one
    {A : Type*} (s : Finset A) (f : A → ℤ)
    (hf : ∀ a ∈ s, f a = 1 ∨ f a = -1) :
    (∏ a ∈ s, f a) = 1 ∨ (∏ a ∈ s, f a) = -1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rcases hf a (Finset.mem_insert_self a s) with ha1 | ha1 <;>
        rcases ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)) with hs1 | hs1 <;>
          simp [ha1, hs1]

open Classical in
theorem IsRelFace.relativeFlagBoundaryProduct_eq_one_or_neg_one
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L τ d) (r : LinearOrder E) :
    relativeFlagBoundaryProduct r τ d = 1 ∨ relativeFlagBoundaryProduct r τ d = -1 := by
  unfold relativeFlagBoundaryProduct
  apply finset_prod_eq_one_or_neg_one
  intro s hs
  apply finset_prod_eq_one_or_neg_one
  intro t ht
  have ht' := Finset.mem_filter.mp ht
  have hts : t ⊆ s := by
    rcases Finset.mem_insert.mp ht'.1 with hts | htd
    · rw [hts]
      exact h.base_subset_of_mem hLK hs
    · rcases h.flag.subset_or_subset htd hs with hts | hst
      · exact hts
      · have hcardle := Finset.card_le_card hst
        omega
  exact simplexBoundaryCoefficient_eq_one_or_neg_one r hts ht'.2

open Classical in
theorem IsRelFace.relativeTopCoefficient_eq_one_or_neg_one
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {N : ℕ} (hKcard : ∀ s ∈ K.faces, s.card ≤ N + 1)
    (hLcard : ∀ s ∈ L.faces, s.card ≤ N)
    {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L τ d)
    (hcard : (τ ∪ d.image fun s => s.centroid ℝ id).card = N + 1)
    (r : LinearOrder E) {c : Finset E → ℤ}
    (hc : ∀ s ∈ K.faces, s.card = N + 1 → c s = 1 ∨ c s = -1) :
    relativeTopCoefficient r N c τ d = 1 ∨ relativeTopCoefficient r N c τ d = -1 := by
  have hdne := h.flag_nonempty_of_top_card hLcard hcard
  obtain ⟨u, hu, htop⟩ := h.flag.exists_top hdne
  have hucard := h.top_card_eq_of_top_face hLK hKcard hcard hu htop
  have hfilter : d.filter (fun s => s.card = N + 1) = {u} := by
    ext s
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hs
      apply Finset.eq_of_subset_of_card_le (htop s hs.1)
      rw [hs.2, hucard]
    · rintro rfl
      exact ⟨hu, hucard⟩
  unfold relativeTopCoefficient
  rw [hfilter, Finset.prod_singleton]
  rcases hc u (h.subset_faces u hu) hucard with hu1 | hu1 <;>
    rcases h.relativeFlagBoundaryProduct_eq_one_or_neg_one hLK r with hd1 | hd1 <;>
      simp [hu1, hd1]

open Classical in
theorem IsRelFace.eq_of_union_image_eq
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L L' : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    (hL' : IsSubdivision L' L) (c : Finset E → E)
    (hc : ∀ s ∈ K.faces, c s ∈ openSimplex s)
    {τ τ' : Finset E} {d d' : Finset (Finset E)}
    (h : IsRelFace K L L' τ d) (h' : IsRelFace K L L' τ' d')
    (heq : τ ∪ d.image c = τ' ∪ d'.image c) : τ = τ' ∧ d = d' := by
  have hne : (τ ∪ d.image c).Nonempty := by
    rcases h.nonempty with hτ | hd
    · exact hτ.mono Finset.subset_union_left
    · obtain ⟨s, hs⟩ := hd
      exact ⟨c s, Finset.mem_union_right _ (Finset.mem_image_of_mem c hs)⟩
  have hx := centroid_mem_openSimplex hne
  have hx' : (τ ∪ d.image c).centroid ℝ id ∈ openSimplex (τ' ∪ d'.image c) := by
    rw [← heq]
    exact hx
  exact h.eq_of_mem_openSimplex hLK hL' hc h' hx hx'

open Classical in
noncomputable instance finite_relDerived_faces_instance
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L L' : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L'.faces]
    (hLK : L.faces ⊆ K.faces) (hL' : IsSubdivision L' L)
    (c : Finset E → E) (hc : ∀ s ∈ K.faces, c s ∈ openSimplex s) :
    Finite (relDerived hLK hL' hc).faces :=
  (relDerived_faces_finite hLK hL' hc).to_subtype

open Classical in
theorem IsRelFace.injOn_card_insert
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L τ d) :
    Set.InjOn Finset.card ((insert τ d : Finset (Finset E)) : Set (Finset E)) := by
  intro s hs t ht hcard
  rcases Finset.mem_insert.mp (Finset.mem_coe.mp hs) with hsτ | hsd
  · rcases Finset.mem_insert.mp (Finset.mem_coe.mp ht) with htτ | htd
    · exact hsτ.trans htτ.symm
    · subst s
      exact Finset.eq_of_subset_of_card_le (h.base_subset_of_mem hLK htd) hcard.ge
  · rcases Finset.mem_insert.mp (Finset.mem_coe.mp ht) with htτ | htd
    · subst t
      exact (Finset.eq_of_subset_of_card_le (h.base_subset_of_mem hLK hsd) hcard.le).symm
    · rcases h.flag.subset_or_subset hsd htd with hst | hts
      · exact Finset.eq_of_subset_of_card_le hst hcard.ge
      · exact (Finset.eq_of_subset_of_card_le hts hcard.le).symm

open Classical in
theorem IsRelFace.data_subset_of_union_image_subset
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L L' : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    (hL' : IsSubdivision L' L) (c : Finset E → E)
    (hc : ∀ s ∈ K.faces, c s ∈ openSimplex s)
    {τ τ' : Finset E} {d d' : Finset (Finset E)}
    (h : IsRelFace K L L' τ d) (h' : IsRelFace K L L' τ' d')
    (hsub : τ ∪ d.image c ⊆ τ' ∪ d'.image c) : τ ⊆ τ' ∧ d ⊆ d' := by
  have hne : (τ ∪ d.image c).Nonempty := by
    rcases h.nonempty with hτ | hd
    · exact hτ.mono Finset.subset_union_left
    · obtain ⟨s, hs⟩ := hd
      exact ⟨c s, Finset.mem_union_right _ (Finset.mem_image_of_mem c hs)⟩
  obtain ⟨τ₀, d₀, h₀, hτ₀, hd₀, heq⟩ := h'.exists_sub hsub hne
  have hdata := h.eq_of_union_image_eq hLK hL' c hc h₀ heq
  rw [hdata.1, hdata.2]
  exact ⟨hτ₀, hd₀⟩

open Classical in
theorem relativeData_eq_or_eq_insert
    {τ τ' : Finset E} {d d' : Finset (Finset E)} {N : ℕ}
    (hτ : τ ⊆ τ') (hd : d ⊆ d')
    (hcard : τ.card + d.card = N)
    (hcard' : τ'.card + d'.card = N + 1) :
    (τ' = τ ∧ ∃ m ∉ d, d' = insert m d) ∨
      (d' = d ∧ ∃ v ∉ τ, τ' = insert v τ) := by
  by_cases hτeq : τ' = τ
  · left
    refine ⟨hτeq, ?_⟩
    have hdcard : d.card + 1 = d'.card := by
      rw [hτeq] at hcard'
      omega
    obtain ⟨m, hm, heq⟩ := Finset.exists_eq_insert_iff.mpr ⟨hd, hdcard⟩
    exact ⟨m, hm, heq.symm⟩
  · right
    have hτlt : τ.card < τ'.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hτ, fun he => hτeq he.symm⟩)
    have hdcard : d'.card = d.card := by
      have := Finset.card_le_card hd
      omega
    have hdeq : d' = d := (Finset.eq_of_subset_of_card_le hd hdcard.le).symm
    refine ⟨hdeq, ?_⟩
    have hτcard : τ.card + 1 = τ'.card := by
      rw [hdeq] at hcard'
      omega
    obtain ⟨v, hv, heq⟩ := Finset.exists_eq_insert_iff.mpr ⟨hτ, hτcard⟩
    exact ⟨v, hv, heq.symm⟩

open Classical in
theorem IsRelFace.existsUnique_missing_card
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {N : ℕ} (hKcard : ∀ s ∈ K.faces, s.card ≤ N + 1)
    {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L τ d)
    (hcard : (τ ∪ d.image fun s => s.centroid ℝ id).card = N) :
    ∃! j, j ∈ Finset.Icc τ.card (N + 1) ∧
      j ∉ (insert τ d).image Finset.card := by
  have hsum := h.card_union_image hLK (IsSubdivision.refl L)
    (fun s => s.centroid ℝ id) (centroid_mem_openSimplex_of_mem_faces K)
  rw [hcard] at hsum
  have hτN : τ.card ≤ N := by omega
  have hmaps : (insert τ d).image Finset.card ⊆ Finset.Icc τ.card (N + 1) := by
    intro k hk
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_Icc]
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact ⟨le_rfl, by omega⟩
    · exact ⟨Finset.card_le_card (h.base_subset_of_mem hLK hs),
        hKcard s (h.subset_faces s hs)⟩
  have himageCard : ((insert τ d).image Finset.card).card = d.card + 1 := by
    rw [Finset.card_image_of_injOn (h.injOn_card_insert hLK),
      Finset.card_insert_of_notMem h.base_not_mem_flag]
  have hmissingCard :
      (Finset.Icc τ.card (N + 1) \ (insert τ d).image Finset.card).card = 1 := by
    rw [Finset.card_sdiff_of_subset hmaps, himageCard]
    simp only [Nat.card_Icc]
    omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hmissingCard
  refine ⟨j, ?_, ?_⟩
  · have hjmem : j ∈ Finset.Icc τ.card (N + 1) \
        (insert τ d).image Finset.card := by
      rw [hj]
      exact Finset.mem_singleton_self j
    exact Finset.mem_sdiff.mp hjmem
  · intro k hk
    have hkmem : k ∈ Finset.Icc τ.card (N + 1) \
        (insert τ d).image Finset.card := Finset.mem_sdiff.mpr hk
    rw [hj, Finset.mem_singleton] at hkmem
    exact hkmem

open Classical in
theorem IsRelFace.existsUnique_card_insert_of_ne_missing
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L τ d) {N j k : ℕ}
    (hjunique : ∀ l, l ∈ Finset.Icc τ.card (N + 1) ∧
      l ∉ (insert τ d).image Finset.card → l = j)
    (hk : k ∈ Finset.Icc τ.card (N + 1)) (hkj : k ≠ j) :
    ∃! s, s ∈ insert τ d ∧ s.card = k := by
  have hkimage : k ∈ (insert τ d).image Finset.card := by
    by_contra hnot
    exact hkj (hjunique k ⟨hk, hnot⟩)
  obtain ⟨s, hs, hscard⟩ := Finset.mem_image.mp hkimage
  refine ⟨s, ⟨hs, hscard⟩, ?_⟩
  intro t ht
  apply h.injOn_card_insert hLK (Finset.mem_coe.mpr ht.1)
    (Finset.mem_coe.mpr hs)
  exact ht.2.trans hscard.symm

open Classical in
theorem IsRelFace.card_filter_gt_missing
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {N : ℕ} (hKcard : ∀ s ∈ K.faces, s.card ≤ N + 1)
    {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L τ d)
    {j : ℕ} (hj : j ∈ Finset.Icc τ.card (N + 1) ∧
      j ∉ (insert τ d).image Finset.card)
    (hjunique : ∀ k, k ∈ Finset.Icc τ.card (N + 1) ∧
      k ∉ (insert τ d).image Finset.card → k = j) :
    (d.filter fun s => j < s.card).card = N + 1 - j := by
  have himage : (d.filter fun s => j < s.card).image Finset.card =
      Finset.Icc (j + 1) (N + 1) := by
    ext k
    constructor
    · intro hk
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hsd, hjs⟩ := Finset.mem_filter.mp hs
      rw [Finset.mem_Icc]
      exact ⟨by omega, hKcard s (h.subset_faces s hsd)⟩
    · intro hk
      have hkIcc := Finset.mem_Icc.mp hk
      have hkGlobal : k ∈ Finset.Icc τ.card (N + 1) := by
        rw [Finset.mem_Icc]
        exact ⟨(Finset.mem_Icc.mp hj.1).1.trans (by omega), hkIcc.2⟩
      have hkj : k ≠ j := by omega
      obtain ⟨s, ⟨hs, hscard⟩, -⟩ := h.existsUnique_card_insert_of_ne_missing hLK
        hjunique hkGlobal hkj
      have hsd : s ∈ d := by
        rcases Finset.mem_insert.mp hs with hsτ | hsd
        · have hτj := (Finset.mem_Icc.mp hj.1).1
          rw [hsτ] at hscard
          omega
        · exact hsd
      exact Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨hsd, by omega⟩, hscard⟩
  have hinj : Set.InjOn Finset.card
      (((d.filter fun s => j < s.card) : Finset (Finset E)) : Set (Finset E)) :=
    (h.injOn_card_insert hLK).mono (fun s hs =>
      Finset.mem_coe.mpr (Finset.mem_insert_of_mem
        (Finset.mem_filter.mp (Finset.mem_coe.mp hs)).1))
  calc
    (d.filter fun s => j < s.card).card =
        ((d.filter fun s => j < s.card).image Finset.card).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = (Finset.Icc (j + 1) (N + 1)).card := congrArg Finset.card himage
    _ = N + 1 - j := by
      simp only [Nat.card_Icc]
      omega

open Classical in
noncomputable def relativeFaceBase
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    (f : Finset E) : Finset E :=
  if hf : f ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces then hf.choose else ∅

open Classical in
noncomputable def relativeFaceFlag
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    (f : Finset E) : Finset (Finset E) :=
  if hf : f ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces then hf.choose_spec.choose else ∅

open Classical in
theorem relativeFaceData_spec
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    {f : Finset E}
    (hf : f ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces) :
    IsRelFace K L L (relativeFaceBase K L hLK f) (relativeFaceFlag K L hLK f) ∧
      f = relativeFaceBase K L hLK f ∪
        (relativeFaceFlag K L hLK f).image (fun s => s.centroid ℝ id) := by
  rw [relativeFaceBase, relativeFaceFlag, dif_pos hf, dif_pos hf]
  exact hf.choose_spec.choose_spec

open Classical in
theorem relativeFaceBase_eq_of_isRelFace
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    {f τ : Finset E} {d : Finset (Finset E)} (h : IsRelFace K L L τ d)
    (hf : f = τ ∪ d.image fun s => s.centroid ℝ id) :
    relativeFaceBase K L hLK f = τ := by
  have hmem : f ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces := ⟨τ, d, h, hf⟩
  obtain ⟨hchosen, hchosenEq⟩ := relativeFaceData_spec K L hLK hmem
  exact (hchosen.eq_of_union_image_eq hLK (IsSubdivision.refl L)
    (fun s => s.centroid ℝ id) (centroid_mem_openSimplex_of_mem_faces K) h
    (hchosenEq.symm.trans hf)).1

open Classical in
theorem relativeFaceFlag_eq_of_isRelFace
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    {f τ : Finset E} {d : Finset (Finset E)} (h : IsRelFace K L L τ d)
    (hf : f = τ ∪ d.image fun s => s.centroid ℝ id) :
    relativeFaceFlag K L hLK f = d := by
  have hmem : f ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces := ⟨τ, d, h, hf⟩
  obtain ⟨hchosen, hchosenEq⟩ := relativeFaceData_spec K L hLK hmem
  exact (hchosen.eq_of_union_image_eq hLK (IsSubdivision.refl L)
    (fun s => s.centroid ℝ id) (centroid_mem_openSimplex_of_mem_faces K) h
    (hchosenEq.symm.trans hf)).2

open Classical in
noncomputable def relativeCofaceCarrier
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    (f g : Finset E) : Finset E :=
  if h : (relativeFaceFlag K L hLK g \ relativeFaceFlag K L hLK f).Nonempty then
    h.choose
  else
    relativeFaceBase K L hLK g

open Classical in
theorem relativeCofaceCarrier_eq_of_flag_insert
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    {f g : Finset E} {d : Finset (Finset E)} {m : Finset E}
    (hfd : relativeFaceFlag K L hLK f = d)
    (hgd : relativeFaceFlag K L hLK g = insert m d) (hm : m ∉ d) :
    relativeCofaceCarrier K L hLK f g = m := by
  unfold relativeCofaceCarrier
  rw [hfd, hgd]
  have hdiff : insert m d \ d = {m} := by
    ext s
    simp [hm]
  rw [hdiff]
  by_cases hne : ({m} : Finset (Finset E)).Nonempty
  · rw [dif_pos hne]
    exact Finset.mem_singleton.mp hne.choose_spec
  · exact False.elim (hne (Finset.singleton_nonempty m))

open Classical in
theorem relativeCofaceCarrier_eq_of_base_insert
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    {f g : Finset E} {d : Finset (Finset E)} {τ : Finset E} {v : E}
    (hfd : relativeFaceFlag K L hLK f = d)
    (hgd : relativeFaceFlag K L hLK g = d)
    (hgτ : relativeFaceBase K L hLK g = insert v τ) :
    relativeCofaceCarrier K L hLK f g = insert v τ := by
  simp [relativeCofaceCarrier, hfd, hgd, hgτ]

open Classical in
theorem relativeCofaceData
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {N : ℕ} {f g : Finset E}
    (hf : f ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces)
    (hg : g ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces)
    (hfg : f ⊆ g) (hfcard : f.card = N) (hgcard : g.card = N + 1) :
    (relativeFaceBase K L hLK g = relativeFaceBase K L hLK f ∧
        ∃ m ∉ relativeFaceFlag K L hLK f,
          relativeFaceFlag K L hLK g = insert m (relativeFaceFlag K L hLK f) ∧
          relativeCofaceCarrier K L hLK f g = m) ∨
      (relativeFaceFlag K L hLK g = relativeFaceFlag K L hLK f ∧
        ∃ v ∉ relativeFaceBase K L hLK f,
          relativeFaceBase K L hLK g = insert v (relativeFaceBase K L hLK f) ∧
          relativeCofaceCarrier K L hLK f g =
            insert v (relativeFaceBase K L hLK f)) := by
  obtain ⟨hfrel, hfeq⟩ := relativeFaceData_spec K L hLK hf
  obtain ⟨hgrel, hgeq⟩ := relativeFaceData_spec K L hLK hg
  have hsub := hfrel.data_subset_of_union_image_subset hLK (IsSubdivision.refl L)
    (fun s => s.centroid ℝ id) (centroid_mem_openSimplex_of_mem_faces K) hgrel
    (hfeq ▸ hgeq ▸ hfg)
  have hfdata : (relativeFaceBase K L hLK f).card +
      (relativeFaceFlag K L hLK f).card = N := by
    rw [← hfrel.card_union_image hLK (IsSubdivision.refl L)
      (fun s => s.centroid ℝ id) (centroid_mem_openSimplex_of_mem_faces K),
      ← hfeq]
    exact hfcard
  have hgdata : (relativeFaceBase K L hLK g).card +
      (relativeFaceFlag K L hLK g).card = N + 1 := by
    rw [← hgrel.card_union_image hLK (IsSubdivision.refl L)
      (fun s => s.centroid ℝ id) (centroid_mem_openSimplex_of_mem_faces K),
      ← hgeq]
    exact hgcard
  rcases relativeData_eq_or_eq_insert hsub.1 hsub.2 hfdata hgdata with hflag | hbase
  · left
    refine ⟨hflag.1, ?_⟩
    obtain ⟨m, hm, hgm⟩ := hflag.2
    exact ⟨m, hm, hgm,
      relativeCofaceCarrier_eq_of_flag_insert K L hLK rfl hgm hm⟩
  · right
    refine ⟨hbase.1, ?_⟩
    obtain ⟨v, hv, hgv⟩ := hbase.2
    exact ⟨v, hv, hgv,
      relativeCofaceCarrier_eq_of_base_insert K L hLK rfl hbase.1 hgv⟩

open Classical in
theorem relativeCofaceCarrier_mem_faces_and_missing
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {N : ℕ} (hKcard : ∀ s ∈ K.faces, s.card ≤ N + 1)
    {f g : Finset E}
    (hf : f ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces)
    (hg : g ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces)
    (hfg : f ⊆ g) (hfcard : f.card = N) (hgcard : g.card = N + 1) :
    relativeCofaceCarrier K L hLK f g ∈ K.faces ∧
      (relativeCofaceCarrier K L hLK f g).card ∈
        Finset.Icc (relativeFaceBase K L hLK f).card (N + 1) ∧
      (relativeCofaceCarrier K L hLK f g).card ∉
        (insert (relativeFaceBase K L hLK f) (relativeFaceFlag K L hLK f)).image
          Finset.card := by
  obtain ⟨hfrel, -⟩ := relativeFaceData_spec K L hLK hf
  obtain ⟨hgrel, -⟩ := relativeFaceData_spec K L hLK hg
  rcases relativeCofaceData hLK hf hg hfg hfcard hgcard with hflag | hbase
  · obtain ⟨hbaseEq, m, hm, hflagEq, hcarrier⟩ := hflag
    rw [hcarrier]
    have hmTop : m ∈ relativeFaceFlag K L hLK g := by
      rw [hflagEq]
      exact Finset.mem_insert_self m _
    have hmK : m ∈ K.faces := hgrel.subset_faces m hmTop
    refine ⟨hmK, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Finset.card_le_card (hbaseEq ▸ hgrel.base_subset_of_mem hLK hmTop),
        hKcard m hmK⟩
    · intro hmImage
      obtain ⟨s, hs, hscard⟩ := Finset.mem_image.mp hmImage
      have hmOld : m ∉ insert (relativeFaceBase K L hLK f)
          (relativeFaceFlag K L hLK f) := by
        intro hmOld
        rcases Finset.mem_insert.mp hmOld with hmBase | hmFlag
        · apply hgrel.base_not_mem_flag
          rw [hbaseEq, ← hmBase]
          exact hmTop
        · exact hm hmFlag
      have hsTop : s ∈ insert (relativeFaceBase K L hLK g)
          (relativeFaceFlag K L hLK g) := by
        rcases Finset.mem_insert.mp hs with hsBase | hsFlag
        · rw [Finset.mem_insert, hbaseEq]
          exact Or.inl hsBase
        · rw [Finset.mem_insert, hflagEq]
          exact Or.inr (Finset.mem_insert_of_mem hsFlag)
      have hmTop' : m ∈ insert (relativeFaceBase K L hLK g)
          (relativeFaceFlag K L hLK g) := Finset.mem_insert_of_mem hmTop
      exact hmOld (hgrel.injOn_card_insert hLK (Finset.mem_coe.mpr hmTop')
        (Finset.mem_coe.mpr hsTop) hscard.symm ▸ hs)
  · obtain ⟨hflagEq, v, hv, hbaseEq, hcarrier⟩ := hbase
    rw [hcarrier]
    have hbaseNonempty : (insert v (relativeFaceBase K L hLK f)).Nonempty :=
      ⟨v, Finset.mem_insert_self v _⟩
    have hbaseK : insert v (relativeFaceBase K L hLK f) ∈ K.faces := by
      rcases hgrel.base with hzero | hmem
      · exact False.elim (hbaseNonempty.ne_empty (hbaseEq ▸ hzero))
      · exact hLK (hbaseEq ▸ hmem)
    refine ⟨hbaseK, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Finset.card_le_card (Finset.subset_insert v _), hKcard _ hbaseK⟩
    · intro hImage
      obtain ⟨s, hs, hscard⟩ := Finset.mem_image.mp hImage
      rcases Finset.mem_insert.mp hs with hsBase | hsFlag
      · subst s
        rw [Finset.card_insert_of_notMem hv] at hscard
        omega
      · have hsTop : s ∈ insert (relativeFaceBase K L hLK g)
            (relativeFaceFlag K L hLK g) := by
          rw [Finset.mem_insert, hflagEq]
          exact Or.inr hsFlag
        have hbaseTop : relativeFaceBase K L hLK g ∈
            insert (relativeFaceBase K L hLK g) (relativeFaceFlag K L hLK g) :=
          Finset.mem_insert_self _ _
        have heq := hgrel.injOn_card_insert hLK (Finset.mem_coe.mpr hsTop)
          (Finset.mem_coe.mpr hbaseTop) (by rw [hbaseEq]; exact hscard)
        exact hgrel.base_not_mem_flag (heq ▸ (hflagEq ▸ hsFlag))

open Classical in
theorem relativeCofaceCarrier_injOn
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {N : ℕ} {f : Finset E}
    (hf : f ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces)
    (hfcard : f.card = N) :
    Set.InjOn (relativeCofaceCarrier K L hLK f)
      {g | g ∈ (relDerived hLK (IsSubdivision.refl L)
          (centroid_mem_openSimplex_of_mem_faces K)).faces ∧
        g.card = N + 1 ∧ f ⊆ g} := by
  intro g hg q hq hcarrier
  obtain ⟨hgrel, hgeq⟩ := relativeFaceData_spec K L hLK hg.1
  obtain ⟨hqrel, hqeq⟩ := relativeFaceData_spec K L hLK hq.1
  rcases relativeCofaceData hLK hf hg.1 hg.2.2 hfcard hg.2.1 with hgflag | hgbase <;>
    rcases relativeCofaceData hLK hf hq.1 hq.2.2 hfcard hq.2.1 with hqflag | hqbase
  · obtain ⟨hgτ, m, -, hgm, hgcarrier⟩ := hgflag
    obtain ⟨hqτ, p, -, hqp, hqcarrier⟩ := hqflag
    have hmp : m = p := hgcarrier.symm.trans (hcarrier.trans hqcarrier)
    rw [hgeq, hqeq, hgτ, hqτ, hgm, hqp, hmp]
  · obtain ⟨-, m, -, hgm, hgcarrier⟩ := hgflag
    obtain ⟨hqd, v, -, hqτ, hqcarrier⟩ := hqbase
    have hmL : m ∈ L.faces := by
      have hbaseNonempty : (insert v (relativeFaceBase K L hLK f)).Nonempty :=
        ⟨v, Finset.mem_insert_self v _⟩
      rcases hqrel.base with hzero | hmem
      · exact False.elim (hbaseNonempty.ne_empty (hqτ ▸ hzero))
      · rw [← hgcarrier, hcarrier, hqcarrier, ← hqτ]
        exact hmem
    exact False.elim (hgrel.notMem m (hgm ▸ Finset.mem_insert_self m _) hmL)
  · obtain ⟨hgd, v, -, hgτ, hgcarrier⟩ := hgbase
    obtain ⟨-, m, -, hqm, hqcarrier⟩ := hqflag
    have hmL : m ∈ L.faces := by
      have hbaseNonempty : (insert v (relativeFaceBase K L hLK f)).Nonempty :=
        ⟨v, Finset.mem_insert_self v _⟩
      rcases hgrel.base with hzero | hmem
      · exact False.elim (hbaseNonempty.ne_empty (hgτ ▸ hzero))
      · rw [← hqcarrier, ← hcarrier, hgcarrier, ← hgτ]
        exact hmem
    exact False.elim (hqrel.notMem m (hqm ▸ Finset.mem_insert_self m _) hmL)
  · obtain ⟨hgd, v, -, hgτ, hgcarrier⟩ := hgbase
    obtain ⟨hqd, w, -, hqτ, hqcarrier⟩ := hqbase
    have hbaseEq : insert v (relativeFaceBase K L hLK f) =
        insert w (relativeFaceBase K L hLK f) :=
      hgcarrier.symm.trans (hcarrier.trans hqcarrier)
    rw [hgeq, hqeq, hgd, hqd, hgτ, hqτ, hbaseEq]

open Classical in
theorem relativeCofaceCarrier_comparable
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {N : ℕ} {f g : Finset E}
    (hf : f ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces)
    (hg : g ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces)
    (hfg : f ⊆ g) (hfcard : f.card = N) (hgcard : g.card = N + 1)
    {u : Finset E}
    (hu : u ∈ insert (relativeFaceBase K L hLK f) (relativeFaceFlag K L hLK f)) :
    u ⊆ relativeCofaceCarrier K L hLK f g ∨
      relativeCofaceCarrier K L hLK f g ⊆ u := by
  obtain ⟨hgrel, -⟩ := relativeFaceData_spec K L hLK hg
  rcases relativeCofaceData hLK hf hg hfg hfcard hgcard with hflag | hbase
  · obtain ⟨hbaseEq, m, -, hflagEq, hcarrierEq⟩ := hflag
    rw [hcarrierEq]
    rcases Finset.mem_insert.mp hu with huBase | huFlag
    · left
      exact huBase ▸ hbaseEq ▸ hgrel.base_subset_of_mem hLK
        (hflagEq ▸ Finset.mem_insert_self m _)
    · exact hgrel.flag.subset_or_subset
        (hflagEq ▸ Finset.mem_insert_of_mem huFlag)
        (hflagEq ▸ Finset.mem_insert_self m _)
  · obtain ⟨hflagEq, v, -, hbaseEq, hcarrierEq⟩ := hbase
    rw [hcarrierEq]
    rcases Finset.mem_insert.mp hu with huBase | huFlag
    · left
      rw [huBase]
      exact Finset.subset_insert v _
    · right
      exact hbaseEq ▸ hgrel.base_subset_of_mem hLK (hflagEq ▸ huFlag)

noncomputable def relativeOrientationSign
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation N K) (L : Geometry.SimplicialComplex ℝ E)
    (hLK : L.faces ⊆ K.faces) (f : Finset E) : ℤ :=
  relativeTopCoefficient o.vertexOrder N o.sign
    (relativeFaceBase K L hLK f) (relativeFaceFlag K L hLK f)

open Classical in
theorem relativeOrientationSign_eq_one_or_neg_one
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation N K) (hLK : L.faces ⊆ K.faces)
    (hKcard : ∀ s ∈ K.faces, s.card ≤ N + 1)
    (hLcard : ∀ s ∈ L.faces, s.card ≤ N)
    {f : Finset E}
    (hf : f ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces)
    (hfcard : f.card = N + 1) :
    relativeOrientationSign o L hLK f = 1 ∨
      relativeOrientationSign o L hLK f = -1 := by
  obtain ⟨hrel, hfeq⟩ := relativeFaceData_spec K L hLK hf
  unfold relativeOrientationSign
  apply hrel.relativeTopCoefficient_eq_one_or_neg_one hLK hKcard hLcard
  · rw [← hfeq]
    exact hfcard
  · exact o.sign_top

open Classical in
theorem relativeOrientationCofaceTerm
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation N K) (hLK : L.faces ⊆ K.faces)
    (hKcard : ∀ s ∈ K.faces, s.card ≤ N + 1)
    (hLcard : ∀ s ∈ L.faces, s.card ≤ N)
    {f g : Finset E}
    (hf : f ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces)
    (hg : g ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces)
    (hfg : f ⊆ g) (hfcard : f.card = N) (hgcard : g.card = N + 1)
    {j : ℕ} (hj : j ∈ Finset.Icc (relativeFaceBase K L hLK f).card (N + 1) ∧
      j ∉ (insert (relativeFaceBase K L hLK f)
        (relativeFaceFlag K L hLK f)).image Finset.card)
    (hjunique : ∀ k, k ∈ Finset.Icc (relativeFaceBase K L hLK f).card (N + 1) ∧
      k ∉ (insert (relativeFaceBase K L hLK f)
        (relativeFaceFlag K L hLK f)).image Finset.card → k = j) :
    relativeOrientationSign o L hLK g *
        simplexBoundaryCoefficient (o.relativeVertexOrder L) g f =
      (-1 : ℤ) ^ (N + 1 - j) *
        relativeTopCoefficient o.vertexOrder N o.sign
          (relativeFaceBase K L hLK f)
          (insert (relativeCofaceCarrier K L hLK f g)
            (relativeFaceFlag K L hLK f)) := by
  obtain ⟨hfrel, hfeq⟩ := relativeFaceData_spec K L hLK hf
  obtain ⟨hgrel, hgeq⟩ := relativeFaceData_spec K L hLK hg
  have hcarrier := relativeCofaceCarrier_mem_faces_and_missing hLK hKcard
    hf hg hfg hfcard hgcard
  have hcarrierCard : (relativeCofaceCarrier K L hLK f g).card = j :=
    hjunique _ ⟨hcarrier.2.1, hcarrier.2.2⟩
  rcases relativeCofaceData hLK hf hg hfg hfcard hgcard with hflag | hbase
  · obtain ⟨hbaseEq, m, hm, hflagEq, hcarrierEq⟩ := hflag
    have hgrel' : IsRelFace K L L (relativeFaceBase K L hLK f)
        (insert m (relativeFaceFlag K L hLK f)) := by
      rwa [hbaseEq, hflagEq] at hgrel
    have hmj : m.card = j := by
      calc
        m.card = (relativeCofaceCarrier K L hLK f g).card :=
          congrArg Finset.card hcarrierEq.symm
        _ = j := hcarrierCard
    have hfilterCard :
        ((relativeFaceFlag K L hLK f).filter fun s => m.card < s.card).card =
          N + 1 - j := by
      simpa only [hmj] using hfrel.card_filter_gt_missing hLK hKcard hj hjunique
    have hcoefficient :
        simplexBoundaryCoefficient (o.relativeVertexOrder L) g f =
          (-1 : ℤ) ^ ((relativeFaceFlag K L hLK f).filter
            fun s => m.card < s.card).card := by
      calc
        simplexBoundaryCoefficient (o.relativeVertexOrder L) g f =
            simplexBoundaryCoefficient (o.relativeVertexOrder L)
              (relativeFaceBase K L hLK f ∪
                (insert m (relativeFaceFlag K L hLK f)).image
                  (fun s => s.centroid ℝ id)) f := by
          rw [hgeq, hbaseEq, hflagEq]
        _ = simplexBoundaryCoefficient (o.relativeVertexOrder L)
              (relativeFaceBase K L hLK f ∪
                (insert m (relativeFaceFlag K L hLK f)).image
                  (fun s => s.centroid ℝ id))
              (relativeFaceBase K L hLK f ∪
                (relativeFaceFlag K L hLK f).image (fun s => s.centroid ℝ id)) :=
          congrArg _ hfeq
        _ = _ := o.simplexBoundaryCoefficient_relative_centroid hLK hgrel' hm
    unfold relativeOrientationSign
    rw [hbaseEq, hflagEq, hcarrierEq, hcoefficient, hfilterCard]
    ring
  · obtain ⟨hflagEq, v, hv, hbaseEq, hcarrierEq⟩ := hbase
    let τ := relativeFaceBase K L hLK f
    let d := relativeFaceFlag K L hLK f
    let m := insert v τ
    have hgrel' : IsRelFace K L L m d := by
      simpa only [m, τ, d, hbaseEq, hflagEq] using hgrel
    have hmL : m ∈ L.faces := by
      rcases hgrel'.base with hzero | hmem
      · have hvEmpty : v ∈ (∅ : Finset E) := hzero ▸ Finset.mem_insert_self v τ
        exact False.elim (Finset.notMem_empty v hvEmpty)
      · exact hmem
    have hmN : m.card ≤ N := hLcard m hmL
    have hmcard : τ.card + 1 = m.card := by
      dsimp only [m, τ]
      exact (Finset.card_insert_of_notMem hv).symm
    have hfdata : τ.card + d.card = N := by
      have hcard := hfrel.card_union_image hLK (IsSubdivision.refl L)
        (fun s => s.centroid ℝ id) (centroid_mem_openSimplex_of_mem_faces K)
      rw [← hfeq, hfcard] at hcard
      exact hcard.symm
    have hmj : m.card = j := by
      simpa only [m, hcarrierEq] using hcarrierCard
    have hdcard : d.card = N + 1 - j := by omega
    have htop := hgrel'.relativeTopCoefficient_insert_base hLK o.vertexOrder o.sign
      hmcard hmN
    have hcoefficient :
        simplexBoundaryCoefficient (o.relativeVertexOrder L) g f =
          (-1 : ℤ) ^ d.card * simplexBoundaryCoefficient o.vertexOrder m τ := by
      rw [hgeq, hfeq, hbaseEq, hflagEq]
      exact o.simplexBoundaryCoefficient_relative_boundary hLK hgrel' hv
    unfold relativeOrientationSign
    simp only [τ, d, m] at hgrel' hmcard hfdata hmj hdcard htop hcoefficient ⊢
    have hdec : @Finset.decidableEq E o.vertexOrder.toDecidableEq =
        @Finset.decidableEq E (Classical.decEq E) := Subsingleton.elim _ _
    rw [hdec] at htop
    rw [hbaseEq, hflagEq, hcarrierEq, hcoefficient, hdcard]
    calc
      _ = (-1 : ℤ) ^ (N + 1 - j) *
          (relativeTopCoefficient o.vertexOrder N o.sign
              (insert v (relativeFaceBase K L hLK f))
              (relativeFaceFlag K L hLK f) *
            simplexBoundaryCoefficient o.vertexOrder
              (insert v (relativeFaceBase K L hLK f))
              (relativeFaceBase K L hLK f)) := by ring
      _ = _ := by
        simpa only using congrArg (fun z : ℤ => (-1 : ℤ) ^ (N + 1 - j) * z) htop.symm

open Classical in
theorem relativeTopCoefficient_coface_pair_cancel
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation (n + 1) K)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hLK : L.faces ⊆ K.faces) {f g q : Finset E}
    (hf : f ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces)
    (hg : g ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces)
    (hq : q ∈ (relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)).faces)
    (hfg : f ⊆ g) (hfq : f ⊆ q)
    (hfcard : f.card = n + 1)
    (hgcard : g.card = n + 2) (hqcard : q.card = n + 2)
    (hgq : g ≠ q) :
    relativeTopCoefficient o.vertexOrder (n + 1) o.sign
        (relativeFaceBase K L hLK f)
        (insert (relativeCofaceCarrier K L hLK f g)
          (relativeFaceFlag K L hLK f)) +
      relativeTopCoefficient o.vertexOrder (n + 1) o.sign
        (relativeFaceBase K L hLK f)
        (insert (relativeCofaceCarrier K L hLK f q)
          (relativeFaceFlag K L hLK f)) = 0 := by
  let τ := relativeFaceBase K L hLK f
  let d := relativeFaceFlag K L hLK f
  let m := relativeCofaceCarrier K L hLK f g
  let p := relativeCofaceCarrier K L hLK f q
  have hKcard : ∀ s ∈ K.faces, s.card ≤ (n + 1) + 1 := fun s hs => hK.card_le K hs
  obtain ⟨hfrel, hfeq⟩ := relativeFaceData_spec K L hLK hf
  have hfrel' : IsRelFace K L L τ d := by
    simpa only [τ, d] using hfrel
  have hfeq' : f = τ ∪ d.image (fun s => s.centroid ℝ id) := by
    simpa only [τ, d] using hfeq
  have hfaceDataCard : (τ ∪ d.image fun s => s.centroid ℝ id).card = n + 1 := by
    rw [← hfeq']
    exact hfcard
  obtain ⟨j, hj, hjunique⟩ :=
    hfrel'.existsUnique_missing_card hLK hKcard hfaceDataCard
  have hmData := relativeCofaceCarrier_mem_faces_and_missing hLK hKcard
    hf hg hfg hfcard hgcard
  have hpData := relativeCofaceCarrier_mem_faces_and_missing hLK hKcard
    hf hq hfq hfcard hqcard
  have hmK : m ∈ K.faces := by simpa only [m] using hmData.1
  have hpK : p ∈ K.faces := by simpa only [p] using hpData.1
  have hmIcc : m.card ∈ Finset.Icc τ.card (n + 2) := by
    simpa only [m, τ] using hmData.2.1
  have hpIcc : p.card ∈ Finset.Icc τ.card (n + 2) := by
    simpa only [p, τ] using hpData.2.1
  have hmMissing : m.card ∉ (insert τ d).image Finset.card := by
    simpa only [m, τ, d] using hmData.2.2
  have hpMissing : p.card ∉ (insert τ d).image Finset.card := by
    simpa only [p, τ, d] using hpData.2.2
  have hmcard : m.card = j := hjunique m.card ⟨hmIcc, hmMissing⟩
  have hpcard : p.card = j := hjunique p.card ⟨hpIcc, hpMissing⟩
  have hmp : m ≠ p := by
    intro hmp
    apply hgq
    apply relativeCofaceCarrier_injOn hLK hf hfcard
    · exact ⟨hg, hgcard, hfg⟩
    · exact ⟨hq, hqcard, hfq⟩
    · simpa only [m, p] using hmp
  have hmNotD : m ∉ d := by
    intro hmd
    apply hmMissing
    exact Finset.mem_image.mpr ⟨m, Finset.mem_insert_of_mem hmd, rfl⟩
  have hpNotD : p ∉ d := by
    intro hpd
    apply hpMissing
    exact Finset.mem_image.mpr ⟨p, Finset.mem_insert_of_mem hpd, rfl⟩
  have hmNeτ : m ≠ τ := by
    intro hmτ
    apply hmMissing
    exact Finset.mem_image.mpr ⟨m, Finset.mem_insert.mpr (Or.inl hmτ), rfl⟩
  have hpNeτ : p ≠ τ := by
    intro hpτ
    apply hpMissing
    exact Finset.mem_image.mpr ⟨p, Finset.mem_insert.mpr (Or.inl hpτ), rfl⟩
  change relativeTopCoefficient o.vertexOrder (n + 1) o.sign τ (insert m d) +
      relativeTopCoefficient o.vertexOrder (n + 1) o.sign τ (insert p d) = 0
  by_cases hjTop : j = n + 2
  · have hτcard : τ.card ≤ n + 1 := by
      have hsub : τ ⊆ τ ∪ d.image (fun s => s.centroid ℝ id) := Finset.subset_union_left
      have := Finset.card_le_card hsub
      rw [hfaceDataCard] at this
      exact this
    have hkIcc : n + 1 ∈ Finset.Icc τ.card (n + 2) := by
      rw [Finset.mem_Icc]
      exact ⟨hτcard, by omega⟩
    have hnotTop : n + 1 ≠ j := by omega
    obtain ⟨u, hu, huunique⟩ :=
      hfrel'.existsUnique_card_insert_of_ne_missing hLK hjunique hkIcc hnotTop
    have hucard : u.card = n + 1 := hu.2
    have huK : u ∈ K.faces := by
      rcases Finset.mem_insert.mp hu.1 with huτ | hud
      · subst u
        rcases hfrel'.base with hτzero | hτL
        · rw [hτzero, Finset.card_empty] at hucard
          omega
        · exact hLK hτL
      · exact hfrel'.subset_faces u hud
    have hmcardTop : m.card = n + 2 := hmcard.trans hjTop
    have hpcardTop : p.card = n + 2 := hpcard.trans hjTop
    have hum : u ⊆ m := by
      have hcomp := relativeCofaceCarrier_comparable hLK hf hg hfg hfcard hgcard hu.1
      have hcomp' : u ⊆ m ∨ m ⊆ u := by simpa only [m] using hcomp
      rcases hcomp' with hum | hmu
      · exact hum
      · have := Finset.card_le_card hmu
        omega
    have hup : u ⊆ p := by
      have hcomp := relativeCofaceCarrier_comparable hLK hf hq hfq hfcard hqcard hu.1
      have hcomp' : u ⊆ p ∨ p ⊆ u := by simpa only [p] using hcomp
      rcases hcomp' with hup | hpu
      · exact hup
      · have := Finset.card_le_card hpu
        omega
    have hmco : m ∈ faceCofaces K u (n + 2) :=
      (mem_faceCofaces K).mpr ⟨hmK, hmcardTop, hum⟩
    have hpco : p ∈ faceCofaces K u (n + 2) :=
      (mem_faceCofaces K).mpr ⟨hpK, hpcardTop, hup⟩
    have hnotone : (faceCofaces K u (n + 2)).card ≠ 1 := by
      intro hone
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hone
      have hmz : m = z := by simpa [hz] using hmco
      have hpz : p = z := by simpa [hz] using hpco
      exact hmp (hmz.trans hpz.symm)
    have htwo : (faceCofaces K u (n + 2)).card = 2 :=
      (hK.card_faceCofaces_eq_one_or_two K huK hucard).resolve_left hnotone
    have hpairSub : ({m, p} : Finset (Finset E)) ⊆ faceCofaces K u (n + 2) := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hmco, hpco⟩
    have hcofaces : faceCofaces K u (n + 2) = {m, p} := by
      apply (Finset.eq_of_subset_of_card_le hpairSub ?_).symm
      rw [htwo]
      simp [hmp]
    have horiginal := o.coherent u huK hucard hnotone
    rw [orientedBoundary_eq_sum_faceCofaces, hcofaces] at horiginal
    simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton, hmp,
      not_false_eq_true] at horiginal
    have hdcard : ∀ s ∈ d, s.card ≤ n + 1 := by
      intro s hs
      have hsK := hfrel'.subset_faces s hs
      have hsle := hKcard s hsK
      have hsne : s.card ≠ n + 2 := by
        intro hscard
        apply hj.2
        rw [hjTop, ← hscard]
        exact Finset.mem_image.mpr ⟨s, Finset.mem_insert_of_mem hs, rfl⟩
      omega
    have hdec : @Finset.decidableEq E o.vertexOrder.toDecidableEq =
        @Finset.decidableEq E (Classical.decEq E) := Subsingleton.elim _ _
    have huOrder : u ∈ @insert (Finset E) (Finset (Finset E))
        (@Finset.instInsert (Finset E) (@Finset.decidableEq E o.vertexOrder.toDecidableEq))
        τ d := by
      rw [hdec]
      exact hu.1
    have huUniqueOrder : ∀ t ∈ @insert (Finset E) (Finset (Finset E))
        (@Finset.instInsert (Finset E) (@Finset.decidableEq E o.vertexOrder.toDecidableEq))
        τ d,
        t.card = n + 1 → t = u := by
      intro t ht htcard
      rw [hdec] at ht
      exact huunique t ⟨ht, htcard⟩
    have hmTop := relativeTopCoefficient_insert_top o.vertexOrder (n + 1) o.sign τ d
      hmNotD hmNeτ hmcardTop hdcard huOrder hucard huUniqueOrder
    have hpTop := relativeTopCoefficient_insert_top o.vertexOrder (n + 1) o.sign τ d
      hpNotD hpNeτ hpcardTop hdcard huOrder hucard huUniqueOrder
    rw [hdec] at hmTop hpTop
    rw [hmTop, hpTop]
    calc
      _ = relativeTopCoefficient o.vertexOrder (n + 1) o.sign τ d *
          (o.sign m * simplexBoundaryCoefficient o.vertexOrder m u +
            o.sign p * simplexBoundaryCoefficient o.vertexOrder p u) := by ring
      _ = 0 := by rw [horiginal, mul_zero]
  · have hjLe : j ≤ n + 1 := by
      have := (Finset.mem_Icc.mp hj.1).2
      omega
    have hτj : τ.card < j := by
      have hτle := (Finset.mem_Icc.mp hj.1).1
      have hτne : τ.card ≠ j := by
        intro hτeq
        apply hj.2
        rw [← hτeq]
        exact Finset.mem_image.mpr ⟨τ, Finset.mem_insert_self τ d, rfl⟩
      omega
    have haIcc : j - 1 ∈ Finset.Icc τ.card (n + 2) := by
      rw [Finset.mem_Icc]
      exact ⟨by omega, by omega⟩
    have hbIcc : j + 1 ∈ Finset.Icc τ.card (n + 2) := by
      rw [Finset.mem_Icc]
      exact ⟨by omega, by omega⟩
    have haj : j - 1 ≠ j := by omega
    have hbj : j + 1 ≠ j := by omega
    obtain ⟨a, ha, haunique⟩ :=
      hfrel'.existsUnique_card_insert_of_ne_missing hLK hjunique haIcc haj
    obtain ⟨b, hb, hbunique⟩ :=
      hfrel'.existsUnique_card_insert_of_ne_missing hLK hjunique hbIcc hbj
    have hacard : a.card + 1 = m.card := by omega
    have hapcard : a.card + 1 = p.card := by omega
    have hmbcard : m.card + 1 = b.card := by omega
    have hbD : b ∈ d := by
      rcases Finset.mem_insert.mp hb.1 with hbτ | hbd
      · have := hb.2
        rw [hbτ] at this
        omega
      · exact hbd
    have ham : a ⊆ m := by
      have hcomp := relativeCofaceCarrier_comparable hLK hf hg hfg hfcard hgcard ha.1
      have hcomp' : a ⊆ m ∨ m ⊆ a := by simpa only [m] using hcomp
      rcases hcomp' with ham | hma
      · exact ham
      · have := Finset.card_le_card hma
        omega
    have hap : a ⊆ p := by
      have hcomp := relativeCofaceCarrier_comparable hLK hf hq hfq hfcard hqcard ha.1
      have hcomp' : a ⊆ p ∨ p ⊆ a := by simpa only [p] using hcomp
      rcases hcomp' with hap | hpa
      · exact hap
      · have := Finset.card_le_card hpa
        omega
    have hmb : m ⊆ b := by
      have hcomp := relativeCofaceCarrier_comparable hLK hf hg hfg hfcard hgcard hb.1
      have hcomp' : b ⊆ m ∨ m ⊆ b := by simpa only [m] using hcomp
      rcases hcomp' with hbm | hmb
      · have := Finset.card_le_card hbm
        exact False.elim (by omega)
      · exact hmb
    have hpb : p ⊆ b := by
      have hcomp := relativeCofaceCarrier_comparable hLK hf hq hfq hfcard hqcard hb.1
      have hcomp' : b ⊆ p ∨ p ⊆ b := by simpa only [p] using hcomp
      rcases hcomp' with hbp | hpb
      · have := Finset.card_le_card hbp
        exact False.elim (by omega)
      · exact hpb
    have haUnique' : ∀ t ∈ insert τ d, t.card + 1 = m.card → t = a := by
      intro t ht htcard
      apply haunique t
      exact ⟨ht, by omega⟩
    have hbUnique' : ∀ s ∈ d, m.card + 1 = s.card → s = b := by
      intro s hs hscard
      apply hbunique s
      exact ⟨Finset.mem_insert_of_mem hs, by omega⟩
    have hpHaUnique : ∀ t ∈ insert τ d, t.card + 1 = p.card → t = a := by
      intro t ht htcard
      apply haunique t
      exact ⟨ht, by omega⟩
    have hpHbUnique : ∀ s ∈ d, p.card + 1 = s.card → s = b := by
      intro s hs hscard
      apply hbunique s
      exact ⟨Finset.mem_insert_of_mem hs, by omega⟩
    have hmLe : m.card ≤ n + 1 := by omega
    have hpLe : p.card ≤ n + 1 := by omega
    have hdec : @Finset.decidableEq E o.vertexOrder.toDecidableEq =
        @Finset.decidableEq E (Classical.decEq E) := Subsingleton.elim _ _
    have haOrder : a ∈ @insert (Finset E) (Finset (Finset E))
        (@Finset.instInsert (Finset E) (@Finset.decidableEq E o.vertexOrder.toDecidableEq))
        τ d := by
      rw [hdec]
      exact ha.1
    have haUniqueOrder : ∀ t ∈ @insert (Finset E) (Finset (Finset E))
        (@Finset.instInsert (Finset E) (@Finset.decidableEq E o.vertexOrder.toDecidableEq))
        τ d,
        t.card + 1 = m.card → t = a := by
      intro t ht htcard
      rw [hdec] at ht
      exact haUnique' t ht htcard
    have hpHaUniqueOrder : ∀ t ∈ @insert (Finset E) (Finset (Finset E))
        (@Finset.instInsert (Finset E) (@Finset.decidableEq E o.vertexOrder.toDecidableEq))
        τ d,
        t.card + 1 = p.card → t = a := by
      intro t ht htcard
      rw [hdec] at ht
      exact hpHaUnique t ht htcard
    have hmMiddle := relativeTopCoefficient_insert_middle o.vertexOrder (n + 1) o.sign τ d
      hmNotD hmNeτ hmLe haOrder hacard haUniqueOrder hbD hmbcard hbUnique'
    have hpMiddle := relativeTopCoefficient_insert_middle o.vertexOrder (n + 1) o.sign τ d
      hpNotD hpNeτ hpLe haOrder hapcard hpHaUniqueOrder hbD (by omega) hpHbUnique
    rw [hdec] at hmMiddle hpMiddle
    have hcancel := simplexBoundaryCoefficient_pair_cancel o.vertexOrder
      ham hacard hmb hmbcard hap hapcard hpb hmp
    rw [hmMiddle, hpMiddle]
    calc
      _ = relativeTopCoefficient o.vertexOrder (n + 1) o.sign τ d *
          (simplexBoundaryCoefficient o.vertexOrder b m *
              simplexBoundaryCoefficient o.vertexOrder m a +
            simplexBoundaryCoefficient o.vertexOrder b p *
              simplexBoundaryCoefficient o.vertexOrder p a) := by ring
      _ = 0 := by rw [hcancel, mul_zero]

open Classical in
noncomputable def CoherentOrientation.relativeSubdivision
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {K L : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] [Finite L.faces]
    (o : CoherentOrientation (n + 1) K)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hLK : L.faces ⊆ K.faces)
    (hLcard : ∀ s ∈ L.faces, s.card ≤ n + 1) :
    CoherentOrientation (n + 1)
      (relDerived hLK (IsSubdivision.refl L)
        (centroid_mem_openSimplex_of_mem_faces K)) where
  vertexOrder := o.relativeVertexOrder L
  sign := relativeOrientationSign o L hLK
  sign_top := by
    intro s hs hscard
    exact relativeOrientationSign_eq_one_or_neg_one o hLK
      (fun t ht => hK.card_le K ht) hLcard hs hscard
  coherent := by
    intro f hf hfcard hnotone
    let R := relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K)
    have hR : IsCombinatorialManifoldWithBoundary (n + 1) R :=
      hK.of_isSubdivision (relDerived_isSubdivision hLK (IsSubdivision.refl L)
        (centroid_mem_openSimplex_of_mem_faces K))
    have htwo : (faceCofaces R f (n + 2)).card = 2 :=
      (hR.card_faceCofaces_eq_one_or_two R hf hfcard).resolve_left hnotone
    obtain ⟨g, q, hgq, hcofaces⟩ := Finset.card_eq_two.mp htwo
    have hgco : g ∈ faceCofaces R f (n + 2) := by
      rw [hcofaces]
      exact Finset.mem_insert_self g {q}
    have hqco : q ∈ faceCofaces R f (n + 2) := by
      rw [hcofaces]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
    obtain ⟨hg, hgcard, hfg⟩ := (mem_faceCofaces R).mp hgco
    obtain ⟨hq, hqcard, hfq⟩ := (mem_faceCofaces R).mp hqco
    obtain ⟨hfrel, hfeq⟩ := relativeFaceData_spec K L hLK hf
    have hfaceDataCard :
        ((relativeFaceBase K L hLK f) ∪
          (relativeFaceFlag K L hLK f).image (fun s => s.centroid ℝ id)).card =
            n + 1 := by
      rw [← hfeq]
      exact hfcard
    obtain ⟨j, hj, hjunique⟩ := hfrel.existsUnique_missing_card hLK
      (fun t ht => hK.card_le K ht) hfaceDataCard
    have hgTerm := relativeOrientationCofaceTerm o hLK
      (fun t ht => hK.card_le K ht) hLcard hf hg hfg hfcard hgcard hj hjunique
    have hqTerm := relativeOrientationCofaceTerm o hLK
      (fun t ht => hK.card_le K ht) hLcard hf hq hfq hfcard hqcard hj hjunique
    have hcancel := relativeTopCoefficient_coface_pair_cancel o hK hLK
      hf hg hq hfg hfq hfcard hgcard hqcard hgq
    rw [orientedBoundary_eq_sum_faceCofaces, hcofaces]
    simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton, hgq,
      not_false_eq_true]
    rw [hgTerm, hqTerm, ← mul_add, hcancel, mul_zero]

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

section

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

open Classical in
noncomputable instance finite_boundaryRelSubdivision_faces
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Finite (boundaryRelSubdivision n K).faces :=
  (boundaryRelSubdivision_faces_finite n K).to_subtype

open Classical in
noncomputable instance finite_double_faces
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Finite (double n K).faces := by
  exact (gluedComplex_faces_finite (boundaryRelSubdivision n K) K
    (isGlueIso_id (boundaryComplex n K))
    (boundaryComplex_faces_subset n K)
    (boundaryComplex_full_boundaryRelSubdivision n K)).to_subtype

open Classical in
noncomputable def CoherentOrientation.boundaryRelSubdivision
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (o : CoherentOrientation (n + 1) K) :
    CoherentOrientation (n + 1) (boundaryRelSubdivision (n + 1) K) := by
  exact o.relativeSubdivision hK (boundaryComplex_faces_subset (n + 1) K)
    (fun s hs => ((hK.mem_boundaryComplex_faces_iff K).mp hs).2.1)

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem isPLSphere_gluedComplex_of_isPLBall
    [FiniteDimensional ℝ E]
    (K₁ K₂ A : Geometry.SimplicialComplex ℝ E)
    [Finite K₁.faces] [Finite K₂.faces] [Finite A.faces]
    {n : ℕ} (hK₁ : IsPLBall (n + 1) K₁.space)
    (hK₂ : IsPLBall (n + 1) K₂.space)
    (hA₁ : A = boundaryComplex (n + 1) K₁)
    (hA₂ : A = boundaryComplex (n + 1) K₂)
    (hfull : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A.faces) → s ∈ A.faces) :
    IsPLSphere (n + 1) (gluedComplex K₁ K₂ (isGlueIso_id A)
      (by rw [hA₂]; exact boundaryComplex_faces_subset (n + 1) K₂) hfull).space := by
  classical
  have hAK₁ : A.faces ⊆ K₁.faces := by
    rw [hA₁]
    exact boundaryComplex_faces_subset (n + 1) K₁
  have hAK₂ : A.faces ⊆ K₂.faces := by
    rw [hA₂]
    exact boundaryComplex_faces_subset (n + 1) K₂
  have hidA : IsPLHomeomorphOn id A.space A.space :=
    (isGlueIso_id A).isPLHomeomorphOn.congr
      (fun x hx => (simplicialMap_id_eq_of_mem A hx).symm)
  have hboundary : IsPLHomeomorphOn id
      (boundaryComplex (n + 1) K₁).space
      (boundaryComplex (n + 1) K₂).space := by
    rw [← hA₁, ← hA₂]
    exact hidA
  obtain ⟨G, hG, hGA⟩ :=
    exists_isPLHomeomorphOn_of_boundaryComplex K₁ K₂ hK₁ hK₂ hboundary
  let R₂ := boundaryRelSubdivision (n + 1) K₂
  let hR₂finite : Finite R₂.faces :=
    (boundaryRelSubdivision_faces_finite (n + 1) K₂).to_subtype
  have hR₂sub : IsSubdivision R₂ K₂ := boundaryRelSubdivision_isSubdivision (n + 1) K₂
  let ι₁ := simplicialMap R₂ (glueEmbed₁ A id)
  let ι₂ := simplicialMap K₂ (glueEmbed₂ A id)
  let g₁ := ι₁ ∘ G
  let g₂ := ι₂
  let Y₁ := (glued₁ R₂ A id).space
  let Y₂ := (glued₂ K₂ A id).space
  have hemb₁ := isPLHomeomorphOn_embedComplex R₂ (glueEmbed₁ A id)
    (glueFst E E) (fun _ _ _ _ => rfl)
  have hemb₂ := isPLHomeomorphOn_embedComplex K₂ (glueEmbed₂ A id)
    (glueSnd E E) (fun _ _ _ _ => rfl)
  have hGR₂ : IsPLHomeomorphOn G K₁.space R₂.space := by
    rw [hR₂sub.space_eq]
    exact hG
  have hg₁ : IsPLHomeomorphOn g₁ K₁.space Y₁ := hGR₂.trans hemb₁
  have hg₂ : IsPLHomeomorphOn g₂ K₂.space Y₂ := hemb₂
  have hcompat : ∀ x ∈ A.space, g₂ (simplicialMap A id x) = g₁ x := by
    intro x hx
    rw [simplicialMap_id_eq_of_mem A hx]
    have hGx : G x = x := hGA (hA₁ ▸ hx)
    change ι₂ x = ι₁ (G x)
    rw [hGx]
    exact (simplicialMap_glueEmbed_id_eq R₂ K₂ A
      (by rw [hA₂]; exact boundaryComplex_faces_subset_boundaryRelSubdivision (n + 1) K₂)
      hAK₂ hx).symm
  have hoverlap : Y₁ ∩ Y₂ = g₁ '' A.space := by
    have hAR₂ : A.faces ⊆ R₂.faces := by
      rw [hA₂]
      exact boundaryComplex_faces_subset_boundaryRelSubdivision (n + 1) K₂
    calc
      Y₁ ∩ Y₂ = ι₁ '' A.space :=
        glued₁_space_inter_glued₂_space R₂ K₂ (isGlueIso_id A) hAR₂ hAK₂
          (by
            rw [hA₂]
            exact boundaryComplex_full_boundaryRelSubdivision (n + 1) K₂)
      _ = ι₁ '' (G '' A.space) := by
        congr 1
        ext y
        constructor
        · intro hy
          exact ⟨y, hy, by simpa using hGA (hA₁ ▸ hy)⟩
        · rintro ⟨x, hx, rfl⟩
          rwa [hGA (hA₁ ▸ hx)]
      _ = g₁ '' A.space := by rw [Set.image_image]; rfl
  have hmap := isPLHomeomorphOn_gluedMap_of_full K₁ K₂ A A id id
    (isGlueIso_id A) hAK₁ hAK₂ hfull g₁ g₂ Y₁ Y₂ hg₁ hg₂ hcompat hoverlap
  rw [← gluedComplex_space R₂ K₂ (isGlueIso_id A) hAK₂ (by
    rw [hA₂]
    exact boundaryComplex_full_boundaryRelSubdivision (n + 1) K₂)] at hmap
  have hdouble : IsPLHomeomorphOn (gluedMap K₁ A id g₁ g₂)
      (gluedComplex K₁ K₂ (isGlueIso_id A) hAK₂ hfull).space
      (double (n + 1) K₂).space := by
    simpa only [double, R₂, hA₂] using hmap
  exact (isPLSphere_double_of_isPLBall K₂ hK₂).of_isPLHomeomorphOn hdouble.symm

theorem eq_of_faces_subset_of_space_eq
    (K L R : Geometry.SimplicialComplex ℝ E)
    (hKR : K.faces ⊆ R.faces) (hLR : L.faces ⊆ R.faces)
    (hspace : K.space = L.space) : K = L := by
  apply Geometry.SimplicialComplex.ext
  ext s
  constructor
  · intro hsK
    have hsR := hKR hsK
    have hx := centroid_mem_openSimplex_of_mem_faces R s hsR
    have hxL : s.centroid ℝ id ∈ L.space := by
      rw [← hspace]
      exact K.convexHull_subset_space hsK (openSimplex_subset_convexHull s hx)
    obtain ⟨t, htL, hxt⟩ := L.mem_space_iff.mp hxL
    have hst := face_subset_of_mem_openSimplex_of_mem_convexHull R hsR (hLR htL) hx hxt
    exact L.down_closed htL hst (K.nonempty_of_mem_faces hsK)
  · intro hsL
    have hsR := hLR hsL
    have hx := centroid_mem_openSimplex_of_mem_faces R s hsR
    have hxK : s.centroid ℝ id ∈ K.space := by
      rw [hspace]
      exact L.convexHull_subset_space hsL (openSimplex_subset_convexHull s hx)
    obtain ⟨t, htK, hxt⟩ := K.mem_space_iff.mp hxK
    have hst := face_subset_of_mem_openSimplex_of_mem_convexHull R hsR (hKR htK) hx hxt
    exact K.down_closed htK hst (L.nonempty_of_mem_faces hsL)

open Classical in
theorem boundaryComplex_boundaryRelSubdivision
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) :
    boundaryComplex (n + 1) (boundaryRelSubdivision (n + 1) K) =
      boundaryComplex (n + 1) K := by
  classical
  let R := boundaryRelSubdivision (n + 1) K
  let hRfinite : Finite R.faces :=
    (boundaryRelSubdivision_faces_finite (n + 1) K).to_subtype
  have hR : IsSubdivision R K := boundaryRelSubdivision_isSubdivision (n + 1) K
  apply eq_of_faces_subset_of_space_eq
    (boundaryComplex (n + 1) R) (boundaryComplex (n + 1) K) R
  · exact boundaryComplex_faces_subset (n + 1) R
  · exact boundaryComplex_faces_subset_boundaryRelSubdivision (n + 1) K
  · exact boundaryComplex_space_of_isSubdivision K R hK hR

open Classical in
theorem CoherentOrientation.orientedBoundary_boundaryRelSubdivision_eq
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 2) K)
    (o : CoherentOrientation (n + 2) K) {t : Finset E}
    (htB : t ∈ (boundaryComplex (n + 2) K).faces) (htcard : t.card = n + 2) :
    orientedBoundary (o.boundaryRelSubdivision K hK).vertexOrder
        (DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K)
        (n + 2)
        (o.boundaryRelSubdivision K hK).sign t =
      orientedBoundary o.vertexOrder K (n + 2) o.sign t := by
  let B := boundaryComplex (n + 2) K
  let R := DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K
  have hBK : B.faces ⊆ K.faces := boundaryComplex_faces_subset (n + 2) K
  have htR : t ∈ R.faces := boundaryComplex_faces_subset_boundaryRelSubdivision
    (n + 2) K htB
  have hR : IsCombinatorialManifoldWithBoundary (n + 2) R :=
    hK.of_isSubdivision (boundaryRelSubdivision_isSubdivision (n + 2) K)
  have htBR : t ∈ (boundaryComplex (n + 2) R).faces := by
    rw [boundaryComplex_boundaryRelSubdivision K hK]
    exact htB
  have hRone : (faceCofaces R t (n + 3)).card = 1 :=
    (hR.mem_boundaryComplex_iff_card_cofaces_eq_one R htR htcard).mp htBR
  have hKone : (faceCofaces K t (n + 3)).card = 1 :=
    (hK.mem_boundaryComplex_iff_card_cofaces_eq_one K (hBK htB) htcard).mp htB
  obtain ⟨g, hgcofaces⟩ := Finset.card_eq_one.mp hRone
  obtain ⟨q, hqcofaces⟩ := Finset.card_eq_one.mp hKone
  have hgco : g ∈ faceCofaces R t (n + 3) := by
    rw [hgcofaces]
    exact Finset.mem_singleton_self g
  have hqco : q ∈ faceCofaces K t (n + 3) := by
    rw [hqcofaces]
    exact Finset.mem_singleton_self q
  obtain ⟨hgR, hgcard, htg⟩ := (mem_faceCofaces R).mp hgco
  have htRel : IsRelFace K B B t ∅ := by
    refine ⟨Or.inr htB, ⟨?_, ?_⟩, ?_, ?_, Or.inl ?_⟩
    · intro s hs
      exact False.elim (Finset.notMem_empty s hs)
    · intro s hs
      exact False.elim (Finset.notMem_empty s hs)
    · intro s hs
      exact False.elim (Finset.notMem_empty s hs)
    · intro s hs
      exact False.elim (Finset.notMem_empty s hs)
    · exact (boundaryComplex (n + 2) K).nonempty_of_mem_faces htB
  have htEq : t = t ∪ (∅ : Finset (Finset E)).image (fun s => s.centroid ℝ id) := by
    simp
  have hbase : relativeFaceBase K B hBK t = t :=
    relativeFaceBase_eq_of_isRelFace K B hBK htRel htEq
  have hflag : relativeFaceFlag K B hBK t = ∅ :=
    relativeFaceFlag_eq_of_isRelFace K B hBK htRel htEq
  have hj : n + 3 ∈ Finset.Icc (relativeFaceBase K B hBK t).card (n + 3) ∧
      n + 3 ∉ (insert (relativeFaceBase K B hBK t)
        (relativeFaceFlag K B hBK t)).image Finset.card := by
    constructor
    · rw [Finset.mem_Icc, hbase, htcard]
      omega
    · rw [hbase, hflag]
      simp [htcard]
  have hjunique : ∀ k, k ∈ Finset.Icc (relativeFaceBase K B hBK t).card (n + 3) ∧
      k ∉ (insert (relativeFaceBase K B hBK t)
        (relativeFaceFlag K B hBK t)).image Finset.card → k = n + 3 := by
    intro k hk
    rw [hbase, hflag] at hk
    simp only [Finset.insert_empty, Finset.image_singleton, Finset.mem_Icc,
      Finset.mem_singleton] at hk
    omega
  have hKcard : ∀ s ∈ K.faces, s.card ≤ (n + 2) + 1 :=
    fun s hs => hK.card_le K hs
  have hBcard : ∀ s ∈ B.faces, s.card ≤ n + 2 :=
    fun s hs => ((hK.mem_boundaryComplex_faces_iff K).mp hs).2.1
  have hterm := relativeOrientationCofaceTerm o hBK hKcard hBcard
    htR hgR htg htcard hgcard hj hjunique
  let m := relativeCofaceCarrier K B hBK t g
  have hmData := relativeCofaceCarrier_mem_faces_and_missing hBK hKcard
    htR hgR htg htcard hgcard
  have hmK : m ∈ K.faces := by simpa only [m] using hmData.1
  have hmcard : m.card = n + 3 := by
    apply hjunique m.card
    simpa only [m] using hmData.2
  have htm : t ⊆ m := by
    rcases relativeCofaceCarrier_comparable hBK htR hgR htg htcard hgcard
        (show t ∈ insert (relativeFaceBase K B hBK t)
          (relativeFaceFlag K B hBK t) by rw [hbase, hflag]; simp) with htm | hmt
    · simpa only [m] using htm
    · have hle : m.card ≤ t.card := by
        simpa only [m] using Finset.card_le_card hmt
      exact False.elim (by omega)
  have hmco : m ∈ faceCofaces K t (n + 3) :=
    (mem_faceCofaces K).mpr ⟨hmK, hmcard, htm⟩
  have hmq : m = q := by
    rw [hqcofaces, Finset.mem_singleton] at hmco
    exact hmco
  have hmNotEmpty : m ∉ (∅ : Finset (Finset E)) := Finset.notMem_empty m
  have hmNeT : m ≠ t := by
    intro hmt
    rw [hmt, htcard] at hmcard
    omega
  have hdec : @Finset.decidableEq E o.vertexOrder.toDecidableEq =
      @Finset.decidableEq E (Classical.decEq E) := Subsingleton.elim _ _
  have htOrder : t ∈ @insert (Finset E) (Finset (Finset E))
      (@Finset.instInsert (Finset E) (@Finset.decidableEq E o.vertexOrder.toDecidableEq))
      t ∅ := by
    rw [hdec]
    exact Finset.mem_insert_self t ∅
  have htUniqueOrder : ∀ u ∈ @insert (Finset E) (Finset (Finset E))
      (@Finset.instInsert (Finset E) (@Finset.decidableEq E o.vertexOrder.toDecidableEq))
      t ∅, u.card = n + 2 → u = t := by
    intro u hu _
    rw [hdec] at hu
    simpa using hu
  have htop := relativeTopCoefficient_insert_top o.vertexOrder (n + 2) o.sign t ∅
    hmNotEmpty hmNeT hmcard (fun s hs => False.elim (Finset.notMem_empty s hs))
    htOrder htcard htUniqueOrder
  rw [hdec] at htop
  have hempty : relativeTopCoefficient o.vertexOrder (n + 2) o.sign t ∅ = 1 := by
    simp [relativeTopCoefficient, relativeFlagBoundaryProduct]
  rw [hempty, one_mul] at htop
  have hterm' :
      (o.boundaryRelSubdivision K hK).sign g *
          simplexBoundaryCoefficient (o.boundaryRelSubdivision K hK).vertexOrder g t =
        o.sign m * simplexBoundaryCoefficient o.vertexOrder m t := by
    change relativeOrientationSign o B hBK g *
        simplexBoundaryCoefficient (o.relativeVertexOrder B) g t = _
    calc
      _ = (-1 : ℤ) ^ ((n + 2) + 1 - (n + 3)) *
          relativeTopCoefficient o.vertexOrder (n + 2) o.sign
            (relativeFaceBase K B hBK t)
            (insert (relativeCofaceCarrier K B hBK t g)
              (relativeFaceFlag K B hBK t)) := hterm
      _ = relativeTopCoefficient o.vertexOrder (n + 2) o.sign t (insert m ∅) := by
        simp only [hbase, hflag, m]
        norm_num
      _ = o.sign m * simplexBoundaryCoefficient o.vertexOrder m t := htop
  rw [orientedBoundary_eq_of_cofaces_eq_singleton
      (o.boundaryRelSubdivision K hK).vertexOrder R
      (o.boundaryRelSubdivision K hK).sign hgcofaces,
    orientedBoundary_eq_of_cofaces_eq_singleton o.vertexOrder K o.sign hqcofaces,
    ← hmq]
  exact hterm'

open Classical in
theorem isGlueIso_glued₁_id
    (K A : Geometry.SimplicialComplex ℝ E) :
    IsGlueIso K (glued₁ K A id) (glueEmbed₁ A id) (glueFst E E) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (mem_glued₁_faces_iff K A id).mpr ⟨s, hs, rfl⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := (mem_glued₁_faces_iff K A id).mp ht
    rw [Finset.image_image]
    have hcomp : (fun v : E => glueFst E E (glueEmbed₁ A id v)) = id := by
      funext v
      rfl
    rw [show (⇑(glueFst E E) ∘ glueEmbed₁ A id) = id from hcomp,
      Finset.image_id]
    exact hs
  · intro s hs v hv
    rfl
  · intro t ht z hz
    obtain ⟨s, hs, hst⟩ := (mem_glued₁_faces_iff K A id).mp ht
    obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp (hst ▸ hz)
    rw [← hvz]
    rfl

open Classical in
theorem isGlueIso_glued₂_id
    (K A : Geometry.SimplicialComplex ℝ E) :
    IsGlueIso K (glued₂ K A id) (glueEmbed₂ A id) (glueSnd E E) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (mem_glued₂_faces_iff K A id).mpr ⟨s, hs, rfl⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := (mem_glued₂_faces_iff K A id).mp ht
    rw [Finset.image_image]
    have hcomp : (fun v : E => glueSnd E E (glueEmbed₂ A id v)) = id := by
      funext v
      rfl
    rw [show (⇑(glueSnd E E) ∘ glueEmbed₂ A id) = id from hcomp,
      Finset.image_id]
    exact hs
  · intro s hs v hv
    rfl
  · intro t ht z hz
    obtain ⟨s, hs, hst⟩ := (mem_glued₂_faces_iff K A id).mp ht
    obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp (hst ▸ hz)
    rw [← hvz]
    rfl

open Classical in
theorem geometricLink_gluedComplex_space
    (K₁ K₂ A : Geometry.SimplicialComplex ℝ E)
    (hA₂ : A.faces ⊆ K₂.faces)
    (hfull : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A.faces) → s ∈ A.faces)
    (z : E × E × ℝ) :
    (SimplicialComplex.geometricLink
      (gluedComplex K₁ K₂ (isGlueIso_id A) hA₂ hfull) {z}).space =
      (SimplicialComplex.geometricLink (glued₁ K₁ A id) {z}).space ∪
        (SimplicialComplex.geometricLink (glued₂ K₂ A id) {z}).space := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := (SimplicialComplex.geometricLink
      (gluedComplex K₁ K₂ (isGlueIso_id A) hA₂ hfull) {z}).mem_space_iff.mp hx
    rw [SimplicialComplex.mem_geometricLink_singleton,
      mem_gluedComplex_faces_iff] at ht
    rcases ht.2.2 with ht₁ | ht₂
    · apply Or.inl
      apply (SimplicialComplex.geometricLink
        (glued₁ K₁ A id) {z}).mem_space_iff.mpr
      refine ⟨t, ?_, hxt⟩
      rw [SimplicialComplex.mem_geometricLink_singleton]
      exact ⟨ht.1, ht.2.1, ht₁⟩
    · apply Or.inr
      apply (SimplicialComplex.geometricLink
        (glued₂ K₂ A id) {z}).mem_space_iff.mpr
      refine ⟨t, ?_, hxt⟩
      rw [SimplicialComplex.mem_geometricLink_singleton]
      exact ⟨ht.1, ht.2.1, ht₂⟩
  · rintro (hx | hx)
    · obtain ⟨t, ht, hxt⟩ := (SimplicialComplex.geometricLink
        (glued₁ K₁ A id) {z}).mem_space_iff.mp hx
      apply (SimplicialComplex.geometricLink
        (gluedComplex K₁ K₂ (isGlueIso_id A) hA₂ hfull) {z}).mem_space_iff.mpr
      rw [SimplicialComplex.mem_geometricLink_singleton] at ht
      refine ⟨t, ?_, hxt⟩
      rw [SimplicialComplex.mem_geometricLink_singleton,
        mem_gluedComplex_faces_iff]
      exact ⟨ht.1, ht.2.1, Or.inl ht.2.2⟩
    · obtain ⟨t, ht, hxt⟩ := (SimplicialComplex.geometricLink
        (glued₂ K₂ A id) {z}).mem_space_iff.mp hx
      apply (SimplicialComplex.geometricLink
        (gluedComplex K₁ K₂ (isGlueIso_id A) hA₂ hfull) {z}).mem_space_iff.mpr
      rw [SimplicialComplex.mem_geometricLink_singleton] at ht
      refine ⟨t, ?_, hxt⟩
      rw [SimplicialComplex.mem_geometricLink_singleton,
        mem_gluedComplex_faces_iff]
      exact ⟨ht.1, ht.2.1, Or.inr ht.2.2⟩

open Classical in
theorem geometricLink_gluedComplex_eq_left_of_not_mem
    (K₁ K₂ A : Geometry.SimplicialComplex ℝ E)
    (hA₂ : A.faces ⊆ K₂.faces)
    (hfull : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A.faces) → s ∈ A.faces)
    {z : E × E × ℝ} (hz : {z} ∉ (glued₂ K₂ A id).faces) :
    SimplicialComplex.geometricLink
      (gluedComplex K₁ K₂ (isGlueIso_id A) hA₂ hfull) {z} =
      SimplicialComplex.geometricLink (glued₁ K₁ A id) {z} := by
  apply Geometry.SimplicialComplex.ext
  ext t
  simp only [SimplicialComplex.mem_geometricLink_singleton]
  constructor
  · rintro ⟨htne, hzt, ht⟩
    rcases ht with ht | ht
    · exact ⟨htne, hzt, ht⟩
    · exact False.elim (hz ((glued₂ K₂ A id).down_closed ht
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self z t))
        (Finset.singleton_nonempty z)))
  · rintro ⟨htne, hzt, ht⟩
    exact ⟨htne, hzt, Or.inl ht⟩

open Classical in
theorem geometricLink_gluedComplex_eq_right_of_not_mem
    (K₁ K₂ A : Geometry.SimplicialComplex ℝ E)
    (hA₂ : A.faces ⊆ K₂.faces)
    (hfull : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A.faces) → s ∈ A.faces)
    {z : E × E × ℝ} (hz : {z} ∉ (glued₁ K₁ A id).faces) :
    SimplicialComplex.geometricLink
      (gluedComplex K₁ K₂ (isGlueIso_id A) hA₂ hfull) {z} =
      SimplicialComplex.geometricLink (glued₂ K₂ A id) {z} := by
  apply Geometry.SimplicialComplex.ext
  ext t
  simp only [SimplicialComplex.mem_geometricLink_singleton]
  constructor
  · rintro ⟨htne, hzt, ht⟩
    rcases ht with ht | ht
    · exact False.elim (hz ((glued₁ K₁ A id).down_closed ht
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self z t))
        (Finset.singleton_nonempty z)))
    · exact ⟨htne, hzt, ht⟩
  · rintro ⟨htne, hzt, ht⟩
    exact ⟨htne, hzt, Or.inr ht⟩

open Classical in
theorem fullSubcomplex_space_inter_geometricLink
    (K A : Geometry.SimplicialComplex ℝ E)
    (hAK : A.faces ⊆ K.faces)
    (hfull : ∀ s ∈ K.faces, (∀ w ∈ s, {w} ∈ A.faces) → s ∈ A.faces)
    {v : E} (hvA : {v} ∈ A.faces) :
    A.space ∩ (SimplicialComplex.geometricLink K {v}).space =
      (SimplicialComplex.geometricLink A {v}).space := by
  ext x
  constructor
  · rintro ⟨hxA, hxL⟩
    obtain ⟨s, hsA, hxs⟩ := A.mem_space_iff.mp hxA
    obtain ⟨t, htL, hxt⟩ :=
      (SimplicialComplex.geometricLink K {v}).mem_space_iff.mp hxL
    have htK : t ∈ K.faces := SimplicialComplex.geometricLink_le K {v} htL
    have hxst : x ∈ convexHull ℝ (((s ∩ t : Finset E) : Set E)) := by
      rw [Finset.coe_inter]
      exact K.inter_subset_convexHull (hAK hsA) htK ⟨hxs, hxt⟩
    have hune : (s ∩ t).Nonempty := nonempty_of_mem_convexHull hxst
    have huA : s ∩ t ∈ A.faces :=
      A.down_closed hsA Finset.inter_subset_left hune
    have huL : s ∩ t ∈ (SimplicialComplex.geometricLink K {v}).faces :=
      (SimplicialComplex.geometricLink K {v}).down_closed htL
        Finset.inter_subset_right hune
    rw [SimplicialComplex.mem_geometricLink_singleton] at huL
    have hinsA : insert v (s ∩ t) ∈ A.faces := by
      apply hfull (insert v (s ∩ t)) huL.2.2
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hvA
      · exact A.down_closed hsA (Finset.singleton_subset_iff.mpr
          (Finset.mem_inter.mp hw).1) (Finset.singleton_nonempty w)
    apply (SimplicialComplex.geometricLink A {v}).mem_space_iff.mpr
    refine ⟨s ∩ t, ?_, hxst⟩
    rw [SimplicialComplex.mem_geometricLink_singleton]
    exact ⟨hune, huL.2.1, hinsA⟩
  · intro hx
    obtain ⟨t, ht, hxt⟩ :=
      (SimplicialComplex.geometricLink A {v}).mem_space_iff.mp hx
    rw [SimplicialComplex.mem_geometricLink_singleton] at ht
    refine ⟨A.convexHull_subset_space
      (SimplicialComplex.geometricLink_le A {v} (by
        rw [SimplicialComplex.mem_geometricLink_singleton]
        exact ht)) hxt, ?_⟩
    apply (SimplicialComplex.geometricLink K {v}).mem_space_iff.mpr
    refine ⟨t, ?_, hxt⟩
    rw [SimplicialComplex.mem_geometricLink_singleton]
    exact ⟨ht.1, ht.2.1, hAK ht.2.2⟩

open Classical in
theorem geometricLink_glued₁_space_inter_glued₂_space
    [FiniteDimensional ℝ E]
    (K₁ K₂ A : Geometry.SimplicialComplex ℝ E)
    [Finite K₁.faces] [Finite K₂.faces]
    (hA₁ : A.faces ⊆ K₁.faces) (hA₂ : A.faces ⊆ K₂.faces)
    (hfull : ∀ s ∈ K₁.faces, (∀ w ∈ s, {w} ∈ A.faces) → s ∈ A.faces)
    {v : E} (hvA : {v} ∈ A.faces) :
    (SimplicialComplex.geometricLink (glued₁ K₁ A id)
        {glueEmbed₁ A id v}).space ∩
      (SimplicialComplex.geometricLink (glued₂ K₂ A id)
        {glueEmbed₁ A id v}).space =
      simplicialMap (SimplicialComplex.geometricLink K₁ {v})
          (glueEmbed₁ A id) ''
        (SimplicialComplex.geometricLink A {v}).space := by
  classical
  let L₁ := SimplicialComplex.geometricLink K₁ {v}
  let L₂ := SimplicialComplex.geometricLink K₂ {v}
  let LA := SimplicialComplex.geometricLink A {v}
  let G₁ := glued₁ K₁ A id
  let G₂ := glued₂ K₂ A id
  let ι₁ := glueEmbed₁ A id
  let ι₂ := glueEmbed₂ A id
  have hvK₁ : {v} ∈ K₁.faces := hA₁ hvA
  have hvK₂ : {v} ∈ K₂.faces := hA₂ hvA
  have hz : ι₂ v = ι₁ v := by
    simp only [ι₁, ι₂, glueEmbed₁, glueEmbed₂, if_pos hvA, id_eq]
  have hLA₁ : LA.faces ⊆ L₁.faces := by
    intro s hs
    change s ∈ (SimplicialComplex.geometricLink A {v}).faces at hs
    change s ∈ (SimplicialComplex.geometricLink K₁ {v}).faces
    rw [SimplicialComplex.mem_geometricLink_singleton] at hs ⊢
    exact ⟨hs.1, hs.2.1, hA₁ hs.2.2⟩
  have hLA₂ : LA.faces ⊆ L₂.faces := by
    intro s hs
    change s ∈ (SimplicialComplex.geometricLink A {v}).faces at hs
    change s ∈ (SimplicialComplex.geometricLink K₂ {v}).faces
    rw [SimplicialComplex.mem_geometricLink_singleton] at hs ⊢
    exact ⟨hs.1, hs.2.1, hA₂ hs.2.2⟩
  let hAfinite : Finite A.faces := ((Set.toFinite K₁.faces).subset hA₁).to_subtype
  let hG₁finite : Finite G₁.faces := (glued₁_faces_finite K₁ A id).to_subtype
  let hG₂finite : Finite G₂.faces := (glued₂_faces_finite K₂ A id).to_subtype
  let hL₁finite : Finite L₁.faces :=
    ((Set.toFinite K₁.faces).subset (SimplicialComplex.geometricLink_le K₁ {v})).to_subtype
  let hL₂finite : Finite L₂.faces :=
    ((Set.toFinite K₂.faces).subset (SimplicialComplex.geometricLink_le K₂ {v})).to_subtype
  let hGL₁finite : Finite
      (SimplicialComplex.geometricLink G₁ {ι₁ v}).faces :=
    ((Set.toFinite G₁.faces).subset
      (SimplicialComplex.geometricLink_le G₁ {ι₁ v})).to_subtype
  let hGL₂finite : Finite
      (SimplicialComplex.geometricLink G₂ {ι₂ v}).faces :=
    ((Set.toFinite G₂.faces).subset
      (SimplicialComplex.geometricLink_le G₂ {ι₂ v})).to_subtype
  have hlink₁ := (isGlueIso_glued₁_id K₁ A).geometricLink hvK₁
  have hlink₂ := (isGlueIso_glued₂_id K₂ A).geometricLink hvK₂
  ext x
  constructor
  · rintro hx
    have hxG₁ : x ∈ G₁.space :=
      space_mono_of_faces_subset
        (SimplicialComplex.geometricLink_le G₁ {ι₁ v}) hx.1
    have hxG₂ : x ∈ G₂.space := by
      apply space_mono_of_faces_subset
        (SimplicialComplex.geometricLink_le G₂ {ι₂ v})
      simpa only [hz] using hx.2
    have hxinter : x ∈ G₁.space ∩ G₂.space := ⟨hxG₁, hxG₂⟩
    change x ∈ (glued₁ K₁ A id).space ∩ (glued₂ K₂ A id).space at hxinter
    rw [
      glued₁_space_inter_glued₂_space K₁ K₂ (isGlueIso_id A) hA₁ hA₂ hfull]
      at hxinter
    obtain ⟨y, hyA, hyx⟩ := hxinter
    have hyK₁ : y ∈ K₁.space := space_mono_of_faces_subset hA₁ hyA
    obtain ⟨y', hy'L₁, hy'x⟩ := hlink₁.isPLHomeomorphOn.bijOn.surjOn hx.1
    have hy'K₁ : y' ∈ K₁.space :=
      space_mono_of_faces_subset (SimplicialComplex.geometricLink_le K₁ {v}) hy'L₁
    have hyy' : y = y' := by
      apply (isPLHomeomorphOn_embedComplex K₁ ι₁ (glueFst E E)
        (fun _ _ _ _ => rfl)).bijOn.injOn hyK₁ hy'K₁
      rw [hyx, simplicialMap_eqOn_of_faces_subset K₁ L₁
        (SimplicialComplex.geometricLink_le K₁ {v}) ι₁ hy'L₁, hy'x]
    have hyL₁ : y ∈ L₁.space := hyy' ▸ hy'L₁
    have hyLA : y ∈ LA.space := by
      rw [← fullSubcomplex_space_inter_geometricLink K₁ A hA₁ hfull hvA]
      exact ⟨hyA, hyL₁⟩
    refine ⟨y, hyLA, ?_⟩
    rw [← hyx]
    exact (simplicialMap_eqOn_of_faces_subset K₁ L₁
      (SimplicialComplex.geometricLink_le K₁ {v}) ι₁ hyL₁).symm
  · rintro ⟨y, hyLA, rfl⟩
    have hyA : y ∈ A.space :=
      space_mono_of_faces_subset (SimplicialComplex.geometricLink_le A {v}) hyLA
    have hyL₁ : y ∈ L₁.space := space_mono_of_faces_subset hLA₁ hyLA
    have hyL₂ : y ∈ L₂.space := space_mono_of_faces_subset hLA₂ hyLA
    constructor
    · exact hlink₁.isPLHomeomorphOn.bijOn.mapsTo hyL₁
    · rw [← simplicialMap_eqOn_of_faces_subset K₁ L₁
          (SimplicialComplex.geometricLink_le K₁ {v}) ι₁ hyL₁,
        simplicialMap_glueEmbed_id_eq K₁ K₂ A hA₁ hA₂ hyA,
        simplicialMap_eqOn_of_faces_subset K₂ L₂
          (SimplicialComplex.geometricLink_le K₂ {v}) ι₂ hyL₂]
      change simplicialMap L₂ ι₂ y ∈
        (SimplicialComplex.geometricLink G₂ {ι₁ v}).space
      rw [← hz]
      exact hlink₂.isPLHomeomorphOn.bijOn.mapsTo hyL₂

open Classical in
theorem geometricLink_full_of_full
    (K A : Geometry.SimplicialComplex ℝ E)
    (hfull : ∀ s ∈ K.faces, (∀ w ∈ s, {w} ∈ A.faces) → s ∈ A.faces)
    {v : E} (hvA : {v} ∈ A.faces) :
    ∀ s ∈ (SimplicialComplex.geometricLink K {v}).faces,
      (∀ w ∈ s, {w} ∈ (SimplicialComplex.geometricLink A {v}).faces) →
        s ∈ (SimplicialComplex.geometricLink A {v}).faces := by
  classical
  intro s hs hvertices
  rw [SimplicialComplex.mem_geometricLink_singleton] at hs ⊢
  refine ⟨hs.1, hs.2.1, hfull (insert v s) hs.2.2 ?_⟩
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact hvA
  · exact SimplicialComplex.geometricLink_le A {v} (hvertices w hw)

open Classical in
theorem simplicialMap_geometricLink_glueEmbed_id_eq
    (K₁ K₂ A : Geometry.SimplicialComplex ℝ E)
    (hA₁ : A.faces ⊆ K₁.faces) (hA₂ : A.faces ⊆ K₂.faces)
    {v : E} {x : E} (hx : x ∈ (SimplicialComplex.geometricLink A {v}).space) :
    simplicialMap (SimplicialComplex.geometricLink K₁ {v}) (glueEmbed₁ A id) x =
      simplicialMap (SimplicialComplex.geometricLink K₂ {v}) (glueEmbed₂ A id) x := by
  classical
  have hxA : x ∈ A.space :=
    space_mono_of_faces_subset (SimplicialComplex.geometricLink_le A {v}) hx
  have hLA₁ : (SimplicialComplex.geometricLink A {v}).faces ⊆
      (SimplicialComplex.geometricLink K₁ {v}).faces := by
    intro s hs
    rw [SimplicialComplex.mem_geometricLink_singleton] at hs ⊢
    exact ⟨hs.1, hs.2.1, hA₁ hs.2.2⟩
  have hLA₂ : (SimplicialComplex.geometricLink A {v}).faces ⊆
      (SimplicialComplex.geometricLink K₂ {v}).faces := by
    intro s hs
    rw [SimplicialComplex.mem_geometricLink_singleton] at hs ⊢
    exact ⟨hs.1, hs.2.1, hA₂ hs.2.2⟩
  have hxL₁ : x ∈ (SimplicialComplex.geometricLink K₁ {v}).space :=
    space_mono_of_faces_subset hLA₁ hx
  have hxL₂ : x ∈ (SimplicialComplex.geometricLink K₂ {v}).space :=
    space_mono_of_faces_subset hLA₂ hx
  rw [← simplicialMap_eqOn_of_faces_subset K₁
      (SimplicialComplex.geometricLink K₁ {v})
      (SimplicialComplex.geometricLink_le K₁ {v}) (glueEmbed₁ A id) hxL₁,
    simplicialMap_glueEmbed_id_eq K₁ K₂ A hA₁ hA₂ hxA,
    simplicialMap_eqOn_of_faces_subset K₂
      (SimplicialComplex.geometricLink K₂ {v})
      (SimplicialComplex.geometricLink_le K₂ {v}) (glueEmbed₂ A id) hxL₂]

open Classical in
theorem isPLSphere_geometricLink_gluedComplex_of_isPLBall
    [FiniteDimensional ℝ E]
    (K₁ K₂ A : Geometry.SimplicialComplex ℝ E)
    [Finite K₁.faces] [Finite K₂.faces]
    (hA₁ : A.faces ⊆ K₁.faces) (hA₂ : A.faces ⊆ K₂.faces)
    (hfull : ∀ s ∈ K₁.faces, (∀ w ∈ s, {w} ∈ A.faces) → s ∈ A.faces)
    {v : E} (hvA : {v} ∈ A.faces) {n : ℕ}
    (hK₁ : IsPLBall (n + 1) (SimplicialComplex.geometricLink K₁ {v}).space)
    (hK₂ : IsPLBall (n + 1) (SimplicialComplex.geometricLink K₂ {v}).space)
    (hboundary₁ : SimplicialComplex.geometricLink A {v} =
      boundaryComplex (n + 1) (SimplicialComplex.geometricLink K₁ {v}))
    (hboundary₂ : SimplicialComplex.geometricLink A {v} =
      boundaryComplex (n + 1) (SimplicialComplex.geometricLink K₂ {v})) :
    IsPLSphere (n + 1)
      (SimplicialComplex.geometricLink
        (gluedComplex K₁ K₂ (isGlueIso_id A) hA₂ hfull)
        {glueEmbed₁ A id v}).space := by
  classical
  let L₁ := SimplicialComplex.geometricLink K₁ {v}
  let L₂ := SimplicialComplex.geometricLink K₂ {v}
  let LA := SimplicialComplex.geometricLink A {v}
  let G₁ := glued₁ K₁ A id
  let G₂ := glued₂ K₂ A id
  let z := glueEmbed₁ A id v
  let g₁ := simplicialMap L₁ (glueEmbed₁ A id)
  let g₂ := simplicialMap L₂ (glueEmbed₂ A id)
  let Y₁ := (SimplicialComplex.geometricLink G₁ {z}).space
  let Y₂ := (SimplicialComplex.geometricLink G₂ {z}).space
  have hvK₁ : {v} ∈ K₁.faces := hA₁ hvA
  have hvK₂ : {v} ∈ K₂.faces := hA₂ hvA
  have hz : glueEmbed₂ A id v = z := by
    simp only [z, glueEmbed₁, glueEmbed₂, if_pos hvA, id_eq]
  have hLA₁ : LA.faces ⊆ L₁.faces := by
    intro s hs
    change s ∈ (SimplicialComplex.geometricLink A {v}).faces at hs
    change s ∈ (SimplicialComplex.geometricLink K₁ {v}).faces
    rw [SimplicialComplex.mem_geometricLink_singleton] at hs ⊢
    exact ⟨hs.1, hs.2.1, hA₁ hs.2.2⟩
  have hLA₂ : LA.faces ⊆ L₂.faces := by
    intro s hs
    change s ∈ (SimplicialComplex.geometricLink A {v}).faces at hs
    change s ∈ (SimplicialComplex.geometricLink K₂ {v}).faces
    rw [SimplicialComplex.mem_geometricLink_singleton] at hs ⊢
    exact ⟨hs.1, hs.2.1, hA₂ hs.2.2⟩
  have hfullL₁ : ∀ s ∈ L₁.faces, (∀ w ∈ s, {w} ∈ LA.faces) → s ∈ LA.faces :=
    geometricLink_full_of_full K₁ A hfull hvA
  let hAfinite : Finite A.faces := ((Set.toFinite K₁.faces).subset hA₁).to_subtype
  let hL₁finite : Finite L₁.faces :=
    ((Set.toFinite K₁.faces).subset (SimplicialComplex.geometricLink_le K₁ {v})).to_subtype
  let hL₂finite : Finite L₂.faces :=
    ((Set.toFinite K₂.faces).subset (SimplicialComplex.geometricLink_le K₂ {v})).to_subtype
  let hLAfinite : Finite LA.faces :=
    ((Set.toFinite A.faces).subset (SimplicialComplex.geometricLink_le A {v})).to_subtype
  let hG₁finite : Finite G₁.faces := (glued₁_faces_finite K₁ A id).to_subtype
  let hG₂finite : Finite G₂.faces := (glued₂_faces_finite K₂ A id).to_subtype
  let hY₁finite : Finite (SimplicialComplex.geometricLink G₁ {z}).faces :=
    ((Set.toFinite G₁.faces).subset
      (SimplicialComplex.geometricLink_le G₁ {z})).to_subtype
  let hY₂finite : Finite
      (SimplicialComplex.geometricLink G₂ {glueEmbed₂ A id v}).faces :=
    ((Set.toFinite G₂.faces).subset
      (SimplicialComplex.geometricLink_le G₂ {glueEmbed₂ A id v})).to_subtype
  have hsphere : IsPLSphere (n + 1)
      (gluedComplex L₁ L₂ (isGlueIso_id LA) hLA₂ hfullL₁).space :=
    isPLSphere_gluedComplex_of_isPLBall L₁ L₂ LA hK₁ hK₂ hboundary₁ hboundary₂ hfullL₁
  have hlink₁ := (isGlueIso_glued₁_id K₁ A).geometricLink hvK₁
  have hlink₂ := (isGlueIso_glued₂_id K₂ A).geometricLink hvK₂
  have hg₁ : IsPLHomeomorphOn g₁ L₁.space Y₁ := hlink₁.isPLHomeomorphOn
  have hg₂ : IsPLHomeomorphOn g₂ L₂.space Y₂ := by
    simpa only [g₂, L₂, G₂, Y₂, hz] using hlink₂.isPLHomeomorphOn
  have hcompat : ∀ x ∈ LA.space, g₂ (simplicialMap LA id x) = g₁ x := by
    intro x hx
    rw [simplicialMap_id_eq_of_mem LA hx]
    exact (simplicialMap_geometricLink_glueEmbed_id_eq K₁ K₂ A hA₁ hA₂ hx).symm
  have hoverlap : Y₁ ∩ Y₂ = g₁ '' LA.space := by
    exact geometricLink_glued₁_space_inter_glued₂_space K₁ K₂ A hA₁ hA₂ hfull hvA
  have hmap := isPLHomeomorphOn_gluedMap_of_full L₁ L₂ LA LA id id
    (isGlueIso_id LA) hLA₁ hLA₂ hfullL₁ g₁ g₂ Y₁ Y₂ hg₁ hg₂ hcompat hoverlap
  have hmap' : IsPLHomeomorphOn (gluedMap L₁ LA id g₁ g₂)
      (gluedComplex L₁ L₂ (isGlueIso_id LA) hLA₂ hfullL₁).space
      (SimplicialComplex.geometricLink
        (gluedComplex K₁ K₂ (isGlueIso_id A) hA₂ hfull) {z}).space := by
    rw [geometricLink_gluedComplex_space K₁ K₂ A hA₂ hfull z]
    exact hmap
  exact hsphere.of_isPLHomeomorphOn hmap'

open Classical in
theorem exists_eq_glueEmbed₁_of_singleton_mem
    (K A : Geometry.SimplicialComplex ℝ E) {z : E × E × ℝ}
    (hz : {z} ∈ (glued₁ K A id).faces) :
    ∃ v, {v} ∈ K.faces ∧ z = glueEmbed₁ A id v := by
  classical
  obtain ⟨s, hs, hzs⟩ := (mem_glued₁_faces_iff K A id).mp hz
  have hzimage : z ∈ s.image (glueEmbed₁ A id) := by
    rw [← hzs]
    exact Finset.mem_singleton_self z
  obtain ⟨v, hvs, hvz⟩ := Finset.mem_image.mp hzimage
  exact ⟨v, K.down_closed hs (Finset.singleton_subset_iff.mpr hvs)
    (Finset.singleton_nonempty v), hvz.symm⟩

open Classical in
theorem exists_eq_glueEmbed₂_of_singleton_mem
    (K A : Geometry.SimplicialComplex ℝ E) {z : E × E × ℝ}
    (hz : {z} ∈ (glued₂ K A id).faces) :
    ∃ v, {v} ∈ K.faces ∧ z = glueEmbed₂ A id v := by
  classical
  obtain ⟨s, hs, hzs⟩ := (mem_glued₂_faces_iff K A id).mp hz
  have hzimage : z ∈ s.image (glueEmbed₂ A id) := by
    rw [← hzs]
    exact Finset.mem_singleton_self z
  obtain ⟨v, hvs, hvz⟩ := Finset.mem_image.mp hzimage
  exact ⟨v, K.down_closed hs (Finset.singleton_subset_iff.mpr hvs)
    (Finset.singleton_nonempty v), hvz.symm⟩

open Classical in
theorem glueEmbed₁_not_mem_glued₂_of_not_mem
    (K₂ A : Geometry.SimplicialComplex ℝ E) {v : E}
    (hvA : {v} ∉ A.faces) : {glueEmbed₁ A id v} ∉ (glued₂ K₂ A id).faces := by
  classical
  intro hv
  have hle := glueHeight_nonpos_of_mem_glued₂_face K₂ A id hv
    (glueEmbed₁ A id v) (Finset.mem_singleton_self _)
  have hge := glueHeight_glueEmbed₁_nonneg (F := E) A id v
  have hzero : glueHeight E E (glueEmbed₁ A id v) = 0 := le_antisymm hle hge
  exact hvA ((glueHeight_glueEmbed₁_eq_zero_iff (F := E) A id v).mp hzero)

open Classical in
theorem glueEmbed₂_not_mem_glued₁_of_not_mem
    (K₁ A : Geometry.SimplicialComplex ℝ E) {v : E}
    (hvA : {v} ∉ A.faces) : {glueEmbed₂ A id v} ∉ (glued₁ K₁ A id).faces := by
  classical
  intro hv
  have hge := glueHeight_nonneg_of_mem_glued₁_face K₁ A id hv
    (glueEmbed₂ A id v) (Finset.mem_singleton_self _)
  have hle := glueHeight_glueEmbed₂_nonpos (E := E) A id v
  have hzero : glueHeight E E (glueEmbed₂ A id v) = 0 := le_antisymm hle hge
  exact hvA ((glueHeight_glueEmbed₂_eq_zero_iff (E := E) A id v).mp hzero)

private theorem isGlueIso_redecide
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {K : Geometry.SimplicialComplex ℝ X} {L : Geometry.SimplicialComplex ℝ Y}
    {φ : X → Y} {ψ : Y → X} {dX : DecidableEq X} {dY : DecidableEq Y}
    (h : @IsGlueIso X Y _ _ _ _ K L φ ψ dX dY)
    (dX' : DecidableEq X) (dY' : DecidableEq Y) :
    @IsGlueIso X Y _ _ _ _ K L φ ψ dX' dY' := by
  have hX : dX = dX' := Subsingleton.elim _ _
  have hY : dY = dY' := Subsingleton.elim _ _
  subst dX'
  subst dY'
  exact h

open Classical in
noncomputable def CoherentOrientation.mapGlued₁
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    [Finite (DifferentialGeometry.Topology.PiecewiseLinear.glued₁ K A id).faces]
    {n : ℕ} (o : CoherentOrientation n K) :
    CoherentOrientation n
      (DifferentialGeometry.Topology.PiecewiseLinear.glued₁ K A id) := by
  let h := isGlueIso_redecide (isGlueIso_glued₁_id K A)
    (Classical.decEq E) (Classical.decEq (E × E × ℝ))
  exact o.map h

open Classical in
noncomputable def CoherentOrientation.mapGlued₂
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    [Finite (DifferentialGeometry.Topology.PiecewiseLinear.glued₂ K A id).faces]
    {n : ℕ} (o : CoherentOrientation n K) :
    CoherentOrientation n
      (DifferentialGeometry.Topology.PiecewiseLinear.glued₂ K A id) := by
  let h := isGlueIso_redecide (isGlueIso_glued₂_id K A)
    (Classical.decEq E) (Classical.decEq (E × E × ℝ))
  exact o.map h

open Classical in
theorem CoherentOrientation.mapGlued₁_vertexOrder_lt_iff
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    [Finite (DifferentialGeometry.Topology.PiecewiseLinear.glued₁ K A id).faces]
    {n : ℕ} (o : CoherentOrientation n K) {z w : E × E × ℝ}
    (hz : {z} ∈ (DifferentialGeometry.Topology.PiecewiseLinear.glued₁ K A id).faces)
    (hw : {w} ∈ (DifferentialGeometry.Topology.PiecewiseLinear.glued₁ K A id).faces) :
    @LT.lt (E × E × ℝ) (o.mapGlued₁ K A).vertexOrder.toLT z w ↔
      @LT.lt E o.vertexOrder.toLT (glueFst E E z) (glueFst E E w) := by
  let h := isGlueIso_redecide (isGlueIso_glued₁_id K A)
    (Classical.decEq E) (Classical.decEq (E × E × ℝ))
  change @LT.lt (E × E × ℝ)
      (o.mapVertexOrder h).toLT z w ↔ _
  exact o.mapVertexOrder_lt_iff h hz hw

open Classical in
theorem CoherentOrientation.mapGlued₂_vertexOrder_lt_iff
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    [Finite (DifferentialGeometry.Topology.PiecewiseLinear.glued₂ K A id).faces]
    {n : ℕ} (o : CoherentOrientation n K) {z w : E × E × ℝ}
    (hz : {z} ∈ (DifferentialGeometry.Topology.PiecewiseLinear.glued₂ K A id).faces)
    (hw : {w} ∈ (DifferentialGeometry.Topology.PiecewiseLinear.glued₂ K A id).faces) :
    @LT.lt (E × E × ℝ) (o.mapGlued₂ K A).vertexOrder.toLT z w ↔
      @LT.lt E o.vertexOrder.toLT (glueSnd E E z) (glueSnd E E w) := by
  let h := isGlueIso_redecide (isGlueIso_glued₂_id K A)
    (Classical.decEq E) (Classical.decEq (E × E × ℝ))
  change @LT.lt (E × E × ℝ)
      (o.mapVertexOrder h).toLT z w ↔ _
  exact o.mapVertexOrder_lt_iff h hz hw

open Classical in
theorem CoherentOrientation.orientedBoundary_mapGlued₁
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    [Finite (DifferentialGeometry.Topology.PiecewiseLinear.glued₁ K A id).faces]
    {n : ℕ} (o : CoherentOrientation n K) {t : Finset (E × E × ℝ)}
    (ht : t ∈ (DifferentialGeometry.Topology.PiecewiseLinear.glued₁ K A id).faces)
    (htcard : t.card = n) :
    orientedBoundary (o.mapGlued₁ K A).vertexOrder
        (DifferentialGeometry.Topology.PiecewiseLinear.glued₁ K A id) n
        (o.mapGlued₁ K A).sign t =
      orientedBoundary o.vertexOrder K n o.sign (t.image (glueFst E E)) := by
  let h := isGlueIso_redecide (isGlueIso_glued₁_id K A)
    (Classical.decEq E) (Classical.decEq (E × E × ℝ))
  change orientedBoundary (o.mapVertexOrder h)
      (DifferentialGeometry.Topology.PiecewiseLinear.glued₁ K A id) n
      (fun s => o.sign (s.image (glueFst E E))) t = _
  exact o.orientedBoundary_mapVertexOrder h ht htcard

open Classical in
theorem CoherentOrientation.orientedBoundary_mapGlued₂
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    [Finite (DifferentialGeometry.Topology.PiecewiseLinear.glued₂ K A id).faces]
    {n : ℕ} (o : CoherentOrientation n K) {t : Finset (E × E × ℝ)}
    (ht : t ∈ (DifferentialGeometry.Topology.PiecewiseLinear.glued₂ K A id).faces)
    (htcard : t.card = n) :
    orientedBoundary (o.mapGlued₂ K A).vertexOrder
        (DifferentialGeometry.Topology.PiecewiseLinear.glued₂ K A id) n
        (o.mapGlued₂ K A).sign t =
      orientedBoundary o.vertexOrder K n o.sign (t.image (glueSnd E E)) := by
  let h := isGlueIso_redecide (isGlueIso_glued₂_id K A)
    (Classical.decEq E) (Classical.decEq (E × E × ℝ))
  change orientedBoundary (o.mapVertexOrder h)
      (DifferentialGeometry.Topology.PiecewiseLinear.glued₂ K A id) n
      (fun s => o.sign (s.image (glueSnd E E))) t = _
  exact o.orientedBoundary_mapVertexOrder h ht htcard

open Classical in
private theorem exists_common_glued_face
    (K₁ K₂ A : Geometry.SimplicialComplex ℝ E)
    (hfull : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A.faces) → s ∈ A.faces)
    {t : Finset (E × E × ℝ)}
    (ht₁ : t ∈ (glued₁ K₁ A id).faces) (ht₂ : t ∈ (glued₂ K₂ A id).faces)
    (htne : t.Nonempty) :
    ∃ q ∈ A.faces,
      t = q.image (glueEmbed₁ A id) ∧ t = q.image (glueEmbed₂ A id) := by
  have hzero : ∀ z ∈ t, glueHeight E E z = 0 := by
    intro z hz
    exact le_antisymm
      (glueHeight_nonpos_of_mem_glued₂_face K₂ A id ht₂ z hz)
      (glueHeight_nonneg_of_mem_glued₁_face K₁ A id ht₁ z hz)
  have hfilter : t.filter (fun z => glueHeight E E z = 0) = t :=
    Finset.filter_eq_self.mpr hzero
  obtain ⟨q, hqA, hq⟩ := exists_face_filter_glued₁ K₁ hfull ht₁ (by
    rw [hfilter]
    exact htne)
  have htq₁ : t = q.image (glueEmbed₁ A id) := hfilter.symm.trans hq
  have htq₂ : t = q.image (glueEmbed₂ A id) := by
    rw [htq₁]
    simpa only [Finset.image_id] using
      image_glueEmbed₁_eq (isGlueIso_id A) hqA
  exact ⟨q, hqA, htq₁, htq₂⟩

private theorem faceCofaces_eq_empty_of_not_mem
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {t : Finset E} (ht : t ∉ K.faces) (htne : t.Nonempty) (n : ℕ) :
    faceCofaces K t n = ∅ := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨hsK, _, hts⟩ := (mem_faceCofaces K).mp hs
    exact False.elim (ht (K.down_closed hsK hts htne))
  · intro hs
    exact False.elim (Finset.notMem_empty s hs)

private theorem faceCofaces_eq_left_of_faces_eq_union_of_not_mem
    (D K L : Geometry.SimplicialComplex ℝ E)
    [Finite D.faces] [Finite K.faces] [Finite L.faces]
    (hfaces : D.faces = K.faces ∪ L.faces) {t : Finset E}
    (htL : t ∉ L.faces) (htne : t.Nonempty) (n : ℕ) :
    faceCofaces D t n = faceCofaces K t n := by
  classical
  ext s
  rw [mem_faceCofaces, mem_faceCofaces]
  constructor
  · rintro ⟨hsD, hscard, hts⟩
    rw [hfaces] at hsD
    rcases hsD with hsK | hsL
    · exact ⟨hsK, hscard, hts⟩
    · exact False.elim (htL (L.down_closed hsL hts htne))
  · rintro ⟨hsK, hscard, hts⟩
    refine ⟨?_, hscard, hts⟩
    rw [hfaces]
    exact Or.inl hsK

private theorem faceCofaces_eq_right_of_faces_eq_union_of_not_mem
    (D K L : Geometry.SimplicialComplex ℝ E)
    [Finite D.faces] [Finite K.faces] [Finite L.faces]
    (hfaces : D.faces = K.faces ∪ L.faces) {t : Finset E}
    (htK : t ∉ K.faces) (htne : t.Nonempty) (n : ℕ) :
    faceCofaces D t n = faceCofaces L t n := by
  classical
  ext s
  rw [mem_faceCofaces, mem_faceCofaces]
  constructor
  · rintro ⟨hsD, hscard, hts⟩
    rw [hfaces] at hsD
    rcases hsD with hsK | hsL
    · exact False.elim (htK (K.down_closed hsK hts htne))
    · exact ⟨hsL, hscard, hts⟩
  · rintro ⟨hsL, hscard, hts⟩
    refine ⟨?_, hscard, hts⟩
    rw [hfaces]
    exact Or.inr hsL

open Classical in
private noncomputable def orientationUnionSign
    (K : Geometry.SimplicialComplex ℝ E) (c₁ c₂ : Finset E → ℤ)
    (s : Finset E) : ℤ :=
  if s ∈ K.faces then c₁ s else -c₂ s

open Classical in
private theorem orientedBoundary_orientationUnionSign
    (D K L : Geometry.SimplicialComplex ℝ E)
    [Finite D.faces] [Finite K.faces] [Finite L.faces]
    (hfaces : D.faces = K.faces ∪ L.faces) (r : LinearOrder E)
    {n : ℕ} (c₁ c₂ : Finset E → ℤ)
    (htop : ∀ s ∈ K.faces, s ∈ L.faces → s.card = n + 1 → False)
    (t : Finset E) :
    orientedBoundary r D n (orientationUnionSign K c₁ c₂) t =
      orientedBoundary r K n c₁ t - orientedBoundary r L n c₂ t := by
  let _ : DecidableEq (Finset E) := Classical.decEq (Finset E)
  let F₁ := SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex (n + 1)
  let F₂ := SimplicialComplex.facesOfCard L.toPreAbstractSimplicialComplex (n + 1)
  let U := F₁ ∪ F₂
  have hfacesCard :
      SimplicialComplex.facesOfCard D.toPreAbstractSimplicialComplex (n + 1) = U := by
    ext s
    simp only [SimplicialComplex.mem_facesOfCard]
    change (s ∈ D.faces ∧ s.card = n + 1) ↔ s ∈ U
    rw [hfaces]
    simp only [U, Finset.mem_union, SimplicialComplex.mem_facesOfCard, F₁, F₂]
    change (s ∈ K.faces ∪ L.faces ∧ s.card = n + 1) ↔
      (s ∈ K.faces ∧ s.card = n + 1) ∨ (s ∈ L.faces ∧ s.card = n + 1)
    rw [Set.mem_union]
    tauto
  have hdisjoint : Disjoint F₁ F₂ := by
    apply Finset.disjoint_left.mpr
    intro s hs₁ hs₂
    obtain ⟨hsK, hscard⟩ :=
      (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs₁
    have hsL :=
      (SimplicialComplex.mem_facesOfCard L.toPreAbstractSimplicialComplex).mp hs₂
    exact htop s hsK hsL.1 hscard
  unfold orientedBoundary
  rw [hfacesCard]
  have hsum :
      (∑ s ∈ U, orientationUnionSign K c₁ c₂ s *
        simplexBoundaryCoefficient r s t) =
      (∑ s ∈ F₁, orientationUnionSign K c₁ c₂ s *
        simplexBoundaryCoefficient r s t) +
      ∑ s ∈ F₂, orientationUnionSign K c₁ c₂ s *
        simplexBoundaryCoefficient r s t :=
    show (∑ s ∈ F₁ ∪ F₂, orientationUnionSign K c₁ c₂ s *
      simplexBoundaryCoefficient r s t) = _ from Finset.sum_union hdisjoint
  rw [hsum]
  have hleft :
      (∑ s ∈ F₁, orientationUnionSign K c₁ c₂ s *
        simplexBoundaryCoefficient r s t) =
      ∑ s ∈ F₁, c₁ s * simplexBoundaryCoefficient r s t := by
    apply Finset.sum_congr rfl
    intro s hs
    have hsK :=
      (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs
    have hsK' : s ∈ K.faces := hsK.1
    rw [orientationUnionSign, if_pos hsK']
  have hright :
      (∑ s ∈ F₂, orientationUnionSign K c₁ c₂ s *
        simplexBoundaryCoefficient r s t) =
      -(∑ s ∈ F₂, c₂ s * simplexBoundaryCoefficient r s t) := by
    calc
      _ = ∑ s ∈ F₂, -(c₂ s * simplexBoundaryCoefficient r s t) := by
        apply Finset.sum_congr rfl
        intro s hs
        have hsL :=
          (SimplicialComplex.mem_facesOfCard L.toPreAbstractSimplicialComplex).mp hs
        have hsK : s ∉ K.faces := by
          intro hsK
          exact htop s hsK hsL.1 hsL.2
        rw [orientationUnionSign, if_neg hsK, neg_mul]
      _ = _ := by rw [Finset.sum_neg_distrib]
  rw [hleft, hright]
  rfl

open Classical in
private theorem orientedBoundary_eq_of_orders_agree_on_vertices
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (r₁ r₂ : LinearOrder E) {n : ℕ} (c : Finset E → ℤ)
    {t : Finset E} (htcard : t.card = n)
    (horder : ∀ v w, {v} ∈ K.faces → {w} ∈ K.faces →
      (@LT.lt E r₁.toLT v w ↔ @LT.lt E r₂.toLT v w)) :
    orientedBoundary r₁ K n c t = orientedBoundary r₂ K n c t := by
  rw [orientedBoundary_eq_sum_faceCofaces, orientedBoundary_eq_sum_faceCofaces]
  apply Finset.sum_congr rfl
  intro s hs
  obtain ⟨hsK, hscard, hts⟩ := (mem_faceCofaces K).mp hs
  congr 1
  apply simplexBoundaryCoefficient_eq_of_lt_iff r₁ r₂ hts (by omega)
  intro v hv w hw
  apply horder v w
  · exact K.down_closed hsK (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)
  · exact K.down_closed hsK (Finset.singleton_subset_iff.mpr hw)
      (Finset.singleton_nonempty w)

open Classical in
private theorem not_common_top_face_double_sides
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 2) K)
    {s : Finset (E × E × ℝ)}
    (hs₁ : s ∈ (glued₁
      (DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K)
      (boundaryComplex (n + 2) K) id).faces)
    (hs₂ : s ∈ (glued₂ K (boundaryComplex (n + 2) K) id).faces)
    (hscard : s.card = n + 3) : False := by
  let R := DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K
  let B := boundaryComplex (n + 2) K
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q, hqB, hsq, _⟩ := exists_common_glued_face R K B
    (boundaryComplex_full_boundaryRelSubdivision (n + 2) K) hs₁ hs₂ hsne
  have hqcard : q.card ≤ n + 2 :=
    ((hK.mem_boundaryComplex_faces_iff K).mp hqB).2.1
  rw [hsq, Finset.card_image_of_injective q (glueEmbed₁_injective B id)] at hscard
  omega

open Classical in
private theorem mapped_orientedBoundaries_eq_on_double_overlap
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 2) K)
    (o : CoherentOrientation (n + 2) K) {t : Finset (E × E × ℝ)}
    [Finite (glued₁
      (DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K)
      (boundaryComplex (n + 2) K) id).faces]
    [Finite (glued₂ K (boundaryComplex (n + 2) K) id).faces]
    (ht₁ : t ∈ (glued₁
      (DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K)
      (boundaryComplex (n + 2) K) id).faces)
    (ht₂ : t ∈ (glued₂ K (boundaryComplex (n + 2) K) id).faces)
    (htcard : t.card = n + 2) :
    orientedBoundary
        ((o.boundaryRelSubdivision K hK).mapGlued₁
          (DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K)
          (boundaryComplex (n + 2) K)).vertexOrder
        (glued₁
          (DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K)
          (boundaryComplex (n + 2) K) id)
        (n + 2)
        ((o.boundaryRelSubdivision K hK).mapGlued₁
          (DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K)
          (boundaryComplex (n + 2) K)).sign t =
      orientedBoundary (o.mapGlued₂ K (boundaryComplex (n + 2) K)).vertexOrder
        (glued₂ K (boundaryComplex (n + 2) K) id) (n + 2)
        (o.mapGlued₂ K (boundaryComplex (n + 2) K)).sign t := by
  let R := DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K
  let B := boundaryComplex (n + 2) K
  let oR := o.boundaryRelSubdivision K hK
  have htne : t.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q, hqB, htq₁, htq₂⟩ := exists_common_glued_face R K B
    (boundaryComplex_full_boundaryRelSubdivision (n + 2) K) ht₁ ht₂ htne
  have hqcard : q.card = n + 2 := by
    rw [htq₁, Finset.card_image_of_injective q (glueEmbed₁_injective B id)] at htcard
    exact htcard
  have hproj₁ : t.image (glueFst E E) = q := by
    rw [htq₁, Finset.image_image]
    have hcomp : (fun v : E => glueFst E E (glueEmbed₁ B id v)) = id := by
      funext v
      rfl
    rw [show (⇑(glueFst E E) ∘ glueEmbed₁ B id) = id from hcomp,
      Finset.image_id]
  have hproj₂ : t.image (glueSnd E E) = q := by
    rw [htq₂, Finset.image_image]
    have hcomp : (fun v : E => glueSnd E E (glueEmbed₂ B id v)) = id := by
      funext v
      rfl
    rw [show (⇑(glueSnd E E) ∘ glueEmbed₂ B id) = id from hcomp,
      Finset.image_id]
  rw [oR.orientedBoundary_mapGlued₁ R B ht₁ htcard,
    o.orientedBoundary_mapGlued₂ K B ht₂ htcard, hproj₁, hproj₂]
  exact o.orientedBoundary_boundaryRelSubdivision_eq K hK hqB hqcard

open Classical in
theorem CoherentOrientation.map_orders_agree_on_double_overlap
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 2) K)
    (o : CoherentOrientation (n + 2) K) {z w : E × E × ℝ}
    [Finite (glued₁
      (DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K)
      (boundaryComplex (n + 2) K) id).faces]
    [Finite (glued₂ K (boundaryComplex (n + 2) K) id).faces]
    (hz₁ : {z} ∈ (glued₁
      (DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K)
      (boundaryComplex (n + 2) K) id).faces)
    (hz₂ : {z} ∈ (glued₂ K (boundaryComplex (n + 2) K) id).faces)
    (hw₁ : {w} ∈ (glued₁
      (DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K)
      (boundaryComplex (n + 2) K) id).faces)
    (hw₂ : {w} ∈ (glued₂ K (boundaryComplex (n + 2) K) id).faces) :
    @LT.lt (E × E × ℝ)
        ((o.boundaryRelSubdivision K hK).mapGlued₁
            (DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K)
            (boundaryComplex (n + 2) K)).vertexOrder.toLT z w ↔
      @LT.lt (E × E × ℝ)
        (o.mapGlued₂ K (boundaryComplex (n + 2) K)).vertexOrder.toLT z w := by
  let B := boundaryComplex (n + 2) K
  let R := DifferentialGeometry.Topology.PiecewiseLinear.boundaryRelSubdivision (n + 2) K
  let oR := o.boundaryRelSubdivision K hK
  obtain ⟨v, hvR, hz⟩ := exists_eq_glueEmbed₁_of_singleton_mem R B hz₁
  obtain ⟨u, huR, hw⟩ := exists_eq_glueEmbed₁_of_singleton_mem R B hw₁
  subst z
  subst w
  have hvB : {v} ∈ B.faces := by
    by_contra hvB
    exact glueEmbed₁_not_mem_glued₂_of_not_mem K B hvB hz₂
  have huB : {u} ∈ B.faces := by
    by_contra huB
    exact glueEmbed₁_not_mem_glued₂_of_not_mem K B huB hw₂
  have hvEq : glueEmbed₁ B id v = glueEmbed₂ B id v := by
    simp only [glueEmbed₁, glueEmbed₂, if_pos hvB, id_eq]
  have huEq : glueEmbed₁ B id u = glueEmbed₂ B id u := by
    simp only [glueEmbed₁, glueEmbed₂, if_pos huB, id_eq]
  have hleft :
      @LT.lt (E × E × ℝ)
          (oR.mapGlued₁ R B).vertexOrder.toLT
          (glueEmbed₁ B id v) (glueEmbed₁ B id u) ↔
        @LT.lt E oR.vertexOrder.toLT v u := by
    simpa only [glueFst_glueEmbed₁] using
      oR.mapGlued₁_vertexOrder_lt_iff R B hz₁ hw₁
  have hrelative : @LT.lt E oR.vertexOrder.toLT v u ↔
      @LT.lt E o.vertexOrder.toLT v u := by
    change (let _ := o.relativeVertexOrder B; v < u) ↔
      @LT.lt E o.vertexOrder.toLT v u
    exact o.relativeVertexOrder_boundary_lt_iff
      (boundaryComplex_faces_subset (n + 2) K) hvB huB
  have hright :
      @LT.lt (E × E × ℝ)
          (o.mapGlued₂ K B).vertexOrder.toLT
          (glueEmbed₂ B id v) (glueEmbed₂ B id u) ↔
        @LT.lt E o.vertexOrder.toLT v u := by
    have h := o.mapGlued₂_vertexOrder_lt_iff K B
      (hvEq ▸ hz₂) (huEq ▸ hw₂)
    rw [glueSnd_glueEmbed₂ (E := E) B id v,
      glueSnd_glueEmbed₂ (E := E) B id u] at h
    exact h
  have hright' :
      @LT.lt (E × E × ℝ)
          (o.mapGlued₂ K B).vertexOrder.toLT
          (glueEmbed₁ B id v) (glueEmbed₁ B id u) ↔
        @LT.lt E o.vertexOrder.toLT v u := by
    rw [hvEq, huEq]
    exact hright
  change @LT.lt (E × E × ℝ)
      (oR.mapGlued₁ R B).vertexOrder.toLT
      (glueEmbed₁ B id v) (glueEmbed₁ B id u) ↔
    @LT.lt (E × E × ℝ)
      (o.mapGlued₂ K B).vertexOrder.toLT
      (glueEmbed₁ B id v) (glueEmbed₁ B id u)
  exact hleft.trans (hrelative.trans hright'.symm)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLSphere_geometricLink_of_not_mem_boundary
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {v : E} (hvK : {v} ∈ K.faces) (hvB : {v} ∉ (boundaryComplex (n + 1) K).faces) :
    IsPLSphere n (SimplicialComplex.geometricLink K {v}).space := by
  classical
  rcases hK v hvK with hsphere | hball
  · exact hsphere
  · exfalso
    apply hvB
    apply (hK.mem_boundaryComplex_faces_iff K).mpr
    refine ⟨hvK, by simp, ?_⟩
    simpa using hball

open Classical in
theorem isCombinatorialManifold_double_succ_succ
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) :
    IsCombinatorialManifold (n + 2) (double (n + 2) K) := by
  classical
  let _ : DecidableEq E := Classical.decEq E
  let _ : DecidableEq ℝ := Classical.decEq ℝ
  let _ : DecidableEq (E × E × ℝ) := inferInstance
  have hdec : Classical.decEq (E × E × ℝ) =
      (inferInstance : DecidableEq (E × E × ℝ)) := Subsingleton.elim _ _
  let R := boundaryRelSubdivision (n + 2) K
  let B := boundaryComplex (n + 2) K
  let G₁ := glued₁ R B id
  let G₂ := glued₂ K B id
  let D := gluedComplex R K (isGlueIso_id B)
    (boundaryComplex_faces_subset (n + 2) K)
    (boundaryComplex_full_boundaryRelSubdivision (n + 2) K)
  let hRfinite : Finite R.faces :=
    (boundaryRelSubdivision_faces_finite (n + 2) K).to_subtype
  let hBfinite : Finite B.faces := (boundaryComplex_faces_finite (n + 2) K).to_subtype
  let hG₁finite : Finite G₁.faces := (glued₁_faces_finite R B id).to_subtype
  let hG₂finite : Finite G₂.faces := (glued₂_faces_finite K B id).to_subtype
  have hRsub : IsSubdivision R K := boundaryRelSubdivision_isSubdivision (n + 2) K
  have hR : IsCombinatorialManifoldWithBoundary (n + 2) R := hK.of_isSubdivision hRsub
  have hBR : boundaryComplex (n + 2) R = B :=
    boundaryComplex_boundaryRelSubdivision K hK
  have hBRfaces : B.faces ⊆ R.faces :=
    boundaryComplex_faces_subset_boundaryRelSubdivision (n + 2) K
  have hBKfaces : B.faces ⊆ K.faces := boundaryComplex_faces_subset (n + 2) K
  have hfull : ∀ s ∈ R.faces, (∀ w ∈ s, {w} ∈ B.faces) → s ∈ B.faces :=
    boundaryComplex_full_boundaryRelSubdivision (n + 2) K
  change IsCombinatorialManifold (Nat.succ (n + 1)) D
  simp only [IsCombinatorialManifold]
  change ∀ z, {z} ∈ D.faces → IsPLSphere (n + 1)
    ((@SimplicialComplex.geometricLink ℝ (E × E × ℝ) _ _ _ _
      (Classical.decEq (E × E × ℝ)) D {z}).space)
  rw [hdec]
  intro z hzD
  change {z} ∈ (gluedComplex R K (isGlueIso_id B) hBKfaces hfull).faces at hzD
  rw [mem_gluedComplex_faces_iff] at hzD
  rcases hzD with hz₁ | hz₂
  · obtain ⟨v, hvR, rfl⟩ := exists_eq_glueEmbed₁_of_singleton_mem R B hz₁
    by_cases hvB : {v} ∈ B.faces
    · have hvBR : {v} ∈ (boundaryComplex (n + 2) R).faces := by
        rw [hBR]
        exact hvB
      have hballR : IsPLBall (n + 1)
          (SimplicialComplex.geometricLink R {v}).space := by
        have hball := ((hR.mem_boundaryComplex_faces_iff R).mp hvBR).2.2
        simpa using hball
      have hballK : IsPLBall (n + 1)
          (SimplicialComplex.geometricLink K {v}).space := by
        have hball := ((hK.mem_boundaryComplex_faces_iff K).mp hvB).2.2
        simpa using hball
      have hboundaryR : SimplicialComplex.geometricLink B {v} =
          boundaryComplex (n + 1) (SimplicialComplex.geometricLink R {v}) := by
        rw [← hBR]
        simpa only [Nat.add_assoc, Nat.reduceAdd] using
          geometricLink_boundaryComplex (n + 1) R v
      have hboundaryK : SimplicialComplex.geometricLink B {v} =
          boundaryComplex (n + 1) (SimplicialComplex.geometricLink K {v}) := by
        simpa only [B, Nat.add_assoc, Nat.reduceAdd] using
          geometricLink_boundaryComplex (n + 1) K v
      have hsphere := isPLSphere_geometricLink_gluedComplex_of_isPLBall R K B
        hBRfaces hBKfaces hfull hvB hballR hballK hboundaryR hboundaryK
      simpa only [D] using hsphere
    · have hvnotBR : {v} ∉ (boundaryComplex (n + 2) R).faces := by
        rwa [hBR]
      have hsphereR := hR.isPLSphere_geometricLink_of_not_mem_boundary R hvR hvnotBR
      let hLRfinite : Finite (SimplicialComplex.geometricLink R {v}).faces :=
        ((Set.toFinite R.faces).subset
          (SimplicialComplex.geometricLink_le R {v})).to_subtype
      let hLG₁finite : Finite
          (SimplicialComplex.geometricLink G₁ {glueEmbed₁ B id v}).faces :=
        ((Set.toFinite G₁.faces).subset
          (SimplicialComplex.geometricLink_le G₁ {glueEmbed₁ B id v})).to_subtype
      have hsphereG₁ : IsPLSphere (n + 1)
          (SimplicialComplex.geometricLink G₁ {glueEmbed₁ B id v}).space :=
        hsphereR.of_isPLHomeomorphOn
          ((isGlueIso_glued₁_id R B).geometricLink hvR).isPLHomeomorphOn
      have hvnotG₂ : {glueEmbed₁ B id v} ∉ G₂.faces :=
        glueEmbed₁_not_mem_glued₂_of_not_mem K B hvB
      have hlinkeq : SimplicialComplex.geometricLink D {glueEmbed₁ B id v} =
          SimplicialComplex.geometricLink G₁ {glueEmbed₁ B id v} := by
        simpa only [D, G₁] using
          geometricLink_gluedComplex_eq_left_of_not_mem R K B hBKfaces hfull hvnotG₂
      rw [hlinkeq]
      exact hsphereG₁
  · obtain ⟨v, hvK, rfl⟩ := exists_eq_glueEmbed₂_of_singleton_mem K B hz₂
    by_cases hvB : {v} ∈ B.faces
    · have hvBR : {v} ∈ (boundaryComplex (n + 2) R).faces := by
        rw [hBR]
        exact hvB
      have hballR : IsPLBall (n + 1)
          (SimplicialComplex.geometricLink R {v}).space := by
        have hball := ((hR.mem_boundaryComplex_faces_iff R).mp hvBR).2.2
        simpa using hball
      have hballK : IsPLBall (n + 1)
          (SimplicialComplex.geometricLink K {v}).space := by
        have hball := ((hK.mem_boundaryComplex_faces_iff K).mp hvB).2.2
        simpa using hball
      have hboundaryR : SimplicialComplex.geometricLink B {v} =
          boundaryComplex (n + 1) (SimplicialComplex.geometricLink R {v}) := by
        rw [← hBR]
        simpa only [Nat.add_assoc, Nat.reduceAdd] using
          geometricLink_boundaryComplex (n + 1) R v
      have hboundaryK : SimplicialComplex.geometricLink B {v} =
          boundaryComplex (n + 1) (SimplicialComplex.geometricLink K {v}) := by
        simpa only [B, Nat.add_assoc, Nat.reduceAdd] using
          geometricLink_boundaryComplex (n + 1) K v
      have hsphere := isPLSphere_geometricLink_gluedComplex_of_isPLBall R K B
        hBRfaces hBKfaces hfull hvB hballR hballK hboundaryR hboundaryK
      have hz : glueEmbed₂ B id v = glueEmbed₁ B id v := by
        simp only [glueEmbed₁, glueEmbed₂, if_pos hvB, id_eq]
      simpa only [D, hz] using hsphere
    · have hsphereK := hK.isPLSphere_geometricLink_of_not_mem_boundary K hvK hvB
      let hLKfinite : Finite (SimplicialComplex.geometricLink K {v}).faces :=
        ((Set.toFinite K.faces).subset
          (SimplicialComplex.geometricLink_le K {v})).to_subtype
      let hLG₂finite : Finite
          (SimplicialComplex.geometricLink G₂ {glueEmbed₂ B id v}).faces :=
        ((Set.toFinite G₂.faces).subset
          (SimplicialComplex.geometricLink_le G₂ {glueEmbed₂ B id v})).to_subtype
      have hsphereG₂ : IsPLSphere (n + 1)
          (SimplicialComplex.geometricLink G₂ {glueEmbed₂ B id v}).space :=
        hsphereK.of_isPLHomeomorphOn
          ((isGlueIso_glued₂_id K B).geometricLink hvK).isPLHomeomorphOn
      have hvnotG₁ : {glueEmbed₂ B id v} ∉ G₁.faces :=
        glueEmbed₂_not_mem_glued₁_of_not_mem R B hvB
      have hlinkeq : SimplicialComplex.geometricLink D {glueEmbed₂ B id v} =
          SimplicialComplex.geometricLink G₂ {glueEmbed₂ B id v} := by
        simpa only [D, G₂] using
          geometricLink_gluedComplex_eq_right_of_not_mem R K B hBKfaces hfull hvnotG₁
      rw [hlinkeq]
      exact hsphereG₂

open Classical in
theorem IsOrientable.double
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 2) K)
    (h : IsOrientable (n + 2) K) : IsOrientable (n + 2) (double (n + 2) K) := by
  classical
  obtain ⟨o⟩ := h
  let R := boundaryRelSubdivision (n + 2) K
  let B := boundaryComplex (n + 2) K
  let G₁ := glued₁ R B id
  let G₂ := glued₂ K B id
  let D := DifferentialGeometry.Topology.PiecewiseLinear.double (n + 2) K
  let hRfinite : Finite R.faces := (boundaryRelSubdivision_faces_finite (n + 2) K).to_subtype
  let hG₁finite : Finite G₁.faces := (glued₁_faces_finite R B id).to_subtype
  let hG₂finite : Finite G₂.faces := (glued₂_faces_finite K B id).to_subtype
  let hDfinite : Finite D.faces := inferInstance
  let oR := o.boundaryRelSubdivision K hK
  let oG₁ := oR.mapGlued₁ R B
  let oG₂ := o.mapGlued₂ K B
  let V₁ := complexVertexFinset G₁
  let V₂ := complexVertexFinset G₂
  let A := @Inter.inter (Finset (E × E × ℝ))
    (@Finset.instInter (E × E × ℝ)
      (fun z w => oG₂.vertexOrder.toDecidableEq z w)) V₁ V₂
  have hagree : ∀ z ∈ A, ∀ w ∈ A,
      (@LT.lt (E × E × ℝ) oG₁.vertexOrder.toLT z w ↔
        @LT.lt (E × E × ℝ) oG₂.vertexOrder.toLT z w) := by
    intro z hz w hw
    have hzV : z ∈ V₁ ∧ z ∈ V₂ := by
      change z ∈ @Inter.inter (Finset (E × E × ℝ))
        (@Finset.instInter (E × E × ℝ)
          (fun a b => oG₂.vertexOrder.toDecidableEq a b)) V₁ V₂ at hz
      exact (@Finset.mem_inter (E × E × ℝ)
        (fun a b => oG₂.vertexOrder.toDecidableEq a b)
        z V₁ V₂).mp hz
    have hwV : w ∈ V₁ ∧ w ∈ V₂ := by
      change w ∈ @Inter.inter (Finset (E × E × ℝ))
        (@Finset.instInter (E × E × ℝ)
          (fun a b => oG₂.vertexOrder.toDecidableEq a b)) V₁ V₂ at hw
      exact (@Finset.mem_inter (E × E × ℝ)
        (fun a b => oG₂.vertexOrder.toDecidableEq a b)
        w V₁ V₂).mp hw
    have hz₁ : {z} ∈ G₁.faces := (mem_complexVertexFinset G₁ z).mp hzV.1
    have hz₂ : {z} ∈ G₂.faces := (mem_complexVertexFinset G₂ z).mp hzV.2
    have hw₁ : {w} ∈ G₁.faces := (mem_complexVertexFinset G₁ w).mp hwV.1
    have hw₂ : {w} ∈ G₂.faces := (mem_complexVertexFinset G₂ w).mp hwV.2
    exact o.map_orders_agree_on_double_overlap K hK hz₁ hz₂ hw₁ hw₂
  let r := orderAmalgam oG₁.vertexOrder oG₂.vertexOrder V₁ V₂ A
  have horder₁ : ∀ z w, {z} ∈ G₁.faces → {w} ∈ G₁.faces →
      (@LT.lt (E × E × ℝ) r.toLT z w ↔
        @LT.lt (E × E × ℝ) oG₁.vertexOrder.toLT z w) := by
    intro z w hz hw
    have hzV : z ∈ V₁ := (mem_complexVertexFinset G₁ z).mpr hz
    have hwV : w ∈ V₁ := (mem_complexVertexFinset G₁ w).mpr hw
    change @LT.lt (E × E × ℝ)
        (orderAmalgam oG₁.vertexOrder oG₂.vertexOrder V₁ V₂ A).toLT z w ↔ _
    exact orderAmalgam_lt_iff_left (V₁ := V₁) (V₂ := V₂) (A := A)
      oG₁.vertexOrder oG₂.vertexOrder hzV hwV
  have horder₂ : ∀ z w, {z} ∈ G₂.faces → {w} ∈ G₂.faces →
      (@LT.lt (E × E × ℝ) r.toLT z w ↔
        @LT.lt (E × E × ℝ) oG₂.vertexOrder.toLT z w) := by
    intro z w hz hw
    have hzV : z ∈ V₂ := (mem_complexVertexFinset G₂ z).mpr hz
    have hwV : w ∈ V₂ := (mem_complexVertexFinset G₂ w).mpr hw
    change @LT.lt (E × E × ℝ)
        (orderAmalgam oG₁.vertexOrder oG₂.vertexOrder V₁ V₂ A).toLT z w ↔ _
    exact orderAmalgam_lt_iff_right (V₁ := V₁) (V₂ := V₂) (A := A)
      oG₁.vertexOrder oG₂.vertexOrder (by
        intro x hx
        change x ∈ @Inter.inter (Finset (E × E × ℝ))
          (@Finset.instInter (E × E × ℝ)
            (fun a b => oG₂.vertexOrder.toDecidableEq a b)) V₁ V₂
        exact hx) hagree hzV hwV
  let o₁ := oG₁.withVertexOrder r horder₁
  let o₂ := oG₂.withVertexOrder r horder₂
  have hDfaces : D.faces = G₁.faces ∪ G₂.faces := rfl
  have htop : ∀ s ∈ G₁.faces, s ∈ G₂.faces → s.card = (n + 2) + 1 → False := by
    intro s hs₁ hs₂ hscard
    exact not_common_top_face_double_sides K hK hs₁ hs₂ (by omega)
  have hD : IsCombinatorialManifold (n + 2) D := by
    simpa only [D] using isCombinatorialManifold_double_succ_succ K hK
  change Nonempty (CoherentOrientation (n + 2) D)
  refine ⟨{
    vertexOrder := r
    sign := orientationUnionSign G₁ o₁.sign o₂.sign
    sign_top := ?_
    coherent := ?_ }⟩
  · intro s hsD hscard
    have hsSides : s ∈ G₁.faces ∨ s ∈ G₂.faces := by
      rw [hDfaces] at hsD
      exact hsD
    by_cases hs₁ : s ∈ G₁.faces
    · rw [orientationUnionSign, if_pos hs₁]
      exact o₁.sign_top s hs₁ hscard
    · have hs₂ : s ∈ G₂.faces := hsSides.resolve_left hs₁
      rw [orientationUnionSign, if_neg hs₁]
      rcases o₂.sign_top s hs₂ hscard with hsone | hsneg
      · right
        rw [hsone]
      · left
        rw [hsneg]
        norm_num
  · intro t htD htcard _
    have htne : t.Nonempty := Finset.card_pos.mp (by omega)
    have htSides : t ∈ G₁.faces ∨ t ∈ G₂.faces := by
      rw [hDfaces] at htD
      exact htD
    have hDtwo : (faceCofaces D t (n + 3)).card = 2 := by
      have htwo := hD.card_faceCofaces_eq_two D htD htcard
      simpa only [Nat.add_assoc, Nat.reduceAdd] using htwo
    rw [orientedBoundary_orientationUnionSign D G₁ G₂ hDfaces r o₁.sign o₂.sign
      htop t]
    by_cases ht₁ : t ∈ G₁.faces
    · by_cases ht₂ : t ∈ G₂.faces
      · have hleft : orientedBoundary r G₁ (n + 2) o₁.sign t =
            orientedBoundary oG₁.vertexOrder G₁ (n + 2) oG₁.sign t := by
          change orientedBoundary r G₁ (n + 2) oG₁.sign t = _
          exact orientedBoundary_eq_of_orders_agree_on_vertices G₁ r oG₁.vertexOrder
            oG₁.sign htcard horder₁
        have hright : orientedBoundary r G₂ (n + 2) o₂.sign t =
            orientedBoundary oG₂.vertexOrder G₂ (n + 2) oG₂.sign t := by
          change orientedBoundary r G₂ (n + 2) oG₂.sign t = _
          exact orientedBoundary_eq_of_orders_agree_on_vertices G₂ r oG₂.vertexOrder
            oG₂.sign htcard horder₂
        have hseam := mapped_orientedBoundaries_eq_on_double_overlap K hK o
          ht₁ ht₂ htcard
        rw [hleft, hright, hseam, sub_self]
      · have hco : faceCofaces D t (n + 3) = faceCofaces G₁ t (n + 3) :=
          faceCofaces_eq_left_of_faces_eq_union_of_not_mem D G₁ G₂ hDfaces
            ht₂ htne (n + 3)
        have hG₁two : (faceCofaces G₁ t (n + 3)).card = 2 := by
          rw [← hco]
          exact hDtwo
        have hG₁notone :
            (faceCofaces G₁ t ((n + 2) + 1)).card ≠ 1 := by
          have htwo : (faceCofaces G₁ t ((n + 2) + 1)).card = 2 := by
            simpa only [Nat.add_assoc, Nat.reduceAdd] using hG₁two
          omega
        have hco₂ : faceCofaces G₂ t ((n + 2) + 1) = ∅ :=
          faceCofaces_eq_empty_of_not_mem G₂ ht₂ htne ((n + 2) + 1)
        have hleft : orientedBoundary r G₁ (n + 2) o₁.sign t = 0 :=
          o₁.coherent t ht₁ htcard hG₁notone
        have hright : orientedBoundary r G₂ (n + 2) o₂.sign t = 0 := by
          rw [orientedBoundary_eq_sum_faceCofaces, hco₂]
          simp
        rw [hleft, hright, sub_zero]
    · have ht₂ : t ∈ G₂.faces := htSides.resolve_left ht₁
      have hco : faceCofaces D t (n + 3) = faceCofaces G₂ t (n + 3) :=
        faceCofaces_eq_right_of_faces_eq_union_of_not_mem D G₁ G₂ hDfaces
          ht₁ htne (n + 3)
      have hG₂two : (faceCofaces G₂ t (n + 3)).card = 2 := by
        rw [← hco]
        exact hDtwo
      have hG₂notone :
          (faceCofaces G₂ t ((n + 2) + 1)).card ≠ 1 := by
        have htwo : (faceCofaces G₂ t ((n + 2) + 1)).card = 2 := by
          simpa only [Nat.add_assoc, Nat.reduceAdd] using hG₂two
        omega
      have hco₁ : faceCofaces G₁ t ((n + 2) + 1) = ∅ :=
        faceCofaces_eq_empty_of_not_mem G₁ ht₁ htne ((n + 2) + 1)
      have hleft : orientedBoundary r G₁ (n + 2) o₁.sign t = 0 := by
        rw [orientedBoundary_eq_sum_faceCofaces, hco₁]
        simp
      have hright : orientedBoundary r G₂ (n + 2) o₂.sign t = 0 :=
        o₂.coherent t ht₂ htcard hG₂notone
      rw [hleft, hright, sub_self]

open Classical in
theorem relDerived_bot_eq_barycentricSubdivision
    (K : Geometry.SimplicialComplex ℝ E) :
    relDerived (show (⊥ : Geometry.SimplicialComplex ℝ E).faces ⊆ K.faces by
          rw [Geometry.SimplicialComplex.faces_bot]
          exact Set.empty_subset K.faces)
        (IsSubdivision.refl (⊥ : Geometry.SimplicialComplex ℝ E))
        (centroid_mem_openSimplex_of_mem_faces K) =
      barycentricSubdivision K := by
  apply Geometry.SimplicialComplex.ext
  ext f
  constructor
  · rintro ⟨τ, d, h, rfl⟩
    have hτ : τ = ∅ := by
      rcases h.base with hτ | hτ
      · exact hτ
      · rw [Geometry.SimplicialComplex.faces_bot] at hτ
        exact False.elim (Set.notMem_empty τ hτ)
    have hd : d.Nonempty := by
      rcases h.nonempty with hτne | hd
      · exact False.elim (hτne.ne_empty hτ)
      · exact hd
    rw [hτ, Finset.empty_union]
    exact ⟨d, h.flag, hd, rfl⟩
  · rintro ⟨d, hd, hdne, rfl⟩
    refine ⟨∅, d, ?_, by simp⟩
    exact {
      base := Or.inl rfl
      flag := hd
      notMem := by
        intro s hs
        rw [Geometry.SimplicialComplex.faces_bot]
        exact Set.notMem_empty s
      subset := by simp
      nonempty := Or.inr hdne }

open Classical in
noncomputable def CoherentOrientation.barycentricSubdivision
    [FiniteDimensional ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation (n + 1) K)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) :
    CoherentOrientation (n + 1) (PiecewiseLinear.barycentricSubdivision K) := by
  let L : Geometry.SimplicialComplex ℝ E := ⊥
  let hLK : L.faces ⊆ K.faces := by
    intro s hs
    change s ∈ (⊥ : Geometry.SimplicialComplex ℝ E).faces at hs
    rw [Geometry.SimplicialComplex.faces_bot] at hs
    exact False.elim (Set.notMem_empty s hs)
  let hLcard : ∀ s ∈ L.faces, s.card ≤ n + 1 := by
    intro s hs
    change s ∈ (⊥ : Geometry.SimplicialComplex ℝ E).faces at hs
    rw [Geometry.SimplicialComplex.faces_bot] at hs
    exact False.elim (Set.notMem_empty s hs)
  let hLfinite : Finite L.faces := by
    change Finite (↥(⊥ : Geometry.SimplicialComplex ℝ E).faces)
    rw [Geometry.SimplicialComplex.faces_bot]
    exact Set.finite_empty.to_subtype
  let _ : Finite L.faces := hLfinite
  let R := relDerived hLK (IsSubdivision.refl L)
    (centroid_mem_openSimplex_of_mem_faces K)
  let oR := o.relativeSubdivision hK hLK hLcard
  have hR : R = PiecewiseLinear.barycentricSubdivision K := by
    change relDerived hLK (IsSubdivision.refl L)
        (centroid_mem_openSimplex_of_mem_faces K) =
          PiecewiseLinear.barycentricSubdivision K
    have hLK' : hLK = (show (⊥ : Geometry.SimplicialComplex ℝ E).faces ⊆ K.faces by
        rw [Geometry.SimplicialComplex.faces_bot]
        exact Set.empty_subset K.faces) := Subsingleton.elim _ _
    rw [hLK']
    exact relDerived_bot_eq_barycentricSubdivision K
  have hR' : relDerived hLK (IsSubdivision.refl L)
      (centroid_mem_openSimplex_of_mem_faces K) =
        PiecewiseLinear.barycentricSubdivision K := hR
  refine {
    vertexOrder := oR.vertexOrder
    sign := oR.sign
    sign_top := ?_
    coherent := ?_ }
  · intro s hs hscard
    apply oR.sign_top s
    · rw [hR']
      exact hs
    · exact hscard
  · intro t ht htcard hne
    have htR : t ∈ R.faces := by
      rw [hR]
      exact ht
    have hneR :
        (faceCofaces (relDerived hLK (IsSubdivision.refl L)
          (centroid_mem_openSimplex_of_mem_faces K)) t ((n + 1) + 1)).card ≠ 1 := by
      simpa only [hR'] using hne
    have hzero := oR.coherent t htR htcard hneR
    simpa only [hR'] using hzero

open Classical in
theorem IsOrientable.barycentricSubdivision
    [FiniteDimensional ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (h : IsOrientable (n + 1) K)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) :
    IsOrientable (n + 1) (PiecewiseLinear.barycentricSubdivision K) := by
  obtain ⟨o⟩ := h
  exact ⟨o.barycentricSubdivision hK⟩

abbrev SimplicialVertex
    (K : Geometry.SimplicialComplex ℝ E) :=
  {v : E // {v} ∈ K.faces}

open Classical in
def simplicialVertexAdjacent
    (K : Geometry.SimplicialComplex ℝ E)
    (v w : SimplicialVertex K) : Prop :=
  ({v.1, w.1} : Finset E) ∈ K.faces

abbrev SimplicialComponent
    (K : Geometry.SimplicialComplex ℝ E) :=
  Quot (simplicialVertexAdjacent K)

def simplicialComponentOfVertex
    (K : Geometry.SimplicialComplex ℝ E)
    (v : SimplicialVertex K) : SimplicialComponent K :=
  Quot.mk _ v

open Classical in
def simplicialComponent
    (K : Geometry.SimplicialComplex ℝ E)
    (c : SimplicialComponent K) : Geometry.SimplicialComplex ℝ E where
  faces := {s | ∃ (hs : s ∈ K.faces) (v : E) (hv : v ∈ s),
    simplicialComponentOfVertex K
      ⟨v, K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)⟩ = c}
  isRelLowerSet_faces := by
    rintro s ⟨hsK, v, hv, hvc⟩
    refine ⟨K.nonempty_of_mem_faces hsK, ?_⟩
    intro t hts htne
    obtain ⟨w, hwt⟩ := htne
    have htne' : t.Nonempty := ⟨w, hwt⟩
    let htK := K.down_closed hsK hts htne'
    refine ⟨htK, w, hwt, ?_⟩
    have hwv : simplicialComponentOfVertex K
        ⟨w, K.down_closed htK (Finset.singleton_subset_iff.mpr hwt)
          (Finset.singleton_nonempty w)⟩ =
      simplicialComponentOfVertex K
        ⟨v, K.down_closed hsK (Finset.singleton_subset_iff.mpr hv)
          (Finset.singleton_nonempty v)⟩ := by
      apply Quot.sound
      exact K.down_closed hsK
        (Finset.insert_subset_iff.mpr
          ⟨hts hwt, Finset.singleton_subset_iff.mpr hv⟩)
        ⟨w, Finset.mem_insert_self w {v}⟩
    exact hwv.trans hvc
  indep := by
    rintro s ⟨hsK, -⟩
    exact K.indep hsK
  inter_subset_convexHull := by
    rintro s t ⟨hsK, -⟩ ⟨htK, -⟩
    exact K.inter_subset_convexHull hsK htK

theorem mem_simplicialComponent_faces
    (K : Geometry.SimplicialComplex ℝ E) (c : SimplicialComponent K)
    {s : Finset E} :
    s ∈ (simplicialComponent K c).faces ↔
      ∃ (hs : s ∈ K.faces) (v : E) (hv : v ∈ s),
        simplicialComponentOfVertex K
          ⟨v, K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
            (Finset.singleton_nonempty v)⟩ = c :=
  Iff.rfl

theorem simplicialComponent_faces_subset
    (K : Geometry.SimplicialComplex ℝ E) (c : SimplicialComponent K) :
    (simplicialComponent K c).faces ⊆ K.faces :=
  fun _ hs => hs.choose

open Classical in
theorem simplicialComponentOfVertex_eq_of_mem_face
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    {v w : E} (hv : v ∈ s) (hw : w ∈ s) :
    simplicialComponentOfVertex K
        ⟨v, K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
          (Finset.singleton_nonempty v)⟩ =
      simplicialComponentOfVertex K
        ⟨w, K.down_closed hs (Finset.singleton_subset_iff.mpr hw)
          (Finset.singleton_nonempty w)⟩ := by
  apply Quot.sound
  exact K.down_closed hs
    (Finset.insert_subset_iff.mpr ⟨hv, Finset.singleton_subset_iff.mpr hw⟩)
    ⟨v, Finset.mem_insert_self v {w}⟩

open Classical in
theorem exists_unique_simplicialComponent_of_mem_faces
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces) :
    ∃! c : SimplicialComponent K, s ∈ (simplicialComponent K c).faces := by
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  let hvK : {v} ∈ K.faces := K.down_closed hs
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  let c := simplicialComponentOfVertex K ⟨v, hvK⟩
  refine ⟨c, ⟨hs, v, hv, rfl⟩, ?_⟩
  · intro d hsd
    obtain ⟨hsK, w, hw, hwc⟩ := hsd
    exact hwc.symm.trans (simplicialComponentOfVertex_eq_of_mem_face K hs hw hv)

open Classical in
noncomputable def simplicialComponentOfFace
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces) :
    SimplicialComponent K :=
  Classical.choose (exists_unique_simplicialComponent_of_mem_faces K hs)

open Classical in
theorem mem_simplicialComponentOfFace
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces) :
    s ∈ (simplicialComponent K (simplicialComponentOfFace K hs)).faces :=
  (Classical.choose_spec (exists_unique_simplicialComponent_of_mem_faces K hs)).1

open Classical in
theorem simplicialComponentOfFace_eq_of_mem
    (K : Geometry.SimplicialComplex ℝ E) (c : SimplicialComponent K)
    {s : Finset E} (hs : s ∈ K.faces)
    (hsc : s ∈ (simplicialComponent K c).faces) :
    simplicialComponentOfFace K hs = c :=
  ((Classical.choose_spec (exists_unique_simplicialComponent_of_mem_faces K hs)).2 c hsc).symm

noncomputable instance
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (c : SimplicialComponent K) : Finite (simplicialComponent K c).faces :=
  ((Set.toFinite K.faces).subset (simplicialComponent_faces_subset K c)).to_subtype

open Classical in
theorem faceCofaces_simplicialComponent
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (c : SimplicialComponent K) {t : Finset E}
    (ht : t ∈ (simplicialComponent K c).faces) (m : ℕ) :
    faceCofaces (simplicialComponent K c) t m = faceCofaces K t m := by
  ext s
  simp only [mem_faceCofaces]
  constructor
  · rintro ⟨hs, hscard, hts⟩
    exact ⟨simplicialComponent_faces_subset K c hs, hscard, hts⟩
  · rintro ⟨hsK, hscard, hts⟩
    obtain ⟨htK, v, hvt, hvc⟩ := ht
    refine ⟨⟨hsK, v, hts hvt, ?_⟩, hscard, hts⟩
    exact hvc

open Classical in
noncomputable def CoherentOrientation.simplicialComponent
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation n K) (c : SimplicialComponent K) :
    CoherentOrientation n (simplicialComponent K c) where
  vertexOrder := o.vertexOrder
  sign := o.sign
  sign_top := by
    intro s hs hscard
    exact o.sign_top s (simplicialComponent_faces_subset K c hs) hscard
  coherent := by
    intro t ht htcard hne
    have hcofaces := faceCofaces_simplicialComponent K c ht (n + 1)
    have hneK : (faceCofaces K t (n + 1)).card ≠ 1 := by
      rwa [hcofaces] at hne
    have hzero := o.coherent t (simplicialComponent_faces_subset K c ht) htcard hneK
    rw [orientedBoundary_eq_sum_faceCofaces] at hzero
    rw [orientedBoundary_eq_sum_faceCofaces]
    rw [hcofaces]
    exact hzero

open Classical in
theorem IsOrientable.simplicialComponent
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (h : IsOrientable n K) (c : SimplicialComponent K) :
    IsOrientable n (simplicialComponent K c) := by
  obtain ⟨o⟩ := h
  exact ⟨o.simplicialComponent c⟩

open Classical in
theorem isOrientable_iff_forall_simplicialComponent
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    IsOrientable n K ↔
      ∀ c : SimplicialComponent K, IsOrientable n (simplicialComponent K c) := by
  constructor
  · intro h c
    exact h.simplicialComponent c
  · intro h
    let componentOrder : LinearOrder (SimplicialComponent K) :=
      linearOrderOfSTO WellOrderingRel
    let _ := componentOrder
    let chosen : ∀ c : SimplicialComponent K,
        CoherentOrientation n (simplicialComponent K c) :=
      fun c => Classical.choice (h c)
    let Key :=
      (SimplicialComponent K ×ₗ (ℕ ×ₗ OrderAmalgamTie E)) ⊕ₗ OrderAmalgamTie E
    let key : E → Key := fun x =>
      if hx : {x} ∈ K.faces then
        toLex (Sum.inl (toLex
          (simplicialComponentOfVertex K ⟨x, hx⟩,
            toLex (finiteOrderRank
              (chosen (simplicialComponentOfVertex K ⟨x, hx⟩)).vertexOrder
              (complexVertexFinset K) x, ⟨x⟩))))
      else toLex (Sum.inr ⟨x⟩)
    let untie : Key → E := fun z =>
      match ofLex z with
      | Sum.inl p => (ofLex (ofLex p).2).2.val
      | Sum.inr x => x.val
    have untie_key (x : E) : untie (key x) = x := by
      simp only [key]
      split <;> rfl
    have key_injective : Function.Injective key := by
      intro x y hxy
      calc
        x = untie (key x) := (untie_key x).symm
        _ = untie (key y) := congrArg untie hxy
        _ = y := untie_key y
    let r : LinearOrder E := LinearOrder.lift' key key_injective
    have key_lt_of_component_lt (c : SimplicialComponent K) {x y : E}
        (hxK : {x} ∈ K.faces) (hyK : {y} ∈ K.faces)
        (hxc : simplicialComponentOfVertex K ⟨x, hxK⟩ = c)
        (hyc : simplicialComponentOfVertex K ⟨y, hyK⟩ = c)
        (hxy : @LT.lt E (chosen c).vertexOrder.toLT x y) :
        key x < key y := by
      have hxV : x ∈ complexVertexFinset K := (mem_complexVertexFinset K x).mpr hxK
      have hrank := finiteOrderRank_lt_of_mem (chosen c).vertexOrder
        (complexVertexFinset K) hxV hxy
      dsimp only [key]
      rw [dif_pos hxK, dif_pos hyK]
      apply Sum.Lex.inl
      apply Prod.Lex.toLex_lt_toLex.mpr
      refine Or.inr ⟨hxc.trans hyc.symm, ?_⟩
      apply Prod.Lex.toLex_lt_toLex.mpr
      have hxorder :
          (chosen (simplicialComponentOfVertex K ⟨x, hxK⟩)).vertexOrder =
            (chosen c).vertexOrder :=
        congrArg (fun d => (chosen d).vertexOrder) hxc
      have hyorder :
          (chosen (simplicialComponentOfVertex K ⟨y, hyK⟩)).vertexOrder =
            (chosen c).vertexOrder :=
        congrArg (fun d => (chosen d).vertexOrder) hyc
      exact Or.inl (by rw [hxorder, hyorder]; exact hrank)
    have horder (c : SimplicialComponent K) (x y : E)
        (hx : {x} ∈ (simplicialComponent K c).faces)
        (hy : {y} ∈ (simplicialComponent K c).faces) :
        (@LT.lt E r.toLT x y ↔ @LT.lt E (chosen c).vertexOrder.toLT x y) := by
      have hxK : {x} ∈ K.faces := simplicialComponent_faces_subset K c hx
      have hyK : {y} ∈ K.faces := simplicialComponent_faces_subset K c hy
      rcases hx with ⟨hxK', vx, hvx, hvxc⟩
      rcases hy with ⟨hyK', vy, hvy, hvyc⟩
      have hxc : simplicialComponentOfVertex K ⟨x, hxK⟩ = c := by
        have hvxeq : vx = x := Finset.mem_singleton.mp hvx
        subst vx
        exact hvxc
      have hyc : simplicialComponentOfVertex K ⟨y, hyK⟩ = c := by
        have hvyeq : vy = y := Finset.mem_singleton.mp hvy
        subst vy
        exact hvyc
      change key x < key y ↔ _
      constructor
      · intro hkey
        let _ := (chosen c).vertexOrder
        rcases lt_trichotomy x y with hxy | hxy | hyx
        · exact hxy
        · subst y
          exact False.elim (lt_irrefl _ hkey)
        · have hreverse := key_lt_of_component_lt c hyK hxK hyc hxc hyx
          exact False.elim (asymm hkey hreverse)
      · exact key_lt_of_component_lt c hxK hyK hxc hyc
    let oriented : ∀ c : SimplicialComponent K,
        CoherentOrientation n (simplicialComponent K c) :=
      fun c => (chosen c).withVertexOrder r (horder c)
    let sign : Finset E → ℤ := fun s =>
      if hs : s ∈ K.faces then
        (oriented (simplicialComponentOfFace K hs)).sign s
      else 0
    refine ⟨{
      vertexOrder := r
      sign := sign
      sign_top := ?_
      coherent := ?_ }⟩
    · intro s hs hscard
      simp only [sign, dif_pos hs]
      exact (oriented (simplicialComponentOfFace K hs)).sign_top s
        (mem_simplicialComponentOfFace K hs) hscard
    · intro t ht htcard hne
      let c := simplicialComponentOfFace K ht
      have htC : t ∈ (simplicialComponent K c).faces :=
        mem_simplicialComponentOfFace K ht
      have hcofaces := faceCofaces_simplicialComponent K c htC (n + 1)
      have hneC : (faceCofaces (simplicialComponent K c) t (n + 1)).card ≠ 1 := by
        rwa [hcofaces]
      have hzero := (oriented c).coherent t htC htcard hneC
      rw [orientedBoundary_eq_sum_faceCofaces] at hzero ⊢
      rw [hcofaces] at hzero
      calc
        (∑ s ∈ faceCofaces K t (n + 1),
            sign s * simplexBoundaryCoefficient r s t) =
            ∑ s ∈ faceCofaces K t (n + 1),
              (oriented c).sign s * simplexBoundaryCoefficient r s t := by
          apply Finset.sum_congr rfl
          intro s hsco
          obtain ⟨hsK, -, -⟩ := (mem_faceCofaces K).mp hsco
          have hscoC : s ∈ faceCofaces (simplicialComponent K c) t (n + 1) := by
            rw [hcofaces]
            exact hsco
          have hsC := (mem_faceCofaces (simplicialComponent K c)).mp hscoC |>.1
          have hc := simplicialComponentOfFace_eq_of_mem K c hsK hsC
          have hsign : (oriented (simplicialComponentOfFace K hsK)).sign s =
              (oriented c).sign s :=
            congrArg (fun d => (oriented d).sign s) hc
          simp only [sign, dif_pos hsK]
          rw [hsign]
        _ = 0 := hzero

end

noncomputable def permutedFacePrefix
    (r : LinearOrder E) (T : Finset E) {N : ℕ} (hT : T.card = N + 1)
    (σ : Equiv.Perm (Fin (N + 1))) (k : Fin (N + 1)) : Finset E := by
  let _ := r
  exact (Finset.Iic k).image
    (fun i => ((Finset.orderIsoOfFin T hT) (σ i)).1)

noncomputable def permutedFaceFlag
    (r : LinearOrder E) (T : Finset E) {N : ℕ} (hT : T.card = N + 1)
    (σ : Equiv.Perm (Fin (N + 1))) : Finset (Finset E) :=
  Finset.univ.image (permutedFacePrefix r T hT σ)

open Classical in
theorem permutedFacePrefix_card
    (r : LinearOrder E) (T : Finset E) {N : ℕ} (hT : T.card = N + 1)
    (σ : Equiv.Perm (Fin (N + 1))) (k : Fin (N + 1)) :
    (permutedFacePrefix r T hT σ k).card = k + 1 := by
  let _ := r
  unfold permutedFacePrefix
  rw [Finset.card_image_of_injective]
  · exact Fin.card_Iic k
  · exact Subtype.val_injective.comp
      ((Finset.orderIsoOfFin T hT).injective.comp σ.injective)

open Classical in
theorem permutedFacePrefix_nonempty
    (r : LinearOrder E) (T : Finset E) {N : ℕ} (hT : T.card = N + 1)
    (σ : Equiv.Perm (Fin (N + 1))) (k : Fin (N + 1)) :
    (permutedFacePrefix r T hT σ k).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have hc := permutedFacePrefix_card r T hT σ k
  rw [h, Finset.card_empty] at hc
  omega

open Classical in
theorem permutedFacePrefix_subset
    (r : LinearOrder E) (T : Finset E) {N : ℕ} (hT : T.card = N + 1)
    (σ : Equiv.Perm (Fin (N + 1))) (k : Fin (N + 1)) :
    permutedFacePrefix r T hT σ k ⊆ T := by
  let _ := r
  intro x hx
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
  exact ((Finset.orderIsoOfFin T hT) (σ i)).2

open Classical in
theorem permutedFacePrefix_mono
    (r : LinearOrder E) (T : Finset E) {N : ℕ} (hT : T.card = N + 1)
    (σ : Equiv.Perm (Fin (N + 1))) :
    Monotone (permutedFacePrefix r T hT σ) := by
  let _ := r
  intro i j hij x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_image.mpr
  exact ⟨a, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp ha).trans hij), rfl⟩

open Classical in
theorem permutedFaceFlag_card
    (r : LinearOrder E) (T : Finset E) {N : ℕ} (hT : T.card = N + 1)
    (σ : Equiv.Perm (Fin (N + 1))) :
    (permutedFaceFlag r T hT σ).card = N + 1 := by
  unfold permutedFaceFlag
  rw [Finset.card_image_of_injOn]
  · simp
  · intro i hi j hj heq
    have hc := congrArg Finset.card heq
    rw [permutedFacePrefix_card, permutedFacePrefix_card] at hc
    exact Fin.ext (by omega)

open Classical in
theorem permutedFacePrefix_injective
    (r : LinearOrder E) (T : Finset E) {N : ℕ} (hT : T.card = N + 1)
    (σ : Equiv.Perm (Fin (N + 1))) :
    Function.Injective (permutedFacePrefix r T hT σ) := by
  intro i j hij
  have hc := congrArg Finset.card hij
  rw [permutedFacePrefix_card, permutedFacePrefix_card] at hc
  exact Fin.ext (by omega)

open Classical in
theorem permutedFaceFlag_nonempty
    (r : LinearOrder E) (T : Finset E) {N : ℕ} (hT : T.card = N + 1)
    (σ : Equiv.Perm (Fin (N + 1))) :
    (permutedFaceFlag r T hT σ).Nonempty := by
  refine ⟨permutedFacePrefix r T hT σ 0, ?_⟩
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

open Classical in
theorem permutedFaceFlag_isFlag
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (r : LinearOrder E)
    {T : Finset E} (hTK : T ∈ K.faces) {N : ℕ} (hT : T.card = N + 1)
    (σ : Equiv.Perm (Fin (N + 1))) :
    IsFlag K (permutedFaceFlag r T hT σ) := by
  constructor
  · intro s hs
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hs
    exact K.down_closed hTK (permutedFacePrefix_subset r T hT σ k)
      (permutedFacePrefix_nonempty r T hT σ k)
  · intro s hs t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht
    rcases le_total i j with hij | hji
    · exact Or.inl (permutedFacePrefix_mono r T hT σ hij)
    · exact Or.inr (permutedFacePrefix_mono r T hT σ hji)

def adjacentPermutedFaceSwap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 2)) :=
  σ * Equiv.swap i.castSucc i.succ

@[simp]
theorem adjacentPermutedFaceSwap_apply {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1))
    (j : Fin (n + 2)) :
    adjacentPermutedFaceSwap σ i j = σ (Equiv.swap i.castSucc i.succ j) := by
  rfl

theorem adjacentFaceSwap_le_iff_of_ne {n : ℕ}
    (i : Fin (n + 1)) (k a : Fin (n + 2)) (hk : k ≠ i.castSucc) :
    Equiv.swap i.castSucc i.succ a ≤ k ↔ a ≤ k := by
  rw [Equiv.swap_apply_def]
  split_ifs with ha hia
  · subst a
    constructor
    · exact fun h => (Fin.castSucc_le_succ i).trans h
    · intro h
      simpa only [Fin.orderSucc_castSucc] using
        Order.succ_le_of_lt (lt_of_le_of_ne h hk.symm)
  · subst a
    constructor
    · intro h
      simpa only [Fin.orderSucc_castSucc] using
        Order.succ_le_of_lt (lt_of_le_of_ne h hk.symm)
    · exact fun h => (Fin.castSucc_le_succ i).trans h
  · rfl

open Classical in
theorem permutedFacePrefix_adjacentPermutedFaceSwap_of_ne
    (r : LinearOrder E) (T : Finset E) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ i.castSucc) :
    permutedFacePrefix r T hT (adjacentPermutedFaceSwap σ i) k =
      permutedFacePrefix r T hT σ k := by
  let _ := r
  have hswap :
      (Finset.Iic k).image (Equiv.swap i.castSucc i.succ) = Finset.Iic k := by
    ext a
    simp only [Finset.mem_image, Finset.mem_Iic]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (adjacentFaceSwap_le_iff_of_ne i k b hk).2 hb
    · intro ha
      refine ⟨Equiv.swap i.castSucc i.succ a, ?_, ?_⟩
      · exact (adjacentFaceSwap_le_iff_of_ne i k _ hk).2 ha
      · simp
  unfold permutedFacePrefix
  let f : Fin (n + 2) → E :=
    fun j => ((Finset.orderIsoOfFin T hT) (σ j)).1
  change (Finset.Iic k).image
      (f ∘ Equiv.swap i.castSucc i.succ) = (Finset.Iic k).image f
  rw [← Finset.image_image, hswap]

open Classical in
theorem permutedFacePrefix_adjacentPermutedFaceSwap_succAbove
    (r : LinearOrder E) (T : Finset E) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i j : Fin (n + 1)) :
    permutedFacePrefix r T hT (adjacentPermutedFaceSwap σ i)
        (i.castSucc.succAbove j) =
      permutedFacePrefix r T hT σ (i.castSucc.succAbove j) := by
  apply permutedFacePrefix_adjacentPermutedFaceSwap_of_ne
  exact Fin.succAbove_ne _ _

open Classical in
theorem permutedFaceFlag_eq_insert_prefix_image_succAbove
    (r : LinearOrder E) (T : Finset E) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    permutedFaceFlag r T hT σ =
      insert (permutedFacePrefix r T hT σ i.castSucc)
        (Finset.univ.image (fun j : Fin (n + 1) =>
          permutedFacePrefix r T hT σ (i.castSucc.succAbove j))) := by
  unfold permutedFaceFlag
  let f := permutedFacePrefix r T hT σ
  calc
    Finset.univ.image f =
        (insert i.castSucc (Finset.univ.image i.castSucc.succAbove)).image f := by
      rw [Fin.image_succAbove_univ]
      simp
    _ = insert (f i.castSucc)
        ((Finset.univ.image i.castSucc.succAbove).image f) := by
      rw [Finset.image_insert]
    _ = insert (f i.castSucc)
        (Finset.univ.image (fun j => f (i.castSucc.succAbove j))) := by
      rw [Finset.image_image]
      rfl

open Classical in
theorem permutedFaceFlag_adjacent_decomposition
    (r : LinearOrder E) (T : Finset E) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    let d := Finset.univ.image (fun j : Fin (n + 1) =>
      permutedFacePrefix r T hT σ (i.castSucc.succAbove j))
    permutedFaceFlag r T hT σ =
        insert (permutedFacePrefix r T hT σ i.castSucc) d ∧
      permutedFaceFlag r T hT (adjacentPermutedFaceSwap σ i) =
        insert (permutedFacePrefix r T hT (adjacentPermutedFaceSwap σ i)
          i.castSucc) d := by
  dsimp only
  constructor
  · exact permutedFaceFlag_eq_insert_prefix_image_succAbove r T hT σ i
  · rw [permutedFaceFlag_eq_insert_prefix_image_succAbove]
    congr 1
    apply Finset.image_congr
    intro j hj
    exact permutedFacePrefix_adjacentPermutedFaceSwap_succAbove r T hT σ i j

noncomputable def adjacentFaceCommonFlag
    (r : LinearOrder E) (T : Finset E) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    Finset (Finset E) :=
  Finset.univ.image (fun j : Fin (n + 1) =>
    permutedFacePrefix r T hT σ (i.castSucc.succAbove j))

open Classical in
theorem permutedFacePrefix_not_mem_adjacentFaceCommonFlag
    (r : LinearOrder E) (T : Finset E) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    permutedFacePrefix r T hT σ i.castSucc ∉
      adjacentFaceCommonFlag r T hT σ i := by
  rintro hm
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hm
  have heq := permutedFacePrefix_injective r T hT σ hj.symm
  exact Fin.succAbove_ne i.castSucc j heq.symm

open Classical in
theorem adjacentPermutedFacePrefix_not_mem_adjacentFaceCommonFlag
    (r : LinearOrder E) (T : Finset E) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    permutedFacePrefix r T hT (adjacentPermutedFaceSwap σ i) i.castSucc ∉
      adjacentFaceCommonFlag r T hT σ i := by
  rintro hp
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hp
  have hsame := permutedFacePrefix_adjacentPermutedFaceSwap_succAbove
    r T hT σ i j
  have heq := permutedFacePrefix_injective r T hT
    (adjacentPermutedFaceSwap σ i) (hj.symm.trans hsame.symm)
  exact Fin.succAbove_ne i.castSucc j heq.symm

open Classical in
theorem adjacentFaceCommonFlag_card
    (r : LinearOrder E) (T : Finset E) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    (adjacentFaceCommonFlag r T hT σ i).card = n + 1 := by
  unfold adjacentFaceCommonFlag
  rw [Finset.card_image_of_injOn]
  · simp
  · intro j hj k hk hjk
    apply Fin.succAbove_right_injective
    exact permutedFacePrefix_injective r T hT σ hjk

open Classical in
theorem adjacentFacePrefixes_ne
    (r : LinearOrder E) (T : Finset E) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    permutedFacePrefix r T hT σ i.castSucc ≠
      permutedFacePrefix r T hT (adjacentPermutedFaceSwap σ i) i.castSucc := by
  intro h
  let _ := r
  let e := Finset.orderIsoOfFin T hT
  let f : Fin (n + 2) → E := fun j => (e (σ j)).1
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (e.injective.comp σ.injective)
  have hleft : (Finset.Iic i.castSucc).image f =
      permutedFacePrefix r T hT σ i.castSucc := rfl
  have hright :
      ((Finset.Iic i.castSucc).image (Equiv.swap i.castSucc i.succ)).image f =
        permutedFacePrefix r T hT (adjacentPermutedFaceSwap σ i) i.castSucc := by
    rw [Finset.image_image]
    rfl
  have hsource : Finset.Iic i.castSucc =
      (Finset.Iic i.castSucc).image (Equiv.swap i.castSucc i.succ) := by
    apply Finset.image_injective hf
    exact hleft.trans (h.trans hright.symm)
  have hi : i.castSucc ∈
      (Finset.Iic i.castSucc).image (Equiv.swap i.castSucc i.succ) :=
    (Finset.ext_iff.mp hsource i.castSucc).mp (Finset.mem_Iic.mpr le_rfl)
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
  have hjval : j = i.succ := by
    have hs := congrArg (Equiv.swap i.castSucc i.succ) hji
    simpa using hs
  rw [Finset.mem_Iic, hjval] at hj
  exact (not_le_of_gt i.castSucc_lt_succ) hj

open Classical in
noncomputable def permutedBarycentricFace
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : LinearOrder E) (T : Finset E) {N : ℕ} (hT : T.card = N + 1)
    (σ : Equiv.Perm (Fin (N + 1))) : Finset E :=
  (permutedFaceFlag r T hT σ).image (fun s => s.centroid ℝ id)

open Classical in
theorem permutedBarycentricFace_mem
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (r : LinearOrder E)
    {T : Finset E} (hTK : T ∈ K.faces) {N : ℕ} (hT : T.card = N + 1)
    (σ : Equiv.Perm (Fin (N + 1))) :
    permutedBarycentricFace r T hT σ ∈ (barycentricSubdivision K).faces := by
  exact ⟨permutedFaceFlag r T hT σ,
    permutedFaceFlag_isFlag K r hTK hT σ,
    permutedFaceFlag_nonempty r T hT σ, rfl⟩

open Classical in
theorem permutedBarycentricFace_card
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (r : LinearOrder E)
    {T : Finset E} (hTK : T ∈ K.faces) {N : ℕ} (hT : T.card = N + 1)
    (σ : Equiv.Perm (Fin (N + 1))) :
    (permutedBarycentricFace r T hT σ).card = N + 1 := by
  unfold permutedBarycentricFace
  rw [Finset.card_image_of_injOn]
  · exact permutedFaceFlag_card r T hT σ
  · exact (injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K)).mono
        (permutedFaceFlag_isFlag K r hTK hT σ).coe_subset_faces

open Classical in
noncomputable def barycentricFlagNormalizedSign
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : LinearOrder E)
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] [Finite (barycentricSubdivision K).faces]
    (o : CoherentOrientation (n + 1) (barycentricSubdivision K))
    {T : Finset E} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) : ℤ :=
  o.sign (permutedBarycentricFace r T hT σ) *
    (Equiv.Perm.sign σ : ℤ)

noncomputable def orderChangePermutation
    (r₁ r₂ : LinearOrder E) (s : Finset E) : Equiv.Perm (Fin s.card) := by
  let e₁ : Fin s.card ≃ s := by
    let _ := r₁
    exact (Finset.orderIsoOfFin s rfl).toEquiv
  let e₂ : Fin s.card ≃ s := by
    let _ := r₂
    exact (Finset.orderIsoOfFin s rfl).toEquiv
  exact e₁.trans e₂.symm

noncomputable def orderChangeSign
    (r₁ r₂ : LinearOrder E) (s : Finset E) : ℤ :=
  (Equiv.Perm.sign (orderChangePermutation r₁ r₂ s) : ℤ)

open Classical in
theorem orderIsoOfFin_symm_eq_incidenceIndex
    (r : LinearOrder E) (s : Finset E) {v : E} (hv : v ∈ s) :
    (((Finset.orderIsoOfFin s rfl).symm ⟨v, hv⟩ : Fin s.card) : ℕ) =
      incidenceIndex r s v := by
  let _ := r
  let e := Finset.orderIsoOfFin s rfl
  let p : Fin s.card := e.symm ⟨v, hv⟩
  have hfilter : s.filter (fun w => w < v) =
      (Finset.Iio p).image (fun i => (e i).1) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨hw, hwv⟩
      let i : Fin s.card := e.symm ⟨w, hw⟩
      refine ⟨i, ?_, ?_⟩
      · apply (e.lt_iff_lt).mp
        change (e i).1 < (e p).1
        simpa [i, p] using hwv
      · simp [i]
    · rintro ⟨i, hip, rfl⟩
      refine ⟨(e i).2, ?_⟩
      have hlt : e i < e p := e.strictMono hip
      change (e i).1 < (e p).1 at hlt
      simpa [p] using hlt
  change _ = (s.filter fun w => w < v).card
  rw [hfilter, Finset.card_image_of_injective]
  · exact (Fin.card_Iio p).symm
  · exact Subtype.val_injective.comp e.injective

private noncomputable def orderChangePermutationOfCard
    (r₁ r₂ : LinearOrder E) (s : Finset E) {N : ℕ} (h : s.card = N) :
    Equiv.Perm (Fin N) := by
  let e₁ : Fin N ≃ s := by
    let _ := r₁
    exact (Finset.orderIsoOfFin s h).toEquiv
  let e₂ : Fin N ≃ s := by
    let _ := r₂
    exact (Finset.orderIsoOfFin s h).toEquiv
  exact e₁.trans e₂.symm

private noncomputable def orderChangeSignOfCard
    (r₁ r₂ : LinearOrder E) (s : Finset E) {N : ℕ} (h : s.card = N) : ℤ :=
  (Equiv.Perm.sign (orderChangePermutationOfCard r₁ r₂ s h) : ℤ)

open Classical in
private theorem orderChangeSignOfCard_eq
    (r₁ r₂ : LinearOrder E) (s : Finset E) {N : ℕ} (h : s.card = N) :
    orderChangeSignOfCard r₁ r₂ s h = orderChangeSign r₁ r₂ s := by
  subst N
  rfl

open Classical in
private theorem orderEmbOfFin_erase_apply
    (r : LinearOrder E) (s : Finset E) {n : ℕ} (hs : s.card = n + 1)
    {v : E} (hv : v ∈ s)
    (ht : (@Finset.erase E (Classical.decEq E) s v).card = n) (i : Fin n) :
    let p := (Finset.orderIsoOfFin s hs).symm ⟨v, hv⟩
    Finset.orderEmbOfFin (@Finset.erase E (Classical.decEq E) s v) ht i =
      Finset.orderEmbOfFin s hs
        (Fin.cycleIcc p (Fin.last n) i.castSucc) := by
  let _ := r
  let e := Finset.orderEmbOfFin s hs
  let p := (Finset.orderIsoOfFin s hs).symm ⟨v, hv⟩
  have hp : p ≤ Fin.last n := Fin.le_last p
  have hcycle (j : Fin n) :
      Fin.cycleIcc p (Fin.last n) j.castSucc = p.succAbove j := by
    simpa [Function.comp_apply] using congrFun
      (Fin.cycleIcc_comp_succAbove p (Fin.last n) hp) j
  have hmem (j : Fin n) :
      e (p.succAbove j) ∈ @Finset.erase E (Classical.decEq E) s v := by
    apply (@Finset.mem_erase E (Classical.decEq E) (e (p.succAbove j)) v s).mpr
    refine ⟨?_, Finset.orderEmbOfFin_mem s hs _⟩
    intro heq
    have hpval : e p = v := by
      change ((Finset.orderIsoOfFin s hs) p).1 = v
      simp [p]
    have := e.injective (heq.trans hpval.symm)
    exact Fin.succAbove_ne p j this
  have heq : (fun j : Fin n => e (p.succAbove j)) =
      Finset.orderEmbOfFin (@Finset.erase E (Classical.decEq E) s v) ht := by
    apply Finset.orderEmbOfFin_unique ht hmem
    exact e.strictMono.comp (Fin.strictMono_succAbove p)
  change Finset.orderEmbOfFin (@Finset.erase E (Classical.decEq E) s v) ht i =
    e (Fin.cycleIcc p (Fin.last n) i.castSucc)
  rw [hcycle]
  exact congrFun heq i |>.symm


private noncomputable def orderPositionOfCard
    (r : LinearOrder E) (s : Finset E) {N : ℕ} (h : s.card = N)
    (v : E) (hv : v ∈ s) : Fin N := by
  let _ := r
  exact (Finset.orderIsoOfFin s h).symm ⟨v, hv⟩

open Classical in
private theorem orderChangePermutationOfCard_apply_orderPosition
    (r₁ r₂ : LinearOrder E) (s : Finset E) {N : ℕ} (h : s.card = N)
    (v : E) (hv : v ∈ s) :
    orderChangePermutationOfCard r₁ r₂ s h
        (orderPositionOfCard r₁ s h v hv) =
      orderPositionOfCard r₂ s h v hv := by
  unfold orderChangePermutationOfCard orderPositionOfCard
  simp

private noncomputable def normalizedOrderChangePermutation
    (r₁ r₂ : LinearOrder E) (s : Finset E) {n : ℕ} (h : s.card = n + 1)
    (v : E) (hv : v ∈ s) : Equiv.Perm (Fin (n + 1)) :=
  let p₁ := orderPositionOfCard r₁ s h v hv
  let p₂ := orderPositionOfCard r₂ s h v hv
  ((Fin.cycleIcc p₁ (Fin.last n)).trans
    (orderChangePermutationOfCard r₁ r₂ s h)).trans
      (Fin.cycleIcc p₂ (Fin.last n)).symm

open Classical in
private theorem normalizedOrderChangePermutation_last
    (r₁ r₂ : LinearOrder E) (s : Finset E) {n : ℕ} (h : s.card = n + 1)
    (v : E) (hv : v ∈ s) :
    normalizedOrderChangePermutation r₁ r₂ s h v hv (Fin.last n) =
      Fin.last n := by
  unfold normalizedOrderChangePermutation
  simp only [Equiv.trans_apply]
  rw [Fin.cycleIcc_of_last (Fin.le_last _),
    orderChangePermutationOfCard_apply_orderPosition]
  apply (Fin.cycleIcc (orderPositionOfCard r₂ s h v hv) (Fin.last n)).injective
  rw [Equiv.apply_symm_apply, Fin.cycleIcc_of_last (Fin.le_last _)]

private noncomputable def orderValueOfCard
    (r : LinearOrder E) (s : Finset E) {N : ℕ} (h : s.card = N)
    (i : Fin N) : E := by
  let _ := r
  exact Finset.orderEmbOfFin s h i

open Classical in
private theorem orderValueOfCard_orderChangePermutation
    (r₁ r₂ : LinearOrder E) (s : Finset E) {N : ℕ} (h : s.card = N)
    (i : Fin N) :
    orderValueOfCard r₂ s h (orderChangePermutationOfCard r₁ r₂ s h i) =
      orderValueOfCard r₁ s h i := by
  let e₁ : Fin N ≃ s := by
    let _ := r₁
    exact (Finset.orderIsoOfFin s h).toEquiv
  let e₂ : Fin N ≃ s := by
    let _ := r₂
    exact (Finset.orderIsoOfFin s h).toEquiv
  unfold orderValueOfCard orderChangePermutationOfCard
  change (e₂ (e₂.symm (e₁ i))).1 = (e₁ i).1
  rw [Equiv.apply_symm_apply]

open Classical in
private theorem orderValueOfCard_erase_apply
    (r : LinearOrder E) (s : Finset E) {n : ℕ} (hs : s.card = n + 1)
    {v : E} (hv : v ∈ s)
    (ht : (@Finset.erase E (Classical.decEq E) s v).card = n) (i : Fin n) :
    orderValueOfCard r (@Finset.erase E (Classical.decEq E) s v) ht i =
      orderValueOfCard r s hs
        (Fin.cycleIcc (orderPositionOfCard r s hs v hv) (Fin.last n) i.castSucc) := by
  let _ := r
  exact orderEmbOfFin_erase_apply r s hs hv ht i

open Classical in
private theorem normalizedOrderChangePermutation_apply_castSucc
    (r₁ r₂ : LinearOrder E) (s : Finset E) {n : ℕ} (hs : s.card = n + 1)
    (v : E) (hv : v ∈ s)
    (ht : (@Finset.erase E (Classical.decEq E) s v).card = n) (i : Fin n) :
    normalizedOrderChangePermutation r₁ r₂ s hs v hv i.castSucc =
      (orderChangePermutationOfCard r₁ r₂
        (@Finset.erase E (Classical.decEq E) s v) ht i).castSucc := by
  let p₁ := orderPositionOfCard r₁ s hs v hv
  let p₂ := orderPositionOfCard r₂ s hs v hv
  let q₁ := Fin.cycleIcc p₁ (Fin.last n)
  let q₂ := Fin.cycleIcc p₂ (Fin.last n)
  let σ := orderChangePermutationOfCard r₁ r₂ s hs
  let t := @Finset.erase E (Classical.decEq E) s v
  let τ := orderChangePermutationOfCard r₁ r₂ t ht
  have hq₁ (j : Fin n) : q₁ j.castSucc = p₁.succAbove j := by
    simpa [q₁, Function.comp_apply] using congrFun
      (Fin.cycleIcc_comp_succAbove p₁ (Fin.last n) (Fin.le_last _)) j
  have hq₂ (j : Fin n) : q₂ j.castSucc = p₂.succAbove j := by
    simpa [q₂, Function.comp_apply] using congrFun
      (Fin.cycleIcc_comp_succAbove p₂ (Fin.last n) (Fin.le_last _)) j
  change q₂.symm (σ (q₁ i.castSucc)) = (τ i).castSucc
  apply q₂.injective
  rw [Equiv.apply_symm_apply, hq₂]
  apply (show Function.Injective (orderValueOfCard r₂ s hs) by
    unfold orderValueOfCard
    let _ := r₂
    exact (Finset.orderEmbOfFin s hs).injective)
  calc
    orderValueOfCard r₂ s hs (σ (q₁ i.castSucc)) =
        orderValueOfCard r₁ s hs (q₁ i.castSucc) :=
      orderValueOfCard_orderChangePermutation r₁ r₂ s hs _
    _ = orderValueOfCard r₁ t ht i := by
      simpa [t, p₁, q₁] using
        (orderValueOfCard_erase_apply r₁ s hs hv ht i).symm
    _ = orderValueOfCard r₂ t ht (τ i) := by
      exact (orderValueOfCard_orderChangePermutation r₁ r₂ t ht i).symm
    _ = orderValueOfCard r₂ s hs (p₂.succAbove (τ i)) := by
      calc
        orderValueOfCard r₂ t ht (τ i) =
            orderValueOfCard r₂ s hs (q₂ (τ i).castSucc) := by
          simpa [t, p₂, q₂] using
            orderValueOfCard_erase_apply r₂ s hs hv ht (τ i)
        _ = _ := by rw [hq₂]

open Classical in
private theorem eraseLastPermutation_normalizedOrderChangePermutation
    (r₁ r₂ : LinearOrder E) (s : Finset E) {n : ℕ} (hs : s.card = n + 1)
    (v : E) (hv : v ∈ s)
    (ht : (@Finset.erase E (Classical.decEq E) s v).card = n) :
    SphereSeparation.eraseLastPermutation
        (normalizedOrderChangePermutation r₁ r₂ s hs v hv) =
      orderChangePermutationOfCard r₁ r₂
        (@Finset.erase E (Classical.decEq E) s v) ht := by
  apply Equiv.ext
  intro i
  have h := SphereSeparation.succAbove_eraseLastPermutation
    (normalizedOrderChangePermutation r₁ r₂ s hs v hv) i
  rw [normalizedOrderChangePermutation_last] at h
  simp only [Fin.succAbove_last_apply] at h
  rw [normalizedOrderChangePermutation_apply_castSucc r₁ r₂ s hs v hv ht i] at h
  exact Fin.castSucc_injective _ h

private theorem negOne_pow_tsub_mul_negOne_pow_tsub
    {n a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) :
    (-1 : ℤˣ) ^ (n - a) * (-1 : ℤˣ) ^ (n - b) =
      (-1 : ℤˣ) ^ (a + b) := by
  let A : ℤˣ := (-1 : ℤˣ) ^ (n - a) * (-1 : ℤˣ) ^ (n - b)
  let C : ℤˣ := (-1 : ℤˣ) ^ (a + b)
  have hsum : (n - a) + (n - b) + (a + b) = 2 * n := by omega
  have hAC : A * C = 1 := by
    dsimp only [A, C]
    rw [← pow_add, ← pow_add, hsum]
    rw [pow_mul]
    norm_num
  have hCC : C * C = 1 := by
    dsimp only [C]
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    A = A * 1 := (mul_one A).symm
    _ = A * (C * C) := by rw [hCC]
    _ = (A * C) * C := by ac_rfl
    _ = 1 * C := by rw [hAC]
    _ = C := one_mul C

open Classical in
private theorem orderPositionOfCard_eq_incidenceIndex
    (r : LinearOrder E) (s : Finset E) {N : ℕ} (h : s.card = N)
    (v : E) (hv : v ∈ s) :
    (orderPositionOfCard r s h v hv : ℕ) = incidenceIndex r s v := by
  subst N
  exact orderIsoOfFin_symm_eq_incidenceIndex r s hv

open Classical in
private theorem sign_orderChangePermutationOfCard_erase
    (r₁ r₂ : LinearOrder E) (s : Finset E) {n : ℕ} (hs : s.card = n + 1)
    (v : E) (hv : v ∈ s)
    (ht : (@Finset.erase E (Classical.decEq E) s v).card = n) :
    Equiv.Perm.sign (orderChangePermutationOfCard r₁ r₂ s hs) =
      Equiv.Perm.sign (orderChangePermutationOfCard r₁ r₂
          (@Finset.erase E (Classical.decEq E) s v) ht) *
        (-1 : ℤˣ) ^ (incidenceIndex r₁ s v + incidenceIndex r₂ s v) := by
  let p₁ := orderPositionOfCard r₁ s hs v hv
  let p₂ := orderPositionOfCard r₂ s hs v hv
  let q₁ := Fin.cycleIcc p₁ (Fin.last n)
  let q₂ := Fin.cycleIcc p₂ (Fin.last n)
  let σ := orderChangePermutationOfCard r₁ r₂ s hs
  let τ := orderChangePermutationOfCard r₁ r₂
    (@Finset.erase E (Classical.decEq E) s v) ht
  let ρ := normalizedOrderChangePermutation r₁ r₂ s hs v hv
  have hρτ : Equiv.Perm.sign ρ = Equiv.Perm.sign τ := by
    rw [SphereSeparation.sign_eq_sign_eraseLastPermutation_mul]
    rw [eraseLastPermutation_normalizedOrderChangePermutation r₁ r₂ s hs v hv ht]
    rw [normalizedOrderChangePermutation_last r₁ r₂ s hs v hv]
    simp only [Fin.val_last, tsub_self, pow_zero, mul_one]
    congr
  have hρ : Equiv.Perm.sign ρ =
      Equiv.Perm.sign q₂ * Equiv.Perm.sign σ * Equiv.Perm.sign q₁ := by
    dsimp only [ρ, normalizedOrderChangePermutation, p₁, p₂, q₁, q₂, σ]
    rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_trans, Equiv.Perm.sign_symm]
    exact (mul_assoc _ _ _).symm
  have hq₁ : Equiv.Perm.sign q₁ =
      (-1 : ℤˣ) ^ (n - (p₁ : ℕ)) := by
    exact Fin.sign_cycleIcc_of_le (Fin.le_last p₁)
  have hq₂ : Equiv.Perm.sign q₂ =
      (-1 : ℤˣ) ^ (n - (p₂ : ℕ)) := by
    exact Fin.sign_cycleIcc_of_le (Fin.le_last p₂)
  let C : ℤˣ := (-1 : ℤˣ) ^ ((p₁ : ℕ) + (p₂ : ℕ))
  have hfactor : Equiv.Perm.sign q₁ * Equiv.Perm.sign q₂ = C := by
    rw [hq₁, hq₂]
    exact negOne_pow_tsub_mul_negOne_pow_tsub
      (Fin.le_last p₁) (Fin.le_last p₂)
  have hC : C * C = 1 := by
    dsimp only [C]
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hτ : Equiv.Perm.sign τ = C * Equiv.Perm.sign σ := by
    calc
      Equiv.Perm.sign τ = Equiv.Perm.sign ρ := hρτ.symm
      _ = Equiv.Perm.sign q₂ * Equiv.Perm.sign σ * Equiv.Perm.sign q₁ := hρ
      _ = (Equiv.Perm.sign q₁ * Equiv.Perm.sign q₂) *
          Equiv.Perm.sign σ := by ac_rfl
      _ = C * Equiv.Perm.sign σ := by rw [hfactor]
  change Equiv.Perm.sign σ = Equiv.Perm.sign τ * _
  have hp₁ : (p₁ : ℕ) = incidenceIndex r₁ s v :=
    orderPositionOfCard_eq_incidenceIndex r₁ s hs v hv
  have hp₂ : (p₂ : ℕ) = incidenceIndex r₂ s v :=
    orderPositionOfCard_eq_incidenceIndex r₂ s hs v hv
  rw [← hp₁, ← hp₂]
  change Equiv.Perm.sign σ = Equiv.Perm.sign τ * C
  calc
    Equiv.Perm.sign σ = 1 * Equiv.Perm.sign σ := (one_mul _).symm
    _ = (C * C) * Equiv.Perm.sign σ := by rw [hC]
    _ = C * (C * Equiv.Perm.sign σ) := by ac_rfl
    _ = C * Equiv.Perm.sign τ := by rw [hτ]
    _ = Equiv.Perm.sign τ * C := mul_comm _ _

theorem incidenceSign_mul_self
    (r : LinearOrder E) (s : Finset E) (v : E) :
    incidenceSign r s v * incidenceSign r s v = 1 := by
  unfold incidenceSign
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

open Classical in
private theorem orderChangeSignOfCard_erase
    (r₁ r₂ : LinearOrder E) (s : Finset E) {n : ℕ} (hs : s.card = n + 1)
    (v : E) (hv : v ∈ s)
    (ht : (@Finset.erase E (Classical.decEq E) s v).card = n) :
    orderChangeSignOfCard r₁ r₂ s hs =
      orderChangeSignOfCard r₁ r₂
          (@Finset.erase E (Classical.decEq E) s v) ht *
        incidenceSign r₁ s v * incidenceSign r₂ s v := by
  have h := congrArg (fun z : ℤˣ => (z : ℤ))
    (sign_orderChangePermutationOfCard_erase r₁ r₂ s hs v hv ht)
  simpa only [orderChangeSignOfCard, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, pow_add, incidenceSign, mul_assoc] using h

open Classical in
theorem orderChangeSign_mul_simplexBoundaryCoefficient
    (r₁ r₂ : LinearOrder E) {s t : Finset E}
    (hts : t ⊆ s) (hcard : t.card + 1 = s.card) :
    orderChangeSign r₁ r₂ s * simplexBoundaryCoefficient r₂ s t =
      orderChangeSign r₁ r₂ t * simplexBoundaryCoefficient r₁ s t := by
  obtain ⟨v, hvt, hsv⟩ := Finset.exists_eq_insert_iff.mpr ⟨hts, hcard⟩
  have hv : v ∈ s := hsv ▸ Finset.mem_insert_self v t
  have erase_eq (d : DecidableEq E) : @Finset.erase E d s v = t := by
    rw [← hsv]
    ext w
    simp only [Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hwv, hwv' | hwt⟩
      · exact False.elim (hwv hwv')
      · exact hwt
    · intro hwt
      exact ⟨fun hwv => hvt (hwv ▸ hwt), Or.inr hwt⟩
  have herase : @Finset.erase E (Classical.decEq E) s v = t := erase_eq _
  have hs : s.card = t.card + 1 := hcard.symm
  have ht : (@Finset.erase E (Classical.decEq E) s v).card = t.card := by
    rw [herase]
  have hsign := orderChangeSignOfCard_erase r₁ r₂ s hs v hv ht
  rw [orderChangeSignOfCard_eq, orderChangeSignOfCard_eq, herase] at hsign
  have hcoefficient₁ : simplexBoundaryCoefficient r₁ s t = incidenceSign r₁ s v := by
    calc
      simplexBoundaryCoefficient r₁ s t =
          simplexBoundaryCoefficient r₁ s (@Finset.erase E r₁.toDecidableEq s v) := by
        rw [erase_eq r₁.toDecidableEq]
      _ = incidenceSign r₁ s v := simplexBoundaryCoefficient_erase r₁ hv
  have hcoefficient₂ : simplexBoundaryCoefficient r₂ s t = incidenceSign r₂ s v := by
    calc
      simplexBoundaryCoefficient r₂ s t =
          simplexBoundaryCoefficient r₂ s (@Finset.erase E r₂.toDecidableEq s v) := by
        rw [erase_eq r₂.toDecidableEq]
      _ = incidenceSign r₂ s v := simplexBoundaryCoefficient_erase r₂ hv
  rw [hcoefficient₁, hcoefficient₂, hsign]
  calc
    (orderChangeSign r₁ r₂ t * incidenceSign r₁ s v *
          incidenceSign r₂ s v) * incidenceSign r₂ s v =
        orderChangeSign r₁ r₂ t * incidenceSign r₁ s v *
          (incidenceSign r₂ s v * incidenceSign r₂ s v) := by ring
    _ = orderChangeSign r₁ r₂ t * incidenceSign r₁ s v := by
      rw [incidenceSign_mul_self, mul_one]

theorem orderChangeSign_eq_one_or_neg_one
    (r₁ r₂ : LinearOrder E) (s : Finset E) :
    orderChangeSign r₁ r₂ s = 1 ∨ orderChangeSign r₁ r₂ s = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign (orderChangePermutation r₁ r₂ s)) with h | h
  · left
    unfold orderChangeSign
    rw [h]
    rfl
  · right
    unfold orderChangeSign
    rw [h]
    rfl

open Classical in
noncomputable def CoherentOrientation.changeVertexOrder
    [AddCommGroup E] [Module ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (o : CoherentOrientation n K) (r : LinearOrder E) :
    CoherentOrientation n K where
  vertexOrder := r
  sign := fun s => o.sign s * orderChangeSign o.vertexOrder r s
  sign_top := by
    intro s hs hscard
    rcases o.sign_top s hs hscard with hs | hs <;>
      rcases orderChangeSign_eq_one_or_neg_one o.vertexOrder r s with hc | hc <;>
        simp [hs, hc]
  coherent := by
    intro t ht htcard hnotone
    rw [orientedBoundary_eq_sum_faceCofaces]
    have hold := o.coherent t ht htcard hnotone
    rw [orientedBoundary_eq_sum_faceCofaces] at hold
    calc
      (∑ s ∈ faceCofaces K t (n + 1),
          (o.sign s * orderChangeSign o.vertexOrder r s) *
            simplexBoundaryCoefficient r s t) =
          ∑ s ∈ faceCofaces K t (n + 1),
            orderChangeSign o.vertexOrder r t *
              (o.sign s * simplexBoundaryCoefficient o.vertexOrder s t) := by
        apply Finset.sum_congr rfl
        intro s hs
        obtain ⟨hsK, hscard, hts⟩ := (mem_faceCofaces K).mp hs
        rw [mul_assoc, orderChangeSign_mul_simplexBoundaryCoefficient
          o.vertexOrder r hts (by omega)]
        ring
      _ = orderChangeSign o.vertexOrder r t *
          (∑ s ∈ faceCofaces K t (n + 1),
            o.sign s * simplexBoundaryCoefficient o.vertexOrder s t) := by
        rw [Finset.mul_sum]
      _ = 0 := by rw [hold, mul_zero]

open Classical in
@[instance_reducible]
noncomputable def barycentricOrientationVertexOrder
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (r : LinearOrder E) : LinearOrder E := by
  let _ := r
  exact LinearOrder.lift' (relativeOrientationVertexKey K ⊥)
    (relativeOrientationVertexKey_injective K ⊥)

open Classical in
theorem barycentricOrientationVertexOrder_centroid_lt_centroid
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (r : LinearOrder E)
    {s t : Finset E} (hsK : s ∈ K.faces) (htK : t ∈ K.faces)
    (hst : t.card < s.card) :
    let _ := barycentricOrientationVertexOrder K r
    s.centroid ℝ id < t.centroid ℝ id := by
  let _ : LinearOrder E := r
  have hsbot : s ∉ (⊥ : Geometry.SimplicialComplex ℝ E).faces := by
    change s ∉ (∅ : Set (Finset E))
    intro h
    exact h
  have htbot : t ∉ (⊥ : Geometry.SimplicialComplex ℝ E).faces := by
    change t ∉ (∅ : Set (Finset E))
    intro h
    exact h
  change relativeOrientationVertexKey K ⊥ (s.centroid ℝ id) <
    relativeOrientationVertexKey K ⊥ (t.centroid ℝ id)
  rw [relativeOrientationVertexKey, relativeOrientationVertexKey,
    relativeVertexRank_centroid K ⊥ hsK hsbot,
    relativeVertexRank_centroid K ⊥ htK htbot]
  change toLex (Sum.inl (toLex (OrderDual.toDual s.card, s.centroid ℝ id))) <
    toLex (Sum.inl (toLex (OrderDual.toDual t.card, t.centroid ℝ id)))
  rw [Sum.Lex.inl_lt_inl_iff, Prod.Lex.toLex_lt_toLex]
  exact Or.inl hst

open Classical in
theorem barycentricOrientationIncidenceIndex_centroid
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (r : LinearOrder E)
    {m : Finset E} {d : Finset (Finset E)}
    (h : IsFlag K (insert m d)) (hm : m ∉ d) :
    incidenceIndex (barycentricOrientationVertexOrder K r)
      ((insert m d).image (fun s => s.centroid ℝ id)) (m.centroid ℝ id) =
      (d.filter fun s => m.card < s.card).card := by
  have hmFlag : m ∈ insert m d := Finset.mem_insert_self m d
  have hmK : m ∈ K.faces := h.coe_subset_faces (Finset.mem_coe.mpr hmFlag)
  have hfilter :
      ((insert m d).image (fun s => s.centroid ℝ id)).filter
          (fun x => @LT.lt E (barycentricOrientationVertexOrder K r).toLT
            x (m.centroid ℝ id)) =
        (d.filter fun s => m.card < s.card).image (fun s => s.centroid ℝ id) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxmem, hxlt⟩ := Finset.mem_filter.mp hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hxmem
      rcases Finset.mem_insert.mp hs with hsm | hsd
      · subst s
        let _ : LinearOrder E := barycentricOrientationVertexOrder K r
        exact False.elim (lt_irrefl _ hxlt)
      · have hsK : s ∈ K.faces := h.coe_subset_faces
          (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hsd))
        have hcard : m.card < s.card := by
          by_contra hnot
          have hle : s.card ≤ m.card := Nat.le_of_not_gt hnot
          have hne : s.card ≠ m.card := by
            intro heq
            rcases h.subset_or_subset
              (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hsd))
              (Finset.mem_coe.mpr hmFlag) with hsm | hms
            · exact hm ((Finset.eq_of_subset_of_card_le hsm heq.ge).symm ▸ hsd)
            · exact hm (Finset.eq_of_subset_of_card_le hms heq.le ▸ hsd)
          have hslt : s.card < m.card := lt_of_le_of_ne hle hne
          have hreverse := barycentricOrientationVertexOrder_centroid_lt_centroid
            K r hmK hsK hslt
          let _ : LinearOrder E := barycentricOrientationVertexOrder K r
          exact (not_lt_of_ge hxlt.le)
            hreverse
        exact Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨hsd, hcard⟩, rfl⟩
    · intro hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hsd, hcard⟩ := Finset.mem_filter.mp hs
      have hsK : s ∈ K.faces := h.coe_subset_faces
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hsd))
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem hsd),
        barycentricOrientationVertexOrder_centroid_lt_centroid
          K r hsK hmK hcard⟩
  unfold incidenceIndex
  change (((insert m d).image (fun s => s.centroid ℝ id)).filter
    (fun x => @LT.lt E (barycentricOrientationVertexOrder K r).toLT
      x (m.centroid ℝ id))).card = _
  calc
    _ = ((d.filter fun s => m.card < s.card).image
        (fun s => s.centroid ℝ id)).card := congrArg Finset.card hfilter
    _ = (d.filter fun s => m.card < s.card).card :=
      Finset.card_image_of_injOn
        ((injOn_faces_of_mem_openSimplex K
          (centroid_mem_openSimplex_of_mem_faces K)).mono
            (fun s hs => h.coe_subset_faces
              (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
                (Finset.mem_filter.mp (Finset.mem_coe.mp hs)).1))))

noncomputable def adjacentBarycentricCommonFace
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : LinearOrder E) (T : Finset E) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) : Finset E :=
  (adjacentFaceCommonFlag r T hT σ i).image (fun s => s.centroid ℝ id)

open Classical in
theorem adjacentFaceCommonFlag_subset_permutedFaceFlag
    (r : LinearOrder E) (T : Finset E) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    adjacentFaceCommonFlag r T hT σ i ⊆ permutedFaceFlag r T hT σ := by
  intro s hs
  rw [(permutedFaceFlag_adjacent_decomposition r T hT σ i).1]
  exact Finset.mem_insert_of_mem hs

open Classical in
theorem adjacentBarycentricCommonFace_card
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (r : LinearOrder E)
    {T : Finset E} (hTK : T ∈ K.faces) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    (adjacentBarycentricCommonFace r T hT σ i).card = n + 1 := by
  unfold adjacentBarycentricCommonFace
  rw [Finset.card_image_of_injOn]
  · exact adjacentFaceCommonFlag_card r T hT σ i
  · exact (injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K)).mono (fun s hs =>
        (permutedFaceFlag_isFlag K r hTK hT σ).coe_subset_faces
          (Finset.mem_coe.mpr
            (adjacentFaceCommonFlag_subset_permutedFaceFlag r T hT σ i
              (Finset.mem_coe.mp hs))))

open Classical in
theorem adjacentBarycentricCommonFace_mem
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (r : LinearOrder E)
    {T : Finset E} (hTK : T ∈ K.faces) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    adjacentBarycentricCommonFace r T hT σ i ∈
      (barycentricSubdivision K).faces := by
  apply (barycentricSubdivision K).down_closed
    (permutedBarycentricFace_mem K r hTK hT σ)
  · exact Finset.image_mono (fun s => s.centroid ℝ id)
      (adjacentFaceCommonFlag_subset_permutedFaceFlag r T hT σ i)
  · rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have hcard := adjacentBarycentricCommonFace_card K r hTK hT σ i
    rw [hzero, Finset.card_empty] at hcard
    omega

open Classical in
theorem permutedBarycentricFace_adjacent_decomposition
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : LinearOrder E) (T : Finset E) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    let D := adjacentBarycentricCommonFace r T hT σ i
    permutedBarycentricFace r T hT σ =
        insert ((permutedFacePrefix r T hT σ i.castSucc).centroid ℝ id) D ∧
      permutedBarycentricFace r T hT (adjacentPermutedFaceSwap σ i) =
        insert ((permutedFacePrefix r T hT (adjacentPermutedFaceSwap σ i)
          i.castSucc).centroid ℝ id) D := by
  obtain ⟨h₁, h₂⟩ := permutedFaceFlag_adjacent_decomposition r T hT σ i
  constructor
  · unfold permutedBarycentricFace adjacentBarycentricCommonFace adjacentFaceCommonFlag
    rw [h₁, Finset.image_insert]
  · unfold permutedBarycentricFace adjacentBarycentricCommonFace adjacentFaceCommonFlag
    rw [h₂, Finset.image_insert]

open Classical in
theorem permutedFacePrefix_centroid_not_mem_adjacentBarycentricCommonFace
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (r : LinearOrder E)
    {T : Finset E} (hTK : T ∈ K.faces) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    (permutedFacePrefix r T hT σ i.castSucc).centroid ℝ id ∉
      adjacentBarycentricCommonFace r T hT σ i := by
  intro hm
  obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hm
  have hflag := permutedFaceFlag_isFlag K r hTK hT σ
  have hpMem : permutedFacePrefix r T hT σ i.castSucc ∈
      permutedFaceFlag r T hT σ :=
    Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, rfl⟩
  have hsMem := adjacentFaceCommonFlag_subset_permutedFaceFlag r T hT σ i hs
  have hpK := hflag.coe_subset_faces (Finset.mem_coe.mpr hpMem)
  have hsK := hflag.coe_subset_faces (Finset.mem_coe.mpr hsMem)
  have hps := injOn_faces_of_mem_openSimplex K
    (centroid_mem_openSimplex_of_mem_faces K) hpK hsK heq.symm
  exact permutedFacePrefix_not_mem_adjacentFaceCommonFlag r T hT σ i (hps ▸ hs)

open Classical in
theorem adjacentPermutedFacePrefix_centroid_not_mem_adjacentBarycentricCommonFace
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (r : LinearOrder E)
    {T : Finset E} (hTK : T ∈ K.faces) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    (permutedFacePrefix r T hT (adjacentPermutedFaceSwap σ i) i.castSucc).centroid ℝ id ∉
      adjacentBarycentricCommonFace r T hT σ i := by
  intro hm
  obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hm
  have hflag := permutedFaceFlag_isFlag K r hTK hT (adjacentPermutedFaceSwap σ i)
  have hpMem : permutedFacePrefix r T hT (adjacentPermutedFaceSwap σ i) i.castSucc ∈
      permutedFaceFlag r T hT (adjacentPermutedFaceSwap σ i) :=
    Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, rfl⟩
  have hsMem : s ∈ permutedFaceFlag r T hT (adjacentPermutedFaceSwap σ i) := by
    rw [(permutedFaceFlag_adjacent_decomposition r T hT σ i).2]
    exact Finset.mem_insert_of_mem hs
  have hpK := hflag.coe_subset_faces (Finset.mem_coe.mpr hpMem)
  have hsK := hflag.coe_subset_faces (Finset.mem_coe.mpr hsMem)
  have hps := injOn_faces_of_mem_openSimplex K
    (centroid_mem_openSimplex_of_mem_faces K) hpK hsK heq.symm
  exact adjacentPermutedFacePrefix_not_mem_adjacentFaceCommonFlag
    r T hT σ i (hps ▸ hs)

open Classical in
theorem permutedBarycentricFace_ne_adjacentPermutedFaceSwap
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (r : LinearOrder E)
    {T : Finset E} (hTK : T ∈ K.faces) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    permutedBarycentricFace r T hT σ ≠
      permutedBarycentricFace r T hT (adjacentPermutedFaceSwap σ i) := by
  intro heq
  let A := permutedFacePrefix r T hT σ i.castSucc
  let B := permutedFacePrefix r T hT (adjacentPermutedFaceSwap σ i) i.castSucc
  let D := adjacentBarycentricCommonFace r T hT σ i
  have hdecomp := permutedBarycentricFace_adjacent_decomposition r T hT σ i
  have hA : A.centroid ℝ id ∈ insert (A.centroid ℝ id) D := Finset.mem_insert_self _ _
  rw [← hdecomp.1, heq, hdecomp.2] at hA
  rcases Finset.mem_insert.mp hA with hAB | hAD
  · have hflag := permutedFaceFlag_isFlag K r hTK hT σ
    have hflag' := permutedFaceFlag_isFlag K r hTK hT (adjacentPermutedFaceSwap σ i)
    have hAK : A ∈ K.faces := hflag.coe_subset_faces (Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, rfl⟩))
    have hBK : B ∈ K.faces := hflag'.coe_subset_faces (Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, rfl⟩))
    have hAB' := injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K) hAK hBK hAB
    exact adjacentFacePrefixes_ne r T hT σ i hAB'
  · exact permutedFacePrefix_centroid_not_mem_adjacentBarycentricCommonFace
      K r hTK hT σ i hAD

open Classical in
theorem simplexBoundaryCoefficient_permutedBarycentricFace_adjacent
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (r : LinearOrder E)
    {T : Finset E} (hTK : T ∈ K.faces) {n : ℕ} (hT : T.card = n + 2)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    simplexBoundaryCoefficient (barycentricOrientationVertexOrder K r)
        (permutedBarycentricFace r T hT σ)
        (adjacentBarycentricCommonFace r T hT σ i) =
      simplexBoundaryCoefficient (barycentricOrientationVertexOrder K r)
        (permutedBarycentricFace r T hT (adjacentPermutedFaceSwap σ i))
        (adjacentBarycentricCommonFace r T hT σ i) := by
  let A := permutedFacePrefix r T hT σ i.castSucc
  let B := permutedFacePrefix r T hT (adjacentPermutedFaceSwap σ i) i.castSucc
  let d := adjacentFaceCommonFlag r T hT σ i
  let D := adjacentBarycentricCommonFace r T hT σ i
  have hdecomp := permutedBarycentricFace_adjacent_decomposition r T hT σ i
  have hAnot : A.centroid ℝ id ∉ D :=
    permutedFacePrefix_centroid_not_mem_adjacentBarycentricCommonFace
      K r hTK hT σ i
  have hBnot : B.centroid ℝ id ∉ D :=
    adjacentPermutedFacePrefix_centroid_not_mem_adjacentBarycentricCommonFace
      K r hTK hT σ i
  have hflagEqA : permutedFaceFlag r T hT σ = insert A d := by
    simpa only [A, d, adjacentFaceCommonFlag] using
      (permutedFaceFlag_adjacent_decomposition r T hT σ i).1
  have hflagEqB : permutedFaceFlag r T hT (adjacentPermutedFaceSwap σ i) =
      insert B d := by
    simpa only [B, d, adjacentFaceCommonFlag] using
      (permutedFaceFlag_adjacent_decomposition r T hT σ i).2
  have hflagA : IsFlag K (insert A d) := by
    rw [← hflagEqA]
    exact permutedFaceFlag_isFlag K r hTK hT σ
  have hflagB : IsFlag K (insert B d) := by
    rw [← hflagEqB]
    exact permutedFaceFlag_isFlag K r hTK hT (adjacentPermutedFaceSwap σ i)
  have hAnotd : A ∉ d := permutedFacePrefix_not_mem_adjacentFaceCommonFlag r T hT σ i
  have hBnotd : B ∉ d :=
    adjacentPermutedFacePrefix_not_mem_adjacentFaceCommonFlag r T hT σ i
  have hindexA := barycentricOrientationIncidenceIndex_centroid K r hflagA hAnotd
  have hindexB := barycentricOrientationIncidenceIndex_centroid K r hflagB hBnotd
  have himageA : (insert A d).image (fun s => s.centroid ℝ id) =
      insert (A.centroid ℝ id) D := by
    rw [Finset.image_insert]
    rfl
  have himageB : (insert B d).image (fun s => s.centroid ℝ id) =
      insert (B.centroid ℝ id) D := by
    rw [Finset.image_insert]
    rfl
  rw [himageA] at hindexA
  rw [himageB] at hindexB
  have hABcard : A.card = B.card := by
    rw [permutedFacePrefix_card r T hT σ i.castSucc,
      permutedFacePrefix_card r T hT (adjacentPermutedFaceSwap σ i) i.castSucc]
  have hfilter : (d.filter fun s => A.card < s.card).card =
      (d.filter fun s => B.card < s.card).card := by rw [hABcard]
  rw [hdecomp.1, hdecomp.2]
  change simplexBoundaryCoefficient (barycentricOrientationVertexOrder K r)
      (insert (A.centroid ℝ id) D) D =
    simplexBoundaryCoefficient (barycentricOrientationVertexOrder K r)
      (insert (B.centroid ℝ id) D) D
  have hcoefficientA := simplexBoundaryCoefficient_insert
    (barycentricOrientationVertexOrder K r) hAnot
  have hcoefficientB := simplexBoundaryCoefficient_insert
    (barycentricOrientationVertexOrder K r) hBnot
  have hdec : (barycentricOrientationVertexOrder K r).toDecidableEq =
      r.toDecidableEq := Subsingleton.elim _ _
  rw [hdec] at hcoefficientA hcoefficientB
  rw [hcoefficientA, hcoefficientB]
  unfold incidenceSign
  rw [hindexA, hindexB, hfilter]

open Classical in
theorem barycentricFlagNormalizedSign_adjacent
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (r : LinearOrder E)
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] [Finite (barycentricSubdivision K).faces]
    (o : CoherentOrientation (n + 1) (barycentricSubdivision K))
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {T : Finset E} (hTK : T ∈ K.faces)
    (hT : T.card = n + 2) (σ : Equiv.Perm (Fin (n + 2)))
    (i : Fin (n + 1)) :
    barycentricFlagNormalizedSign r
        (o.changeVertexOrder (barycentricOrientationVertexOrder K r)) hT σ =
      barycentricFlagNormalizedSign r
        (o.changeVertexOrder (barycentricOrientationVertexOrder K r)) hT
          (adjacentPermutedFaceSwap σ i) := by
  let F := permutedBarycentricFace r T hT σ
  let G := permutedBarycentricFace r T hT (adjacentPermutedFaceSwap σ i)
  let D := adjacentBarycentricCommonFace r T hT σ i
  let oB := o.changeVertexOrder (barycentricOrientationVertexOrder K r)
  have hF : F ∈ (barycentricSubdivision K).faces :=
    permutedBarycentricFace_mem K r hTK hT σ
  have hG : G ∈ (barycentricSubdivision K).faces :=
    permutedBarycentricFace_mem K r hTK hT (adjacentPermutedFaceSwap σ i)
  have hD : D ∈ (barycentricSubdivision K).faces :=
    adjacentBarycentricCommonFace_mem K r hTK hT σ i
  have hFcard : F.card = n + 2 := permutedBarycentricFace_card K r hTK hT σ
  have hGcard : G.card = n + 2 :=
    permutedBarycentricFace_card K r hTK hT (adjacentPermutedFaceSwap σ i)
  have hDcard : D.card = n + 1 := adjacentBarycentricCommonFace_card K r hTK hT σ i
  have hdecomp := permutedBarycentricFace_adjacent_decomposition r T hT σ i
  have hDF : D ⊆ F := by
    change D ⊆ permutedBarycentricFace r T hT σ
    rw [hdecomp.1]
    exact Finset.subset_insert _ _
  have hDG : D ⊆ G := by
    change D ⊆ permutedBarycentricFace r T hT (adjacentPermutedFaceSwap σ i)
    rw [hdecomp.2]
    exact Finset.subset_insert _ _
  have hFco : F ∈ faceCofaces (barycentricSubdivision K) D (n + 2) :=
    (mem_faceCofaces (barycentricSubdivision K)).mpr ⟨hF, hFcard, hDF⟩
  have hGco : G ∈ faceCofaces (barycentricSubdivision K) D (n + 2) :=
    (mem_faceCofaces (barycentricSubdivision K)).mpr ⟨hG, hGcard, hDG⟩
  have hFG : F ≠ G :=
    permutedBarycentricFace_ne_adjacentPermutedFaceSwap K r hTK hT σ i
  have hnotone : (faceCofaces (barycentricSubdivision K) D (n + 2)).card ≠ 1 := by
    intro hone
    obtain ⟨Q, hQ⟩ := Finset.card_eq_one.mp hone
    have hFQ : F = Q := by simpa [hQ] using hFco
    have hGQ : G = Q := by simpa [hQ] using hGco
    exact hFG (hFQ.trans hGQ.symm)
  have hBary :
      @barycentricSubdivision E _ _ (Classical.decEq E) K =
        @barycentricSubdivision E _ _ r.toDecidableEq K :=
    congrArg (fun d : DecidableEq E => @barycentricSubdivision E _ _ d K)
      (Subsingleton.elim _ _)
  have hR : IsCombinatorialManifoldWithBoundary (n + 1) (barycentricSubdivision K) :=
    by
      have hR' := hK.barycentricSubdivision
      rw [hBary] at hR'
      exact hR'
  have htwo : (faceCofaces (barycentricSubdivision K) D (n + 2)).card = 2 :=
    (hR.card_faceCofaces_eq_one_or_two (barycentricSubdivision K) hD hDcard).resolve_left hnotone
  have hpairSub : ({F, G} : Finset (Finset E)) ⊆
      faceCofaces (barycentricSubdivision K) D (n + 2) := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hFco, hGco⟩
  have hcofaces : faceCofaces (barycentricSubdivision K) D (n + 2) = {F, G} := by
    apply (Finset.eq_of_subset_of_card_le hpairSub ?_).symm
    rw [htwo]
    simp [hFG]
  have hnotone' :
      (faceCofaces (barycentricSubdivision K) D ((n + 1) + 1)).card ≠ 1 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hnotone
  have hzero := oB.coherent D hD hDcard hnotone'
  rw [orientedBoundary_eq_sum_faceCofaces,
    show (n + 1) + 1 = n + 2 by omega, hcofaces] at hzero
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton,
    hFG, not_false_eq_true] at hzero
  have hcoefficient : simplexBoundaryCoefficient oB.vertexOrder F D =
      simplexBoundaryCoefficient oB.vertexOrder G D := by
    exact simplexBoundaryCoefficient_permutedBarycentricFace_adjacent
      K r hTK hT σ i
  have hcoefficientNe : simplexBoundaryCoefficient oB.vertexOrder F D ≠ 0 := by
    rcases simplexBoundaryCoefficient_eq_one_or_neg_one oB.vertexOrder hDF (by omega) with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  have hproduct :
      (oB.sign F + oB.sign G) * simplexBoundaryCoefficient oB.vertexOrder F D = 0 := by
    rw [← hcoefficient] at hzero
    rw [add_mul]
    exact hzero
  have hsum : oB.sign F + oB.sign G = 0 :=
    (mul_eq_zero.mp hproduct).resolve_right hcoefficientNe
  have hsign : oB.sign G = -oB.sign F := by omega
  have hswap : i.castSucc ≠ i.succ := ne_of_lt i.castSucc_lt_succ
  have hpermUnits : Equiv.Perm.sign (adjacentPermutedFaceSwap σ i) =
      -Equiv.Perm.sign σ := by
    unfold adjacentPermutedFaceSwap
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hswap]
    simp
  have hperm := congrArg (fun u : ℤˣ => (u : ℤ)) hpermUnits
  have hpermInt : (Equiv.Perm.sign (adjacentPermutedFaceSwap σ i) : ℤ) =
      -(Equiv.Perm.sign σ : ℤ) := by
    simpa only [Units.val_neg] using hperm
  unfold barycentricFlagNormalizedSign
  change oB.sign F * (Equiv.Perm.sign σ : ℤ) =
    oB.sign G * (Equiv.Perm.sign (adjacentPermutedFaceSwap σ i) : ℤ)
  rw [hsign, hpermInt]
  ring

open Classical in
theorem barycentricFlagNormalizedSign_eq
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (r : LinearOrder E)
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] [Finite (barycentricSubdivision K).faces]
    (o : CoherentOrientation (n + 1) (barycentricSubdivision K))
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {T : Finset E} (hTK : T ∈ K.faces) (hT : T.card = n + 2)
    (σ τ : Equiv.Perm (Fin (n + 2))) :
    barycentricFlagNormalizedSign r
        (o.changeVertexOrder (barycentricOrientationVertexOrder K r)) hT σ =
      barycentricFlagNormalizedSign r
        (o.changeVertexOrder (barycentricOrientationVertexOrder K r)) hT τ := by
  let oB := o.changeVertexOrder (barycentricOrientationVertexOrder K r)
  let value : Equiv.Perm (Fin (n + 2)) → ℤ :=
    fun ρ => barycentricFlagNormalizedSign r oB hT ρ
  let P : Equiv.Perm (Fin (n + 2)) → Prop :=
    fun q => ∀ ρ, value (ρ * q) = value ρ
  have hgenerator : ∀ q ∈ Set.range
      (fun i : Fin (n + 1) => Equiv.swap i.castSucc i.succ), P q := by
    intro q hq
    obtain ⟨i, rfl⟩ := hq
    intro ρ
    change barycentricFlagNormalizedSign r oB hT
        (adjacentPermutedFaceSwap ρ i) =
      barycentricFlagNormalizedSign r oB hT ρ
    exact (barycentricFlagNormalizedSign_adjacent r o hK hTK hT ρ i).symm
  have hone : P 1 := by
    intro ρ
    rw [mul_one]
  have hmul : ∀ a b, P a → P b → P (a * b) := by
    intro a b ha hb ρ
    rw [← mul_assoc, hb (ρ * a), ha ρ]
  have hclosure : Submonoid.closure (Set.range
      (fun i : Fin (n + 1) => Equiv.swap i.castSucc i.succ)) = ⊤ := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      Equiv.Perm.mclosure_swap_castSucc_succ (n + 1)
  have hall (q : Equiv.Perm (Fin (n + 2))) : value q = value 1 := by
    have hq : q ∈ Submonoid.closure (Set.range
        (fun i : Fin (n + 1) => Equiv.swap i.castSucc i.succ)) := by
      rw [hclosure]
      exact Submonoid.mem_top q
    have hP : P q := Submonoid.closure_induction hgenerator hone
      (fun x y _ _ hx hy => hmul x y hx hy) hq
    simpa only [one_mul] using hP 1
  exact (hall σ).trans (hall τ).symm

open Classical in
theorem permutedFacePrefix_cycleIcc_orderPosition_castSucc
    (r : LinearOrder E) (s t : Finset E) {n : ℕ}
    (hs : s.card = n + 2) {v : E} (hv : v ∈ s)
    (herase : @Finset.erase E (Classical.decEq E) s v = t)
    (ht : t.card = n + 1) (k : Fin (n + 1)) :
    permutedFacePrefix r s hs
        (Fin.cycleIcc (orderPositionOfCard r s hs v hv) (Fin.last (n + 1)))
        k.castSucc =
      permutedFacePrefix r t ht 1 k := by
  subst t
  let q := Fin.cycleIcc (orderPositionOfCard r s hs v hv) (Fin.last (n + 1))
  have hvalue (j : Fin (n + 1)) :
      orderValueOfCard r s hs (q j.castSucc) =
        orderValueOfCard r (@Finset.erase E (Classical.decEq E) s v) ht j := by
    exact (orderValueOfCard_erase_apply r s hs hv ht j).symm
  unfold permutedFacePrefix
  simp only [Equiv.Perm.one_apply]
  change (Finset.Iic k.castSucc).image (fun i => orderValueOfCard r s hs (q i)) =
    (Finset.Iic k).image (fun i =>
      orderValueOfCard r (@Finset.erase E (Classical.decEq E) s v) ht i)
  rw [← Fin.finsetImage_castSucc_Iic k, Finset.image_image]
  apply Finset.image_congr
  intro j hj
  exact hvalue j

open Classical in
theorem permutedFacePrefix_last_eq
    (r : LinearOrder E) (s : Finset E) {N : ℕ} (hs : s.card = N + 1)
    (σ : Equiv.Perm (Fin (N + 1))) :
    permutedFacePrefix r s hs σ (Fin.last N) = s := by
  apply Finset.eq_of_subset_of_card_le
  · exact permutedFacePrefix_subset r s hs σ (Fin.last N)
  · rw [permutedFacePrefix_card, hs]
    simp

open Classical in
theorem permutedFaceFlag_cycleIcc_orderPosition
    (r : LinearOrder E) (s t : Finset E) {n : ℕ}
    (hs : s.card = n + 2) {v : E} (hv : v ∈ s)
    (herase : @Finset.erase E (Classical.decEq E) s v = t)
    (ht : t.card = n + 1) :
    let q := Fin.cycleIcc (orderPositionOfCard r s hs v hv) (Fin.last (n + 1))
    permutedFaceFlag r s hs q = insert s (permutedFaceFlag r t ht 1) := by
  intro q
  unfold permutedFaceFlag
  let f := permutedFacePrefix r s hs q
  calc
    Finset.univ.image f =
        (insert (Fin.last (n + 1))
          (Finset.univ.image (Fin.last (n + 1)).succAbove)).image f := by
      rw [Fin.image_succAbove_univ]
      simp
    _ = insert (f (Fin.last (n + 1)))
        (Finset.univ.image (fun k : Fin (n + 1) => f k.castSucc)) := by
      rw [Finset.image_insert, Finset.image_image]
      congr 2
      funext k
      simp only [Function.comp_apply, Fin.succAbove_last_apply]
    _ = insert s (Finset.univ.image
        (permutedFacePrefix r t ht (1 : Equiv.Perm (Fin (n + 1))))) := by
      rw [show f (Fin.last (n + 1)) = s by
        exact permutedFacePrefix_last_eq r s hs q]
      congr 1
      apply Finset.image_congr
      intro k hk
      exact permutedFacePrefix_cycleIcc_orderPosition_castSucc
        r s t hs hv herase ht k

open Classical in
theorem permutedBarycentricFace_cycleIcc_orderPosition
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : LinearOrder E) (s t : Finset E) {n : ℕ}
    (hs : s.card = n + 2) {v : E} (hv : v ∈ s)
    (herase : @Finset.erase E (Classical.decEq E) s v = t)
    (ht : t.card = n + 1) :
    let q := Fin.cycleIcc (orderPositionOfCard r s hs v hv) (Fin.last (n + 1))
    permutedBarycentricFace r s hs q =
      insert (s.centroid ℝ id) (permutedBarycentricFace r t ht 1) := by
  intro q
  unfold permutedBarycentricFace
  rw [permutedFaceFlag_cycleIcc_orderPosition r s t hs hv herase ht,
    Finset.image_insert]

open Classical in
theorem simplexBoundaryCoefficient_permutedBarycentricFace_cycleIcc_eq_one
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (r : LinearOrder E)
    {s t : Finset E} {n : ℕ} (hsK : s ∈ K.faces) (htK : t ∈ K.faces)
    (hs : s.card = n + 2) {v : E} (hv : v ∈ s)
    (herase : @Finset.erase E (Classical.decEq E) s v = t)
    (ht : t.card = n + 1) :
    let q := Fin.cycleIcc (orderPositionOfCard r s hs v hv) (Fin.last (n + 1))
    simplexBoundaryCoefficient (barycentricOrientationVertexOrder K r)
        (permutedBarycentricFace r s hs q)
        (permutedBarycentricFace r t ht 1) = 1 := by
  intro q
  let d := permutedFaceFlag r t ht (1 : Equiv.Perm (Fin (n + 1)))
  let D := permutedBarycentricFace r t ht (1 : Equiv.Perm (Fin (n + 1)))
  have hface : permutedBarycentricFace r s hs q = insert (s.centroid ℝ id) D :=
    permutedBarycentricFace_cycleIcc_orderPosition r s t hs hv herase ht
  have hDcard : D.card = n + 1 := permutedBarycentricFace_card K r htK ht 1
  have hfaceCard : (permutedBarycentricFace r s hs q).card = n + 2 :=
    permutedBarycentricFace_card K r hsK hs q
  have hcentroidNot : s.centroid ℝ id ∉ D := by
    intro hmem
    rw [hface, Finset.card_insert_of_mem hmem, hDcard] at hfaceCard
    omega
  have hflag : IsFlag K (insert s d) := by
    have hflag' := permutedFaceFlag_isFlag K r hsK hs q
    rw [permutedFaceFlag_cycleIcc_orderPosition r s t hs hv herase ht] at hflag'
    exact hflag'
  have hsnot : s ∉ d := by
    intro hsd
    exact hcentroidNot (Finset.mem_image_of_mem (fun u => u.centroid ℝ id) hsd)
  have hindex := barycentricOrientationIncidenceIndex_centroid K r hflag hsnot
  have himage : (insert s d).image (fun u => u.centroid ℝ id) =
      insert (s.centroid ℝ id) D := by
    rw [Finset.image_insert]
    rfl
  rw [himage] at hindex
  have hfilter : (d.filter fun u => s.card < u.card) = ∅ := by
    ext u
    constructor
    · intro hu
      exfalso
      have hu' := Finset.mem_filter.mp hu
      have huFlag := hu'.1
      have huCard := hu'.2
      change u ∈ permutedFaceFlag r t ht 1 at huFlag
      obtain ⟨k, -, huk⟩ := Finset.mem_image.mp huFlag
      have hcardle := Finset.card_le_card
        (permutedFacePrefix_subset r t ht 1 k)
      rw [huk] at hcardle
      exact (not_lt_of_ge (hcardle.trans (by omega))) huCard
    · simp
  have hcoefficient := simplexBoundaryCoefficient_insert
    (barycentricOrientationVertexOrder K r) hcentroidNot
  change simplexBoundaryCoefficient (barycentricOrientationVertexOrder K r)
      (permutedBarycentricFace r s hs q) D = 1
  rw [hface]
  have hdec : (barycentricOrientationVertexOrder K r).toDecidableEq =
      r.toDecidableEq := Subsingleton.elim _ _
  have hinsert :
      @insert E (Finset E)
          (@Finset.instInsert E (barycentricOrientationVertexOrder K r).toDecidableEq)
          (s.centroid ℝ id) D =
        @insert E (Finset E) (@Finset.instInsert E r.toDecidableEq)
          (s.centroid ℝ id) D :=
    congrArg (fun d : DecidableEq E =>
      @insert E (Finset E) (@Finset.instInsert E d) (s.centroid ℝ id) D) hdec
  rw [← hinsert] at hindex
  rw [← hinsert]
  rw [hcoefficient]
  unfold incidenceSign
  rw [hindex, hfilter]
  simp

open Classical in
theorem sign_cycleIcc_orderPosition_mul_simplexBoundaryCoefficient
    (r : LinearOrder E) {s t : Finset E} {n : ℕ}
    (hs : s.card = n + 2) {v : E} (hv : v ∈ s)
    (herase : @Finset.erase E (Classical.decEq E) s v = t) :
    let q := Fin.cycleIcc (orderPositionOfCard r s hs v hv) (Fin.last (n + 1))
    (Equiv.Perm.sign q : ℤ) * simplexBoundaryCoefficient r s t =
      (-1 : ℤ) ^ (n + 1) := by
  intro q
  let p := orderPositionOfCard r s hs v hv
  have hp : (p : ℕ) = incidenceIndex r s v :=
    orderPositionOfCard_eq_incidenceIndex r s hs v hv
  have hpLe : (p : ℕ) ≤ n + 1 := Fin.le_last p
  have hqUnits : Equiv.Perm.sign q = (-1 : ℤˣ) ^ (n + 1 - (p : ℕ)) := by
    exact Fin.sign_cycleIcc_of_le (Fin.le_last p)
  have hq := congrArg (fun z : ℤˣ => (z : ℤ)) hqUnits
  have hqInt : (Equiv.Perm.sign q : ℤ) =
      (-1 : ℤ) ^ (n + 1 - (p : ℕ)) := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using hq
  have hdec : r.toDecidableEq = Classical.decEq E := Subsingleton.elim _ _
  have heraseR : @Finset.erase E r.toDecidableEq s v = t := by
    rw [hdec]
    exact herase
  have hcoefficient : simplexBoundaryCoefficient r s t = incidenceSign r s v := by
    rw [← heraseR]
    exact simplexBoundaryCoefficient_erase r hv
  rw [hqInt, hcoefficient]
  unfold incidenceSign
  rw [← hp, ← pow_add, Nat.sub_add_cancel hpLe]

open Classical in
theorem CoherentOrientation.pair_cancel_of_faceCofaces_eq
    [AddCommGroup E] [Module ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {n : ℕ}
    (o : CoherentOrientation n K) {t s p : Finset E}
    (htK : t ∈ K.faces) (ht : t.card = n) (hsp : s ≠ p)
    (hpair : faceCofaces K t (n + 1) = {s, p}) :
    o.sign s * simplexBoundaryCoefficient o.vertexOrder s t +
      o.sign p * simplexBoundaryCoefficient o.vertexOrder p t = 0 := by
  have hnotone : (faceCofaces K t (n + 1)).card ≠ 1 := by
    rw [hpair]
    simp [hsp]
  have hzero := o.coherent t htK ht hnotone
  rw [orientedBoundary_eq_sum_faceCofaces, hpair] at hzero
  simpa only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton,
    hsp, not_false_eq_true] using hzero

open Classical in
theorem CoherentOrientation.sign_add_eq_zero_of_faceCofaces_eq_pair
    [AddCommGroup E] [Module ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {n : ℕ}
    (o : CoherentOrientation (n + 1) K) {t s p : Finset E}
    (htK : t ∈ K.faces) (ht : t.card = n + 1) (hsp : s ≠ p)
    (htwo : (faceCofaces K t (n + 2)).card = 2)
    (hsCoface : s ∈ faceCofaces K t (n + 2))
    (hpCoface : p ∈ faceCofaces K t (n + 2))
    (hsCoefficient : simplexBoundaryCoefficient o.vertexOrder s t = 1)
    (hpCoefficient : simplexBoundaryCoefficient o.vertexOrder p t = 1) :
    o.sign s + o.sign p = 0 := by
  have hpairSub : ({s, p} : Finset (Finset E)) ⊆ faceCofaces K t (n + 2) := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hsCoface, hpCoface⟩
  have hcofaces : faceCofaces K t (n + 2) = {s, p} := by
    apply (Finset.eq_of_subset_of_card_le hpairSub ?_).symm
    rw [htwo]
    simp [hsp]
  have hzero := o.pair_cancel_of_faceCofaces_eq htK ht hsp hcofaces
  rw [hsCoefficient, hpCoefficient, mul_one, mul_one] at hzero
  exact hzero

open Classical in
theorem barycentricFlagNormalizedSign_pair_cancel
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (r : LinearOrder E)
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    [Finite (PiecewiseLinear.barycentricSubdivision K).faces] {n : ℕ}
    (o : CoherentOrientation (n + 1) (PiecewiseLinear.barycentricSubdivision K))
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {t s p : Finset E} (htK : t ∈ K.faces) (hsK : s ∈ K.faces)
    (hpK : p ∈ K.faces) (ht : t.card = n + 1)
    (hs : s.card = n + 2) (hp : p.card = n + 2)
    (hts : t ⊆ s) (htp : t ⊆ p) (hsp : s ≠ p) :
    barycentricFlagNormalizedSign r
        (o.changeVertexOrder (barycentricOrientationVertexOrder K r)) hs 1 *
          simplexBoundaryCoefficient r s t +
      barycentricFlagNormalizedSign r
        (o.changeVertexOrder (barycentricOrientationVertexOrder K r)) hp 1 *
          simplexBoundaryCoefficient r p t = 0 := by
  obtain ⟨v, hvt, hsv⟩ := Finset.exists_eq_insert_iff.mpr ⟨hts, by omega⟩
  obtain ⟨w, hwt, hpw⟩ := Finset.exists_eq_insert_iff.mpr ⟨htp, by omega⟩
  have hv : v ∈ s := hsv ▸ Finset.mem_insert_self v t
  have hw : w ∈ p := hpw ▸ Finset.mem_insert_self w t
  have hserase : @Finset.erase E (Classical.decEq E) s v = t := by
    rw [← hsv]
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hxv, hxv' | hxt⟩
      · exact False.elim (hxv hxv')
      · exact hxt
    · intro hxt
      exact ⟨fun hxv => hvt (hxv ▸ hxt), Or.inr hxt⟩
  have hperase : @Finset.erase E (Classical.decEq E) p w = t := by
    rw [← hpw]
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hxw, hxw' | hxt⟩
      · exact False.elim (hxw hxw')
      · exact hxt
    · intro hxt
      exact ⟨fun hxw => hwt (hxw ▸ hxt), Or.inr hxt⟩
  let qS := Fin.cycleIcc (orderPositionOfCard r s hs v hv) (Fin.last (n + 1))
  let qP := Fin.cycleIcc (orderPositionOfCard r p hp w hw) (Fin.last (n + 1))
  let D := permutedBarycentricFace r t ht (1 : Equiv.Perm (Fin (n + 1)))
  let FS := permutedBarycentricFace r s hs qS
  let FP := permutedBarycentricFace r p hp qP
  let oB := o.changeVertexOrder (barycentricOrientationVertexOrder K r)
  have hfaceS : FS = insert (s.centroid ℝ id) D :=
    permutedBarycentricFace_cycleIcc_orderPosition r s t hs hv hserase ht
  have hfaceP : FP = insert (p.centroid ℝ id) D :=
    permutedBarycentricFace_cycleIcc_orderPosition r p t hp hw hperase ht
  have hDmem : D ∈ (barycentricSubdivision K).faces :=
    permutedBarycentricFace_mem K r htK ht 1
  have hFSmem : FS ∈ (barycentricSubdivision K).faces :=
    permutedBarycentricFace_mem K r hsK hs qS
  have hFPmem : FP ∈ (barycentricSubdivision K).faces :=
    permutedBarycentricFace_mem K r hpK hp qP
  have hDcard : D.card = n + 1 := permutedBarycentricFace_card K r htK ht 1
  have hFScard : FS.card = n + 2 := permutedBarycentricFace_card K r hsK hs qS
  have hFPcard : FP.card = n + 2 := permutedBarycentricFace_card K r hpK hp qP
  have hsCentroidNot : s.centroid ℝ id ∉ D := by
    intro hmem
    rw [hfaceS, Finset.card_insert_of_mem hmem, hDcard] at hFScard
    omega
  have hpCentroidNot : p.centroid ℝ id ∉ D := by
    intro hmem
    rw [hfaceP, Finset.card_insert_of_mem hmem, hDcard] at hFPcard
    omega
  have hcentroidNe : s.centroid ℝ id ≠ p.centroid ℝ id := by
    intro heq
    exact hsp (injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K) hsK hpK heq)
  have hFSFP : FS ≠ FP := by
    intro heq
    have hmem : s.centroid ℝ id ∈ FS := by
      rw [hfaceS]
      exact Finset.mem_insert_self _ _
    rw [heq, hfaceP] at hmem
    rcases Finset.mem_insert.mp hmem with hcentroid | hD
    · exact hcentroidNe hcentroid
    · exact hsCentroidNot hD
  have hDFS : D ⊆ FS := by
    rw [hfaceS]
    exact Finset.subset_insert _ _
  have hDFP : D ⊆ FP := by
    rw [hfaceP]
    exact Finset.subset_insert _ _
  have hFSco : FS ∈ faceCofaces (barycentricSubdivision K) D (n + 2) :=
    (mem_faceCofaces (barycentricSubdivision K)).mpr ⟨hFSmem, hFScard, hDFS⟩
  have hFPco : FP ∈ faceCofaces (barycentricSubdivision K) D (n + 2) :=
    (mem_faceCofaces (barycentricSubdivision K)).mpr ⟨hFPmem, hFPcard, hDFP⟩
  have hnotone : (faceCofaces (barycentricSubdivision K) D (n + 2)).card ≠ 1 := by
    intro hone
    obtain ⟨Q, hQ⟩ := Finset.card_eq_one.mp hone
    have hFSQ : FS = Q := by simpa [hQ] using hFSco
    have hFPQ : FP = Q := by simpa [hQ] using hFPco
    exact hFSFP (hFSQ.trans hFPQ.symm)
  have hBary :
      @barycentricSubdivision E _ _ (Classical.decEq E) K =
        @barycentricSubdivision E _ _ r.toDecidableEq K :=
    congrArg (fun d : DecidableEq E => @barycentricSubdivision E _ _ d K)
      (Subsingleton.elim _ _)
  have hR : IsCombinatorialManifoldWithBoundary (n + 1) (barycentricSubdivision K) := by
    have hR' := hK.barycentricSubdivision
    rw [hBary] at hR'
    exact hR'
  have htwo : (faceCofaces (barycentricSubdivision K) D (n + 2)).card = 2 :=
    (hR.card_faceCofaces_eq_one_or_two (barycentricSubdivision K) hDmem hDcard).resolve_left
      hnotone
  have hcoefficientS : simplexBoundaryCoefficient oB.vertexOrder FS D = 1 := by
    exact simplexBoundaryCoefficient_permutedBarycentricFace_cycleIcc_eq_one
      K r hsK htK hs hv hserase ht
  have hcoefficientP : simplexBoundaryCoefficient oB.vertexOrder FP D = 1 := by
    exact simplexBoundaryCoefficient_permutedBarycentricFace_cycleIcc_eq_one
      K r hpK htK hp hw hperase ht
  have hsignSum : oB.sign FS + oB.sign FP = 0 :=
    oB.sign_add_eq_zero_of_faceCofaces_eq_pair hDmem hDcard hFSFP htwo
      hFSco hFPco hcoefficientS hcoefficientP
  have hnormalizedS := barycentricFlagNormalizedSign_eq r o hK hsK hs 1 qS
  have hnormalizedP := barycentricFlagNormalizedSign_eq r o hK hpK hp 1 qP
  have hqS := sign_cycleIcc_orderPosition_mul_simplexBoundaryCoefficient
    r hs hv hserase
  have hqP := sign_cycleIcc_orderPosition_mul_simplexBoundaryCoefficient
    r hp hw hperase
  change barycentricFlagNormalizedSign r oB hs 1 * simplexBoundaryCoefficient r s t +
      barycentricFlagNormalizedSign r oB hp 1 * simplexBoundaryCoefficient r p t = 0
  rw [hnormalizedS, hnormalizedP]
  unfold barycentricFlagNormalizedSign
  change (oB.sign FS * (Equiv.Perm.sign qS : ℤ)) *
        simplexBoundaryCoefficient r s t +
      (oB.sign FP * (Equiv.Perm.sign qP : ℤ)) *
        simplexBoundaryCoefficient r p t = 0
  calc
    _ = oB.sign FS * ((Equiv.Perm.sign qS : ℤ) *
          simplexBoundaryCoefficient r s t) +
        oB.sign FP * ((Equiv.Perm.sign qP : ℤ) *
          simplexBoundaryCoefficient r p t) := by ring
    _ = oB.sign FS * ((-1 : ℤ) ^ (n + 1)) +
        oB.sign FP * ((-1 : ℤ) ^ (n + 1)) := by rw [hqS, hqP]
    _ = (oB.sign FS + oB.sign FP) * ((-1 : ℤ) ^ (n + 1)) := by ring
    _ = 0 := by rw [hsignSum, zero_mul]

open Classical in
noncomputable def barycentricRecoveredOrientationSign
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : LinearOrder E)
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    [Finite (barycentricSubdivision K).faces] {n : ℕ}
    (o : CoherentOrientation (n + 1) (barycentricSubdivision K))
    (s : Finset E) : ℤ :=
  if hs : s.card = n + 2 then
    barycentricFlagNormalizedSign r
      (o.changeVertexOrder (barycentricOrientationVertexOrder K r)) hs 1
  else 0

open Classical in
noncomputable def CoherentOrientation.ofBarycentricSubdivision
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (r : LinearOrder E)
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    [Finite (PiecewiseLinear.barycentricSubdivision K).faces] {n : ℕ}
    (o : CoherentOrientation (n + 1) (PiecewiseLinear.barycentricSubdivision K))
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) :
    CoherentOrientation (n + 1) K where
  vertexOrder := r
  sign := barycentricRecoveredOrientationSign r o
  sign_top := by
    intro s hsK hscard
    rw [barycentricRecoveredOrientationSign, dif_pos hscard]
    let oB := o.changeVertexOrder (barycentricOrientationVertexOrder K r)
    have hface := permutedBarycentricFace_mem K r hsK hscard
      (1 : Equiv.Perm (Fin (n + 2)))
    have hfaceCard := permutedBarycentricFace_card K r hsK hscard
      (1 : Equiv.Perm (Fin (n + 2)))
    have hsign := oB.sign_top
      (permutedBarycentricFace r s hscard 1) hface hfaceCard
    simpa only [barycentricFlagNormalizedSign, Equiv.Perm.sign_one,
      Units.val_one, mul_one] using hsign
  coherent := by
    intro t htK htcard hnotone
    have htwo : (faceCofaces K t (n + 2)).card = 2 :=
      (hK.card_faceCofaces_eq_one_or_two K htK htcard).resolve_left hnotone
    obtain ⟨s, p, hsp, hcofaces⟩ := Finset.card_eq_two.mp htwo
    have hsco : s ∈ faceCofaces K t (n + 2) := by
      rw [hcofaces]
      exact Finset.mem_insert_self s {p}
    have hpco : p ∈ faceCofaces K t (n + 2) := by
      rw [hcofaces]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self p)
    obtain ⟨hsK, hscard, hts⟩ := (mem_faceCofaces K).mp hsco
    obtain ⟨hpK, hpcard, htp⟩ := (mem_faceCofaces K).mp hpco
    have hcancel := barycentricFlagNormalizedSign_pair_cancel r o hK
      htK hsK hpK htcard hscard hpcard hts htp hsp
    rw [orientedBoundary_eq_sum_faceCofaces, hcofaces]
    simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton,
      hsp, not_false_eq_true]
    rw [barycentricRecoveredOrientationSign, dif_pos hscard,
      barycentricRecoveredOrientationSign, dif_pos hpcard]
    exact hcancel

open Classical in
theorem IsOrientable.of_barycentricSubdivision
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (h : IsOrientable (n + 1) (PiecewiseLinear.barycentricSubdivision K)) :
    IsOrientable (n + 1) K := by
  obtain ⟨o⟩ := h
  let r := o.vertexOrder
  let R₀ := @PiecewiseLinear.barycentricSubdivision E _ _ (Classical.decEq E) K
  let R₁ := @PiecewiseLinear.barycentricSubdivision E _ _ r.toDecidableEq K
  have hR : R₀ = R₁ :=
    congrArg (fun d : DecidableEq E =>
      @PiecewiseLinear.barycentricSubdivision E _ _ d K) (Subsingleton.elim _ _)
  have hpack₀ : ∃ f : Finite R₀.faces,
      Nonempty (@CoherentOrientation E _ _ (n + 1) R₀ f) := by
    exact ⟨inferInstance, ⟨o⟩⟩
  have hpack₁ : ∃ f : Finite R₁.faces,
      Nonempty (@CoherentOrientation E _ _ (n + 1) R₁ f) := by
    rw [← hR]
    exact hpack₀
  obtain ⟨fR, ⟨oR⟩⟩ := hpack₁
  let _ := fR
  exact ⟨CoherentOrientation.ofBarycentricSubdivision r oR hK⟩

open Classical in
theorem isOrientable_barycentricSubdivision_iff
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K) :
    IsOrientable n (barycentricSubdivision K) ↔ IsOrientable n K := by
  cases n with
  | zero => exact iff_of_true (isOrientable_zero _) (isOrientable_zero _)
  | succ n =>
    exact ⟨IsOrientable.of_barycentricSubdivision hK, fun h => h.barycentricSubdivision hK⟩

def dualGraph [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) :
    SimpleGraph {s : Finset E // s ∈ K.faces ∧ s.card = n + 1} where
  Adj s t := s ≠ t ∧ ∃ f ∈ K.faces, f.card = n ∧ f ⊆ s.1 ∧ f ⊆ t.1
  symm := ⟨by
    rintro s t ⟨hne, f, hf, hcard, hfs, hft⟩
    exact ⟨hne.symm, f, hf, hcard, hft, hfs⟩⟩
  loopless := ⟨by
    intro s h
    exact h.1 rfl⟩

open Classical in
theorem CoherentOrientation.sign_mul_sign_eq_of_dualGraph_adj
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o o' : CoherentOrientation n K) (horder : o'.vertexOrder = o.vertexOrder)
    {s t : {s : Finset E // s ∈ K.faces ∧ s.card = n + 1}}
    (hadj : (dualGraph n K).Adj s t) :
    o.sign s.1 * o'.sign s.1 = o.sign t.1 * o'.sign t.1 := by
  obtain ⟨hne, f, hf, hcard, hfs, hft⟩ := hadj
  have hst : s.1 ≠ t.1 := fun h => hne (Subtype.ext h)
  cases n with
  | zero =>
    exact ((K.nonempty_of_mem_faces hf).ne_empty (Finset.card_eq_zero.mp hcard)).elim
  | succ n =>
    have hsco : s.1 ∈ faceCofaces K f (n + 2) :=
      (mem_faceCofaces K).mpr ⟨s.2.1, s.2.2, hfs⟩
    have htco : t.1 ∈ faceCofaces K f (n + 2) :=
      (mem_faceCofaces K).mpr ⟨t.2.1, t.2.2, hft⟩
    have hsub : ({s.1, t.1} : Finset (Finset E)) ⊆ faceCofaces K f (n + 2) := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hsco, htco⟩
    have hcardge : 2 ≤ (faceCofaces K f (n + 2)).card := by
      simpa only [Finset.card_pair hst] using Finset.card_le_card hsub
    have htwo : (faceCofaces K f (n + 2)).card = 2 :=
      (hK.card_faceCofaces_eq_one_or_two K hf hcard).resolve_left (by omega)
    have hpair : faceCofaces K f (n + 2) = {s.1, t.1} := by
      apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
      rw [htwo, Finset.card_pair hst]
    have hcancel := o.pair_cancel_of_faceCofaces_eq hf hcard hst hpair
    have hcancel' := o'.pair_cancel_of_faceCofaces_eq hf hcard hst hpair
    rw [horder] at hcancel'
    have hcs : simplexBoundaryCoefficient o.vertexOrder s.1 f *
        simplexBoundaryCoefficient o.vertexOrder s.1 f = 1 := by
      rcases simplexBoundaryCoefficient_eq_one_or_neg_one o.vertexOrder hfs
        (by rw [hcard, s.2.2]) with h | h <;> rw [h] <;> norm_num
    have hct : simplexBoundaryCoefficient o.vertexOrder t.1 f *
        simplexBoundaryCoefficient o.vertexOrder t.1 f = 1 := by
      rcases simplexBoundaryCoefficient_eq_one_or_neg_one o.vertexOrder hft
        (by rw [hcard, t.2.2]) with h | h <;> rw [h] <;> norm_num
    calc
      o.sign s.1 * o'.sign s.1 =
          (o.sign s.1 * simplexBoundaryCoefficient o.vertexOrder s.1 f) *
            (o'.sign s.1 * simplexBoundaryCoefficient o.vertexOrder s.1 f) := by
        rw [mul_mul_mul_comm, hcs, mul_one]
      _ = (o.sign t.1 * simplexBoundaryCoefficient o.vertexOrder t.1 f) *
            (o'.sign t.1 * simplexBoundaryCoefficient o.vertexOrder t.1 f) := by
        rw [eq_neg_of_add_eq_zero_left hcancel, eq_neg_of_add_eq_zero_left hcancel', neg_mul_neg]
      _ = o.sign t.1 * o'.sign t.1 := by rw [mul_mul_mul_comm, hct, mul_one]

open Classical in
theorem CoherentOrientation.sign_mul_sign_eq_of_dualGraph_reachable
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o o' : CoherentOrientation n K) (horder : o'.vertexOrder = o.vertexOrder)
    {s t : {s : Finset E // s ∈ K.faces ∧ s.card = n + 1}}
    (hreach : (dualGraph n K).Reachable s t) :
    o.sign s.1 * o'.sign s.1 = o.sign t.1 * o'.sign t.1 := by
  obtain ⟨w⟩ := hreach
  induction w with
  | nil => rfl
  | cons h _ ih =>
    exact (o.sign_mul_sign_eq_of_dualGraph_adj hK o' horder h).trans ih

open Classical in
theorem coherentOrientation_eq_or_eq_neg
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K) (hconn : (dualGraph n K).Preconnected)
    (o o' : CoherentOrientation n K) :
    (∀ s ∈ K.faces, s.card = n + 1 →
      o.sign s = (o'.changeVertexOrder o.vertexOrder).sign s) ∨
    (∀ s ∈ K.faces, s.card = n + 1 →
      o.sign s = -(o'.changeVertexOrder o.vertexOrder).sign s) := by
  by_cases htop : ∃ s ∈ K.faces, s.card = n + 1
  · obtain ⟨s₀, hs₀, hs₀card⟩ := htop
    let q := o'.changeVertexOrder o.vertexOrder
    have hformula : ∀ s ∈ K.faces, s.card = n + 1 →
        o.sign s = (o.sign s₀ * q.sign s₀) * q.sign s := by
      intro s hs hscard
      have hratio := o.sign_mul_sign_eq_of_dualGraph_reachable hK q rfl
        (hconn ⟨s₀, hs₀, hs₀card⟩ ⟨s, hs, hscard⟩)
      have hsq : q.sign s * q.sign s = 1 := by
        rcases q.sign_top s hs hscard with h | h <;> rw [h] <;> norm_num
      calc
        o.sign s = (o.sign s * q.sign s) * q.sign s := by rw [mul_assoc, hsq, mul_one]
        _ = (o.sign s₀ * q.sign s₀) * q.sign s := by rw [← hratio]
    have hprod : o.sign s₀ * q.sign s₀ = 1 ∨ o.sign s₀ * q.sign s₀ = -1 := by
      rcases o.sign_top s₀ hs₀ hs₀card with h | h <;>
        rcases q.sign_top s₀ hs₀ hs₀card with h' | h' <;> simp only [h, h'] <;> norm_num
    rcases hprod with hprod | hprod
    · left
      intro s hs hscard
      simpa only [hprod, one_mul] using hformula s hs hscard
    · right
      intro s hs hscard
      simpa only [hprod, neg_one_mul] using hformula s hs hscard
  · left
    intro s hs hscard
    exact (htop ⟨s, hs, hscard⟩).elim

open Classical in
theorem faceCofaces_simplexComplex
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hne : T.Nonempty) {s : Finset E} (hs : s ⊆ T) :
    letI := (simplexComplex_faces_finite T hT).to_subtype
    faceCofaces (simplexComplex T hT) s T.card = {T} := by
  let _ := (simplexComplex_faces_finite T hT).to_subtype
  ext t
  rw [mem_faceCofaces, Finset.mem_singleton]
  constructor
  · rintro ⟨ht, hcard, _⟩
    exact Finset.eq_of_subset_of_card_le ht.2 hcard.ge
  · rintro rfl
    exact ⟨⟨hne, subset_rfl⟩, rfl, hs⟩

open Classical in
noncomputable def CoherentOrientation.simplex
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : LinearOrder E) (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    {n : ℕ} (hcard : T.card = n + 1) :
    letI := (simplexComplex_faces_finite T hT).to_subtype
    CoherentOrientation n (simplexComplex T hT) := by
  letI := (simplexComplex_faces_finite T hT).to_subtype
  refine {
    vertexOrder := r
    sign := fun _ => 1
    sign_top := fun _ _ _ => Or.inl rfl
    coherent := ?_ }
  intro s hs _ hnotone
  have hne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hcofaces := faceCofaces_simplexComplex T hT hne hs.2
  rw [hcard] at hcofaces
  exact (hnotone (by rw [hcofaces, Finset.card_singleton])).elim

open Classical in
theorem isOrientable_simplexComplex
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    {n : ℕ} (hcard : T.card = n + 1) :
    letI := (simplexComplex_faces_finite T hT).to_subtype
    IsOrientable n (simplexComplex T hT) := by
  exact ⟨CoherentOrientation.simplex (linearOrderOfSTO WellOrderingRel) T hT hcard⟩

open Classical in
noncomputable def CoherentOrientation.simplexBoundary
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : LinearOrder E) (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    {n : ℕ} (hcard : T.card = n + 2) :
    letI := (simplexBoundary_faces_finite T hT).to_subtype
    CoherentOrientation n (PiecewiseLinear.simplexBoundary T hT) := by
  letI := (simplexComplex_faces_finite T hT).to_subtype
  letI := (simplexBoundary_faces_finite T hT).to_subtype
  refine {
    vertexOrder := r
    sign := simplexBoundaryCoefficient r T
    sign_top := ?_
    coherent := ?_ }
  · intro s hs hscard
    exact simplexBoundaryCoefficient_eq_one_or_neg_one r hs.1 (by omega)
  · intro s _ _ _
    have hfaces :
        SimplicialComplex.facesOfCard
          (PiecewiseLinear.simplexBoundary T hT).toPreAbstractSimplicialComplex (n + 1) =
        SimplicialComplex.facesOfCard
          (simplexComplex T hT).toPreAbstractSimplicialComplex (n + 1) := by
      ext t
      rw [SimplicialComplex.mem_facesOfCard, SimplicialComplex.mem_facesOfCard]
      constructor
      · rintro ⟨ht, htcard⟩
        exact ⟨⟨ht.2.1, ht.1⟩, htcard⟩
      · rintro ⟨ht, htcard⟩
        refine ⟨⟨ht.2, ht.1, ?_⟩, htcard⟩
        intro heq
        have := congrArg Finset.card heq
        omega
    rw [orientedBoundary, hfaces]
    exact sum_simplexBoundaryCoefficient_comp_eq_zero r (simplexComplex T hT)
      ⟨Finset.card_pos.mp (by omega), subset_rfl⟩ hcard

open Classical in
theorem isOrientable_simplexBoundary
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    {n : ℕ} (hcard : T.card = n + 2) :
    letI := (simplexBoundary_faces_finite T hT).to_subtype
    IsOrientable n (simplexBoundary T hT) := by
  exact ⟨CoherentOrientation.simplexBoundary (linearOrderOfSTO WellOrderingRel) T hT hcard⟩

private theorem det_mul_dotProduct_eq_of_rows_eq_except
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.det ≠ 0) (i₀ : ι)
    (hrow : ∀ i, i ≠ i₀ → B i = A i) (v : ι → ℝ)
    (hv : ∀ i, i ≠ i₀ → dotProduct (A i) v = 0) :
    B.det * dotProduct (A i₀) v = A.det * dotProduct (B i₀) v := by
  obtain ⟨c, hc⟩ := Matrix.vecMul_surjective_iff_isUnit.mpr
    (A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hA)) (B i₀)
  have hsum : ∑ i, c i • A i = B i₀ := by
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct]
      using congrFun hc j
  have hB : B = A.updateRow i₀ (B i₀) := by
    ext i j
    by_cases hi : i = i₀
    · subst i
      rw [Matrix.updateRow_self]
    · rw [Matrix.updateRow_ne hi, hrow i hi]
  have hdet : B.det = c i₀ * A.det := by
    rw [hB, ← hsum, Matrix.det_updateRow_sum, smul_eq_mul]
  have hvalue : dotProduct (B i₀) v = c i₀ * dotProduct (A i₀) v := by
    rw [← hc, ← Matrix.dotProduct_mulVec]
    change (∑ i, c i * dotProduct (A i) v) = _
    apply Finset.sum_eq_single i₀
    · intro i _ hi
      rw [hv i hi, mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  rw [hdet, hvalue]
  ring

private theorem sign_det_permute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : Equiv.Perm ι) (A : Matrix ι ι ℝ) :
    (SignType.sign (A.submatrix q id).det : ℤ) =
      (Equiv.Perm.sign q : ℤ) * (SignType.sign A.det : ℤ) := by
  rw [Matrix.det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign q) with h | h <;>
    simp [h, Left.sign_neg, SignType.coe_neg]

open Classical in
private theorem sign_permuted_simplexCoordinateMatrix_mul_boundary
    [AddCommGroup E] [Module ℝ E]
    (r : LinearOrder E) {n : ℕ} {s t u : Finset E}
    (hs : s.card = n + 2) (hu : u.card = n + 2) {v : E} (hv : v ∈ s)
    (herase : @Finset.erase E (Classical.decEq E) s v = t) :
    let q := Fin.cycleIcc (orderPositionOfCard r s hs v hv) (Fin.last (n + 1))
    (SignType.sign ((simplexCoordinateMatrix r hs hu).submatrix q id).det : ℤ) *
        (-1 : ℤ) ^ (n + 1) =
      affineSimplexOrientationSign r hs hu * simplexBoundaryCoefficient r s t := by
  intro q
  have hq := sign_cycleIcc_orderPosition_mul_simplexBoundaryCoefficient r hs hv herase
  change (Equiv.Perm.sign q : ℤ) * simplexBoundaryCoefficient r s t = _ at hq
  rw [sign_det_permute, ← hq]
  unfold affineSimplexOrientationSign
  rcases Int.units_eq_one_or (Equiv.Perm.sign q) with h | h <;>
    simp [h]

open Classical in
theorem affineSimplexOrientationSign_pair_cancel
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : LinearOrder E) (K : Geometry.SimplicialComplex ℝ E)
    {n : ℕ} {s t f u : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hst : s ≠ t) (hfs : f ⊆ s) (hft : f ⊆ t)
    (hfcard : f.card = n + 1) (hscard : s.card = n + 2)
    (htcard : t.card = n + 2) (hucard : u.card = n + 2)
    (hsu : convexHull ℝ (s : Set E) ⊆ convexHull ℝ (u : Set E))
    (htu : convexHull ℝ (t : Set E) ⊆ convexHull ℝ (u : Set E)) :
    affineSimplexOrientationSign r hscard hucard * simplexBoundaryCoefficient r s f +
      affineSimplexOrientationSign r htcard hucard * simplexBoundaryCoefficient r t f = 0 := by
  let _ := r
  obtain ⟨a, haf, has⟩ := Finset.exists_eq_insert_iff.mpr ⟨hfs, by omega⟩
  obtain ⟨b, hbf, hbt⟩ := Finset.exists_eq_insert_iff.mpr ⟨hft, by omega⟩
  have ha : a ∈ s := has ▸ Finset.mem_insert_self a f
  have hb : b ∈ t := hbt ▸ Finset.mem_insert_self b f
  have hab : a ≠ b := fun h => hst (has.symm.trans (h ▸ hbt))
  have hsErase : @Finset.erase E (Classical.decEq E) s a = f := by
    have hdec : Classical.decEq E = r.toDecidableEq := Subsingleton.elim _ _
    rw [hdec, ← has, Finset.erase_insert haf]
  have htErase : @Finset.erase E (Classical.decEq E) t b = f := by
    have hdec : Classical.decEq E = r.toDecidableEq := Subsingleton.elim _ _
    rw [hdec, ← hbt, Finset.erase_insert hbf]
  let x := f.centroid ℝ id
  have hfK : f ∈ K.faces := K.down_closed hs hfs (Finset.card_pos.mp (by omega))
  have hx : x ∈ openSimplex f := centroid_mem_openSimplex_of_mem_faces K f hfK
  obtain ⟨ℓ, hℓf, hℓa, hℓb⟩ := exists_linearMap_separating_cofaces K hx haf hbf hab
    (by
      let _ := Classical.decEq E
      have has' : insert a f = s := by
        ext z
        simpa only [Finset.mem_insert] using Finset.ext_iff.mp has z
      rw [has']
      exact hs)
    (by
      let _ := Classical.decEq E
      have hbt' : insert b f = t := by
        ext z
        simpa only [Finset.mem_insert] using Finset.ext_iff.mp hbt z
      rw [hbt']
      exact ht)
  let qS := Fin.cycleIcc (orderPositionOfCard r s hscard a ha) (Fin.last (n + 1))
  let qT := Fin.cycleIcc (orderPositionOfCard r t htcard b hb) (Fin.last (n + 1))
  let A := (simplexCoordinateMatrix r hscard hucard).submatrix qS id
  let B := (simplexCoordinateMatrix r htcard hucard).submatrix qT id
  let v := fun j : Fin (n + 2) => ℓ (((Finset.orderIsoOfFin u hucard) j).1 - x)
  have hsEnum (i : Fin (n + 1)) :
      orderValueOfCard r s hscard (qS i.castSucc) = orderValueOfCard r f hfcard i := by
    have h := orderValueOfCard_erase_apply r s hscard ha (hsErase.symm ▸ hfcard) i
    simpa only [hsErase] using h.symm
  have htEnum (i : Fin (n + 1)) :
      orderValueOfCard r t htcard (qT i.castSucc) = orderValueOfCard r f hfcard i := by
    have h := orderValueOfCard_erase_apply r t htcard hb (htErase.symm ▸ hfcard) i
    simpa only [htErase] using h.symm
  have hsLast : orderValueOfCard r s hscard (qS (Fin.last (n + 1))) = a := by
    dsimp only [qS]
    rw [Fin.cycleIcc_of_last (Fin.le_last _)]
    change ((Finset.orderIsoOfFin s hscard)
      ((Finset.orderIsoOfFin s hscard).symm ⟨a, ha⟩)).1 = a
    simp only [OrderIso.apply_symm_apply]
  have htLast : orderValueOfCard r t htcard (qT (Fin.last (n + 1))) = b := by
    dsimp only [qT]
    rw [Fin.cycleIcc_of_last (Fin.le_last _)]
    change ((Finset.orderIsoOfFin t htcard)
      ((Finset.orderIsoOfFin t htcard).symm ⟨b, hb⟩)).1 = b
    simp only [OrderIso.apply_symm_apply]
  have hrows : ∀ i, i ≠ Fin.last (n + 1) → B i = A i := by
    intro i hi
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    funext k
    change weights u (orderValueOfCard r t htcard (qT j.castSucc))
      ((Finset.orderIsoOfFin u hucard) k).1 =
      weights u (orderValueOfCard r s hscard (qS j.castSucc))
        ((Finset.orderIsoOfFin u hucard) k).1
    rw [hsEnum, htEnum]
  have hAeval (i : Fin (n + 2)) :
      dotProduct (A i) v = ℓ (orderValueOfCard r s hscard (qS i) - x) :=
    congrFun (simplexCoordinateMatrix_mulVec r hscard hucard hsu ℓ x) (qS i)
  have hBeval (i : Fin (n + 2)) :
      dotProduct (B i) v = ℓ (orderValueOfCard r t htcard (qT i) - x) :=
    congrFun (simplexCoordinateMatrix_mulVec r htcard hucard htu ℓ x) (qT i)
  have hzero : ∀ i, i ≠ Fin.last (n + 1) → dotProduct (A i) v = 0 := by
    intro i hi
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    rw [hAeval, hsEnum]
    apply hℓf
    have hy : orderValueOfCard r f hfcard j ∈ affineSpan ℝ (f : Set E) :=
      mem_affineSpan ℝ (Finset.orderEmbOfFin_mem f hfcard j)
    have hxspan : x ∈ affineSpan ℝ (f : Set E) :=
      convexHull_subset_affineSpan (f : Set E) (openSimplex_subset_convexHull f hx)
    simpa only [direction_affineSpan, vsub_eq_sub] using
      AffineSubspace.vsub_mem_direction hy hxspan
  have hA : A.det ≠ 0 := by
    dsimp only [A]
    rw [Matrix.det_permute]
    apply mul_ne_zero
    · exact_mod_cast (Units.ne_zero (Equiv.Perm.sign qS))
    · exact simplexCoordinateMatrix_det_ne_zero r hscard hucard (K.indep hs) hsu
  have hdet := det_mul_dotProduct_eq_of_rows_eq_except A B hA (Fin.last (n + 1)) hrows v hzero
  rw [hAeval, hBeval, hsLast, htLast, hℓa, mul_one] at hdet
  have hsign : (SignType.sign B.det : ℤ) = -(SignType.sign A.det : ℤ) := by
    rw [hdet, sign_mul, sign_neg hℓb, SignType.coe_mul, SignType.coe_neg_one, mul_neg_one]
  have hS := sign_permuted_simplexCoordinateMatrix_mul_boundary r hscard hucard ha hsErase
  have hT := sign_permuted_simplexCoordinateMatrix_mul_boundary r htcard hucard hb htErase
  change (SignType.sign A.det : ℤ) * (-1 : ℤ) ^ (n + 1) = _ at hS
  change (SignType.sign B.det : ℤ) * (-1 : ℤ) ^ (n + 1) = _ at hT
  rw [← hS, ← hT, hsign, neg_mul, add_neg_cancel]

open Classical in
noncomputable def CoherentOrientation.ofConvexHull
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (r : LinearOrder E) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (T : Finset E) (hTcard : T.card = n + 2)
    (hsub : K.space ⊆ convexHull ℝ (T : Set E)) : CoherentOrientation (n + 1) K where
  vertexOrder := r
  sign s := if hs : s.card = n + 2 then affineSimplexOrientationSign r hs hTcard else 0
  sign_top := by
    intro s hs hscard
    simp only [dif_pos hscard]
    exact affineSimplexOrientationSign_eq_one_or_neg_one r hscard hTcard (K.indep hs)
      ((K.convexHull_subset_space hs).trans hsub)
  coherent := by
    intro f hf hfcard hnotone
    have htwo : (faceCofaces K f (n + 2)).card = 2 :=
      (hK.card_faceCofaces_eq_one_or_two K hf hfcard).resolve_left hnotone
    obtain ⟨s, t, hst, hcofaces⟩ := Finset.card_eq_two.mp htwo
    have hsco : s ∈ faceCofaces K f (n + 2) := by
      rw [hcofaces]
      exact Finset.mem_insert_self s {t}
    have htco : t ∈ faceCofaces K f (n + 2) := by
      rw [hcofaces]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self t)
    obtain ⟨hs, hscard, hfs⟩ := (mem_faceCofaces K).mp hsco
    obtain ⟨ht, htcard, hft⟩ := (mem_faceCofaces K).mp htco
    rw [orientedBoundary_eq_sum_faceCofaces, hcofaces]
    simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton,
      hst, not_false_eq_true, dif_pos hscard, dif_pos htcard]
    exact affineSimplexOrientationSign_pair_cancel r K hs ht hst hfs hft hfcard hscard htcard
      hTcard ((K.convexHull_subset_space hs).trans hsub) ((K.convexHull_subset_space ht).trans hsub)

open Classical in
theorem isOrientable_of_space_subset_convexHull
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary n K)
    (T : Finset E) (hTcard : T.card = n + 1)
    (hsub : K.space ⊆ convexHull ℝ (T : Set E)) : IsOrientable n K := by
  cases n with
  | zero => exact isOrientable_zero K
  | succ n =>
    exact ⟨CoherentOrientation.ofConvexHull (linearOrderOfSTO WellOrderingRel) K hK T hTcard hsub⟩

open Classical in
theorem isOrientable_of_isSubdivision_simplexComplex
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    {n : ℕ} (hTcard : T.card = n + 1) (h : IsSubdivision K (simplexComplex T hT)) :
    IsOrientable n K := by
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hspace : K.space = convexHull ℝ (T : Set E) :=
    h.space_eq.trans (simplexComplex_space T hT hTne)
  have hball : IsPLBall n K.space := by
    rw [hspace]
    exact isPLBall_convexHull_of_affineIndependent T hT hTcard
  cases n with
  | zero => exact isOrientable_zero K
  | succ n =>
    exact isOrientable_of_space_subset_convexHull K hball.isCombinatorialManifoldWithBoundary
      T hTcard hspace.subset

open Classical in
private theorem orderValueOfCard_cycleIcc_last
    (r : LinearOrder E) {s : Finset E} {n : ℕ} (hs : s.card = n + 1)
    {a : E} (ha : a ∈ s) :
    orderValueOfCard r s hs
      (Fin.cycleIcc (orderPositionOfCard r s hs a ha) (Fin.last n) (Fin.last n)) = a := by
  let _ := r
  rw [Fin.cycleIcc_of_last (Fin.le_last _)]
  change ((Finset.orderIsoOfFin s hs) ((Finset.orderIsoOfFin s hs).symm ⟨a, ha⟩)).1 = a
  simp only [OrderIso.apply_symm_apply]

open Classical in
private theorem orderValueOfCard_cycleIcc_castSucc
    (r : LinearOrder E) {s f : Finset E} {n : ℕ}
    (hs : s.card = n + 1) (hf : f.card = n) {a : E} (ha : a ∈ s)
    (herase : @Finset.erase E (Classical.decEq E) s a = f) (i : Fin n) :
    orderValueOfCard r s hs
      (Fin.cycleIcc (orderPositionOfCard r s hs a ha) (Fin.last n) i.castSucc) =
      orderValueOfCard r f hf i := by
  have h := orderValueOfCard_erase_apply r s hs ha (herase.symm ▸ hf) i
  simpa only [herase] using h.symm

open Classical in
private theorem simplexCoordinateMatrix_det_facet
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : LinearOrder E) {n : ℕ} {s f u g : Finset E}
    (hs : s.card = n + 2) (hf : f.card = n + 1)
    (hu : u.card = n + 2) (hg : g.card = n + 1)
    {a b : E} (ha : a ∈ s) (hb : b ∈ u)
    (hsErase : @Finset.erase E (Classical.decEq E) s a = f)
    (huErase : @Finset.erase E (Classical.decEq E) u b = g)
    (hindep : AffineIndependent ℝ ((↑) : u → E))
    (hfg : convexHull ℝ (f : Set E) ⊆ convexHull ℝ (g : Set E)) :
    let qS := Fin.cycleIcc (orderPositionOfCard r s hs a ha) (Fin.last (n + 1))
    let qU := Fin.cycleIcc (orderPositionOfCard r u hu b hb) (Fin.last (n + 1))
    ((simplexCoordinateMatrix r hs hu).submatrix qS qU).det =
      weights u a b * (simplexCoordinateMatrix r hf hg).det := by
  let _ := r
  intro qS qU
  let C := (simplexCoordinateMatrix r hs hu).submatrix qS qU
  have huEraseR : @Finset.erase E r.toDecidableEq u b = g := by
    rw [show r.toDecidableEq = Classical.decEq E from Subsingleton.elim _ _]
    exact huErase
  have hgu : g ⊆ u := huEraseR ▸ Finset.erase_subset b u
  have hbg : b ∉ g := huEraseR ▸ Finset.notMem_erase b u
  have hsEnum (i : Fin (n + 1)) :
      orderValueOfCard r s hs (qS i.castSucc) = orderValueOfCard r f hf i :=
    orderValueOfCard_cycleIcc_castSucc r hs hf ha hsErase i
  have huEnum (i : Fin (n + 1)) :
      orderValueOfCard r u hu (qU i.castSucc) = orderValueOfCard r g hg i :=
    orderValueOfCard_cycleIcc_castSucc r hu hg hb huErase i
  have hsLast : orderValueOfCard r s hs (qS (Fin.last (n + 1))) = a :=
    orderValueOfCard_cycleIcc_last r hs ha
  have huLast : orderValueOfCard r u hu (qU (Fin.last (n + 1))) = b :=
    orderValueOfCard_cycleIcc_last r hu hb
  have hminor : C.submatrix Fin.castSucc Fin.castSucc = simplexCoordinateMatrix r hf hg := by
    ext i j
    change weights u (orderValueOfCard r s hs (qS i.castSucc))
      (orderValueOfCard r u hu (qU j.castSucc)) =
      weights g (orderValueOfCard r f hf i) (orderValueOfCard r g hg j)
    rw [hsEnum, huEnum]
    exact weights_eq_of_subset_of_mem hindep hgu
      (hfg (subset_convexHull ℝ _ (Finset.orderEmbOfFin_mem f hf i)))
      (Finset.orderEmbOfFin_mem g hg j)
  have hcol : ∀ i, i ≠ Fin.last (n + 1) → C i (Fin.last (n + 1)) = 0 := by
    intro i hi
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    change weights u (orderValueOfCard r s hs (qS j.castSucc))
      (orderValueOfCard r u hu (qU (Fin.last (n + 1)))) = 0
    rw [hsEnum, huLast]
    exact weights_eq_zero_of_subset_of_notMem hindep hgu
      (hfg (subset_convexHull ℝ _ (Finset.orderEmbOfFin_mem f hf j))) hb hbg
  have hcorner : C (Fin.last (n + 1)) (Fin.last (n + 1)) = weights u a b := by
    change weights u (orderValueOfCard r s hs (qS (Fin.last (n + 1))))
      (orderValueOfCard r u hu (qU (Fin.last (n + 1)))) = _
    rw [hsLast, huLast]
  change C.det = _
  rw [Matrix.det_succ_column C (Fin.last (n + 1)), Finset.sum_eq_single (Fin.last (n + 1))]
  · have hminor' : C.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove =
        simplexCoordinateMatrix r hf hg := by
      ext i j
      simpa only [Matrix.submatrix_apply, Fin.succAbove_last_apply] using
        congrFun (congrFun hminor i) j
    rw [hcorner, hminor']
    norm_num [Fin.val_last, ← two_mul, pow_mul]
  · intro i _ hi
    rw [hcol i hi, mul_zero, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]

private theorem sign_det_permute_columns
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : Equiv.Perm ι) (A : Matrix ι ι ℝ) :
    (SignType.sign (A.submatrix id q).det : ℤ) =
      (Equiv.Perm.sign q : ℤ) * (SignType.sign A.det : ℤ) := by
  rw [Matrix.det_permute']
  rcases Int.units_eq_one_or (Equiv.Perm.sign q) with h | h <;>
    simp [h, Left.sign_neg, SignType.coe_neg]

open Classical in
theorem affineSimplexOrientationSign_mul_simplexBoundaryCoefficient
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : LinearOrder E) {n : ℕ} {s f u g : Finset E}
    (hs : s.card = n + 2) (hf : f.card = n + 1)
    (hu : u.card = n + 2) (hg : g.card = n + 1)
    (hsindep : AffineIndependent ℝ ((↑) : s → E))
    (huindep : AffineIndependent ℝ ((↑) : u → E))
    (hfs : f ⊆ s) (hgu : g ⊆ u)
    (hsu : convexHull ℝ (s : Set E) ⊆ convexHull ℝ (u : Set E))
    (hfg : convexHull ℝ (f : Set E) ⊆ convexHull ℝ (g : Set E)) :
    affineSimplexOrientationSign r hs hu * simplexBoundaryCoefficient r s f =
      affineSimplexOrientationSign r hf hg * simplexBoundaryCoefficient r u g := by
  obtain ⟨a, haf, has⟩ := Finset.exists_eq_insert_iff.mpr ⟨hfs, by omega⟩
  obtain ⟨b, hbg, hbu⟩ := Finset.exists_eq_insert_iff.mpr ⟨hgu, by omega⟩
  have ha : a ∈ s := has ▸ Finset.mem_insert_self a f
  have hb : b ∈ u := hbu ▸ Finset.mem_insert_self b g
  have hsErase : @Finset.erase E (Classical.decEq E) s a = f := by
    have hdec : Classical.decEq E = r.toDecidableEq := Subsingleton.elim _ _
    rw [hdec, ← has, Finset.erase_insert haf]
  have huErase : @Finset.erase E (Classical.decEq E) u b = g := by
    have hdec : Classical.decEq E = r.toDecidableEq := Subsingleton.elim _ _
    rw [hdec, ← hbu, Finset.erase_insert hbg]
  let qS := Fin.cycleIcc (orderPositionOfCard r s hs a ha) (Fin.last (n + 1))
  let qU := Fin.cycleIcc (orderPositionOfCard r u hu b hb) (Fin.last (n + 1))
  let A := (simplexCoordinateMatrix r hs hu).submatrix qS id
  let C := A.submatrix id qU
  have hdet : C.det = weights u a b * (simplexCoordinateMatrix r hf hg).det :=
    simplexCoordinateMatrix_det_facet r hs hf hu hg ha hb hsErase huErase huindep hfg
  have hC : C.det ≠ 0 := by
    dsimp only [C, A]
    rw [Matrix.det_permute', Matrix.det_permute]
    apply mul_ne_zero
    · exact_mod_cast (Units.ne_zero (Equiv.Perm.sign qU))
    · apply mul_ne_zero
      · exact_mod_cast (Units.ne_zero (Equiv.Perm.sign qS))
      · exact simplexCoordinateMatrix_det_ne_zero r hs hu hsindep hsu
  have hpos : 0 < weights u a b := by
    have hne : weights u a b ≠ 0 := by
      intro hz
      exact hC (by rw [hdet, hz, zero_mul])
    exact lt_of_le_of_ne (weights_nonneg (hsu (subset_convexHull ℝ _ ha)) hb) hne.symm
  have hsignC : (SignType.sign C.det : ℤ) = affineSimplexOrientationSign r hf hg := by
    rw [hdet, sign_mul, sign_pos hpos, one_mul]
    rfl
  have hU := sign_cycleIcc_orderPosition_mul_simplexBoundaryCoefficient r hu hb huErase
  change (Equiv.Perm.sign qU : ℤ) * simplexBoundaryCoefficient r u g = _ at hU
  have hS := sign_permuted_simplexCoordinateMatrix_mul_boundary r hs hu ha hsErase
  change (SignType.sign A.det : ℤ) * (-1 : ℤ) ^ (n + 1) = _ at hS
  calc
    affineSimplexOrientationSign r hs hu * simplexBoundaryCoefficient r s f =
        (SignType.sign A.det : ℤ) * (-1 : ℤ) ^ (n + 1) := hS.symm
    _ = ((Equiv.Perm.sign qU : ℤ) * (SignType.sign A.det : ℤ)) *
        simplexBoundaryCoefficient r u g := by rw [← hU]; ring
    _ = (SignType.sign C.det : ℤ) * simplexBoundaryCoefficient r u g := by
      rw [show (SignType.sign C.det : ℤ) = _ from sign_det_permute_columns qU A]
    _ = affineSimplexOrientationSign r hf hg * simplexBoundaryCoefficient r u g := by rw [hsignC]

end DifferentialGeometry.Topology.PiecewiseLinear
