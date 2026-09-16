import DifferentialGeometry.Topology.Homology.ModuleHomologyClasses
import DifferentialGeometry.Topology.PiecewiseLinear.DoubleCoverComplex
import DifferentialGeometry.Topology.PiecewiseLinear.HandleCount
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private def zmodTwoOfBool : Bool → ZMod 2
  | false => 0
  | true => 1

private def boolOfZModTwo (x : ZMod 2) : Bool :=
  match x.val with
  | 0 => false
  | _ + 1 => true

private theorem zmodTwoOfBool_injective : Function.Injective zmodTwoOfBool := by
  intro a b
  cases a <;> cases b <;> simp [zmodTwoOfBool]

private theorem zmodTwoOfBool_boolOfZModTwo (x : ZMod 2) :
    zmodTwoOfBool (boolOfZModTwo x) = x := by
  fin_cases x
  · rfl
  · rfl

private theorem zmodTwoOfBool_xor (a b : Bool) :
    zmodTwoOfBool (Bool.xor a b) = zmodTwoOfBool a + zmodTwoOfBool b := by
  cases a <;> cases b
  · rfl
  · rfl
  · rfl
  · change (0 : ZMod 2) = 2
    exact (ZMod.natCast_self 2).symm

private theorem exists_edgeFunctional_of_nontrivial_homology
    {k : Type} [Field k] (S : ShortComplex (ModuleCat k))
    [Nontrivial S.homology] :
    ∃ φ : Module.Dual k S.X₂,
      (∀ b : S.X₁, φ (S.f b) = 0) ∧
      ∃ z : LinearMap.ker S.g.hom, φ z.1 ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_ne (0 : S.homology)
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero k ha
  obtain ⟨z, hz⟩ := moduleHomologyClass_surjective S a
  let φZ : Module.Dual k (LinearMap.ker S.g.hom) :=
    ψ.comp (moduleHomologyClass S)
  let φ : Module.Dual k S.X₂ := Subspace.dualLift (LinearMap.ker S.g.hom) φZ
  refine ⟨φ, ?_, ?_⟩
  · intro b
    have hmem : S.f b ∈ LinearMap.ker S.g.hom := by
      change S.g (S.f b) = 0
      have h := congrArg (fun q : S.X₁ ⟶ S.X₃ => q b) S.zero
      change S.g (S.f b) = 0 at h
      exact h
    rw [show φ (S.f b) = φZ ⟨S.f b, hmem⟩ from Subspace.dualLift_of_mem hmem]
    have hz0 : moduleHomologyClass S ⟨S.f b, hmem⟩ = 0 :=
      (moduleHomologyClass_eq_zero_iff S _).2 ⟨b, rfl⟩
    simp [φZ, hz0]
  · refine ⟨z, ?_⟩
    rw [show φ z.1 = φZ z from Subspace.dualLift_of_subtype z]
    simpa [φZ, hz] using hψ

private theorem simplexBoundaryCoefficient_mod_two
    {E : Type} (r : LinearOrder E) {s t : Finset E}
    (hcard : t.card + 1 = s.card) :
    (simplexBoundaryCoefficient r s t : ZMod 2) = if t ⊆ s then 1 else 0 := by
  classical
  by_cases hts : t ⊆ s
  · rw [if_pos hts]
    rcases simplexBoundaryCoefficient_eq_one_or_neg_one r hts hcard with h | h
    · simp [h]
    · rw [h]
      simpa only [Int.cast_neg, Int.cast_one] using
        ZMod.neg_eq_self_mod_two (1 : ZMod 2)
  · rw [if_neg hts]
    have hzero : simplexBoundaryCoefficient r s t = 0 := by
      rw [simplexBoundaryCoefficient]
      apply Finset.sum_eq_zero
      intro v hv
      have hne : s.erase v ≠ t := by
        intro h
        apply hts
        rw [← h]
        exact Finset.erase_subset v s
      simp [hne]
    simp [hzero]

private theorem eq_pair_or_pair_or_pair_of_card_two_subset_triple
    {E : Type} [DecidableEq E] {s : Finset E} {a b c : E}
    (hs : s.card = 2) (hsub : s ⊆ {a, b, c}) :
    s = {a, b} ∨ s = {b, c} ∨ s = {a, c} := by
  classical
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hs
  have hx : x = a ∨ x = b ∨ x = c := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hsub (by simp)
  have hy : y = a ∨ y = b ∨ y = c := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hsub (by simp)
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    simp_all [Finset.pair_comm]

private noncomputable def pairChain
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (a b : E) :
    {s : Finset E // s ∈ K.faces ∧ s.card = 2} → ZMod 2 :=
  by
    classical
    exact if h : {a, b} ∈ K.faces ∧ ({a, b} : Finset E).card = 2 then
      Pi.single ⟨{a, b}, h⟩ 1
    else 0

private theorem pairChain_self
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (a : E) : pairChain K a a = 0 := by
  simp [pairChain]

private theorem pairChain_symm
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (a b : E) : pairChain K a b = pairChain K b a := by
  unfold pairChain
  rw [Finset.pair_comm a b]

private theorem pairChain_of_face
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {a b : E} (hab : {a, b} ∈ K.faces) (hne : a ≠ b) :
    pairChain K a b = Pi.single ⟨{a, b}, hab, Finset.card_pair hne⟩ 1 := by
  simp [pairChain, hab, Finset.card_pair hne]

private theorem orderedNormalizedBoundary_triangle_mod_two
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {a b c : E} (habc : {a, b, c} ∈ K.faces)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    SimplicialComplex.orderedNormalizedBoundary (k := ZMod 2)
        K.toPreAbstractSimplicialComplex 1
        (Pi.single ⟨{a, b, c}, habc, by simp [hab, hbc, hac]⟩ 1) =
      pairChain K a b + pairChain K b c + pairChain K a c := by
  classical
  have habFace : {a, b} ∈ K.faces :=
    K.down_closed habc (by simp) (by simp)
  have hbcFace : {b, c} ∈ K.faces :=
    K.down_closed habc (by simp) (by simp)
  have hacFace : {a, c} ∈ K.faces :=
    K.down_closed habc (by simp) (by simp)
  let eab : {s : Finset E // s ∈ K.faces ∧ s.card = 2} :=
    ⟨{a, b}, habFace, Finset.card_pair hab⟩
  let ebc : {s : Finset E // s ∈ K.faces ∧ s.card = 2} :=
    ⟨{b, c}, hbcFace, Finset.card_pair hbc⟩
  let eac : {s : Finset E // s ∈ K.faces ∧ s.card = 2} :=
    ⟨{a, c}, hacFace, Finset.card_pair hac⟩
  have eabNeEbc : eab ≠ ebc := by
    intro h
    have hsets := congrArg (fun e : {s : Finset E // s ∈ K.faces ∧ s.card = 2} => e.1) h
    change ({a, b} : Finset E) = {b, c} at hsets
    have haMem : a ∈ ({b, c} : Finset E) := by
      rw [← hsets]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at haMem
    exact haMem.elim hab hac
  have eabNeEac : eab ≠ eac := by
    intro h
    have hsets := congrArg (fun e : {s : Finset E // s ∈ K.faces ∧ s.card = 2} => e.1) h
    change ({a, b} : Finset E) = {a, c} at hsets
    have hbMem : b ∈ ({a, c} : Finset E) := by
      rw [← hsets]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbMem
    exact hbMem.elim (Ne.symm hab) hbc
  have ebcNeEac : ebc ≠ eac := by
    intro h
    have hsets := congrArg (fun e : {s : Finset E // s ∈ K.faces ∧ s.card = 2} => e.1) h
    change ({b, c} : Finset E) = {a, c} at hsets
    have hbMem : b ∈ ({a, c} : Finset E) := by
      rw [← hsets]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbMem
    exact hbMem.elim (Ne.symm hab) hbc
  rw [show pairChain K a b = Pi.single eab 1 by
      simpa only [eab] using pairChain_of_face K habFace hab,
    show pairChain K b c = Pi.single ebc 1 by
      simpa only [ebc] using pairChain_of_face K hbcFace hbc,
    show pairChain K a c = Pi.single eac 1 by
      simpa only [eac] using pairChain_of_face K hacFace hac]
  funext t
  rw [SimplicialComplex.orderedNormalizedBoundary_single_apply]
  rw [simplexBoundaryCoefficient_mod_two (hcard := by
    rw [t.2.2]
    dsimp
    simp [hab, hbc, hac])]
  by_cases hsub : t.1 ⊆ {a, b, c}
  · rw [if_pos hsub]
    rcases eq_pair_or_pair_or_pair_of_card_two_subset_triple t.2.2 hsub with h | h | h
    · have ht : t = eab := Subtype.ext h
      subst t
      simp [eabNeEbc, eabNeEac]
    · have ht : t = ebc := Subtype.ext h
      subst t
      simp [eabNeEbc, ebcNeEac]
    · have ht : t = eac := Subtype.ext h
      subst t
      simp [eabNeEac, ebcNeEac]
  · rw [if_neg hsub]
    have habNe : t ≠ eab := by
      intro h
      apply hsub
      rw [h]
      simp [eab]
    have hbcNe : t ≠ ebc := by
      intro h
      apply hsub
      rw [h]
      simp [ebc]
    have hacNe : t ≠ eac := by
      intro h
      apply hsub
      rw [h]
      simp [eac]
    simp [habNe, hbcNe, hacNe]

private def singletonVertex
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
    {K : Geometry.SimplicialComplex ℝ E}
    (v : {s : Finset E // s ∈ K.faces ∧ s.card = 1}) : E :=
  v.1.min' (Finset.card_pos.mp (by rw [v.2.2]; decide))

private theorem singletonVertex_singleton
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
    {K : Geometry.SimplicialComplex ℝ E}
    {a : E} (ha : {a} ∈ K.faces) :
    singletonVertex (K := K) ⟨{a}, ha, Finset.card_singleton a⟩ = a := by
  simp [singletonVertex]

private noncomputable def vertexFunctional
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (δ : E → Bool) :
    ({s : Finset E // s ∈ K.faces ∧ s.card = 1} → ZMod 2) →ₗ[ZMod 2] ZMod 2 := by
  let _ : Finite {s : Finset E // s ∈ K.faces ∧ s.card = 1} := Finite.of_injective
    (fun s => (⟨s.1, s.2.1⟩ : K.faces))
    (fun _ _ h => Subtype.ext (congrArg (fun x : K.faces => x.1) h))
  let _ : Fintype {s : Finset E // s ∈ K.faces ∧ s.card = 1} := Fintype.ofFinite _
  exact {
    toFun := fun x => ∑ v, zmodTwoOfBool (δ (singletonVertex v)) * x v
    map_add' := by
      intro x y
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c x
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring }

private theorem vertexFunctional_single
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (δ : E → Bool) (v : {s : Finset E // s ∈ K.faces ∧ s.card = 1}) :
    vertexFunctional K δ (Pi.single v 1) = zmodTwoOfBool (δ (singletonVertex v)) := by
  classical
  let _ : Finite {s : Finset E // s ∈ K.faces ∧ s.card = 1} := Finite.of_injective
    (fun s => (⟨s.1, s.2.1⟩ : K.faces))
    (fun _ _ h => Subtype.ext (congrArg (fun x : K.faces => x.1) h))
  let _ : Fintype {s : Finset E // s ∈ K.faces ∧ s.card = 1} := Fintype.ofFinite _
  change (∑ w, zmodTwoOfBool (δ (singletonVertex w)) *
      ((Pi.single v (1 : ZMod 2) :
        {s : Finset E // s ∈ K.faces ∧ s.card = 1} → ZMod 2) w)) =
    zmodTwoOfBool (δ (singletonVertex v))
  rw [Finset.sum_eq_single v]
  · simp
  · intro w hw hwv
    simp [Pi.single, hwv]
  · simp

private theorem eq_singleton_or_singleton_of_card_one_subset_pair
    {E : Type} [DecidableEq E] {s : Finset E} {a b : E}
    (hs : s.card = 1) (hsub : s ⊆ {a, b}) : s = {a} ∨ s = {b} := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hs
  subst s
  have hxmem : x = a ∨ x = b := by
    simpa only [Finset.singleton_subset_iff, Finset.mem_insert, Finset.mem_singleton] using hsub
  rcases hxmem with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem orderedNormalizedBoundary_pair_mod_two
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {a b : E} (habFace : {a, b} ∈ K.faces) (hab : a ≠ b) :
    SimplicialComplex.orderedNormalizedBoundary (k := ZMod 2)
        K.toPreAbstractSimplicialComplex 0
        (Pi.single ⟨{a, b}, habFace, Finset.card_pair hab⟩ 1) =
      Pi.single ⟨{a}, K.down_closed habFace (by simp) (by simp), Finset.card_singleton a⟩ 1 +
      Pi.single ⟨{b}, K.down_closed habFace (by simp) (by simp), Finset.card_singleton b⟩ 1 := by
  classical
  let va : {s : Finset E // s ∈ K.faces ∧ s.card = 1} :=
    ⟨{a}, K.down_closed habFace (by simp) (by simp), Finset.card_singleton a⟩
  let vb : {s : Finset E // s ∈ K.faces ∧ s.card = 1} :=
    ⟨{b}, K.down_closed habFace (by simp) (by simp), Finset.card_singleton b⟩
  have vaNeVb : va ≠ vb := by
    intro h
    have hsets := congrArg
      (fun v : {s : Finset E // s ∈ K.faces ∧ s.card = 1} => v.1) h
    change ({a} : Finset E) = {b} at hsets
    exact hab (Finset.singleton_inj.mp hsets)
  change SimplicialComplex.orderedNormalizedBoundary (k := ZMod 2)
      K.toPreAbstractSimplicialComplex 0
      (Pi.single ⟨{a, b}, habFace, Finset.card_pair hab⟩ 1) =
    Pi.single va 1 + Pi.single vb 1
  funext t
  rw [SimplicialComplex.orderedNormalizedBoundary_single_apply]
  rw [simplexBoundaryCoefficient_mod_two (hcard := by
    rw [t.2.2]
    dsimp
    simp [hab])]
  by_cases hsub : t.1 ⊆ {a, b}
  · rw [if_pos hsub]
    rcases eq_singleton_or_singleton_of_card_one_subset_pair t.2.2 hsub with h | h
    · have ht : t = va := Subtype.ext h
      subst t
      simp [vaNeVb]
    · have ht : t = vb := Subtype.ext h
      subst t
      simp [vaNeVb]
  · rw [if_neg hsub]
    have hva : t ≠ va := by
      intro h
      apply hsub
      rw [h]
      simp [va]
    have hvb : t ≠ vb := by
      intro h
      apply hsub
      rw [h]
      simp [vb]
    simp [hva, hvb]

namespace SimplicialBoolCocycle

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_not_isCoboundary_of_bettiNumber_one_pos
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hbettiPos : 0 < Homology.bettiNumber (ZMod 2) (TopCat.of K.space) 1) :
    ∃ ε : SimplicialBoolCocycle K, ¬ ε.IsCoboundary := by
  let _ : LinearOrder E := linearOrderOfSTO WellOrderingRel
  let X := SimplicialComplex.orderedSimplicialSet K.toPreAbstractSimplicialComplex
  let R := ModuleCat.of (ZMod 2) (ZMod 2)
  let C := X.normalizedChainComplex R
  let e₀ := SimplicialComplex.orderedNormalizedChainEquiv (k := ZMod 2)
    K.toPreAbstractSimplicialComplex 0
  let e₁ := SimplicialComplex.orderedNormalizedChainEquiv (k := ZMod 2)
    K.toPreAbstractSimplicialComplex 1
  let e₂ := SimplicialComplex.orderedNormalizedChainEquiv (k := ZMod 2)
    K.toPreAbstractSimplicialComplex 2
  have hnorm := (isoOfQuasiIsoAt (X.toNormalizedChainComplex R) 1).toLinearEquiv.finrank_eq
  change Module.finrank (ZMod 2) ((X.chainComplex R).homology 1) =
    Module.finrank (ZMod 2) (C.homology 1) at hnorm
  have hreal := (DifferentialGeometry.SSet.realizationHomologyIso R X 1).toLinearEquiv.finrank_eq
  let F := (singularHomologyFunctor (ModuleCat (ZMod 2)) 1).obj R
  let e : _root_.SSet.toTop.obj X ≅ TopCat.of K.space :=
    TopCat.isoOfHomeo (by simpa [X] using
      SimplicialComplex.geometricRealizationHomeomorphism K)
  have hhomeo := (F.mapIso e).toLinearEquiv.finrank_eq
  have hbetti : Module.finrank (ZMod 2) (C.homology 1) =
      Homology.bettiNumber (ZMod 2) (TopCat.of K.space) 1 := by
    calc
      Module.finrank (ZMod 2) (C.homology 1) =
          Module.finrank (ZMod 2) ((X.chainComplex R).homology 1) := hnorm.symm
      _ = Module.finrank (ZMod 2)
          (((singularHomologyFunctor (ModuleCat (ZMod 2)) 1).obj R).obj
            (_root_.SSet.toTop.obj X)) := hreal
      _ = Module.finrank (ZMod 2)
          (((singularHomologyFunctor (ModuleCat (ZMod 2)) 1).obj R).obj
            (TopCat.of K.space)) := by simpa [F, X] using hhomeo
      _ = Homology.bettiNumber (ZMod 2) (TopCat.of K.space) 1 := rfl
  let _ : Nontrivial (C.homology 1) :=
    Module.nontrivial_of_finrank_pos (hbetti ▸ hbettiPos)
  let S := C.sc' 2 1 0
  let eh := C.homologyIsoSc' 2 1 0 (by simp) (by simp)
  let _ : Nontrivial S.homology := by
    change Nontrivial ((C.sc' 2 1 0).homology)
    exact eh.symm.toLinearEquiv.toEquiv.nontrivial
  obtain ⟨φ, hφBoundary, z, hφz⟩ :=
    exists_edgeFunctional_of_nontrivial_homology S
  let φC : Module.Dual (ZMod 2) (C.X 1) := φ
  have hφBoundaryC (b : C.X 2) : φC (C.d 2 1 b) = 0 := by
    exact hφBoundary b
  let zC : LinearMap.ker (C.d 1 0).hom := ⟨z.1, z.2⟩
  have hφzC : φC zC.1 ≠ 0 := hφz
  let ω : E → E → ZMod 2 := fun a b => φC (e₁.symm (pairChain K a b))
  let ε : SimplicialBoolCocycle K := {
    parity := fun a b => boolOfZModTwo (ω a b)
    symm := by
      intro a b _
      apply zmodTwoOfBool_injective
      rw [zmodTwoOfBool_boolOfZModTwo, zmodTwoOfBool_boolOfZModTwo]
      simp only [ω]
      rw [pairChain_symm K a b]
    self := by
      intro a _
      apply zmodTwoOfBool_injective
      rw [zmodTwoOfBool_boolOfZModTwo]
      change φC (e₁.symm (pairChain K a a)) = 0
      rw [pairChain_self K a]
      rw [map_zero e₁.symm]
      exact map_zero φC
    cocycle := by
      intro a b c habc
      apply zmodTwoOfBool_injective
      rw [zmodTwoOfBool_xor, zmodTwoOfBool_boolOfZModTwo,
        zmodTwoOfBool_boolOfZModTwo, zmodTwoOfBool_boolOfZModTwo]
      by_cases hab : a = b
      · subst b
        have haa : ω a a = 0 := by
          simp only [ω]
          rw [pairChain_self K a]
          rw [map_zero e₁.symm]
          exact map_zero φC
        rw [haa, zero_add]
      by_cases hbc : b = c
      · subst c
        have hbb : ω b b = 0 := by
          simp only [ω]
          rw [pairChain_self K b]
          rw [map_zero e₁.symm]
          exact map_zero φC
        rw [hbb, add_zero]
      by_cases hac : a = c
      · subst c
        rw [show ω b a = ω a b by simp only [ω]; rw [pairChain_symm K b a]]
        rw [show ω a a = 0 by
          simp only [ω]
          rw [pairChain_self K a]
          rw [map_zero e₁.symm]
          exact map_zero φC]
        exact CharTwo.add_self_eq_zero _
      have habcOrder : ({a, b, c} : Finset E) ∈ K.faces := by
        convert habc using 1
        ext x
        simp
      let q : {s : Finset E // s ∈ K.faces ∧ s.card = 3} :=
        ⟨{a, b, c}, habcOrder, by simp [hab, hbc, hac]⟩
      have hcoord := orderedNormalizedBoundary_triangle_mod_two K habcOrder hab hbc hac
      have hchain : C.d 2 1 (e₂.symm (Pi.single q 1)) =
          e₁.symm (pairChain K a b + pairChain K b c + pairChain K a c) := by
        apply e₁.injective
        rw [e₁.apply_symm_apply]
        simpa [SimplicialComplex.orderedNormalizedBoundary, C, X, e₁, e₂, q] using hcoord
      have hzero := hφBoundaryC (e₂.symm (Pi.single q 1))
      rw [hchain] at hzero
      simp only [map_add] at hzero
      change (ω a b + ω b c) + ω a c = 0 at hzero
      have hneg : ω a b + ω b c = -(ω a c) :=
        eq_neg_of_add_eq_zero_left hzero
      simpa only [ZMod.neg_eq_self_mod_two] using hneg }
  refine ⟨ε, ?_⟩
  intro hε
  obtain ⟨δ, hδ⟩ := hε
  let gCoord := vertexFunctional K δ
  let g : Module.Dual (ZMod 2) (C.X 0) := gCoord.comp e₀.toLinearMap
  have hbasis (s : {s : Finset E // s ∈ K.faces ∧ s.card = 2}) :
      φC (e₁.symm (Pi.single s 1)) =
        g (C.d 1 0 (e₁.symm (Pi.single s 1))) := by
    rcases s with ⟨s, hsFace, hsCard⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hsCard
    have hsCardEq : hsCard = Finset.card_pair hab := Subsingleton.elim _ _
    cases hsCardEq
    have hδBool : ε.parity a b = Bool.xor (δ a) (δ b) := hδ a b (by
      convert hsFace using 1
      ext x
      simp)
    change boolOfZModTwo (ω a b) = Bool.xor (δ a) (δ b) at hδBool
    have hδZ := congrArg zmodTwoOfBool hδBool
    rw [zmodTwoOfBool_boolOfZModTwo, zmodTwoOfBool_xor] at hδZ
    have haFace : {a} ∈ K.faces := K.down_closed hsFace (by simp) (by simp)
    have hbFace : {b} ∈ K.faces := K.down_closed hsFace (by simp) (by simp)
    have hcoord := orderedNormalizedBoundary_pair_mod_two K hsFace hab
    have hdcoord : e₀ (C.d 1 0
          (e₁.symm (Pi.single ⟨{a, b}, hsFace, Finset.card_pair hab⟩ 1))) =
        Pi.single
            ⟨{a}, haFace, Finset.card_singleton a⟩ 1 +
          Pi.single
            ⟨{b}, hbFace, Finset.card_singleton b⟩ 1 := by
      simpa [SimplicialComplex.orderedNormalizedBoundary, C, X, e₀, e₁] using hcoord
    dsimp only [g, LinearMap.comp_apply]
    change _ = gCoord (e₀ (C.d 1 0
      (e₁.symm (Pi.single ⟨{a, b}, hsFace, Finset.card_pair hab⟩ 1))))
    rw [hdcoord, map_add, vertexFunctional_single, vertexFunctional_single,
      singletonVertex_singleton (K := K) haFace,
      singletonVertex_singleton (K := K) hbFace]
    rw [← pairChain_of_face K hsFace hab]
    simpa only [ω] using hδZ
  have hall (x : C.X 1) : φC x = g (C.d 1 0 x) := by
    let _ : Finite {s : Finset E // s ∈ K.faces ∧ s.card = 2} := Finite.of_injective
      (fun s => (⟨s.1, s.2.1⟩ : K.faces))
      (fun _ _ h => Subtype.ext (congrArg (fun y : K.faces => y.1) h))
    let _ : Fintype {s : Finset E // s ∈ K.faces ∧ s.card = 2} := Fintype.ofFinite _
    have hx : x = ∑ s, (e₁ x s) • e₁.symm (Pi.single s 1) := by
      apply e₁.injective
      rw [map_sum]
      funext t
      simp only [map_smul, LinearEquiv.apply_symm_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      symm
      convert Fintype.sum_pi_single t (e₁ x) using 1
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hst : s = t <;> simp [hst]
    rw [hx]
    rw [map_sum φC, map_sum (C.d 1 0).hom, map_sum g]
    simp only [map_smul]
    apply Finset.sum_congr rfl
    intro s hs
    exact congrArg ((e₁ x s) • ·) (hbasis s)
  have hcycle := hall zC.1
  rw [show C.d 1 0 zC.1 = 0 from zC.2, map_zero] at hcycle
  exact hφzC hcycle

end SimplicialBoolCocycle

end DifferentialGeometry.Topology.PiecewiseLinear
